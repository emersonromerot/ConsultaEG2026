/*
 * app.js — Fase 4: mapa de coropletas multinivel + selectores + tabla top-10
 *
 * Depende de cargador.js (carga perezosa vía <script>) y de que ya estén
 * cargados: Leaflet, topojson-client, MANIFEST (data/manifest.js).
 *
 * Claves de cruce (deben coincidir con las de consolidar_nacional.py /
 * preparar_geometrias.py):
 *   circunscripción → circunscripcion_slug
 *   provincia       → ubigeo_prov (4 dígitos)
 *   distrito        → ubigeo (6 dígitos)
 *   local           → local_key (calculado en Python, ver preparar_geometrias.py)
 */

let circLocalAjustada = null; // circunscripción a la que ya se encuadró el mapa en nivel local

const estado = {
  eleccionSlug: null,
  agregados: null,
  pkey: null,
  modo: 'total',           // 'total' | 'candidato'
  circCandidato: null,     // circunscripción elegida para desambiguar candidato (elecciones regionales)
  candidatoClave: null,
  nivelActivo: 'circunscripcion',
  circLocal: null,         // circunscripción elegida para ver "local" en elecciones regionales
  datosLocalesActuales: null, // dict local_key -> nodo, para el nivel local ya resuelto
  metrica: 'abs',          // 'abs' | 'pct' — comparte mapa y tabla
  decilesSeleccionados: new Set(), // checklist de la leyenda: vacío = mostrar todo; si no, solo esos deciles/outlier
  graficoActivo: 'mesas',  // 'mesas' | 'concentracion' | 'ganador' | 'nulos'
  graficoNivel: 'distrito', // nivel usado por los gráficos de ganador/nulos
  graficoPkey: null,       // partido elegido en la pestaña Gráficos — independiente del de la pestaña Mapa
  comparacionA: null,      // pkey del partido A en modo comparación (gráfico ganador)
  comparacionACand: null,  // candidato específico del lado A (null = total del partido)
  comparacionB: null,      // pkey del partido B en modo comparación (gráfico ganador)
  comparacionBCand: null,  // candidato específico del lado B (null = total del partido)
  comparacionCirc: null,   // circunscripción elegida para poder listar candidatos (elecciones regionales)
  detalleNivel: 'circunscripcion', // nivel de la pestaña Detalle — independiente de Mapa y Gráficos
  detalleCirc: null,       // circunscripción elegida para ver locales en Detalle (independiente de circLocal)
  detalleProvincia: null,  // provincia elegida para acotar la lista de distritos/locales en Detalle
  detalleDistrito: null,   // distrito elegido para acotar la lista de locales en Detalle
  detalleDatosLocales: null, // dict local_key -> nodo, para el nivel local de Detalle ya resuelto
  detalleBusqueda: '',
  detalleClave: null,      // clave del polígono actualmente mostrado en la ficha
  detallePartidosAbiertos: new Set(), // pkeys con su lista de candidatos desplegada, para la ficha activa
};

// geojson decodificado + lookup de nombre, cacheados por nivel (no hay que
// redecodificar el TopoJSON cada vez que se cambia de partido/candidato)
const cacheGeo = {}; // nivel -> { geojson, nombresPorClave, propClave }

let map, capaActual, capaLocalActual, tooltip;
let capaFondoLocal = null, fondoLocalClave = null; // capa de contexto nacional (nivel distrito, opacidad baja), solo en modo local
let mapComparacion, capaComparacion; // segundo mapa Leaflet, solo para el modo comparación de Gráficos
let mapNulos, capaNulos; // tercer mapa Leaflet, solo para la coropleta de nulos/blancos
const layerPorClave = {}; // clave del nivel activo -> capa Leaflet (para el clic de la tabla)

// ══════════════════════════════════════════════════════════════════
// UTILIDADES DE COLOR (blanco → color del partido, según percentil 90)
// ══════════════════════════════════════════════════════════════════

function hexToRgb(color) {
  // Acepta tanto "#rrggbb"/"#rgb" como "rgb(r,g,b)" (colorAcentoOutlier()
  // y otras funciones de color de la comparación devuelven este último).
  const comoRgb = /^rgb\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)\s*\)$/i.exec(color);
  if (comoRgb) return [Number(comoRgb[1]), Number(comoRgb[2]), Number(comoRgb[3])];
  let hex = color.replace('#', '');
  if (hex.length === 3) hex = hex.split('').map(c => c + c).join('');
  const n = parseInt(hex, 16);
  return [n >> 16 & 255, n >> 8 & 255, n & 255];
}

function interpColor(colorHex, t) {
  const [r, g, b] = hexToRgb(colorHex);
  t = Math.max(0, Math.min(1, t));
  return `rgb(${Math.round(255 + (r - 255) * t)},${Math.round(255 + (g - 255) * t)},${Math.round(255 + (b - 255) * t)})`;
}

function percentil(valoresOrdenados, p) {
  if (!valoresOrdenados.length) return 0;
  const idx = Math.min(valoresOrdenados.length - 1, Math.floor(valoresOrdenados.length * p));
  return valoresOrdenados[idx];
}

// Escala por deciles: clasifica los valores mostrados (>0) en 10 grupos
// de igual cantidad de polígonos (P10..P90 como cortes) y les asigna un
// color de intensidad creciente — a diferencia de una escala continua
// lineal o potencia, esto garantiza buena separación visual sin importar
// qué tan sesgada esté la distribución del partido (confirmado con
// graficar_distribucion_partido.py: en votos por distrito el IQR clásico
// no aísla un grupo chico de outliers, pero P99 sí). Los valores por
// encima de P99 —el 1% más alto— se pintan aparte, con un color de
// acento en vez de "decil 11", para que se lean como "fuera de escala".
const CORTES_DECIL = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]; // P10..P90

function calcularEscala(valores) {
  const v = valores.filter(x => x > 0).sort((a, b) => a - b);
  if (!v.length) return { deciles: [], p99: Infinity };
  const deciles = CORTES_DECIL.map(p => percentil(v, p));
  const p99 = percentil(v, 0.99);
  return { deciles, p99 };
}

function esOutlier(valor, escala) {
  return valor > 0 && valor > escala.p99;
}

// Número de decil (1..10) de un valor dentro de la escala — 1 = P0-P10
// (el más bajo), 10 = por encima de P90 (incluye a los outliers >P99,
// que después se pintan aparte con su propio color de acento).
function numeroDecil(valor, escala) {
  if (valor <= 0) return 0;
  let decil = 1;
  for (let i = 0; i < escala.deciles.length; i++) {
    if (valor > escala.deciles[i]) decil = i + 2;
    else break;
  }
  return Math.min(decil, 10);
}

// Color del decil (sin outliers) para un valor dado.
function colorDecil(valor, escala, colorPartido) {
  if (valor <= 0) return '#ffffff';
  return interpColor(colorPartido, numeroDecil(valor, escala) / 10);
}

// Checklist de la leyenda: si no hay nada marcado, se ve todo (default).
// Si hay algo marcado, solo se ve lo que cae en esos deciles/outlier —
// el resto se atenúa casi a invisible pero sin desaparecer del todo, para
// no perder la referencia de la forma del mapa.
function visiblePorFiltroDecil(valor, escala) {
  if (estado.decilesSeleccionados.size === 0) return true;
  if (valor <= 0) return false;
  if (esOutlier(valor, escala)) return estado.decilesSeleccionados.has('outlier');
  return estado.decilesSeleccionados.has(numeroDecil(valor, escala));
}

// Color de acento para el bucket de outliers: en vez de un color fijo
// (que puede coincidir con el propio color de un partido — hay varios
// que usan amarillos), se calcula rotando el matiz (hue) del color del
// partido 180° en HSL. Así siempre queda maximamente distinto del color
// que se está usando para ese partido en particular, sin necesidad de
// mantener una lista de colores "prohibidos" por partido.
function rgbToHsl(r, g, b) {
  r /= 255; g /= 255; b /= 255;
  const max = Math.max(r, g, b), min = Math.min(r, g, b);
  let h, s, l = (max + min) / 2;
  if (max === min) { h = s = 0; }
  else {
    const d = max - min;
    s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
    switch (max) {
      case r: h = (g - b) / d + (g < b ? 6 : 0); break;
      case g: h = (b - r) / d + 2; break;
      default: h = (r - g) / d + 4;
    }
    h /= 6;
  }
  return [h, s, l];
}

function hslToRgb(h, s, l) {
  let r, g, b;
  if (s === 0) { r = g = b = l; }
  else {
    const hue2rgb = (p, q, t) => {
      if (t < 0) t += 1;
      if (t > 1) t -= 1;
      if (t < 1 / 6) return p + (q - p) * 6 * t;
      if (t < 1 / 2) return q;
      if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
      return p;
    };
    const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
    const p = 2 * l - q;
    r = hue2rgb(p, q, h + 1 / 3);
    g = hue2rgb(p, q, h);
    b = hue2rgb(p, q, h - 1 / 3);
  }
  return [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
}

function colorAcentoOutlier(colorPartidoHex) {
  const [r, g, b] = hexToRgb(colorPartidoHex);
  let [h, s, l] = rgbToHsl(r, g, b);
  h = (h + 0.5) % 1;             // matiz opuesto — máximo contraste posible
  s = Math.max(s, 0.8);          // bien saturado, que no salga "lavado"
  l = 0.55;                      // ni muy oscuro ni muy claro sobre el mapa oscuro
  const [r2, g2, b2] = hslToRgb(h, s, l);
  return `rgb(${r2},${g2},${b2})`;
}

// ══════════════════════════════════════════════════════════════════
// CALCULO DE VALORES (abs / % de votos válidos) por nodo de nivel
// ══════════════════════════════════════════════════════════════════

function valorNodo(nodo) {
  if (!nodo || !nodo.partidos) return { abs: 0, pct: 0 };
  const datosPartido = nodo.partidos[estado.pkey];
  if (!datosPartido) return { abs: 0, pct: 0 };

  let abs = 0;
  if (estado.modo === 'total') {
    abs = datosPartido.total || 0;
  } else if (estado.candidatoClave) {
    abs = (datosPartido.candidatos && datosPartido.candidatos[estado.candidatoClave]) || 0;
  }

  const validos = Math.max(0, (nodo.total_votantes || 0) - (nodo.votos_blanco || 0) - (nodo.votos_viciado || 0));
  const pct = validos > 0 ? (abs / validos) * 100 : 0;
  return { abs, pct };
}

// ══════════════════════════════════════════════════════════════════
// GEOMETRIA: decodificar + cachear + construir lookup de nombre
// ══════════════════════════════════════════════════════════════════

const CONFIG_NIVEL = {
  circunscripcion: { geoNivel: 'circunscripciones', propClave: 'circunscripcion_slug', propNombre: 'nombre_display' },
  provincia:        { geoNivel: 'provincias',        propClave: 'ubigeo_prov',          propNombre: 'provincia' },
  distrito:         { geoNivel: 'distritos',          propClave: 'ubigeo',                propNombre: 'distrito' },
  local:            { geoNivel: 'locales',            propClave: 'local_key',             propNombre: 'NOMBRE DEL LOCAL' },
};

async function obtenerGeoDecodificada(nivel) {
  if (cacheGeo[nivel]) return cacheGeo[nivel];
  const cfg = CONFIG_NIVEL[nivel];
  const topologia = await cargarGeometria(cfg.geoNivel);
  const geojson = topojsonAGeojson(topologia);
  const nombresPorClave = {};
  for (const f of geojson.features) {
    nombresPorClave[f.properties[cfg.propClave]] = f.properties[cfg.propNombre] || f.properties[cfg.propClave];
  }
  cacheGeo[nivel] = { geojson, nombresPorClave };
  return cacheGeo[nivel];
}

// ══════════════════════════════════════════════════════════════════
// DATOS DEL NIVEL ACTIVO (de dónde salen los nodos a pintar/tabular)
// ══════════════════════════════════════════════════════════════════

// Cuando el candidato elegido pertenece a una elección de lista regional,
// la circunscripción que define esa lista también acota qué provincias/
// distritos/locales se muestran en el mapa y la tabla (no tiene sentido
// ver el resto del país si el candidato solo compitió en una región).
const MAPA_CIRC_POR_NIVEL = {
  provincia: 'circunscripcion_por_provincia',
  distrito: 'circunscripcion_por_distrito',
  local: 'circunscripcion_por_local',
};

function circunscripcionActivaParaFiltro() {
  if (estado.modo !== 'candidato') return null;
  if (!estado.agregados || estado.agregados.es_nacional) return null;
  return estado.circCandidato || null;
}

function datosNivelActivo() {
  let datos;
  if (estado.nivelActivo === 'local') {
    datos = estado.datosLocalesActuales || {};
  } else {
    datos = (estado.agregados.niveles[estado.nivelActivo]) || {};
  }

  const circActiva = circunscripcionActivaParaFiltro();
  if (!circActiva) return datos;

  if (estado.nivelActivo === 'circunscripcion') {
    return Object.fromEntries(Object.entries(datos).filter(([clave]) => clave === circActiva));
  }
  const nombreMapa = MAPA_CIRC_POR_NIVEL[estado.nivelActivo];
  const mapaCirc = (estado.agregados[nombreMapa]) || {};
  return Object.fromEntries(Object.entries(datos).filter(([clave]) => mapaCirc[clave] === circActiva));
}

// ══════════════════════════════════════════════════════════════════
// RENDER: MAPA
// ══════════════════════════════════════════════════════════════════

async function renderMapa() {
  if (capaActual) { map.removeLayer(capaActual); capaActual = null; }
  if (capaLocalActual) { map.removeLayer(capaLocalActual); capaLocalActual = null; }
  if (estado.nivelActivo !== 'local') {
    circLocalAjustada = null;
    if (capaFondoLocal) { map.removeLayer(capaFondoLocal); capaFondoLocal = null; fondoLocalClave = null; }
  }
  Object.keys(layerPorClave).forEach(k => delete layerPorClave[k]);

  if (!estado.pkey) { renderLeyenda(null); return; }

  if (estado.nivelActivo === 'local') {
    renderMapaLocal();
    return;
  }

  const { geojson, nombresPorClave } = await obtenerGeoDecodificada(estado.nivelActivo);
  const cfg = CONFIG_NIVEL[estado.nivelActivo];
  const datos = datosNivelActivo();
  const circActiva = circunscripcionActivaParaFiltro();
  const featuresVisibles = circActiva
    ? geojson.features.filter(f => f.properties[cfg.propClave] in datos)
    : geojson.features;

  const metrica = estado.metrica;
  const valores = featuresVisibles.map(f => valorNodo(datos[f.properties[cfg.propClave]])[metrica]);
  const escala = calcularEscala(valores);
  const color = (estado.agregados.metadata_partidos[estado.pkey] || {}).color || '#4da6ff';
  const colorOutlier = colorAcentoOutlier(color);

  capaActual = L.geoJSON({ type: 'FeatureCollection', features: featuresVisibles }, {
    style: f => {
      const valor = valorNodo(datos[f.properties[cfg.propClave]])[metrica];
      const outlier = esOutlier(valor, escala);
      const visible = visiblePorFiltroDecil(valor, escala);
      return {
        fillColor: outlier ? colorOutlier : colorDecil(valor, escala, color),
        fillOpacity: visible ? 0.82 : 0.05,
        color: '#ffffff',
        weight: outlier ? 1.6 : 0.6,
        opacity: visible ? (outlier ? 1 : 0.45) : 0.08,
      };
    },
    onEachFeature: (f, layer) => {
      const clave = f.properties[cfg.propClave];
      layerPorClave[clave] = layer;
      const nombre = nombresPorClave[clave];
      const { abs, pct } = valorNodo(datos[clave]);
      const outlier = esOutlier(valorNodo(datos[clave])[metrica], escala);
      layer.bindTooltip(`<b>${nombre}</b><br>${abs.toLocaleString('es-PE')} votos (${pct.toFixed(1)}%)`
        + (outlier ? `<br><span style="color:${colorOutlier}">⬤ fuera de escala (top 1%)</span>` : ''),
        { sticky: true, className: 'info-tooltip' });
      layer.on('click', () => { map.fitBounds(layer.getBounds(), { maxZoom: 12 }); resaltar(layer); });
    },
  }).addTo(map);

  if (Object.keys(layerPorClave).length) map.fitBounds(capaActual.getBounds());
  renderLeyenda(escala, color, colorOutlier);
}

let capaResaltada = null;
function resaltar(layer) {
  if (capaResaltada && capaResaltada !== layer) {
    (capaActual || capaLocalActual).resetStyle(capaResaltada);
  }
  layer.setStyle({ weight: 2.5, color: '#ffffff' });
  layer.bringToFront();
  capaResaltada = layer;
}

// Capa de contexto: el país completo a nivel distrito, en opacidad baja
// y sin interactividad, siempre presente en modo "local" — así al
// acercarse a una circunscripción no se pierde la referencia visual del
// resto del país. Se agrega ANTES que la capa de locales (queda debajo,
// según el orden de inserción del renderer de Leaflet) y se cachea por
// partido/modo/candidato/métrica para no reconstruir ~1900 polígonos en
// cada pan/zoom.
async function renderFondoLocal() {
  if (!estado.pkey) {
    if (capaFondoLocal) { map.removeLayer(capaFondoLocal); capaFondoLocal = null; }
    fondoLocalClave = null;
    return;
  }
  const clave = `${estado.eleccionSlug}|${estado.pkey}|${estado.modo}|${estado.candidatoClave}|${estado.metrica}`;
  if (clave === fondoLocalClave && capaFondoLocal) return; // ya está al día, no se reconstruye
  fondoLocalClave = clave;
  if (capaFondoLocal) { map.removeLayer(capaFondoLocal); capaFondoLocal = null; }

  const { geojson } = await obtenerGeoDecodificada('distrito');
  const cfg = CONFIG_NIVEL.distrito;
  const datosNacionales = estado.agregados.niveles.distrito || {};
  const metrica = estado.metrica;
  const valores = geojson.features.map(f => valorNodo(datosNacionales[f.properties[cfg.propClave]])[metrica]);
  const escala = calcularEscala(valores);
  const color = (estado.agregados.metadata_partidos[estado.pkey] || {}).color || '#4da6ff';

  capaFondoLocal = L.geoJSON(geojson, {
    interactive: false, // solo contexto visual — no compite con clics/tooltips de los locales
    style: f => {
      const valor = valorNodo(datosNacionales[f.properties[cfg.propClave]])[metrica];
      return {
        fillColor: colorDecil(valor, escala, color),
        fillOpacity: 0.14,
        color: '#ffffff',
        weight: 0.3,
        opacity: 0.18,
      };
    },
  }).addTo(map);
}

// true si todas las coordenadas del polígono son números finitos — un solo
// vértice NaN hace que Leaflet aborte la capa completa de la circunscripción.
function geometriaValida(f) {
  const g = f && f.geometry;
  if (!g || !g.coordinates) return false;
  const anillos = g.type === 'Polygon' ? g.coordinates
    : g.type === 'MultiPolygon' ? g.coordinates.flat() : null;
  if (!anillos || !anillos.length) return false;
  return anillos.every(r => r.every(p => Number.isFinite(p[0]) && Number.isFinite(p[1])));
}

async function renderMapaLocal() {
  await renderFondoLocal();
  const avisoEl = document.getElementById('aviso-local');
  if (!estado.datosLocalesActuales) {
    avisoEl.style.display = 'block';
    avisoEl.textContent = 'Elige una circunscripción para cargar sus locales.';
    renderLeyenda(null);
    return;
  }
  avisoEl.style.display = 'none';

  const { geojson, nombresPorClave } = await obtenerGeoDecodificada('local');
  const datos = datosNivelActivo(); // ya filtrado por circunscripción de candidato si aplica
  const featuresVisibles = geojson.features.filter(f => f.properties.local_key in datos && geometriaValida(f));

  if (capaLocalActual) map.removeLayer(capaLocalActual);
  const color = (estado.agregados.metadata_partidos[estado.pkey] || {}).color || '#4da6ff';
  const colorOutlier = colorAcentoOutlier(color);
  const metrica = estado.metrica;
  const valores = featuresVisibles.map(f => valorNodo(datos[f.properties.local_key])[metrica]);
  const escala = calcularEscala(valores);

  capaLocalActual = L.geoJSON({ type: 'FeatureCollection', features: featuresVisibles }, {
    style: f => {
      const valor = valorNodo(datos[f.properties.local_key])[metrica];
      const outlier = esOutlier(valor, escala);
      const visible = visiblePorFiltroDecil(valor, escala);
      return {
        fillColor: outlier ? colorOutlier : colorDecil(valor, escala, color),
        fillOpacity: visible ? 0.85 : 0.05,
        color: '#ffffff',
        weight: outlier ? 1.4 : 0.5,
        opacity: visible ? (outlier ? 1 : 0.4) : 0.08,
      };
    },
    onEachFeature: (f, layer) => {
      const clave = f.properties.local_key;
      layerPorClave[clave] = layer;
      const nombre = nombresPorClave[clave];
      const { abs, pct } = valorNodo(datos[clave]);
      const outlier = esOutlier(valorNodo(datos[clave])[metrica], escala);
      layer.bindTooltip(`<b>${nombre}</b><br>${abs.toLocaleString('es-PE')} votos (${pct.toFixed(1)}%)`
        + (outlier ? `<br><span style="color:${colorOutlier}">⬤ fuera de escala (top 1%)</span>` : ''),
        { sticky: true, className: 'info-tooltip' });
      layer.on('click', () => resaltar(layer));
    },
  }).addTo(map);
  // sin umbral de zoom: al elegir circunscripción se encuadra el mapa en ella (solo la primera vez,
  // para no perder el zoom del usuario al cambiar de partido/candidato/métrica)
  if (circLocalAjustada !== estado.circLocal && featuresVisibles.length) {
    circLocalAjustada = estado.circLocal;
    map.fitBounds(capaLocalActual.getBounds());
  }
  renderLeyenda(escala, color, colorOutlier);
}

// ══════════════════════════════════════════════════════════════════
// LEYENDA (gradiente de deciles + outlier) — checklist para aislar niveles
// ══════════════════════════════════════════════════════════════════

function formatoVotos(v) {
  if (estado.metrica === 'pct') return `${v.toFixed(1)}%`;
  return Math.round(v).toLocaleString('es-PE');
}

// escala === null quita la leyenda (sin partido elegido / sin datos aún).
function renderLeyenda(escala, colorPartido, colorOutlier) {
  const cont = document.getElementById('leyenda-mapa');
  if (!escala) { cont.innerHTML = ''; cont.style.display = 'none'; return; }
  cont.style.display = 'block';

  const bordes = [0, ...escala.deciles, escala.p99]; // 11 cortes → 10 deciles (1..10)
  const filas = [];

  // outlier primero (arriba de todo, es "más que el decil 10")
  filas.push({
    id: 'outlier', color: colorOutlier,
    etiqueta: `> ${formatoVotos(escala.p99)} (top 1%)`,
  });
  for (let d = 10; d >= 1; d--) {
    const inf = bordes[d - 1];
    const sup = bordes[d];
    const etiqueta = d === 1
      ? `≤ ${formatoVotos(sup)}`
      : `${formatoVotos(inf)} – ${formatoVotos(sup)}`;
    filas.push({ id: d, color: interpColor(colorPartido, d / 10), etiqueta });
  }

  cont.innerHTML = `
    <div class="leyenda-header">
      <span>Escala (clic para aislar)</span>
      ${estado.decilesSeleccionados.size ? '<button id="leyenda-limpiar">ver todo</button>' : ''}
    </div>
    ${filas.map(f => `
      <label class="leyenda-fila">
        <input type="checkbox" data-decil="${f.id}" ${estado.decilesSeleccionados.has(f.id) ? 'checked' : ''}>
        <span class="leyenda-swatch" style="background:${f.color}"></span>
        <span class="leyenda-etiqueta">${f.etiqueta}</span>
      </label>`).join('')}
  `;

  cont.querySelectorAll('input[type=checkbox]').forEach(chk => {
    chk.addEventListener('change', () => {
      const id = chk.dataset.decil === 'outlier' ? 'outlier' : Number(chk.dataset.decil);
      if (chk.checked) estado.decilesSeleccionados.add(id);
      else estado.decilesSeleccionados.delete(id);
      renderMapa();
    });
  });
  const btnLimpiar = document.getElementById('leyenda-limpiar');
  if (btnLimpiar) {
    btnLimpiar.addEventListener('click', () => {
      estado.decilesSeleccionados.clear();
      renderMapa();
    });
  }
}

// ══════════════════════════════════════════════════════════════════
// RENDER: TABLA TOP-10
// ══════════════════════════════════════════════════════════════════

async function renderTabla() {
  const tbody = document.getElementById('tabla-body');
  const titulo = document.getElementById('tabla-titulo');
  tbody.innerHTML = '';
  if (!estado.pkey) { titulo.textContent = 'Top 10'; return; }

  let nombresPorClave = {};
  if (estado.nivelActivo !== 'local' || estado.datosLocalesActuales) {
    const g = await obtenerGeoDecodificada(estado.nivelActivo);
    nombresPorClave = g.nombresPorClave;
  }

  const datos = datosNivelActivo();
  const filas = Object.entries(datos).map(([clave, nodo]) => {
    const { abs, pct } = valorNodo(nodo);
    return { clave, nombre: nombresPorClave[clave] || clave, abs, pct };
  }).filter(f => f.abs > 0);

  filas.sort((a, b) => estado.metrica === 'abs' ? b.abs - a.abs : b.pct - a.pct);
  const top10 = filas.slice(0, 10);

  const nombreNivel = { circunscripcion: 'circunscripciones', provincia: 'provincias', distrito: 'distritos', local: 'locales' }[estado.nivelActivo];
  titulo.textContent = `Top 10 ${nombreNivel} · ${estado.metrica === 'abs' ? 'votos' : '%'}`;

  tbody.innerHTML = top10.map((f, i) => `
    <tr class="fila-rank" data-clave="${f.clave}">
      <td class="rk-num">${i + 1}</td>
      <td class="rk-nombre" title="${f.nombre}">${f.nombre}</td>
      <td class="rk-valor">${estado.metrica === 'abs' ? f.abs.toLocaleString('es-PE') : f.pct.toFixed(1) + '%'}</td>
    </tr>`).join('');

  tbody.querySelectorAll('.fila-rank').forEach(tr => {
    tr.addEventListener('click', () => {
      const layer = layerPorClave[tr.dataset.clave];
      if (layer) { map.fitBounds(layer.getBounds ? layer.getBounds() : layer.getLatLng(), { maxZoom: 13 }); resaltar(layer); }
    });
  });
}

function renderTodo() { renderMapa(); renderTabla(); }

// ══════════════════════════════════════════════════════════════════
// CARGA DE LOCALES (siempre por circunscripción — para las 5 elecciones)
// ══════════════════════════════════════════════════════════════════

async function cargarLocalesParaNivelActivo() {
  if (!estado.circLocal) { estado.datosLocalesActuales = null; return; }
  document.getElementById('estado-carga').textContent = `Cargando locales de ${estado.circLocal}…`;
  estado.datosLocalesActuales = await cargarLocalesRegion(estado.eleccionSlug, estado.circLocal);
  document.getElementById('estado-carga').textContent = '';
}

// Cuando el modo es "candidato" en una elección regional y ya se eligió
// la circunscripción que define esa lista, esa misma circunscripción se
// usa para el nivel local — no tiene sentido pedirla dos veces. Si no
// hay candidato eligiendo la circunscripción (modo total, o elección de
// lista nacional), el selector de circunscripción para locales se pide
// de forma independiente, como antes.
async function sincronizarNivelLocal() {
  if (estado.nivelActivo !== 'local') return;
  const campo = document.getElementById('campo-circ-local');
  const circActiva = circunscripcionActivaParaFiltro();
  if (circActiva) {
    campo.style.display = 'none';
    estado.circLocal = circActiva;
  } else {
    campo.style.display = 'block';
    poblarCircunscripcionesGenerico(document.getElementById('sel-circ-local'));
    document.getElementById('sel-circ-local').value = estado.circLocal || '';
  }
  await cargarLocalesParaNivelActivo();
}

// ══════════════════════════════════════════════════════════════════
// POBLAR SELECTORES
// ══════════════════════════════════════════════════════════════════

function poblarPartidos() {
  const sel = document.getElementById('sel-partido');
  const partidos = Object.entries(estado.agregados.metadata_partidos)
    .sort((a, b) => a[1].nombre_completo.localeCompare(b[1].nombre_completo));
  sel.innerHTML = '<option value="">— elige un partido —</option>' +
    partidos.map(([pkey, m]) => `<option value="${pkey}">${m.nombre_completo}</option>`).join('');
  sel.disabled = false;
}

function poblarCircunscripcionesGenerico(selectEl) {
  const circs = MANIFEST.circunscripciones_por_eleccion[estado.eleccionSlug] || [];
  const { nombresPorClave } = cacheGeo['circunscripcion'] || { nombresPorClave: {} };
  selectEl.innerHTML = '<option value="">— elige una circunscripción —</option>' +
    circs.map(c => `<option value="${c}">${nombresPorClave[c] || c}</option>`).join('');
}

// Número de lista de un candidato a partir de su clave ("circ||numero" en
// elecciones regionales, o "numero" directo en las nacionales) — se usa
// para ordenar candidatos POR NÚMERO y no alfabéticamente (con orden de
// texto, "10" sale antes que "2"). Compartida entre la pestaña Mapa y el
// modo comparación de Gráficos.
function numeroDeClaveCandidato(clave) {
  const parte = clave.includes('||') ? clave.slice(clave.lastIndexOf('||') + 2) : clave;
  const n = parseInt(parte, 10);
  return Number.isNaN(n) ? Infinity : n; // ej. "PLANCHA" (Presidencial) al final
}

function poblarCandidatos() {
  const sel = document.getElementById('sel-candidato');
  const meta = estado.agregados.metadata_partidos[estado.pkey];
  if (!meta) { sel.innerHTML = ''; return; }

  let entradas;
  if (estado.agregados.es_nacional) {
    entradas = Object.entries(meta.candidatos);
  } else {
    if (!estado.circCandidato) { sel.innerHTML = '<option value="">— elige circunscripción primero —</option>'; return; }
    const prefijo = `${estado.circCandidato}||`;
    entradas = Object.entries(meta.candidatos)
      .filter(([clave]) => clave.startsWith(prefijo))
      .map(([clave, v]) => [clave, v]);
  }
  entradas.sort((a, b) => numeroDeClaveCandidato(a[0]) - numeroDeClaveCandidato(b[0]));
  sel.innerHTML = '<option value="">— elige un candidato —</option>' +
    entradas.map(([clave, v]) => {
      const n = numeroDeClaveCandidato(clave);
      const etiqueta = Number.isFinite(n) ? `${n} — ${v.nombre}` : v.nombre;
      return `<option value="${clave}">${etiqueta}</option>`;
    }).join('');
}

// ══════════════════════════════════════════════════════════════════
// FASE 5 — PESTAÑA DE GRÁFICOS
// Usa series_graficos (mesas_por_votos, concentración) que ya vienen
// precalculadas en agregados_{eleccion}.json — no requiere cargar nada
// nuevo. "Ganador por polígono" y "Nulos y blancos" se calculan al
// vuelo en el cliente a partir de niveles.circunscripcion/provincia/
// distrito, que también ya están cargados.
// ══════════════════════════════════════════════════════════════════

const COLORES_PALETA_DEFECTO = ['#4da6ff', '#ff6b6b', '#51cf66', '#f7c948', '#c084fc'];
const chartsActivos = {}; // id de canvas -> instancia Chart.js (para destruir antes de re-crear)

function crearChart(idCanvas, config) {
  if (chartsActivos[idCanvas]) { chartsActivos[idCanvas].destroy(); delete chartsActivos[idCanvas]; }
  const el = document.getElementById(idCanvas);
  if (!el) return null;
  const chart = new Chart(el.getContext('2d'), config);
  chartsActivos[idCanvas] = chart;
  return chart;
}

const OPCIONES_CHART_BASE = {
  responsive: true,
  maintainAspectRatio: false,
  plugins: { legend: { labels: { color: '#e2e8f0', font: { size: 11 } } } },
  scales: {
    x: { ticks: { color: '#8892a4', font: { size: 10 } }, grid: { color: '#2a2d3e' } },
    y: { ticks: { color: '#8892a4', font: { size: 10 } }, grid: { color: '#2a2d3e' } },
  },
};

function mostrarBloqueGrafico(id) {
  document.querySelectorAll('.graf-bloque').forEach(b => b.style.display = 'none');
  const el = document.getElementById(id);
  if (el) el.style.display = 'flex'; // .graf-bloque es columna flex, para que el mapa/gráfico se estire hasta el fondo
}

function poblarPartidosGrafico() {
  const sel = document.getElementById('graf-sel-partido');
  const partidos = Object.entries(estado.agregados.metadata_partidos)
    .sort((a, b) => a[1].nombre_completo.localeCompare(b[1].nombre_completo));
  sel.innerHTML = '<option value="">— elige un partido —</option>' +
    partidos.map(([pkey, m]) => `<option value="${pkey}">${m.nombre_completo}</option>`).join('');
  sel.disabled = false;
}

function poblarSelectoresComparacion() {
  if (!estado.agregados) return;
  const partidos = Object.entries(estado.agregados.metadata_partidos)
    .sort((a, b) => a[1].nombre_completo.localeCompare(b[1].nombre_completo));
  const opciones = '<option value="">— elige —</option>' +
    partidos.map(([pkey, m]) => `<option value="${pkey}">${m.nombre_completo}</option>`).join('');
  document.getElementById('graf-comp-a').innerHTML = opciones;
  document.getElementById('graf-comp-b').innerHTML = opciones;
  poblarCandidatosComparacion(document.getElementById('graf-comp-a-cand'), null, estado.comparacionCirc);
  poblarCandidatosComparacion(document.getElementById('graf-comp-b-cand'), null, estado.comparacionCirc);
  if (!estado.agregados.es_nacional) {
    poblarCircunscripcionesGenerico(document.getElementById('graf-comp-circ'));
  }
  actualizarUIComparacion();
}

// La Presidencial no admite comparar candidatos (la "lista" es el partido/
// plancha, igual que en la pestaña Mapa) — solo total del partido. En las
// elecciones regionales (diputados, senado regional) los candidatos solo
// existen dentro de UNA circunscripción, así que hace falta elegirla antes
// de poder listarlos — se muestra/oculta el selector de circunscripción
// según corresponda.
function actualizarUIComparacion() {
  const esPresidencial = estado.eleccionSlug === 'presidencial';
  const esRegional = !!(estado.agregados && !estado.agregados.es_nacional);
  document.getElementById('graf-comp-a-cand').style.display = esPresidencial ? 'none' : '';
  document.getElementById('graf-comp-b-cand').style.display = esPresidencial ? 'none' : '';
  document.getElementById('graf-comp-circ-fila').style.display = (esRegional && !esPresidencial) ? 'block' : 'none';
}

// Lista de candidatos de un partido para el selector de comparación. En
// elecciones regionales requiere `circFiltro` (la circunscripción elegida
// arriba) — sin ella no se listan candidatos, porque cada uno solo tiene
// sentido dentro de su propia región. Ordenados por NÚMERO de lista
// (numeroDeClaveCandidato), no alfabéticamente.
function poblarCandidatosComparacion(selectEl, pkey, circFiltro) {
  if (!pkey || !estado.agregados || !estado.agregados.metadata_partidos[pkey]) {
    selectEl.innerHTML = '<option value="">Total del partido</option>';
    selectEl.disabled = true;
    return;
  }
  const esRegional = !estado.agregados.es_nacional;
  if (esRegional && !circFiltro) {
    selectEl.innerHTML = '<option value="">Total del partido</option>' +
      '<option value="" disabled>— elige circunscripción arriba para ver candidatos —</option>';
    selectEl.disabled = false;
    return;
  }
  const meta = estado.agregados.metadata_partidos[pkey];
  let entradas = Object.entries(meta.candidatos || {});
  if (circFiltro) entradas = entradas.filter(([clave]) => clave.startsWith(`${circFiltro}||`));
  entradas.sort((a, b) => numeroDeClaveCandidato(a[0]) - numeroDeClaveCandidato(b[0]));
  const etiqueta = (clave, v) => {
    const n = numeroDeClaveCandidato(clave);
    return Number.isFinite(n) ? `${n} — ${v.nombre}` : v.nombre;
  };
  selectEl.innerHTML = '<option value="">Total del partido</option>' +
    entradas.map(([clave, v]) => `<option value="${clave}">${etiqueta(clave, v)}</option>`).join('');
  selectEl.disabled = false;
}

function renderGraficos() {
  const estadoEl = document.getElementById('graf-estado');
  if (!estado.agregados) {
    estadoEl.style.display = 'flex';
    estadoEl.textContent = 'Elige una elección para ver los gráficos.';
    document.querySelectorAll('.graf-bloque').forEach(b => b.style.display = 'none');
    return;
  }
  estadoEl.style.display = 'none';

  if (estado.graficoActivo === 'mesas') renderGraficoMesas();
  else if (estado.graficoActivo === 'concentracion') renderGraficoConcentracion();
  else if (estado.graficoActivo === 'ganador') renderGraficoGanador();
  else if (estado.graficoActivo === 'nulos') renderGraficoNulos();
}

// ── Distribución de mesas por votos (absoluto y relativo) ──────────

function renderGraficoMesas() {
  mostrarBloqueGrafico('graf-mesas');
  const pkey = estado.graficoPkey;
  const nombrePartido = pkey ? (estado.agregados.metadata_partidos[pkey] || {}).nombre_completo : null;
  document.getElementById('graf-mesas-partido').textContent = nombrePartido || '(elige un partido arriba)';

  const serie = pkey && (estado.agregados.series_graficos.mesas_por_votos || {})[pkey];
  if (!serie) {
    if (chartsActivos['canvas-mesas']) { chartsActivos['canvas-mesas'].destroy(); delete chartsActivos['canvas-mesas']; }
    return;
  }

  const color = (estado.agregados.metadata_partidos[pkey] || {}).color || '#4da6ff';
  const labels = serie.conteo.map((_, i) => {
    const a = serie.bordes[i], b = serie.bordes[i + 1];
    return `${Math.round(a)}–${Math.round(b)}`;
  });

  // Un solo histograma (las barras son el conteo absoluto); el eje derecho
  // es el mismo dato expresado en % de las mesas del partido — como % es
  // proporcional al conteo (factor 100/n_mesas), fijamos el máximo de
  // ambos ejes con ese mismo factor para que las grillas queden alineadas
  // y una sola barra se pueda leer en las dos unidades a la vez.
  const factorPct = serie.n_mesas > 0 ? 100 / serie.n_mesas : 0;
  const maxConteo = Math.max(...serie.conteo, 1) * 1.08;
  const escalaLogActiva = chartsActivos['canvas-mesas'] && chartsActivos['canvas-mesas'].options.scales.y.type === 'logarithmic';

  crearChart('canvas-mesas', {
    type: 'bar',
    data: {
      labels,
      datasets: [{
        label: `Mesas (n=${serie.n_mesas})`,
        data: serie.conteo,
        backgroundColor: color,
        yAxisID: 'y',
      }],
    },
    options: {
      ...OPCIONES_CHART_BASE,
      plugins: {
        ...OPCIONES_CHART_BASE.plugins,
        legend: { display: false },
        tooltip: {
          callbacks: {
            label: (ctx) => {
              const n = ctx.parsed.y;
              return `${n.toLocaleString('es-PE')} mesas (${(n * factorPct).toFixed(2)}%)`;
            },
          },
        },
      },
      scales: {
        x: { ...OPCIONES_CHART_BASE.scales.x, title: { display: true, text: 'Votos por mesa (bins log)', color: '#8892a4', font: { size: 10 } } },
        y: {
          ...OPCIONES_CHART_BASE.scales.y,
          type: escalaLogActiva ? 'logarithmic' : 'linear',
          position: 'left',
          min: escalaLogActiva ? undefined : 0,
          max: escalaLogActiva ? undefined : maxConteo,
          title: { display: true, text: 'Total de mesas (n)', color: '#8892a4', font: { size: 10 } },
        },
        y1: {
          ...OPCIONES_CHART_BASE.scales.y,
          type: escalaLogActiva ? 'logarithmic' : 'linear',
          position: 'right',
          min: escalaLogActiva ? undefined : 0,
          max: escalaLogActiva ? undefined : maxConteo * factorPct,
          grid: { drawOnChartArea: false },
          title: { display: true, text: '% de las mesas del partido', color: '#8892a4', font: { size: 10 } },
          ticks: { ...OPCIONES_CHART_BASE.scales.y.ticks, callback: (v) => `${v}%` },
        },
      },
    },
  });
}

document.getElementById('btn-escala-log-mesas').addEventListener('click', () => {
  const chart = chartsActivos['canvas-mesas'];
  if (!chart) return;
  const actual = chart.options.scales.y.type === 'logarithmic';
  const nuevoTipo = actual ? 'linear' : 'logarithmic';
  chart.options.scales.y.type = nuevoTipo;
  chart.options.scales.y1.type = nuevoTipo;
  // en log no se puede fijar un min/max compartido con sentido (log de 0
  // no existe) — se deja que Chart.js autoescale cada eje por su cuenta;
  // al volver a lineal se recalculan min/max proporcionales de nuevo.
  chart.options.scales.y.min = nuevoTipo === 'linear' ? 0 : undefined;
  chart.options.scales.y1.min = nuevoTipo === 'linear' ? 0 : undefined;
  if (nuevoTipo === 'linear') {
    const maxConteo = Math.max(...chart.data.datasets[0].data, 1) * 1.08;
    const nMesas = Number((estado.agregados.series_graficos.mesas_por_votos[estado.graficoPkey] || {}).n_mesas) || 1;
    chart.options.scales.y.max = maxConteo;
    chart.options.scales.y1.max = maxConteo * 100 / nMesas;
  } else {
    chart.options.scales.y.max = undefined;
    chart.options.scales.y1.max = undefined;
  }
  document.getElementById('btn-escala-log-mesas').textContent = actual ? 'Escala Y: lineal' : 'Escala Y: log';
  chart.update();
});

// ── Curva de concentración (Lorenz) ─────────────────────────────────

function renderGraficoConcentracion() {
  mostrarBloqueGrafico('graf-concentracion');
  const pkey = estado.graficoPkey;
  const nombrePartido = pkey ? (estado.agregados.metadata_partidos[pkey] || {}).nombre_completo : null;
  document.getElementById('graf-conc-partido').textContent = nombrePartido || '(elige un partido arriba)';
  const giniEl = document.getElementById('graf-conc-gini');

  const serie = pkey && (estado.agregados.series_graficos.concentracion || {})[pkey];
  if (!serie) {
    if (chartsActivos['canvas-concentracion']) { chartsActivos['canvas-concentracion'].destroy(); delete chartsActivos['canvas-concentracion']; }
    giniEl.textContent = '';
    return;
  }

  const color = (estado.agregados.metadata_partidos[pkey] || {}).color || '#4da6ff';
  const puntosLorenz = serie.x_pct_mesas.map((x, i) => ({ x: x * 100, y: serie.y_pct_votos[i] * 100 }));

  // Gini aproximado por trapecios sobre la curva de Lorenz ya muestreada
  // (0 = reparto perfectamente parejo entre mesas, 1 = todo el voto
  // concentrado en poquísimas mesas).
  let area = 0;
  for (let i = 1; i < serie.x_pct_mesas.length; i++) {
    const dx = serie.x_pct_mesas[i] - serie.x_pct_mesas[i - 1];
    area += dx * (serie.y_pct_votos[i] + serie.y_pct_votos[i - 1]) / 2;
  }
  const gini = 1 - 2 * area;
  giniEl.textContent = `Índice de concentración (Gini aprox.): ${gini.toFixed(3)} — más cerca de 1 = voto más concentrado en pocas mesas; más cerca de 0 = repartido parejo.`;

  crearChart('canvas-concentracion', {
    type: 'line',
    data: {
      datasets: [
        { label: 'Curva de Lorenz', data: puntosLorenz, borderColor: color, backgroundColor: color, pointRadius: 0, borderWidth: 2, tension: 0.15 },
        { label: 'Igualdad perfecta', data: [{ x: 0, y: 0 }, { x: 100, y: 100 }], borderColor: '#555b6e', borderDash: [5, 4], pointRadius: 0, borderWidth: 1 },
      ],
    },
    options: {
      ...OPCIONES_CHART_BASE,
      scales: {
        x: { ...OPCIONES_CHART_BASE.scales.x, type: 'linear', min: 0, max: 100, title: { display: true, text: '% acumulado de mesas (de menor a mayor votación)', color: '#8892a4', font: { size: 10 } } },
        y: { ...OPCIONES_CHART_BASE.scales.y, min: 0, max: 100, title: { display: true, text: '% acumulado de votos', color: '#8892a4', font: { size: 10 } } },
      },
    },
  });
}

// ── Ganador por polígono ────────────────────────────────────────────

function nodosNivelGrafico() {
  return (estado.agregados.niveles[estado.graficoNivel]) || {};
}

function totalPartidoEnNodo(nodo, pkey) {
  return (nodo.partidos && nodo.partidos[pkey] && nodo.partidos[pkey].total) || 0;
}

// Valor a comparar en un nodo: total del partido, o el de un candidato
// específico si se eligió uno en el selector "-cand" correspondiente.
function valorComparacion(nodo, pkey, candClave) {
  if (!pkey || !nodo || !nodo.partidos || !nodo.partidos[pkey]) return 0;
  const dp = nodo.partidos[pkey];
  if (candClave) return (dp.candidatos && dp.candidatos[candClave]) || 0;
  return dp.total || 0;
}

function etiquetaComparacion(pkey, candClave) {
  if (!pkey) return '';
  const meta = estado.agregados.metadata_partidos[pkey];
  if (!meta) return '';
  let nombre = meta.nombre_completo;
  if (candClave && meta.candidatos && meta.candidatos[candClave]) {
    nombre += ` — ${meta.candidatos[candClave].nombre}`;
  }
  return nombre;
}

function renderGraficoGanador() {
  mostrarBloqueGrafico('graf-ganador');
  const nodos = nodosNivelGrafico();
  const partidos = estado.agregados.metadata_partidos;
  const modoComparacion = estado.comparacionA && estado.comparacionB;
  document.getElementById('graf-campo-comparacion').style.display =
    estado.graficoActivo === 'ganador' ? 'block' : 'none';
  document.getElementById('canvas-ganador-cont').style.display = modoComparacion ? 'none' : 'block';
  document.getElementById('mapa-comparacion-cont').style.display = modoComparacion ? 'block' : 'none';

  if (modoComparacion) {
    renderMapaComparacion(nodos, partidos);
    return;
  }

  // Modo por defecto: ranking de "ganador" (mayor votación total) entre
  // TODOS los partidos, contando en cuántos polígonos gana cada uno.
  const conteo = {};
  Object.values(nodos).forEach(nodo => {
    let mejorP = null, mejorV = -1;
    for (const pkey of Object.keys(partidos)) {
      const v = totalPartidoEnNodo(nodo, pkey);
      if (v > mejorV) { mejorV = v; mejorP = pkey; }
    }
    if (mejorP && mejorV > 0) conteo[mejorP] = (conteo[mejorP] || 0) + 1;
  });
  const filas = Object.entries(conteo)
    .map(([pkey, n]) => ({ pkey, n, nombre: partidos[pkey].nombre_completo, color: partidos[pkey].color }))
    .sort((a, b) => b.n - a.n)
    .slice(0, 12);

  crearChart('canvas-ganador', {
    type: 'bar',
    data: {
      labels: filas.map(f => f.nombre),
      datasets: [{ data: filas.map(f => f.n), backgroundColor: filas.map(f => f.color) }],
    },
    options: {
      ...OPCIONES_CHART_BASE,
      indexAxis: 'y',
      plugins: { ...OPCIONES_CHART_BASE.plugins, legend: { display: false },
        title: { display: true, text: `${nombreNivelPlural(estado.graficoNivel)} ganados por partido`, color: '#e2e8f0', font: { size: 11 } } },
    },
  });
}

function nombreNivelPlural(nivel) {
  return { circunscripcion: 'circunscripciones', provincia: 'provincias', distrito: 'distritos' }[nivel] || nivel;
}

// Colorea cada polígono del nivel activo según cuál de los dos partidos/
// candidatos elegidos ganó ahí — en vez de un ranking agregado, se ve
// directamente el patrón geográfico de la comparación. La escala es
// divergente: blanco al centro (empate técnico) y sale hacia el color de
// A o de B según la diferencia de puntos porcentuales de voto válido en
// ese polígono, con más resolución cerca de 0% (donde una elección se
// decide) que lejos.
const COLOR_SIN_DATOS_COMPARACION = '#2a2d3e';
const UMBRAL_SIMILITUD_COLOR = 80; // distancia euclidiana en RGB (0-441) por debajo de la cual dos colores se consideran "muy parecidos"

function distanciaColor(hexA, hexB) {
  const [r1, g1, b1] = hexToRgb(hexA);
  const [r2, g2, b2] = hexToRgb(hexB);
  return Math.sqrt((r1 - r2) ** 2 + (g1 - g2) ** 2 + (b1 - b2) ** 2);
}

// Color derivado del matiz del fondo de la interfaz (--bg), rotado
// `offsetDeg` grados — usado para formar una tríada equidistante
// (fondo + 120° + 240°) cuando se comparan dos candidatos del MISMO
// partido, caso en el que no tiene sentido usar el color del partido
// dos veces.
function normalizarVec3(v) {
  const n = Math.sqrt(v[0] ** 2 + v[1] ** 2 + v[2] ** 2) || 1;
  return [v[0] / n, v[1] / n, v[2] / n];
}
function productoCruz(a, b) {
  return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
}

// Construye 2 colores que, junto con el color de fondo de la interfaz,
// forman un TRIÁNGULO EQUILÁTERO en el espacio RGB — el fondo es uno de
// los 3 vértices (no el centro). Se arma un plano perpendicular al eje
// acromático (r=g=b) que pasa por el fondo, y ahí se ubican los otros
// dos vértices con dos vectores del mismo largo separados 60° entre sí:
// con dos lados iguales (fondo→A y fondo→B) y 60° entre ellos, el tercer
// lado (A→B) sale automáticamente igual de largo (ley del coseno con
// cos 60° = 0.5) — sin necesidad de resolver el sistema de 3 distancias.
// Como el fondo es casi negro, el resultado geométrico puro también
// sale oscuro; para que sea legible se sube su luminosidad/saturación
// en HSL después, conservando el matiz que salió de la triangulación.
function triadaEquidistanteFondo() {
  const bg = hexToRgb('#0f1117');
  const eje = normalizarVec3([1, 1, 1]); // diagonal acromática del cubo RGB
  let u = productoCruz(eje, [0, 0, 1]);
  if (Math.hypot(...u) < 1e-6) u = productoCruz(eje, [0, 1, 0]);
  u = normalizarVec3(u);
  const w = normalizarVec3(productoCruz(eje, u)); // segundo eje del plano, ⟂ a u y al eje acromático

  const lado = 170; // largo de lado del triángulo, en unidades de canal RGB (0-255)
  const anguloBase = Math.PI / 2; // arbitrario: solo fija qué matiz de partida sale del primer vértice
  const vertice = (ang) => [
    bg[0] + lado * (Math.cos(ang) * u[0] + Math.sin(ang) * w[0]),
    bg[1] + lado * (Math.cos(ang) * u[1] + Math.sin(ang) * w[1]),
    bg[2] + lado * (Math.cos(ang) * u[2] + Math.sin(ang) * w[2]),
  ];
  const clamp = (v) => Math.max(0, Math.min(255, Math.round(v)));

  const aHex = (n) => clamp(n).toString(16).padStart(2, '0');
  const legible = ([r, g, b]) => {
    let [h, s, l] = rgbToHsl(clamp(r), clamp(g), clamp(b));
    s = Math.max(s, 0.65);
    l = Math.max(l, 0.55); // "menos oscuros si es necesario"
    const [r2, g2, b2] = hslToRgb(h, s, l);
    return `#${aHex(r2)}${aHex(g2)}${aHex(b2)}`; // hex, no rgb() — interpColor()/hexToRgb() esperan hex
  };

  return {
    colorA: legible(vertice(anguloBase)),
    colorB: legible(vertice(anguloBase + Math.PI / 3)), // 60° de separación
  };
}

// Decide los dos colores de la comparación:
//  - mismo partido (comparando candidatos): tríada equidistante en RGB
//    con el color de fondo de la interfaz como tercer vértice.
//  - partidos distintos con colores muy parecidos: se fuerza el color B
//    al opuesto (180° en HSL) del color A, mismo criterio que ya se usa
//    para el acento de outliers en el mapa principal.
//  - en cualquier otro caso: los colores propios de cada partido.
function coloresComparacion(partidos) {
  if (estado.comparacionA === estado.comparacionB) {
    return triadaEquidistanteFondo();
  }
  let colorA = (partidos[estado.comparacionA] || {}).color || '#4da6ff';
  let colorB = (partidos[estado.comparacionB] || {}).color || '#ff6b6b';
  if (distanciaColor(colorA, colorB) < UMBRAL_SIMILITUD_COLOR) {
    colorB = colorAcentoOutlier(colorA);
  }
  return { colorA, colorB };
}

// La escala de diferencia es RELATIVA a la dispersión real de la
// comparación activa, no a umbrales fijos (±1/3/5/10%): en diputados
// —muchos candidatos, votaciones bajas— las diferencias por polígono
// rara vez pasan de 1-2 puntos, así que una escala fija en % dejaba casi
// todo el mapa blanco sin contraste. En cambio, se toman los |diferencia|
// de TODOS los polígonos de la comparación activa y se usan sus propios
// percentiles (P50, P75, P92 y el máximo) como cortes — igual que la
// escala de deciles del mapa principal, pero aplicada a la diferencia
// A-B en vez de al valor absoluto. Así el color siempre se reparte sobre
// el rango real de esa comparación en particular, sea de 0.3 o de 30 pts.
const ANCLAS_T = [0, 0.3, 0.55, 0.78, 1];
const ANCLAS_DIFERENCIA_DEFECTO = [0, 1, 3, 5, 10]; // respaldo si hay muy poca variación para estimar percentiles

function calcularAnclasDiferencia(diffsPct) {
  const abs = diffsPct
    .filter(d => d !== null && d !== undefined)
    .map(Math.abs)
    .filter(d => d > 0)
    .sort((a, b) => a - b);
  if (abs.length < 5) return ANCLAS_DIFERENCIA_DEFECTO;
  const anclas = [0, percentil(abs, 0.5), percentil(abs, 0.75), percentil(abs, 0.92), abs[abs.length - 1]];
  for (let i = 1; i < anclas.length; i++) {
    if (anclas[i] <= anclas[i - 1]) anclas[i] = anclas[i - 1] + 0.01; // evita anclas degeneradas (empatadas)
  }
  return anclas;
}

function tDiferencia(diffAbsPct, anclas) {
  if (diffAbsPct <= 0) return 0;
  const max = anclas[anclas.length - 1];
  if (diffAbsPct >= max) return 1;
  for (let i = 1; i < anclas.length; i++) {
    if (diffAbsPct <= anclas[i]) {
      const x0 = anclas[i - 1], x1 = anclas[i];
      const y0 = ANCLAS_T[i - 1], y1 = ANCLAS_T[i];
      return y0 + (diffAbsPct - x0) / (x1 - x0) * (y1 - y0);
    }
  }
  return 1;
}

function colorDiferencia(diffPct, colorA, colorB, anclas) {
  if (diffPct === 0) return '#ffffff';
  const t = tDiferencia(Math.abs(diffPct), anclas || ANCLAS_DIFERENCIA_DEFECTO);
  return interpColor(diffPct > 0 ? colorA : colorB, t);
}

function formatoAnclaDiferencia(v) {
  if (v >= 10) return `${v.toFixed(0)}%`;
  if (v >= 1) return `${v.toFixed(1)}%`;
  return `${v.toFixed(2)}%`;
}

function renderEscalaComparacion(colorA, colorB, anclas) {
  const cont = document.getElementById('mapa-comparacion-escala');
  const [, a1, a2, a3, a4] = anclas;
  const cortes = [-a4, -a3, -a2, -a1, 0, a1, a2, a3, a4];
  const etiquetas = [
    `≥${formatoAnclaDiferencia(a4)}`, formatoAnclaDiferencia(a3), formatoAnclaDiferencia(a2), formatoAnclaDiferencia(a1),
    '0',
    formatoAnclaDiferencia(a1), formatoAnclaDiferencia(a2), formatoAnclaDiferencia(a3), `≥${formatoAnclaDiferencia(a4)}`,
  ];
  cont.innerHTML = cortes.map((c, i) => {
    const color = colorDiferencia(c, colorA, colorB, anclas);
    return `<div class="chip"><div class="sw" style="background:${color}"></div><div class="et">${etiquetas[i]}</div></div>`;
  }).join('');
}

async function renderMapaComparacion(nodos, partidos) {
  if (!mapComparacion) {
    mapComparacion = L.map('map-comparacion', { zoomControl: true, preferCanvas: true, attributionControl: false })
      .setView([-9.2, -75.0], 5.2);
  }
  if (capaComparacion) { mapComparacion.removeLayer(capaComparacion); capaComparacion = null; }

  const nivel = estado.graficoNivel;
  const { geojson, nombresPorClave } = await obtenerGeoDecodificada(nivel);
  const cfg = CONFIG_NIVEL[nivel];
  const { colorA, colorB } = coloresComparacion(partidos);
  const nombreA = etiquetaComparacion(estado.comparacionA, estado.comparacionACand);
  const nombreB = etiquetaComparacion(estado.comparacionB, estado.comparacionBCand);

  // Primera pasada: calcular la diferencia (pts. porcentuales de voto
  // válido) de cada polígono y, con esa distribución completa, derivar
  // los cortes de la escala — antes de dibujar nada, para que todos los
  // polígonos usen la misma escala ya calibrada a esta comparación.
  const diffPorClave = {};
  geojson.features.forEach(f => {
    const clave = f.properties[cfg.propClave];
    const nodo = nodos[clave];
    const a = valorComparacion(nodo, estado.comparacionA, estado.comparacionACand);
    const b = valorComparacion(nodo, estado.comparacionB, estado.comparacionBCand);
    if (a === 0 && b === 0) { diffPorClave[clave] = null; return; }
    const validos = Math.max(0, ((nodo && nodo.total_votantes) || 0) - ((nodo && nodo.votos_blanco) || 0) - ((nodo && nodo.votos_viciado) || 0));
    diffPorClave[clave] = validos > 0 ? (a - b) / validos * 100 : 0;
  });
  const anclas = calcularAnclasDiferencia(Object.values(diffPorClave));

  let ganaA = 0, ganaB = 0, empate = 0;

  capaComparacion = L.geoJSON(geojson, {
    style: f => {
      const diffPct = diffPorClave[f.properties[cfg.propClave]];
      if (diffPct === null) return { fillColor: COLOR_SIN_DATOS_COMPARACION, fillOpacity: 0.35, color: '#ffffff', weight: 0.5, opacity: 0.3 };
      return { fillColor: colorDiferencia(diffPct, colorA, colorB, anclas), fillOpacity: 0.85, color: '#ffffff', weight: 0.5, opacity: 0.4 };
    },
    onEachFeature: (f, layer) => {
      const clave = f.properties[cfg.propClave];
      const nodo = nodos[clave];
      const nombre = nombresPorClave[clave] || clave;
      const a = valorComparacion(nodo, estado.comparacionA, estado.comparacionACand);
      const b = valorComparacion(nodo, estado.comparacionB, estado.comparacionBCand);
      if (a || b) { if (a > b) ganaA++; else if (b > a) ganaB++; else empate++; }
      const diffPct = diffPorClave[clave] || 0;
      layer.bindTooltip(
        `<b>${nombre}</b><br>${nombreA}: ${a.toLocaleString('es-PE')}<br>${nombreB}: ${b.toLocaleString('es-PE')}` +
        `<br>diferencia: ${diffPct > 0 ? '+' : ''}${diffPct.toFixed(2)} pts.`,
        { sticky: true, className: 'info-tooltip' });
    },
  }).addTo(mapComparacion);

  // Si se eligió una circunscripción arriba (elecciones regionales, para
  // poder listar candidatos), autozoom a esa región en vez de al país
  // entero — es donde vive toda la data relevante de la comparación.
  if (estado.comparacionCirc) {
    const { geojson: geoCirc } = await obtenerGeoDecodificada('circunscripcion');
    const featCirc = geoCirc.features.find(f => f.properties.circunscripcion_slug === estado.comparacionCirc);
    if (featCirc) mapComparacion.fitBounds(L.geoJSON(featCirc).getBounds(), { maxZoom: 11 });
    else if (geojson.features.length) mapComparacion.fitBounds(capaComparacion.getBounds());
  } else if (geojson.features.length) {
    mapComparacion.fitBounds(capaComparacion.getBounds());
  }

  document.getElementById('mapa-comparacion-resumen').innerHTML =
    `<div><span style="color:${colorA}">⬤</span> ${nombreA}: ganó en ${ganaA} ${nombreNivelPlural(nivel)}</div>` +
    `<div><span style="color:${colorB}">⬤</span> ${nombreB}: ganó en ${ganaB} ${nombreNivelPlural(nivel)}</div>` +
    `<div>Empate: ${empate}</div>`;
  renderEscalaComparacion(colorA, colorB, anclas);

  setTimeout(() => mapComparacion.invalidateSize(), 60);
}

// ── Votos nulos y blancos ───────────────────────────────────────────

function renderGraficoNulos() {
  mostrarBloqueGrafico('graf-nulos');
  const nodos = nodosNivelGrafico();
  const { nombresPorClave } = cacheGeo[estado.graficoNivel] || { nombresPorClave: {} };

  let sumBlanco = 0, sumViciado = 0, sumVotantes = 0;
  const filas = Object.entries(nodos).map(([clave, nodo]) => {
    const blanco = nodo.votos_blanco || 0, viciado = nodo.votos_viciado || 0, votantes = nodo.total_votantes || 0;
    sumBlanco += blanco; sumViciado += viciado; sumVotantes += votantes;
    const pct = votantes > 0 ? (blanco + viciado) / votantes * 100 : 0;
    return { clave, nombre: nombresPorClave[clave] || clave, pct };
  }).filter(f => f.pct > 0).sort((a, b) => b.pct - a.pct).slice(0, 15);

  const pctNacional = sumVotantes > 0 ? (sumBlanco + sumViciado) / sumVotantes * 100 : 0;
  document.getElementById('graf-nulos-resumen').textContent =
    `Total ${nombreNivelPlural(estado.graficoNivel)}: ${(pctNacional).toFixed(2)}% de nulos+blancos sobre votantes ` +
    `(${sumBlanco.toLocaleString('es-PE')} blancos, ${sumViciado.toLocaleString('es-PE')} nulos, de ${sumVotantes.toLocaleString('es-PE')} votantes).`;

  crearChart('canvas-nulos', {
    type: 'bar',
    data: {
      labels: filas.map(f => f.nombre),
      datasets: [{ label: '% nulos + blancos', data: filas.map(f => f.pct), backgroundColor: '#e8b23a' }],
    },
    options: {
      ...OPCIONES_CHART_BASE,
      indexAxis: 'y',
      plugins: { ...OPCIONES_CHART_BASE.plugins, legend: { display: false },
        title: { display: true, text: `Top 15 ${nombreNivelPlural(estado.graficoNivel)} con más nulos+blancos`, color: '#e2e8f0', font: { size: 11 } } },
    },
  });

  renderMapaNulos(nodos);
}

// Coropleta de % nulos+blancos (misma metodología de deciles + P99 que el
// mapa principal) — vista adicional a la lista de arriba, para ver el
// patrón geográfico completo en vez de solo el top 15.
async function renderMapaNulos(nodos) {
  if (!mapNulos) {
    mapNulos = L.map('map-nulos', { zoomControl: true, preferCanvas: true, attributionControl: false })
      .setView([-9.2, -75.0], 5.2);
  }
  if (capaNulos) { mapNulos.removeLayer(capaNulos); capaNulos = null; }

  const nivel = estado.graficoNivel;
  const { geojson, nombresPorClave } = await obtenerGeoDecodificada(nivel);
  const cfg = CONFIG_NIVEL[nivel];
  const colorBase = '#e8b23a';
  const colorOutlier = colorAcentoOutlier(colorBase);

  const pctPorClave = {};
  Object.entries(nodos).forEach(([clave, nodo]) => {
    const votantes = nodo.total_votantes || 0;
    pctPorClave[clave] = votantes > 0 ? ((nodo.votos_blanco || 0) + (nodo.votos_viciado || 0)) / votantes * 100 : 0;
  });
  const valores = geojson.features.map(f => pctPorClave[f.properties[cfg.propClave]] || 0);
  const escala = calcularEscala(valores);

  capaNulos = L.geoJSON(geojson, {
    style: f => {
      const valor = pctPorClave[f.properties[cfg.propClave]] || 0;
      const outlier = esOutlier(valor, escala);
      return {
        fillColor: outlier ? colorOutlier : colorDecil(valor, escala, colorBase),
        fillOpacity: valor > 0 ? 0.82 : 0.08,
        color: '#ffffff',
        weight: outlier ? 1.4 : 0.5,
        opacity: outlier ? 1 : 0.4,
      };
    },
    onEachFeature: (f, layer) => {
      const clave = f.properties[cfg.propClave];
      const nombre = nombresPorClave[clave] || clave;
      const valor = pctPorClave[clave] || 0;
      layer.bindTooltip(`<b>${nombre}</b><br>${valor.toFixed(2)}% nulos + blancos`, { sticky: true, className: 'info-tooltip' });
    },
  }).addTo(mapNulos);

  if (geojson.features.length) mapNulos.fitBounds(capaNulos.getBounds());
  document.getElementById('mapa-nulos-resumen').textContent =
    `Coropleta de % nulos+blancos por ${nombreNivelPlural(nivel)} (deciles P10–P90; más intenso = mayor %; borde blanco = top 1%).`;

  setTimeout(() => mapNulos.invalidateSize(), 60);
}

// ── Eventos propios de la pestaña de gráficos ───────────────────────

document.querySelectorAll('#graf-tabs button').forEach(btn => {
  btn.addEventListener('click', () => {
    document.querySelectorAll('#graf-tabs button').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    estado.graficoActivo = btn.dataset.graf;
    const necesitaNivel = estado.graficoActivo === 'ganador' || estado.graficoActivo === 'nulos';
    const necesitaPartido = estado.graficoActivo === 'mesas' || estado.graficoActivo === 'concentracion';
    document.getElementById('graf-campo-nivel').style.display = necesitaNivel ? 'block' : 'none';
    document.getElementById('graf-campo-partido').style.display = necesitaPartido ? 'block' : 'none';
    document.getElementById('graf-campo-comparacion').style.display =
      estado.graficoActivo === 'ganador' ? 'block' : 'none';
    renderGraficos();
  });
});

document.querySelectorAll('#graf-nivel-tabs button').forEach(btn => {
  btn.addEventListener('click', () => {
    document.querySelectorAll('#graf-nivel-tabs button').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    estado.graficoNivel = btn.dataset.nivel;
    renderGraficos();
  });
});

document.getElementById('graf-sel-partido').addEventListener('change', (e) => {
  estado.graficoPkey = e.target.value || null;
  renderGraficos();
});

document.getElementById('graf-comp-a').addEventListener('change', (e) => {
  estado.comparacionA = e.target.value || null;
  estado.comparacionACand = null;
  poblarCandidatosComparacion(document.getElementById('graf-comp-a-cand'), estado.comparacionA, estado.comparacionCirc);
  renderGraficos();
});
document.getElementById('graf-comp-b').addEventListener('change', (e) => {
  estado.comparacionB = e.target.value || null;
  estado.comparacionBCand = null;
  poblarCandidatosComparacion(document.getElementById('graf-comp-b-cand'), estado.comparacionB, estado.comparacionCirc);
  renderGraficos();
});
document.getElementById('graf-comp-a-cand').addEventListener('change', (e) => {
  estado.comparacionACand = e.target.value || null;
  renderGraficos();
});
document.getElementById('graf-comp-b-cand').addEventListener('change', (e) => {
  estado.comparacionBCand = e.target.value || null;
  renderGraficos();
});
document.getElementById('graf-comp-circ').addEventListener('change', (e) => {
  estado.comparacionCirc = e.target.value || null;
  estado.comparacionACand = null;
  estado.comparacionBCand = null;
  poblarCandidatosComparacion(document.getElementById('graf-comp-a-cand'), estado.comparacionA, estado.comparacionCirc);
  poblarCandidatosComparacion(document.getElementById('graf-comp-b-cand'), estado.comparacionB, estado.comparacionCirc);
  renderGraficos();
});

// ══════════════════════════════════════════════════════════════════
// FASE 6 — PESTAÑA DE DETALLE
// Buscador independiente de Mapa y Gráficos, con selección EN CASCADA:
// al elegir una circunscripción, la lista de provincias/distritos se
// acota a las comprendidas en ella (y al elegir provincia, el listado de
// distritos se acota más todavía) — igual concepto que "circunscripción
// define candidatos" de la pestaña Mapa, pero aplicado a ir angostando
// niveles geográficos. La circunscripción elegida PERSISTE al cambiar de
// nivel (así se sigue bajando de circunscripción → provincia → distrito
// → local sin tener que volver a elegirla), y local sigue requiriéndola
// (single, obligatoria) porque sus datos se cargan perezosamente por
// circunscripción. Distrito/local sobre los mismos `niveles` de
// agregados_{eleccion}.json ya cargados. Al elegir un polígono se arma
// una ficha con el resumen (electores/participación/nulos/blancos) y el
// desglose completo partido→candidato (colapsable). Mesa a mesa queda
// para una vuelta posterior.
// ══════════════════════════════════════════════════════════════════

function datosNivelDetalle() {
  if (estado.detalleNivel === 'local') return estado.detalleDatosLocales || {};
  return (estado.agregados && estado.agregados.niveles[estado.detalleNivel]) || {};
}

async function cargarLocalesDetalle() {
  if (!estado.detalleCirc) { estado.detalleDatosLocales = null; return; }
  document.getElementById('detalle-estado-carga').textContent = `Cargando locales de ${estado.detalleCirc}…`;
  estado.detalleDatosLocales = await cargarLocalesRegion(estado.eleccionSlug, estado.detalleCirc);
  document.getElementById('detalle-estado-carga').textContent = '';
}

// Claves válidas del nivel activo dado el filtro en cascada elegido
// arriba (circunscripción / provincia / distrito) — null significa "sin
// acotar, se muestran todas". Provincia se deriva del ubigeo del distrito
// (los 4 primeros dígitos, igual que preparar_geometrias.py) en vez de
// depender de un mapa nuevo del backend. Local ya viene acotado por
// circunscripción de por sí (solo se cargan los de la circunscripción
// elegida); para acotarlo también por provincia/distrito hace falta el
// mapa opcional `distrito_por_local` (ubigeo de 6 dígitos por local_key)
// — si el paquete de datos es de antes de este cambio y no lo trae, se
// degrada solo a "acotado por circunscripción" sin romperse.
function clavesValidasDetalle(datos) {
  if (estado.detalleNivel === 'provincia' && estado.detalleCirc) {
    const mapa = estado.agregados.circunscripcion_por_provincia || {};
    return new Set(Object.keys(datos).filter(c => mapa[c] === estado.detalleCirc));
  }
  if (estado.detalleNivel === 'distrito') {
    if (estado.detalleProvincia) {
      return new Set(Object.keys(datos).filter(c => c.slice(0, 4) === estado.detalleProvincia));
    }
    if (estado.detalleCirc) {
      const mapa = estado.agregados.circunscripcion_por_distrito || {};
      return new Set(Object.keys(datos).filter(c => mapa[c] === estado.detalleCirc));
    }
  }
  if (estado.detalleNivel === 'local') {
    const distritoPorLocal = estado.agregados.distrito_por_local;
    if (distritoPorLocal) {
      if (estado.detalleDistrito) {
        return new Set(Object.keys(datos).filter(c => distritoPorLocal[c] === estado.detalleDistrito));
      }
      if (estado.detalleProvincia) {
        return new Set(Object.keys(datos).filter(c => (distritoPorLocal[c] || '').slice(0, 4) === estado.detalleProvincia));
      }
    }
  }
  return null;
}

// true si los datos cargados traen el mapa local_key → ubigeo de distrito
// (agregado opcionalmente por consolidar_nacional.py) — controla si se
// muestran los selectores de provincia/distrito para el nivel "local".
function tieneDistritoPorLocal() {
  return !!(estado.agregados && estado.agregados.distrito_por_local);
}

// Repuebla el selector de provincia (visible en nivel "distrito" y, si
// el paquete de datos trae `distrito_por_local`, también en "local"),
// acotado a la circunscripción elegida si hay una.
async function poblarProvinciasDetalle() {
  const sel = document.getElementById('detalle-sel-provincia');
  if (!estado.agregados) { sel.innerHTML = ''; return; }
  const { nombresPorClave } = await obtenerGeoDecodificada('provincia');
  const mapa = estado.agregados.circunscripcion_por_provincia || {};
  let claves = Object.keys(nombresPorClave);
  if (estado.detalleCirc) claves = claves.filter(c => mapa[c] === estado.detalleCirc);
  claves.sort((a, b) => (nombresPorClave[a] || a).localeCompare(nombresPorClave[b] || b, 'es-PE'));
  sel.innerHTML = '<option value="">— todas —</option>' +
    claves.map(c => `<option value="${c}">${nombresPorClave[c] || c}</option>`).join('');
  sel.value = estado.detalleProvincia || '';
}

// Repuebla el selector de distrito (visible solo en nivel "local", y solo
// si el paquete trae `distrito_por_local`) — acotado a la provincia
// elegida, o si no hay provincia, a la circunscripción elegida.
async function poblarDistritosDetalle() {
  const sel = document.getElementById('detalle-sel-distrito');
  if (!estado.agregados) { sel.innerHTML = ''; return; }
  const { nombresPorClave } = await obtenerGeoDecodificada('distrito');
  const mapaCirc = estado.agregados.circunscripcion_por_distrito || {};
  let claves = Object.keys(nombresPorClave);
  if (estado.detalleProvincia) claves = claves.filter(c => c.slice(0, 4) === estado.detalleProvincia);
  else if (estado.detalleCirc) claves = claves.filter(c => mapaCirc[c] === estado.detalleCirc);
  claves.sort((a, b) => (nombresPorClave[a] || a).localeCompare(nombresPorClave[b] || b, 'es-PE'));
  sel.innerHTML = '<option value="">— todos —</option>' +
    claves.map(c => `<option value="${c}">${nombresPorClave[c] || c}</option>`).join('');
  sel.value = estado.detalleDistrito || '';
}

// Muestra/oculta los selectores de acotado según el nivel activo, y
// ajusta el texto del de circunscripción (obligatorio en "local",
// opcional en el resto). Provincia se ofrece en "distrito" siempre y en
// "local" solo si los datos traen `distrito_por_local`; distrito solo en
// "local" y bajo la misma condición.
function actualizarFiltrosDetalle() {
  const nivel = estado.detalleNivel;
  const conDistritoPorLocal = tieneDistritoPorLocal();
  const label = document.getElementById('detalle-circ-label');
  document.getElementById('detalle-campo-circ').style.display = nivel === 'circunscripcion' ? 'none' : 'block';
  document.getElementById('detalle-campo-provincia').style.display =
    (nivel === 'distrito' || (nivel === 'local' && conDistritoPorLocal)) ? 'block' : 'none';
  document.getElementById('detalle-campo-distrito').style.display =
    (nivel === 'local' && conDistritoPorLocal) ? 'block' : 'none';
  document.getElementById('detalle-provincia-label').textContent = nivel === 'local'
    ? 'Provincia (acota la lista de locales)'
    : 'Provincia (acota la lista de distritos)';
  label.textContent = nivel === 'local'
    ? 'Circunscripción (necesaria para ver locales)'
    : 'Circunscripción (acota la lista de abajo)';
}

const LIMITE_LISTA_DETALLE = 300; // no renderizar de más en niveles con miles de locales sin filtrar

async function renderListaDetalle() {
  const listaEl = document.getElementById('detalle-lista');
  const cargaEl = document.getElementById('detalle-estado-carga');
  if (!estado.agregados) {
    listaEl.innerHTML = '';
    cargaEl.textContent = 'Elige una elección para empezar.';
    return;
  }
  if (estado.detalleNivel === 'local' && !estado.detalleCirc) {
    listaEl.innerHTML = '<div class="detalle-vacio">Elige una circunscripción arriba para ver sus locales.</div>';
    cargaEl.textContent = '';
    return;
  }

  const { nombresPorClave } = await obtenerGeoDecodificada(estado.detalleNivel);
  const datos = datosNivelDetalle();
  const clavesValidas = clavesValidasDetalle(datos);
  const q = estado.detalleBusqueda.trim().toLocaleLowerCase('es-PE');

  let filas = Object.keys(datos)
    .filter(clave => !clavesValidas || clavesValidas.has(clave))
    .map(clave => ({ clave, nombre: nombresPorClave[clave] || clave }));
  if (q) filas = filas.filter(f => f.nombre.toLocaleLowerCase('es-PE').includes(q));
  filas.sort((a, b) => a.nombre.localeCompare(b.nombre, 'es-PE'));

  cargaEl.textContent = `${filas.length} de ${Object.keys(datos).length} — clic para ver el detalle`;

  if (!filas.length) {
    listaEl.innerHTML = '<div class="detalle-vacio">Sin resultados.</div>';
    return;
  }

  const mostrar = filas.slice(0, LIMITE_LISTA_DETALLE);
  listaEl.innerHTML = mostrar.map(f => {
    const votantes = (datos[f.clave] || {}).total_votantes || 0;
    return `<div class="detalle-fila ${f.clave === estado.detalleClave ? 'activa' : ''}" data-clave="${f.clave}">
      <span class="df-nombre">${f.nombre}</span>
      <span class="df-sub">${votantes.toLocaleString('es-PE')} vot.</span>
    </div>`;
  }).join('') + (filas.length > LIMITE_LISTA_DETALLE
    ? `<div class="detalle-vacio">…y ${filas.length - LIMITE_LISTA_DETALLE} más — afina la búsqueda.</div>`
    : '');

  listaEl.querySelectorAll('.detalle-fila').forEach(el => {
    el.addEventListener('click', () => {
      estado.detalleClave = el.dataset.clave;
      estado.detallePartidosAbiertos.clear();
      listaEl.querySelectorAll('.detalle-fila').forEach(f => f.classList.toggle('activa', f === el));
      renderFichaDetalle();
    });
  });
}

async function renderFichaDetalle() {
  const placeholder = document.getElementById('detalle-placeholder');
  const ficha = document.getElementById('detalle-ficha');
  if (!estado.detalleClave || !estado.agregados) { placeholder.style.display = 'flex'; ficha.style.display = 'none'; return; }

  const { nombresPorClave } = await obtenerGeoDecodificada(estado.detalleNivel);
  const datos = datosNivelDetalle();
  const nodo = datos[estado.detalleClave];
  if (!nodo) { placeholder.style.display = 'flex'; ficha.style.display = 'none'; return; }

  placeholder.style.display = 'none';
  ficha.style.display = 'block';

  document.getElementById('detalle-ficha-nombre').textContent = nombresPorClave[estado.detalleClave] || estado.detalleClave;

  const electores = nodo.electores_habiles || 0;
  const votantes = nodo.total_votantes || 0;
  const blanco = nodo.votos_blanco || 0;
  const viciado = nodo.votos_viciado || 0;
  const validos = Math.max(0, votantes - blanco - viciado);
  const participacion = nodo['participacion_%'];

  document.getElementById('detalle-ficha-resumen').innerHTML = [
    ['Electores hábiles', electores.toLocaleString('es-PE')],
    ['Votantes', votantes.toLocaleString('es-PE')],
    ['Participación', participacion != null ? `${participacion.toFixed(1)}%` : '—'],
    ['Votos válidos', validos.toLocaleString('es-PE')],
    ['Blancos', `${blanco.toLocaleString('es-PE')} (${votantes > 0 ? (blanco / votantes * 100).toFixed(1) : '0.0'}%)`],
    ['Nulos', `${viciado.toLocaleString('es-PE')} (${votantes > 0 ? (viciado / votantes * 100).toFixed(1) : '0.0'}%)`],
  ].map(([etiqueta, valor]) => `<div class="detalle-stat"><div class="ds-valor">${valor}</div><div class="ds-etiqueta">${etiqueta}</div></div>`).join('');

  const metaPartidos = estado.agregados.metadata_partidos;
  // Presidencial no tiene desglose por candidato (la "lista" es la
  // plancha completa) — mismo criterio que el resto de la app.
  const esPresidencial = estado.eleccionSlug === 'presidencial';
  const filasPartidos = Object.entries(nodo.partidos || {})
    .map(([pkey, dp]) => ({ pkey, total: dp.total || 0, candidatos: dp.candidatos || {}, meta: metaPartidos[pkey] }))
    .filter(f => f.meta)
    .sort((a, b) => b.total - a.total);

  // Top 5: en Presidencial no hay desglose por candidato, así que se
  // rankean partidos (planchas); en el resto, candidatos individuales de
  // todos los partidos mezclados, con su número y partido como subtítulo.
  document.getElementById('detalle-top5-titulo').textContent = esPresidencial ? 'Top 5 partidos' : 'Top 5 candidatos';
  const top5 = esPresidencial
    ? filasPartidos.slice(0, 5).map(f => ({
        color: f.meta.color || '#4da6ff',
        nombre: f.meta.nombre_completo,
        sub: '',
        votos: f.total,
      }))
    : filasPartidos.flatMap(f => Object.entries(f.candidatos).map(([clave, votos]) => {
        const nombreCand = (f.meta.candidatos && f.meta.candidatos[clave] && f.meta.candidatos[clave].nombre) || clave;
        const n = numeroDeClaveCandidato(clave);
        return {
          color: f.meta.color || '#4da6ff',
          nombre: nombreCand,
          sub: `N.º ${Number.isFinite(n) ? n : '—'} · ${f.meta.abrev || f.meta.nombre_completo}`,
          votos,
        };
      })).sort((a, b) => b.votos - a.votos).slice(0, 5);

  document.getElementById('detalle-top5-body').innerHTML = top5.length
    ? top5.map((c, i) => {
        const pct = validos > 0 ? (c.votos / validos * 100) : 0;
        return `<tr class="dt5-fila">
          <td class="dt5-num">${i + 1}</td>
          <td>
            <div class="dt5-nombre-fila"><span class="dt5-swatch" style="background:${c.color}"></span><span class="dt5-nombre" title="${c.nombre}">${c.nombre}</span></div>
            ${c.sub ? `<div class="dt5-sub">${c.sub}</div>` : ''}
          </td>
          <td class="dt5-valor">${c.votos.toLocaleString('es-PE')}<span class="dt5-pct">${pct.toFixed(1)}%</span></td>
        </tr>`;
      }).join('')
    : '<tr><td class="dt5-vacio" colspan="3">Sin votos registrados en este polígono.</td></tr>';

  document.getElementById('detalle-ficha-partidos').innerHTML = filasPartidos.map(f => {
    const pct = validos > 0 ? (f.total / validos * 100) : 0;
    const abierto = estado.detallePartidosAbiertos.has(f.pkey);
    const candEntradas = esPresidencial ? [] : Object.entries(f.candidatos)
      .sort((a, b) => numeroDeClaveCandidato(a[0]) - numeroDeClaveCandidato(b[0]));
    const candidatosHtml = candEntradas.map(([clave, votos]) => {
      const nombreCand = (f.meta.candidatos && f.meta.candidatos[clave] && f.meta.candidatos[clave].nombre) || clave;
      const n = numeroDeClaveCandidato(clave);
      const pctCand = validos > 0 ? (votos / validos * 100) : 0;
      return `<div class="detalle-candidato-fila">
        <span class="detalle-candidato-num">${Number.isFinite(n) ? n : ''}</span>
        <span class="detalle-candidato-nombre">${nombreCand}</span>
        <span class="detalle-candidato-valor">${votos.toLocaleString('es-PE')} (${pctCand.toFixed(1)}%)</span>
      </div>`;
    }).join('');
    return `<div class="detalle-partido ${abierto ? 'abierto' : ''}" data-pkey="${f.pkey}">
      <div class="detalle-partido-header">
        <span class="detalle-partido-swatch" style="background:${f.meta.color || '#4da6ff'}"></span>
        <span class="detalle-partido-nombre">${f.meta.nombre_completo}</span>
        <span class="detalle-partido-valor">${f.total.toLocaleString('es-PE')} (${pct.toFixed(1)}%)</span>
        ${candEntradas.length ? '<span class="detalle-partido-caret">▶</span>' : ''}
      </div>
      ${candEntradas.length ? `<div class="detalle-candidatos">${candidatosHtml}</div>` : ''}
    </div>`;
  }).join('') || '<div class="detalle-vacio">Sin votos registrados en este polígono.</div>';

  document.querySelectorAll('#detalle-ficha-partidos .detalle-partido-header').forEach(el => {
    el.addEventListener('click', () => {
      const cont = el.parentElement;
      const pkey = cont.dataset.pkey;
      if (estado.detallePartidosAbiertos.has(pkey)) estado.detallePartidosAbiertos.delete(pkey);
      else estado.detallePartidosAbiertos.add(pkey);
      cont.classList.toggle('abierto');
    });
  });
}

document.querySelectorAll('#detalle-nivel-tabs button').forEach(btn => {
  btn.addEventListener('click', async () => {
    if (!estado.agregados) return;
    document.querySelectorAll('#detalle-nivel-tabs button').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    estado.detalleNivel = btn.dataset.nivel;
    // La circunscripción/provincia/distrito elegidos se mantienen al
    // cambiar de nivel — así la cascada "engancha" según se profundiza
    // circunscripción → provincia → distrito → local.
    estado.detalleClave = null;
    estado.detallePartidosAbiertos.clear();
    actualizarFiltrosDetalle();
    document.getElementById('detalle-sel-circ').value = estado.detalleCirc || '';
    const mostrarProvincia = document.getElementById('detalle-campo-provincia').style.display !== 'none';
    const mostrarDistrito = document.getElementById('detalle-campo-distrito').style.display !== 'none';
    if (mostrarProvincia) await poblarProvinciasDetalle();
    if (mostrarDistrito) await poblarDistritosDetalle();
    if (estado.detalleNivel === 'local') await cargarLocalesDetalle();
    renderFichaDetalle();
    renderListaDetalle();
  });
});

document.getElementById('detalle-sel-circ').addEventListener('change', async (e) => {
  estado.detalleCirc = e.target.value || null;
  // La provincia/distrito elegidos pueden ya no pertenecer a la nueva
  // circunscripción — se resetean y se repueblan.
  estado.detalleProvincia = null;
  estado.detalleDistrito = null;
  estado.detalleClave = null;
  estado.detallePartidosAbiertos.clear();
  const mostrarProvincia = document.getElementById('detalle-campo-provincia').style.display !== 'none';
  const mostrarDistrito = document.getElementById('detalle-campo-distrito').style.display !== 'none';
  if (mostrarProvincia) await poblarProvinciasDetalle();
  if (mostrarDistrito) await poblarDistritosDetalle();
  if (estado.detalleNivel === 'local') await cargarLocalesDetalle();
  renderFichaDetalle();
  renderListaDetalle();
});

document.getElementById('detalle-sel-provincia').addEventListener('change', async (e) => {
  estado.detalleProvincia = e.target.value || null;
  estado.detalleDistrito = null; // el distrito elegido puede ya no pertenecer a la nueva provincia
  estado.detalleClave = null;
  estado.detallePartidosAbiertos.clear();
  const mostrarDistrito = document.getElementById('detalle-campo-distrito').style.display !== 'none';
  if (mostrarDistrito) await poblarDistritosDetalle();
  renderFichaDetalle();
  renderListaDetalle();
});

document.getElementById('detalle-sel-distrito').addEventListener('change', (e) => {
  estado.detalleDistrito = e.target.value || null;
  estado.detalleClave = null;
  estado.detallePartidosAbiertos.clear();
  renderFichaDetalle();
  renderListaDetalle();
});

let detalleBusquedaTimeout = null;
document.getElementById('detalle-buscar').addEventListener('input', (e) => {
  estado.detalleBusqueda = e.target.value;
  clearTimeout(detalleBusquedaTimeout);
  detalleBusquedaTimeout = setTimeout(() => renderListaDetalle(), 150); // debounce liviano
});

// ══════════════════════════════════════════════════════════════════
// EVENTOS
// ══════════════════════════════════════════════════════════════════

document.getElementById('sel-eleccion').addEventListener('change', async (e) => {
  const slug = e.target.value;
  if (!slug) return;
  estado.eleccionSlug = slug;
  estado.pkey = null; estado.modo = 'total'; estado.circCandidato = null; estado.candidatoClave = null;
  estado.circLocal = null; estado.datosLocalesActuales = null; estado.nivelActivo = 'circunscripcion';
  estado.decilesSeleccionados.clear();
  estado.graficoPkey = null;
  estado.comparacionA = null; estado.comparacionACand = null;
  estado.comparacionB = null; estado.comparacionBCand = null;
  estado.comparacionCirc = null;
  estado.detalleNivel = 'circunscripcion'; estado.detalleCirc = null; estado.detalleProvincia = null; estado.detalleDistrito = null; estado.detalleDatosLocales = null;
  estado.detalleBusqueda = ''; estado.detalleClave = null; estado.detallePartidosAbiertos.clear();
  document.querySelectorAll('#nivel-tabs button').forEach(b => b.classList.toggle('active', b.dataset.nivel === 'circunscripcion'));
  document.querySelectorAll('#modo-tabs button').forEach(b => b.classList.toggle('active', b.dataset.modo === 'total'));
  document.querySelectorAll('#detalle-nivel-tabs button').forEach(b => b.classList.toggle('active', b.dataset.nivel === 'circunscripcion'));
  document.getElementById('campo-circ-candidato').style.display = 'none';
  document.getElementById('campo-candidato').style.display = 'none';
  document.getElementById('campo-circ-local').style.display = 'none';
  document.getElementById('detalle-sel-provincia').innerHTML = '';
  document.getElementById('detalle-sel-distrito').innerHTML = '';
  document.getElementById('detalle-buscar').value = '';
  actualizarFiltrosDetalle();

  // Presidencial no tiene desglose por candidato (la "lista" es el
  // partido/plancha) — no tiene sentido ofrecer "Candidato específico".
  const btnCandidato = document.querySelector('#modo-tabs button[data-modo="candidato"]');
  btnCandidato.style.display = slug === 'presidencial' ? 'none' : '';

  document.getElementById('estado-carga').textContent = 'Cargando elección…';
  const [, agregados] = await Promise.all([
    obtenerGeoDecodificada('circunscripcion'), // siempre se usa como base, cargarla de una vez
    cargarAgregados(slug),
  ]);
  estado.agregados = agregados;
  poblarPartidos();
  poblarPartidosGrafico();
  document.getElementById('estado-carga').textContent =
    `${agregados.eleccion} · ${agregados.tiene_preferencial ? 'con' : 'sin'} voto preferencial · ${agregados.es_nacional ? 'lista nacional' : 'por circunscripción'}`;
  renderTodo();
  poblarSelectoresComparacion();
  if (graficosVisibles()) renderGraficos();
  poblarCircunscripcionesGenerico(document.getElementById('detalle-sel-circ'));
  renderFichaDetalle();
  renderListaDetalle();
});

document.getElementById('sel-partido').addEventListener('change', (e) => {
  estado.pkey = e.target.value || null;
  estado.candidatoClave = null;
  estado.decilesSeleccionados.clear(); // la escala es otra con otro partido
  // En modo "candidato específico" hay que repoblar el selector con los
  // candidatos del NUEVO partido — antes solo se vaciaba y quedaba en
  // blanco hasta tocar algún otro control (circunscripción o modo), que
  // sí llamaban a poblarCandidatos().
  if (estado.modo === 'candidato' && estado.pkey) {
    poblarCandidatos();
  } else {
    document.getElementById('sel-candidato').innerHTML = '';
  }
  renderTodo();
});

document.querySelectorAll('#modo-tabs button').forEach(btn => {
  btn.addEventListener('click', async () => {
    document.querySelectorAll('#modo-tabs button').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    estado.modo = btn.dataset.modo;
    estado.candidatoClave = null;
    estado.decilesSeleccionados.clear(); // total vs. candidato tienen otra distribución de valores
    const esCandidato = estado.modo === 'candidato';
    document.getElementById('campo-candidato').style.display = esCandidato ? 'block' : 'none';
    document.getElementById('campo-circ-candidato').style.display =
      (esCandidato && estado.agregados && !estado.agregados.es_nacional) ? 'block' : 'none';
    if (esCandidato && estado.pkey) {
      if (estado.agregados.es_nacional) poblarCandidatos();
      else poblarCircunscripcionesGenerico(document.getElementById('sel-circ-candidato'));
    }
    await sincronizarNivelLocal();
    renderTodo();
  });
});

document.getElementById('sel-circ-candidato').addEventListener('change', async (e) => {
  estado.circCandidato = e.target.value || null;
  estado.candidatoClave = null;
  poblarCandidatos();
  await sincronizarNivelLocal();
  renderTodo();
});

document.getElementById('sel-candidato').addEventListener('change', (e) => {
  estado.candidatoClave = e.target.value || null;
  estado.decilesSeleccionados.clear(); // cada candidato tiene su propia distribución de valores
  renderTodo();
});

document.querySelectorAll('#nivel-tabs button').forEach(btn => {
  btn.addEventListener('click', async () => {
    if (!estado.agregados) return;
    document.querySelectorAll('#nivel-tabs button').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    estado.nivelActivo = btn.dataset.nivel;
    document.getElementById('aviso-local').style.display = 'none';

    if (estado.nivelActivo === 'local') {
      await sincronizarNivelLocal();
    } else {
      document.getElementById('campo-circ-local').style.display = 'none';
    }
    renderTodo();
  });
});

document.getElementById('sel-circ-local').addEventListener('change', async (e) => {
  estado.circLocal = e.target.value || null;
  await cargarLocalesParaNivelActivo();
  renderTodo();
});

document.querySelectorAll('#orden-tabs button').forEach(btn => {
  btn.addEventListener('click', () => {
    document.querySelectorAll('#orden-tabs button').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    estado.metrica = btn.dataset.orden;
    renderTodo();
  });
});

document.querySelectorAll('.tab-btn').forEach(btn => {
  btn.addEventListener('click', () => {
    document.querySelectorAll('.tab-btn').forEach(b => b.classList.remove('active'));
    document.querySelectorAll('.vista').forEach(v => v.classList.remove('active'));
    btn.classList.add('active');
    document.getElementById('vista-' + btn.dataset.vista).classList.add('active');
    if (map) setTimeout(() => map.invalidateSize(), 50);
    if (btn.dataset.vista === 'graficos') setTimeout(() => renderGraficos(), 50);
  });
});

function graficosVisibles() {
  const v = document.getElementById('vista-graficos');
  return v && v.classList.contains('active');
}

// ══════════════════════════════════════════════════════════════════
// INIT
// ══════════════════════════════════════════════════════════════════

const ORDEN_ELECCIONES = ['presidencial', 'diputados', 'senado_nacional', 'senado_regional', 'parlamento_andino'];

function poblarSelectorEleccion() {
  const sel = document.getElementById('sel-eleccion');
  const elecciones = [...MANIFEST.elecciones].sort((a, b) => {
    const ia = ORDEN_ELECCIONES.indexOf(a.slug), ib = ORDEN_ELECCIONES.indexOf(b.slug);
    return (ia === -1 ? 999 : ia) - (ib === -1 ? 999 : ib);
  });
  sel.innerHTML = '<option value="">— Elige una elección —</option>' +
    elecciones.map(e => `<option value="${e.slug}">${e.nombre}</option>`).join('');
}

// Sin mapa base: no se usa ningún tile server (evita depender de una
// clave de API de terceros como CARTO). Se ven directamente los polígonos
// de las circunscripciones/provincias/distritos sobre fondo oscuro.
map = L.map('map', { zoomControl: true, preferCanvas: true, attributionControl: false }).setView([-9.2, -75.0], 5.2);

poblarSelectorEleccion();
