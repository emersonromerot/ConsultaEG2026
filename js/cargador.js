/*
 * cargador.js — Fase 3: mecanismo de carga perezosa sin servidor.
 *
 * Un HTML abierto con doble clic (file://) NO puede usar fetch()/XHR para
 * traer JSON externo — el navegador lo bloquea por CORS. Pero SÍ puede
 * cargar <script src="..."> normalmente, incluso agregado dinámicamente
 * en tiempo de ejecución. Por eso todos los datos (geometría y votos)
 * se generaron como archivos .js que hacen `window.ALGO = {...}` en vez
 * de archivos .json — este archivo es el que decide cuándo pedir cada uno.
 */

const _scriptsCargados = new Set();

function cargarScript(src) {
  if (_scriptsCargados.has(src)) return Promise.resolve();
  return new Promise((resolve, reject) => {
    const el = document.createElement('script');
    el.src = src;
    el.onload = () => { _scriptsCargados.add(src); resolve(); };
    el.onerror = () => reject(new Error('No se pudo cargar: ' + src));
    document.head.appendChild(el);
  });
}

/** nivel: 'circunscripciones' | 'provincias' | 'distritos' | 'locales' */
function cargarGeometria(nivel) {
  const varName = 'GEO_' + nivel.toUpperCase();
  if (window[varName]) return Promise.resolve(window[varName]);
  return cargarScript(`data/geo/${nivel}.js`).then(() => window[varName]);
}

function cargarAgregados(eleccionSlug) {
  const varName = 'AGREGADOS_' + eleccionSlug.toUpperCase();
  if (window[varName]) return Promise.resolve(window[varName]);
  return cargarScript(`data/elecciones/${eleccionSlug}/agregados.js`).then(() => window[varName]);
}

function cargarLocalesRegion(eleccionSlug, circSlug) {
  const varName = `LOCALES_${eleccionSlug.toUpperCase()}_${circSlug.toUpperCase()}`;
  if (window[varName]) return Promise.resolve(window[varName]);
  return cargarScript(`data/elecciones/${eleccionSlug}/locales/${circSlug}.js`)
    .then(() => window[varName]);
}

/** Convierte un objeto TopoJSON (con un único "object" adentro, que es
 * como los genera preparar_geometrias.py) a GeoJSON usable por Leaflet.
 * No asume el nombre del objeto ("data" por defecto en la librería
 * topojson de Python) — lo detecta dinámicamente. */
function topojsonAGeojson(topologia) {
  const nombreObjeto = Object.keys(topologia.objects)[0];
  return topojson.feature(topologia, topologia.objects[nombreObjeto]);
}
