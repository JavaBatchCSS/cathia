/* CathIA : cache des bibliothèques (versions figées) et page en « réseau d'abord » (toujours à jour, utilisable hors ligne ensuite) */
const V='cathia-v1',LIBS=['https://cdn.jsdelivr.net/npm/three@0.128.0/build/three.min.js','https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/controls/OrbitControls.js','https://cdn.jsdelivr.net/npm/@jscad/modeling@2.12.3/dist/jscad-modeling.min.js'];
self.addEventListener('install',e=>{self.skipWaiting();e.waitUntil(caches.open(V).then(c=>c.addAll(LIBS)).catch(()=>{}))});
self.addEventListener('activate',e=>e.waitUntil(caches.keys().then(ks=>Promise.all(ks.filter(k=>k!=V).map(k=>caches.delete(k)))).then(()=>self.clients.claim())));
self.addEventListener('fetch',e=>{const u=new URL(e.request.url);if(e.request.method!='GET')return;
 if(u.hostname=='cdn.jsdelivr.net'){e.respondWith(caches.match(e.request).then(r=>r||fetch(e.request).then(x=>{const c=x.clone();caches.open(V).then(ca=>ca.put(e.request,c));return x})));return}
 if(u.origin==location.origin&&(u.pathname.endsWith('/')||u.pathname.endsWith('.html'))){e.respondWith(fetch(e.request).then(x=>{const c=x.clone();caches.open(V).then(ca=>ca.put(e.request,c));return x}).catch(()=>caches.match(e.request)))}});
