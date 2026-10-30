/* CathIA — Apps Script
 * - sert l'application (index.html)
 * - connexion : Google (principal) ou adresse e-mail + code à 6 chiffres (publication seulement) ; seule l'adresse e-mail est conservée
 * - les projets des utilisateurs sont enregistrés dans LEUR Drive (par l'application, avec leur jeton Google) ;
 *   ce script ne stocke que les modèles publiés dans la bibliothèque communautaire
 * - bibliothèques : modèles vérifiés (dossier géré à la main) et modèles partagés (publiés depuis l'application)
 * Propriétés du script à renseigner (Paramètres du projet) : GOOGLE_CLIENT_ID, GOOGLE_CLIENT_SECRET, APP_URL (adresse /exec publique)
 */
var VERIFIED_ID = '1FRT--8pMdDFSbnKZCKeTk-FrSmkgWkS9';   // modèles vérifiés
var COMMUNITY_ID = '1z741rZqj5pWHSftU9uxWpoQBRAY8FEaE';  // modèles partagés (communauté)
var SESSION_JOURS = 60;
var TAILLE_MAX = 45 * 1024 * 1024;
var EXT_OK = /\.(html|xhtml|svg|pdf|json|jpg|png)$/i;
var GSCOPE = 'openid email https://www.googleapis.com/auth/drive.file';

function doGet(e) {
  var p = (e && e.parameter) || {};
  if (p.code && p.state) return googleReturn_(p);
  return HtmlService.createHtmlOutputFromFile('index')
    .setTitle('CathIA')
    .addMetaTag('viewport', 'width=device-width, initial-scale=1')
    .setXFrameOptionsMode(HtmlService.XFrameOptionsMode.ALLOWALL);
}
/* API JSON pour la version hébergée ailleurs (GitHub Pages) : l'application appelle ces fonctions par POST */
var API_ = ['appInfo', 'authRequest', 'authVerify', 'authMe', 'authLogout', 'googleStart', 'googleClaim', 'listLibrary', 'readLibraryItem', 'readByLink', 'getThumb', 'publishModel'];
function doPost(e) {
  var out;
  try {
    var q = JSON.parse(e.postData.contents), fn = String(q.fn);
    if (API_.indexOf(fn) < 0) throw new Error('Fonction inconnue.');
    out = { result: ({ appInfo: appInfo, authRequest: authRequest, authVerify: authVerify, authMe: authMe, authLogout: authLogout, googleStart: googleStart, googleClaim: googleClaim, listLibrary: listLibrary, readLibraryItem: readLibraryItem, readByLink: readByLink, getThumb: getThumb, publishModel: publishModel })[fn].apply(null, q.args || []) };
  } catch (err) { out = { error: String(err && err.message || err) }; }
  return ContentService.createTextOutput(JSON.stringify(out)).setMimeType(ContentService.MimeType.JSON);
}
function appUrl_() { return props_().getProperty('APP_URL') || ScriptApp.getService().getUrl(); }
function appInfo() {
  var p = props_(), ok = p.getProperty('GOOGLE_CLIENT_ID') && p.getProperty('GOOGLE_CLIENT_SECRET');
  return { url: appUrl_(), gid: ok ? p.getProperty('GOOGLE_CLIENT_ID') : '' };
}
/* source complète de l'application (pour le téléchargement hors ligne) */
function appSource() { return HtmlService.createHtmlOutputFromFile('index').getContent(); }

/* ------------------------------ utilitaires ------------------------------ */
function props_() { return PropertiesService.getScriptProperties(); }
function salt_() {
  var p = props_(), s = p.getProperty('SALT');
  if (!s) { s = Utilities.getUuid() + Utilities.getUuid(); p.setProperty('SALT', s); }
  return s;
}
function sha_(s) {
  var d = Utilities.computeDigest(Utilities.DigestAlgorithm.SHA_256, salt_() + '|' + s, Utilities.Charset.UTF_8);
  return d.map(function (b) { return ('0' + (b & 0xff).toString(16)).slice(-2); }).join('');
}
function clean_(n) {
  n = String(n || '').replace(/[\\\/:*?"<>|\u0000-\u001f]+/g, ' ').replace(/\s+/g, ' ').trim().replace(/\.+$/, '').slice(0, 80);
  return n || 'Projet';
}

/* ------------------------------ sessions ------------------------------ */
function session_(email) {
  var tok = (Utilities.getUuid() + Utilities.getUuid()).replace(/-/g, ''), lock = LockService.getScriptLock();
  lock.waitLock(10000);
  try {
    var p = props_(), now = Date.now(), all = p.getProperties();
    Object.keys(all).forEach(function (key) {
      if (key.indexOf('T_') === 0) { try { if (JSON.parse(all[key]).x < now) p.deleteProperty(key); } catch (e) { p.deleteProperty(key); } }
    });
    p.setProperty('T_' + sha_(tok), JSON.stringify({ e: email, x: now + SESSION_JOURS * 86400000 }));
  } finally { lock.releaseLock(); }
  return tok;
}
function user_(tok) {
  var raw = tok && props_().getProperty('T_' + sha_(tok));
  if (!raw) throw new Error('Session expirée : reconnectez-vous.');
  var o = JSON.parse(raw);
  if (o.x < Date.now()) { props_().deleteProperty('T_' + sha_(tok)); throw new Error('Session expirée : reconnectez-vous.'); }
  return o.e;
}
function authMe(tok) { try { return user_(tok); } catch (e) { return null; } }
function authLogout(tok) { if (tok) props_().deleteProperty('T_' + sha_(tok)); return true; }

/* ------------------------------ connexion par e-mail (code à 6 chiffres) ------------------------------ */
function authRequest(email) {
  email = String(email || '').trim().toLowerCase();
  if (!/^[^\s@<>,;:"]+@[^\s@<>,;:"]+\.[^\s@<>,;:"]{2,}$/.test(email) || email.length > 120) throw new Error('Adresse e-mail invalide.');
  var cache = CacheService.getScriptCache(), k = sha_(email);
  var n = +(cache.get('rl_' + k) || 0);
  if (n >= 5) throw new Error('Trop de demandes pour cette adresse : réessayez dans une heure.');
  if (MailApp.getRemainingDailyQuota() < 5) throw new Error('Limite quotidienne d’envoi de codes atteinte : réessayez demain.');
  var code = String(100000 + (parseInt(sha_(Utilities.getUuid()).slice(0, 8), 16) % 900000));
  cache.put('otp_' + k, JSON.stringify({ h: sha_(code + '|' + email), n: 0 }), 600);
  cache.put('rl_' + k, String(n + 1), 3600);
  MailApp.sendEmail({
    to: email, name: 'CathIA',
    subject: 'Votre code de connexion CathIA : ' + code,
    body: 'Bonjour,\n\nVotre code de connexion à CathIA est : ' + code + '\n\nIl est valable 10 minutes. Votre adresse e-mail n’est utilisée que pour retrouver et répertorier vos modèles 3D. Si vous n’êtes pas à l’origine de cette demande, ignorez ce message.\n\nCathIA — conception de mobilier en froissartage'
  });
  return { ok: true };
}
function authVerify(email, code) {
  email = String(email || '').trim().toLowerCase(); code = String(code || '').replace(/\D/g, '');
  var cache = CacheService.getScriptCache(), k = sha_(email), raw = cache.get('otp_' + k);
  if (!raw) throw new Error('Code expiré ou inconnu : demandez un nouveau code.');
  var o = JSON.parse(raw);
  if (o.n >= 5) { cache.remove('otp_' + k); throw new Error('Trop d’essais : demandez un nouveau code.'); }
  if (o.h !== sha_(code + '|' + email)) { o.n++; cache.put('otp_' + k, JSON.stringify(o), 600); throw new Error('Code incorrect.'); }
  cache.remove('otp_' + k);
  return { token: session_(email), email: email };
}

/* ------------------------------ connexion Google ------------------------------
 * Fenêtre pop-up : Google renvoie ici (?code=&state=). Le serveur échange le code, vérifie l'e-mail, ouvre une session
 * et dépose le résultat en cache 2 minutes pour que l'application le récupère. Le jeton d'accès Drive de l'utilisateur
 * (1 h, scope drive.file : seulement les fichiers créés par CathIA) n'est jamais conservé ici : il sert au navigateur de l'utilisateur. */
function googleStart(hint) {
  var p = props_(), cid = p.getProperty('GOOGLE_CLIENT_ID');
  if (!cid || !p.getProperty('GOOGLE_CLIENT_SECRET')) throw new Error('Connexion Google non configurée.');
  var state = Utilities.getUuid().replace(/-/g, '') + Utilities.getUuid().replace(/-/g, '');
  CacheService.getScriptCache().put('gn_' + state, '1', 600);
  var q = { client_id: cid, redirect_uri: appUrl_(), response_type: 'code', scope: GSCOPE, state: state, access_type: 'online' };
  if (!hint) q.prompt = 'select_account';
  if (hint && /^[^\s@]+@[^\s@]+$/.test(hint)) q.login_hint = hint;
  return { url: 'https://accounts.google.com/o/oauth2/v2/auth?' + Object.keys(q).map(function (k) { return k + '=' + encodeURIComponent(q[k]); }).join('&'), state: state };
}
function googleReturn_(p) {
  var cache = CacheService.getScriptCache(), k = 'gc_' + p.state, ok = false, msg = 'Connexion Google refusée.';
  try {
    if (!cache.get('gn_' + p.state)) throw new Error('Demande expirée : recommencez.');
    cache.remove('gn_' + p.state);
    var pr = props_(), cid = pr.getProperty('GOOGLE_CLIENT_ID');
    var r = UrlFetchApp.fetch('https://oauth2.googleapis.com/token', { method: 'post', muteHttpExceptions: true, payload: { code: p.code, client_id: cid, client_secret: pr.getProperty('GOOGLE_CLIENT_SECRET'), redirect_uri: appUrl_(), grant_type: 'authorization_code' } });
    var t = JSON.parse(r.getContentText());
    if (r.getResponseCode() !== 200 || !t.id_token || !t.access_token) throw new Error('Google a refusé la connexion.');
    if (String(t.scope || '').indexOf('auth/drive.file') < 0) throw new Error('Il faut autoriser l’accès aux fichiers créés par CathIA pour enregistrer dans votre Drive.');
    var c = JSON.parse(Utilities.newBlob(Utilities.base64DecodeWebSafe(t.id_token.split('.')[1])).getDataAsString());
    if (c.aud !== cid || (c.iss !== 'https://accounts.google.com' && c.iss !== 'accounts.google.com') || !c.email || c.email_verified !== true) throw new Error('Identité Google non vérifiée.');
    var mail = String(c.email).toLowerCase();
    cache.put(k, JSON.stringify({ token: session_(mail), email: mail, at: t.access_token, exp: Date.now() + (+t.expires_in || 3600) * 1000 }), 120);
    ok = true;
  } catch (err) { msg = String(err.message || err); cache.put(k, JSON.stringify({ err: msg }), 120); }
  var html = '<!DOCTYPE html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><style>body{font:16px system-ui,sans-serif;text-align:center;padding:48px 20px;color:#222}</style></head><body><h2>' +
    (ok ? 'Connexion réussie' : 'Connexion impossible') + '</h2><p>' + (ok ? 'Vous pouvez fermer cette fenêtre et retourner dans CathIA.' : msg.replace(/[<>&]/g, '')) +
    '</p><script>setTimeout(function(){try{window.top.close()}catch(e){}},1200)<\/script></body></html>';
  return HtmlService.createHtmlOutput(html).setTitle('CathIA');
}
/* l'application interroge régulièrement jusqu'à ce que la connexion soit terminée */
function googleClaim(state) {
  var cache = CacheService.getScriptCache(), k = 'gc_' + String(state || ''), raw = cache.get(k);
  if (!raw) return null;
  cache.remove(k);
  return JSON.parse(raw);
}

/* ------------------------------ bibliothèques ------------------------------ */
function limite_(email, cle, max) {
  var c = CacheService.getScriptCache(), k = 'q_' + cle + '_' + sha_(email), n = +(c.get(k) || 0);
  if (n >= max) throw new Error('Trop d’envois récents : réessayez dans quelques heures.');
  c.put(k, String(n + 1), 21600);
}
function fiche_(f) {
  f = f || {};
  var u = (f.u || []).filter(function (x) { return ['louveteaux', 'louvettes', 'scouts', 'guides'].indexOf(x) >= 0; });
  var p = (f.par || []).filter(function (x) { return x === 'jeunes' || x === 'chefs'; });
  return { type: String(f.type || '').slice(0, 40), tx: String(f.tx || '').slice(0, 40), dif: Math.max(0, Math.min(5, +f.dif || 0)), u: u, par: p, h: Math.max(0, Math.min(999, +f.h || 0)), desc: String(f.desc || '').slice(0, 240) };
}
function meta_(folder) {
  try { var o = JSON.parse(folder.getDescription() || '{}'); return o && typeof o === 'object' ? o : {}; } catch (e) { return {}; }
}
function enfantDe_(item, parentId) {
  var it = item.getParents();
  while (it.hasNext()) if (it.next().getId() === parentId) return true;
  return false;
}
function contenu_(dossier) {
  var it = dossier.getFiles(), best = null;
  while (it.hasNext()) {
    var f = it.next(), n = f.getName();
    if (/\.cathia\.html$/i.test(n)) return f.getBlob().getDataAsString('UTF-8');
    if (!best && /\.(html|xhtml)$/i.test(n)) best = f;
  }
  if (!best) throw new Error('Aucun modèle 3D (.html) dans ce projet.');
  return best.getBlob().getDataAsString('UTF-8');
}
/* écrit les fichiers publiés ; remplace les marqueurs @@CATHIA_*@@ des .html/.svg par l'identifiant du dossier, l'e-mail et l'adresse de l'application */
function ecrire_(dossier, files, email) {
  var total = 0, app = appUrl_();
  files.forEach(function (f) {
    var n = clean_(f.n);
    if (!EXT_OK.test(n)) throw new Error('Type de fichier non accepté : ' + n);
    total += String(f.b || '').length * 0.75;
    if (total > TAILLE_MAX) throw new Error('Projet trop volumineux.');
  });
  files.forEach(function (f) {
    var n = clean_(f.n), old = dossier.getFilesByName(n), mime = f.m || 'application/octet-stream', blob;
    if (/\.(html|xhtml|svg)$/i.test(n)) {
      var txt = Utilities.newBlob(Utilities.base64Decode(f.b)).getDataAsString('UTF-8')
        .replace(/@@CATHIA_ID@@/g, dossier.getId()).replace(/@@CATHIA_EMAIL@@/g, email).replace(/@@CATHIA_APP@@/g, app);
      blob = Utilities.newBlob(txt, mime, n);
    } else blob = Utilities.newBlob(Utilities.base64Decode(f.b), mime, n);
    while (old.hasNext()) old.next().setTrashed(true);
    dossier.createFile(blob);
  });
}
function biblio_(which) { return DriveApp.getFolderById(which === 'verified' ? VERIFIED_ID : COMMUNITY_ID); }
function listLibrary(which) {
  if (which !== 'verified' && which !== 'community') throw new Error('Bibliothèque inconnue.');
  var cache = CacheService.getScriptCache(), ck = 'lib2_' + which, c = cache.get(ck);
  if (c) return JSON.parse(c);
  var root = biblio_(which), out = [], it = root.getFolders();
  while (it.hasNext()) {
    var f = it.next(), n = f.getName();
    if (/\.cathia$/i.test(n)) out.push({ id: f.getId(), name: n.replace(/\.cathia$/i, ''), fiche: meta_(f).fiche || null, t: f.getLastUpdated().getTime() });
  }
  var fi = root.getFiles();
  while (fi.hasNext()) {
    var g = fi.next(), gn = g.getName();
    if (/\.(html|xhtml|htm)$/i.test(gn)) out.push({ id: g.getId(), name: gn.replace(/\.(cathia\.)?(html|xhtml|htm)$/i, ''), fiche: null, t: g.getLastUpdated().getTime() });
  }
  out.sort(function (a, b) { return a.name.localeCompare(b.name); });
  out = out.slice(0, 300);
  try { cache.put(ck, JSON.stringify(out), 60); } catch (e) {}
  return out;
}
function readLibraryItem(which, id) {
  if (which !== 'verified' && which !== 'community') throw new Error('Bibliothèque inconnue.');
  var rid = biblio_(which).getId(), f = null;
  try { f = DriveApp.getFolderById(id); } catch (e) {}
  if (f) { if (!enfantDe_(f, rid)) throw new Error('Modèle introuvable dans cette bibliothèque.'); return contenu_(f); }
  var g = DriveApp.getFileById(id);
  if (!enfantDe_(g, rid)) throw new Error('Modèle introuvable dans cette bibliothèque.');
  return g.getBlob().getDataAsString('UTF-8');
}
/* ouverture par lien (bouton « Ouvrir avec CathIA » d'un fichier .html) : les bibliothèques sont publiques ;
 * un projet privé est dans le Drive de son auteur : l'application le lit elle-même avec le jeton Google de l'utilisateur. */
function readByLink(tok, id) {
  var f;
  try { f = DriveApp.getFolderById(id); } catch (e) { throw new Error('Ce projet est privé : connectez-vous avec Google pour l’ouvrir.'); }
  if (enfantDe_(f, VERIFIED_ID) || enfantDe_(f, COMMUNITY_ID)) return { name: f.getName().replace(/\.cathia$/i, ''), html: contenu_(f), mine: false };
  throw new Error('Ce projet est privé : connectez-vous avec Google pour l’ouvrir.');
}
/* vignette d'un modèle (image enregistrée dans son dossier) : chargée à la demande, jamais préchargée */
function getThumb(which, id) {
  if (which !== 'verified' && which !== 'community') return '';
  var cache = CacheService.getScriptCache(), ck = 'th_' + id, c = cache.get(ck);
  if (c !== null) return c.trim();
  var f;
  try { f = DriveApp.getFolderById(id); } catch (e) { return ''; }
  if (!enfantDe_(f, biblio_(which).getId())) return '';
  var it = f.getFilesByName('vignette.jpg'), out = '';
  if (it.hasNext()) out = 'data:image/jpeg;base64,' + Utilities.base64Encode(it.next().getBlob().getBytes());
  if (out.length < 95000) try { cache.put(ck, out || ' ', 3600); } catch (e) {}
  return out;
}
function publishModel(tok, name, files, fiche) {
  var email = user_(tok), base = clean_(name), nom = base + '.cathia', root = biblio_('community'), h = sha_(email);
  limite_(email, 'pub', 10);
  var lock = LockService.getScriptLock();
  lock.waitLock(15000);
  try {
    var f = null, k = 1, it;
    for (;;) {
      it = root.getFoldersByName(nom);
      if (!it.hasNext()) { f = root.createFolder(nom); break; }
      var g = it.next();
      if (meta_(g).o === h) { f = g; break; }
      k++; nom = base + ' (' + k + ').cathia';
      if (k > 50) throw new Error('Trop de modèles portent ce nom : choisissez-en un autre.');
    }
    f.setDescription(JSON.stringify({ fiche: fiche_(fiche), o: h }));
    ecrire_(f, files || [], email);
    CacheService.getScriptCache().remove('lib2_community');
    return { id: f.getId(), name: nom.replace(/\.cathia$/i, '') };
  } finally { lock.releaseLock(); }
}
/* à lancer une fois depuis l'éditeur : déclenche la demande d'autorisation des services utilisés */
function autorisation() { UrlFetchApp.fetch('https://oauth2.googleapis.com/'); MailApp.getRemainingDailyQuota(); DriveApp.getRootFolder(); return 'ok'; }
