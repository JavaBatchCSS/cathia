/* =====================  Compte, fiche, vignettes, bibliothèques, plans SVG (version Google Apps Script)  ===================== */
const CLOUD={id:'',app:'',gid:'',src:null};
const FTYPES=['Tente','Vaisselier','Table de prépa','Table','Assise / banc','Étagère / rangement','Établi','Oratoire','Mât','Portique','Séchoir / porte-sac','Autre'];
const FDIF=['Très facile','Facile','Moyen','Difficile','Très difficile'];
const FUNI=[['louveteaux','Louveteaux'],['louvettes','Louvettes'],['scouts','Scouts'],['guides','Guides']];
const FPAR=[['jeunes','Réalisable par les jeunes'],['chefs','Réalisable par les chefs']];
const ALL4=['louveteaux','louvettes','scouts','guides'],JC=['jeunes','chefs'];
const LIBF={etabli:{type:'Établi',dif:3,u:['scouts','guides'],par:JC},banc:{type:'Assise / banc',dif:1,u:ALL4,par:JC},bancdos:{type:'Assise / banc',dif:2,u:['scouts','guides'],par:JC},bancdiag:{type:'Assise / banc',dif:2,u:['scouts','guides'],par:JC},fauteuil:{type:'Assise / banc',dif:4,u:['scouts','guides'],par:['chefs']},table:{type:'Table',dif:3,u:['scouts','guides'],par:JC},prepa:{type:'Table de prépa',dif:3,u:['scouts','guides'],par:JC},cuisine:{type:'Table de prépa',dif:4,u:['scouts','guides'],par:['chefs']},etagere:{type:'Étagère / rangement',dif:3,u:['scouts','guides'],par:JC},vaisselier:{type:'Vaisselier',dif:3,u:['scouts','guides'],par:JC},feu:{type:'Table',dif:2,u:ALL4,par:JC}};
const LIBCAT=[['Tables et plans de travail',['table','prepa','cuisine','feu']],['Rangements',['etagere','vaisselier']],['Assises',['banc','bancdos','bancdiag','fauteuil']],['Outils et ateliers',['etabli']]];
const ftype=f=>f&&(f.type=='Autre'&&f.tx?f.tx:f.type)||'';
const ficheLine=f=>f?[ftype(f),f.dif?'niveau '+f.dif+' ('+FDIF[f.dif-1]+')':'',(f.u||[]).length==4?'toutes unités':(f.u||[]).map(u=>(FUNI.find(x=>x[0]==u)||[0,u])[1]).join(', '),(f.par||[]).length==2?'jeunes ou chefs':(f.par||[]).map(p=>p=='jeunes'?'par les jeunes':'par les chefs').join('')].filter(Boolean).join(' · '):'';
const gasUrl=()=>{try{return !!(window.google&&google.script&&google.script.url)}catch(e){return false}};

/* ----- appels serveur et connexion (Google : vos projets sont enregistrés dans VOTRE Drive) ----- */
const AUTH={tok:null,email:null,at:null,exp:0};
try{AUTH.tok=localStorage.getItem('cathia.tok');AUTH.email=localStorage.getItem('cathia.mail');AUTH.at=localStorage.getItem('cathia.at');AUTH.exp=+localStorage.getItem('cathia.exp')||0}catch(e){}
const gcall=(fn,...a)=>inGas()?new Promise((ok,ko)=>google.script.run.withSuccessHandler(ok).withFailureHandler(e=>ko(new Error((e&&e.message)||String(e))))[fn](...a))
 :fetch(CFG.api,{method:'POST',body:JSON.stringify({fn,args:a})}).then(r=>r.json()).then(j=>{if(j.error)throw new Error(j.error);return j.result},e=>{throw new Error(/Failed to fetch|NetworkError/i.test(e.message)?'Serveur CathIA injoignable (connexion internet ?)':e.message)});
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const driveTok=()=>AUTH.at&&AUTH.exp>Date.now()+60000?AUTH.at:null;
function authSet(tok,email,at,exp){AUTH.tok=tok;AUTH.email=email;if(at!==undefined){AUTH.at=at||null;AUTH.exp=at?exp:0}if(!tok){AUTH.at=null;AUTH.exp=0}
 try{if(tok){localStorage.setItem('cathia.tok',tok);localStorage.setItem('cathia.mail',email||'')}else localStorage.removeItem('cathia.tok');if(AUTH.at){localStorage.setItem('cathia.at',AUTH.at);localStorage.setItem('cathia.exp',String(AUTH.exp))}else{localStorage.removeItem('cathia.at');localStorage.removeItem('cathia.exp')}}catch(e){}
 if(typeof bsGo=='function'&&document.body.classList.contains('hm'))bsGo(fsec)}
async function authCheck(){if(!gasOK()||!AUTH.tok)return;try{const m=await gcall('authMe',AUTH.tok);if(!m)authSet(null,AUTH.email);else if(m!=AUTH.email)authSet(AUTH.tok,m)}catch(e){}}
function cloudInit(){if(!gasOK())return;
 gcall('appInfo').then(r=>{CLOUD.app=inGas()?r.url||'':location.origin+location.pathname;CLOUD.gid=r.gid||'';CLOUD.gh=!!r.gh}).catch(()=>{});authCheck();
 if(!inGas()){const p=new URLSearchParams(location.search).get('p');if(p){history.replaceState(null,'',location.pathname);openByLink(p)}}
 else if(gasUrl())google.script.url.getLocation(loc=>{const q=loc&&loc.parameter||{},one=v=>Array.isArray(v)?v[0]:v;if(q.p)openByLink(one(q.p))})}
const AUTH_NOTE='Votre adresse e-mail est conservée uniquement pour retrouver et répertorier vos modèles 3D. Aucun nom, aucun numéro de téléphone, pas de mot de passe.';
function authDlg(then,why){const err=t=>{const e=$('#au_e');if(e){e.textContent=t||'';e.style.display=t?'block':'none'}};
 if(why=='drive'&&!CLOUD.gid){msg('La connexion Google n’est pas encore activée sur cette version : téléchargez votre projet à la place.',8000);return}
 const s1=()=>{modal(`<h3>Connexion</h3><p class="mu">${AUTH_NOTE}</p>${CLOUD.gid?`<p class="mu">Avec Google, vos projets sont enregistrés dans <b>votre propre Drive</b> (dossier « CathIA »). CathIA n’a accès qu’aux fichiers qu’elle y crée.</p><button class="p" id="au_g" style="width:100%;margin:6px 0">Continuer avec Google</button>`:''}${why=='drive'?'':`<details${CLOUD.gid?'':' open'} style="margin-top:8px"><summary class="mu" style="cursor:pointer">Sans compte Google : recevoir un code par e-mail (publication de modèles seulement)</summary><label style="margin-top:6px">Adresse e-mail<input id="au_m" type="email" autocomplete="email" placeholder="votre@adresse.fr" value="${esc(AUTH.email||'')}"></label><div class="r" style="margin-top:6px"><button id="au_s">Recevoir le code</button></div></details>`}<p id="au_e" style="color:var(--er);display:none"></p><div class="r"><button id="au_x">Annuler</button></div>`);
  $('#au_x').onclick=closeMd;if($('#au_g'))$('#au_g').onclick=()=>googleLogin(then);
  const m=$('#au_m');if(m){const go=async()=>{const em=m.value.trim().toLowerCase();if(!/^\S+@\S+\.\S{2,}$/.test(em))return err('Adresse e-mail invalide.');$('#au_s').disabled=true;$('#au_s').textContent='Envoi…';try{await gcall('authRequest',em);s2(em)}catch(e){err(e.message);$('#au_s').disabled=false;$('#au_s').textContent='Recevoir le code'}};$('#au_s').onclick=go;m.onkeydown=e=>{if(e.key=='Enter'){e.preventDefault();go()}}}};
 const s2=em=>{modal(`<h3>Entrez le code</h3><p class="mu">Un code à 6 chiffres a été envoyé à <b>${esc(em)}</b> (pensez à regarder les courriers indésirables). Il est valable 10 minutes.</p><label>Code<input id="au_c" inputmode="numeric" maxlength="6" autocomplete="one-time-code" style="font-size:22px;letter-spacing:.3em;text-align:center"></label><p id="au_e" style="color:var(--er);display:none"></p><div class="r"><button class="p" id="au_v">Valider</button><button id="au_b">Changer d’adresse</button></div>`);
  const c=$('#au_c');c.focus();$('#au_b').onclick=s1;const go=async()=>{if(c.value.replace(/\D/g,'').length!=6)return err('Le code comporte 6 chiffres.');$('#au_v').disabled=true;try{const r=await gcall('authVerify',em,c.value);authSet(r.token,r.email);closeMd();msg('Connecté : '+r.email);if(then)then()}catch(e){err(e.message);$('#au_v').disabled=false}};$('#au_v').onclick=go;c.oninput=()=>{if(c.value.replace(/\D/g,'').length==6)go()};c.onkeydown=e=>{if(e.key=='Enter'){e.preventDefault();go()}}};
 s1()}
async function googleLogin(then){try{const r=await gcall('googleStart',AUTH.email||''),w=window.open(r.url,'cathia_google','width=500,height=680');
  if(!w)throw new Error('La fenêtre Google a été bloquée : autorisez les fenêtres pop-up pour ce site, puis réessayez.');
  modal(`<h3>Connexion Google en cours…</h3><p class="mu">Terminez la connexion dans la fenêtre Google qui vient de s’ouvrir. Cette fenêtre se fermera toute seule.</p><div class="r"><button id="gw_x">Annuler</button></div>`);let stop=false,gone=0;$('#gw_x').onclick=()=>{stop=true;closeMd()};const t0=Date.now();
  while(!stop&&Date.now()-t0<300000){await sleep(1500);let c=null;try{c=await gcall('googleClaim',r.state)}catch(x){}
   if(c){if(c.err)throw new Error(c.err);authSet(c.token,c.email,c.at,c.exp);try{w.close()}catch(_){}closeMd();msg('Connecté avec Google : '+c.email);if(then)then();return}
   try{gone=w.closed?gone+1:0}catch(_){}if(gone>=4){stop=true;closeMd();msg('Connexion Google annulée.')}}
  if(!stop)throw new Error('Délai dépassé : recommencez.')}catch(x){closeMd();msg(x.message,9000)}}
function authOut(){const t=AUTH.tok;authSet(null,AUTH.email);if(t)gcall('authLogout',t).catch(()=>{});msg('Déconnecté.')}
const needAuth=then=>AUTH.tok?then():authDlg(then);

/* ----- fichier HTML / XHTML qui n'a pas été créé par CathIA : lecture seule, dans un cadre isolé ----- */
let FV=null;
function closeForeign(){if(!FV)return;if(FV.url)URL.revokeObjectURL(FV.url);FV.el.remove();FV=null}
function openForeign(t,name){closeForeign();const xml=/^\s*<\?xml/i.test(t)||/\.xht(ml)?$/i.test(name||''),el=document.createElement('div');
 el.style.cssText='position:fixed;inset:0;z-index:80;background:var(--bg);display:flex;flex-direction:column';
 el.innerHTML=`<div style="display:flex;gap:10px;align-items:center;flex-wrap:wrap;padding:10px 14px;background:var(--pn);border-bottom:1px solid var(--bd)"><span style="flex:1;min-width:240px"><b>Lecture seule.</b> « ${esc(name||'modèle')} » n’a pas été créé par CathIA : c’est un modèle qui ne peut pas être modifié ici. Vous pouvez le consulter, ou le télécharger.</span><button id="fv_d">Télécharger</button><button class="p" id="fv_c">Fermer</button></div><iframe id="fv_f" sandbox="allow-scripts allow-popups" style="flex:1;border:0;background:#fff;width:100%"></iframe>`;
 document.body.appendChild(el);FV={el,url:null};const fr_=el.querySelector('#fv_f');
 if(xml){FV.url=URL.createObjectURL(new Blob([t],{type:'application/xhtml+xml'}));fr_.src=FV.url}else fr_.srcdoc=t;
 el.querySelector('#fv_c').onclick=closeForeign;el.querySelector('#fv_d').onclick=()=>save((name||'modele')+(/\.(x?html?)$/i.test(name||'')?'':'.html'),t,xml?'application/xhtml+xml':'text/html');
 msg('Modèle en lecture seule : il n’a pas été créé par CathIA et ne peut pas être modifié ici.',7000)}

/* ----- origine d'un projet ouvert : une copie de travail, l'original n'est jamais modifié ----- */
function cloudOrigin(o,name){CLOUD.src=o||null;CLOUD.id=o&&o.id&&!o.from?o.id:'';if(o&&o.from)msg('« '+name+' » est ouvert comme copie de travail : l’original n’est jamais modifié. Enregistrez-le dans vos projets pour le garder.',9000)}

/* ----- vignette du projet (image qui le représente le mieux) ----- */
function projThumb(){const sol=objs.filter(o=>o.m&&o.m.visible!==false&&o.m.geometry);if(!sol.length)return'';
 const r=new THREE.WebGLRenderer({antialias:true,preserveDrawingBuffer:true});try{r.setSize(360,270);const s2=new THREE.Scene();s2.background=new THREE.Color(0xf4f5f7);s2.add(new THREE.AmbientLight(0xffffff,.75));const dl=new THREE.DirectionalLight(0xffffff,.8);dl.position.set(500,-800,1000);s2.add(dl);
  const g=new THREE.Group();s2.add(g);const box=new THREE.Box3();
  sol.forEach(o=>{o.m.updateMatrixWorld(true);const mat=o.m.material.clone();mat.emissive.set(0);mat.transparent=false;mat.opacity=1;const m=new THREE.Mesh(o.m.geometry,mat);m.matrixAutoUpdate=false;m.matrix.copy(o.m.matrixWorld);m.matrixWorldNeedsUpdate=true;g.add(m);box.expandByObject(m)});
  const c=box.getCenter(new THREE.Vector3()),sp=box.getBoundingSphere(new THREE.Sphere()),cam2=new THREE.PerspectiveCamera(35,360/270,10,400000);cam2.up.set(0,0,1);const d=new THREE.Vector3(.75,-1,.6).normalize(),dist=sp.radius/Math.tan(35*Math.PI/360)*1.05;cam2.position.copy(c).addScaledVector(d,dist);cam2.lookAt(c);
  r.render(s2,cam2);return r.domElement.toDataURL('image/jpeg',.82)}finally{r.dispose();try{r.forceContextLoss()}catch(e){}}}

/* ----- plans SVG : chaque fichier .svg embarque ses données, il peut être rouvert et modifié dans CathIA ----- */
const hasPlan=()=>{ensurePages();return pages.some(p=>p.views.length||p.shots.length||p.bg)||views.length>0||shots.length>0};
function planSvgs(s){if(!hasPlan())return[];savePage();const out=[],n=pages.filter(p=>p.views.length||p.shots.length||p.bg).length;
 pages.forEach((p,i)=>{if(!(p.views.length||p.shots.length||p.bg))return;const svg=withPage(i,svgDoc),pd={name:p.name,bg:p.bg,made:true,views:p.views.map(w=>({id:w.id,k:w.k,x:w.x,y:w.y,s:w.s,nm:w.nm,only:w.only||null,dv:w.dv||null})),dims:p.dims,texts:p.texts,shots:p.shots,nom:p.nom},
  js=JSON.stringify({app:'cathia',v:1,ref:CLOUD.id||'',titre:meta.titre,page:pd}).replace(/\]\]>/g,']]\\u003e');
  out.push({n:s+'.plan'+(n>1?'-'+(out.length+1):'')+'.svg',svg:svg.replace(/^(<svg[^>]*>)/,'$1<metadata id="cathia-plan"><![CDATA['+js+']]></metadata>')})});return out}
function svgBody(t){const root=/<svg\b([^>]*)>/i.exec(t);if(!root)return null;const vb=/viewBox="([^"]+)"/i.exec(root[1]),w=vb?vb[1].trim().split(/[\s,]+/).map(Number):null;
 let inner=t.slice(root.index+root[0].length,t.lastIndexOf('</svg>'));inner=inner.replace(/<script[\s\S]*?<\/script>/gi,'').replace(/<metadata[\s\S]*?<\/metadata>/gi,'').replace(/\son\w+="[^"]*"/gi,'').replace(/\son\w+='[^']*'/gi,'').replace(/(xlink:href|href)="javascript:[^"]*"/gi,'');
 const W=w&&w[2]>0?w[2]:420;return'<g transform="scale('+(420/W).toFixed(5)+')">'+inner+'</g>'}
function importSvg(t,name){const m=/<metadata id="cathia-plan"><!\[CDATA\[([\s\S]*?)\]\]><\/metadata>/.exec(t);ensurePages();savePage();
 if(m){let d;try{d=JSON.parse(m[1])}catch(e){return msg('Ce plan CathIA est illisible.',6000)}if(!d||d.app!='cathia'||!d.page)return msg('Ce plan CathIA est illisible.',6000);
  if(!solids().length)return msg('Ouvrez d’abord le modèle 3D (le fichier .html du même projet), puis ce plan : il s’applique au modèle ouvert.',9000);
  const p=d.page;pages.push({name:p.name||'Plan',made:true,bg:p.bg,views:p.views||[],dims:p.dims||[],texts:p.texts||[],shots:p.shots||[],nom:Object.assign(newNom(),p.nom||{})});
  const all=pages.flatMap(x=>x.views),ad=pages.flatMap(x=>x.dims),at=pages.flatMap(x=>x.texts);vid=Math.max(vid,...all.map(w=>w.id+1));did=Math.max(did,...ad.map(x=>x.id+1));tid=Math.max(tid,...at.map(x=>x.id+1))}
 else{const body=svgBody(t);if(!body)return msg('Fichier SVG invalide.',6000);pages.push({name:(name||'Dessin').replace(/\.svg$/i,''),made:true,bg:body,views:[],dims:[],texts:[],shots:[],nom:{...newNom(),show:false}})}
 planOn=true;tabClick('Mise en plan');loadPage(pages.length-1);msg(m?'Plan ajouté : vous pouvez le modifier comme les autres pages.':'Dessin SVG importé comme fond de page : ajoutez-y vues, cotes et textes.',7000)}

/* ----- fiche de caractérisation (recherche pertinente) ----- */
function ficheDlg(title,pub,then){const f=meta.fiche||{},u=f.u||[],p=f.par||[];
 const F=[{k:'n',l:'Nom du projet',t:'txt',v:meta.titre||'Mon projet'},{k:'type',l:'Type d’installation',t:'sel',v:f.type||'',o:[['','— choisir —'],...FTYPES]},{k:'tx',l:'Si « Autre » : précisez',t:'txt',v:f.tx||''},{k:'dif',l:'Niveau de difficulté',t:'sel',v:f.dif||'',o:[['','— choisir —'],...FDIF.map((l,i)=>[i+1,(i+1)+' – '+l])]},
  {k:'i1',t:'info',l:'<b>À quelles unités est-il destiné ?</b>'},...FUNI.map(([a,b])=>({k:'u_'+a,l:b,t:'chk',v:u.includes(a)})),{k:'i2',t:'info',l:'<b>Qui peut le construire ?</b>'},...FPAR.map(([a,b])=>({k:'p_'+a,l:b,t:'chk',v:p.includes(a)})),
  {k:'h',l:'Durée de construction estimée (heures, 0 = inconnue)',t:'num',v:f.h||0},{k:'d',l:'Description courte (matériel, conseils…)',t:'txt',v:f.desc||''}];
 if(!pub)F.push({k:'pdf',l:'Inclure aussi le PDF du plan',t:'chk',v:false});
 F.push({k:'inf',t:'info',l:pub?'<b>Public :</b> le modèle (3D, plan, vignette) sera enregistré dans le dépôt GitHub de CathIA, dans un dossier à votre identifiant anonyme, et visible et notable par tous dans « Modèles partagés ». Ni votre nom ni votre adresse e-mail ne sont publiés.':'Un dossier « nom.cathia » est créé dans VOTRE Drive (CathIA › nom.cathia) : modèle 3D (.html lisible dans tout navigateur), plan (.svg) et vignette. Privé : vous seul y avez accès.'});
 dlg(title,F,v=>{if(!v.n.trim())throw new Error('Donnez un nom au projet.');const fi={type:v.type||'',tx:v.tx||'',dif:+v.dif||0,u:FUNI.filter(([a])=>v['u_'+a]).map(x=>x[0]),par:FPAR.filter(([a])=>v['p_'+a]).map(x=>x[0]),h:+v.h||0,desc:String(v.d||'').slice(0,240)};
  if(pub){if(!fi.type)throw new Error('Choisissez le type d’installation.');if(fi.type=='Autre'&&!fi.tx.trim())throw new Error('Précisez le type d’installation.');if(!fi.dif)throw new Error('Choisissez le niveau de difficulté.');if(!fi.u.length)throw new Error('Choisissez au moins une unité.');if(!fi.par.length)throw new Error('Indiquez qui peut le construire (jeunes, chefs).')}
  then(v.n.trim(),fi,!!v.pdf)},pub?'Partager':'Enregistrer')}
async function projFiles(name,withPdf){const s=slug(name),F=[{n:s+'.cathia.html',m:'text/html',t:viewerHTML(true)}];
 try{const th=projThumb();if(th)F.push({n:'vignette.jpg',m:'image/jpeg',b:th.split(',')[1]})}catch(e){console.warn('vignette',e)}
 for(const x of planSvgs(s))F.push({n:x.n,m:'image/svg+xml',t:x.svg});
 if(withPdf&&hasPlan())F.push({n:s+'.plan.pdf',m:'application/pdf',b:await b64of(await planPdfBlob())});return F}
const b64of=d=>new Promise(ok=>{const f=new FileReader();f.onload=()=>ok(String(f.result).split(',')[1]);f.readAsDataURL(d instanceof Blob?d:new Blob([d]))});
const fillPh=(t,id)=>t.replace(/@@CATHIA_ID@@/g,id||'').replace(/@@CATHIA_EMAIL@@/g,AUTH.email||'').replace(/@@CATHIA_APP@@/g,CLOUD.app||'');
const withB=async(F,id)=>{const o=[];for(const f of F)o.push({n:f.n,m:f.m,b:f.b||await b64of(new Blob([id!=null?fillPh(f.t,id):f.t],{type:f.m}))});return o};
async function planPdfBlob(px=2000){const P=[];for(const s of allDocs()){const c=await svgCanvas(s,px),b=await toBlob(c,'image/jpeg',.9);P.push({u:new Uint8Array(await b.arrayBuffer()),w:c.width,h:c.height})}return pdfFromJpegs(P,1190.55,841.89)}

/* ----- Drive de l'utilisateur (API REST, jeton Google côté navigateur : le serveur ne voit jamais ces fichiers) ----- */
const DAPI='https://www.googleapis.com/drive/v3/files',DUP='https://www.googleapis.com/upload/drive/v3/files',qq=s=>String(s).replace(/\\/g,'\\\\').replace(/'/g,"\\'");
async function dr(url,o={}){const t=driveTok();if(!t)throw new Error('DRIVE_EXP');const r=await fetch(url,{...o,headers:{Authorization:'Bearer '+t,...(o.headers||{})}});
 if(r.status==401){AUTH.at=null;throw new Error('DRIVE_EXP')}if(!r.ok){let m='';try{m=(await r.json()).error.message}catch(e){}throw new Error('Drive : '+(m||r.status))}return r}
const djson=async(url,o)=>(await dr(url,o)).json();
function withDrive(fn){const again=()=>new Promise((ok,ko)=>authDlg(()=>withDrive(fn).then(ok,ko),'drive'));if(!driveTok())return again();return fn().catch(e=>{if(e.message=='DRIVE_EXP')return again();throw e})}
const dkids=async(id,extra='')=>(await djson(DAPI+'?fields=files(id,name)&pageSize=100&q='+encodeURIComponent(`'${id}' in parents and trashed=false${extra}`))).files||[];
async function dfolder(name,parent,desc){let f=(await dkids(parent,` and name='${qq(name)}' and mimeType='application/vnd.google-apps.folder'`))[0];
 if(!f)f=await djson(DAPI+'?fields=id,name',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({name,mimeType:'application/vnd.google-apps.folder',parents:[parent],description:desc||''})});
 else if(desc!==undefined)await dr(DAPI+'/'+f.id,{method:'PATCH',headers:{'Content-Type':'application/json'},body:JSON.stringify({description:desc})});return f}
async function dput(parent,old,f,b64){const bd='cathia'+Math.random().toString(36).slice(2),meta=old?{name:f.n}:{name:f.n,parents:[parent]};
 const body=`--${bd}\r\nContent-Type: application/json; charset=UTF-8\r\n\r\n${JSON.stringify(meta)}\r\n--${bd}\r\nContent-Type: ${f.m}\r\nContent-Transfer-Encoding: base64\r\n\r\n${b64}\r\n--${bd}--`;
 await dr(DUP+(old?'/'+old.id:'')+'?uploadType=multipart&fields=id',{method:old?'PATCH':'POST',headers:{'Content-Type':'multipart/related; boundary='+bd},body})}
const dname=n=>String(n).replace(/[\\\/:*?"<>|\u0000-\u001f]+/g,' ').replace(/\s+/g,' ').trim().slice(0,80)||'Projet';
const dread=b=>new Promise(ok=>{const f=new FileReader();f.onload=()=>ok(f.result);f.readAsDataURL(b)});
function driveSave(name,fiche,pdf){return withDrive(async()=>{const root=await dfolder('CathIA','root'),pf=await dfolder(dname(name)+'.cathia',root.id,JSON.stringify({fiche})),F=await projFiles(name,pdf),old=await dkids(pf.id);
  for(const f of F)await dput(pf.id,old.find(o=>o.name==f.n),f,f.b||await b64of(new Blob([fillPh(f.t,pf.id)],{type:f.m})));CLOUD.id=pf.id;return{id:pf.id,name:dname(name)}})}
const driveList=()=>withDrive(async()=>(await djson(DAPI+'?fields=files(id,name,modifiedTime,description)&orderBy=modifiedTime%20desc&pageSize=100&q='+encodeURIComponent("mimeType='application/vnd.google-apps.folder' and name contains '.cathia' and trashed=false"))).files.filter(f=>/\.cathia$/i.test(f.name)).map(f=>{let fi=null;try{fi=JSON.parse(f.description||'{}').fiche||null}catch(e){}return{id:f.id,name:f.name.replace(/\.cathia$/i,''),date:new Date(f.modifiedTime).toLocaleString('fr-FR',{dateStyle:'short',timeStyle:'short'}),fiche:fi}}));
async function driveThumb(id){try{const f=(await dkids(id,` and name='vignette.jpg'`))[0];return f?await dread(await (await dr(DAPI+'/'+f.id+'?alt=media')).blob()):''}catch(e){return''}}
const driveRead=id=>withDrive(async()=>{const f=(await dkids(id)).find(x=>/\.cathia\.html$/i.test(x.name))||(await dkids(id)).find(x=>/\.x?html?$/i.test(x.name));if(!f)throw new Error('Aucun modèle 3D dans ce dossier.');return await (await dr(DAPI+'/'+f.id+'?alt=media')).text()});

/* ----- enregistrer, partager, ouvrir ----- */
function saveCloud(pub){if(!objs.length)return msg('Rien à enregistrer pour l’instant.');
 if(pub){if(!AUTH.tok)return authDlg(()=>saveCloud(pub))}else if(!CLOUD.gid&&!driveTok())return authDlg(null,'drive');
 ficheDlg(pub?'Partager avec la communauté':'Enregistrer dans mon Drive',!!pub,(name,fiche,pdf)=>cloudSend(name,fiche,pdf,!!pub))}
async function cloudSend(name,fiche,pdf,pub){msg('Enregistrement en cours…',25000);try{meta.titre=name;meta.fiche=fiche;let r;
 if(pub){const F=await withB(await projFiles(name,pdf));r=await gcall('publishModel',AUTH.tok,name,F,fiche)}else r=await driveSave(name,fiche,pdf);
 touch();msg(pub?'Modèle publié dans « Modèles partagés » : '+r.name:'Projet enregistré dans votre Drive : CathIA › '+r.name+'.cathia',7000);if(pub&&libWhich=='com'&&document.body.classList.contains('lb'))libRefresh()}
 catch(e){msg('Échec : '+e.message,9000);if(/Session expirée/.test(e.message))authSet(null,AUTH.email)}}
const shareModel=()=>gasOK()?saveCloud(true):msg('Le partage de modèles n’existe que dans la version en ligne (Google Apps Script).',6000);
const projCard=f=>`<div class="lbc" onclick="gasOpen('${f.id}','${esc(f.name).replace(/'/g,'’')}')" style="position:relative"><img data-dth="${f.id}" alt=""><div><b>${esc(f.name)}</b><br><small>${esc(ficheLine(f.fiche))}</small><br><small class="mu">${esc(f.date)}</small></div><button class="dg" title="Mettre à la corbeille" style="position:absolute;top:6px;right:6px;padding:2px 8px" onclick="event.stopPropagation();gasDel('${f.id}')">✕</button></div>`;
async function openDrive(){if(!gasOK())return;msg('Lecture de votre Drive…',15000);try{const L=await driveList();
 modal(`<h3>Mes projets <small class="mu">${esc(AUTH.email||'')}</small></h3>${L.length?`<div class="lbg" style="grid-template-columns:repeat(auto-fill,minmax(200px,1fr))">${L.map(projCard).join('')}</div>`:'<p class="mu">Aucun projet enregistré dans votre Drive pour l’instant : utilisez Fichier › Enregistrer.</p>'}<div class="r"><button onclick="closeMd()">Fermer</button></div>`);$('#mb').classList.add('wide');
 const q=[...document.querySelectorAll('#mb img[data-dth]')];let run=0;const pump=()=>{while(run<3&&q.length){const i=q.shift();run++;driveThumb(i.dataset.dth).then(u=>{if(u&&i.isConnected)i.src=u}).finally(()=>{run--;pump()})}};pump()}
 catch(e){msg('Drive : '+e.message,7000)}}
async function gasOpen(id,name){closeMd();msg('Ouverture…');try{openText(await driveRead(id),name,{id,name});if(!FV)tabClick('Créer')}catch(e){msg('Ouverture impossible : '+e.message,7000)}}
function gasDel(id){modal(`<h3>Supprimer ce projet ?</h3><p class="mu">Le dossier est mis à la corbeille de votre Drive (récupérable).</p><div class="r"><button class="dg" id="gd_y">Mettre à la corbeille</button><button onclick="openDrive()">Annuler</button></div>`);$('#gd_y').onclick=async()=>{try{await withDrive(()=>dr(DAPI+'/'+id,{method:'PATCH',headers:{'Content-Type':'application/json'},body:JSON.stringify({trashed:true})}));openDrive()}catch(e){closeMd();msg('Suppression impossible : '+e.message,7000)}}}
async function openByLink(id){msg('Ouverture du modèle…');try{let r;try{r=await gcall('readByLink',AUTH.tok||'',id)}catch(e){if(!/privé/i.test(e.message))throw e;r=null}
 if(r)openText(r.html,r.name,{id,name:r.name,from:'lien'});else openText(await driveRead(id),'Projet',{id,name:'Projet'});if(!FV)tabClick('Créer')}catch(e){msg('Ouverture impossible : '+e.message,8000)}}
function openDlg(){const c=(i,t,s,fn)=>`<div class="hmc" onclick="closeMd();${fn}">${ic(i,34)}<div><b>${t}</b><small>${s}</small></div></div>`;
 modal(`<h3>Ouvrir</h3><div class="hmg" style="grid-template-columns:1fr">${c('open','Depuis cet appareil','Fichier .cathia.html, .json ou plan .svg','openProj()')}${gasOK()?c('drive','Mes projets (Google Drive)','Les projets que vous avez enregistrés','openDrive()'):''}${c('asm','Modèles partagés','Réalisations de la communauté','tabClick(\'Modèles partagés\')')}${c('table','Modèles de référence','Établi, tables, bancs… et modèles vérifiés','tabClick(\'Bibliothèque de modèles\')')}</div><div class="r"><button onclick="closeMd()">Annuler</button></div>`)}
/* application complète : un seul fichier, bibliothèques externes incluses, utilisable sans internet */
async function dlApp(){msg('Préparation du fichier hors ligne…',30000);try{let h=gasOK()?await gcall('appSource'):await fetch(location.href.split('#')[0]).then(r=>r.text());
 for(const m of [...h.matchAll(/<script src="(https:[^"]+)"><\/script>/g)]){const t=await fetch(m[1]).then(r=>{if(!r.ok)throw new Error('bibliothèque introuvable ('+m[1].split('/').pop()+')');return r.text()});h=h.replace(m[0],()=>'<script>'+t.replace(/<\/script/gi,'<\\/script')+'\n</script>')}
 await save('CathIA-hors-ligne.html',h,'text/html');msg('Application complète téléchargée : ouvrez ce fichier dans un navigateur, même sans internet.',9000)}catch(e){msg('Téléchargement impossible : '+e.message,9000)}}
/* Entrée valide la fenêtre ouverte */
document.addEventListener('keydown',e=>{if(e.key!='Enter'||e.defaultPrevented||e.isComposing)return;const md=$('#md');if(!md||!md.classList.contains('on'))return;const t=e.target;if(t&&/^(BUTTON|TEXTAREA|A|SUMMARY)$/.test(t.tagName))return;if(t&&t!==document.body&&!md.contains(t))return;const b=md.querySelector('button.p');if(b&&!b.disabled){e.preventDefault();b.click()}});

/* ----- les deux bibliothèques : « Modèles de référence » et « Modèles partagés » ----- */
const LIBDATA={verified:null,community:null},THUMBC={};let LF={sort:'best',q:'',type:'',dif:'',uni:'',par:''},libWhich='ref',libLoading=false;
const fopt=(arr,v,ph)=>`<option value="">${ph}</option>`+arr.map(x=>{const[a,b]=Array.isArray(x)?x:[x,x];return`<option value="${esc(a)}"${String(a)==String(v)?' selected':''}>${esc(b)}</option>`}).join('');
const fmatch=(name,desc,f)=>{f=f||{};const q=LF.q.trim().toLowerCase();if(q&&!(name+' '+(desc||'')+' '+ftype(f)+' '+(f.desc||'')).toLowerCase().includes(q))return false;if(LF.type&&f.type!=LF.type)return false;if(LF.dif&&+f.dif!=+LF.dif)return false;if(LF.uni&&!(f.u||[]).includes(LF.uni))return false;if(LF.par&&!(f.par||[]).includes(LF.par))return false;return true};
const lfActive=()=>!!(LF.q.trim()||LF.type||LF.dif||LF.uni||LF.par);
const starsOf=m=>`<span class="stars" onclick="event.stopPropagation()" title="${m.n?m.avg+' / 5 ('+m.n+' avis)':'Pas encore noté'} : cliquez pour noter">${[1,2,3,4,5].map(i=>`<i class="${m.my?(i<=m.my?'on my':''):(i<=Math.round(m.avg||0)?'on':'')}" onclick="rateIt('${m.id}',${i})">★</i>`).join('')}<small>${m.n?(+m.avg).toFixed(1)+' ('+m.n+')':'pas noté'}</small></span>`;
const libCard=(w,m)=>`<div class="lbc" onclick="${m.k?`exWin('${m.k}')`:`openShared('${w}','${m.id}','${esc(m.name).replace(/'/g,'’')}')`}"><img ${m.k?`data-k="${m.k}"`:m.th?`src="${esc(m.th)}" loading="lazy"`:`data-th="${w}|${m.id}"`} ${m.k&&LIBC[m.k]?`src="${LIBC[m.k]}"`:''} alt=""><div><b>${esc(m.name)}</b>${w=='community'&&m.id?'<br>'+starsOf(m):''}<br><small>${esc(ficheLine(m.f))}</small>${m.desc?`<br><small>${esc(m.desc)}</small>`:''}${m.mine?`<br><small class="mu">Votre modèle (public)</small> <button class="dg" style="padding:1px 8px" onclick="event.stopPropagation();delPub('${m.id}')">Retirer</button>`:''}</div></div>`;
function libLists(){const ref=libWhich=='ref',w=ref?'verified':'community',out=[];
 if(ref){const B=Object.keys(EXN).map(k=>({k,name:EXN[k],desc:LIBD[k],f:LIBF[k]||{}})).filter(m=>fmatch(m.name,m.desc,m.f)),V=(LIBDATA.verified||[]).map(x=>({id:x.id,name:x.name,desc:(x.fiche&&x.fiche.desc)||'',f:x.fiche||{}})).filter(m=>fmatch(m.name,m.desc,m.f));
  if(!lfActive())LIBCAT.forEach(([n,ks])=>{const L=B.filter(m=>ks.includes(m.k));if(L.length)out.push(`<h4 class="lbh">${n}</h4><div class="lbg">${L.map(m=>libCard('ref',m)).join('')}</div>`)});
  else if(B.length)out.push(`<h4 class="lbh">Modèles paramétrables</h4><div class="lbg">${B.map(m=>libCard('ref',m)).join('')}</div>`);
  if(gasOK()){out.push(`<h4 class="lbh">Modèles vérifiés <small class="mu">(validés par l’équipe)</small></h4>`+(LIBDATA.verified==null?'<p class="mu">Chargement…</p>':V.length?`<div class="lbg">${V.map(m=>libCard('verified',m)).join('')}</div>`:`<p class="mu">${lfActive()?'Aucun modèle vérifié ne correspond.':'Aucun modèle vérifié pour l’instant.'}</p>`))}
  if(!B.length&&!V.length&&LIBDATA.verified&&lfActive())out.push('<p class="mu">Aucun modèle ne correspond à votre recherche.</p>')}
 else{if(!gasOK())return'<p class="mu">Les modèles partagés sont disponibles dans la version en ligne (Google Apps Script).</p>';const C=(LIBDATA.community||[]).map(x=>({id:x.id,name:x.name,desc:(x.fiche&&x.fiche.desc)||'',f:x.fiche||{},t:x.t,avg:x.avg||0,n:x.n||0,my:x.my||0,mine:!!x.mine,th:x.thumb||''})).filter(m=>fmatch(m.name,m.desc,m.f));if(LF.sort=='recent')C.sort((a,b)=>(b.t||0)-(a.t||0));else if(LF.sort=='name')C.sort((a,b)=>a.name.localeCompare(b.name));
  out.push(LIBDATA.community==null?'<p class="mu">Chargement…</p>':C.length?`<div class="lbg">${C.map(m=>libCard('community',m)).join('')}</div>`:`<p class="mu">${lfActive()?'Aucun modèle ne correspond à votre recherche.':'Aucun modèle partagé pour l’instant. Soyez le premier : Fichier › Enregistrer › Publier dans la communauté.'}</p>`)}
 return out.join('')}
function libRender(){const e=$('#lbl');if(!e)return;e.innerHTML=libLists();lazyThumbs()}
function libShow(which){libWhich=which;const L=$('#lbv'),ref=which=='ref';
 L.innerHTML=`<div class="r" style="align-items:center;gap:10px;flex-wrap:wrap"><h3 style="margin:0">${ref?'Modèles de référence':'Modèles partagés'}</h3><span style="flex:1"></span><button style="flex:none" onclick="libRefresh()">Actualiser</button>${ref?'':'<button class="p" style="flex:none" onclick="shareModel()">Publier mon projet…</button>'}</div><p class="mu">${ref?'Modèles paramétrables du livre (réglez les dimensions, puis créez-les) et modèles vérifiés par l’équipe.':'Les modèles publiés par tous les utilisateurs, classés par note (étoiles). Ils sont publics. Un modèle s’ouvre comme une copie de travail : l’original n’est jamais modifié. Cliquez les étoiles pour noter.'}</p><div class="r" style="flex-wrap:wrap;gap:8px;margin:8px 0 14px"><input id="lbq" type="search" placeholder="Rechercher…" value="${esc(LF.q)}" style="flex:1;min-width:180px;max-width:340px"><select id="lbt">${fopt(FTYPES,LF.type,'Tous les types')}</select><select id="lbd">${fopt(FDIF.map((l,i)=>[i+1,(i+1)+' – '+l]),LF.dif,'Toute difficulté')}</select><select id="lbu">${fopt(FUNI,LF.uni,'Toutes les unités')}</select><select id="lbp">${fopt(FPAR,LF.par,'Jeunes ou chefs')}</select>${ref?'':`<select id="lbs"><option value="best"${LF.sort=='best'?' selected':''}>Mieux notés d’abord</option><option value="recent"${LF.sort=='recent'?' selected':''}>Plus récents</option><option value="name"${LF.sort=='name'?' selected':''}>Nom (A-Z)</option></select>`}</div><div id="lbl"></div>`;
 const bind=(id,k)=>{$('#'+id).oninput=$('#'+id).onchange=ev=>{LF[k]=ev.target.value;libRender()}};bind('lbq','q');bind('lbt','type');bind('lbd','dif');bind('lbu','uni');bind('lbp','par');if($('#lbs'))bind('lbs','sort');
 libRender();if(gasOK()){const w=ref?'verified':'community';if(LIBDATA[w]==null)loadLib(w)}}
async function loadLib(w){try{LIBDATA[w]=await gcall('listLibrary',w,AUTH.tok||'')}catch(e){LIBDATA[w]=[];msg('Bibliothèque indisponible : '+e.message,7000)}if(document.body.classList.contains('lb'))libRender()}
function libRefresh(){const w=libWhich=='ref'?'verified':'community';LIBDATA[w]=null;for(const k in THUMBC)if(k.indexOf(w+'|')==0)delete THUMBC[k];libRender();if(gasOK())loadLib(w)}
/* vignettes : les modèles intégrés ont une image pré-calculée ; les autres sont chargées une à une, à la demande */
let thQ=0;
function lazyThumbs(){const imgs=[...document.querySelectorAll('#lbl img:not([src])')];
 imgs.filter(i=>i.dataset.k).forEach(i=>{const k=i.dataset.k;if(LIBC[k])i.src=LIBC[k]});
 const T=imgs.filter(i=>i.dataset.th&&!i.getAttribute('src'));T.forEach(i=>{const k=i.dataset.th;if(THUMBC[k])i.src=THUMBC[k]});
 const todo=T.filter(i=>!i.getAttribute('src'));const pump=()=>{while(thQ<3&&todo.length){const i=todo.shift(),k=i.dataset.th,[w,id]=k.split('|');if(!i.isConnected)continue;thQ++;gcall('getThumb',w,id,AUTH.tok||'').then(u=>{if(u){THUMBC[k]=u;if(i.isConnected)i.src=u}}).catch(()=>{}).finally(()=>{thQ--;pump()})}};pump();
 const miss=imgs.filter(i=>i.dataset.k&&!LIBC[i.dataset.k]);(function nx(){const i=miss.shift();if(!i||!document.body.classList.contains('lb'))return;try{i.src=libThumb(i.dataset.k)}catch(e){}setTimeout(nx,40)})()}
async function openShared(w,id,name){msg('Ouverture…');try{const it=(LIBDATA[w]||[]).find(x=>x.id==id),t=it&&it.html?await fetch(it.html).then(r=>{if(!r.ok)throw new Error('Modèle introuvable.');return r.text()}):await gcall('readLibraryItem',w,id);openText(t,name,{id,name,from:w});if(!FV)tabClick('Créer')}catch(e){msg('Ouverture impossible : '+e.message,7000)}}
/* notes et retrait */
function rateIt(id,n){needAuth(async()=>{try{const r=await gcall('rateModel',AUTH.tok,id,n),it=(LIBDATA.community||[]).find(x=>x.id==id);if(it){it.avg=r.avg;it.n=r.n;it.my=r.my}if(document.body.classList.contains('lb'))libRender();msg('Merci pour votre note.')}catch(e){msg(e.message,6000)}})}
function delPub(id){modal(`<h3>Retirer ce modèle ?</h3><p class="mu">Il disparaît de la bibliothèque publique (son historique reste dans le dépôt).</p><div class="r"><button class="dg" id="dp_y">Retirer</button><button onclick="closeMd()">Annuler</button></div>`);$('#dp_y').onclick=async()=>{try{await gcall('deleteModel',AUTH.tok,id);closeMd();libRefresh();msg('Modèle retiré.')}catch(e){closeMd();msg(e.message,7000)}}}
function libTabBtn(){const t=viewTab=='Bibliothèque de modèles'?'Modèles de référence':viewTab=='Modèles partagés'?'Modèles partagés':'';return t?`<button class="p" onclick="tabClick('${viewTab}')">${t}<span class="px" title="Fermer" onclick="event.stopPropagation();tabClick('Créer')">✕</span></button>`:''}
cloudInit();
if('serviceWorker' in navigator&&location.protocol=='https:'&&!inGas())navigator.serviceWorker.register('sw.js').catch(()=>{});
