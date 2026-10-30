/* =====================  Compléments : nomenclature des assemblages, filets, table de prépa avec étagère, cotes de pieds en X, montage  ===================== */

/* ----- nomenclature des assemblages : combien de mi-bois, de tenons (et lesquels), de chevilles, de ligatures… ----- */
function asmRows(){const only=nom.only?new Set(nom.only):null,inL=o=>!only||only.has(o.id),J={},R={},
 norm=n=>String(n||'').replace(/ (gauche|droit|droite|avant|arrière|haut|bas)\b/g,'').replace(/ \(.*\)$/,'').replace(/ \d+$/,'').trim(),
 kn=k=>{const e=KINDS.find(x=>x[0]==k);return e?e[1]:k},
 add_=(lab,pcs)=>{const r=R[lab]||(R[lab]={label:lab,qty:0,pcs:new Set()});r.qty++;if(pcs&&r.pcs.size<2)r.pcs.add(pcs)};
 objs.forEach(o=>{if(!inL(o))return;(o.ops||[]).forEach(p=>{if(p.jid&&!J[p.jid])J[p.jid]={op:p,ps:[]};if(p.jid)J[p.jid].ps.push(o)})});
 Object.values(J).forEach(g=>{const rec=g.op.rec||{},o=rec.opt||{},k=rec.k||'';if(!k||k=='coupe'||k=='pointe'||k=='quart')return;let lab;
  if(k=='mibois')lab='Mi-bois'+(o.pc?' '+Math.round(o.pc)+' %':'');
  else if(k=='cheville')lab='Cheville'+(o.d?' Ø '+Math.round(o.d)+' mm':'');
  else{lab=kn(o.style||k);if(o.d)lab+=' Ø '+Math.round(o.d)+' mm';if(o.mort)lab+=o.mort=='blind'?', mortaise borgne':', mortaise débouchante'}
  add_(lab,[...new Set(g.ps.map(p=>norm(p.name)))].slice(0,2).join(' × '))});
 objs.forEach(o=>{if(!inL(o))return;if(o.type=='lash')add_('Brêlage ('+(o.p.turns||'')+' tours)','');else if(o.type=='ph')add_(o.p.kind=='filet'?'Filet de ficelle':'Cordes (PH)','');else if(/^Cheville/.test(o.name)&&o.type=='trav'&&o.p)add_('Cheville Ø '+Math.round(o.p.d)+' mm × '+Math.round(o.p.L)+' mm','')});
 return Object.values(R).sort((a,b)=>b.qty-a.qty).map((r,i)=>({n:i+1,qty:r.qty,label:r.label,pcs:(t=>t.length>46?t.slice(0,45)+'…':t)([...r.pcs].join(' ; '))}))}
function nomAsmBuild(){const rows=asmRows(),f=nom.sz/3,rh=nom.sz*1.5,C=[['n','N°'],['qty','Qté'],['label','Assemblage'],['pcs','Pièces assemblées']],
 W=C.map(([k,l])=>Math.max(l.length,...rows.map(r=>String(r[k]).length))*1.75*f+3),w=Math.max(W.reduce((a,b)=>a+b,0),24*2.1*f);let y=rh,x=0,s='';
 const hdr=`<rect x="0" y="0" width="${fx(w)}" height="${fx(rh)}" fill="#e9edf3" stroke="#111" stroke-width=".35"/><text class="h" x="1.5" y="${fx(rh*.72)}" style="font-size:${fx(nom.sz*1.05)}px">NOMENCLATURE DES ASSEMBLAGES</text>`;
 s+=C.map(([k,l],i)=>{const t=`<text class="h" x="${fx(x+1.2)}" y="${fx(y+rh*.72)}">${esc(l)}</text>`;x+=W[i];return t}).join('')+`<line x1="0" y1="${fx(y+rh)}" x2="${fx(w)}" y2="${fx(y+rh)}" stroke="#111" stroke-width=".3"/>`;y+=rh;
 for(const r of rows){x=0;s+=C.map(([k],i)=>{const t=`<text x="${fx(x+1.2)}" y="${fx(y+rh*.72)}">${esc(r[k])}</text>`;x+=W[i];return t}).join('')+`<line x1="0" y1="${fx(y+rh)}" x2="${fx(w)}" y2="${fx(y+rh)}" stroke="#bbb" stroke-width=".15"/>`;y+=rh}
 if(!rows.length){s+=`<text x="1.5" y="${fx(y+rh*.72)}">Aucun assemblage</text>`;y+=rh}
 x=0;const vl=C.slice(0,-1).map(([k],i)=>{x+=W[i];return`<line x1="${fx(x)}" y1="${fx(rh)}" x2="${fx(x)}" y2="${fx(y)}" stroke="#666" stroke-width=".15"/>`}).join('');
 return{w,h:y,svg:`<rect x="0" y="0" width="${fx(w)}" height="${fx(y)}" fill="#fff"/>`+hdr+vl+s+`<rect class="fr" x="0" y="0" width="${fx(w)}" height="${fx(y)}" fill="none" stroke="#111" stroke-width=".5"/>`}}
function nomAsmSvg(){const b2=nomAsmBuild(),A=nom.anchor,showN=nom.show&&objs.length;let ax,ay;
 if(showN){ax=nom.x;ay=(A=='bl'||A=='br')?nom.y-b2.h-4:nom.y+(nom.bh||0)+4}else if(A=='bl'){ax=14;ay=283-b2.h}else if(A=='br'){ax=408-b2.w;ay=244-b2.h}else if(A=='tl'){ax=14;ay=14}else if(A=='tr'){ax=408-b2.w;ay=14}else{ax=nom.x;ay=nom.y}
 nom.aw=b2.w;nom.ah=b2.h;return`<g class="nm2" transform="translate(${fx(ax)} ${fx(ay)})">${b2.svg}</g>`}

/* ----- filet de ficelle : mailles en losange tendues d'un cadre à l'autre, très légèrement creusées, anneaux autour des barres ----- */
function netDiamond(P,yt,zr,xa,xb,pitch,rr){const segs=[],gap=2*yt,sag=Math.min(24,Math.max(8,gap*.035)),d=2*pitch,NS=8,ring=new Set(),
 cord=(xs,s0,xe,s1)=>{const pts=[];for(let i=0;i<=NS;i++){const t=i/NS;pts.push(P(xs+(xe-xs)*t,s0*(yt-rr)+(s1*(yt-rr)-s0*(yt-rr))*t,zr-sag*4*t*(1-t)))}for(let i=0;i<NS;i++)segs.push([pts[i],pts[i+1]])},
 rg=(x,s)=>{const key=Math.round(x)+','+s;if(ring.has(key))return;ring.add(key);const c=[];for(let i=0;i<=10;i++){const th=2*Math.PI*i/10;c.push(P(x,s*yt+rr*Math.cos(th)*0,zr+0))}
  const pts=[];for(let i=0;i<=10;i++){const th=2*Math.PI*i/10;pts.push(P(x,s*yt+Math.sin(th)*rr,zr+Math.cos(th)*rr))}for(let i=0;i<10;i++)segs.push([pts[i],pts[i+1]])};
 for(let x=xa;x+d<=xb+1e-6;x+=pitch){cord(x,-1,x+d,1);cord(x+d,-1,x,1);[x,x+d].forEach(u=>{rg(u,-1);rg(u,1)})}
 return segs}
function mkNet(par,name,P,yt,zr,xa,xb,railD){const segs=netDiamond(P,yt,zr,xa,xb,60,railD/2+3);if(!segs.length)return null;return mkObj('ph',{segs,d:2.5,kind:'filet'},null,name,'#cfc8b8',[0,0,0],[0,0,0],par)}

/* ----- Table de prépa avec étagère : traverses continues, cadre haut en mi-bois partout, filets haut et bas, contreventement ----- */
EXB.cuisine=function(P,a,q){const Lp=q.long,Wp=q.larg,H=q.h,Wc=q.lc||600,ht=q.ht,dc=q.dc,dr=q.dr||70,ty=q.etage=='filet'?'filet':'claies',mb=q.asm!='tenons';
 if(Lp<800||Wp<400||H<400)throw new Error('Table trop petite.');if(dc<8||dc>20)throw new Error('Diamètre des claies : de 8 à 20 mm.');
 if(ht<H+500)throw new Error('La colonne doit dépasser le plan de travail d’au moins 50 cm.');
 const ep=dr/2,zt=H-ep,x0=60,x1=Lp-60,x2=x1+Wc,yt=(Wp-50)/2,rp=35,ztop=ht-25,zb=Math.round(H/2)-35,e=mb?30:2,pl={};
 /* poteaux : 2 pieds côté gauche, 2 pieds hauts au milieu (table + étagère), 2 montants au bout */
 [[x0,zt+(mb?27:70),'Pied'],[x1,ztop+27,'Pied haut'],[x2,ztop+27,'Montant étagère']].forEach(([x,top,nm])=>[-1,1].forEach(s=>pl[x+','+s]=bar(`${nm} ${x==x0?'gauche':x==x1?'central':'droit'} ${s<0?'avant':'arrière'}`,P(x,s*yt,0),P(x,s*yt,top),70,a.id)));
 const post=(x,s)=>pl[x+','+s],td=p=>Math.min(30,Math.round(crossMin(p)/3));
 /* traverses continues d'un bout à l'autre : mi-bois avec le premier poteau rencontré, tenon dans le dernier */
 const through=(name,z,d,ee)=>[-1,1].map(s=>bar(name,P(x0-rp-ee,s*yt,z),P(x2+rp+2,s*yt,z),d,a.id));
 const top=through('Traverse du plateau (continue)',zt,50,e),low=through('Traverse basse (continue)',zb,40,2);
 /* cadre du plan de travail : traverse de largeur côté pied gauche (mi-bois) */
 const C0=bar('Traverse haute (largeur)',P(x0,-yt-rp-e,mb?zt:zt-80),P(x0,yt+rp+e,mb?zt:zt-80),50,a.id),C1=bar('Traverse haute (largeur)',P(x1,-yt+5,zt-28),P(x1,yt-5,zt-28),50,a.id);
 [-1,1].forEach((s,i)=>{const L=top[i];
  if(mb){try{mkMibois(L,C0,{pc:50})}catch(er){console.error('mibois cadre',er)}try{TJ(post(x0,s),C0,{mort:'thru',d:td(post(x0,s))});drill(L,P(x0,s*yt,zt),[0,0,1],td(post(x0,s))+1,'Mortaise du tenon du pied')}catch(er){console.error('tenon cadre',er)}}
  else{TJ(L,post(x0,s));}
  try{mkMibois(L,post(x1,s),{pc:50})}catch(er){console.error('mibois poteau central',er)}
  TJ(L,post(x2,s));TJ(C1,post(x1,s),{mort:'blind'});
  const B=low[i];TJ(B,post(x0,s));try{mkMibois(B,post(x1,s),{pc:50})}catch(er){console.error('mibois bas',er)}TJ(B,post(x2,s))});
 if(!mb){TJ(C0,post(x0,-1));TJ(C0,post(x0,1))}
 /* plateau du plan de travail : claies/rondins fendus sur les traverses continues */
 deckBuild(P,a,q,{x0,x1,yt,zt,dt:50,rp,pl,dc,nm:'plateau (rondins fendus)',logs:{d:dr,z:H},rails:top});
 /* étagère au niveau du plan de travail : claies sur les MÊMES traverses continues (deuxième encoche en quart de bois) */
 const ox=P(0,0,0)[0],r0=top[0].pos[0]-ox,c2={x0:x1,x1:x2,yt,rp,pl,tall:x1};
 if(ty=='claies')deckBuild(P,a,q,{...c2,zt,dt:50,dc,nm:'étagère au niveau du plan (claies droites)',rails:top});
 else mkNet(newAsm('Filet étagère au niveau du plan',a.id).id,'Filet de ficelle',P,yt,zt,x1+rp+8,x2-rp-8,50);
 /* étagère intermédiaire éventuelle (1,5 fois la hauteur du plan) : traverses propres, tenonnées */
 [1.5*H].filter(z=>z<ztop-250).forEach(z=>{z=Math.round(z);const rl=[-1,1].map(s=>{const b=bar('Traverse étagère haute',P(x1+5,s*yt,z),P(x2+rp+2,s*yt,z),50,a.id);TJ(b,post(x1,s),{mort:'blind'});TJ(b,post(x2,s));return b});
  if(ty=='claies')deckBuild(P,a,q,{...c2,zt:z,dt:50,dc,nm:'étagère haute (claies droites)',rails:rl});else mkNet(newAsm('Filet étagère haute',a.id).id,'Filet de ficelle',P,yt,z,x1+rp+8,x2-rp-8,50)});
 /* filet du bas : sous le plan de travail ET dans la colonne, sur les traverses basses continues, au plan médian des traverses */
 mkNet(newAsm('Filet du bas',a.id).id,'Filet de ficelle (bas)',P,yt,zb,x0+rp+8,x2-rp-8,40);
 /* dessus de la colonne : cadre en mi-bois sur les DEUX côtés, filet dessus */
 const tf=topFrame(P,a,q,{x0:x1,x1:x2,y:yt,zt:ztop,dl:50,dc:50,rp,pl,nameL:'Lisse haute étagère',crossZ:ztop-80});
 mkNet(newAsm('Filet du haut',a.id).id,'Filet de ficelle (haut)',P,yt,ztop,x1+rp+8,x2-rp-8,50);
 /* colonne à gauche : on tourne tout l'ensemble de 180° autour de la verticale */
 if(q.cote=='gauche'){const L=piecesOf(a.id),[mn,mx]=bounds(L),cc=[(mn[0]+mx[0])/2,(mn[1]+mx[1])/2,0],R=new THREE.Matrix4().makeTranslation(cc[0],cc[1],0).multiply(new THREE.Matrix4().makeRotationZ(Math.PI)).multiply(new THREE.Matrix4().makeTranslation(-cc[0],-cc[1],0));
  L.forEach(o=>{const M0=new THREE.Matrix4().compose(new THREE.Vector3(...o.pos),new THREE.Quaternion().setFromEuler(new THREE.Euler(o.rot[0]*D,o.rot[1]*D,o.rot[2]*D,'ZYX')),new THREE.Vector3(1,1,1));setMat(o,R.clone().multiply(M0))})}};

/* ----- cotes : longueur du morceau incliné (pieds en X) ----- */
function xDims(a){const w=views.find(v=>v.k=='left');if(!w)return;vdata(w);const f=nrm(DIRS[w.k][1]),h=Math.abs(f[2])>.99?[1,0,0]:nrm(cr(f,[0,0,1])),v=cr(h,f),uv=p=>[dot(p,h),dot(p,v)],legs=piecesOf(a.id).filter(o=>/pied (montant|descendant)/.test(o.name));
 [legs.find(o=>/montant/.test(o.name)),legs.find(o=>/descendant/.test(o.name))].filter(Boolean).forEach((o,i)=>{const ax=axisOf(o);dims.push({id:did++,v:w.id,t:'d',pre:'',a:uv(ax.p0),b:uv(ax.p1),o:(i?-1:1)*14})})}

/* ----- montage : fenêtre d'action montrée à la première occurrence de chaque opération ----- */
function mtWin(s){const T=(MT_TOOLS.find(t=>t[0]==s.tool)||[])[1]||'Opération';let rows=[];
 if(s.kind=='joint'){const ops=[...new Set(s.objs.map(p=>(p.ops||[]).find(q=>q.jid==s.g.jid)).filter(Boolean).map(q=>U(q.lab||'')))],o=(s.g.op.rec||{}).opt||{};rows=['Pièces : '+s.objs.slice(0,3).map(p=>p.name).join(' + '),...ops.slice(0,3)];if(o.d)rows.push('Ø du tenon : '+Math.round(o.d)+' mm');if(o.pc)rows.push('Profondeur : '+Math.round(o.pc)+' %')}
 else{const o=s.objs[0];rows=[o.name+(o.type=='trav'&&o.p?' — Ø '+Math.round(o.p.d)+' × '+Math.round(o.p.L)+' mm':''),s.objs.length>1?s.objs.length+' pièces':''].filter(Boolean)}
 const el=document.createElement('div');el.id='mtw';el.innerHTML=`<b>${esc(T)}</b>${rows.map(r=>`<div>${esc(r)}</div>`).join('')}<button class="p">${s.kind=='joint'?'Appliquer':'Créer'}</button>`;document.body.appendChild(el);return el}
function mtStart(){const tops=Object.values(asms).filter(x=>!x.par);montage(selA!=null?selA:tops.length==1?tops[0].id:0)}
