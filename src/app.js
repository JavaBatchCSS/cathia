/* =====================  CathIA : noyau  ===================== */
const $=s=>document.querySelector(s),D=Math.PI/180;
const esc=t=>String(t).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
const r1=v=>Math.round(v*10)/10,fr=v=>(+v).toLocaleString('fr-FR',{maximumFractionDigits:2});
const J=jscadModeling,{cuboid,cylinder,cylinderElliptic,roundedCuboid,sphere}=J.primitives,{subtract,union,intersect}=J.booleans,{translate,rotateX,rotateY,rotateZ,transform}=J.transforms,G=J.geometries.geom3;
const add=(a,b)=>[a[0]+b[0],a[1]+b[1],a[2]+b[2]],sub=(a,b)=>[a[0]-b[0],a[1]-b[1],a[2]-b[2]],mul=(a,s)=>[a[0]*s,a[1]*s,a[2]*s],dot=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2],dt=dot,
 cr=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],len=a=>Math.hypot(a[0],a[1],a[2]),nrm=a=>{const l=len(a)||1;return[a[0]/l,a[1]/l,a[2]/l]};
let objs=[],asms={},nid=1,aid=1,sel=[],selA=null,snapOn=true,stepT=10,stepR=15,showDims=true,ghost=false,expert=false,curTab='Opérations',viewTab='Opérations',ver=0,dirty=true,vpA=1.6;
try{expert=localStorage.getItem('cathia.expert')=='1'}catch(e){}
const req=()=>{dirty=true};
const GL=['lash','ph'];
const uk=()=>PREF.unit=='mm'?1:.1,us=()=>PREF.unit=='mm'?'mm':'cm',fu=v=>fr(Math.round(v*uk()*100)/100),sm=v=>PREF.unit=='mm'?fr(Math.round(v*10)/10)+' mm':Math.abs(v)<50?fr(Math.round(v*10)/10)+' mm':Math.abs(v)>=1500?fr(Math.round(v/10)/100)+' m':fr(Math.round(v)/10)+' cm';
/* conversion d'un texte contenant des mm vers l'unité d'affichage */
function U(s){if(PREF.unit=='mm')return s;const f=x=>fu(+String(x).replace(/\s/g,'').replace(',','.'));
 return String(s).replace(/Ø\s?(\d+(?:[.,]\d+)?)(\s*mm\b)?|(\d[\d\s]*(?:[.,]\d+)?)\s*mm\b|(\d+(?:\.\d+)?)×(\d+(?:\.\d+)?)(\s*mm\b)?/g,(m,a,_,b,c,d)=>a!=null?'Ø'+(_?sm(+String(a).replace(',','.')):f(a)):b!=null?sm(+String(b).replace(/\s/g,'').replace(',','.')):f(c)+'×'+f(d)+(m.endsWith('mm')?' cm':''))}
let tm;function msg(t,ms=3200){const e=$('#toast');e.textContent=U(t);e.classList.add('on');clearTimeout(tm);tm=setTimeout(()=>e.classList.remove('on'),ms)}
const SPEC={
 trav:{n:'Traverse',d:{d:80,L:1500},f:[['L','Longueur'],['d','Diamètre']]},
 box:{n:'Équarri',d:{l:1000,w:100,h:100,ch:0,fi:0},f:[['l','Longueur X'],['w','Largeur Y'],['h','Hauteur Z'],['ch','Chanfrein'],['fi','Congé']]},
 cyl:{n:'Cylindre',d:{r:25,h:100},f:[['r','Rayon'],['h','Hauteur']]},
 tube:{n:'Tube rond',d:{ro:20,ri:17,h:300},f:[['ro','Rayon ext.'],['ri','Rayon int.'],['h','Longueur']]},
 sph:{n:'Sphère',d:{r:30},f:[['r','Rayon']]},
 cone:{n:'Cône',d:{r:30,r2:10,h:80},f:[['r','Rayon base'],['r2','Rayon sommet'],['h','Hauteur']]},
 tcar:{n:'Tube carré',d:{w:40,b:40,t:3,h:300},f:[['w','Largeur'],['b','Hauteur section'],['t','Épaisseur'],['h','Longueur']]},
 corn:{n:'Cornière L',d:{w:40,b:40,t:4,h:300},f:[['w','Aile 1'],['b','Aile 2'],['t','Épaisseur'],['h','Longueur']]},
 U:{n:'Profilé U',d:{w:60,b:40,t:5,h:300},f:[['w','Profondeur'],['b','Largeur'],['t','Épaisseur'],['h','Longueur']]},
 I:{n:'Poutre I',d:{w:60,b:100,t:6,h:300},f:[['w','Largeur semelle'],['b','Hauteur'],['t','Épaisseur'],['h','Longueur']]},
 courbe:{n:'Claie',d:{pts:[[0,0,0],[100,0,0]],d0:20,d1:20,len:0},f:[]},
 mesh:{n:'Pièce',d:{},f:[]},
 lash:{n:'Brêlage',d:{turns:6,rope:6},f:[]},
 cavalier:{n:'Clou cavalier',d:{w:22,h:30,wire:3},f:[]},
 ph:{n:'PH (cordes)',d:{segs:[],d:4},f:[]}};
const AX2=['cyl','tube','cone','tcar','corn','U','I','trav'];
const okp=o=>{const p=o.p,t=o.type;return t=='box'?(p.ch||0)+(p.fi||0)<Math.min(p.l,p.w,p.h)/2-.01:t=='tube'?p.ri<p.ro:t=='corn'?p.t<Math.min(p.w,p.b):['tcar','U','I'].includes(t)?2*p.t<Math.min(p.w,p.b):1};
const segs=r=>r<20?20:r<60?28:36;
/* ---------- Matrices et repères ---------- */
const _e=new THREE.Euler(0,0,0,'ZYX');
const qOf=o=>{_e.set(o.rot[0]*D,o.rot[1]*D,o.rot[2]*D,'ZYX');return new THREE.Quaternion().setFromEuler(_e)};
const dl2w=(o,v)=>new THREE.Vector3(...v).applyQuaternion(qOf(o)).toArray(),dw2l=(o,v)=>new THREE.Vector3(...v).applyQuaternion(qOf(o).invert()).toArray();
const l2w=(o,p)=>add(dl2w(o,p),o.pos),w2l=(o,p)=>dw2l(o,sub(p,o.pos));
const matOf=o=>new THREE.Matrix4().compose(new THREE.Vector3(...o.pos),qOf(o),new THREE.Vector3(1,1,1));
const bas=u=>{u=nrm(u);const t=Math.abs(u[0])<.9?[1,0,0]:[0,1,0],e1=nrm(cr(t,u));return[e1,cr(u,e1),u]};
const fm=(c,a,b,d)=>[a[0],a[1],a[2],0,b[0],b[1],b[2],0,d[0],d[1],d[2],0,c[0],c[1],c[2],1];
const cylAB=(a,b,r,sg=32)=>{const d=sub(b,a),[e1,e2,u]=bas(d);return transform(fm(mul(add(a,b),.5),e1,e2,u),cylinder({radius:r,height:len(d),segments:sg}))};
const coneAB=(a,ra,b,rb,sg=32)=>{const d=sub(b,a),[e1,e2,u]=bas(d);return transform(fm(mul(add(a,b),.5),e1,e2,u),cylinderElliptic({height:len(d),startRadius:[Math.max(ra,.01),Math.max(ra,.01)],endRadius:[Math.max(rb,.01),Math.max(rb,.01)],segments:sg}))};
const boxF=(c,e1,e2,h)=>transform(fm(c,e1,e2,cr(e1,e2)),cuboid({size:[2*h[0],2*h[1],2*h[2]]}));
const prismF=(c,e1,e2,pts,H)=>transform(fm(sub(c,mul(cr(e1,e2),H/2)),e1,e2,cr(e1,e2)),J.extrusions.extrudeLinear({height:H},J.geometries.geom2.fromPoints(pts)));
/* ---------- Géométrie de base d'une pièce (repère local : axe long = Z pour les rondins et profilés) ---------- */
function tubeGeom(p){const pts=p.pts.map(q=>new THREE.Vector3(...q)),cv=new THREE.CatmullRomCurve3(pts,false,'centripetal'),Ln=cv.getLength(),N=Math.max(12,Math.round(Ln/40)),P=cv.getPoints(N),SN=10;p.len=Ln;
 let n=new THREE.Vector3(0,0,1);const t0=P[1].clone().sub(P[0]).normalize();if(Math.abs(t0.z)>.9)n.set(1,0,0);const rings=[];
 for(let i=0;i<=N;i++){const t=(P[Math.min(i+1,N)].clone().sub(P[Math.max(i-1,0)])).normalize();n=n.sub(t.clone().multiplyScalar(n.dot(t))).normalize();const b=new THREE.Vector3().crossVectors(t,n),r=(p.d0+(p.d1-p.d0)*i/N)/2,ring=[];for(let j=0;j<SN;j++){const a=2*Math.PI*j/SN;ring.push(P[i].clone().add(n.clone().multiplyScalar(Math.cos(a)*r)).add(b.clone().multiplyScalar(Math.sin(a)*r)).toArray())}rings.push(ring)}
 const pl=J.geometries.poly3.create,polys=[];for(let i=0;i<N;i++)for(let j=0;j<SN;j++){const j2=(j+1)%SN,A=rings[i][j],B=rings[i][j2],C=rings[i+1][j2],Dd=rings[i+1][j];polys.push(pl([A,B,C]),pl([A,C,Dd]))}
 polys.push(pl(rings[0].slice().reverse()),pl(rings[N]));return G.create(polys)}
function build(o){const p=o.p,t=o.type,bx=(x,y,w,d)=>cuboid({size:[w,d,p.h],center:[x+w/2,y+d/2,p.h/2]});let g;
 if(t=='courbe')return tubeGeom(p);
 if(t=='cavalier'){const r=p.wire/2,w=p.w,h=p.h,R=w/2,zc=h-R,leg=x=>cylAB([x,0,0],[x,0,zc],r,10),arc=[];for(let i=0;i<8;i++){const a0=Math.PI*i/8,a1=Math.PI*(i+1)/8;arc.push(cylAB([R*Math.cos(a0+Math.PI*0)*-1+0,0,zc+R*Math.sin(a0)],[-R*Math.cos(a1),0,zc+R*Math.sin(a1)],r,8))}return union(leg(-R),leg(R),...arc)}
 if(t=='trav')return cylinder({radius:p.d/2,height:p.L,segments:segs(p.d/2),center:[0,0,p.L/2]});
 if(t=='box'){const c=p.ch||0,f=p.fi||0,sz=[p.l,p.w,p.h],o2=[p.l/2,p.w/2,p.h/2];return f>0?translate(o2,roundedCuboid({size:sz,roundRadius:f,segments:16})):c>0?translate(o2,chamf(sz,c)):cuboid({size:sz,center:o2})}
 if(t=='sph')return translate([0,0,p.r],sphere({radius:p.r,segments:32}));
 if(t=='cyl'||t=='tube'){g=cylinder({radius:p.r||p.ro,height:p.h,segments:48,center:[0,0,p.h/2]});if(t=='tube')g=subtract(g,cylinder({radius:p.ri,height:p.h+2,segments:48,center:[0,0,p.h/2]}));return g}
 if(t=='cone')return cylinderElliptic({height:p.h,startRadius:[p.r,p.r],endRadius:[Math.max(p.r2,.01),Math.max(p.r2,.01)],segments:48,center:[0,0,p.h/2]});
 if(t=='tcar')return subtract(bx(0,0,p.w,p.b),cuboid({size:[p.w-2*p.t,p.b-2*p.t,p.h+2],center:[p.w/2,p.b/2,p.h/2]}));
 if(t=='corn')return union(bx(0,0,p.w,p.t),bx(0,0,p.t,p.b));
 if(t=='U')return union(bx(0,0,p.t,p.b),bx(0,0,p.w,p.t),bx(0,p.b-p.t,p.w,p.t));
 return union(bx(0,0,p.w,p.t),bx(0,p.b-p.t,p.w,p.t),bx((p.w-p.t)/2,p.t,p.t,p.b-2*p.t))}
const tcache=new WeakMap();
function polysOf(g){let c=tcache.get(g);if(!c){c={};tcache.set(g,c)}if(!c.polys)c.polys=G.toPolygons(g).map(p=>p.vertices.map(v=>[+v[0].toFixed(3),+v[1].toFixed(3),+v[2].toFixed(3)]));return c.polys}
function bpts(o){if(!o.g)return new Float32Array(0);let c=tcache.get(o.g);if(!c){c={};tcache.set(o.g,c)}if(!c.pts){const a=[];G.toPolygons(o.g).forEach(p=>p.vertices.forEach(v=>a.push(v[0],v[1],v[2])));c.pts=new Float32Array(a)}return c.pts}
function tris(o){let c=tcache.get(o.g);if(!c){c={};tcache.set(o.g,c)}if(!c.tri){const a=[];for(const pl of G.toPolygons(o.g)){const v=pl.vertices;for(let i=1;i<v.length-1;i++)a.push(...v[0],...v[i],...v[i+1])}c.tri=new Float32Array(a)}return c.tri}
function lbb(o){const p=bpts(o),mn=[1e9,1e9,1e9],mx=[-1e9,-1e9,-1e9];for(let i=0;i<p.length;i+=3)for(let k=0;k<3;k++){const v=p[i+k];if(v<mn[k])mn[k]=v;if(v>mx[k])mx[k]=v}return{min:mn,max:mx}}
/* axe long d'une pièce, en coordonnées monde */
function axisOf(o){const b=lbb(o),e=[0,1,2].map(i=>b.max[i]-b.min[i]),k=AX2.includes(o.type)?2:e.indexOf(Math.max(...e)),u=[0,0,0];u[k]=1;
 const c=[0,1,2].map(i=>(b.min[i]+b.max[i])/2),p0=[...c],p1=[...c];p0[k]=b.min[k];p1[k]=b.max[k];
 const W0=l2w(o,p0),W1=l2w(o,p1);return{u:nrm(sub(W1,W0)),p0:W0,p1:W1,L:e[k],k,e}}
/* étendue de la pièce selon une direction monde */
function ext(o,d){const dl=dw2l(o,d),p=bpts(o);let lo=1e18,hi=-1e18;for(let i=0;i<p.length;i+=3){const t=p[i]*dl[0]+p[i+1]*dl[1]+p[i+2]*dl[2];if(t<lo)lo=t;if(t>hi)hi=t}const c=dot(o.pos,d);return[lo+c,hi+c]}
/* intersections d'une droite (monde) avec la pièce de base : liste triée de paramètres t */
function lineHits(o,P,d){const O=w2l(o,P),Dl=dw2l(o,d),T=tris(o),ts=[];
 for(let i=0;i<T.length;i+=9){const e1=[T[i+3]-T[i],T[i+4]-T[i+1],T[i+5]-T[i+2]],e2=[T[i+6]-T[i],T[i+7]-T[i+1],T[i+8]-T[i+2]],pv=cr(Dl,e2),det=dot(e1,pv);if(Math.abs(det)<1e-12)continue;
  const tv=[O[0]-T[i],O[1]-T[i+1],O[2]-T[i+2]],u=dot(tv,pv)/det;if(u<-1e-9||u>1+1e-9)continue;const qv=cr(tv,e1),v=dot(Dl,qv)/det;if(v<-1e-9||u+v>1+1e-9)continue;ts.push(dot(e2,qv)/det)}
 ts.sort((a,b)=>a-b);const out=[];for(const t of ts)if(!out.length||t-out[out.length-1]>1e-3)out.push(t);return out}
/* ---------- Opérations (non destructives) : découpes exprimées dans le repère local de la pièce ---------- */
function bigR(o,axis){const p=bpts(o);let m=0;const L=axis.o;for(let i=0;i<p.length;i+=3){const v=[p[i]-L[0],p[i+1]-L[1],p[i+2]-L[2]],t=dot(v,axis.u),r=Math.hypot(v[0]-axis.u[0]*t,v[1]-axis.u[1]*t,v[2]-axis.u[2]*t);if(r>m)m=r}return m}
const stad=(W,d,n=8)=>{const r=Math.min(d/2,W/2),hx=W/2-r,P=[];for(let i=0;i<=n;i++){const t=-Math.PI/2+Math.PI*i/n;P.push([hx+r*Math.cos(t),(d/2/r)*r*Math.sin(t)])}for(let i=0;i<=n;i++){const t=Math.PI/2+Math.PI*i/n;P.push([-hx+r*Math.cos(t),r*Math.sin(t)])}return P};
function cutter(op){
 switch(op.k){
 case'hole':return cylAB(add(op.o,mul(op.u,op.s0)),add(op.o,mul(op.u,op.s1)),op.r,32);
 case'obox':return boxF(op.c,op.e1,op.e2,op.h);
 case'prism':return prismF(op.c,op.e1,op.e2,op.pts,op.H);
 case'cut':{const[e1,e2]=bas(op.n),H=1e4;return boxF(add(op.o,mul(op.n,H)),e1,e2,[H,H,H])}
 case'tenon':{const{o,u,L,d,style}=op,r=d/2,R=op.rmax+3,hache=style=='hache',Lc=(hache||style=='plat')?(op.Lc||0):0,end=L+Lc,P=x=>add(o,mul(u,x));
  const reg=cylAB(P(-1),P(end),R,40);let sh;
  if(style=='plat'){const w=op.w;sh=prismF(P((L-1)/2),w,cr(u,w),stad(op.W,d),L+3);if(Lc>0){const rT=Math.max(op.rT,r+1),T=2.04*rT,e3=cr(u,w),pA=[[-d/2,L-1],[d/2,L-1],[T/2,end+1],[-T/2,end+1]],pB=[[-op.W/2,L-1],[op.W/2,L-1],[T/2,end+1],[-T/2,end+1]];sh=union(sh,intersect(prismF(P(0),e3,u,pA,4*rT+20),prismF(P(0),w,u,pB,4*rT+20)))}}
  else if(style=='aronde'&&op.typ==3){const w=op.w,tn=Math.tan(op.theta*D),W=op.W,t=op.d,f=op.fl?-1:1;const pp=[[-W/2,-t/2*f],[W/2,-t/2*f],[W/2+t*tn,t/2*f],[-W/2-t*tn,t/2*f]];sh=prismF(P((L-1)/2),w,cr(u,w),f<0?pp.reverse():pp,L+3)}
  else if(style=='aronde'){const w=op.w,tn=Math.tan(op.theta*D),hw=x=>op.W/2+(L-x)*tn,o2=op.typ==2&&op.off,th=o2?d+(op.rT||d)+6:d,oc=o2?Math.sign(op.off)*th/2:(op.off||0);sh=prismF(add(P(0),mul(cr(u,w),oc)),w,u,[[-hw(-2),-2],[hw(-2),-2],[hw(L+1),L+1],[-hw(L+1),L+1]],th)}
  else{const r0=op.taper?r*op.taper:r;sh=coneAB(P(-2),r0-(r-r0)*2/Math.max(L,1),P(L+1),r+(r-r0)*1/Math.max(L,1),40);
   if(hache){const rT=Math.max(op.rT,r+1),k=(rT-r)/Lc;sh=union(sh,coneAB(P(L-1),r-k,P(end+1),rT+k,40))}}
  return subtract(reg,sh)}
 case'point':{const{o,u,L}=op,P=x=>add(o,mul(u,x)),R=op.rmax+3,k=(op.rT-op.r0)/L;return subtract(cylAB(P(-1),P(L),R,40),coneAB(P(-2),op.r0-2*k,P(L+1),op.rT+k,40))}
 }return null}
function mortiseOps(){}
/* géométrie finale d'une pièce = base − opérations */
function geo(o){if(GL.includes(o.type))return null;const k=o.ops&&o.ops.length?JSON.stringify(o.ops):'';if(o._gk===k&&o._gg===o.g&&o._fg)return o._fg;
 let g=o.g;for(const op of o.ops||[]){try{const c=cutter(op),r=subtract(g,c);if(G.toPolygons(r).length)g=r;else console.warn('opération vide',op.k)}catch(e){console.warn('opération ignorée',op.k,e)}}
 o._fg=g;o._gk=k;o._gg=o.g;o._wk=null;return g}
const wg=o=>{const g=geo(o),k=o.pos.join()+'|'+o.rot.join();if(o._w&&o._wk===k&&o._wg===g)return o._w;let w=g;const[x,y,z]=o.rot.map(d=>d*D);if(x)w=rotateX(x,w);if(y)w=rotateY(y,w);if(z)w=rotateZ(z,w);o._w=translate(o.pos,w);o._wg=g;o._wk=k;return o._w};
const solids=()=>objs.filter(o=>!GL.includes(o.type));
/* ---------- Maillage 3D avec normales lissées par angle ---------- */
function toGeo(g){const tri=[];for(const pl of G.toPolygons(g)){const v=pl.vertices;for(let i=1;i<v.length-1;i++)tri.push([v[0],v[i],v[i+1]])}
 const fnr=[],map=new Map(),key=v=>Math.round(v[0]*50)+','+Math.round(v[1]*50)+','+Math.round(v[2]*50);
 tri.forEach((t,i)=>{let n=cr(sub(t[1],t[0]),sub(t[2],t[0]));const l=len(n);fnr.push(l>1e-12?mul(n,1/l):[0,0,1]);for(const v of t){const k=key(v);let a=map.get(k);if(!a)map.set(k,a=[]);a.push(i)}});
 const pos=new Float32Array(tri.length*9),nor=new Float32Array(tri.length*9),C=.78;
 tri.forEach((t,i)=>t.forEach((v,j)=>{let s=[0,0,0];for(const q of map.get(key(v)))if(dot(fnr[i],fnr[q])>C)s=add(s,fnr[q]);s=nrm(s);const o=i*9+j*3;pos[o]=v[0];pos[o+1]=v[1];pos[o+2]=v[2];nor[o]=s[0];nor[o+1]=s[1];nor[o+2]=s[2]}));
 const b=new THREE.BufferGeometry();b.setAttribute('position',new THREE.BufferAttribute(pos,3));b.setAttribute('normal',new THREE.BufferAttribute(nor,3));return b}
/* ---------- Arêtes vives : sous-découpe des jonctions en T, puis angle entre faces voisines ---------- */
function featEdges(pols){const idm=new Map(),V=[],q=p=>Math.round(p[0]*100)+','+Math.round(p[1]*100)+','+Math.round(p[2]*100),vid=p=>{const k=q(p);let i=idm.get(k);if(i==null){i=V.length;idm.set(k,i);V.push(p)}return i};
 const F=[];for(const vs of pols){if(vs.length<3)continue;let nx=0,ny=0,nz=0;for(let i=0;i<vs.length;i++){const a=vs[i],b=vs[(i+1)%vs.length];nx+=(a[1]-b[1])*(a[2]+b[2]);ny+=(a[2]-b[2])*(a[0]+b[0]);nz+=(a[0]-b[0])*(a[1]+b[1])}const l=Math.hypot(nx,ny,nz);if(l<1e-9)continue;F.push({v:vs.map(vid),n:[nx/l,ny/l,nz/l]})}
 const ord=V.map((_,i)=>i).sort((a,b)=>V[a][0]-V[b][0]),xs=ord.map(i=>V[i][0]),eps=.03,E=new Map();
 const lb=x=>{let lo=0,hi=xs.length;while(lo<hi){const m=(lo+hi)>>1;if(xs[m]<x)lo=m+1;else hi=m}return lo};
 for(const f of F){const n=f.v.length;for(let i=0;i<n;i++){const a=f.v[i],b=f.v[(i+1)%n];if(a==b)continue;const A=V[a],B=V[b],d=sub(B,A),dd=dot(d,d),mids=[];
   const x0=Math.min(A[0],B[0])-eps,x1=Math.max(A[0],B[0])+eps,y0=Math.min(A[1],B[1])-eps,y1=Math.max(A[1],B[1])+eps,z0=Math.min(A[2],B[2])-eps,z1=Math.max(A[2],B[2])+eps;
   for(let k=lb(x0);k<xs.length&&xs[k]<=x1;k++){const j=ord[k];if(j==a||j==b)continue;const P=V[j];if(P[1]<y0||P[1]>y1||P[2]<z0||P[2]>z1)continue;const t=dot(sub(P,A),d)/dd;if(t<=1e-5||t>=1-1e-5)continue;const Q=sub(P,add(A,mul(d,t)));if(dot(Q,Q)<eps*eps)mids.push([t,j])}
   mids.sort((u,v)=>u[0]-v[0]);const chain=[a,...mids.map(m=>m[1]),b];
   for(let k=0;k+1<chain.length;k++){const u=chain[k],w=chain[k+1],key=u<w?u+'_'+w:w+'_'+u;let e=E.get(key);if(!e){e={u,w,n:[]};E.set(key,e)}e.n.push(f.n)}}}
 return[...E.values()].map(e=>({p:V[e.u],q:V[e.w],n:e.n}))}
const edgeMat=()=>new THREE.LineBasicMaterial({color:0x2a2a2a,transparent:true,opacity:.45});
const thinGeo=pols=>{let a=[1e9,1e9,1e9],z=[-1e9,-1e9,-1e9];pols.forEach(p=>p.forEach(v=>{for(let i=0;i<3;i++){a[i]=Math.min(a[i],v[i]);z[i]=Math.max(z[i],v[i])}}));const s=[0,1,2].map(i=>z[i]-a[i]).sort((x,y)=>x-y);return s[1]<45};
const sharpEdges=(pols,cosT=.955)=>thinGeo(pols)?[]:featEdges(pols).filter(e=>e.n.length>=2&&Math.min(...e.n.slice(1).map(m=>dot(e.n[0],m)))<cosT);
function mergeG(gs){let n=0;gs=gs.map(g=>g.index?g.toNonIndexed():g);gs.forEach(g=>n+=g.attributes.position.count);const P=new Float32Array(n*3),N=new Float32Array(n*3);let o=0;gs.forEach(g=>{P.set(g.attributes.position.array,o);N.set(g.attributes.normal.array,o);o+=g.attributes.position.count*3});const b=new THREE.BufferGeometry();b.setAttribute('position',new THREE.BufferAttribute(P,3));b.setAttribute('normal',new THREE.BufferAttribute(N,3));return b}
/* ---------- Brêlage (dernier recours) : tours de corde + nœud de cabestan au départ ---------- */
function lashGeoP(o){const rp=o.p.rope/2,gs=[];for(const P of o.p.paths){const pts=P.pts.map(q=>new THREE.Vector3(...q));if(pts.length<2)continue;const cv=new THREE.CatmullRomCurve3(pts,!!P.closed,'centripetal');gs.push(new THREE.TubeGeometry(cv,Math.max(8,pts.length*3),P.r||rp,6,!!P.closed))}return gs.length?mergeG(gs):new THREE.BufferGeometry()}
function lashGeo(o){if(o.p.paths)return lashGeoP(o);const p=o.p,rp=p.rope/2,gs=[],Z=new THREE.Vector3(0,0,1);
 const ring=(c,u,R,rt,tilt)=>{const g=new THREE.TorusGeometry(R,rt,8,28),m=new THREE.Matrix4().makeRotationFromQuaternion(new THREE.Quaternion().setFromUnitVectors(Z,new THREE.Vector3(...nrm(u))));if(tilt)m.multiply(new THREE.Matrix4().makeRotationX(tilt));m.setPosition(...c);g.applyMatrix4(m);gs.push(g)};
 for(const s of p.parts){const{c,u,r}=s,step=p.rope*1.05,[e1]=bas(u);
  for(let i=0;i<p.turns;i++)ring(add(c,mul(u,(i-(p.turns-1)/2)*step)),u,r+rp+(i%2?0:.3),rp);
  if(s.knot){const c0=add(c,mul(u,-((p.turns-1)/2+1)*step));ring(c0,u,r+rp*1.2,rp*1.1,.5);ring(c0,u,r+rp*1.2,rp*1.1,-.5);const tail=new THREE.CylinderGeometry(rp,rp,p.rope*4,8),m=new THREE.Matrix4().makeRotationFromQuaternion(new THREE.Quaternion().setFromUnitVectors(new THREE.Vector3(0,1,0),new THREE.Vector3(...e1)));m.setPosition(...add(add(c0,mul(e1,r+rp*3)),mul(e1,p.rope)));tail.applyMatrix4(m);gs.push(tail)}}
 return mergeG(gs)}
function phGeo(o){const r=Math.max(o.p.d,5)/2,gs=[],Y=new THREE.Vector3(0,1,0);for(const[A,B]of o.p.segs){const v=new THREE.Vector3(...sub(B,A)),l=v.length();if(l<1)continue;const g=new THREE.CylinderGeometry(r,r,l,6),m=new THREE.Matrix4().makeRotationFromQuaternion(new THREE.Quaternion().setFromUnitVectors(Y,v.clone().normalize()));m.setPosition(...mul(add(A,B),.5));g.applyMatrix4(m);gs.push(g)}return gs.length?mergeG(gs):new THREE.BufferGeometry()}
const phLen=o=>o.p.segs.reduce((s,[a,b])=>s+len(sub(b,a)),0);
function ropeLen(o){if(o.p.paths){let L=0;for(const P of o.p.paths)for(let i=1;i<P.pts.length;i++)L+=len(sub(P.pts[i],P.pts[i-1]));return L*1.15}let L=0;for(const s of o.p.parts)L+=o.p.turns*2*Math.PI*(s.r+o.p.rope/2)+(s.knot?400:0);return L*1.25}
/* ---------- Création / suppression d'objets ---------- */
function freeSpot(){const S=solids().concat(objs.filter(o=>GL.includes(o.type)));if(!S.length)return[0,0,0];const[,mx]=bounds(S);return[Math.round(mx[0]/100)*100+300,0,0]}
function mkObj(type,p,g,name,color,pos,rot,par){const o={id:nid++,type,p:p||{...SPEC[type].d},rot:rot||[0,0,0],pos:pos||freeSpot(),color:color||(AX2.includes(type)&&type=='trav'?WC[nid%4]:'#b8bcc4'),par:par||0,mat:'',ops:[]};
 o.name=name||SPEC[type].n+' '+o.id;if(!GL.includes(type))o.g=g||build(o);objs.push(o);mk(o);touch();return o}
function addObj(type,p,g,name,color,pos,rot,par){const o=mkObj(type,p,g,name,color,pos,rot,par);select([o]);return o}
const WC=['#c8a06a','#bd935a','#d2ab76','#b5894f'];
function rmObjs(list){list=new Set(list);list.forEach(o=>{sc.remove(o.m);o.m.geometry.dispose()});objs=objs.filter(o=>!list.has(o));sel=sel.filter(o=>!list.has(o));touch()}
const bounds=(L=solids())=>{const b=new THREE.Box3();L.forEach(o=>{o.m.updateMatrixWorld(true);b.expandByObject(o.m)});return L.length?[b.min.toArray(),b.max.toArray()]:[[0,0,0],[1,1,1]]};
/* ---------- Arborescence : assemblages et sous-assemblages ---------- */
const kidsP=a=>objs.filter(o=>o.par==a),kidsA=a=>Object.values(asms).filter(x=>x.par==a);
function piecesOf(a){let L=kidsP(a);kidsA(a).forEach(x=>L=L.concat(piecesOf(x.id)));return L}
function isDesc(a,b){let x=asms[a];while(x){if(x.id==b)return true;x=asms[x.par]}return false}
function newAsm(name,par){const a={id:aid++,n:name||'Assemblage '+aid,par:par||0,mat:''};asms[a.id]=a;return a}
function moveTo(nodes,parent){for(const n of nodes){if(n.t=='p'){const o=objs.find(x=>x.id==n.id);if(o)o.par=parent}else if(n.id!=parent&&!(parent&&isDesc(parent,n.id))){asms[n.id].par=parent}}touch()}
function asmPath(o){const L=[];let a=asms[o.par];while(a){L.unshift(a.n);a=asms[a.par]}return L}
function delAsm(id,withKids){const a=asms[id];if(!a)return;if(withKids){const P=piecesOf(id);const subs=[];(function w(i){kidsA(i).forEach(x=>{subs.push(x.id);w(x.id)})})(id);subs.forEach(i=>delete asms[i]);rmObjs(P)}else{kidsP(id).forEach(o=>o.par=a.par);kidsA(id).forEach(x=>x.par=a.par)}delete asms[id];touch()}

/* =====================  Scène 3D (Z vers le haut)  ===================== */
const R=new THREE.WebGLRenderer({antialias:true});R.setPixelRatio(Math.min(devicePixelRatio||1,2));$('#v').appendChild(R.domElement);
const sc=new THREE.Scene();sc.background=new THREE.Color(0xf4f5f7);
const camP=new THREE.PerspectiveCamera(45,1,1,400000);camP.up.set(0,0,1);camP.position.set(2500,-3500,2200);let cam=camP;
const camO=new THREE.OrthographicCamera(-1,1,1,-1,1,1e6);camO.up.set(0,0,1);
let oc=null,pickMode=null,gzS=null,gzC=[0,0,0];
const rc=new THREE.Raycaster();
const ndc=e=>{const b=R.domElement.getBoundingClientRect();return{x:(e.clientX-b.left)/b.width*2-1,y:-(e.clientY-b.top)/b.height*2+1}};
/* ----- poignées : flèches de translation + petites flèches courbes de rotation (comme FreeCAD) ----- */
const GZ=new THREE.Group(),AXC=[0xe03a3a,0x2fa84f,0x2f6fdb],AXV=[[1,0,0],[0,1,0],[0,0,1]],gH=[];GZ.visible=false;sc.add(GZ);
{const hm=c=>new THREE.MeshBasicMaterial({color:c,depthTest:false,transparent:true,opacity:.92}),inv=()=>new THREE.MeshBasicMaterial({transparent:true,opacity:0,depthTest:false,depthWrite:false}),V=a=>new THREE.Vector3(...a);
 for(let i=0;i<3;i++){const col=AXC[i],m=hm(col),a=new THREE.Group();
  const sh=new THREE.Mesh(new THREE.CylinderGeometry(.03,.03,.78,10),m);sh.position.y=.39;const hd=new THREE.Mesh(new THREE.ConeGeometry(.09,.24,14),m);hd.position.y=.9;
  const pk=new THREE.Mesh(new THREE.CylinderGeometry(.11,.11,1.05,8),inv());pk.position.y=.52;a.add(sh,hd,pk);a.quaternion.setFromUnitVectors(V([0,1,0]),V(AXV[i]));a.userData={h:'t',i,m,col};GZ.add(a);gH.push(a);
  const r=new THREE.Group(),m2=hm(col),arc=new THREE.Mesh(new THREE.TorusGeometry(.5,.03,8,24,70*D),m2);arc.rotation.z=10*D;
  const cn=new THREE.Mesh(new THREE.ConeGeometry(.075,.2,12),m2);cn.position.set(Math.cos(80*D)*.5,Math.sin(80*D)*.5,0);cn.rotation.z=80*D;
  const pk2=new THREE.Mesh(new THREE.TorusGeometry(.5,.1,6,24,70*D),inv());pk2.rotation.z=10*D;r.add(arc,cn,pk2);
  const B=[[AXV[1],AXV[2],AXV[0]],[AXV[2],AXV[0],AXV[1]],[AXV[0],AXV[1],AXV[2]]][i];r.quaternion.setFromRotationMatrix(new THREE.Matrix4().makeBasis(V(B[0]),V(B[1]),V(B[2])));r.userData={h:'r',i,m:m2,col};GZ.add(r);gH.push(r)}}
/* poignées d'étirement (longueur) aux deux bouts d'une traverse sélectionnée + règle graduée pendant le glissement */
let stretchOn=false;const SHD=[0,1].map(end=>{const g=new THREE.Group(),m=new THREE.MeshBasicMaterial({color:0xe08a00,depthTest:false,transparent:true,opacity:.95}),c=new THREE.Mesh(new THREE.ConeGeometry(.13,.36,16),m),pk=new THREE.Mesh(new THREE.SphereGeometry(.28,8,8),new THREE.MeshBasicMaterial({transparent:true,opacity:0,depthTest:false,depthWrite:false}));c.position.y=.18;g.add(c,pk);g.userData={h:'s',end,m};g.visible=false;sc.add(g);gH.push(g);return g});
const RUL=new THREE.LineSegments(new THREE.BufferGeometry(),new THREE.LineBasicMaterial({color:0xe08a00,depthTest:false}));RUL.visible=false;RUL.renderOrder=9;sc.add(RUL);
const RLB=document.createElement('div');RLB.style.cssText='position:absolute;pointer-events:none;background:#e08a00;color:#fff;font-size:12px;padding:1px 6px;border-radius:8px;display:none;z-index:5';$('#v').appendChild(RLB);
function rulerDraw(A,dir,d,step,txt){const n=Math.abs(d),sg=d<0?-1:1;if(n<1e-6){RUL.visible=false;RLB.style.display='none';return}let st=step||10;while(n/st>40)st*=2;const P=[],[e1]=bas(dir),tk=cam.position.distanceTo(new THREE.Vector3(...A))*.012;P.push(...A,...add(A,mul(dir,d)));for(let t=0;t<=n+1e-6;t+=st){const q=add(A,mul(dir,sg*t)),big=Math.round(t/st)%5==0,h=tk*(big?1.8:1);P.push(...sub(q,mul(e1,h)),...add(q,mul(e1,h)))}RUL.geometry.dispose();RUL.geometry=new THREE.BufferGeometry();RUL.geometry.setAttribute('position',new THREE.BufferAttribute(new Float32Array(P),3));RUL.visible=true;
 const e=add(A,mul(dir,d)),v=new THREE.Vector3(...e).project(cam),b=R.domElement.getBoundingClientRect();RLB.textContent=txt;RLB.style.display='block';RLB.style.left=((v.x+1)/2*b.width+10)+'px';RLB.style.top=((1-v.y)/2*b.height-10)+'px'}
function angDraw(c,ev,a0,d,step,txt){const[e1,e2]=bas(ev),R_=cam===camO?(camO.top-camO.bottom)/camO.zoom*.2:cam.position.distanceTo(new THREE.Vector3(...c))*.2,pt=(a,r)=>add(c,add(mul(e1,Math.cos(a)*r),mul(e2,Math.sin(a)*r))),P=[],n=Math.max(24,Math.ceil(Math.abs(d)/D/3));for(let i=0;i<n;i++){P.push(...pt(a0+d*i/n,R_),...pt(a0+d*(i+1)/n,R_))}P.push(...c,...pt(a0,R_*1.15),...c,...pt(a0+d,R_*1.15));let st=step||15;while(Math.abs(d)/D/st>45)st*=2;const sg=d<0?-1:1;for(let t=0;t<=Math.abs(d)/D+1e-6;t+=st){const a=a0+sg*t*D,big=Math.round(t/st)%5==0;P.push(...pt(a,R_*(big?.86:.93)),...pt(a,R_*1.07))}RUL.geometry.dispose();RUL.geometry=new THREE.BufferGeometry();RUL.geometry.setAttribute('position',new THREE.BufferAttribute(new Float32Array(P),3));RUL.visible=true;const v=new THREE.Vector3(...pt(a0+d,R_*1.2)).project(cam),b=R.domElement.getBoundingClientRect();RLB.textContent=txt;RLB.style.display='block';RLB.style.left=((v.x+1)/2*b.width+10)+'px';RLB.style.top=((1-v.y)/2*b.height-10)+'px'}
const rulerOff=()=>{RUL.visible=false;RLB.style.display='none'};
const targets=()=>selA!=null?piecesOf(selA):sel;
function gzCenter(){const T=targets();if(!T.length){GZ.visible=false;return}const[mn,mx]=bounds(T);gzC=mn.map((v,i)=>(v+mx[i])/2);req()}
function gzPlace(){const T=targets();SHD.forEach(g=>g.visible=false);if(T.length==1&&selA==null&&!pickMode&&T[0].type=='trav'&&!gzS&&stretchOn){const o=T[0],ax=axisOf(o),sc_=cam===camO?(camO.top-camO.bottom)/camO.zoom*.1:cam.position.distanceTo(new THREE.Vector3(...ax.p0))*.1;SHD.forEach((g,i)=>{const E=i?ax.p1:ax.p0,dir=i?ax.u:mul(ax.u,-1);g.position.set(...E);g.quaternion.setFromUnitVectors(new THREE.Vector3(0,1,0),new THREE.Vector3(...dir));g.scale.setScalar(sc_);g.visible=true})}if(!T.length||pickMode){GZ.visible=false;return}GZ.visible=true;GZ.position.set(...gzC);GZ.scale.setScalar(cam===camO?(camO.top-camO.bottom)/camO.zoom*.15:cam.position.distanceTo(GZ.position)*.16)}
function gzHit(e){if(!GZ.visible)return null;rc.setFromCamera(ndc(e),cam);const h=rc.intersectObjects(gH,true)[0];if(!h)return null;let o=h.object;while(o&&!o.userData.h)o=o.parent;return o?o.userData:null}
function axisParam(ray,c,ev){const O=ray.origin.toArray(),d=ray.direction.toArray(),w0=sub(c,O),b=dot(ev,d),den=1-b*b;return den<1e-6?0:(b*dot(d,w0)-dot(ev,w0))/den}
function planeAngle(ray,c,ev){const O=ray.origin.toArray(),d=ray.direction.toArray(),dn=dot(d,ev);if(Math.abs(dn)<1e-6)return null;const s=dot(sub(c,O),ev)/dn,v=sub(add(O,mul(d,s)),c),[e1,e2]=bas(ev);return Math.atan2(dot(v,e2),dot(v,e1))}
const _p=new THREE.Vector3(),_q=new THREE.Quaternion(),_s=new THREE.Vector3();
function setMat(o,M){M.decompose(_p,_q,_s);o.pos=_p.toArray();const E=new THREE.Euler().setFromQuaternion(_q,'ZYX');o.rot=[E.x/D,E.y/D,E.z/D];o.m.position.copy(_p);o.m.quaternion.copy(_q);o.m.updateMatrixWorld()}
R.domElement.addEventListener('pointerdown',e=>{if(e.button!==0||pickMode)return;const h=gzHit(e);if(!h)return;e.stopImmediatePropagation();rc.setFromCamera(ndc(e),cam);
 if(h.h=='s'){const o=sel[0],ax=axisOf(o);if(h.end==0&&o.ops&&o.ops.length){msg('Cette extrémité porte déjà des opérations : étirez l’autre bout, ou supprimez-les d’abord.',5000);return}const E=h.end?ax.p1:ax.p0;gzS={h:'s',end:h.end,o,u:ax.u,E:[...E],L0:o.p.L,pos0:[...o.pos],pid:e.pointerId,v0:axisParam(rc.ray,E,ax.u),d:0};R.domElement.setPointerCapture(e.pointerId);return}
 const ev=AXV[h.i];
 gzS={h:h.h,i:h.i,ev,c:[...gzC],init:moveTargets().map(o=>[o,matOf(o)]),pid:e.pointerId,v0:h.h=='t'?axisParam(rc.ray,gzC,ev):planeAngle(rc.ray,gzC,ev)};R.domElement.setPointerCapture(e.pointerId);if(gzS.v0==null)gzS=null},true);
R.domElement.addEventListener('pointermove',e=>{if(!gzS)return;rc.setFromCamera(ndc(e),cam);
 if(gzS.h=='s'){const s=gzS;let d=axisParam(rc.ray,s.E,s.u)-s.v0;if(snapOn)d=Math.round(d/stepT)*stepT;const L=s.end?s.L0+d:s.L0-d;if(L<20)return;s.d=d;const o=s.o;o.p.L=L;if(!s.end)o.pos=add(s.pos0,mul(s.u,d));o.g=build(o);o._gk=null;mk(o);o.m.position.set(...o.pos);ver++;req();rulerDraw(s.E,s.u,d,snapOn?stepT:10,'Longueur '+sm(L));setHint('Longueur : '+sm(L));return}
 const{ev,c,init}=gzS;let M;
 if(gzS.h=='t'){let d=axisParam(rc.ray,c,ev)-gzS.v0;if(snapOn)d=Math.round(d/stepT)*stepT;rulerDraw(c,ev,d,snapOn?stepT:10,sm(Math.abs(d))+(d<0?' (−)':''));M=new THREE.Matrix4().makeTranslation(...mul(ev,d));gzS.d=d;setHint(`Déplacement ${'XYZ'[gzS.i]} : ${r1(d*uk())} ${us()}`)}
 else{const a=planeAngle(rc.ray,c,ev);if(a==null)return;let d=a-gzS.v0;while(d>Math.PI)d-=2*Math.PI;while(d<-Math.PI)d+=2*Math.PI;if(snapOn)d=Math.round(d/D/stepR)*stepR*D;gzS.d=d;angDraw(c,ev,gzS.v0,d,stepR,r1(d/D)+'°');
  M=new THREE.Matrix4().makeTranslation(...c).multiply(new THREE.Matrix4().makeRotationAxis(new THREE.Vector3(...ev),d)).multiply(new THREE.Matrix4().makeTranslation(...mul(c,-1)));setHint(`Rotation autour de ${'XYZ'[gzS.i]} : ${r1(d/D)}°`)}
 for(const[o,M0]of init)setMat(o,M.clone().multiply(M0));if(gzS.h=='t')gzC=add(c,mul(ev,gzS.d));ver++;req();gzFields()});
addEventListener('pointerup',()=>{if(!gzS)return;const had=gzS.d;gzS=null;rulerOff();setHint();if(had)touch();gzCenter();ui()},true);
function gzFields(){const o=sel.length==1&&!selA?sel[0]:null;if(!o)return;[...o.pos,...o.rot].forEach((v,i)=>{const e=$((i<3?'#p':'#r')+i%3);if(e)e.value=r1(i<3?v*uk():v)})}
function setHint(t){const h=$('#hint');h.textContent=t||HINTS();h.style.display=(t||HINTS())?'':'none'}
const HINTS=()=>pickMode?pickMode.prompt+'  (Échap : annuler)':'';
/* ----- orbite ----- */
oc=new THREE.OrbitControls(cam,R.domElement);oc.addEventListener('change',req);oc.screenSpacePanning=true;
sc.add(new THREE.AmbientLight(0xffffff,.65));const dl=new THREE.DirectionalLight(0xffffff,.8);dl.position.set(500,-800,1000);sc.add(dl);
const gr=new THREE.GridHelper(40000,400,0xdddddd,0xe6e7ea),gr2=new THREE.GridHelper(40000,40,0x999999,0xb9bcc2);gr.rotation.x=gr2.rotation.x=Math.PI/2;sc.add(gr,gr2);const axh=new THREE.AxesHelper(500);sc.add(axh);
function rs(){const e=$('#v'),w=e.clientWidth||300,h=e.clientHeight||300;if(e.clientWidth>50)vpA=w/h;R.setSize(w,h);camP.aspect=w/h;camP.updateProjectionMatrix();camO.left=-camO.top*w/h;camO.right=camO.top*w/h;camO.updateProjectionMatrix();req()}
addEventListener('resize',rs);
/* ----- matériaux, maillage ----- */
function mk(o){if(o.m){sc.remove(o.m);o.m.geometry.dispose()}
 const bg=o.type=='lash'?lashGeo(o):o.type=='ph'?phGeo(o):toGeo(geo(o)),m=new THREE.Mesh(bg,new THREE.MeshStandardMaterial({color:o.color,roughness:.75,metalness:.05,side:THREE.DoubleSide,transparent:ghost,opacity:ghost?.35:1}));
 if(!GL.includes(o.type)&&o.type!='courbe'){const ed=sharpEdges(polysOf(geo(o))),pa=new Float32Array(ed.length*6);ed.forEach((e,i)=>pa.set([...e.p,...e.q],i*6));const lg=new THREE.BufferGeometry();lg.setAttribute('position',new THREE.BufferAttribute(pa,3));m.add(new THREE.LineSegments(lg,edgeMat()))}
 m.position.set(...o.pos);m.rotation.order='ZYX';m.rotation.set(...o.rot.map(d=>d*D));o.m=m;sc.add(m);req()}
function toggleGhost(){ghost=!ghost;objs.forEach(o=>{o.m.material.transparent=ghost;o.m.material.opacity=ghost?.35:1;o.m.material.depthWrite=!ghost;o.m.material.needsUpdate=true});buildRibbon();req()}
function emi(h){const S=new Set(targets());objs.forEach(o=>{if(o.m)o.m.material.emissive.set(pickMode&&o===h?0x3a6a1a:S.has(o)?0x10285a:o===h?0x2a2a2a:0)});req()}
/* ----- sélection ----- */
function select(list,a){if(!(list&&list.length==1&&sel.length==1&&sel[0]===list[0]))stretchOn=false;sel=list||[];selA=a==null?null:a;if(selA!=null&&!asms[selA])selA=null;gzCenter();emi();ui();req();if(typeof buildRibbon=='function'&&MODEL_TABS.includes(viewTab))buildRibbon()}
const selAsm=a=>select([],a);
function pickAt(e){const b=R.domElement.getBoundingClientRect();rc.setFromCamera({x:(e.clientX-b.left)/b.width*2-1,y:-(e.clientY-b.top)/b.height*2+1},cam);const h=rc.intersectObjects(objs.map(o=>o.m),false)[0];
 /* les cordes (PH, filets) sont très fines : on les attrape à quelques pixels près, si elles sont devant ce qui est derrière */
 let best=null,bd=1e18;const V0=new THREE.Vector3(),V1=new THREE.Vector3(),Pr=new THREE.Vector3();for(const o of objs){if(o.type!='ph'||!o.p.segs)continue;for(const s of o.p.segs){V0.set(...s[0]);V1.set(...s[1]);const d2=rc.ray.distanceSqToSegment(V0,V1,Pr),dist=Pr.distanceTo(rc.ray.origin),tol=cam===camO?(camO.top-camO.bottom)/camO.zoom*.012:dist*.012;if(d2<tol*tol&&dist<bd&&(!h||dist<h.distance+5)){bd=dist;best=o}}}
 if(best)return best;return h?objs.find(x=>x.m===h.object):null}
let dn=null;R.domElement.addEventListener('pointerdown',e=>{dn=e.button==0?[e.clientX,e.clientY]:null});
R.domElement.addEventListener('pointerup',e=>{if(e.button!=0||!dn||Math.hypot(e.clientX-dn[0],e.clientY-dn[1])>4)return;dn=null;const o=pickAt(e);hideCm();
 if(pickMode){if(o){const f=pickMode.cb;pickMode=null;R.domElement.style.cursor='';setHint();emi();gzCenter();f(o)}return}
 if(e.shiftKey||e.ctrlKey||e.metaKey){if(!o)return;const L=selA!=null?[]:sel.slice(),i=L.indexOf(o);i<0?L.push(o):L.splice(i,1);select(L)}else{select(o?[o]:[]);if(o)revealSel()}});
R.domElement.addEventListener('dblclick',e=>{const o=pickAt(e);if(!o||pickMode)return;if(sideTab!='prop')sideSet('prop');if(editable(o))return editObj(o);if(o.par&&asms[o.par]&&asms[o.par].src&&asms[o.par].src.t=='clay'&&/^Claie|^Traverse fine/.test(o.name))return clayWin(null,o.par);let a=o.par;if(a&&selA==a&&asms[a].par)a=asms[a].par;if(a)selAsm(a);else msg('Cette pièce n’est dans aucun assemblage.')});
R.domElement.addEventListener('pointermove',e=>{if(e.buttons||gzS)return;const g=gzHit(e),h=g?null:pickAt(e);R.domElement.style.cursor=pickMode?'crosshair':g?'grab':h?'pointer':'';gH.forEach(x=>x.userData.m.opacity=g&&x.userData===g?1:.78);emi(h)});
let cmDn=null;R.domElement.addEventListener('pointerdown',e=>{if(e.button==2)cmDn=[e.clientX,e.clientY]},true);
R.domElement.addEventListener('pointerup',e=>{if(e.button==2&&cmDn&&Math.hypot(e.clientX-cmDn[0],e.clientY-cmDn[1])<5)ctx3d(e,pickAt(e));cmDn=null});
R.domElement.addEventListener('contextmenu',e=>e.preventDefault());
function askPick(prompt,cb){pickMode={prompt,cb};R.domElement.style.cursor='crosshair';setHint();gzCenter();emi();msg(prompt,4500)}

/* ---------- ViewCube chanfreiné : 6 faces, 12 arêtes, 8 coins ---------- */
const cs=new THREE.Scene(),cc=new THREE.OrthographicCamera(-1.6,1.6,1.6,-1.6,.1,30),cells=[],VC=120,CH=.34,a1=1-CH,LAB={'0,-1,0':'Face','0,1,0':'Arrière','1,0,0':'Droite','-1,0,0':'Gauche','0,0,1':'Dessus','0,0,-1':'Dessous'};
const Vs=(a,b)=>[a[0]-b[0],a[1]-b[1],a[2]-b[2]],Vc=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]],Vd=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2];
cs.add(new THREE.AmbientLight(0xffffff,.72));const hlt=new THREE.DirectionalLight(0xffffff,.55);cs.add(hlt);
function lab(t,bg){const c=document.createElement('canvas');c.width=c.height=128;const x=c.getContext('2d');x.fillStyle=bg;x.fillRect(0,0,128,128);x.fillStyle='#1d2330';x.font='bold 26px sans-serif';x.textAlign='center';x.textBaseline='middle';x.fillText(t,64,66);return new THREE.CanvasTexture(c)}
function cell(vs,d,col,tex){if(Vd(Vc(Vs(vs[1],vs[0]),Vs(vs[2],vs[0])),d)<0)vs=vs.slice().reverse();
 const pos=[],uv=[],uvf=p=>[(Vd(p,tex.r)/a1+1)/2,(Vd(p,tex.u)/a1+1)/2];
 for(let i=1;i<vs.length-1;i++){pos.push(...vs[0],...vs[i],...vs[i+1]);if(tex)uv.push(...uvf(vs[0]),...uvf(vs[i]),...uvf(vs[i+1]))}
 const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(pos,3));if(tex)g.setAttribute('uv',new THREE.Float32BufferAttribute(uv,2));g.computeVertexNormals();
 const m=new THREE.Mesh(g,new THREE.MeshLambertMaterial({color:tex?0xffffff:col,map:tex?tex.t:null,side:THREE.DoubleSide}));m.userData={d,c:tex?0xffffff:col};
 m.add(new THREE.LineSegments(new THREE.EdgesGeometry(g),new THREE.LineBasicMaterial({color:0x3d4452})));cs.add(m);cells.push(m)}
{const E=[[1,0,0],[0,1,0],[0,0,1]],S=[-1,1];
 for(let a=0;a<3;a++)for(const s of S){const n=E[a].map(x=>x*s),o=[0,1,2].filter(i=>i!=a),u=a==2?[0,1,0]:[0,0,1],r=Vc(u,n);
  cell([[-1,-1],[1,-1],[1,1],[-1,1]].map(([p,q])=>{const v=[0,0,0];v[a]=s;v[o[0]]=p*a1;v[o[1]]=q*a1;return v}),n,0xe9edf3,{t:lab(LAB[n.join(',')],'#e9edf3'),r,u})}
 for(let a=0;a<3;a++)for(let b=a+1;b<3;b++){const c=3-a-b;for(const sa of S)for(const sb of S){const d=[0,0,0];d[a]=sa;d[b]=sb;
  const vs=[-1,1].flatMap(sc=>{const p=[0,0,0],q=[0,0,0];p[a]=sa;p[b]=sb*a1;p[c]=sc*a1;q[a]=sa*a1;q[b]=sb;q[c]=sc*a1;return[p,q]});cell([vs[0],vs[1],vs[3],vs[2]],d,0xcdd3de)}}
 for(const sx of S)for(const sy of S)for(const sz of S)cell([[sx,sy*a1,sz*a1],[sx*a1,sy,sz*a1],[sx*a1,sy*a1,sz]],[sx,sy,sz],0xb3bbc9)}
const vcE=$('#vc'),vr=new THREE.Raycaster();let hv=null;
const hl=(m,on)=>{m.material.color.set(on?0x8ab8ff:m.userData.c);req()};
function vcHit(e){const b=vcE.getBoundingClientRect();vr.setFromCamera({x:(e.clientX-b.left)/b.width*2-1,y:-(e.clientY-b.top)/b.height*2+1},cc);const h=vr.intersectObjects(cells,false)[0];return h?h.object:null}
vcE.onpointermove=e=>{const o=vcHit(e);if(o!==hv){if(hv)hl(hv,false);hv=o;if(o)hl(o,true)}};
vcE.onpointerleave=()=>{if(hv)hl(hv,false);hv=null};
vcE.onclick=e=>{const o=vcHit(e);if(o)setViewV(o.userData.d)};

/* ----- vues ----- */
function setViewV(d){const[mn,mx]=objs.length?bounds(objs):[[-1500,-1500,0],[1500,1500,1500]],c=mn.map((v,i)=>(v+mx[i])/2),r=Math.max(...mx.map((v,i)=>v-mn[i]),600)*1.8,l=Math.hypot(...d),v=d.map(x=>x/l);if(!v[0]&&!v[1])v[1]=-.001;oc.target.set(...c);cam.position.set(c[0]+v[0]*r,c[1]+v[1]*r,c[2]+v[2]*r);ofit(r);oc.update();req()}
const VIEWS={iso:[.6,-.85,.6],front:[0,-1,0],back:[0,1,0],right:[1,0,0],left:[-1,0,0],top:[0,0,1],bottom:[0,0,-1]};
const setView=n=>setViewV(VIEWS[n]);
function ofit(r){if(cam!==camO)return;const a=R.domElement.clientWidth/Math.max(R.domElement.clientHeight,1);camO.zoom=1;camO.top=r*.414;camO.bottom=-r*.414;camO.left=-camO.top*a;camO.right=camO.top*a;camO.updateProjectionMatrix()}
function toggleProj(){const t=oc.target.clone(),dir=cam.position.clone().sub(t).normalize(),d=cam.position.distanceTo(t);
 if(cam===camP){const a=R.domElement.clientWidth/Math.max(R.domElement.clientHeight,1);camO.zoom=1;camO.top=d*Math.tan(camP.fov*Math.PI/360);camO.bottom=-camO.top;camO.left=-camO.top*a;camO.right=camO.top*a;camO.position.copy(cam.position);camO.updateProjectionMatrix();cam=camO}
 else{const hh=(camO.top-camO.bottom)/2/camO.zoom;camP.position.copy(t).addScaledVector(dir,hh/Math.tan(camP.fov*Math.PI/360));cam=camP}
 oc.object=cam;oc.update();req();buildRibbon()}
function fit(){if(!objs.length)return setView('iso');const[mn,mx]=bounds(objs),c=mn.map((v,i)=>(v+mx[i])/2),r=Math.max(...mx.map((v,i)=>v-mn[i]),600);oc.target.set(...c);cam.position.set(c[0]+r*.9,c[1]-r*1.3,c[2]+r*.9);ofit(r*1.8);oc.update();req()}
function toggleGrid(){const v=!gr.visible;gr.visible=gr2.visible=axh.visible=v;buildRibbon();req()}
/* ----- cotes 3D éditables ----- */
const wpt=l2w;
function dimDefs(o){const p=o.p,t=o.type,e=Math.max(...SPEC[t].f.map(([k])=>+p[k]||0),20)*.08,L=[],S=(k,a,b)=>L.push({k,a,b});
 if(t=='trav'){S('L',[p.d/2+e,0,0],[p.d/2+e,0,p.L]);S('d',[-p.d/2,0,p.L],[p.d/2,0,p.L])}
 else if(t=='box'){S('l',[0,-e,0],[p.l,-e,0]);S('w',[p.l+e,0,0],[p.l+e,p.w,0]);S('h',[-e,-e,0],[-e,-e,p.h])}
 else if(t=='cyl'){S('h',[p.r+e,0,0],[p.r+e,0,p.h]);S('r',[0,0,p.h],[p.r,0,p.h])}
 else if(t=='tube'){S('h',[p.ro+e,0,0],[p.ro+e,0,p.h]);S('ro',[0,0,p.h],[p.ro,0,p.h]);S('ri',[0,0,p.h],[-p.ri,0,p.h])}
 else if(t=='sph')S('r',[0,0,p.r],[p.r,0,p.r]);
 else if(t=='cone'){S('h',[p.r+e,0,0],[p.r+e,0,p.h]);S('r',[0,0,0],[p.r,0,0]);S('r2',[0,0,p.h],[p.r2,0,p.h])}
 else if(['tcar','corn','U','I'].includes(t)){S('w',[0,-e,0],[p.w,-e,0]);S('b',[p.w+e,0,0],[p.w+e,p.b,0]);S('h',[-e,-e,0],[-e,-e,p.h]);S('t',[0,0,p.h],[p.t,0,p.h])}
 return L}
function axes3(o){const p=o.p,t=o.type,W=q=>l2w(o,q),A=[];
 if(t=='trav')A.push({a:W([0,0,0]),b:W([0,0,p.L]),r:p.d/2});
 else if(t=='cyl'||t=='tube'||t=='cone')A.push({a:W([0,0,0]),b:W([0,0,p.h]),r:t=='cone'?Math.max(p.r,p.r2):p.r||p.ro});
 else if(t=='sph')A.push({c:W([0,0,p.r]),r:p.r,s:1});
 else if(o.revAx)A.push({a:W(o.revAx.a),b:W(o.revAx.b),r:o.revAx.r});
 return A}
let dlO=[],hotK=null;const PRE={r:'R',ro:'R',ri:'R',r2:'R',R:'R',d:'Ø'};
const sel1=()=>sel.length==1&&selA==null?sel[0]:null;
function dlBuild(){const L=$('#dl'),o=sel1();if(!L)return;if(!showDims||!o||!SPEC[o.type].f.length||GL.includes(o.type)){L.innerHTML='';dlO=[];return}
 dlO=dimDefs(o);L.innerHTML='<svg id="dls"><defs><marker id="ma" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0L10 5L0 10z" fill="#e08a00"/></marker></defs>'+dlO.map((d,i)=>`<line id="dl${i}" marker-start="url(#ma)" marker-end="url(#ma)"/>`).join('')+'</svg>'+dlO.map((d,i)=>`<button class="dlb" id="db${i}" onclick="dlEdit(${i})" title="Cliquez pour modifier">${PRE[d.k]||''}${r1(o.p[d.k]*uk())}</button>`).join('');req()}
const tmpV=new THREE.Vector3();
function dlUpdate(){const o=sel1();if(!dlO.length||!o)return;const w=R.domElement.clientWidth,h=R.domElement.clientHeight;
 dlO.forEach((d,i)=>{const sp=[d.a,d.b].map(q=>{const p=l2w(o,q);tmpV.set(p[0],p[1],p[2]).project(cam);return[(tmpV.x+1)/2*w,(1-tmpV.y)/2*h,tmpV.z]}),ln=document.getElementById('dl'+i),b=document.getElementById('db'+i)||document.getElementById('di'+i);
  if(!ln||!b)return;const vis=sp[0][2]<1&&sp[1][2]<1;ln.setAttribute('x1',sp[0][0]);ln.setAttribute('y1',sp[0][1]);ln.setAttribute('x2',sp[1][0]);ln.setAttribute('y2',sp[1][1]);
  ln.style.display=b.style.display=vis?'':'none';b.style.left=(sp[0][0]+sp[1][0])/2+'px';b.style.top=(sp[0][1]+sp[1][1])/2+'px';b.classList.toggle('hot',d.k==hotK);ln.classList.toggle('hot',d.k==hotK)})}
function dlEdit(i){const o=sel1(),d=dlO[i],b=document.getElementById('db'+i);if(!b||!o)return;const n=document.createElement('input');n.type='number';n.id='di'+i;n.className='dli';n.value=r1(o.p[d.k]*uk());n.style.left=b.style.left;n.style.top=b.style.top;b.replaceWith(n);n.focus();n.select();hotK=d.k;
 n.onkeydown=e=>{if(e.key=='Enter')n.blur();if(e.key=='Escape'){n.value=r1(o.p[d.k]*uk());n.blur()}};n.onblur=()=>{const v=+n.value/uk();if(v>0&&!isNaN(v))setP(d.k,v);hotK=null;ui()}}
function toggleDims(){showDims=!showDims;dlBuild();buildRibbon()}

$('#dl').addEventListener('wheel',e=>{e.preventDefault();R.domElement.dispatchEvent(new WheelEvent('wheel',{deltaY:e.deltaY,deltaMode:e.deltaMode,clientX:e.clientX,clientY:e.clientY,bubbles:true,cancelable:true}))},{passive:false});

/* =====================  Assemblages et opérations (calcul pur, puis application)  ===================== */
let JID=0;const PREF={rigid:true,jeu:1,theta:10,auteur:'',unit:'cm'};
const rad=o=>{const b=lbb(o),e=[0,1,2].map(i=>b.max[i]-b.min[i]),k=AX2.includes(o.type)?2:e.indexOf(Math.max(...e));return Math.max(...e.filter((_,i)=>i!=k))/2};
const crossMin=o=>{const b=lbb(o),e=[0,1,2].map(i=>b.max[i]-b.min[i]),k=AX2.includes(o.type)?2:e.indexOf(Math.max(...e));return Math.min(...e.filter((_,i)=>i!=k))};
const isWood=o=>o&&!['lash','courbe','cavalier','ph'].includes(o.type);
function segClose(p1,q1,p2,q2){const d1=sub(q1,p1),d2=sub(q2,p2),r=sub(p1,p2),a=dot(d1,d1),e=dot(d2,d2),f=dot(d2,r),c=dot(d1,r),b=dot(d1,d2),dn=a*e-b*b,cl=x=>Math.max(0,Math.min(1,x));
 let s=dn>1e-9?cl((b*f-c*e)/dn):0,t=(b*s+f)/e;if(t<0){t=0;s=cl(-c/a)}else if(t>1){t=1;s=cl((b-c)/a)}return[add(p1,mul(d1,s)),add(p2,mul(d2,t))]}
const TEN_NAMES={hache:'tenon classique (hachette)',scie:'tenon scié',plat:'tenon plat',aronde:'queue d’aronde'};
const ARO={1:'classique',2:'à mi-bois (traversante)',3:'trapézoïdale dans l’axe du cylindre'};
const DOF={tenon:'Bloque 4 degrés de liberté : reste la rotation autour du tenon et le glissement hors de la mortaise.',plat:'Bloque 5 degrés de liberté : reste le glissement hors de la mortaise.',aronde:'Bloque 5 degrés de liberté : reste le glissement latéral dans la rainure.',mibois:'Bloque 5 degrés de liberté : reste le décollement perpendiculaire aux pièces (ajoutez une cheville).',cheville:'Bloque la translation dans le plan perpendiculaire à la cheville ; reste la rotation autour d’elle.'};
function tenonDefaults(T,R){const dT=crossMin(T),wR=crossMin(R);return{dT,wR,d:Math.max(8,Math.round(Math.min(dT*.55,wR/3))),W:Math.max(15,Math.round(dT*.7)),Lc:Math.max(10,Math.round(dT*.8)),thick:Math.max(8,Math.round(Math.min(dT*.6,wR/3+8))),depth:Math.max(8,Math.round(wR/3))}}
let BATCH=null;
function refresh(...L){if(BATCH){L.forEach(o=>BATCH.add(o));return}L.forEach(o=>{mk(o)});if(L.some(o=>sel.includes(o)))select(sel,selA);touch()}
function batch(fn){BATCH=new Set();try{fn()}finally{const B=BATCH;BATCH=null;B.forEach(o=>mk(o));touch()}}
const tmpWith=(o,ops,rm)=>({...o,ops:[...o.ops.filter(p=>!rm||p.jid!==rm),...ops],_fg:null,_gk:null,_w:null,_wk:null});
/* ----- tenon / mortaise / queues d'aronde ----- */
/* distance de chaque bout à la jonction (moins le rayon) : sert à choisir le tenon et à détecter les assemblages impossibles */
function endGaps(A,B){const a=axisOf(A),b=axisOf(B),Bg=1e5,[pa,pb]=segClose(add(a.p0,mul(a.u,-Bg)),add(a.p1,mul(a.u,Bg)),add(b.p0,mul(b.u,-Bg)),add(b.p1,mul(b.u,Bg))),ta=dot(sub(pa,a.p0),a.u),tb=dot(sub(pb,b.p0),b.u);return[Math.min(Math.abs(ta),Math.abs(a.L-ta))-rad(A),Math.min(Math.abs(tb),Math.abs(b.L-tb))-rad(B)]}
function roleScore(A,B){const[sa,sb]=endGaps(A,B),m=Math.max(rad(A),rad(B));if(Math.abs(sa-sb)>m*.5)return sa<sb?-1:1;return crossMin(B)<crossMin(A)?1:-1}
function planTenon(T,R,opt){
 if(T===R||!isWood(T)||!isWood(R))throw new Error('Choisissez deux pièces de bois droites différentes.');
 {const[sa,sb]=endGaps(T,R),m=Math.max(rad(T),rad(R))*1.2;if(sa>m&&sb>m)throw new Error('Assemblage impossible : « '+T.name+' » et « '+R.name+' » se croisent en leur milieu, aucun bout n’entre dans l’autre. Utilisez un mi-bois ou des chevilles, ou rapprochez un bout de l’autre pièce.');if(sa>m&&sb<=m&&sb<sa*.5&&!(opt&&opt.keepRoles))throw new Error('Mauvais sens : c’est « '+R.name+' » dont le bout est près de la jonction. Cliquez ⇄ Inverser pour qu’elle porte le tenon.')}
 const df=tenonDefaults(T,R),st=(opt&&opt.style)||'hache',o=Object.assign({style:st,typ:1,d:(st=='plat'||st=='aronde')?df.thick:df.d,mort:'thru',jeu:PREF.jeu,W:df.W,Lc:df.Lc,theta:PREF.theta,taper:0,depth:df.depth},opt);if(o.style=='aronde'&&o.typ==3&&!(opt&&opt.d))o.d=df.thick;if(o.style=='aronde'&&!(opt&&opt.theta))o.theta=20;o.W=Math.round(o.W);
 if(!(o.d>=4))throw new Error('Diamètre ou épaisseur du tenon invalide.');
 const A=axisOf(T),Ra=axisOf(R),Rd=sub(Ra.p1,Ra.p0),dist=p=>{const t=Math.max(0,Math.min(1,dot(sub(p,Ra.p0),Rd)/dot(Rd,Rd)));return len(sub(p,add(Ra.p0,mul(Rd,t))))};
 let tip=A.p0,oth=A.p1;if(dist(A.p1)<dist(A.p0)){tip=A.p1;oth=A.p0}
 const a=nrm(sub(tip,oth)),ts=lineHits(R,tip,a);let iv=null;
 for(let i=0;i+1<ts.length;i+=2)if(ts[i]<-.5&&(!iv||ts[i]>iv[0]))iv=[ts[i],ts[i+1]];
 if(!iv)throw new Error('Le bout de « '+T.name+' » doit pénétrer dans « '+R.name+' ». Rapprochez les deux pièces avec les flèches de déplacement.');
 let L=-iv[0];const h=iv[1];if(L<8)throw new Error('Le tenon serait trop court (moins de 8 mm) : enfoncez davantage la pièce.');
 if(-h>120)throw new Error('La pièce dépasse de '+Math.round(-h)+' mm de l’autre côté : reculez-la pour qu’elle ne dépasse que de quelques millimètres.');
 const dT=crossMin(T),wR=crossMin(R);let w=sub(Ra.u,mul(a,dot(Ra.u,a)));w=len(w)>.2?nrm(w):bas(a)[0];
 const S=add(tip,mul(a,iv[0])),aro=st=='aronde',thru=!aro&&(o.mort=='thru'||h<0),uT=dw2l(T,mul(a,-1)),aR=dw2l(R,a),SR=w2l(R,S),wL=dw2l(T,w),wRl=dw2l(R,w),warn=[],ops=[];
 let tipL=w2l(T,tip),g=L;
 if(aro){g=o.typ!=1?L:Math.min(Math.max(8,o.depth),L);if(L-g>.5){const nt=add(tipL,mul(uT,L-g));ops.push({o:T,op:{k:'cut',o:nt,n:mul(uT,-1),lab:'Bout raccourci pour la queue d’aronde'}});tipL=nt}L=g;if(o.typ==1&&L>wR*.45)warn.push('Rainure profonde ('+Math.round(L)+' mm) : elle affaiblit la pièce, visez environ un tiers de son diamètre ('+Math.round(wR/3)+' mm).')}
 const rmax=bigR(T,{o:tipL,u:uT}),sg=o.flip?-1:1,top={k:'tenon',style:st,o:tipL,u:uT,L,d:aro&&o.typ==1?2*dT+6:o.d,w:wL,W:o.W,Lc:(st=='hache'||st=='plat')?(o.Lc||0):0,theta:o.theta,taper:o.taper,rmax,rT:dT/2,off:aro&&o.typ==2?sg*o.d/2:0,typ:o.typ,fl:o.flip?1:0};
 const s0=-wR,s1=thru?L+h+6:L+o.jeu;let mop;
 if(st=='plat')mop={k:'prism',c:add(SR,mul(aR,(s0+s1)/2)),e1:wRl,e2:cr(aR,wRl),pts:stad(o.W+o.jeu,o.d+o.jeu),H:s1-s0};
 else if(aro&&o.typ==3){const tn=Math.tan(o.theta*D),W=o.W+o.jeu,t=o.d+o.jeu,s1b=L+h+6,f=o.flip?-1:1;mop={k:'prism',c:add(SR,mul(aR,(s0+s1b)/2)),e1:wRl,e2:cr(wRl,aR),pts:(p_=>f<0?p_.reverse():p_)([[-W/2,-t/2*f],[W/2,-t/2*f],[W/2+t*tn,t/2*f],[-W/2-t*tn,t/2*f]]),H:s1b-s0}}
 else if(aro){const e3=o.typ==3?w:cr(w,a),wd=o.typ==3?cr(w,a):w,[lo,hi]=ext(R,e3),s3=dot(S,e3),tn=Math.tan(o.theta*D),hw=t=>o.W/2+o.jeu/2+t*tn,t0=-10,t1=o.typ==2?L+Math.max(h,0)+8:L+o.jeu;let n0,n1;
  if(o.typ==3){const hwT=dT/2+3+o.jeu/2;if(s3-lo<=hi-s3){n0=lo-5;n1=s3+hwT}else{n0=s3-hwT;n1=hi+5}}else if(o.typ!=2){n0=lo-5;n1=hi+5}else if(sg>0){n0=s3-o.jeu/2;n1=hi+5}else{n0=lo-5;n1=s3+o.jeu/2}
  const sc=(n0+n1)/2-s3;mop={k:'prism',c:add(SR,mul(dw2l(R,e3),sc)),e1:dw2l(R,wd),e2:aR,pts:[[-hw(t0),t0],[hw(t0),t0],[hw(t1),t1],[-hw(t1),t1]],H:n1-n0}}
 else mop={k:'hole',o:SR,u:aR,s0,s1,r:o.d/2+o.jeu/2};
 const nm=st=='aronde'?`Queue d’aronde ${ARO[o.typ]}`:st=='plat'?(o.Lc>0?'Tenon plat (hachette, embase conique)':'Tenon plat scié'):TEN_NAMES[st][0].toUpperCase()+TEN_NAMES[st].slice(1);
 top.lab=`${nm} ${aro&&o.typ!=2?'l. '+o.W:st=='plat'||aro?o.W+'×'+o.d:'Ø'+o.d} → ${R.name}`;mop.lab=`Mortaise ${aro?'(rainure)':thru?'débouchante':'borgne'} ← ${T.name}`;
 ops.push({o:T,op:top},{o:R,op:mop});
 if(o.d>wR/3+1&&!aro)warn.push('Mortaise plus grosse que le tiers de la pièce ('+Math.round(wR/3)+' mm) : risque d’affaiblir.');if(h>8&&thru)warn.push('Le tenon est '+Math.round(h)+' mm avant l’autre face : trou visible.');
 return{ops,warn,L,thru,center:S,axis:a,dof:aro?DOF.aronde:st=='plat'?DOF.plat:DOF.tenon,rec:{k:'tenon',ids:[T.id,R.id],opt:{...o}},title:nm}}
/* ----- mi-bois ----- */
function planMibois(A,B,opt){const pc=(opt&&opt.pc!=null?opt.pc:50)/100;if(A===B||!isWood(A)||!isWood(B))throw new Error('Choisissez deux pièces de bois droites différentes.');
 const a=axisOf(A),b=axisOf(B);let k=cr(a.u,b.u);if(len(k)<.25)throw new Error('Les deux pièces sont presque parallèles : le mi-bois demande qu’elles se croisent en angle.');k=nrm(k);
 const cA=mul(add(a.p0,a.p1),.5),cB=mul(add(b.p0,b.p1),.5);if(dot(sub(cB,cA),k)<0)k=mul(k,-1);
 const[aLo,aHi]=ext(A,k),[bLo,bHi]=ext(B,k);if(aHi-bLo<1)throw new Error('Les deux pièces doivent se chevaucher : posez l’une sur l’autre (elles se recouvrent de la profondeur de l’entaille).');
 const m=aHi-pc*(aHi-bLo),notch=(P,Q,v,lo,hi)=>{const c1=nrm(cr(k,v)),[wl,wh]=ext(Q,c1),[ll,lh]=ext(P,v),C=add(add(mul(v,(ll+lh)/2),mul(c1,(wl+wh)/2)),mul(k,(lo+hi)/2));
  return{k:'obox',c:w2l(P,C),e1:dw2l(P,v),e2:dw2l(P,c1),h:[(lh-ll)/2+4,(wh-wl)/2,(hi-lo)/2]}};
 const nA=notch(A,B,b.u,m,aHi+3),nB=notch(B,A,a.u,bLo-3,m);nA.lab=`Mi-bois ${Math.round(pc*100)} % avec ${B.name}`;nB.lab=`Mi-bois ${Math.round((1-pc)*100)} % avec ${A.name}`;
 const[pa,pb]=segClose(a.p0,a.p1,b.p0,b.p1);
 return{ops:[{o:A,op:nA},{o:B,op:nB}],warn:[],dof:DOF.mibois,rec:{k:'mibois',ids:[A.id,B.id],opt:{pc:pc*100}},title:'Mi-bois',axis:k,center:mul(add(pa,pb),.5)}}
/* ----- cheville (trou chevillé traversant une ou plusieurs pièces) ----- */
function planCheville(P,opt){const o=Object.assign({mode:'new',d:20,over:2,axis:'auto',jeu:.5,peg:null,pos:null},opt),L=P.filter(isWood);
 if(L.length<(o.mode=='new'?2:1))throw new Error(o.mode=='new'?'Choisissez au moins deux pièces à cheviller.':'Choisissez la pièce à percer.');
 let dir,C;
 if(o.mode=='existing'){const peg=o.peg;if(!isWood(peg))throw new Error('Choisissez la pièce qui sert de cheville.');const A=axisOf(peg);dir=A.u;const cs=L.filter(x=>x!==peg).map(x=>{const b=axisOf(x);return segClose(A.p0,A.p1,b.p0,b.p1)[0]});if(!cs.length)throw new Error('Choisissez au moins une autre pièce à percer.');C=mul(cs.reduce(add),1/cs.length)}
 else{if(['X','Y','Z'].includes(o.axis))dir=[+(o.axis=='X'),+(o.axis=='Y'),+(o.axis=='Z')];
  else{const a=axisOf(L[0]),b=axisOf(L[1]);let k=cr(a.u,b.u);if(len(k)<.25){k=cr(a.u,sub(mul(add(b.p0,b.p1),.5),mul(add(a.p0,a.p1),.5)));if(len(k)<1e-6)throw new Error('Choisissez l’axe de la cheville (X, Y ou Z).')}dir=nrm(k)}
  const a=axisOf(L[0]),b=axisOf(L[1]),[pa,pb]=segClose(a.p0,a.p1,b.p0,b.p1);C=mul(add(pa,pb),.5)}
 if(o.pos)C=o.pos;
 const ops=[],warn=[],pieced=[];const d=o.mode=='existing'?crossMin(o.peg):o.d;
 const tch=(p,q)=>{const a=axisOf(p),b=axisOf(q),[x,y]=segClose(a.p0,a.p1,b.p0,b.p1);return len(sub(x,y))<=rad(p)+rad(q)+3};
 const tgt=(p,q)=>{const a=axisOf(p),b=axisOf(q),[x,y]=segClose(a.p0,a.p1,b.p0,b.p1);return len(sub(x,y))-(rad(p)+rad(q))};
 for(const p of L){if(p===o.peg)continue;const A=axisOf(p);if(Math.abs(dot(A.u,dir))>.9){warn.push('« '+p.name+' » est parallèle à la cheville : non percée.');continue}
  if(lineHits(p,C,dir).length<2)throw new Error('La cheville ne traverse pas « '+p.name+' » : placez les pièces pour qu’elles se croisent à l’endroit de la cheville.');
  const big=2*(len(sub(A.p1,A.p0))+crossMin(p));ops.push({o:p,op:{k:'hole',o:w2l(p,C),u:dw2l(p,dir),s0:-big,s1:big,r:d/2+o.jeu,lab:`Trou de cheville Ø${d}`+(o.mode=='existing'?' ← '+o.peg.name:'')}});pieced.push(p)}
 if(!pieced.length)throw new Error('Aucune pièce n’est traversée par cette cheville : elle ne peut pas être dans le plan des pièces (elle doit les traverser).');
 if(o.mode=='new'&&!o.lap)for(let i=0;i<pieced.length;i++)for(let j=i+1;j<pieced.length;j++){const g=tgt(pieced[i],pieced[j]);if(g>2.5)throw new Error('« '+pieced[i].name+' » et « '+pieced[j].name+' » ne sont pas tangentes (écart '+Math.round(g)+' mm) : on ne cheville que des pièces qui se touchent. Utilisez le positionnement automatique.');if(g<-2.5)throw new Error('« '+pieced[i].name+' » et « '+pieced[j].name+' » sont insérées l’une dans l’autre ('+Math.round(-g)+' mm) : décalez-les (positionnement automatique, côté au choix).')}
 for(let i=0;i<pieced.length;i++)for(let j=i+1;j<pieced.length;j++)if(!tch(pieced[i],pieced[j]))throw new Error('« '+pieced[i].name+' » et « '+pieced[j].name+' » ne se touchent pas : une cheville ne se pose que sur des pièces en contact. Rapprochez-les.');
 const add_=[];if(o.mode=='new'){let lo=1e18,hi=-1e18;pieced.forEach(p=>{const[l,h]=ext(p,dir);lo=Math.min(lo,l);hi=Math.max(hi,h)});const s=add(C,mul(dir,lo-o.over-dot(C,dir)));
  add_.push({name:'Cheville Ø'+d,d,L:hi-lo+2*o.over,pos:s,rot:eul(dir),par:pieced[0].par,color:'#8a5a2b'});pieced.forEach(p=>{const w=crossMin(p);if(d>w/3+1)warn.push('Cheville Ø'+d+' > un tiers de « '+p.name+' » ('+Math.round(w/3)+' mm).')})}
 return{ops,add:add_,warn,dof:DOF.cheville,rec:{k:'cheville',ids:L.map(x=>x.id),opt:{...o,peg:o.peg?o.peg.id:null,pos:C}},title:'Cheville',axis:dir,center:C}}
/* ----- quart de bois, coupe, pointe ----- */
function localAxis(o){const ax=axisOf(o),b=lbb(o),k=ax.k,u=[0,0,0];u[k]=1;const c=[0,1,2].map(i=>(b.min[i]+b.max[i])/2),p0=[...c],p1=[...c];p0[k]=b.min[k];p1[k]=b.max[k];return{ax,u,p0,p1,c,L:ax.L}}
function planQuart(o,opt){if(!isWood(o))throw new Error('Pièce non adaptée.');const v=Object.assign({start:0,len:300,pos:0,mode:'quart'},opt),la=localAxis(o),ax=axisOf(o);
 if(!(v.len>5))throw new Error('Longueur invalide.');if(v.start<0||v.start+v.len>la.L+.01)throw new Error('Le quart de bois dépasse la pièce (longueur '+Math.round(la.L)+' mm).');
 let up=[0,0,1];if(Math.abs(dot(ax.u,up))>.95)up=[1,0,0];let b0=sub(up,mul(ax.u,dot(up,ax.u)));b0=nrm(b0);const b1=cr(ax.u,b0);
 const th=(v.pos||0)*D,e1w=add(mul(b0,Math.cos(th)),mul(b1,Math.sin(th))),e2w=cr(ax.u,e1w),e1=dw2l(o,e1w),e2=dw2l(o,e2w),Rb=2.5*crossMin(o)+20,span=(v.mode=='demi'?180:90)*D,pts=[[0,0]];
 for(let i=0;i<=6;i++){const t=span*i/6;pts.push([Rb*Math.cos(t),Rb*Math.sin(t)])}
 const u=la.u,c=add(add(la.c,mul(u,-la.L/2+0)),mul(u,0));const base=la.p0,mid=add(base,mul(u,v.start+v.len/2));
 const nm=v.mode=='demi'?'Demi-bois':'Quart de bois';
 return{ops:[{o,op:{k:'prism',c:mid,e1,e2,pts,H:v.len,lab:`${nm} sur ${v.len} mm à ${v.start} mm du bout A`}}],warn:[],dof:'',rec:{k:'quart',ids:[o.id],opt:{...v}},title:nm}}
function planCoupe(o,opt){const la=localAxis(o),[e1]=bas(la.u),ang=(opt.angle||0)*D,keep=opt.keep||'A',t=opt.dist;
 if(!(t>0)||t>=la.L)throw new Error('Le plan de coupe doit être entre les deux bouts de la pièce (0 à '+Math.round(la.L)+' mm).');
 const P=add(la.p0,mul(la.u,t)),nB=add(mul(la.u,Math.cos(ang)),mul(e1,Math.sin(ang))),nA=mul(nB,-1),lab=`Coupe à ${t} mm du bout A`+(ang?` (biais ${opt.angle}°)`:''),
  cutB={k:'cut',o:P,n:nB,lab:lab+' : on garde le côté A'},cutA={k:'cut',o:P,n:nA,lab:lab+' : on garde le côté B'},ops=[],add_=[];
 if(keep=='A')ops.push({o,op:cutB});else if(keep=='B')ops.push({o,op:cutA});
 else{ops.push({o,op:cutB});add_.push({d:o.p.d,L:o.p.L,name:o.name+' (coupe B)',color:o.color,pos:[...o.pos],rot:[...o.rot],par:o.par,ops:[cutA],cutPart:true})}
 return{ops,add:add_,warn:keep=='both'&&!['trav'].includes(o.type)?['Le second morceau est recréé comme une traverse droite.']:[],rec:{k:'coupe',ids:[o.id],opt:{...opt}},title:'Coupe',plane:{p:l2w(o,P),n:dl2w(o,nB)}}}
function planPointe(o,opt){const la=localAxis(o),end1=opt.end==1,o0=end1?la.p1:la.p0,u=end1?mul(la.u,-1):la.u,L=opt.len,rT=rad(o);if(!(L>5))throw new Error('Longueur de pointe invalide.');if(L>=la.L)throw new Error('Pointe plus longue que la pièce.');
 return{ops:[{o,op:{k:'point',o:o0,u,L,r0:opt.r0||3,rT,rmax:bigR(o,{o:o0,u}),lab:`Pointe de ${L} mm au bout ${end1?'B':'A'}`}}],warn:[],rec:{k:'pointe',ids:[o.id],opt:{...opt}},title:'Pointe'}}
/* ----- application d'un plan, suppression, modification ----- */
function applyPlan(pl,jid){jid=jid||++JID;const ch=new Set();pl.ops.forEach(({o,op,at})=>{op.jid=jid;op.rec=pl.rec;op.dof=pl.dof||'';if(at!=null&&at<=o.ops.length)o.ops.splice(at,0,op);else o.ops.push(op);ch.add(o)});
 (pl.add||[]).forEach(a=>{const p=mkObj('trav',{d:a.d,L:a.L},null,a.name,a.color,a.pos,a.rot,a.par);if(a.cutPart)p.lc=[jid];else{p.peg=true;p.lk=[jid]}if(a.ops)a.ops.forEach(op=>{op.jid=jid;op.rec=pl.rec;p.ops.push(op)});ch.add(p)});refresh(...ch);return jid}
function delOp(o,i){const op=o.ops[i];if(!op)return;const ch=new Set([o]);
 if(op.jid){objs.forEach(x=>{for(let j=x.ops.length-1;j>=0;j--)if(x.ops[j].jid==op.jid&&!(x===o&&j==i)){x.ops.splice(j,1);ch.add(x)}});const pg=objs.filter(x=>(x.peg&&x.lk&&x.lk.includes(op.jid))||(x.lc&&x.lc.includes(op.jid)));pg.forEach(x=>{ch.delete(x)});if(pg.length)rmObjs(pg)}
 o.ops.splice(o.ops.indexOf(op),1);refresh(...[...ch].filter(x=>objs.includes(x)))}
function replaceJid(jid,planFn){const saved=[];objs.forEach(x=>x.ops.forEach((p,idx)=>{if(p.jid==jid)saved.push({o:x,op:p,idx})}));const pegs=objs.filter(x=>(x.peg&&x.lk&&x.lk.includes(jid))||(x.lc&&x.lc.includes(jid)));
 saved.slice().reverse().forEach(s=>s.o.ops.splice(s.idx,1));let removedPegs=false;
 try{const pl=planFn();pl.ops.forEach(e=>{const s=saved.find(q=>q.o===e.o);if(s)e.at=s.idx});if(pegs.length){rmObjs(pegs);removedPegs=true}applyPlan(pl,jid)}
 catch(err){saved.forEach(s=>s.o.ops.splice(s.idx,0,s.op));throw err}}
/* ----- liaisons : un assemblage bloque des degrés de liberté, les pièces liées se déplacent ensemble ----- */
const jidsOf=o=>[...(o.ops||[]).filter(p=>p.jid&&!p.free).map(p=>p.jid),...(o.lk||[])];
function linkedOf(o){const J=new Set(jidsOf(o));if(!J.size)return[];return objs.filter(x=>x!==o&&jidsOf(x).some(j=>J.has(j)))}
const supAsm=o=>Object.values(asms).filter(a=>a.src&&a.src.ids&&a.src.ids.includes(o.id));
const moveTargets=()=>{const T=targets();if(!PREF.rigid)return T;const S=new Set(T),Q=[...T];while(Q.length){const o=Q.pop();for(const x of linkedOf(o))if(!S.has(x)){S.add(x);Q.push(x)}for(const a of supAsm(o))for(const x of piecesOf(a.id))if(!S.has(x)){S.add(x);Q.push(x)}}return[...S]};
function freeLinks(list,free){list.forEach(o=>{(o.ops||[]).forEach(p=>{if(p.jid)p.free=free||undefined});if(!free)return});touch();msg(free?'Pièces désolidarisées : elles se déplacent séparément.':'Pièces re-solidarisées.')}
/* ----- fendre : en planches d'épaisseur choisie, en demi-rondins ou en quartiers ----- */
function planFendre(o,v){if(!isWood(o))throw new Error('Impossible de fendre cette pièce.');v=Object.assign({mode:'planches',t:30,n:2,angle:0,gap:15,start:0},v);const la=localAxis(o),b=lbb(o),u=la.u,[e1,e2]=bas(u),g0=geo(o),out=[],cL=la.c,Rb=Math.hypot(...[0,1,2].map(i=>b.max[i]-b.min[i]));
 if(v.mode=='planches'){if(!(v.t>=5))throw new Error('Épaisseur minimale : 5 mm.');const a=v.angle*D,tB=add(mul(e1,Math.cos(a)),mul(e2,Math.sin(a))),nB=cr(tB,u),pts=[...Array(8)].map((_,i)=>i);void pts;
  let lo=1e18,hi=-1e18;const P=bpts(o);for(let i=0;i<P.length;i+=3){const t=P[i]*nB[0]+P[i+1]*nB[1]+P[i+2]*nB[2];lo=Math.min(lo,t);hi=Math.max(hi,t)}
  const n=Math.ceil((hi-lo)/v.t-1e-6);if(n>40)throw new Error('Trop de planches ('+n+') : augmentez l’épaisseur.');if(n<2)throw new Error('L’épaisseur est supérieure au diamètre : une seule planche.');
  const c0=dot(cL,nB);for(let j=0;j<n;j++){const s0=lo+j*v.t,s1=Math.min(hi,s0+v.t),mid=(s0+s1)/2;const g=intersect(g0,boxF(add(cL,mul(nB,mid-c0)),tB,u,[Rb,la.L/2+10,(s1-s0)/2]));if(!G.toPolygons(g).length)continue;const full=s1-s0>v.t*.97;
   out.push({g,dirL:nB,off:mid-(lo+hi)/2,name:`${o.name} – ${full?'planche':'dosse'} ${j+1}/${n}`})}}
 else{const N=v.mode=='demi'?2:v.n;for(let j=0;j<N;j++){const a0=v.start*D+j*2*Math.PI/N,a1=a0+2*Math.PI/N,n=Math.max(2,Math.ceil((a1-a0)/(30*D))),pts=[[0,0]];for(let s=0;s<=n;s++){const t=a0+(a1-a0)*s/n;pts.push([Rb*Math.cos(t),Rb*Math.sin(t)])}
  const g=intersect(g0,prismF(cL,e1,e2,pts,la.L+20));if(!G.toPolygons(g).length)continue;const mid=(a0+a1)/2;out.push({g,dirL:add(mul(e1,Math.cos(mid)),mul(e2,Math.sin(mid))),off:1,name:`${o.name} – ${N==2?'demi '+(j+1):'quartier '+(j+1)+'/'+N}`})}}
 const kept=v.waste?out.filter(p=>!/dosse/.test(p.name)):out;if(out.length<2)throw new Error('Le fendage n’a rien donné.');return{parts:kept.length?kept:out,gap:v.gap,wasted:out.length-kept.length}}
function fendre(o,v){const pl=planFendre(o,v),ob=bounds([o]),uw=dl2w(o,localAxis(o).u),nbs=pl.parts.map(p=>dl2w(o,p.dirL)),res=pl.parts.map(p=>{const q=mkObj('mesh',{},p.g,p.name,o.color,add(o.pos,mul(dl2w(o,p.dirL),pl.gap*(p.off<0?-1:p.off>0?1:0)||0)),[...o.rot],o.par);q.mat=o.mat;return q});rmObjs([o]);
 if(v.layout=='plateau'&&(v.mode||'planches')=='planches'){let cur=ob[0][1];res.forEach((q,i)=>{const n=nrm(nbs[i]),w=nrm(cr(n,uw)),M=new THREE.Matrix4().makeBasis(new THREE.Vector3(...uw),new THREE.Vector3(...w),new THREE.Vector3(...n)).transpose(),Q=new THREE.Quaternion().setFromRotationMatrix(M).multiply(qOf(q)),E=new THREE.Euler().setFromQuaternion(Q,'ZYX');q.rot=[E.x/D,E.y/D,E.z/D];mk(q);const[mn,mx]=bounds([q]);q.pos=[q.pos[0]+ob[0][0]-mn[0],q.pos[1]+cur-mn[1],q.pos[2]+ob[0][2]-mn[2]];mk(q);cur+=mx[1]-mn[1]+(v.gap2||0)})}
 select(res);return res}

/* =====================  Fenêtre d'opération : paramètres, aperçu 3D en direct, schéma  ===================== */
let MV=null;
function mvOpen(){const host=$('#ov');if(!host)return;const r=new THREE.WebGLRenderer({antialias:true});r.setPixelRatio(Math.min(devicePixelRatio||1,2));host.appendChild(r.domElement);
 const sc2=new THREE.Scene();sc2.background=new THREE.Color(0xf4f5f7);const cam2=new THREE.PerspectiveCamera(40,1,1,400000);cam2.up.set(0,0,1);sc2.add(new THREE.AmbientLight(0xffffff,.7));const dl2=new THREE.DirectionalLight(0xffffff,.8);dl2.position.set(500,-800,1000);sc2.add(dl2);
 const ctl=new THREE.OrbitControls(cam2,r.domElement);MV={r,sc:sc2,cam:cam2,ctl,grp:new THREE.Group(),host,labels:[],lastView:null};sc2.add(MV.grp);
 MV.size=()=>{const w=host.clientWidth||400,h=host.clientHeight||300;r.setSize(w,h);cam2.aspect=w/h;cam2.updateProjectionMatrix()};MV.size();
 (function loop(){if(!MV)return;MV.raf=requestAnimationFrame(loop);ctl.update();r.render(sc2,cam2);const w=host.clientWidth,h_=host.clientHeight,h=h_,L=$('#ovl');const H_=$('#ovh');if(H_&&MV.hs)MV.hs.forEach((h,i)=>{const e=H_.children[i];if(!e)return;const p=[h.p0[0]+h.dir[0]*h.t(),h.p0[1]+h.dir[1]*h.t(),h.p0[2]+h.dir[2]*h.t()],v=new THREE.Vector3(...p).project(cam2);e.style.left=(v.x+1)/2*w+'px';e.style.top=(1-v.y)/2*h_+'px';e.style.display=v.z<1?'':'none';try{e.dataset.v=h.label?h.label():sm(h.toVal(h.t()))}catch(_){}});if(L)MV.labels.forEach((l,i)=>{const e=L.children[i];if(!e)return;const v=new THREE.Vector3(...l.p).project(cam2);e.style.left=(v.x+1)/2*w+'px';e.style.top=(1-v.y)/2*h+'px';e.style.display=v.z<1?'':'none'})})()}
function mvDispose(){if(!MV)return;cancelAnimationFrame(MV.raf);MV.grp.children.forEach(c=>{c.geometry&&c.geometry.dispose();c.children.forEach(k=>k.geometry&&k.geometry.dispose())});MV.ctl.dispose();MV.r.dispose();try{MV.r.forceContextLoss()}catch(e){}MV.r.domElement.remove();MV=null}
function mvSet(items,extra){if(!MV)return;const g=MV.grp;g.children.slice().forEach(c=>{g.remove(c);c.geometry&&c.geometry.dispose();c.children.forEach(k=>k.geometry&&k.geometry.dispose())});
 const box=new THREE.Box3();
 for(const it of items){const bg=it.tg||toGeo(it.g),m=new THREE.Mesh(bg,new THREE.MeshStandardMaterial({color:it.color||'#c8a06a',roughness:.75,metalness:.05,side:THREE.DoubleSide,transparent:!!it.ghost,opacity:it.ghost?.3:1,depthWrite:!it.ghost}));
  if(it.eg){m.add(new THREE.LineSegments(it.eg,edgeMat()))}
  if(it.g&&!it.ghost&&!it.noedge){const ed=sharpEdges(polysOf(it.g)),pa=new Float32Array(ed.length*6);ed.forEach((e,i)=>pa.set([...e.p,...e.q],i*6));const lg=new THREE.BufferGeometry();lg.setAttribute('position',new THREE.BufferAttribute(pa,3));m.add(new THREE.LineSegments(lg,edgeMat()))}
  m.position.set(...it.pos);m.rotation.order='ZYX';m.rotation.set(...it.rot.map(d=>d*D));g.add(m);box.expandByObject(m)}
 for(const l of extra&&extra.lines||[]){const lg=new THREE.BufferGeometry();lg.setAttribute('position',new THREE.BufferAttribute(new Float32Array([...l[0],...l[1]]),3));g.add(new THREE.Line(lg,new THREE.LineBasicMaterial({color:l[2]||0xe08a00,depthTest:false})))}
 MV.labels=extra&&extra.labels||[];const L=$('#ovl');if(L)L.innerHTML=MV.labels.map(l=>`<span>${esc(l.t)}</span>`).join('');MV.box=box}
function bestView(P,center,radius){const A=P.filter(Boolean).map(axisOf);let n=[0,0,1];
 if(A.length>=2&&len(cr(A[0].u,A[1].u))>.2)n=nrm(cr(A[0].u,A[1].u));else if(A.length){const t=cr(A[0].u,[0,0,1]);n=len(t)>.2?nrm(cr(t,A[0].u)):[0,-1,0]}
 if(dot(n,[0,-.3,.8])<0)n=mul(n,-1);const side=len(cr(n,[0,0,1]))>.3?nrm(cr(n,[0,0,1])):[1,0,0],dir=nrm(add(n,mul(side,.55)));return{dir,center,radius}}
function mvView(v){if(!MV||!v)return;MV.lastView=v;const c=v.center||(MV.box&&!MV.box.isEmpty()?MV.box.getCenter(new THREE.Vector3()).toArray():[0,0,0]);let r=v.radius;if(!r){const s=MV.box&&!MV.box.isEmpty()?MV.box.getSize(new THREE.Vector3()):new THREE.Vector3(500,500,500);r=Math.max(s.x,s.y,s.z)*.6+50}
 const d=nrm(v.dir||[.6,-.85,.6]),dist=r/Math.tan(MV.cam.fov*Math.PI/360)*1.05;MV.ctl.target.set(...c);MV.cam.position.set(c[0]+d[0]*dist,c[1]+d[1]*dist,c[2]+d[2]*dist);MV.cam.up.set(0,0,Math.abs(d[2])>.97?0:1);if(Math.abs(d[2])>.97)MV.cam.up.set(0,1,0);MV.ctl.update()}
/* ----- schémas explicatifs ----- */
const SV=b=>U(`<svg viewBox="0 0 320 150" xmlns="http://www.w3.org/2000/svg" style="width:100%;height:auto;max-height:230px;font:13px system-ui,sans-serif" fill="none" stroke="currentColor" stroke-width="1.6">${b}</svg>`);
const TXT=(x,y,t,a='middle')=>`<text class="sx" x="${x}" y="${y}" text-anchor="${a}">${esc(t)}</text>`;
const WD='fill="#c8a06a" fill-opacity=".55"',OR='stroke="#e08a00" stroke-width="1.6"';
const RB=(x,y,r)=>r?`<g class="rb" data-r="${r}"><circle cx="${x}" cy="${y}" r="8.5"/><text x="${x}" y="${y+4.2}" font-size="12" text-anchor="middle">${r}</text></g>`:'';
const DIMH=(x1,x2,y,t,r)=>`<g data-r="${r||''}" ${OR}><line x1="${x1}" y1="${y}" x2="${x2}" y2="${y}"/><line x1="${x1}" y1="${y-4}" x2="${x1}" y2="${y+4}"/><line x1="${x2}" y1="${y-4}" x2="${x2}" y2="${y+4}"/></g>`+TXT((x1+x2)/2+(r?9:0),y-5,t)+RB((x1+x2)/2-t.length*3.2-2,y-9,r);
const DIMV=(x,y1,y2,t,r)=>`<g data-r="${r||''}" ${OR}><line x1="${x}" y1="${y1}" x2="${x}" y2="${y2}"/><line x1="${x-4}" y1="${y1}" x2="${x+4}" y2="${y1}"/><line x1="${x-4}" y1="${y2}" x2="${x+4}" y2="${y2}"/></g>`+RB(x+13,(y1+y2)/2,r)+TXT(x+(r?24:6),(y1+y2)/2+4,t,'start');
function schema(k,v){const n=x=>fr(Math.round((+x||0)*10)/10);
 if(k=='tenon'){const hache=v.style=='hache',plat=v.style=='plat',d=Math.max(14,Math.min(46,(+v.d||20)/(+v.dT||60)*50)),y0=75-d/2,thru=v.mort!='blind';
  return SV(`<rect x="170" y="14" width="64" height="122" ${WD}/>${TXT(202,10,'pièce mortaisée')}<rect x="20" y="50" width="${hache?100:150}" height="50" ${WD}/>${hache?`<path d="M120 50L150 ${y0}H${thru?240:222}V${y0+d}H150L120 100" ${WD}/>`:`<path d="M170 ${y0}H${thru?240:222}V${y0+d}H170" ${WD}/>`}`+
   `${TXT(70,43,'pièce à tenon')}${DIMV(246,y0,y0+d,plat?'ép. '+n(v.d)+' mm':'Ø '+n(v.d)+' mm','A')}${DIMH(170,thru?240:222,128,'tenon')}${hache?DIMH(120,150,32,'cône','B'):''}${TXT(160,147,thru?'mortaise débouchante':'mortaise borgne')}`)}
 if(k=='aronde'){const typ=+v.typ||1,th=Math.tan((+v.theta||10)*D)*40,W=Math.max(24,Math.min(70,+v.W||40)/1.2);
  const front=`<rect x="20" y="95" width="170" height="45" ${WD}/><path d="M${105-W/2} 95L${105-W/2-th} 135H${105+W/2+th}L${105+W/2} 95Z" fill="var(--bg)"/><rect x="${105-W/2-th-22}" y="24" width="${W+2*th+44}" height="71" ${WD}/><path d="M${105-W/2} 95L${105-W/2-th} 135H${105+W/2+th}L${105+W/2} 95Z" ${WD}/>`;
  if(typ==3){const fl=!!v.flip,t=Math.max(16,Math.min(30,(+v.d||30)*.6)),Wn=Math.max(20,Math.min(60,(+v.W||40)*.8)),Ww=Wn+2*t*Math.tan((+v.theta||20)*D),y0=28,y1=96,yN=fl?y0:y1,yW=fl?y0+t:y1-t,cx=130;
   return SV(`<rect x="30" y="${y0}" width="200" height="${y1-y0}" ${WD}/><line x1="30" y1="${(y0+y1)/2}" x2="230" y2="${(y0+y1)/2}" stroke="currentColor" stroke-dasharray="6 4" stroke-width=".8"/><path d="M${cx-Wn/2} ${yN}L${cx+Wn/2} ${yN}L${cx+Ww/2} ${yW}L${cx-Ww/2} ${yW}Z" fill="#c8a06a" stroke="currentColor"/>${TXT(160,14,'coupe : le bout du rondin devient un trapèze qui traverse')}${DIMH(cx-Wn/2,cx+Wn/2,fl?y0-6:y1+8,'','A')}${DIMV(244,Math.min(yN,yW),Math.max(yN,yW),'','D')}${TXT(160,124,'petit côté (A = '+n(v.W)+' mm) au ras du bois, '+(fl?'en haut':'en bas'))}${TXT(160,142,'épaisseur D = '+n(v.d)+' mm · angle '+n(v.theta)+'° de chaque côté')}`)}
  if(typ==1)return SV(front+`${TXT(105,18,'vue de face : la queue s’élargit vers le bout')}${DIMH(105-W/2,105+W/2,88,'largeur '+n(v.W)+' mm','A')}${DIMV(200,95,135,'prof. '+n(v.depth)+' mm','B')}${TXT(105,112,'angle '+n(v.theta)+'°')}<g data-r="C"><path d="M${105-W/2-th} 135L${105-W/2} 95" ${OR}/></g>${TXT(230,70,'l’épaisseur du tenon')}${TXT(230,86,'n’est pas réduite','middle')}`)
  return SV(front+`<rect x="20" y="95" width="170" height="${45}" fill="none"/><rect x="${105-W/2-th-22}" y="24" width="${W+2*th+44}" height="36" fill="var(--bg)" fill-opacity=".7" stroke="none"/><g transform="translate(222 0)"><rect x="0" y="95" width="84" height="45" ${WD}/><path d="M18 95V80H66V95" fill="var(--bg)"/><rect x="18" y="62" width="48" height="33" ${WD}/><rect x="10" y="26" width="64" height="36" ${WD}/>${TXT(42,18,'profil')}${DIMV(80,62,95,n(v.d)+' mm','D')}</g>${DIMH(105-W/2,105+W/2,88,'largeur '+n(v.W)+' mm','A')}${TXT(105,115,'angle '+n(v.theta)+'°')}${TXT(105,18,'languette de demi-épaisseur ; l’extérieur reste rond')}${RB(58,127,'B')}${TXT(108,131,'prof. '+n(v.depth)+' mm')}`)}
 if(k=='mibois'){const p=Math.max(10,Math.min(90,+v.pc||50));return SV(`<rect x="30" y="${75-p*.3}" width="150" height="40" ${WD}/><rect x="140" y="${35}" width="150" height="40" ${WD} transform="translate(0 ${p*.0})"/><rect x="140" y="${75-p*.3}" width="40" height="${p*.3+0}" fill="var(--bg)" fill-opacity=".8" stroke="none"/>${TXT(85,28,'pièce du dessous')}${TXT(235,28,'pièce du dessus')}${DIMV(298,75-p*.3,75,n(p)+' %','A')}${TXT(160,146,'les deux pièces affleurent après l’entaille')}`)}
 if(k=='cheville'){const d=Math.max(8,Math.min(30,(+v.d||20)/2));return SV(`<rect x="60" y="45" width="200" height="30" ${WD}/><rect x="110" y="75" width="150" height="30" ${WD}/><rect x="${160-d/2}" y="25" width="${d}" height="100" fill="#8a5a2b" fill-opacity=".8"/>${TXT(160,142,'cheville Ø '+n(v.d)+' traversant les pièces')}`)}
 if(k=='quart'){const c='cx="100" cy="75" r="46"';return SV(`<circle ${c} ${WD}/><path d="M100 75L146 75A46 46 0 0 0 100 29Z" fill="var(--bg)"/><path d="M100 29V75H146" ${OR}/>${TXT(100,142,'section : un quartier retiré')}<rect x="190" y="50" width="110" height="46" ${WD}/><rect x="235" y="50" width="45" height="23" fill="var(--bg)"/>${DIMH(235,280,44,n(v.len)+' mm')}${TXT(245,112,'plateau posé dans le quart de bois')}`)}
 if(k=='fendre'){const t=+v.t||30,s=Math.max(5,Math.min(40,t/ (+v.D||200)*92)),ls=[];for(let y=29+s;y<121;y+=s)ls.push(`<line x1="${100-Math.sqrt(Math.max(0,46*46-(y-75)*(y-75)))}" y1="${y}" x2="${100+Math.sqrt(Math.max(0,46*46-(y-75)*(y-75)))}" y2="${y}" ${OR}/>`);return SV(`<circle cx="100" cy="75" r="46" ${WD}/>${ls.join('')}${TXT(210,70,'planches de')}${TXT(210,86,n(t)+' mm','middle')}`)}
 if(k=='rep'){return v.type=='circ'?SV(`<circle cx="160" cy="75" r="50" ${OR}/>${[0,1,2,3,4,5].map(i=>`<circle cx="${160+50*Math.cos(i*1.0472)}" cy="${75+50*Math.sin(i*1.0472)}" r="7" ${WD}/>`).join('')}${TXT(160,78,n(v.ang)+'°')}`):SV(`${[0,1,2,3].map(i=>`<rect x="${30+i*65}" y="50" width="30" height="50" ${WD}/>`).join('')}${DIMH(45,110,40,n(v.step||v.total)+' mm')}${TXT(160,130,'répétition linéaire')}`)}
 if(k=='clay'){return SV(`<circle cx="90" cy="75" r="14" ${WD}/><circle cx="230" cy="75" r="14" ${WD}/><path d="M20 70C50 70 60 56 90 56S130 94 160 94 200 56 230 56 280 80 300 80" ${OR}/>${TXT(90,110,'support')}${TXT(230,110,'support')}${TXT(160,134,'claie Ø '+n(v.d)+' : dessous, dessus, dessous…')}`)}
 return''}
/* ----- construction de la fenêtre ----- */
const isMm=f=>(!f.t||f.t=='num')&&/\(mm\)/.test(f.l||''),lbl=f=>{const b=f.r?`<b class="rf" data-r="${f.r}">${f.r}</b>`:'';return b+(isMm(f)?f.l.replace('(mm)','('+us()+')'):U(f.l||''))};
const fldHtml=(f,V)=>{let val=f.k!=null&&V[f.k]!==undefined?V[f.k]:f.v;if(isMm(f)&&typeof val=='number')val=Math.round(val*uk()*100)/100;const at=`id="f_${f.k}" data-k="${f.k}"${f.rb?' data-rb="1"':''}`;
 if(f.t=='info')return`<p class="mu" style="font-size:12px">${U(f.l)}</p>`;
 if(f.t=='sel'){const opt=o=>{const[a,b]=Array.isArray(o)?o:[o,o];return`<option value="${esc(a)}"${String(a)==String(val)?' selected':''}>${esc(b)}</option>`};return`<label>${lbl(f)}<select ${at}>${f.o.map(o=>o&&o.g?`<optgroup label="${esc(o.g)}">${o.o.map(opt).join('')}</optgroup>`:opt(o)).join('')}</select></label>`}
 if(f.t=='piece')return`<label>${lbl(f)}<select ${at}>${f.none?'<option value="">(aucune)</option>':''}${objs.filter(o=>f.any||isWood(o)).map(o=>`<option value="${o.id}"${o.id==val?' selected':''}>${esc(o.name)}</option>`).join('')}</select></label>`;
 if(f.t=='chk')return`<label class="ck"><input ${at} type="checkbox" ${val?'checked':''}> ${lbl(f)}</label>`;
 if(f.t=='txt')return`<label>${lbl(f)}<input ${at} type="text" value="${esc(val)}"></label>`;
 return`<label>${lbl(f)}<input ${at} type="number" step="any" value="${val}"></label>`+(f.h?`<div class="mu" style="margin:-4px 0 6px;font-size:11px">${U(f.h)}</div>`:'')};
function opWin(cfg){const mb=$('#mb'),md=$('#md');mvDispose();mb.classList.add('wide');let V={...(cfg.init||{})},tm=null,live=cfg.live!==false;
 const fl=()=>typeof cfg.fields=='function'?cfg.fields(V):cfg.fields;fl().forEach(f=>{if(f.k!=null&&V[f.k]===undefined)V[f.k]=f.v});
 mb.innerHTML=`<div class="ow"><div class="of"><div class="ofs"><h3>${cfg.title}</h3>${cfg.intro?`<p class="mu" style="font-size:12px">${cfg.intro}</p>`:''}<div id="ofl"></div><div id="wrn" style="font-size:12px"></div><p id="derr" style="color:var(--er);margin:6px 0 0;display:none"></p></div><div class="ofb"><button class="p" id="mok">${cfg.ok||'Appliquer'}</button><button id="mno">Annuler</button></div></div>
  <div class="ovw"><div id="ov"><div id="ovl"></div><div id="ovh" style="position:absolute;inset:0;pointer-events:none"></div><span id="ovb" class="mu" style="position:absolute;left:8px;top:6px;font-size:11px;pointer-events:none"></span></div><div class="r" style="margin:6px 0"><button id="vp">Plan optimal</button><button id="vi">Vue 3D</button><button id="vf" title="Affiche le reste du projet autour de l’élément, sans changer le cadrage">Voir tout le projet</button></div><label class="ck" style="margin:0 0 6px"><input type="checkbox" id="vsa"> Montrer aussi le reste du projet (transparent)</label><div id="osch"></div><div id="odof" class="mu" style="font-size:12px"></div></div></div>`;
 document.body.classList.add('act');placeAct();md.classList.add('on');mvOpen();MV.showAll=false;{const c=$('#vsa'),vf=$('#vf');if(c){c.checked=false;c.onchange=()=>{MV.showAll=c.checked;if(vf)vf.textContent=c.checked?'Voir seulement les éléments concernés':'Voir tout le projet';upd(false)}}}
const fld=k=>fl().find(f=>f.k==k),showVal=(k,v)=>{const e=$('#f_'+k),f=fld(k);if(e)e.value=f&&isMm(f)?Math.round(v*uk()*100)/100:Math.round(v*100)/100};
const gradLines=()=>{if(!MV||!MV.hs||!MV.grp)return;const P=[];MV.hs.forEach(h=>{if(h.quad||h.click||!h.dir||h.dir.every(v=>!v))return;const mn=h.min??0,mx=Math.min(h.max??mn+1000,mn+8000),span=mx-mn;if(!(span>0))return;const st=span>2500?500:span>800?100:span>250?50:10,[e1]=bas(h.dir),tk=Math.max(25,span*.03);if(MV.dragH)for(let t=Math.ceil(mn/st)*st;t<=mx+1e-6;t+=st){const big=Math.round(t/st)%5==0,q=add(h.p0,mul(h.dir,t)),w=tk*(big?1.8:1);P.push(...sub(q,mul(e1,w)),...add(q,mul(e1,w)))}P.push(...add(h.p0,mul(h.dir,mn)),...add(h.p0,mul(h.dir,mx)))});
 if(!P.length)return;const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.BufferAttribute(new Float32Array(P),3));MV.grp.add(new THREE.LineSegments(g,new THREE.LineBasicMaterial({color:0xe08a00,transparent:true,opacity:.7,depthTest:false})))};
 const setHandles=hs=>{if(!MV)return;const H=$('#ovh');if(!H)return;MV.hs=hs;while(H.children.length>hs.length)H.lastChild.remove();hs.forEach((h,i)=>{let e=H.children[i];if(!e){e=document.createElement('div');e.className='mvh';e.style.pointerEvents='auto';H.appendChild(e);
   e.onpointerdown=ev=>{ev.preventDefault();const hh=MV.hs[i];if(hh.click){hh.click();rf();rd();sched(20);return}e.setPointerCapture(ev.pointerId);const ctl=MV.ctl;ctl.enabled=false;MV.dragH=true;
    if(hh.quad){const rq=new THREE.Raycaster(),Rq=MV.host.getBoundingClientRect(),pl=new THREE.Plane().setFromNormalAndCoplanarPoint(new THREE.Vector3(...hh.nz),new THREE.Vector3(...hh.p0));e.onpointermove=m=>{rq.setFromCamera({x:(m.clientX-Rq.left)/Rq.width*2-1,y:-(m.clientY-Rq.top)/Rq.height*2+1},MV.cam);const X=new THREE.Vector3();if(!rq.ray.intersectPlane(pl,X))return;let bi=0,bd=1e18;hh.pts.forEach((q,j)=>{const d=X.distanceTo(new THREE.Vector3(...q));if(d<bd){bd=d;bi=j}});if(bi!==hh.cur){hh.cur=bi;hh.set(bi);rf();sched(20)}};e.onpointerup=()=>{e.onpointermove=null;e.onpointerup=null;ctl.enabled=true;MV.dragH=false;rf();sched(10)};return}
const rc=new THREE.Raycaster(),R_=MV.host.getBoundingClientRect(),par=(x,y)=>{rc.setFromCamera({x:(x-R_.left)/R_.width*2-1,y:-(y-R_.top)/R_.height*2+1},MV.cam);const o=rc.ray.origin,d=rc.ray.direction,P=new THREE.Vector3(...hh.p0),u=new THREE.Vector3(...hh.dir),w0=o.clone().sub(P),a=d.dot(d),b=d.dot(u),c=u.dot(u),dd=d.dot(w0),ee=u.dot(w0),den=a*c-b*b;return Math.abs(den)<1e-9?0:(a*ee-b*dd)/den};
    const t0=par(ev.clientX,ev.clientY),s0=hh.t();e.onpointermove=m=>{let t=s0+par(m.clientX,m.clientY)-t0;if(hh.snap)t=Math.round(t/hh.snap)*hh.snap;t=Math.max(hh.min??0,Math.min(hh.max??1e9,t));const v=hh.toVal(t);V[hh.k]=v;showVal(hh.k,v);sched(30)};
    e.onpointerup=()=>{e.onpointermove=null;e.onpointerup=null;ctl.enabled=true;MV.dragH=false;rf();sched(10)}}}});};
 const rf=()=>{$('#ofl').innerHTML=fl().map(f=>fldHtml(f,V)).join('')};rf();
 const rd=()=>{fl().forEach(f=>{if(f.k==null||f.t=='info')return;const e=$('#f_'+f.k);if(!e)return;V[f.k]=f.t=='chk'?e.checked:f.t=='txt'?e.value:(f.t=='sel'||f.t=='piece')?(e.value!==''&&!isNaN(+e.value)?+e.value:e.value):isMm(f)?+e.value/uk():+e.value})};
 const err=t=>{const e=$('#derr');if(e){e.textContent=U(t||'');e.style.display=t?'block':'none'}};
 let upd0;const upd=(fit)=>{if(!MV)return;try{const pv=cfg.preview(V);const its=pv.items||[],used=new Set(its.map(i=>i.pos)),ghosts=(MV&&MV.showAll)&&objs.length<=220?objs.filter(o=>!used.has(o.pos)&&o.m&&o.m.geometry).map(o=>({tg:o.m.geometry.clone(),pos:o.pos,rot:o.rot,color:o.color,ghost:true,noedge:true})):[];mvSet(its.concat(ghosts),pv.extra);setHandles(cfg.handles?cfg.handles(V):[]);gradLines();if(fit||!MV.lastView)mvView(pv.view||(MV.lastView));$('#osch').innerHTML=cfg.schema?cfg.schema(V,pv):'';$('#wrn').innerHTML=(pv.warn||[]).map(w=>`<div style="color:var(--wa)">⚠ ${esc(U(w))}</div>`).join('');$('#odof').textContent=U(pv.dof||'');err('');MV.pv=pv;$('#ovb').textContent=''}catch(e){err(e.message||String(e))}};
 const sched=(ms=120,fit)=>{clearTimeout(tm);$('#ovb')&&($('#ovb').textContent='Aperçu…');tm=setTimeout(()=>upd(fit),ms)};
 $('#osch').addEventListener('click',e=>{const g=e.target.closest('[data-r]');if(!g||!g.dataset.r)return;const f=fl().find(x=>x.r==g.dataset.r&&(!x.t||x.t=='num')&&x.k);if(!f)return;const cur=Math.round((V[f.k]||0)*(isMm(f)?uk():1)*100)/100;editAt(g,String(cur),v=>{const n=parseFloat(String(v).replace(',','.'));if(isNaN(n))return;V[f.k]=isMm(f)?n/uk():n;const inp=$('#f_'+f.k);if(inp)inp.value=n;sched(20)})});
 $('#ofl').addEventListener('input',e=>{rd();sched(cfg.delay||150)});
 $('#ofl').addEventListener('change',e=>{rd();if(e.target.dataset.rb){const sm_=$('#mb').scrollTop,so_=$('#ofl').scrollTop;rf();if(cfg.onRebuild)cfg.onRebuild(V);rd();$('#mb').scrollTop=sm_;$('#ofl').scrollTop=so_}sched(40,!!e.target.dataset.rb&&cfg.refit)});
 const hl=(r,on)=>{document.querySelectorAll('#osch [data-r]').forEach(e=>e.classList.toggle('hl',on&&e.dataset.r==r));document.querySelectorAll('#ofl .rf').forEach(e=>e.classList.toggle('hl',on&&e.dataset.r==r))};
 $('#ofl').addEventListener('focusin',e=>{const l=e.target.closest('label'),b=l&&l.querySelector('.rf');hl(b&&b.dataset.r,!!b)});$('#ofl').addEventListener('focusout',()=>hl(0,false));
 $('#vp').onclick=()=>{const pv=MV&&MV.pv;if(pv&&pv.view)mvView(pv.view)};$('#vi').onclick=()=>mvView({dir:[.6,-.85,.6],center:MV.pv&&MV.pv.view&&MV.pv.view.center,radius:MV.pv&&MV.pv.view&&MV.pv.view.radius});$('#vf').onclick=()=>{const c=$('#vsa');if(c){c.checked=!c.checked;c.onchange()}};
 $('#mno').onclick=closeMd;
 $('#mok').onclick=()=>{rd();try{const r=cfg.apply(V);if(r!==false)closeMd()}catch(e){err(e.message||String(e));msg('Impossible : '+U(e.message||String(e)),7000)}};
 $('#mb').onkeydown=e=>{if(e.key=='Enter'&&e.target.tagName=='INPUT'&&e.target.type!='checkbox'){e.preventDefault();$('#mok').click()}};
 setTimeout(()=>{if(MV){MV.size();upd(true)}},30);new ResizeObserver(()=>{if(MV)MV.size()}).observe($('#ov'));
 return{V,upd,rd}}

/* =====================  Fenêtres d'opérations : assemblages, fendre, quart de bois, coupe, pointe, répétition, clayonnage  ===================== */
const P_=id=>objs.find(o=>o.id==id);
const prevItems=(pl,pieces,rm)=>{const by=new Map();pl.ops.forEach(e=>{if(!by.has(e.o))by.set(e.o,[]);by.get(e.o).push(e.op)});
 const items=pieces.filter(Boolean).map(o=>({g:geo(tmpWith(o,by.get(o)||[],rm)),pos:o.pos,rot:o.rot,color:o.color}));
 (pl.add||[]).forEach(a=>{const t={type:'trav',p:{d:a.d,L:a.L},ops:[]};t.g=build(t);items.push({g:a.ops?geo(tmpWith(t,a.ops)):t.g,pos:a.pos,rot:a.rot,color:a.color})});return items};
const KINDS=[['mibois','Mi-bois'],['hache','Tenon classique (hachette)'],['scie','Tenon scié'],['plat','Tenon plat (hachette, embase conique)'],['platscie','Tenon plat scié'],['aronde1','Queue d’aronde classique (trapèze vu de face)'],['aronde2','Queue d’aronde à mi-bois (traversante, dépasse de l’autre côté)'],['aronde3','Queue d’aronde trapézoïdale dans l’axe du cylindre (petit côté au ras du bois)'],['cheville','Assemblage par chevilles'],['lash','Brêlage (dernier recours)']];
const KINDS_G=[{g:'Tenons et mortaises',o:KINDS.filter(x=>['hache','scie','plat','platscie'].includes(x[0]))},{g:'Mi-bois',o:KINDS.filter(x=>x[0]=='mibois')},{g:'Queues d’aronde',o:KINDS.filter(x=>x[0].startsWith('aronde'))},{g:'Chevilles et brêlage',o:KINDS.filter(x=>['cheville','lash'].includes(x[0]))}];
const kindOpt=k=>k.startsWith('aronde')?{style:'aronde',typ:+k.slice(6)}:k=='platscie'?{style:'plat',Lc:0}:{style:k};
function tang(A,B){const a=axisOf(A),b=axisOf(B),[pa,pb]=segClose(a.p0,a.p1,b.p0,b.p1),d=len(sub(pb,pa));return{a,b,pa,pb,d,gap:d-(rad(A)+rad(B))}}
const secEll=(ax,R,Q,m,N=20)=>{const dn=dot(ax.u,m);if(Math.abs(dn)<1e-3)return[];const t=dot(sub(Q,ax.p0),m)/dn,c=add(ax.p0,mul(ax.u,t)),[e1,e2]=bas(ax.u),P=[];for(let i=0;i<N;i++){const th=2*Math.PI*i/N,p=add(c,add(mul(e1,Math.cos(th)*R),mul(e2,Math.sin(th)*R))),s=dot(sub(Q,p),m)/dn;P.push(add(p,mul(ax.u,s)))}return P};
function hullLoop(pts,Q,m,off){const[f1,f2]=bas(m),P2=pts.map(p=>[dot(sub(p,Q),f1),dot(sub(p,Q),f2)]).map((q,i)=>({q,p:pts[i]})).sort((x,y)=>x.q[0]-y.q[0]||x.q[1]-y.q[1]),cr_=(o,a,b)=>(a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0]),lo=[],up=[];for(const e of P2){while(lo.length>1&&cr_(lo[lo.length-2].q,lo[lo.length-1].q,e.q)<=0)lo.pop();lo.push(e)}for(const e of P2.slice().reverse()){while(up.length>1&&cr_(up[up.length-2].q,up[up.length-1].q,e.q)<=0)up.pop();up.push(e)}
 const H=lo.slice(0,-1).concat(up.slice(0,-1)),c=H.reduce((a,e)=>[a[0]+e.q[0]/H.length,a[1]+e.q[1]/H.length],[0,0]);return H.map(e=>{const d=[e.q[0]-c[0],e.q[1]-c[1]],l=Math.hypot(...d)||1,q=[e.q[0]+d[0]/l*off,e.q[1]+d[1]/l*off];return add(Q,add(mul(f1,q[0]),mul(f2,q[1])))})}
function lashPlan(A,B,v){if(A===B)throw new Error('Choisissez deux pièces différentes.');const T=tang(A,B);
 if(T.gap>2.5)throw new Error('Le brêlage ne se fait que sur des pièces qui se touchent : « '+A.name+' » et « '+B.name+' » sont écartées de '+Math.round(T.gap)+' mm. Utilisez le positionnement automatique.');
 if(T.gap<-2.5)throw new Error('« '+A.name+' » et « '+B.name+' » sont insérées l’une dans l’autre ('+Math.round(-T.gap)+' mm) : le brêlage est impossible. Utilisez le positionnement automatique pour les décaler.');
 const a=T.a,b=T.b,rA=rad(A),rB=rad(B),dr=Math.max(v.rope,4),r=dr/2,n=Math.max(2,Math.round(v.turns)),paths=[],C=mul(add(T.pa,T.pb),.5);let ua=a.u,ub=b.u;if(dot(ua,ub)<0)ub=mul(ub,-1);
 let type=v.ltype=='droit'?'droit':'x',note='';if(type=='droit'&&Math.abs(dot(a.u,b.u))<.9){type='x';note='Pièces non parallèles : brêlage en X utilisé.'}if(type=='x'&&Math.abs(dot(a.u,b.u))>.97){type='droit';note='Pièces parallèles : brêlage droit utilisé.'}
 const ring=(c,u,R,rt,tilt)=>{const[e1,e2]=bas(u),pts=[];for(let i=0;i<16;i++){const th=2*Math.PI*i/16,x=Math.cos(th)*R,y=Math.sin(th)*R*Math.cos(tilt),z=Math.sin(th)*R*Math.sin(tilt);pts.push(add(c,add(add(mul(e1,x),mul(e2,y)),mul(u,z))))}paths.push({pts,closed:true,r:rt})};
 const helix=(c0,u,R,turns)=>{const[e1,e2]=bas(u),pts=[];for(let i=0;i<=turns*14;i++){const th=2*Math.PI*i/14;pts.push(add(add(c0,mul(u,dr*1.05*i/14)),add(mul(e1,Math.cos(th)*R),mul(e2,Math.sin(th)*R))))}return pts};
 if(type=='x'){const nz=nrm(cr(ua,ub)),bs=nrm(add(ua,ub)),bd=nrm(sub(ua,ub)),m1=len(cr(nz,bs))>.1?nrm(cr(nz,bs)):ua,m2=len(cr(nz,bd))>.1?nrm(cr(nz,bd)):ub,k=Math.max(1,Math.ceil(n/2));
  /* une diagonale, puis l'autre, en alternance ; chaque tour est décalé pour que les spires se juxtaposent */
  for(let i=0;i<2*k;i++){const m=i%2?m2:m1,sh=(Math.floor(i/2)-(k-1)/2)*dr*1.05,Q=add(C,mul(m,sh)),pts=[...secEll(a,rA,Q,m),...secEll(b,rB,Q,m)];if(pts.length>5)paths.push({pts:hullLoop(pts,Q,m,r+.3),closed:true,r})}
  ring(add(C,mul(m1,-(k/2+2)*dr)),m1,Math.max(rA,rB)*1.1,r*1.15,.45);ring(add(C,mul(m1,-(k/2+2)*dr)),m1,Math.max(rA,rB)*1.1,r*1.15,-.45);note=note||'Brêlage en X : une diagonale, puis l’autre en alternance, puis serrage.'}
 else if(type=='droit'){const m=ua,L0=Math.max(rA,rB)*0+dr*1.05;for(let i=0;i<n;i++){const Q=add(C,mul(m,(i-(n-1)/2)*dr*1.05)),pts=[...secEll(a,rA,Q,m),...secEll(b,rB,Q,m)];if(pts.length>5)paths.push({pts:hullLoop(pts,Q,m,r+.3),closed:true,r})}
  ring(add(C,mul(m,-(n/2+1.2)*dr)),m,Math.max(rA,rB)*1.1,r*1.15,.45);ring(add(C,mul(m,-(n/2+1.2)*dr)),m,Math.max(rA,rB)*1.1,r*1.15,-.45)}
 else{/* brêlage carré : cabestan sur A, tours autour des deux pièces (devant B, derrière A), serrage, cabestan final sur B */
  const k=Math.max(2,Math.ceil(n/2)),ey=ua,ez=len(sub(T.pb,T.pa))>1e-3?nrm(sub(T.pb,T.pa)):nrm(cr(ua,ub)),ex=nrm(cr(ey,ez)),O=T.pa,zB=len(sub(T.pb,T.pa)),P3=(x,y,z)=>add(O,add(add(mul(ex,x),mul(ey,y)),mul(ez,z))),pit=dr*1.02,
   coil=(c0,u,R,sg,e1,e2,tw)=>{const pts=[],N=k*18;for(let i=0;i<=N;i++){const th=2*Math.PI*i/18,h=sg*pit*i/18;pts.push(add(add(c0,mul(u,h)),add(mul(e1,Math.cos(th)*R),mul(e2,Math.sin(th)*R))))}return pts},
   RA=rA+r*.98,RB=rB+r*.98,yA=rB+r*.98,xB=rA+r*.98,[a1,a2]=bas(ey),[b1,b2]=bas(ex);
  /* spires rondes et serrées : au-dessus et au-dessous de B autour de A, de chaque côté de A autour de B */
  [1,-1].forEach(s=>{paths.push({pts:coil(P3(0,s*yA,0),ey,RA,s,a1,a2),closed:false,r});paths.push({pts:coil(P3(s*xB,0,zB),ex,RB,s,b1,b2),closed:false,r})});
  /* tours de serrage : spires superposées autour des deux pièces ensemble, au niveau de la jointure */
  const hm=(rA+rB+r*2)*.5,loop=(y)=>{const pts=[],M=48,ax=rA+r,bz=rB+r;for(let i=0;i<M;i++){const th=2*Math.PI*i/M;pts.push(P3(Math.cos(th)*(ax+r),y,zB/2+Math.sin(th)*(zB/2+Math.max(rA,rB)+r)))}return pts};
  const c0=P3(0,-(yA+k*pit+dr*2),0);ring(c0,ey,RA+r*.3,r*1.15,.45);ring(c0,ey,RA+r*.3,r*1.15,-.45);
  const c1=P3(xB+k*pit+dr*2,0,zB);ring(c1,ex,RB+r*.3,r*1.15,.45);ring(c1,ex,RB+r*.3,r*1.15,-.45);
  note=note||'Brêlage carré : spires rondes serrées autour de chaque pièce de part et d’autre de la jointure (plusieurs tours superposés), cabestans d’arrêt sur chaque pièce.'}
 return{turns:n,rope:dr,ltype:type,paths,center:C,note}}
/* qui porte le tenon ? la pièce dont un bout est près de la jonction (l'autre la traverse ou la dépasse largement) ; à égalité, la plus fine. > 0 : B doit porter le tenon */
function asmWin(kind,A,B,edit){
 const wood=objs.filter(isWood);if(wood.length<2)return msg('Il faut au moins deux pièces de bois.');
 if(!A)A=wood[0];if(!B||B===A)B=wood.find(o=>o!==A);
 const tenonKind=k=>!['mibois','cheville','lash'].includes(k);
 if(!edit&&tenonKind(kind)&&roleScore(A,B)>0)[A,B]=[B,A];
 const dfl=(k,T,R)=>{const df=tenonDefaults(T,R),pl=k=='plat'||k=='platscie'||k.startsWith('aronde');return{d:k=='aronde2'?Math.round(crossMin(T)/2):pl?df.thick:df.d,W:k.startsWith('aronde')?Math.round(Math.min(crossMin(T),crossMin(R))/2):Math.round(df.W),Lc:(k=='plat')?Math.round(Math.max(12,crossMin(T)*.25)):df.Lc,depth:df.depth,theta:k.startsWith('aronde')?20:PREF.theta}};
 const init={kind,a:A.id,b:B.id,c:'',mort:'thru',jeu:PREF.jeu,pos:edit?'manual':'auto',side:'haut',ltype:(()=>{const t=PRE_LT||'x';PRE_LT=null;return t})(),flip:false,pc:50,turns:6,rope:kind=='lash'?5:PREF.rope||2,rope_:6,expl:true,chev:'peg',peg:'',pd:20,mode:'new',over:2,axis:'auto',taper:false,...dfl(kind,A,B)};
 if(edit){const o=edit.rec.opt,id=edit.rec.ids;Object.assign(init,o);if(edit.rec.k=='tenon'){init.kind=o.style=='aronde'?'aronde'+o.typ:o.style=='plat'?(o.Lc>0?'plat':'platscie'):o.style;init.a=id[0];init.b=id[1];init.taper=!!o.taper}else if(edit.rec.k=='mibois'){init.kind='mibois';init.a=id[0];init.b=id[1];const pg=objs.find(x=>x.peg&&x.lk&&x.lk.includes(edit.jid));init.chev=pg?'peg':'none';if(pg)init.pd=pg.p.d}else if(edit.rec.k=='cheville'){init.kind='cheville';init.a=id[0];init.b=id[1];init.c=id[2]||'';init.pd=o.d;init.peg=o.peg||''}}
 const title=edit?'Modifier l’assemblage':'Assemblage';
 const fields=V=>{const k=V.kind,F=[{k:'kind',l:'Type d’assemblage',t:'sel',v:k,rb:1,o:KINDS_G}];
  if(tenonKind(k))F.push({k:'a',l:'Pièce portant le tenon',t:'piece'},{k:'b',l:'Pièce mortaisée',t:'piece'});
  else if(k=='cheville'){F.push({k:'mode',l:'Cheville',t:'sel',rb:1,o:[['new','Créer une cheville'],['existing','Utiliser une pièce existante (tenon passant)']]},{k:'a',l:'Pièce 1',t:'piece'},{k:'b',l:'Pièce 2',t:'piece'},{k:'c',l:'Pièce 3 (facultative)',t:'piece',none:1});
   if(V.mode=='existing')F.push({k:'peg',l:'Pièce qui sert de cheville',t:'piece'});}
  else F.push({k:'a',l:'Pièce 1',t:'piece'},{k:'b',l:'Pièce 2',t:'piece'});
  if(tenonKind(k)||k=='mibois')F.push({k:'inv',l:'⇄ Inverser (échanger tenon et mortaise / pièce du dessus et du dessous)',t:'chk',rb:1});
  if(k=='mibois')F.push({k:'pc',r:'A',l:'Entaille dans la pièce du dessous (% de la zone de recouvrement)',t:'num',h:'50 % : les deux pièces affleurent. Moins de 50 % garde plus de bois sur la pièce du dessous.'},{k:'chev',l:'Chevillage du mi-bois',t:'sel',rb:1,o:[['peg','Chevillé (cheville ronde dans les deux pièces)'],['tenon','Chevillé par un tenon : une pièce de votre choix traverse le mi-bois'],['none','Sans cheville']]},V.chev=='peg'?{k:'pd',l:'Diamètre de la cheville (mm)',t:'num'}:null);
  if(k=='hache'||k=='scie'||k=='plat'||k=='platscie'){const pt=k=='plat'||k=='platscie';F.push(pt?{k:'W',l:'Largeur du tenon (mm)',t:'num'}:null,{k:'d',r:'A',l:pt?'Épaisseur du tenon (mm)':'Diamètre du tenon / de la mèche (mm)',t:'num',h:'Règle du tiers : au plus un tiers du diamètre de la pièce mortaisée.'});
   if(k=='hache'||k=='plat')F.push({k:'Lc',r:'B',l:k=='plat'?'Longueur de l’embase en pente (mm)':'Longueur du cône de l’embase (mm)',t:'num',h:k=='plat'?'Pente plate taillée à la hachette entre le bois rond et le tenon plat.':'Cône taillé à la hachette, puis tenon cylindrique.'});if(!pt)F.push({k:'taper',l:'Tenon légèrement conique (tient par enfoncement)',t:'chk'});
   F.push({k:'mort',l:'Mortaise',t:'sel',o:[['thru','Débouchante : traverse la pièce (conseillé dans le bois vert)'],['blind','Borgne : s’arrête au fond du tenon']]})}
  if(k.startsWith('aronde')){F.push({k:'W',r:'A',l:'Largeur de la queue (mm)',t:'num'},k=='aronde2'?{k:'d',r:'D',l:'Épaisseur de la languette (mm) = demi-épaisseur',t:'num'}:k=='aronde3'?{k:'d',r:'D',l:'Épaisseur de la queue (mm), dans l’axe du cylindre',t:'num'}:null,k=='aronde2'||k=='aronde3'?{k:'flip',l:'Encoche de l’autre côté (gauche ↔ droite)',t:'chk',rb:1}:null,k=='aronde1'?{k:'depth',r:'B',l:'Profondeur de la rainure (mm)',t:'num',h:'Environ un tiers du diamètre de la pièce qui reçoit. La rainure ne la coupe jamais entièrement.'}:null,{k:'theta',r:'C',l:'Angle de chaque côté (°)',t:'num'})}
  if(k=='cheville'){if(V.mode=='new')F.push({k:'pd',l:'Diamètre de la cheville (mm)',t:'num'},{k:'over',l:'Dépassement de chaque côté (mm)',t:'num'});F.push({k:'axis',l:'Axe de la cheville',t:'sel',o:[['auto','Automatique (perpendiculaire aux pièces)'],['X','Selon X'],['Y','Selon Y'],['Z','Selon Z']]})}
  if(k=='lash')F.push({k:'ltype',l:'Type de brêlage',t:'sel',o:[['x','Brêlage en X (pièces qui se croisent : une diagonale, puis l’autre)'],['droit','Brêlage droit (pièces parallèles)']]},{k:'turns',l:'Nombre de tours de corde',t:'num'},{k:'rope',l:'Diamètre de la corde (mm)',t:'num'},{k:'inf',t:'info',l:'Le froissartage se fait sans ficelle : le brêlage n’est qu’une dernière option (cabestan au départ).'});
  if(k=='lash'||(k=='cheville'&&V.mode=='new'))F.push({k:'side',l:'Côté où poser la 2ᵉ pièce',t:'sel',o:[['haut','Au-dessus de la pièce 1'],['bas','En dessous de la pièce 1']]});
  if(tenonKind(k)||k=='mibois'||k=='lash'||(k=='cheville'&&V.mode=='new'))F.push({k:'pos',l:'Positionnement des pièces',t:'sel',o:[['auto','Automatique : la pièce est ajustée pour que l’assemblage tombe juste'],['manual','Manuel : je garde la position que j’ai donnée']]});
  if(tenonKind(k)||k=='mibois')F.push({k:'jeu',l:'Jeu (mm)',t:'num'});
  if(tenonKind(k))F.push({k:'expl',l:'Vue éclatée dans l’aperçu (écarte la pièce pour voir tenon et mortaise)',t:'chk'});
  return F.filter(Boolean)};
 const sh=V=>{const a=P_(V.a),b=P_(V.b);if(!a||!b||V.pos!='auto'||!(tenonKind(V.kind)||V.kind=='mibois'||V.kind=='lash'||(V.kind=='cheville'&&V.mode=='new')))return{a,b,warn:[]};
  const r=autoShift(V,a,b);if(!r.dv)return{a,b,warn:r.warn||[]};const mv=r.mover,m2={...mv,pos:add(mv.pos,r.dv)};return{a:mv===a?m2:a,b:mv===b?m2:b,dv:r.dv,mv:closure(mv),warn:[]}};
 const plan=(V,S)=>{S=S||sh(V);const a=S.a,b=S.b,k=V.kind;
  if(k=='mibois'){const pl=planMibois(a,b,{pc:V.pc});if(V.chev=='peg'){const pc=planCheville([a,b],{d:V.pd,axis:'auto',lap:true});pl.ops.push(...pc.ops);pl.add=pc.add;pl.warn=pl.warn.concat(pc.warn);pl.pegRec=pc.rec}return pl}
  if(k=='cheville')return planCheville([a,b,P_(V.c)].filter(Boolean),{mode:V.mode,d:V.pd,over:V.over,axis:V.axis,peg:V.mode=='existing'?P_(V.peg):null});
  const o={...kindOpt(k),d:V.d,W:V.W,Lc:k=='platscie'?0:V.Lc,depth:V.depth,theta:V.theta,flip:V.flip,taper:V.taper?.85:0,mort:V.mort,jeu:V.jeu};return planTenon(a,b,o)};
 const win=opWin({init,title,intro:'Le tenon est taillé au bout de la première pièce et entre dans la seconde. Vous pouvez changer le type et les pièces : l’aperçu se met à jour.',fields,ok:edit?'Enregistrer':'Créer',delay:250,
  onRebuild:V=>{if(V.inv){[V.a,V.b]=[V.b,V.a];V.inv=false;['inv','a','b'].forEach(k=>{const e=$('#f_'+k);if(e){if(k=='inv')e.checked=false;else e.value=V[k]}})}if(tenonKind(V.kind)||V.kind=='mibois'){const T=P_(V.a),R=P_(V.b);if(T&&R&&tenonKind(V.kind))Object.assign(V,dfl(V.kind,T,R))}},
  preview:V=>{const a=P_(V.a),b=P_(V.b),k=V.kind;if(!a||!b)throw new Error('Choisissez deux pièces.');
   if(k=='lash'){const S=sh(V),L=lashPlan(S.a,S.b,V);return{items:[S.a,S.b].map(o=>({g:geo(o),pos:o.pos,rot:o.rot,color:o.color})).concat([{tg:lashGeo({p:L}),pos:[0,0,0],rot:[0,0,0],color:'#cfc8b8',noedge:true}]),view:bestView([S.a,S.b],L.center,350),warn:[...S.warn,...(L.note?[L.note]:[])]}}
   const S=sh(V),pl=plan(V,S),ps=[S.a,S.b,P_(V.c)].filter(Boolean);S.warn.forEach(w=>pl.warn.push(w));if(k=='cheville'&&V.mode=='existing')ps.push(P_(V.peg));
   const c=pl.center||pl.ops[0]&&w2lCenter(pl)||[0,0,0],items=prevItems(pl,[...new Set(ps)],edit&&edit.jid);let rad_=Math.max(260,2.6*Math.max(crossMin(a),crossMin(b)));
   if(V.expl&&pl.axis&&tenonKind(k)){const off=mul(pl.axis,-(pl.L+60));items[0]={...items[0],pos:add(items[0].pos,off)};rad_=Math.max(rad_,(pl.L+60)*1.1+120)}
   return{items,warn:pl.warn,dof:pl.dof,view:bestView([S.a,S.b],c,rad_)}},
  schema:(V,pv)=>{const k=V.kind,T=P_(V.a),R=P_(V.b);const ctx={...V,dT:T?crossMin(T):60};if(k=='mibois')return schema('mibois',V);if(k=='cheville')return schema('cheville',{d:V.pd});if(k=='lash')return'';if(k.startsWith('aronde'))return schema('aronde',{...V,typ:+k.slice(6)});return schema('tenon',{...ctx,style:k=='platscie'?'plat':k})},
  apply:V=>{const a=P_(V.a),b=P_(V.b),k=V.kind;
   if(k=='lash'){const S=sh(V);lashPlan(S.a,S.b,V);if(S.dv){S.mv.forEach(o=>{o.pos=add(o.pos,S.dv);o.m.position.set(...o.pos)});gzCenter()}PREF.rope=V.rope;savePrefs();const o=mkLash(a,b,{turns:V.turns,rope:V.rope,ltype:V.ltype});select([o]);msg('Brêlage ajouté (cabestan au départ).');return}
   const S=sh(V);plan(V,S);if(S.dv){S.mv.forEach(o=>{o.pos=add(o.pos,S.dv);o.m.position.set(...o.pos)});gzCenter()}const R_={a,b},pl=plan(V,R_);if(edit)replaceJid(edit.jid,()=>plan(V,R_));else{const jid=applyPlan(pl);if(pl.pegRec){}}
   select([a,b].filter(Boolean));msg((pl.title||'Assemblage')+(edit?' modifié.':' créé.')+(pl.warn.length?' ⚠ '+pl.warn.join(' '):''),6000);if(k=='mibois'&&V.chev=='tenon'&&!edit)setTimeout(()=>askPick('Mi-bois validé. Cliquez maintenant la pièce qui portera le tenon (elle traversera le mi-bois).',P=>{if(P===a||P===b)return msg('Choisissez une autre pièce.');asmWin('hache',P,a)}),80)}});
 return win}
/* positionnement automatique : amène la pièce mobile pour que les axes se croisent et que le tenon traverse comme il faut */
const closure=o=>{const S=new Set([o]);if(PREF.rigid){const Q=[o];while(Q.length){const x=Q.pop();for(const y of linkedOf(x))if(!S.has(y)){S.add(y);Q.push(y)}}}return[...S]};
function autoShift(V,a,b){const k=V.kind;
 if(k=='lash'||k=='cheville'){const ta=axisOf(a),rb=axisOf(b),Bg=1e5,nzv=cr(ta.u,rb.u);if(len(nzv)<.2)return{warn:['Les deux pièces sont presque parallèles : positionnement automatique impossible.']};
  const[pa,pb]=segClose(add(ta.p0,mul(ta.u,-Bg)),add(ta.p1,mul(ta.u,Bg)),add(rb.p0,mul(rb.u,-Bg)),add(rb.p1,mul(rb.u,Bg)));let n=nrm(nzv);if(n[2]<0)n=mul(n,-1);if(V.side=='bas')n=mul(n,-1);
  return{dv:sub(add(pa,mul(n,rad(a)+rad(b))),pb),mover:b,warn:[]}}
 const mibois=k=='mibois',T=mibois?b:a,R=mibois?a:b,ta=axisOf(T),ra=axisOf(R),B=1e5;
 if(len(cr(ta.u,ra.u))<.2)return{warn:['Les deux pièces sont presque parallèles : positionnement automatique impossible.']};
 const[pa,pb]=segClose(add(ta.p0,mul(ta.u,-B)),add(ta.p1,mul(ta.u,B)),add(ra.p0,mul(ra.u,-B)),add(ra.p1,mul(ra.u,B)));let dv=sub(pb,pa);
 if(mibois)return{dv,mover:T,warn:[]};
 const e0=add(ta.p0,dv),e1=add(ta.p1,dv),tip=len(sub(e0,pb))<len(sub(e1,pb))?e0:e1,oth=tip===e0?e1:e0,ax=nrm(sub(tip,oth)),ts=lineHits(R,tip,ax);
 if(ts.length<2)return{warn:['La ligne du tenon ne rencontre pas l’autre pièce : positionnement automatique impossible.']};
 const tN=ts[0],tF=ts[ts.length-1],aro=k.startsWith('aronde');let s;
 if(k=='aronde2'||k=='aronde3')s=tF+2;else if(aro)s=tN+Math.max(8,V.depth||0);else if(V.mort=='blind')s=tN+.75*(tF-tN);else s=tF+2;
 if(k=='aronde3'){const wv=(()=>{let q_=sub(ra.u,mul(ax,dot(ra.u,ax)));return len(q_)>.2?nrm(q_):bas(ax)[0]})(),e2=nrm(cr(wv,ax)),rR=rad(R),t=V.d||crossMin(T)/3;dv=add(dv,mul(e2,(V.flip?1:-1)*((rR-t/2)+2)))}
 return{dv:add(dv,mul(ax,s)),mover:T,warn:[]}}
const w2lCenter=pl=>{const e=pl.ops[0];return e?l2w(e.o,e.op.c||e.op.o||[0,0,0]):[0,0,0]};
function mkLash(A,B,opt){const L=lashPlan(A,B,{turns:6,rope:PREF.rope||2,...opt});return addObj('lash',{turns:L.turns,rope:L.rope,ltype:L.ltype,paths:L.paths},null,'Brêlage '+A.name+' / '+B.name,'#cfc8b8',[0,0,0],[0,0,0],A.par)}
const mkTenon=(T,R,opt)=>{const pl=planTenon(T,R,opt);applyPlan(pl);return pl};
const mkMibois=(A,B,opt)=>{const pl=planMibois(A,B,opt);applyPlan(pl);return pl};
let PRE_LT=null;
function asmStart(type,first){const S=sel.filter(isWood);if(type.startsWith('lash-')){PRE_LT=type.slice(5);type='lash'}const k=type=='lash'?'lash':type;
 const go=(A,B)=>{if(A===B)return msg('Il faut deux pièces différentes.');asmWin(k=='aronde'?'aronde1':k,A,B)};
 if(type=='cheville'&&!first&&S.length>=1&&selA==null)return asmWin('cheville',S[0],S[1]||objs.filter(isWood).find(o=>o!==S[0]));
 if(S.length==2&&selA==null&&!first)return go(S[0],S[1]);
 const a=first||(S.length==1?S[0]:null);
 if(a)askPick(`« ${a.name} » : cliquez maintenant l’autre pièce à assembler.`,b=>go(a,b));
 else askPick('Cliquez la première pièce à assembler.',a=>askPick(`« ${a.name} » : cliquez la deuxième pièce.`,b=>go(a,b)))}
function editOp(o,i){const op=o.ops[i];if(!op||!op.rec)return msg('Cette opération ne se modifie pas : supprimez-la et recréez-la.');const r=op.rec,A=P_(r.ids[0]),B=P_(r.ids[1]);
 if(r.k=='tenon'||r.k=='mibois'||r.k=='cheville')return asmWin(r.k,A,B,{jid:op.jid,rec:r});
 if(r.k=='quart')return quartWin(A,{jid:op.jid,rec:r});if(r.k=='coupe')return coupeWin(A,{jid:op.jid,rec:r});if(r.k=='pointe')return pointeWin(A,{jid:op.jid,rec:r})}
/* ----- opérations sur une seule pièce ----- */
function oneWin(o,cfg,edit){const init=edit?edit.rec.opt:{};const win=opWin({title:cfg.title,intro:cfg.intro,fields:cfg.fields(init),ok:edit?'Enregistrer':'Appliquer',
  preview:V=>{const pl=cfg.plan(o,V),items=prevItems(pl,[o],edit&&edit.jid);if(pl.plane){const r=rad(o)*2.2,gm=new THREE.CylinderGeometry(r,r,1.5,40);gm.rotateX(Math.PI/2);items.push({tg:gm,pos:pl.plane.p,rot:eul(pl.plane.n),color:'#e08a00',ghost:true})}return{items,warn:pl.warn||[],view:cfg.view(o,V),extra:cfg.extra&&cfg.extra(o,V,pl)}},schema:cfg.schema,handles:cfg.handles,
  apply:V=>{if(edit)replaceJid(edit.jid,()=>cfg.plan(o,V));else applyPlan(cfg.plan(o,V));msg(cfg.title+(edit?' modifié.':' appliqué.'))}});return win}
const midW=(o,s)=>{const la=localAxis(o);return l2w(o,add(la.p0,mul(la.u,s)))};
const axW=o=>{const la=localAxis(o);return{p0:l2w(o,la.p0),u:dl2w(o,la.u),L:la.L}};
function quartWin(o,edit){o=o||sel1();if(!o||!isWood(o))return msg('Sélectionnez une traverse.');const la=localAxis(o);
 oneWin(o,{title:'Quart de bois',intro:'Retire un quartier de la pièce sur une longueur choisie, par exemple pour poser un plateau de table.',
  fields:i=>[{k:'mode',l:'Forme',t:'sel',v:i.mode||'quart',o:[['quart','Quart de bois (90°)'],['demi','Demi-bois (180°)']]},{k:'start',l:'Début à partir du bout A (mm)',t:'num',v:i.start??0},{k:'len',l:'Longueur retirée (mm)',t:'num',v:i.len??Math.min(400,Math.round(la.L/2))},{k:'pos',l:'Quartier retiré',t:'sel',v:i.pos??0,o:[[0,'Haut, côté A'],[-90,'Haut, côté B'],[90,'Bas, côté A'],[180,'Bas, côté B']]}],
  handles:V=>{const a=axW(o);return[{p0:a.p0,dir:a.u,k:'start',t:()=>V.start||0,toVal:t=>t,min:0,max:a.L-20,snap:10},{p0:a.p0,dir:a.u,k:'len',t:()=>(V.start||0)+V.len,toVal:t=>t-(V.start||0),min:(V.start||0)+10,max:a.L,snap:10}]},plan:(o,V)=>planQuart(o,V),view:(o,V)=>bestView([o],midW(o,V.start+V.len/2),Math.max(250,la.L>0?Math.min(la.L/2,(V.len||300)*.9+200):300)),schema:V=>schema('quart',V)},edit)}
function coupeWin(o,edit){o=o||sel1();if(!o||!isWood(o))return msg('Sélectionnez une pièce.');const la=localAxis(o);
 oneWin(o,{title:'Couper avec un plan de coupe',intro:'Un plan de coupe (poignée orange) se déplace le long de la pièce, avec une graduation. Choisissez de garder les deux morceaux ou un seul.',fields:i=>[{k:'dist',l:'Position du plan de coupe depuis le bout A (mm)',t:'num',v:i.dist??Math.round(la.L/2)},{k:'angle',l:'Biais du plan de coupe (°), 0 = coupe droite',t:'num',v:i.angle??0},{k:'keep',l:'Que garder ?',t:'sel',v:i.keep??'both',o:[['both','Les deux morceaux'],['A','Seulement le côté du bout A'],['B','Seulement le côté du bout B']]}],
  handles:V=>{const a=axW(o);return[{p0:a.p0,dir:a.u,k:'dist',t:()=>V.dist,toVal:t=>t,min:10,max:a.L-10,snap:10}]},extra:(o,V)=>{const a=axW(o),r=rad(o)*1.3,[e1]=bas(a.u),st=a.L>2500?500:a.L>800?100:50,lines=[[a.p0,add(a.p0,mul(a.u,a.L)),0xe08a00]];for(let t=0;t<=a.L+1e-6;t+=st){const q=add(a.p0,mul(a.u,t)),big=Math.round(t/st)%5==0,h=r*(big?1.5:.9);lines.push([sub(q,mul(e1,h)),add(q,mul(e1,h)),0xe08a00])}return{lines}},plan:(o,V)=>planCoupe(o,V),view:(o,V)=>bestView([o],l2w(o,add(localAxis(o).p0,mul(localAxis(o).u,V.dist))),Math.max(300,la.L*.6))},edit)}
function pointeWin(o,edit){o=o||sel1();if(!o||!isWood(o))return msg('Sélectionnez une pièce.');
 oneWin(o,{title:'Tailler en pointe',intro:'Pointe taillée à la hachette, pour planter un piquet.',fields:i=>[{k:'end',l:'Bout à tailler',t:'sel',v:i.end??0,o:[[0,'Bout A (origine)'],[1,'Bout B']]},{k:'len',l:'Longueur de la pointe (mm)',t:'num',v:i.len??Math.round(crossMin(o)*3)},{k:'r0',l:'Rayon du bout (mm)',t:'num',v:i.r0??3}],
  handles:V=>{const a=axW(o);return[{p0:a.p0,dir:a.u,k:'len',t:()=>V.end==1?a.L-V.len:V.len,toVal:t=>V.end==1?a.L-t:t,min:20,max:a.L-10,snap:10}]},plan:(o,V)=>planPointe(o,V),view:(o,V)=>bestView([o],l2w(o,V.end==1?localAxis(o).p1:localAxis(o).p0),Math.max(300,V.len*1.3))},edit)}
function fendreWin(o){o=o||sel1();if(!o||!isWood(o))return msg('Sélectionnez la pièce à fendre.');const D0=crossMin(o);
 opWin({title:'Fendre « '+esc(o.name)+' »',intro:'Chaque morceau devient une pièce indépendante et réutilisable.',ok:'Fendre',delay:300,
  fields:V=>[{k:'mode',l:'Fendre en',t:'sel',v:V.mode||'planches',rb:1,o:[['planches','Planches d’épaisseur choisie'],['demi','Demi-rondins'],['quartiers','Quartiers (3 ou 4)']]},
   V.mode=='planches'||!V.mode?{k:'t',l:'Épaisseur des planches (mm)',t:'num',v:V.t||Math.max(10,Math.round(D0/5))}:V.mode=='quartiers'?{k:'n',l:'Nombre de quartiers',t:'sel',v:V.n||4,o:[[3,'3'],[4,'4']]}:null,
   {k:'angle',l:'Orientation du trait de fente (°)',t:'num',v:V.angle||0},{k:'gap',l:'Écarter les morceaux de (mm)',t:'num',v:V.gap??15},(V.mode||'planches')=='planches'?{k:'waste',l:'Jeter la chute (morceau qui n’a pas l’épaisseur voulue)',t:'chk',v:V.waste??true}:null,(V.mode||'planches')=='planches'?{k:'layout',l:'Disposition des planches',t:'sel',v:V.layout||'pile',rb:1,o:[['pile','Telles que fendues'],['plateau','En plateau : côte à côte, à plat']]}:null,V.layout=='plateau'?{k:'gap2',l:'Jeu entre planches (mm)',t:'num',v:V.gap2??0}:null].filter(Boolean),
  preview:V=>{const pl=planFendre(o,{mode:V.mode,t:V.t,n:V.n,angle:V.angle,gap:V.gap,start:V.angle,waste:V.waste});const cols=['#c8a06a','#d2ab76','#bd935a','#b5894f'];
   return{items:pl.parts.map((p,i)=>({g:p.g,pos:add(o.pos,mul(dl2w(o,p.dirL),pl.gap*(p.off<0?-1:p.off>0?1:0))),rot:o.rot,color:cols[i%4]})),view:bestView([o],midW(o,localAxis(o).L/2),Math.max(300,rad(o)*3)),warn:[`${pl.parts.length} morceaux`+(pl.wasted?` (chute jetée : ${pl.wasted})`:'')]}},
  schema:V=>schema('fendre',{t:V.t||30,D:D0}),apply:V=>{const L=fendre(o,{mode:V.mode,t:V.t,n:V.n,angle:V.angle,gap:V.gap,start:V.angle,layout:V.layout,gap2:V.gap2,waste:V.waste});msg(L.length+' morceaux créés.')}})}
/* ----- répétition linéaire ou circulaire ----- */
function repMats(list,V){const[mn,mx]=bounds(list),cen=mn.map((v,i)=>(v+mx[i])/2),n=Math.max(2,Math.min(300,Math.round(V.n))),out=[];
 if(V.type=='circ'){const ax=[+(V.axis=='X'),+(V.axis=='Y'),+(V.axis=='Z')],c=[V.cx,V.cy,V.cz],tot=V.ang*(V.inv?-1:1),st=V.ang>=360?tot/n:tot/(n-1);
  for(let k=1;k<n;k++){const a=st*k*D,R=new THREE.Matrix4().makeTranslation(...c).multiply(new THREE.Matrix4().makeRotationAxis(new THREE.Vector3(...ax),a)).multiply(new THREE.Matrix4().makeTranslation(...mul(c,-1)));out.push({M:R,k,a:st*k})}return{out,cen,st}}
 const L=localAxis(list[0]),axw=axisOf(list[0]);let d=[+(V.dir=='X'),+(V.dir=='Y'),+(V.dir=='Z')];if(V.dir=='axe')d=axw.u;if(V.dir=='perp'){d=nrm(cr(axw.u,[0,0,1]));if(len(d)<.1||isNaN(d[0]))d=[1,0,0]}
 const step=V.mode=='total'?V.step/(n-1):V.step,s=step*(V.inv?-1:1);for(let k=1;k<n;k++)out.push({M:new THREE.Matrix4().makeTranslation(...mul(d,s*k)),k,d:s*k});return{out,cen,st:s,d}}
function copyObjs(list,M,jm,par){return list.map(o=>{const p=JSON.parse(JSON.stringify(o.p)),Mo=M.clone().multiply(matOf(o));const c=mkObj(o.type,p,o.g,o.name,o.color,[0,0,0],[0,0,0],par??o.par);setMat(c,Mo);c.mat=o.mat;c.ops=JSON.parse(JSON.stringify(o.ops||[])).map(op=>{if(op.jid){if(!jm.has(op.jid))jm.set(op.jid,++JID);op.jid=jm.get(op.jid);delete op.rec}return op});mk(c);return c})}
function repWin(){let list=targets().filter(isWood);if(!list.length)return msg('Sélectionnez d’abord la ou les pièces à répéter.');const[mn,mx]=bounds(list),cen=mn.map((v,i)=>(v+mx[i])/2);
 opWin({title:'Répétition',intro:'Copie la sélection en série, en ligne ou en cercle. Les distances et angles s’affichent dans l’aperçu.',ok:'Répéter',delay:200,
  fields:V=>[{k:'type',l:'Type',t:'sel',v:V.type||'lin',rb:1,o:[['lin','Linéaire'],['circ','Circulaire']]},{k:'n',l:'Nombre total de pièces (original compris)',t:'num',v:V.n||5},
   ...((V.type||'lin')=='lin'?[{k:'dir',l:'Direction',t:'sel',v:V.dir||'X',o:[['X','Axe X'],['Y','Axe Y'],['Z','Axe Z (vertical)'],['axe','Dans l’axe de la pièce'],['perp','Perpendiculaire à la pièce (horizontal)']]},{k:'mode',l:'Définir par',t:'sel',v:V.mode||'pas',o:[['pas','Pas entre deux pièces'],['total','Longueur totale']]},{k:'step',l:V.mode=='total'?'Longueur totale (mm)':'Pas (mm)',t:'num',v:V.step||200}]
    :[{k:'axis',l:'Axe de rotation',t:'sel',v:V.axis||'Z',o:[['Z','Vertical (Z)'],['X','Axe X'],['Y','Axe Y']]},{k:'cx',l:'Centre X (mm)',t:'num',v:V.cx??Math.round(cen[0])},{k:'cy',l:'Centre Y (mm)',t:'num',v:V.cy??Math.round(cen[1])},{k:'cz',l:'Centre Z (mm)',t:'num',v:V.cz??Math.round(cen[2])},{k:'ang',l:'Angle total (°)',t:'num',v:V.ang||360,h:'360° : les pièces se répartissent sur le cercle complet.'}]),
   {k:'inv',l:'Inverser le sens',t:'chk',v:V.inv||false},{k:'grp',l:'Regrouper les copies dans un assemblage',t:'chk',v:V.grp??true}],
  preview:V=>{const r=repMats(list,V),items=list.map(o=>({g:geo(o),pos:o.pos,rot:o.rot,color:o.color})),lines=[],labels=[];
   r.out.forEach(({M})=>list.forEach(o=>{const Mo=M.clone().multiply(matOf(o)),p=new THREE.Vector3(),q=new THREE.Quaternion(),s=new THREE.Vector3();Mo.decompose(p,q,s);const E=new THREE.Euler().setFromQuaternion(q,'ZYX');items.push({g:geo(o),pos:p.toArray(),rot:[E.x/D,E.y/D,E.z/D],color:o.color,ghost:1})}));
   let prev=cen;r.out.slice(0,40).forEach(({M,k,a,d})=>{const c=new THREE.Vector3(...cen).applyMatrix4(M).toArray();lines.push([prev,c]);if(k==1||k==r.out.length)labels.push({p:mul(add(prev,c),.5),t:V.type=='circ'?r1(Math.abs(r.st))+'°':fr(Math.abs(r.st))+' mm'});prev=c});
   const rad_=Math.max(mx[0]-mn[0],mx[1]-mn[1],mx[2]-mn[2],300);return{items,extra:{lines,labels},view:{dir:[.6,-.85,.6]},warn:[`${Math.max(2,Math.min(300,Math.round(V.n)))} pièces au total`]}},
  schema:V=>schema('rep',{type:V.type,step:V.step,total:V.step,ang:V.ang}),
  apply:V=>{const all=repApply(list,V);msg(all.length+' pièces créées.');select(all)}})}
function repApply(list,V){const r=repMats(list,V),jm=new Map();let par=0;if(V.grp){par=newAsm('Répétition').id}const all=[];batch(()=>r.out.forEach(({M})=>all.push(...copyObjs(list,M,jm,par||undefined))));touch();return all}
/* ----- clayonnage ----- */
function claiePlan(S,V){if(S.length<2)throw new Error('Sélectionnez au moins deux supports (traverses parallèles) avant d’ouvrir le clayonnage.');const A=S.map(axisOf),a=A[0].u;
 S.forEach((s,i)=>{if(Math.abs(dot(A[i].u,a))<.97)throw new Error('Les supports doivent être parallèles.')});if(V.d<8||V.d>20)throw new Error('Diamètre des claies : de 8 à 20 mm.');
 const cen=A.map(x=>mul(add(x.p0,x.p1),.5)),O=cen[0];let p=sub(cen[cen.length-1],O);p=sub(p,mul(a,dot(p,a)));if(len(p)<10)throw new Error('Les supports sont trop proches.');p=nrm(p);let h=nrm(cr(a,p));if(h[2]<0)h=mul(h,-1);
 const idx=S.map((s,i)=>i).sort((i,j)=>dot(sub(cen[i],O),p)-dot(sub(cen[j],O),p)),tO=dot(O,a);let lo=-1e18,hi=1e18;S.forEach(s=>{const[l,u]=ext(s,a);lo=Math.max(lo,l);hi=Math.min(hi,u)});if(V.lim){lo=V.lim[0];hi=V.lim[1]}
 const d=V.d,r=d/2,pitch=V.pm=='joint'?d:V.pitch;if(!(pitch>=d-.01))throw new Error('Le pas ne peut pas être inférieur au diamètre des claies (jointives).');const t0=lo+V.margin+(V.from||0),t1=Math.min(hi-V.margin,V.zone>0?t0+V.zone:1e18),n=Math.floor((t1-t0-d)/pitch)+1;if(n<1)throw new Error('Pas assez de place pour une claie.');if(n>200)throw new Error('Trop de claies ('+n+') : augmentez le pas.');
 const rods=[],warn=[];let minR=1e9;
 for(let i=0;i<n;i++){const t=t0+r+i*pitch,s0=(V.start=='sous'?-1:1)*(i%2==0?1:-1),W=(s,hh)=>add(add(add(O,mul(a,t-tO)),mul(p,s)),mul(h,hh)),pts=[];
  const cr=[],ks=idx.map((j,q)=>({s:dot(sub(cen[j],O),p),hh:dot(sub(cen[j],O),h),r:rad(S[j]),sg:s0*(q%2?-1:1)}));
  {const k0=ks[0];pts.push(W(k0.s-(k0.r+4+V.over),k0.hh+k0.sg*(k0.r+r)))}ks.forEach((k,q)=>{const hw=k.hh+k.sg*(k.r+r),dl=(k.r+r)*1.15;if(q>0)pts.push(W(k.s-dl,hw));pts.push(W(k.s,hw));if(q<ks.length-1)pts.push(W(k.s+dl,hw));cr.push({p:W(k.s,hw),over:k.sg>0,r:k.r,j:q});if(q<ks.length-1){const m=ks[q+1];pts.push(W((k.s+m.s)/2,(hw+m.hh+m.sg*(m.r+r))/2))}});{const kl=ks[ks.length-1];pts.push(W(kl.s+(kl.r+4+V.over),kl.hh+kl.sg*(kl.r+r)))}
  const flip=V.taper&&i%2==1,d0=V.taper?(flip?d:d*.8):d,d1=V.taper?(flip?d*.8:d):d;rods.push({pos:pts[0],pts:pts.map(q=>sub(q,pts[0])),d0,d1,name:'Claie '+(i+1),cr,dir:a});
  if(i<2){const cv=new THREE.CatmullRomCurve3(pts.map(q=>new THREE.Vector3(...q)),false,'centripetal'),P=cv.getPoints(80);for(let j=1;j<P.length-1;j++){const u=P[j].clone().sub(P[j-1]),v=P[j+1].clone().sub(P[j]),w=P[j+1].clone().sub(P[j-1]),cr_=u.clone().cross(v).length();if(cr_>1e-9)minR=Math.min(minR,u.length()*v.length()*w.length()/(2*cr_))}}}
 if(minR<20*d)warn.push(`Rayon de courbure ≈ ${Math.round(minR)} mm (< 20 à 25 fois le diamètre) : le bois vert risque de casser. Estimation à valider, pas une règle du livre.`);
 return{rods,n,warn,pitch,minR}}
/* clous cavaliers aux croisements « dessus » (un toutes les N claies) */
function mkCavaliers(pl,V,par,only){const N=Math.max(1,Math.round(V.cavN||3)),dc=V.d,w=dc+4,h=dc+12,ca=newAsm('Clous cavaliers',par.id);let n=0;
 pl.rods.forEach((r,i)=>{if(i%N)return;(r.cr||[]).forEach(c=>{if(!c.over||(only&&!only(c)))return;const ang=Math.atan2(r.dir[1],r.dir[0])/D;mkObj('cavalier',{w,h,wire:3},null,'Clou cavalier','#8a8f99',[c.p[0],c.p[1],c.p[2]+dc/2+1.5-h],[0,0,ang],ca.id);n++})});return n}
function limOf(S){const a=axisOf(S[0]).u;let lo=-1e18,hi=1e18;S.forEach(s=>{const[l,u]=ext(s,a);lo=Math.max(lo,l);hi=Math.min(hi,u)});return[lo,hi]}
function midPlan(S,dm,V){const A=S.map(axisOf),a=A[0].u;let[lo,hi]=limOf(S);const c=mul(add(mul(add(A[0].p0,A[0].p1),.5),mul(add(A[1].p0,A[1].p1),.5)),.5),k=dot(c,a);
 if(V){try{const pl=claiePlan([S[0],fakeMid(S,dm),S[1]],{...V,lim:[lo,hi]}),R=pl.rods;if(R.length){const r=V.d/2;lo=Math.max(lo,dot(R[0].pos,a)-r-10);hi=Math.min(hi,dot(R[R.length-1].pos,a)+r+10)}}catch(e){}}
 const p0=add(c,mul(a,lo-k)),p1=add(c,mul(a,hi-k)),v=sub(p1,p0);return{p0,p1,L:len(v),rot:eul(v),d:dm}}
function fakeMid(S,dm,V){const m=midPlan(S,dm,V),p={d:dm,L:m.L};return{id:-1,type:'trav',p,g:build({type:'trav',p}),pos:m.p0,rot:m.rot,ops:[],name:'Traverse fine centrale',par:0,color:'#d2ab76',mat:''}}
function clayWin(S,editAsm){const AS=editAsm&&asms[editAsm],E0=AS&&AS.src&&AS.src.V;if(AS&&AS.src)S=AS.src.ids.map(P_).filter(Boolean);S=S||targets().filter(isWood);if(S.length<2)return msg('Sélectionnez d’abord les supports (au moins 2 traverses parallèles).');const SS=V=>V.mid&&S.length==2?[S[0],fakeMid(S,V.dm||30,V),S[1]]:S;
 opWin({title:E0?'Modifier le clayonnage':'Clayonnage (plateau de claies)',init:E0?{...E0}:{mid:S.length==2,dm:30},intro:'Les claies passent alternativement sous et sur les supports. Une claie sur deux est inversée. Avec deux supports, une traverse fine au milieu est nécessaire : sans elle les claies ne seraient pas tordues des deux côtés et tomberaient.',ok:E0?'Enregistrer':'Créer le clayonnage',delay:400,
  fields:V=>[S.length==2?{k:'mid',l:'Ajouter une traverse fine au milieu (recommandé)',t:'chk',rb:1}:null,S.length==2&&V.mid?{k:'dm',l:'Diamètre de la traverse fine (mm)',t:'num'}:null,{k:'d',l:'Diamètre des claies (8 à 20 mm)',t:'num',v:V.d||20},{k:'pm',l:'Espacement',t:'sel',v:V.pm||'joint',rb:1,o:[['joint','Jointives (entraxe = diamètre)'],['libre','Pas libre']]},V.pm=='libre'?{k:'pitch',l:'Pas entre claies (mm)',t:'num',v:V.pitch||30}:null,{k:'margin',l:'Marge aux extrémités (mm)',t:'num',v:V.margin??10},{k:'from',l:'Début du clayage après la marge (mm)',t:'num',v:V.from??0,h:'Distance depuis l’extrémité des supports jusqu’à la première claie.'},{k:'zone',l:'Longueur clayée (mm), 0 = jusqu’au bout',t:'num',v:V.zone??0},{k:'over',l:'Débord au-delà des supports (mm), 5 maximum',t:'num',v:V.over??0},{k:'start',l:'Première claie',t:'sel',v:V.start||'sous',o:[['sous','Sous le premier support'],['dessus','Sur le premier support']]},{k:'taper',l:'Alterner pied et tête (gaules coniques)',t:'chk',v:V.taper??true},{k:'cav',l:'Fixer avec des clous cavaliers',t:'chk',v:V.cav??false,rb:1},V.cav?{k:'cavN',l:'Un clou cavalier toutes les … claies',t:'num',v:V.cavN||3}:null].filter(Boolean),
  preview:V=>{const SX=SS(V),pl=claiePlan(SX,{...V,lim:V.mid&&S.length==2?limOf(S):undefined}),items=SX.map(o=>({g:geo(o),pos:o.pos,rot:o.rot,color:o.color}));pl.rods.slice(0,4).forEach(r=>items.push({g:tubeGeom({pts:r.pts,d0:r.d0,d1:r.d1}),pos:r.pos,rot:[0,0,0],color:'#b5894f',noedge:true}));
   const c=mul(S.map(o=>mul(add(axisOf(o).p0,axisOf(o).p1),.5)).reduce(add),1/S.length);return{items,warn:[pl.n+' claies à créer (aperçu : 4 premières)',...pl.warn],view:{dir:[.5,-.8,.6],center:c,radius:Math.max(300,pl.rods[0]?len(pl.rods[0].pts[pl.rods[0].pts.length-1])*.8:400)}}},
  handles:V=>{const a=axisOf(S[0]),A0=a.u;let lo=-1e18,hi=1e18;S.forEach(s=>{const[l,u]=ext(s,A0);lo=Math.max(lo,l);hi=Math.min(hi,u)});const c0=mul(add(a.p0,a.p1),.5),p0=add(c0,mul(A0,lo-dot(c0,A0))),m=V.margin||0,fr_=V.from||0;return[{p0,dir:A0,k:'from',t:()=>m+(V.from||0),toVal:t=>t-m,min:m,max:hi-lo},{p0,dir:A0,k:'zone',t:()=>m+(V.from||0)+(V.zone>0?V.zone:hi-lo-2*m-(V.from||0)),toVal:t=>t-m-(V.from||0),min:m+(V.from||0)+20,max:hi-lo}]},
  schema:V=>schema('clay',V),onRebuild:null,apply:V=>{if(AS){const m=objs.find(o=>o.id==(AS.src.mid||-1));if(m)rmObjs([m]);delAsm(editAsm,true)}let S2=S,midId=0;if(V.mid&&S.length==2){const m=midPlan(S,V.dm||30,V),mo=mkObj('trav',{d:m.d,L:m.L},null,'Traverse fine centrale','#d2ab76',m.p0,m.rot,S[0].par);midId=mo.id;S2=[S[0],mo,S[1]];}const pl=claieApply(S2,{...V,lim:V.mid&&S.length==2?limOf(S):undefined});if(selA!=null&&asms[selA])asms[selA].src={t:'clay',V:{...V},ids:S.map(o=>o.id),mid:midId};msg(pl.n+' claies créées.'+(pl.warn.length?' ⚠ '+pl.warn[0]:''),6000)}})}
function claieApply(S,V){const pl=claiePlan(S,V),a=newAsm('Clayonnage'),par=S[0].par;batch(()=>{pl.rods.forEach(r=>{mkObj('courbe',{pts:r.pts,d0:r.d0,d1:r.d1,len:0},null,r.name,'#b5894f',r.pos,[0,0,0],a.id)});if(V.cav)mkCavaliers(pl,V,a)});if(par)a.par=par;select([],a.id);return pl}
/* ----- contrôle des collisions ----- */
function rodSegs(o){if(o.type=='courbe'){const cv=new THREE.CatmullRomCurve3(o.p.pts.map(q=>new THREE.Vector3(...l2w(o,q))),false,'centripetal'),P=cv.getPoints(24).map(v=>v.toArray()),r=(o.p.d0+o.p.d1)/4;return P.slice(1).map((q,i)=>({a:P[i],b:q,r}))}
 if(isWood(o)&&(o.type=='trav'||AX2.includes(o.type))){const A=axisOf(o);return[{a:A.p0,b:A.p1,r:rad(o)}]}return[]}
function collisions(){const R=objs.map(o=>({o,s:rodSegs(o),j:new Set(jidsOf(o))})).filter(x=>x.s.length),out=[];
 const bb=x=>{const b=new THREE.Box3();x.s.forEach(g=>{b.expandByPoint(new THREE.Vector3(...g.a));b.expandByPoint(new THREE.Vector3(...g.b))});b.expandByScalar(Math.max(...x.s.map(g=>g.r)));return b};R.forEach(x=>x.bb=bb(x));
 for(let i=0;i<R.length;i++)for(let k=i+1;k<R.length;k++){const A=R[i],B=R[k];if([...A.j].some(j=>B.j.has(j)))continue;if(!A.bb.intersectsBox(B.bb))continue;let worst=0;
  for(const g of A.s)for(const h of B.s){const[p,q]=segClose(g.a,g.b,h.a,h.b),dd=len(sub(p,q)),pen=g.r+h.r-dd;if(pen>worst)worst=pen}
  if(worst>1)out.push({a:A.o,b:B.o,pen:worst});if(out.length>300)return out}
 return out}
function dCollisions(){const L=collisions();modal(`<h3>Contrôle des collisions</h3>`+(L.length?`<p class="mu">${L.length} pièces se chevauchent sans assemblage entre elles. Cliquez une ligne pour les sélectionner.</p><div class="ops">${L.slice(0,60).map((c,i)=>`<div class="op" style="cursor:pointer" onclick="closeMd();select([P_(${c.a.id}),P_(${c.b.id})])"><span>${esc(c.a.name)} / ${esc(c.b.name)}</span><span class="mu">${Math.round(c.pen)} mm</span></div>`).join('')}</div>`:'<p>Aucune collision détectée entre les traverses et les claies (distance entre axes ≥ somme des rayons). Les autres types de pièces ne sont pas contrôlés.</p>')+`<div class="r"><button onclick="closeMd()">Fermer</button></div>`)}

const barHandles=(A,V,ks,kl)=>{if(!A)return[];const a=axisOf(A);return[{p0:a.p0,dir:a.u,k:ks,t:()=>V[ks]||0,toVal:t=>t,min:0,max:a.L-20},{p0:a.p0,dir:a.u,k:kl,t:()=>V[kl]>0?V[kl]:a.L,toVal:t=>t,min:(V[ks]||0)+20,max:a.L}]};
/* ----- PH (paraboloïde hyperbolique) : cordes tendues entre deux (ou quatre) bords gauches, purement décoratif ----- */
/* jonction des deux traverses (là où elles se croisent) : le PH part de là, il n'y a que les bouts « fuyants » à régler */
function phJunction(A,B){const a=axisOf(A),b=axisOf(B),big=1e5;const[pa,pb]=segClose(add(a.p0,mul(a.u,-big)),add(a.p1,mul(a.u,big)),add(b.p0,mul(b.u,-big)),add(b.p1,mul(b.u,big)));
 const tA=Math.max(0,Math.min(a.L,dot(sub(pa,a.p0),a.u))),tB=Math.max(0,Math.min(b.L,dot(sub(pb,b.p0),b.u)));
 const secs=['++','+-','-+','--'],ln=(L,t,s)=>s=='+'?L-t:t,best=secs.map(q=>[Math.min(ln(a.L,tA,q[0]),ln(b.L,tB,q[1])),q]).sort((x,y)=>y[0]-x[0])[0][1];
 return{a,b,tA,tB,J:mul(add(add(a.p0,mul(a.u,tA)),add(b.p0,mul(b.u,tB))),.5),best,la:q=>ln(a.L,tA,q[0]),lb:q=>ln(b.L,tB,q[1])}}
function phPlan(V){const P=[V.a,V.b,V.c,V.d].map(P_).filter(Boolean),pairs=[[P_(V.a),P_(V.b),V.sec,V.l1,V.eb,V.n1,V.e1,V.ord]];if(P_(V.c)&&P_(V.d))pairs.push([P_(V.c),P_(V.d),V.sec2,V.l2,V.l2b,V.n2,V.e2,V.ord]);
 const segs=[],warn=[],info=[];let nrmF=null;
 pairs.forEach(([A,B,sec,l,eb,n,e,ord])=>{if(!A||!B||A===B)throw new Error('Choisissez deux traverses différentes.');const J=phJunction(A,B),q=sec||J.best,da=q[0]=='+'?1:-1,db=q[1]=='+'?1:-1,mA=J.la(q),mB=J.lb(q),dA=Math.min(l>0?l:mA,mA),dB=Math.min(eb>0?eb:mB,mB);
  if(dA<20||dB<20)throw new Error('Zone trop courte : choisissez un autre angle (secteur) ou rallongez les traverses.');const zl=Math.max(dA,dB),cnt=n=='auto'?Math.max(3,Math.round(zl/100)+1):n=='custom'?Math.floor(zl/Math.max(10,e))+1:+n;if(!(cnt>=2))throw new Error('Il faut au moins deux cordes.');if(cnt>80)throw new Error('Trop de cordes : augmentez l’espacement.');
  const a=J.a,b=J.b,ra=rad(A),rb=rad(B),rr=Math.max(1,V.dia)/2,ua=mul(a.u,da),ub=mul(b.u,db),perp=(u,w)=>{const p=sub(w,mul(u,dot(w,u)));return len(p)>1e-6?nrm(p):bas(u)[0]},nA=perp(a.u,ub),nB=perp(b.u,ua),flat=len(cr(a.u,b.u))<.05;let nz=flat?[0,0,1]:nrm(cr(a.u,b.u));if(!nrmF)nrmF=nz;
  const pa=t=>add(add(a.p0,mul(a.u,t)),mul(nA,ra+rr)),pb=t=>add(add(b.p0,mul(b.u,t)),mul(nB,rb+rr)),rev=ord!='ladder';
  for(let i=0;i<cnt;i++){const f=i/(cnt-1);segs.push([pa(J.tA+da*f*dA),pb(J.tB+db*(rev?1-f:f)*dB)])}
  if(flat)info.push('Traverses dans un même plan : les cordes dessinent une courbe (parabole). Faites pivoter une traverse pour un vrai PH gauche.');
  info.push(`${cnt} cordes, ${sm(dA/(cnt-1))} d’écart sur la traverse 1, ${sm(dB/(cnt-1))} sur la traverse 2`)});
 return{segs,warn,info,pieces:P,nrm:nrmF}}
const phSpacing=(L)=>{const o=[['auto','Automatique (environ tous les 10 cm)']];[5,6,8,10,12,15,20,25,30,40].forEach(n=>{const e=L/(n-1);if(e>=15&&e<=400)o.push([String(n),`${n} cordes (tous les ${fr(Math.round(e/10*10)/10)} cm)`])});o.push(['custom','Autre espacement…']);return o};
/* clous cavaliers qui tiennent les cordes du PH sur les bords : une extrémité de corde sur N */
function mkCavPH(pl,V,par){const N=Math.max(1,Math.round(V.cavN||1)),dr=Math.max(1,V.dia),a=newAsm('Clous cavaliers',par),ps=pl.pieces;let n=0;
 pl.segs.forEach((sg,i)=>{if(i%N)return;[0,1].forEach(e=>{const p=sg[e],q=sg[1-e];let best=null,bd=1e18;ps.forEach(o=>{const ax=axisOf(o),t=Math.max(0,Math.min(1,dot(sub(p,ax.p0),sub(ax.p1,ax.p0))/dot(sub(ax.p1,ax.p0),sub(ax.p1,ax.p0)))),c=add(ax.p0,mul(sub(ax.p1,ax.p0),t)),d=len(sub(p,c));if(d<bd){bd=d;best={o,ax,c}}});
  if(!best)return;let u=nrm(sub(best.ax.p1,best.ax.p0)),nn=sub(p,best.c);nn=sub(nn,mul(u,dot(nn,u)));if(len(nn)<1e-6)return;nn=nrm(nn);
  const surf=pl.nrm?p:add(best.c,mul(nn,rad(best.o))),h=22,w=dr+4,org=add(surf,mul(nn,1.5-h)),M=new THREE.Matrix4().makeBasis(new THREE.Vector3(...u),new THREE.Vector3(...cr(nn,u)),new THREE.Vector3(...nn)),E=new THREE.Euler().setFromRotationMatrix(M,'ZYX');
  mkObj('cavalier',{w,h,wire:3},null,'Clou cavalier','#8a8f99',org,[E.x/D,E.y/D,E.z/D],a.id);n++})});return n}
function phInfer(ph){const S=ph.p.segs;if(!S.length)return null;const near=p=>objs.filter(isWood).map(o=>{const ax=axisOf(o),t=Math.max(0,Math.min(1,dot(sub(p,ax.p0),sub(ax.p1,ax.p0))/dot(sub(ax.p1,ax.p0),sub(ax.p1,ax.p0)))),c=add(ax.p0,mul(sub(ax.p1,ax.p0),t));return[len(sub(p,c))-rad(o),o]}).sort((x,y)=>x[0]-y[0])[0];const a=near(S[0][0]),b=near(S[0][1]);return a&&b&&a[1]!==b[1]?{a:a[1].id,b:b[1].id}:null}
function phWin(edit){const W=objs.filter(isWood);if(W.length<2)return msg('Il faut au moins deux pièces (traverses du PH).');let E0=edit&&edit.p.src&&edit.p.src.V;
 if(edit&&!E0){const g=phInfer(edit);if(!g)return msg('Impossible de retrouver les deux traverses de ce PH : supprimez-le et recréez-le.',6000);E0={a:g.a,b:g.b,c:'',d:'',n1:'auto',ord:'cross',face:'axe',dia:edit.p.d||PREF.rope||2,cav:false,cavN:1}}
 const S=sel.filter(isWood),pick=i=>(S[i]||W[i]||'')&&(S[i]||W[i]).id;
 const def=V=>{const A=P_(V.a),B=P_(V.b);if(!A||!B||A===B)return{};const J=phJunction(A,B);return{sec:J.best}};
 opWin({title:edit?'Modifier le PH':'PH — paraboloïde hyperbolique (décoratif)',intro:'Des cordes tendues entre deux traverses dessinent une surface courbe (purement décoratif). Le PH part de l’intersection des deux traverses : réglez seulement les bouts (poignées orange sur chaque traverse). La poignée du centre change d’angle.',ok:edit?'Enregistrer':'Créer le PH',delay:250,
  init:E0?{...E0}:{a:pick(0),b:pick(1),c:S[2]?S[2].id:'',d:S[3]?S[3].id:'',l1:0,eb:0,l2:0,l2b:0,n1:'auto',e1:100,n2:'auto',e2:100,ord:'cross',face:'dessus',cav:true,cavN:1,dia:PREF.rope||2,...def({a:pick(0),b:pick(1)})},
  onRebuild:V=>{const d=def(V);if(!V.sec||V.a!=V._a||V.b!=V._b){V.sec=d.sec;V.l1=0;V.eb=0}V._a=V.a;V._b=V.b},
  fields:V=>{const A=P_(V.a),B=P_(V.b),J=A&&B&&A!==B?phJunction(A,B):null,q=V.sec||(J&&J.best)||'++',zl=J?Math.max(V.l1>0?V.l1:J.la(q),V.eb>0?V.eb:J.lb(q)):500,F=[{k:'a',l:'Traverse 1',t:'piece',r:'A',rb:1},{k:'b',l:'Traverse 2',t:'piece',r:'B',rb:1},
   {k:'sec',l:'Angle utilisé (ou glissez la poignée du centre vers un des 4 angles)',t:'sel',o:[['++','Angle 1'],['+-','Angle 2'],['-+','Angle 3'],['--','Angle 4']]},
   {k:'l1',l:'Longueur sur la traverse 1 depuis l’intersection (mm), 0 = jusqu’au bout',t:'num',r:'A'},{k:'eb',l:'Longueur sur la traverse 2 depuis l’intersection (mm), 0 = jusqu’au bout',t:'num',r:'B'},
   {k:'n1',l:'Espacement des cordes',t:'sel',rb:1,o:phSpacing(Math.max(60,zl))}];
   if(V.n1=='custom')F.push({k:'e1',l:'Espacement entre cordes (mm)',t:'num'});
   F.push({k:'ord',l:'Disposition des cordes',t:'sel',o:[['cross','Croisées (PH classique)'],['ladder','En échelle (cordes parallèles)']]},{k:'cav',l:'Fixer les cordes aux traverses avec des clous cavaliers',t:'chk',rb:1},V.cav?{k:'cavN',l:'Un clou cavalier toutes les … cordes',t:'num'}:null,
   {k:'c',l:'Traverse 3 (second PH, facultatif)',t:'piece',none:1,rb:1},{k:'d',l:'Traverse 4',t:'piece',none:1});
   F.push({k:'dia',l:'Diamètre de la corde (mm)',t:'num'});return F.filter(Boolean)},
  handles:V=>{const A=P_(V.a),B=P_(V.b);if(!A||!B||A===B)return[];const J=phJunction(A,B),q=V.sec||J.best,da=q[0]=='+'?1:-1,db=q[1]=='+'?1:-1,mA=J.la(q),mB=J.lb(q),dA=Math.min(V.l1>0?V.l1:mA,mA),dB=Math.min(V.eb>0?V.eb:mB,mB),
    end=(ax,t0,dir,k,d,m)=>({p0:ax.p0,dir:ax.u,k,t:()=>t0+dir*(V[k]>0?Math.min(V[k],m):m),toVal:t=>Math.max(20,dir*(t-t0)),min:dir>0?t0+20:0,max:dir>0?ax.L:t0-20,snap:10}),
    cyc=['++','+-','-+','--'],ra=rad(A),rb_=rad(B),cor=Q=>{const s1=Q[0]=='+'?1:-1,s2=Q[1]=='+'?1:-1,k=Math.max(30,Math.min(J.la(Q),J.lb(Q))*.35);return add(add(J.J,mul(J.a.u,s1*k)),mul(J.b.u,s2*k))},cur=V.sec||J.best,nz=(()=>{let n=cr(J.a.u,J.b.u);return len(n)<.05?[0,0,1]:nrm(n)})(),pts=cyc.map(cor);
    return[end(J.a,J.tA,da,'l1',dA,mA),end(J.b,J.tB,db,'eb',dB,mB),{quad:true,p0:pts[cyc.indexOf(cur)],dir:[0,0,1],nz,pts,cur:cyc.indexOf(cur),k:'sec',t:()=>0,toVal:()=>V.sec,label:()=>'Angle '+(cyc.indexOf(cur)+1)+' (glissez)',set:i=>{V.sec=cyc[i];V.l1=0;V.eb=0}}]},

  preview:V=>{const pl=phPlan(V),items=pl.pieces.map(o=>({g:geo(o),pos:o.pos,rot:o.rot,color:o.color}));items.push({tg:phGeo({p:{segs:pl.segs,d:Math.max(1,V.dia)}}),pos:[0,0,0],rot:[0,0,0],color:'#cfc8b8'});return{items,warn:[...pl.info,...pl.warn],view:bestView(pl.pieces.slice(0,2),pl.segs.length?mul(add(pl.segs[0][0],pl.segs[pl.segs.length-1][1]),.5):[0,0,0],Math.max(400,Math.max(...pl.pieces.map(p=>axisOf(p).L))*.7))}},
  schema:V=>SV(`<path d="M160 20L60 130M160 20L260 130" ${OR}/>${[0,1,2,3,4,5,6,7].map(i=>`<line x1="${160-i*14.3}" y1="${20+i*15.7}" x2="${160+(7-i)*14.3}" y2="${20+(7-i)*15.7+0}" stroke="currentColor" stroke-width=".9"/>`).join('')}${RB(160,16,'A')}${TXT(160,146,'les cordes partent de l’intersection')}`),
  apply:V=>{const pl=phPlan(V);const par=pl.pieces[0].par;if(edit&&edit.p.src&&edit.p.src.cav&&asms[edit.p.src.cav])delAsm(edit.p.src.cav,true);let ca=0;const src={t:'ph',V:{...V},cav:0};let o;if(edit){edit.p.segs=pl.segs;edit.p.d=Math.max(1,V.dia);edit.p.src=src;mk(edit);o=edit}else o=addObj('ph',{segs:pl.segs,d:Math.max(1,V.dia),src},null,'PH décoratif','#cfc8b8',[0,0,0],[0,0,0],par);let nc=0;if(V.cav){ca=newAsm('PH',par).id;src.cav=ca;nc=mkCavPH(pl,V,ca)}
  const jid=(edit&&edit.p.src&&edit.p.src.jid)||++JID;src.jid=jid;objs.forEach(x=>{if(x.lk&&x.lk.includes(jid)&&!pl.pieces.includes(x)&&x!==o&&!(x.par==ca&&ca))x.lk=x.lk.filter(j=>j!=jid)});[o,...pl.pieces,...(ca?piecesOf(ca):[])].forEach(x=>{x.lk=x.lk||[];if(!x.lk.includes(jid))x.lk.push(jid)});touch();msg(`PH ${edit?'modifié':'créé'} : ${pl.segs.length} cordes${nc?', '+nc+' clous cavaliers':''}, ≈ ${fr(Math.round(phLen(o)/10)/100)} m de corde.`+(pl.warn.length?' ⚠ '+pl.warn[0]:''),7000)}})}
/* ----- Équerre : contrefiche entre deux pièces (perpendiculaires ou non) ----- */
function equerrePlan(V){const A=P_(V.a),B=P_(V.b);if(!A||!B||A===B)throw new Error('Choisissez deux pièces différentes.');const a=axisOf(A),b=axisOf(B),big=1e5;
 if(len(cr(a.u,b.u))<.1)throw new Error('Les deux pièces sont parallèles : pas d’équerre possible.');
 const[pa,pb]=segClose(add(a.p0,mul(a.u,-big)),add(a.p1,mul(a.u,big)),add(b.p0,mul(b.u,-big)),add(b.p1,mul(b.u,big))),C=mul(add(pa,pb),.5);
 const far=(ax)=>{const d0=len(sub(ax.p0,C)),d1=len(sub(ax.p1,C));return d1>=d0?nrm(sub(ax.p1,ax.p0)):nrm(sub(ax.p0,ax.p1))},ua=far(a),ub=far(b);
 let n=nrm(cr(ua,ub));if(n[2]>.3||(Math.abs(n[2])<=.3&&n[1]>0))n=mul(n,-1);if(V.side=='haut')n=mul(n,-1);
 const rP=Math.max(rad(A),rad(B)),mode=V.mode,rb=V.d/2,off=mode=='demi'?rP:mode=='plein'?rP+rb:rP+rb*.4;
 let PA0=add(add(C,mul(ua,V.dist)),mul(n,off)),PB0=add(add(C,mul(ub,V.dist2||V.dist)),mul(n,off)),planEnds=null;
 if(mode=='incruste'){/* incrustée : l'équerre arrive au milieu de chaque pièce, logée dans une encoche à son angle ; elle ne dépasse pas */
  PA0=add(C,mul(ua,V.dist));PB0=add(C,mul(ub,V.dist2||V.dist));planEnds={ea:0,eb:0}}
 const dv=nrm(sub(PB0,PA0)),exA=rP/Math.max(.35,Math.sqrt(Math.max(0,1-dot(dv,ua)**2)))+15,exB=rP/Math.max(.35,Math.sqrt(Math.max(0,1-dot(dv,ub)**2)))+15,PA=planEnds?add(PA0,mul(dv,planEnds.ea)):sub(PA0,mul(dv,exA)),PB=planEnds?add(PB0,mul(dv,planEnds.eb)):add(PB0,mul(dv,exB)),v=sub(PB,PA),ops=mode=='demi'?[]:mode=='incruste'?[[A,PA,dv,rad(A)],[B,PB,mul(dv,-1),rad(B)]].map(([p,P0,u,rp])=>{const s=Math.max(.3,Math.sqrt(Math.max(0,1-dot(u,axisOf(p).u)**2)));return{o:p,op:{k:'hole',o:w2l(p,P0),u:dw2l(p,u),s0:-1,s1:rp/s+rb+10,r:rb+PREF.jeu/2,lab:'Encoche de l’équerre Ø'+V.d+' (jusqu’au milieu, à '+Math.round(Math.acos(Math.min(1,Math.abs(dot(u,axisOf(p).u))))/D)+'°)'}}}):[A,B].map(p=>({o:p,op:{k:'hole',o:w2l(p,PA),u:dw2l(p,dv),s0:-1e3,s1:len(v)+1e3,r:rb+PREF.jeu/2,lab:'Encoche de l’équerre Ø'+V.d}}));
 return{A,B,PA,PB,L:len(v),n,off,C,rb,ua,ub,ops,ma:Math.max(len(sub(a.p0,C)),len(sub(a.p1,C))),mb:Math.max(len(sub(b.p0,C)),len(sub(b.p1,C))),na:Math.min(len(sub(a.p0,C)),len(sub(a.p1,C))),nb:Math.min(len(sub(b.p0,C)),len(sub(b.p1,C)))}}
function equerreMake(V){const pl=equerrePlan(V),{A,B}=pl;let o=mkObj('trav',{d:V.d,L:pl.L},null,'Équerre','#d2ab76',pl.PA,eul(sub(pl.PB,pl.PA)),A.par);
 if(V.mode=='demi'){const dl=dw2l(o,pl.n),[e1,e2]=bas([0,0,1]),th=Math.atan2(dot(dl,e2),dot(dl,e1))/D,res=fendre(o,{mode:'demi',start:th-90,gap:0});o=res[0];res.slice(1).forEach(x=>rmObjs([x]));o.name='Équerre (demi-rondin)'}
 else pl.ops.forEach(e=>{e.o.ops.push(e.op);refresh(e.o)});
 const dvv=nrm(sub(pl.PB,pl.PA)),inc=V.mode=='incruste',pA=inc?{pos:add(pl.PA,mul(dvv,rad(A)*.5))}:{},pB=inc?{pos:sub(pl.PB,mul(dvv,rad(B)*.5))}:{};try{applyPlan(planCheville([A,o],{d:V.pd,axis:'auto',lap:true,...pA}));applyPlan(planCheville([B,o],{d:V.pd,axis:'auto',lap:true,...pB}))}catch(e){msg('Équerre posée ; chevilles non créées : '+e.message,6000)}
 return o}
function equerreWin(mode0){const W=objs.filter(isWood);if(W.length<2)return msg('Il faut deux pièces.');const S=sel.filter(isWood);
 opWin({title:'Équerre entre deux pièces',intro:'Une contrefiche relie les deux pièces, qu’elles soient perpendiculaires ou non. Elle se place en dessous, encochée et chevillée dans chacune, ou en demi-rondin (face plate contre les pièces).',ok:'Créer l’équerre',delay:250,
  init:{a:(S[0]||W[0]).id,b:(S[1]||W.find(o=>o!==(S[0]||W[0]))).id,mode:mode0||'demi',side:'bas',dist:400,dist2:0,d:60,pd:16},
  fields:V=>[{k:'a',l:'Pièce 1',t:'piece'},{k:'b',l:'Pièce 2',t:'piece'},{k:'mode',l:'Type d’équerre',t:'sel',rb:1,o:[['demi','Rondin fendu (demi-rondin), tangent aux pièces et chevillé'],['plein','Rondin entier tangent aux pièces, chevillé'],['incruste','Rondin incrusté : logé dans une encoche jusqu’au milieu de chaque pièce, ne dépasse pas']]},{k:'side',l:'Côté de l’équerre',t:'sel',o:[['bas','Dessous (ou côté arrière)'],['haut','Dessus (ou côté avant)']]},{k:'dist',r:'A',l:'Distance sur la pièce 1 depuis le centre du croisement (mm), négatif = de l’autre côté',t:'num',h:'Glissez la poignée de part et d’autre du point de croisement pour placer l’équerre là où vous voulez.'},{k:'dist2',r:'B',l:'Distance sur la pièce 2 depuis le centre (mm), négatif = de l’autre côté, 0 = identique',t:'num'},{k:'d',l:'Diamètre de l’équerre (mm)',t:'num'},{k:'pd',l:'Diamètre des chevilles (mm)',t:'num'}],
  handles:V=>{try{const pl=equerrePlan({...V,dist2:V.dist2||V.dist});return[{p0:pl.C,dir:pl.ua,k:'dist',t:()=>V.dist,toVal:t=>t,min:-pl.na,max:pl.ma,snap:10},{p0:pl.C,dir:pl.ub,k:'dist2',t:()=>V.dist2||V.dist,toVal:t=>t,min:-pl.nb,max:pl.mb,snap:10}]}catch(e){return[]}},
  preview:V=>{const w={...V,dist2:V.dist2||V.dist},pl=equerrePlan(w),items=[pl.A,pl.B].map(o=>({g:geo(tmpWith(o,pl.ops.filter(e=>e.o===o).map(e=>e.op))),pos:o.pos,rot:o.rot,color:o.color}));{const rot=eul(sub(pl.PB,pl.PA)),p={d:V.d,L:pl.L};let g=build({type:'trav',p});if(V.mode=='demi'){const t={id:-1,type:'trav',p,g,pos:pl.PA,rot,ops:[],name:'x',par:0,color:'#d2ab76',mat:''},dl=dw2l(t,pl.n),[e1,e2]=bas([0,0,1]),th=Math.atan2(dot(dl,e2),dot(dl,e1))/D;try{g=planFendre(t,{mode:'demi',start:th-90,gap:0}).parts[0].g}catch(e){}}items.push({g,pos:pl.PA,rot,color:'#d2ab76'})}const aa=Math.acos(Math.max(-1,Math.min(1,dot(pl.ua,pl.ub))))/D;return{items,extra:{labels:[{p:add(pl.C,mul(pl.ua,(V.dist)/2)),t:sm(V.dist)},{p:add(pl.C,mul(pl.ub,(V.dist2||V.dist)/2)),t:sm(V.dist2||V.dist)}]},warn:[`Équerre de ${sm(pl.L)} de long, angle entre les pièces ${Math.round(aa)}°`,'Dépassement limité à 2 cm de chaque côté (recoupez dans l’axe si besoin).'],view:{dir:add(mul(pl.n,-1),[.3,-.5,.4]),center:pl.C,radius:Math.max(300,V.dist*1.4)}}},
  schema:V=>SV(`<rect x="20" y="30" width="200" height="22" ${WD}/><rect x="20" y="30" width="22" height="110" ${WD}/><path d="M42 120L130 52" stroke="#8a5a2b" stroke-width="10" stroke-linecap="round"/>${DIMV(70,52,120,'','')}${DIMH(42,130,150,'longueur','A')}${TXT(200,100,'chevillée dans chaque pièce')}`),
  apply:V=>{const o=equerreMake({...V,dist2:V.dist2||V.dist});select([o]);msg('Équerre créée.')}})}
/* ----- Filet de ficelle tendu entre deux supports (remplace ou complète le clayonnage) ----- */
/* maillage 2D dans le rectangle [0,zl]×[0,gap] (x le long des supports, y entre eux) : jamais au-delà du bord */
function meshSegs(zl,gap,p,pat){const S=[],n=Math.max(1,Math.round(zl/p)),m=Math.max(1,Math.round(gap/p)),px=zl/n,py=gap/m;
 if(pat!='losange'){for(let i=0;i<=n;i++)S.push([[i*px,0],[i*px,gap]])}
 if(pat=='carre'||pat=='carrediag'){for(let j=0;j<=m;j++)S.push([[0,j*py],[zl,j*py]])}
 if(pat=='losange'||pat=='carrediag'){const st=pat=='losange'?p:2*p;
  for(let c=-gap;c<=zl+1e-6;c+=st){const x0=Math.max(0,c),x1=Math.min(zl,c+gap);if(x1-x0>1)S.push([[x0,x0-c],[x1,x1-c]])}
  for(let c=0;c<=zl+gap+1e-6;c+=st){const x0=Math.max(0,c-gap),x1=Math.min(zl,c);if(x1-x0>1)S.push([[x0,c-x0],[x1,c-x1]])}}
 return S}
function netSegsOn(pa,pb,t0,zl,gap,V){const q=(x,y)=>{const A=pa(t0+x),B=pb(t0+x);return add(A,mul(sub(B,A),y/gap))};return meshSegs(zl,gap,V.pitch,V.pat).map(([a,b])=>[q(...a),q(...b)])}
function netPlan(V){const A=P_(V.a),B=P_(V.b);if(!A||!B||A===B)throw new Error('Choisissez deux supports différents.');const a=axisOf(A),b=axisOf(B);if(Math.abs(dot(a.u,b.u))<.9)throw new Error('Les deux supports doivent être à peu près parallèles.');
 const la=a.L,t0=Math.max(0,V.s||0),zl=(V.l>0?Math.min(V.l,la):la)-t0,pb=t=>{const u=dot(b.u,a.u)>0?b.u:mul(b.u,-1),q0=dot(b.u,a.u)>0?b.p0:b.p1;return add(q0,mul(u,t))},pa=t=>add(a.p0,mul(a.u,t)),gap=len(sub(pb(0),pa(0)));
 let W={...V};if(!(W.pitch>0))W.pitch=Math.max(20,zl/Math.max(2,Math.round(zl/100)));if(W.pitch<15)throw new Error('Maille trop petite (15 mm minimum).');if(zl/W.pitch>200)throw new Error('Trop de mailles : augmentez l’écart.');
 const segs=netSegsOn(pa,pb,t0,zl,gap,W);if(!segs.length)throw new Error('Aucune ficelle.');return{segs,A,B}}
function netWin(edit){const W=objs.filter(isWood);if(W.length<2)return msg('Il faut deux supports.');const E0=edit&&edit.p.src&&edit.p.src.V;const S=sel.filter(isWood);
 opWin({title:edit?'Modifier le filet':'Filet de ficelle',intro:'Ficelle tendue entre deux supports parallèles (le filet réel se tresse à la main : ceci est un modèle sommaire). Il peut remplacer le clayonnage ou s’y ajouter.',ok:edit?'Enregistrer':'Créer le filet',delay:250,
  init:E0?{...E0}:{a:(S[0]||W[0]).id,b:(S[1]||W.find(o=>o!==(S[0]||W[0]))).id,s:0,l:Math.round(axisOf(S[0]||W[0]).L),pitch:0,pat:'carre',dia:PREF.rope||2},
  fields:V=>[{k:'a',l:'Support 1',t:'piece'},{k:'b',l:'Support 2',t:'piece'},{k:'s',r:'A',l:'Début du filet depuis le bout (mm)',t:'num'},{k:'l',r:'B',l:'Fin du filet depuis le bout (mm)',t:'num'},{k:'pat',l:'Maille',t:'sel',o:[['carre','Rectangulaire (maille droite)'],['carrediag','Rectangulaire + diagonales'],['losange','En losanges'],['droit','Ficelles parallèles seulement']]},{k:'pitch',r:'C',l:'Écart entre ficelles (mm), 0 = automatique',t:'num'},{k:'dia',l:'Diamètre de la ficelle (mm)',t:'num'}].filter(Boolean),
  handles:V=>barHandles(P_(V.a),V,'s','l'),
  preview:V=>{const pl=netPlan(V),items=[pl.A,pl.B].map(o=>({g:geo(o),pos:o.pos,rot:o.rot,color:o.color}));items.push({tg:phGeo({p:{segs:pl.segs,d:Math.max(1,V.dia)}}),pos:[0,0,0],rot:[0,0,0],color:'#cfc8b8'});return{items,warn:[pl.segs.length+' ficelles, ≈ '+fr(Math.round(phLen({p:{segs:pl.segs}})/10)/100)+' m'],view:{dir:[.3,-.5,.8],center:mul(add(pl.segs[0][0],pl.segs[pl.segs.length-1][1]),.5),radius:Math.max(400,len(sub(pl.segs[0][0],pl.segs[0][1]))*1.5)}}},
  schema:V=>SV(`<rect x="20" y="20" width="280" height="12" ${WD}/><rect x="20" y="118" width="280" height="12" ${WD}/>${[0,1,2,3,4,5,6,7].map(i=>`<path d="M${40+i*32} 32L${72+i*32} 118M${72+i*32} 32L${40+i*32} 118" stroke="currentColor" stroke-width="1"/>`).join('')}${DIMH(40,72,75,'écart','C')}`),
  apply:V=>{const pl=netPlan(V);PREF.rope=V.dia;savePrefs();const src={t:'net',V:{...V}};if(edit){edit.p.segs=pl.segs;edit.p.d=Math.max(1,V.dia);edit.p.src=src;mk(edit);touch()}else addObj('ph',{segs:pl.segs,d:Math.max(1,V.dia),kind:'filet',src},null,'Filet de ficelle','#cfc8b8',[0,0,0],[0,0,0],pl.A.par);msg(edit?'Filet modifié.':'Filet créé : '+pl.segs.length+' ficelles.')}})}

/* ----- Plateaux : choix du type puis fenêtre dédiée ----- */
function plateauWin(){modal(`<h3>Plateau, claies, filet</h3><p class="mu">Sélectionnez d’abord <b>deux supports parallèles</b> (traverses), puis choisissez le type :</p><div class="cards"><button onclick="closeMd();clayWin()">${ic('clay',36)}Claies tressées<br><small>plan horizontal, incliné ou vertical</small></button><button onclick="closeMd();deckWin('claies')">${ic('plateau',36)}Claies droites<br><small>quart de bois, horizontal seulement</small></button><button onclick="closeMd();deckWin('planches')">${ic('split',36)}Planches<br><small>chevillées, horizontal seulement</small></button><button onclick="closeMd();netWin()">${ic('filet',36)}Filet de ficelle<br><small>horizontal, incliné ou vertical</small></button></div><div class="r" style="margin-top:10px"><button onclick="closeMd()">Annuler</button></div>`)}
function deckPlan(S,V){if(S.length!=2)throw new Error('Sélectionnez exactement deux supports parallèles.');const A=S.map(axisOf),a0=A[0].u;if(Math.abs(dot(A[0].u,A[1].u))<.97)throw new Error('Les supports doivent être parallèles.');
 let a=[a0[0],a0[1],0];const QH='Le quart de bois (claies droites, planches) ne se fait que sur un plan horizontal. Pour un plan incliné ou vertical, utilisez des claies tressées ou un filet.';if(len(a)<.97)throw new Error(QH);a=nrm(a);const c=A.map(x=>mul(add(x.p0,x.p1),.5)),zr=(c[0][2]+c[1][2])/2;if(Math.abs(c[0][2]-c[1][2])>30)throw new Error(QH);let lo=-1e18,hi=1e18;S.forEach(s=>{const[l,u]=ext(s,a);lo=Math.max(lo,l);hi=Math.min(hi,u)});
 const xp=cr(a,[0,0,1]);let i0=dot(c[0],xp)<=dot(c[1],xp)?0:1,i1=1-i0;const P0=c[i0],P1=c[i1],span=dot(sub(P1,P0),xp),k0=dot(P0,a),R0=add(P0,mul(a,lo-k0));
 if(span<80)throw new Error('Les supports sont trop proches.');const from=Math.max(0,V.from||0),end=Math.min(hi-lo,V.end>0?V.end:hi-lo),zone=end-from;if(zone<20)throw new Error('Zone trop courte.');
 const els=[];if(V.mode=='claies'){const d=V.d,n=Math.floor((zone+V.gap)/(d+V.gap));if(d<8||d>30)throw new Error('Diamètre des claies : de 8 à 30 mm.');if(n<1)throw new Error('Pas de place pour une claie.');for(let i=0;i<n;i++){const t=from+d/2+i*(d+V.gap);els.push({kind:'claie',d,t,p:add(add(R0,mul(a,t)),[0,0,d/2+(zr-R0[2])]),L:span})}}
 else{const w=V.w,n=Math.floor((zone+V.gap)/(w+V.gap));if(V.ep<8)throw new Error('Épaisseur minimale : 8 mm.');if(n<1)throw new Error('Pas de place pour une planche.');for(let i=0;i<n;i++){const t=from+i*(w+V.gap);els.push({kind:'planche',t,w,ep:V.ep,p:add(add(R0,mul(a,t)),[0,0,zr-R0[2]]),L:span})}}
 const quart=V.quart?S.map((rl,j)=>{const ax=A[j],b0=nrm(sub([0,0,1],mul(ax.u,ax.u[2]))),b1=cr(ax.u,b0),din=j==i0?xp:mul(xp,-1),Rs=add(P0,mul(a,from)),Re=add(P0,mul(a,end)),s1=dot(sub(add(Rs,sub(c[j],P0)),ax.p0),ax.u),s2=dot(sub(add(Re,sub(c[j],P0)),ax.p0),ax.u),pos=dot(b1,din)>0?0:270;const st=Math.max(0,Math.min(s1,s2));return planQuart(rl,{start:st,len:Math.max(10,Math.min(Math.abs(s2-s1),ax.L-st-1)),pos,mode:'quart'})}):[];
 return{els,a,xp,span,quart,S,zr,R0,ang:Math.atan2(xp[1],xp[0])/D,P0}}
function deckMake(S,V){const pl=deckPlan(S,V),g=newAsm(V.mode=='claies'?'Plateau de claies droites':'Plateau de planches',S[0].par||0);pl.quart.forEach(q=>applyPlan(q));const made=[];
 pl.els.forEach((e,i)=>{if(e.kind=='claie')made.push(mkObj('trav',{d:e.d,L:e.L},null,'Claie '+(i+1),'#b5894f',e.p,eul(pl.xp),g.id));else made.push(mkObj('box',{l:e.L,w:e.w,h:e.ep,ch:0,fi:0},null,'Planche '+(i+1)+' (ép. '+e.ep+' mm)',WC[i%4],e.p,[0,0,pl.ang],g.id))});
 if(V.mode=='planches'&&V.peg)made.forEach(pc=>S.forEach((rl,j)=>{try{const ax=axisOf(rl),c=mul(add(ax.p0,ax.p1),.5),din=j==0?pl.xp:mul(pl.xp,-1),t=dot(sub(bounds([pc])[0],ax.p0),ax.u)*0,mid=mul(add(bounds([pc])[0],bounds([pc])[1]),.5),q=add(add(c,mul(pl.a,dot(sub(mid,c),pl.a))),mul(din,-0.35*rad(rl)));applyPlan(planCheville([pc,rl],{d:V.pd,axis:'Z',pos:[q[0],q[1],pl.zr],lap:true}))}catch(e){}}));
 select([],g.id);return made.length}
function deckWin(mode){const S=sel.filter(isWood);if(S.length!=2)return msg('Sélectionnez d’abord les deux traverses qui portent le plateau.');
 opWin({title:mode=='claies'?'Claies droites dans des quarts de bois':'Plateau de planches',intro:mode=='claies'?'Les claies sont posées en travers dans un quart de bois taillé dans chaque traverse.':'Planches (par exemple fendues dans des rondins) posées dans les quarts de bois ; on peut les cheviller dans chaque traverse.',ok:'Créer le plateau',delay:300,
  init:{mode,d:20,gap:mode=='claies'?0:3,w:100,ep:25,from:0,end:0,quart:true,peg:mode=='planches',pd:10},
  fields:V=>[mode=='claies'?{k:'d',l:'Diamètre des claies (mm)',t:'num'}:{k:'ep',l:'Épaisseur des planches (mm)',t:'num'},mode=='planches'?{k:'w',l:'Largeur des planches (mm)',t:'num'}:null,{k:'gap',l:'Jeu entre éléments (mm)',t:'num'},{k:'from',r:'A',l:'Début après l’extrémité (mm)',t:'num'},{k:'end',r:'B',l:'Fin depuis l’extrémité (mm), 0 = jusqu’au bout',t:'num'},{k:'quart',l:'Tailler les quarts de bois dans les traverses',t:'chk'},mode=='planches'?{k:'peg',l:'Cheviller chaque planche dans les traverses',t:'chk',rb:1}:null,mode=='planches'&&V.peg?{k:'pd',l:'Diamètre des chevilles (mm)',t:'num'}:null].filter(Boolean),
  handles:V=>{try{const pl=deckPlan(S,V),lo=pl.R0,hi=Math.min(1e9,0);const ax=pl.a;return[{p0:pl.R0,dir:ax,k:'from',t:()=>V.from||0,toVal:t=>t,min:0,max:5000,snap:10},{p0:pl.R0,dir:ax,k:'end',t:()=>V.end>0?V.end:pl.els.length?pl.els[pl.els.length-1].t+(pl.els[pl.els.length-1].d||pl.els[pl.els.length-1].w):0,toVal:t=>t,min:(V.from||0)+20,max:5000,snap:10}]}catch(e){return[]}},
  preview:V=>{const pl=deckPlan(S,V),items=S.map((o,j)=>({g:geo(tmpWith(o,pl.quart.flatMap(q=>q.ops.filter(e=>e.o===o).map(e=>e.op)))),pos:o.pos,rot:o.rot,color:o.color}));
   pl.els.slice(0,150).forEach((e,i)=>items.push(e.kind=='claie'?{g:build({type:'trav',p:{d:e.d,L:e.L}}),pos:e.p,rot:eul(pl.xp),color:'#b5894f'}:{g:build({type:'box',p:{l:e.L,w:e.w,h:e.ep,ch:0,fi:0}}),pos:e.p,rot:[0,0,pl.ang],color:WC[i%4]}));
   return{items,warn:[pl.els.length+(mode=='claies'?' claies':' planches')],view:{dir:[.5,-.8,.6],center:add(pl.P0,add(mul(pl.xp,pl.span/2),[0,0,0])),radius:Math.max(500,pl.span*1.5)}}},
  schema:V=>SV(`<rect x="20" y="30" width="280" height="14" ${WD}/><rect x="20" y="106" width="280" height="14" ${WD}/>${[0,1,2,3,4,5,6,7,8].map(i=>`<rect x="${30+i*30}" y="44" width="${mode=='claies'?14:26}" height="62" fill="#b5894f" fill-opacity=".7"/>`).join('')}${DIMH(30,90,140,'début → fin','A')}${TXT(160,22,'quart de bois dans chaque traverse')}`),
  apply:V=>{const n=deckMake(S,V);msg(n+(mode=='claies'?' claies':' planches')+' créées.')}})}

const IC={
 cH:'<path d="M3 12h18"/>',cV:'<path d="M12 3v18"/>',cpar:'<path d="M6 20L12 4M12 20l6-16"/>',cperp:'<path d="M5 19h14M12 19V5"/>',ceq:'<path d="M5 9h14M5 15h14"/>',ccoin:'<circle cx="12" cy="12" r="3" fill="currentColor"/><circle cx="12" cy="12" r="8"/>',cax:'<path d="M3 12h18M12 8v8"/>',cay:'<path d="M12 3v18M8 12h8"/>',clock:'<rect x="6" y="11" width="12" height="9" rx="1"/><path d="M8 11V8a4 4 0 0 1 8 0v3"/>',cpol:'<path d="M3 18L21 6"/><circle cx="12" cy="12" r="2.5" fill="currentColor"/>',
 ddist:'<path d="M4 12h16M4 8v8M20 8v8"/>',dang:'<path d="M4 20h16M4 20L16 6M10 20a6 6 0 0 0-2-4"/>',drad:'<circle cx="12" cy="12" r="8"/><path d="M12 12l6-6"/>',ortho:'<path d="M5 8l7-4 7 4v8l-7 4-7-4zM12 12v8M5 8l7 4 7-4"/>',ax:'<path d="M5 19L19 5M14 5h5v5"/>',axe:'<path d="M3 12h4M9 12h1M12 12h4M18 12h1M21 12h0"/><path d="M12 4v16" opacity=".4"/>',dm3:'<path d="M4 7v10M20 7v10M4 12h16M4 12l3-2M4 12l3 2M20 12l-3-2M20 12l-3 2"/>',
 txt:'<path d="M5 5h14M12 5v14M9 19h6"/>',hid:'<path d="M3 12h4M10 12h4M17 12h4"/>',step:'<path d="M4 20h4v-4h4v-4h4V8h4"/>',stepr:'<path d="M12 12V4M12 12l6 3"/><circle cx="12" cy="12" r="9"/>',
 poly:'<path d="M5 18l3-12 9 3 3 9z"/>',rect:'<rect x="4" y="6" width="16" height="12"/>',circ:'<circle cx="12" cy="12" r="8"/>',
 ext:'<path d="M5 20h10v-4H5zM5 16l4-3h10l-4 3M19 13v-3M16 10l3-4 3 4"/>',rev:'<path d="M12 3v18M12 6c7 0 7 12 0 12"/>',chf:'<path d="M4 20V10l6-6h10v16z"/>',cng:'<path d="M4 20V10a6 6 0 0 1 6-6h10v16z"/>',
 rond:'<ellipse cx="6" cy="12" rx="3" ry="6"/><path d="M6 6h13a3 6 0 0 1 0 12H6"/>',demi:'<path d="M4 11a8 8 0 0 0 16 0z"/>',poutre:'<path d="M3 9l4-3h14v6l-4 3H3z"/><path d="M3 9h14l4-3M17 9v6"/>',planche:'<path d="M3 12l4-3h14l-4 3z"/><path d="M3 12v3h14v-3M17 15l4-3V9"/>',chev:'<rect x="8" y="3" width="8" height="18"/>',
 milb:'<path d="M3 8h12v4H9v4H3zM21 16H9v-4"/>',tenon:'<path d="M3 8h10v8H3zM13 10h8v4h-8z"/>',coupe:'<path d="M4 4l16 16M4 20L20 4"/>',dia:'<circle cx="12" cy="12" r="7"/><path d="M4 20L20 4"/>',
 sph:'<circle cx="12" cy="12" r="8"/><ellipse cx="12" cy="12" rx="8" ry="3"/>',
 cone:'<ellipse cx="12" cy="19" rx="7" ry="2.5"/><path d="M5 19L10 4h4l5 15"/>',
 tore:'<ellipse cx="12" cy="12" rx="9" ry="5"/><ellipse cx="12" cy="12" rx="3.5" ry="1.6"/>',
 tcar:'<rect x="5" y="5" width="14" height="14" rx="1"/><rect x="9" y="9" width="6" height="6"/>',
 corn:'<path d="M6 4v16h13v-4H10V4z"/>',
 U:'<path d="M5 4h4v11h6V4h4v16H5z"/>',
 I:'<path d="M5 4h14v4h-5v8h5v4H5v-4h5V8H5z"/>',
 move:'<path d="M12 3v18M3 12h18M12 3l-3 3M12 3l3 3M12 21l-3-3M12 21l3-3M3 12l3-3M3 12l3 3M21 12l-3-3M21 12l-3 3"/>',
 rot:'<path d="M20 12a8 8 0 1 1-3-6.2M20 4v5h-5"/>',
 cur:'<path d="M5 3l14 8-6 2-2 6z"/>',
 dh:'<path d="M4 7v10M20 7v10M4 12h16M4 12l3-2M4 12l3 2M20 12l-3-2M20 12l-3 2"/>',
 dv:'<path d="M7 4h10M7 20h10M12 4v16M12 4l-2 3M12 4l2 3M12 20l-2-3M12 20l2-3"/>',
 dd:'<path d="M5 19L19 5M4 14l6 6M14 4l6 6M5 19l1-4M5 19l4-1M19 5l-1 4M19 5l-4 1"/>',
 box:'<path d="M12 3l8 4v10l-8 4-8-4V7z"/><path d="M4 7l8 4 8-4M12 11v10"/>',
 cyl:'<ellipse cx="12" cy="6" rx="7" ry="3"/><path d="M5 6v12c0 1.7 3.1 3 7 3s7-1.3 7-3V6"/>',
 tube:'<ellipse cx="12" cy="6" rx="7" ry="3"/><ellipse cx="12" cy="6" rx="3.5" ry="1.5"/><path d="M5 6v12c0 1.7 3.1 3 7 3s7-1.3 7-3V6"/>',
 mesh:'<path d="M12 3l8 5v8l-8 5-8-5V8z"/><path d="M8 10l4 2 4-2"/>',
 union:'<circle cx="9" cy="12" r="6" fill="currentColor" fill-opacity=".25"/><circle cx="15" cy="12" r="6" fill="currentColor" fill-opacity=".25"/>',
 sub:'<circle cx="9" cy="12" r="6" fill="currentColor" fill-opacity=".3"/><circle cx="15" cy="12" r="6" stroke-dasharray="2 2"/>',
 inter:'<circle cx="9" cy="12" r="6"/><circle cx="15" cy="12" r="6"/><path d="M12 7.2a6 6 0 0 1 0 9.6a6 6 0 0 1 0-9.6z" fill="currentColor"/>',
 dup:'<rect x="8" y="8" width="12" height="12" rx="2"/><path d="M16 8V6a2 2 0 0 0-2-2H6a2 2 0 0 0-2 2v8a2 2 0 0 0 2 2h2"/>',
 del:'<path d="M4 7h16M10 11v6M14 11v6M6 7l1 13h10l1-13M9 7V4h6v3"/>',
 snap:'<path d="M4 4h16v16H4zM4 12h16M12 4v16"/>',
 fit:'<path d="M4 9V4h5M15 4h5v5M20 15v5h-5M9 20H4v-5"/>',
 view:'<path d="M12 3l8 4v10l-8 4-8-4V7z"/><path d="M4 7l8 4 8-4" opacity=".5"/>',
 plan:'<rect x="3" y="4" width="18" height="16" rx="1"/><rect x="6" y="7" width="6" height="5"/><path d="M6 15h6M15 7v8M15 17h3"/>',
 svg:'<path d="M12 4v11M7 11l5 5 5-5M5 20h14"/>',
 print:'<path d="M7 9V4h10v5M7 17H5a1 1 0 0 1-1-1v-5a2 2 0 0 1 2-2h12a2 2 0 0 1 2 2v5a1 1 0 0 1-1 1h-2"/><rect x="7" y="14" width="10" height="6"/>',
 perche:'<path d="M10 3h4v18h-4z"/><path d="M10 8h4M10 15h4" opacity=".5"/>',percheH:'<path d="M3 10h18v4H3z"/><path d="M8 10v4M15 10v4" opacity=".5"/>',piquet:'<path d="M10 3h4v13l-2 5-2-5z"/><path d="M4 14h16" stroke-dasharray="2 2"/>',
 tfeu:'<path d="M3 10h18M5 10v10M19 10v10M5 15h14"/><path d="M12 8c-2-2 0-4 0-5 2 2 3 3 0 5z" fill="currentColor"/>',portique:'<path d="M5 3v18M19 3v18M3 6h18M3 10h18"/>',banc:'<path d="M3 11h18v3H3zM6 14v6M18 14v6"/>',trepied:'<path d="M12 3L4 21M12 3l8 18M12 3v18"/><path d="M9 6h6" stroke-width="2.4"/>',etag:'<path d="M5 3v18M19 3v18M5 8h14M5 13h14M5 18h14"/>',
 lash:'<path d="M4 12h16M12 4v16"/><path d="M8 8l8 8M16 8l-8 8" stroke="#e08a00" stroke-width="2.2"/>',bom:'<path d="M8 6h12M8 12h12M8 18h12"/><circle cx="4" cy="6" r="1"/><circle cx="4" cy="12" r="1"/><circle cx="4" cy="18" r="1"/>',
 undo:'<path d="M9 14L4 9l5-5"/><path d="M4 9h10a6 6 0 0 1 0 12h-3"/>',redo:'<path d="M15 14l5-5-5-5"/><path d="M20 9H10a6 6 0 0 0 0 12h3"/>',save:'<path d="M5 3h11l4 4v14H4V3z"/><path d="M8 3v5h8V3M8 21v-7h8v7"/>',open:'<path d="M3 7V5h7l2 2h9v12H3z"/><path d="M12 10v6M9 13l3-3 3 3"/>',new:'<path d="M6 3h9l4 4v14H6z"/><path d="M12 10v7M8.5 13.5h7"/>',help:'<circle cx="12" cy="12" r="9"/><path d="M9.5 9.5a2.5 2.5 0 1 1 3.5 2.3c-.7.3-1 .9-1 1.7M12 17h0"/>',expert:'<circle cx="12" cy="12" r="3"/><path d="M12 2v3M12 19v3M2 12h3M19 12h3M5 5l2 2M17 17l2 2M5 19l2-2M17 7l2-2"/>',ground:'<path d="M12 3v11M8 10l4 4 4-4M3 19h18"/><path d="M5 22l2-3M10 22l2-3M15 22l2-3" opacity=".6"/>',grp:'<rect x="3" y="3" width="8" height="8"/><rect x="13" y="13" width="8" height="8"/><path d="M11 7h4v6M13 17H9v-6" opacity=".6"/>',
 x3d:'<path d="M12 3l7 3.5v7M12 3L5 6.5v11L12 21l3-1.5"/><path d="M18 15v6M15 18l3 3 3-3"/>'};

/* =====================  Interface : ruban, arborescence, panneaux, menus, dialogues  ===================== */
Object.assign(IC,{
 split:'<circle cx="7" cy="7" r="4"/><path d="M7 11v1"/><rect x="3" y="13" width="18" height="3.2" rx=".6"/><rect x="3" y="17.4" width="18" height="3.2" rx=".6"/><path d="M13 4l6 0M13 7l6 0" stroke-dasharray="1.5 1.5"/>',scie:'<path d="M3 9h9v6H3zM12 10.5h8v3h-8z"/><path d="M12 9v6" stroke-width="2.4"/>',hache:'<path d="M3 8h8v8H3zM11 8l4 3v2l-4 3M15 10.5h6v3h-6z"/>',plat:'<path d="M3 8h9v8H3zM12 9h9v6h-9z"/>',aronde:'<path d="M3 8h8v8H3zM11 10h3l3-3v10l-3-3h-3z"/>',
 coupe:'<path d="M4 20L20 4M4 4l16 16"/>',pointe:'<path d="M9 3h6v10l-3 8-3-8z"/>',asm:'<rect x="3" y="3" width="8" height="8"/><rect x="13" y="13" width="8" height="8"/><path d="M11 7h4v6M13 17H9v-6"/>',ungrp:'<rect x="3" y="3" width="8" height="8"/><rect x="13" y="13" width="8" height="8"/>',
 pdf:'<path d="M6 3h9l4 4v14H6z"/><path d="M9 14h6M9 17h4"/>',png:'<rect x="3" y="5" width="18" height="14" rx="1"/><circle cx="9" cy="10" r="1.6"/><path d="M4 18l5-5 4 4 3-3 4 4"/>',html:'<path d="M8 8l-5 4 5 4M16 8l5 4-5 4M14 5l-4 14"/>',json:'<path d="M9 4C6 4 7 9 4 12c3 3 2 8 5 8M15 4c3 0 2 5 5 8-3 3-2 8-5 8"/>',
 cam:'<rect x="3" y="7" width="18" height="12" rx="2"/><circle cx="12" cy="13" r="3.5"/><path d="M8 7l1-3h6l1 3"/>',nom:'<path d="M4 5h16v14H4zM4 10h16M10 5v14"/>',eye:'<path d="M2 12s4-7 10-7 10 7 10 7-4 7-10 7S2 12 2 12z"/><circle cx="12" cy="12" r="3"/>',grid:'<path d="M4 4h16v16H4zM4 9.3h16M4 14.6h16M9.3 4v16M14.6 4v16"/>',ai:'<path d="M12 3l1.8 5.2L19 10l-5.2 1.8L12 17l-1.8-5.2L5 10l5.2-1.8zM18 15l.8 2.2L21 18l-2.2.8L18 21l-.8-2.2L15 18l2.2-.8z"/>',
 fauteuil:'<path d="M6 11V5h3v6M15 11V5h3v6M5 11h14v4H5zM7 15v5M17 15v5M3 11v4"/>',tabouret:'<ellipse cx="12" cy="8" rx="7" ry="2.5"/><path d="M6 9l-2 11M18 9l2 11M12 10v10"/>',banc:'<path d="M3 11h18v3H3zM6 14v6M18 14v6"/>',echelle:'<path d="M7 3v18M17 3v18M7 7h10M7 11h10M7 15h10M7 19h10"/>',chevalet:'<path d="M4 20L12 6l8 14M4 6l8 14L20 6"/>',etabli:'<path d="M3 15l14-7M5 15l14-7M7 21l3-9M16 21l-2-9"/>',
 ph:'<path d="M3 3l6 18M21 3l-6 18"/><path d="M4.5 8L19.5 8M5.2 11L18.8 17M18.8 11L5.2 17M7 14.5h10" stroke-width="1.2"/>',det:'<circle cx="10" cy="10" r="6"/><path d="M15 15l6 6M10 7v6M7 10h6"/>',ang:'<path d="M4 20L20 20M4 20L16 6"/><path d="M11 20a7 7 0 0 0-2.4-5.3"/>',filet:'<path d="M3 5h18M3 19h18M6 5l6 14M12 5L6 19M12 5l6 14M18 5l-6 14"/>',equerre:'<path d="M4 4v16h16M4 12l8 8"/><path d="M4 12l8 8" stroke-width="3"/>',unl:'<path d="M10 14a4 4 0 0 0 6 0l3-3a4 4 0 0 0-6-6l-1 1M14 10a4 4 0 0 0-6 0l-3 3a4 4 0 0 0 6 6l1-1"/><path d="M4 4l16 16"/>',lnk:'<path d="M10 14a4 4 0 0 0 6 0l3-3a4 4 0 0 0-6-6l-1 1M14 10a4 4 0 0 0-6 0l-3 3a4 4 0 0 0 6 6l1-1"/>',plateau:'<path d="M3 9h18v3H3zM6 12v8M18 12v8"/><path d="M5 6h14" stroke-dasharray="2 2"/>',expert0:'<rect x="2" y="7" width="20" height="10" rx="5"/><circle cx="7.5" cy="12" r="2.6"/>',expert:'<rect x="2" y="7" width="20" height="10" rx="5"/><circle cx="16.5" cy="12" r="2.6" fill="currentColor"/>',milb:'<rect x="2" y="12" width="14" height="6"/><rect x="8" y="6" width="14" height="6"/><path d="M8 12h8" stroke-dasharray="2 1.5"/><path d="M12 20v1.5M5 20.5h14" opacity=".0"/>',gear:'<circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1-2.83 2.83l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-4 0v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1 0-4h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 2.83-2.83l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 4 0v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 0 4h-.09a1.65 1.65 0 0 0-1.51 1z"/>',quart:'<circle cx="12" cy="12" r="8"/><path d="M12 12h8V4a8 8 0 0 0-8 8z" fill="currentColor" fill-opacity=".25"/>',coll:'<circle cx="9" cy="12" r="6"/><circle cx="15" cy="12" r="6"/>',table:'<path d="M3 8h18M5 8l4 12M19 8l-4 12M9 14h6"/>',rep:'<rect x="3" y="8" width="5" height="8"/><rect x="10" y="8" width="5" height="8" stroke-dasharray="2 2"/><rect x="17" y="8" width="4" height="8" stroke-dasharray="2 2"/>',clay:'<path d="M3 15c3 0 3-6 6-6s3 6 6 6 3-6 6-6M3 19c3 0 3-6 6-6s3 6 6 6 3-6 6-6"/>',
 fichier:'<path d="M6 3h9l4 4v14H6z"/>',drive:'<path d="M8 4h8l5 9-4 7H7l-4-7zM8 4l5 9M16 4l-5 9M3 13h18"/>'});
const ic=(n,s=28)=>`<svg viewBox="0 0 24 24" width="${s}" height="${s}" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round">${IC[n]||IC.mesh}</svg>`;
const HAS_AI=()=>!!window.__ai;
/* ----- ruban : Fichier, Édition, puis par ordre d'importance ----- */
const TABS={
 'Fichier':[['Projet',[['table','Accueil',"tabClick('Accueil')"],['new','Nouveau','newProj()'],['open','Ouvrir','openDlg()'],['html','Enregistrer','saveProj()'],['json','Fichier .json','saveJSON()']]],['Exporter',[['pdf','PDF du plan','exPDF()'],['pdf','PDF vue 3D','exPDF3()'],['png','PNG vue 3D','exPNG3()'],['png','PNG du plan','exPNGplan()'],['svg','SVG du plan','dlSVG()'],['bom','Matériel CSV','dlBom()'],['print','Imprimer le plan','printAll()']]],['Application',[['gear','Paramètres','settingsDlg()'],['expert',()=>expert?'Passer en mode simple':'Passer en mode expert','toggleExpert()','expert'],['help','Aide','help()']]]],
 'Édition':[['Historique',[['undo','Annuler','undo()'],['redo','Rétablir','redo()']]],['Sélection',[['dup','Dupliquer','dup()'],['dup','Dupliquer sans opérations','dup(false)'],['rep','Répétition…','repWin()'],['del','Supprimer','delSel()'],['ground','Poser au sol','toGround()'],['cur','Tout sélectionner','selAll()']]],['Assemblage (arborescence)',[['asm','Grouper','groupSel()'],['ungrp','Dégrouper','ungroup()'],['move','Sortir du groupe','outOfGroup()']]],['Liaisons des pièces assemblées',[['unl','Détacher (déplacer seule)','unlinkSel(true)'],['lnk','Rattacher','unlinkSel(false)']]],['Contrôle',[['coll','Collisions','dCollisions()'],['bom','Liste des opérations','dOps()']]],['Déplacement',[['snap','Aimant','toggleSnap()','snap'],['step',()=>`Pas dépl. ${stepT} mm`,'cycT()'],['stepr',()=>`Pas rot. ${stepR}°`,'cycR()']]]],
 'Créer':[['Pièces',[['perche','Traverse',"addT('Z')"],['table','Modèles de référence',"tabClick('Bibliothèque de modèles')"],['asm','Modèles partagés',"tabClick('Modèles partagés')"]]],['Renforts',[['equerre','Équerre','equerreWin()','','equerre']]],['Plateaux et parois',[['plateau','Plateau, claies, filet','plateauWin()','','plateau']]],['Décoratif',[['ph','PH (cordes)','phWin()']]]],
 'Opérations':[['Façonner',[['split','Fendre en planches','fendreWin()'],['quart','Quart de bois','quartWin()'],['coupe','Couper','coupeWin()'],['pointe','Pointe','pointeWin()']]],['Assemblages',[['hache','Tenon','asmStart(\'hache\')','','tenon'],['milb','Mi-bois',"asmStart('mibois')"],['aronde','Queue d’aronde',"asmStart('aronde')",'','aronde'],['cheville','Chevilles',"asmStart('cheville')"],['lash','Brêlage (dernier recours)',"asmStart('lash')",'','lash']]],['*Booléens (expert)',[['union','Union',"bool('u')"],['sub','A − B',"bool('s')"],['inter','Intersection',"bool('i')"]]]],
 'Bibliothèque de modèles':[['Modèles',[['lib','Actualiser','libRefresh()']]]],
 'Modèles partagés':[['Modèles',[['lib','Actualiser','libRefresh()']]]],
 'Accueil':[['Démarrer',[['new','Nouveau projet','newProj()'],['open','Ouvrir','openDlg()']]]],
 'Nomenclature':[['Tableur',[['bom','Voir la liste','showBom()'],['json','Exporter CSV','dlBom()'],['dup','Copier','copyBom()']]]],
 'Mise en plan':[['Pages',[['new','Nouvelle page','addPage()'],['del','Supprimer la page','delPage()'],['print','Imprimer','printAll()']]],['Contenu',[['view','Ajouter une projection…','projWin()'],['plan','Disposition auto','autoViews()'],['plan','Feuille Installation + détails','autoPages()'],['det','Vue de détail',"setTool('det')",'det'],['cam','Capture 3D','addShot()'],['nom','Nomenclature','toggleNom()','nom'],['txt','Texte',"setTool('tx')"]]],['Cotation',[['cur','Sélection',"setTool('sel')",'sel'],['dh','Horizontale',"setTool('dh')",'dh'],['dv','Verticale',"setTool('dv')",'dv'],['dd','Alignée',"setTool('dd')",'dd'],['ang','Angle (2 droites)',"setTool('ang')",'ang'],['dia','Diamètre Ø',"setTool('dia')",'dia'],['del','Supprimer','delDraw()']]],['Feuille',[['gear','Paramètres','planSettings()'],['hid','Traits cachés','toggleHid()','hid'],['axe','Axes','toggleAx()','axe']]]],
 'Formes':[['Primitives',[['box','Bloc',"addP('box')"],['cyl','Cylindre',"addP('cyl')"],['tube','Tube rond',"addP('tube')"],['sph','Sphère',"addP('sph')"],['cone','Cône',"addP('cone')"]]],['Profilés métal',[['tcar','Tube carré',"addP('tcar')"],['corn','Cornière',"addP('corn')"],['U','Profilé U',"addP('U')"],['I','Poutre I',"addP('I')"]]]],
 'Esquisse':[['Dessin',[['cur','Sélection',"skTool('sel')",'sel'],['poly','Polyligne',"skTool('poly')",'poly'],['rect','Rectangle',"skTool('rect')",'rect'],['circ','Cercle',"skTool('circ')",'circ']]],['Contraintes géométriques',[['cH','Horizontale',"skC('H')"],['cV','Verticale',"skC('V')"],['cpar','Parallèle',"skC('par')"],['cperp','Perpendiculaire',"skC('perp')"],['ceq','Égalité',"skC('eq')"],['ccoin','Coïncidence',"skC('coin')"],['cpol','Point sur ligne',"skC('pol')"],['cax','Sur axe X',"skC('fy')"],['cay','Sur axe Y',"skC('fx')"],['clock','Verrouiller',"skC('lock')"]]],['Contraintes de cote',[['ddist','Distance',"skD('dist')"],['dh','Horizontale',"skD('dx')"],['dv','Verticale',"skD('dy')"],['dang','Angle',"skD('ang')"],['drad','Rayon',"skD('rad')"]]],['Coins',[['chf','Chanfrein',"skRound('ch')"],['cng','Congé',"skRound('fi')"]]],['Solide',[['ext','Extruder','skExtrude()'],['rev','Révolution','skRevolve()'],['del','Tout effacer','skClear()']]]]};
const EXPERT_ONLY=['Formes','Esquisse','Nomenclature'],MODEL_TABS=['Créer','Opérations','Formes'],TNAME={'Opérations':'Façonner et assembler'},TAB_ORDER=['Fichier','Édition','Créer','Opérations','Formes','Esquisse','Mise en plan','Nomenclature','Accueil'];
function why(f){if(!f||typeof sel=='undefined')return'';const W=sel.filter(isWood),woodN=objs.filter(isWood).length,has=sel.length||selA!=null;
 if(/^(fendreWin|quartWin|coupeWin|pointeWin)\(/.test(f))return W.length==1?'':'Sélectionnez d’abord une seule pièce de bois (clic sur la pièce).';
 if(/^(asmStart|equerreWin|phWin)/.test(f))return woodN<2?'Il faut au moins deux pièces de bois dans le modèle.':(sel.length>2&&!/phWin/.test(f)?'Sélectionnez deux pièces au plus (ou aucune : les deux premières seront proposées).':'');
 if(/^plateauWin/.test(f)){if(W.length<2)return'Sélectionnez d’abord deux supports parallèles (deux traverses) avant d’ajouter un plateau, des claies ou un filet.';const A=W.map(axisOf);if(Math.abs(dot(A[0].u,A[1].u))<.97)return'Les deux supports sélectionnés ne sont pas parallèles.';return''}
 if(/^bool\(/.test(f))return sel.length==2?'':'Sélectionnez exactement deux pièces.';
 if(/^(dup|delSel|toGround|repWin)\(/.test(f))return has?'':'Sélectionnez d’abord un objet.';
 return''}
function buildRibbon(){setTimeout(()=>{viewPanel();vbarBuild();projLbl();const lb=(viewTab=='Bibliothèque de modèles'||viewTab=='Modèles partagés'||viewTab=='Accueil')&&curTab==viewTab;$('#rp').style.display=lb?'none':'';document.body.classList.toggle('lbx',lb)});const M=document.body.classList,cm=M.contains('dm')?tool:M.contains('sk')?sk.tool:'';if(!expert&&EXPERT_ONLY.includes(curTab))curTab=EXPERT_ONLY.includes(viewTab)?(viewTab='Opérations'):curTab;if(!expert&&EXPERT_ONLY.includes(curTab))curTab='Opérations';
 const act=(i,k)=>(k=='snap'&&snapOn)||(k=='hid'&&SHID())||(k=='axe'&&SAX())||(k=='dm3'&&showDims)||(k=='ortho'&&cam===camO)||(k=='ghost'&&ghost)||(k=='grid'&&gr.visible)||(k=='expert'&&expert)||(k=='nom'&&nom.show)||(k&&k==cm&&!['snap','hid','axe','dm3','ortho','ghost','grid','expert','nom'].includes(k));
 $('#tabs').innerHTML=TAB_ORDER.filter(t=>TABS[t]).filter(t=>t=='Fichier'||(t=='Édition'&&expert)||t=='Créer'||t=='Opérations'||t=='Mise en plan'||t=='Nomenclature'||(MODEL_TABS.includes(viewTab)?(MODEL_TABS.includes(t)||t=='Esquisse'):(t==viewTab&&t!='Accueil'))).filter(t=>expert||!EXPERT_ONLY.includes(t)).map(t=>`<button class="t ${t==curTab||(t=='Fichier'&&curTab=='Accueil')?'on':''}" onclick="tabClick('${t}')">${TNAME[t]||t}</button>`).join('')
  +`<span class="qb"><button onclick="undo()" title="Annuler (Ctrl+Z)"${Hi>0?'':' disabled'}>${ic('undo',16)}</button><button onclick="redo()" title="Rétablir (Ctrl+Y)"${Hi<H.length-1?'':' disabled'}>${ic('redo',16)}</button><button onclick="settingsDlg()" title="Paramètres">${ic('gear',16)}</button><button class="${expert?'on':''}" onclick="toggleExpert()" title="${expert?'Vous êtes en mode expert. Cliquez pour revenir au mode simple.':'Vous êtes en mode simple. Cliquez pour activer le mode expert (esquisse, formes, booléens, traits cachés, nomenclature).'}">${ic(expert?'expert':'expert0',16)}<span>${expert?'Passer en mode simple':'Passer en mode expert'}</span></button>${HAS_AI()?`<button onclick="aiToggle()" title="Assistant IA">${ic('ai',16)}<span>Assistant</span></button>`:''}<button onclick="help()" title="Aide">${ic('help',16)}</button></span>`;
 $('#rp').innerHTML=TABS[curTab].filter(([g])=>expert||!g.startsWith('*')).map(([g,bs])=>`<div class="gp"><div class="gb">${bs.filter(b=>expert||!['hid','axe','nom'].includes(b[3])).map(([i,l0,f,k,sp])=>{const l=typeof l0=='function'?l0():l0;const why_=why(f),main=`<button class="rbt${act(i,k)?' act':''}${why_?' dis':''}" onclick="${why_?`msg(${esc(JSON.stringify(why_))},5000)`:f}" title="${esc(l+(why_?' — indisponible : '+why_:''))}">${ic(i)}<span>${esc(l)}</span></button>`;return sp?`<span class="sb">${main}<button class="chv" title="Choisir le type" onclick="menuAt(this,SPLIT['${sp}'])">▾</button></span>`:main}).join('')}</div><div class="gl">${g.replace('*','')}</div></div>`).join('')}
let prevTab='Créer',fsec='accueil';
function tabClick(t){if(document.body.classList.contains('act'))closeMd();if(t=='Fichier'){if(viewTab!='Accueil')prevTab=MODEL_TABS.includes(viewTab)?viewTab:prevTab;t='Accueil'}else if(t=='Accueil'){if(viewTab!='Accueil')prevTab=MODEL_TABS.includes(viewTab)?viewTab:prevTab}curTab=t;if(t!='Édition'){viewTab=t;setMode(t)}buildRibbon();vbarBuild()}
function setMode(t){const b=document.body.classList;b.toggle('dm',t=='Mise en plan');b.toggle('sk',t=='Esquisse');b.toggle('nm',t=='Nomenclature');b.toggle('lb',t=='Bibliothèque de modèles'||t=='Modèles partagés');b.toggle('hm',t=='Accueil');if(t=='Accueil')setTimeout(homeShow);hideCm();sideShow();if(t=='Nomenclature')nomTab();if(t=='Bibliothèque de modèles')libShow('ref');if(t=='Modèles partagés')libShow('com');
 if(t=='Mise en plan'){pend=null;draw();drui()}else if(t=='Esquisse'){skDraw();skui()}else{rs();ui()}}
function toggleExpert(){expert=!expert;if(!expert&&EXPERT_ONLY.includes(viewTab)){tabClick('Créer')}try{localStorage.setItem('cathia.expert',expert?'1':'0')}catch(e){}buildRibbon();msg(expert?'Vous êtes maintenant en MODE EXPERT (Formes, Esquisse, Nomenclature, traits cachés).':'Vous êtes maintenant en MODE SIMPLE.')}
function toggleSnap(){snapOn=!snapOn;buildRibbon()}
function cycT(){const L=[1,5,10,50,100];stepT=L[(L.indexOf(stepT)+1)%L.length];snapOn=true;buildRibbon()}
function cycR(){const L=[1,5,15,45,90];stepR=L[(L.indexOf(stepR)+1)%L.length];snapOn=true;buildRibbon()}
/* ----- boîtes de dialogue ----- */
function dlg(title,F,cb,ok='Valider',intro=''){const m=$('#md');mvDispose();$('#mb').classList.remove('wide');
 const fld=f=>{f={...f};if(isMm(f)&&typeof f.v=='number')f.v=Math.round(f.v*uk()*100)/100;f.l=isMm(f)?f.l.replace('(mm)','('+us()+')'):U(f.l||'');return fld0(f)},fld0=f=>f.t=='info'?`<p class="mu" id="f_${f.k}">${f.l}</p>`:f.t=='sel'?`<label>${f.l}<select id="f_${f.k}">${f.o.map(o=>{const[v,l]=Array.isArray(o)?o:[o,o];return`<option value="${esc(v)}"${String(v)==String(f.v)?' selected':''}>${esc(l)}</option>`}).join('')}</select></label>`:f.t=='chk'?`<label class="ck"><input id="f_${f.k}" type="checkbox" ${f.v?'checked':''}> ${f.l}</label>`:f.t=='txt'?`<label>${f.l}<input id="f_${f.k}" type="text" value="${esc(f.v)}"></label>`:`<label>${f.l}<input id="f_${f.k}" type="number" step="any" value="${f.v}"></label>`+(f.h?`<div class="mu" style="margin:-4px 0 6px;font-size:11px">${f.h}</div>`:'');
 $('#mb').innerHTML=`<h3>${title}</h3>${intro?`<p class="mu">${intro}</p>`:''}`+F.map(fld).join('')+`<p id="derr" style="color:var(--er);margin:6px 0 0;display:none"></p><div class="r" style="margin-top:12px"><button class="p" id="mok">${ok}</button><button id="mno">Annuler</button></div>`;
 m.classList.add('on');const first=$('#mb input,#mb select');if(first&&!/Android|iPhone|iPad/.test(navigator.userAgent))first.focus();
 const go=()=>{const v={};F.forEach(f=>{if(f.t=='info')return;const e=$('#f_'+f.k);v[f.k]=f.t=='chk'?e.checked:f.t=='txt'?e.value:f.t=='sel'?(e.value!==''&&!isNaN(+e.value)?+e.value:e.value):isMm(f)?+e.value/uk():+e.value});
  try{const r=cb(v);if(r!==false)m.classList.remove('on')}catch(err){const e=$('#derr');e.textContent=err.message||String(err);e.style.display='block'}};
 $('#mok').onclick=go;$('#mno').onclick=()=>m.classList.remove('on');$('#mb').onkeydown=e=>{if(e.key=='Enter'&&e.target.tagName!='BUTTON'){e.preventDefault();go()}}}
function modal(h){mvDispose();$('#mb').classList.remove('wide');$('#mb').innerHTML=h;$('#md').classList.add('on')}
function closeMd(){$('#md').classList.remove('on');mvDispose();$('#mb').classList.remove('wide');document.body.classList.remove('act');const md=$('#md');['left','top','width','height'].forEach(k=>md.style[k]='')}
/* fenêtre d'action : elle prend la place du contenu principal (vue 3D, plan…) ; le ruban et le panneau latéral restent visibles */
function placeAct(){if(!document.body.classList.contains('act'))return;const app=$('#app').getBoundingClientRect(),sd=$('#side'),sw=sd&&sd.offsetParent?sd.getBoundingClientRect().width:0,vb=$('#vbar'),vh=vb&&vb.offsetParent?vb.getBoundingClientRect().height:0,md=$('#md');
 md.style.left=(app.left+sw)+'px';md.style.top=app.top+'px';md.style.width=(app.width-sw)+'px';md.style.height=(app.height-vh)+'px';document.body.style.setProperty('--actH',(app.height-vh)+'px')}
addEventListener('resize',placeAct);
$('#md').addEventListener('pointerdown',e=>{if(e.target.id=='md')closeMd()});
/* ----- menu contextuel ----- */
let cmF=[];
const cmHtml=items=>items.filter(Boolean).map(it=>{if(it.sep)return'<div class="sp"></div>';if(it.hd)return`<div class="hd">${esc(it.hd)}</div>`;const id=cmF.push(it.fn||null)-1;
 return`<div class="ci${it.dis?' dis':''}" data-f="${id}">${it.ic?ic(it.ic,16):'<span style="width:16px;flex:none"></span>'}<span>${esc(it.l)}</span>${it.k?`<span class="k">${esc(it.k)}</span>`:''}${it.sub?'<span class="k">▸</span><div class="sub">'+cmHtml(it.sub)+'</div>':''}</div>`}).join('');
function showCm(x,y,items){cmF=[];const cm=$('#cm');cm.innerHTML=cmHtml(items);cm.classList.add('on');cm.style.left=cm.style.top='0px';const w=cm.offsetWidth,h=cm.offsetHeight;cm.style.left=Math.max(4,Math.min(x,innerWidth-w-4))+'px';cm.style.top=Math.max(4,Math.min(y,innerHeight-h-4))+'px';if(x+w+210>innerWidth)cm.querySelectorAll('.sub').forEach(s=>s.classList.add('l'))}
function hideCm(){$('#cm').classList.remove('on')}
$('#cm').addEventListener('click',e=>{const c=e.target.closest('.ci');if(!c||c.classList.contains('dis'))return;const f=cmF[+c.dataset.f];if(!f){e.stopPropagation();return}hideCm();f()});
addEventListener('pointerdown',e=>{if(!e.target.closest('#cm'))hideCm()},true);
const menuAt=(el,items)=>{const b=el.getBoundingClientRect();showCm(b.left,b.bottom+2,items)};
const asmItems=o=>[{l:'Tenon classique (hachette)…',ic:'hache',fn:()=>asmStart('hache',o)},{l:'Tenon scié…',ic:'scie',fn:()=>asmStart('scie',o)},{l:'Tenon plat…',ic:'plat',fn:()=>asmStart('plat',o)},{l:'Mi-bois…',ic:'milb',fn:()=>asmStart('mibois',o)},{l:'Queue d’aronde',ic:'aronde',sub:[1,2,3].map(t=>({l:'Queue d’aronde '+ARO[t]+'…',fn:()=>asmWin('aronde'+t,o)}))},{l:'Cheviller…',ic:'cheville',fn:()=>asmStart('cheville',o)},{sep:1},{l:'Brêlage (dernier recours)…',ic:'lash',fn:()=>asmStart('lash',o)}];
function moveItems(){const L=[{l:'Nouvel assemblage avec la sélection',ic:'asm',fn:groupSel},{l:'Racine (aucun assemblage)',fn:()=>moveSel(0),dis:!sel.length&&selA==null}];Object.values(asms).forEach(a=>L.push({l:asmPath({par:a.id}).join(' › '),fn:()=>moveSel(a.id)}));return L}
function pieceMenu(o){const A=o.par&&asms[o.par],ops=o.ops||[],lk=linkedOf(o).length;
 return[{hd:o.name},
  editable(o)?{l:'Modifier… (esquisse / fenêtre d’édition)',ic:'gear',fn:()=>editObj(o)}:null,
  A?{l:`Sélectionner l’assemblage « ${A.n} »`,ic:'asm',fn:()=>selAsm(A.id)}:null,
  o.type=='trav'?{l:stretchOn?'Masquer les poignées d’allongement':'Allonger / raccourcir avec des poignées',ic:'coupe',fn:()=>{stretchOn=!stretchOn;gzPlace();req()}}:null,
  {l:'Assembler avec…',ic:'milb',sub:asmItems(o),dis:!isWood(o)},
  {l:'Façonner',ic:'split',sub:[{l:'Fendre…',ic:'split',fn:()=>fendreWin(o)},{l:'Quart de bois…',ic:'quart',fn:()=>quartWin(o)},{l:'Couper (plan de coupe)…',ic:'coupe',fn:()=>coupeWin(o)},{l:'Tailler en pointe…',ic:'pointe',fn:()=>pointeWin(o)}],dis:!isWood(o)},
  {l:ops.length?`Opérations (${ops.length})`:'Créer',ic:'bom',sub:ops.length?ops.flatMap((p,i)=>[{l:'Modifier : '+p.lab,ic:'bom',fn:()=>editOp(o,i),dis:!p.rec},{l:'Supprimer : '+p.lab,ic:'del',fn:()=>delOp(o,i)}]):[{l:'Aucune opération',dis:1}]},
  {l:'Répétition…',ic:'rep',fn:repWin},
  lk?{l:'Désolidariser des pièces liées',ic:'ungrp',fn:()=>unlinkSel(true)}:null,
  {sep:1},{l:'Déplacer vers un assemblage',ic:'grp',sub:moveItems()},
  A?{l:'Sortir de l’assemblage',fn:()=>{o.par=A.par;touch();ui()}}:null,
  {sep:1},{l:'Renommer…',fn:()=>dRename(o),k:'F2'},{l:'Dupliquer',ic:'dup',fn:()=>dup(),k:'Ctrl+D'},{l:'Dupliquer sans opérations',ic:'dup',fn:()=>dup(false)},{l:'Poser au sol',ic:'ground',fn:toGround},{l:'Isoler (masquer les autres)',ic:'eye',fn:()=>isolate(o)},{sep:1},{l:'Supprimer',ic:'del',fn:delSel,k:'Suppr'}]}
function asmMenu(id){const a=asms[id];return[{hd:'Assemblage « '+a.n+' »'},a.src&&a.src.t=='clay'?{l:'Modifier le clayonnage…',ic:'clay',fn:()=>clayWin(null,id)}:null,{l:'Sélectionner',ic:'asm',fn:()=>selAsm(id)},{l:'Voir le montage pas à pas',ic:'play',fn:()=>montage(id)},{l:'Nouveau sous-assemblage',ic:'asm',fn:()=>{const n=newAsm('Sous-assemblage',id);touch();selAsm(n.id)}},{l:'Renommer…',fn:()=>dRename(null,id)},{l:'Dupliquer',ic:'dup',fn:()=>{selAsm(id);dup()}},{l:'Poser au sol',ic:'ground',fn:()=>{selAsm(id);toGround()}},{l:'Sortir de l’assemblage parent',fn:()=>{a.par=asms[a.par]?asms[a.par].par:0;touch();ui()},dis:!a.par},{l:'Dégrouper',ic:'ungrp',fn:()=>{delAsm(id,false);select([]);ui()}},{sep:1},{l:'Supprimer avec son contenu',ic:'del',fn:()=>{delAsm(id,true);select([]);ui()}}]}
function emptyMenu(){return[{hd:'Ajouter'},{l:'Traverse debout',ic:'perche',fn:()=>addT('Z')},{l:'Traverse couchée',ic:'percheH',fn:()=>addT('X')},{l:'Piquet pointu',ic:'piquet',fn:addPiquet},{l:'Équarri',ic:'box',fn:addBox},{l:'Mobilier de l’atelier Froissart',ic:'fauteuil',sub:[['etabli','Établi de camp'],['banc','Banc court'],['fauteuil','Fauteuil carré'],['table','Table à pieds en X']].map(([k,l])=>({l,ic:k,fn:()=>exWin(k)}))},{sep:1},{l:'Tout sélectionner',ic:'cur',fn:selAll},{l:'Nouvel assemblage vide',ic:'asm',fn:()=>{const a=newAsm();touch();selAsm(a.id)}},{sep:1},{l:'Vue',ic:'view',sub:[['iso','Isométrique'],['front','Face'],['back','Arrière'],['right','Droite'],['left','Gauche'],['top','Dessus'],['bottom','Dessous']].map(([k,l])=>({l,fn:()=>setView(k)}))},{l:'Tout voir',ic:'fit',fn:fit},{l:showDims?'Masquer les cotes 3D':'Afficher les cotes 3D',ic:'dm3',fn:toggleDims},{l:ghost?'Opaque':'Transparence',ic:'eye',fn:toggleGhost},{sep:1},{l:'Annuler',ic:'undo',fn:undo,k:'Ctrl+Z',dis:Hi<=0},{l:'Rétablir',ic:'redo',fn:redo,k:'Ctrl+Y',dis:Hi>=H.length-1}]}
function ctx3d(e,o){if(o&&!sel.includes(o)&&!(selA!=null&&piecesOf(selA).includes(o)))select([o]);
 const items=o?(sel.length>1&&sel.includes(o)||selA!=null&&piecesOf(selA).includes(o)?multiMenu():pieceMenu(o)):emptyMenu();showCm(e.clientX,e.clientY,items)}
function multiMenu(){const n=targets().length,two=sel.length==2&&selA==null;return[{hd:selA!=null?`Assemblage « ${asms[selA].n} » (${n} pièces)`:n+' pièces'},
 {l:'Assembler les deux pièces…',ic:'milb',sub:asmItems(sel[0]),dis:!two},{l:'Grouper dans un assemblage',ic:'asm',fn:groupSel,dis:selA!=null},{l:'Déplacer vers un assemblage',ic:'grp',sub:moveItems()},{sep:1},{l:'Dupliquer',ic:'dup',fn:dup},{l:'Poser au sol',ic:'ground',fn:toGround},{l:'Couleur…',fn:dColor},{sep:1},{l:'Supprimer',ic:'del',fn:delSel}]}
/* ----- actions sur la sélection ----- */
const selAll=()=>select(objs.slice());
function delSel(){const T=targets();if(!T.length)return msg('Sélectionnez un objet.');if(selA!=null){delAsm(selA,true)}else rmObjs(T);select([]);ui()}
function toGround(){const T=targets();if(!T.length)return msg('Sélectionnez un objet.');const dz=-bounds(T)[0][2];if(Math.abs(dz)<.01)return msg('Déjà posé au sol.');T.forEach(o=>{if(o.type=='lash')o.p.parts.forEach(s=>s.c[2]+=dz);else if(o.type=='ph')o.p.segs.forEach(s=>{s[0][2]+=dz;s[1][2]+=dz});else{o.pos[2]+=dz;o.m.position.z=o.pos[2]}});T.forEach(o=>GL.includes(o.type)&&mk(o));gzCenter();touch();ui()}
function isolate(o){const on=objs.some(x=>x.m.visible===false);objs.forEach(x=>x.m.visible=on||x===o);req();msg(on?'Tout est de nouveau visible.':'Autres pièces masquées (même commande pour tout réafficher).')}
function cloneObjs(L,dx,jm,parMap,withOps=true){return L.map(o=>{const p=JSON.parse(JSON.stringify(o.p));if(o.type=='lash')p.parts.forEach(s=>s.c[0]+=dx);if(o.type=='ph')p.segs.forEach(s=>{s[0][0]+=dx;s[1][0]+=dx});
 const c=mkObj(o.type,p,o.g,o.name,o.color,GL.includes(o.type)?[0,0,0]:[o.pos[0]+dx,o.pos[1],o.pos[2]],[...o.rot],parMap?parMap.get(o.par)??o.par:o.par);c.mat=o.mat;if(withOps){c.ops=JSON.parse(JSON.stringify(o.ops||[])).map(op=>{if(op.jid){if(!jm.has(op.jid))jm.set(op.jid,++JID);op.jid=jm.get(op.jid);delete op.rec}return op});if(c.ops.length)mk(c)}return c})}
function dup(w){const T=targets();if(!T.length)return msg('Sélectionnez un objet.');
 if(w===undefined&&selA==null&&T.some(o=>o.ops&&o.ops.length))return dlg('Dupliquer',[{k:'o',l:'Copier aussi les opérations (tenons, mortaises, mi-bois…)',t:'chk',v:false},{k:'i',t:'info',l:'Sans opérations, la copie est une pièce brute, prête à recevoir d’autres assemblages.'}],v=>dup(v.o),'Dupliquer');
 const withOps=w!==false,[mn,mx]=bounds(T),dx=Math.round((mx[0]-mn[0])/100)*100+200,jm=new Map();
 if(selA!=null){const pm=new Map(),cp=(id,par)=>{const a=asms[id],n=newAsm(a.n+(par==a.par?' (copie)':''),par);n.mat=a.mat;pm.set(id,n.id);kidsA(id).forEach(k=>cp(k.id,n.id));return n};const root=cp(selA,asms[selA].par);cloneObjs(piecesOf(selA),dx,jm,pm,withOps);touch();selAsm(root.id)}
 else{const L=cloneObjs(sel,dx,jm,null,withOps);select(L)}}
function unlinkSel(free){const T=targets();if(!T.length)return msg('Sélectionnez une pièce ou un assemblage.');const S=new Set(T);moveTargets().forEach(o=>S.add(o));freeLinks([...S],free?true:undefined)}
function groupSel(){const nodes=selA!=null?[{t:'a',id:selA}]:sel.map(o=>({t:'p',id:o.id}));if(!nodes.length)return msg('Sélectionnez d’abord une ou plusieurs pièces (Ctrl+clic pour en ajouter).');
 const par=selA!=null?asms[selA].par:sel[0].par;const a=newAsm('Assemblage '+aid,par);moveTo(nodes,a.id);selAsm(a.id);msg('Assemblage créé. Double-clic sur une pièce : sélectionne son assemblage.')}
function ungroup(){if(selA==null)return msg('Sélectionnez un assemblage (double-clic sur une pièce, ou dans la liste).');const id=selA;delAsm(id,false);select([]);ui()}
function outOfGroup(){if(selA!=null){const a=asms[selA];a.par=asms[a.par]?asms[a.par].par:0}else sel.forEach(o=>o.par=asms[o.par]?asms[o.par].par:0);touch();ui()}
function moveSel(parent){if(selA!=null)moveTo([{t:'a',id:selA}],parent);else sel.forEach(o=>o.par=parent);touch();ui()}
function dRename(o,aid){const cur=o?o.name:asms[aid].n;dlg('Renommer',[{k:'n',l:'Nom',t:'txt',v:cur}],v=>{if(!v.n.trim())throw new Error('Nom vide.');if(o)o.name=v.n.trim();else asms[aid].n=v.n.trim();touch();ui()})}
function dColor(){dlg('Couleur',[{k:'c',l:'Couleur',t:'txt',v:'#c8a06a'}],v=>{targets().forEach(o=>{o.color=v.c;o.m.material.color.set(v.c)});touch();ui()})}
/* ----- ajout de pièces ----- */
function addT(ax){const s=sel1(),vert=ax!='X',p=freeSpot();if(s&&s.type=='trav'){p[0]=Math.max(p[0],bounds([s])[1][0]+300)}
 const o=mkObj('trav',{d:80,L:vert?1500:2000},null,null,null,vert?[p[0],0,0]:[p[0],0,800],vert?[0,0,0]:[0,90,0],0);select([o]);if(objs.length<3)fit();msg(vert?'Traverse verticale posée à l’aplomb (repère absolu).':'Traverse horizontale posée selon X (repère absolu).')}
function straighten(ax){const T=targets().filter(isWood);if(!T.length)return msg('Sélectionnez une pièce.');T.forEach(o=>{o.rot=ax=='X'?[0,90,0]:ax=='Y'?[-90,0,0]:[0,0,0];o.m.rotation.set(...o.rot.map(d=>d*D))});gzCenter();touch();ui()}
function addPiquet(){const p=freeSpot();p[2]=-300;const o=mkObj('trav',{d:50,L:800},null,'Piquet '+nid,null,p);o.ops.push({k:'point',o:[0,0,0],u:[0,0,1],L:150,r0:3,rT:25,rmax:25,lab:'Pointe de 150 mm au bout A'});mk(o);select([o])}
function addBox(){select([mkObj('box',{...SPEC.box.d},null,'Équarri '+nid,'#d2ab76')])}
function addP(t){select([mkObj(t,{...SPEC[t].d},null,null,'#b8bcc4')]);msg('Forme ajoutée ('+SPEC[t].n+').')}
function bool(op){const[a,b]=sel;if(sel.length!=2||selA!=null)return msg('Sélectionnez exactement deux pièces (clic puis Ctrl+clic). A = la première.');
 const g={u:union,s:subtract,i:intersect}[op](wg(a),wg(b));if(!G.toPolygons(g).length)return msg('Le résultat est vide.');const c=a.color,n='Forme '+nid;rmObjs([a,b]);select([mkObj('mesh',{},g,n,c,[0,0,0])])}
/* ----- fenêtres d'opérations : voir d3_wins.js ----- */
const dFendre=o=>fendreWin(o),dCoupe=o=>coupeWin(o),dPointe=o=>pointeWin(o);
function dOps(){const o=sel1();if(!o)return msg('Sélectionnez une pièce.');if(!o.ops.length)return msg('Cette pièce n’a aucune opération (tenon, mortaise, mi-bois…).');
 modal(`<h3>Opérations de « ${esc(o.name)} »</h3><div class="ops">${o.ops.map((p,i)=>`<div class="op"><span>${esc(p.lab)}</span><button title="Modifier" ${p.rec?'':'disabled'} onclick="closeMd();editOp(sel1(),${i})">✎</button><button class="dg" onclick="delOp(sel1(),${i});dOps()">✕</button></div>`).join('')}</div><div class="r"><button onclick="closeMd()">Fermer</button></div>`)}
/* ----- arborescence (liste des objets) ----- */
let dragN=null;const modelMode=()=>!document.body.classList.contains('dm')&&!document.body.classList.contains('sk');
function lst(){if(document.body.classList.contains('dm')||document.body.classList.contains('sk'))return;const S=new Set(sel);
 const prow=(o,d)=>`<div class="it${S.has(o)?' on':''}" style="padding-left:${6+d*14}px" draggable="true" data-t="p" data-id="${o.id}">${ic(o.type=='lash'?'lash':o.type=='box'?'box':o.type=='trav'?'perche':o.type,16)}<span class="nm">${esc(o.name)}</span>${o.ops&&o.ops.length?`<span class="mu" title="Opérations">${o.ops.length}⚒</span>`:''}<i style="background:${o.color}"></i></div>`;
 const node=(par,d)=>kidsA(par).map(a=>{const open=a.open===true,n=piecesOf(a.id).length;return`<div class="it${selA==a.id?' on':''}" style="padding-left:${6+d*14}px;font-weight:600" draggable="true" data-t="a" data-id="${a.id}"><span class="tg" data-tg="${a.id}">${open?'▾':'▸'}</span>${ic('asm',16)}<span class="nm">${esc(a.n)}</span><span class="mu">${n}</span></div>`+(open?node(a.id,d+1):'')}).join('')+kidsP(par).map(o=>prow(o,d)).join('');
 $('#ls').innerHTML=`<h4>Objets</h4>${objs.length?'<button class="p mtgo" onclick="mtStart()" title="Rejoue la construction pièce par pièce, comme à la main">▶ Montage pas à pas</button><p class="mu" style="font-size:11px;margin:0 0 6px">Ctrl + clic : ajouter ou retirer une pièce · Maj + clic : sélectionner une plage</p>':''}<div id="tree" data-t="root">${node(0,0)||'<p class="mu">Aucun objet. Onglet <b>Créer</b> : ajoutez une traverse ; ou <b>Bibliothèque de modèles</b> (onglet du bas) : un meuble du livre.</p>'}</div>`;req()}
const tree=$('#ls');
tree.addEventListener('click',e=>{if(!modelMode())return;const tg=e.target.closest('[data-tg]');if(tg){const a=asms[tg.dataset.tg];a.open=a.open!==true;lst();return}const r=e.target.closest('.it');if(!r)return;const id=+r.dataset.id;
 if(r.dataset.t=='a')return selAsm(id);const o=objs.find(x=>x.id==id);if(e.shiftKey&&treeLast!=null){const ids=[...tree.querySelectorAll('.it[data-t="p"]')].map(x=>+x.dataset.id),i0=ids.indexOf(treeLast),i1=ids.indexOf(id);if(i0>=0&&i1>=0){select(ids.slice(Math.min(i0,i1),Math.max(i0,i1)+1).map(k=>objs.find(x=>x.id==k)).filter(Boolean));return}}
 if(e.ctrlKey||e.metaKey||e.shiftKey){const L=selA!=null?[]:sel.slice(),i=L.indexOf(o);i<0?L.push(o):L.splice(i,1);select(L)}else select([o]);treeLast=id});
let treeLast=null;
tree.addEventListener('contextmenu',e=>{e.preventDefault();if(!modelMode())return;const r=e.target.closest('.it');if(!r)return showCm(e.clientX,e.clientY,emptyMenu());const id=+r.dataset.id;
 if(r.dataset.t=='a'){selAsm(id);showCm(e.clientX,e.clientY,asmMenu(id))}else{const o=objs.find(x=>x.id==id);if(!sel.includes(o))select([o]);showCm(e.clientX,e.clientY,sel.length>1?multiMenu():pieceMenu(o))}});
tree.addEventListener('dragstart',e=>{const r=e.target.closest('.it');if(!r||!r.dataset.t)return;dragN={t:r.dataset.t,id:+r.dataset.id};e.dataTransfer.setData('text/plain',dragN.t+dragN.id);e.dataTransfer.effectAllowed='move'});
tree.addEventListener('dragover',e=>{if(!dragN)return;e.preventDefault();tree.querySelectorAll('.dz').forEach(x=>x.classList.remove('dz'));const r=e.target.closest('.it[data-t="a"]');if(r)r.classList.add('dz')});
tree.addEventListener('drop',e=>{if(!dragN)return;e.preventDefault();const r=e.target.closest('.it[data-t="a"]'),to=r?+r.dataset.id:0;const nodes=dragN.t=='p'&&sel.some(o=>o.id==dragN.id)&&selA==null?sel.map(o=>({t:'p',id:o.id})):[dragN];dragN=null;moveTo(nodes,to);ui()});
tree.addEventListener('dragend',()=>{dragN=null;tree.querySelectorAll('.dz').forEach(x=>x.classList.remove('dz'))});
/* ----- panneau de propriétés ----- */
let sideTab='arbre';
function revealSel(){if(!sel.length||selA!=null)return;if(sideTab!='arbre')sideSet('arbre');let a=sel[0].par,ch=false;while(a&&asms[a]){if(asms[a].open!==true){asms[a].open=true;ch=true}a=asms[a].par}if(ch)lst();const e=document.querySelector('#ls .it.on');if(e)e.scrollIntoView({block:'nearest'})}
const PJI={persp:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6"><path d="M4 9l8-4 8 4v8l-8 4-8-4z"/><path d="M12 5v16M4 9l8 4 8-4"/></svg>',ortho:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6"><path d="M12 3l8 4.5v9L12 21l-8-4.5v-9z"/><path d="M12 12v9M12 12l8-4.5M12 12L4 7.5"/></svg>'};
function projLbl(){const b=$('#pjb');if(b){const o=cam===camO;b.innerHTML=(o?PJI.persp:PJI.ortho)+'<span>'+(o?'Passer en perspective':'Passer en vue orthogonale')+'</span>';b.title=o?'Vous êtes en vue orthogonale. Cliquez pour la perspective.':'Vous êtes en perspective. Cliquez pour la vue orthogonale.'}}
function sideSet(t){sideTab=t;sideShow()}
function sideShow(){const pv=$('#pvw');if(pv)pv.style.display=modelMode()&&sideTab=='prop'?'':'none';const m=modelMode();$('#stabs').style.display=m?'flex':'none';$('#stabs').innerHTML=[['arbre','Objets'],['prop','Propriétés']].map(([k,l])=>`<button class="${k==sideTab?'on':''}" onclick="sideSet('${k}')">${l}</button>`).join('');
 $('#ls').style.display=!m||sideTab=='arbre'?'':'none';$('#pr').style.display=!m||sideTab=='prop'?'':'none';}
/* nomenclature éditable (tableur) : désignation et essence modifiables, appliquées à toutes les pièces du groupe */
function nomTab(){const G=groups(objs);window._nomG=G;
 $('#nmv').innerHTML=`<h3>Nomenclature</h3><p class="mu">Tableur : modifiez directement la désignation et l’essence ; le changement s’applique à toutes les pièces du groupe et à la mise en plan.</p><table><tr><th>N°</th><th>Qté</th><th>Désignation</th><th>Dimensions</th><th>Assemblages</th><th>Essence</th></tr>${G.map((g,i)=>`<tr><td>${i+1}</td><td>${g.n}</td><td><input value="${esc(desOf(g.o))}" onchange="nomSet(${i},'dsg',this.value)"></td><td>${esc(descOf(g.o))}</td><td>${esc(opsOf(g.o))}</td><td><input value="${esc(g.o.mat||'')}" onchange="nomSet(${i},'mat',this.value)"></td></tr>`).join('')}</table><div class="r" style="margin-top:8px"><button onclick="dlBom()">Exporter CSV</button><button onclick="showBom()">Voir la liste</button></div>`}
function nomSet(i,k,v){const g=window._nomG[i];if(!g)return;g.list.forEach(o=>{if(k=='dsg')o.dsg=v.trim()||undefined;else o.mat=v});touch();lst()}
function ui(){sideShow();if(document.body.classList.contains('nm'))nomTab();if(document.body.classList.contains('dm'))return drui();if(document.body.classList.contains('sk'))return skui();lst();const P=$('#pr');
 if(selA!=null){const a=asms[selA],L=piecesOf(selA);P.innerHTML=`<h4>Assemblage</h4><label>Nom<input value="${esc(a.n)}" oninput="asms[selA].n=this.value;lst();touch()"></label><p class="mu">${L.length} pièces. Tirez les flèches de la poignée pour déplacer ou tourner tout l’assemblage ; clic droit pour plus d’options.</p>
  <label>Essence / matière (appliquée à toutes les pièces)<input value="${esc(a.mat||'')}" oninput="asms[selA].mat=this.value;piecesOf(selA).forEach(o=>o.mat=this.value);touch()"></label><label>Couleur de toutes les pièces<input type="color" value="${L[0]?L[0].color:'#c8a06a'}" oninput="piecesOf(selA).forEach(o=>{o.color=this.value;o.m.material.color.set(this.value)});req();lst();touch()"></label>
  <div class="r"><button onclick="dup()">Dupliquer</button><button onclick="toGround()">Poser au sol</button></div><div class="r" style="margin-top:6px"><button onclick="ungroup()">Dégrouper</button><button class="dg" onclick="delSel()">Supprimer</button></div>`+sumHTML();dlBuild();return}
 if(!sel.length){P.innerHTML=sumHTML()+'<p class="mu">Cliquez une pièce pour la modifier (Ctrl+clic pour en ajouter). Double-clic dans la 3D : son assemblage ; dans la liste : renommer. Ctrl+G / Ctrl+Maj+G : grouper / dégrouper. Clic droit : toutes les options. Glisser : tourner la vue ; molette : zoom.</p>';dlBuild();return}
 if(sel.length>1){const two=sel.length==2;P.innerHTML=`<h4>${sel.length} pièces sélectionnées</h4><div class="r"><button onclick="groupSel()">Grouper</button><button onclick="dup()">Dupliquer</button></div><div class="r" style="margin-top:6px"><button onclick="toGround()">Poser au sol</button><button class="dg" onclick="delSel()">Supprimer</button></div>`+(two?`<h4>Assembler ces deux pièces</h4><div class="r"><button onclick="asmStart('mibois')">Mi-bois</button><button onclick="asmStart('scie')">Tenon scié</button></div><div class="r" style="margin-top:6px"><button onclick="asmStart('hache')">Tenon hache</button><button onclick="asmStart('plat')">Tenon plat</button></div><div class="r" style="margin-top:6px"><button onclick="asmStart('aronde')">Queue d’aronde</button><button onclick="asmStart('lash')">Brêlage</button></div>`:'')+sumHTML();dlBuild();return}
 const o=sel[0],F=SPEC[o.type].f;let h=`<h4>Pièce</h4><label>Nom<input value="${esc(o.name)}" oninput="sel1().name=this.value;lst();touch()"></label>`;
 if(o.par&&asms[o.par])h+=`<p class="mu">Assemblage : ${esc(asmPath(o).join(' › '))}</p>`;
 h+=F.map(([k,l])=>`<label>${l} (${us()})${o.p[k]>=1000?' — '+fr(o.p[k]/1000)+' m':''}<input type="number" min="0.1" step="${uk()==1?1:.5}" value="${r1(o.p[k]*uk())}" oninput="setP('${k}',+this.value/uk())" onfocus="hotK='${k}'" onblur="hotK=null"></label>`).join('');
 if(o.type=='mesh'){const b=lbb(o);h+=`<p class="mu">Dimensions : ${[0,1,2].map(i=>fu(b.max[i]-b.min[i])).join(' × ')} ${us()}</p>`}
 h+=`<label>Essence / matière<input value="${esc(o.mat||'')}" placeholder="ex. châtaignier" oninput="sel1().mat=this.value;touch()"></label><label>Couleur<input type="color" value="${o.color}" oninput="sel1().color=this.value;sel1().m.material.color.set(this.value);req();lst();touch()"></label>
  <h4>Position (${us()})</h4><div class="r">${[0,1,2].map(i=>`<label>${'XYZ'[i]}<input id="p${i}" type="number" step="${uk()==1?10:1}" value="${r1(o.pos[i]*uk())}" oninput="setPos(${i},+this.value/uk())"></label>`).join('')}</div>
  <h4>Rotation (°)</h4><div class="r">${[0,1,2].map(i=>`<label>${'XYZ'[i]}<input id="r${i}" type="number" step="5" value="${r1(o.rot[i])}" oninput="setRot(${i},+this.value)"></label>`).join('')}</div>`;
 if(!GL.includes(o.type))h+=`<h4>Opérations</h4><div class="ops">${o.ops.length?o.ops.map((p,i)=>`<div class="op" title="${esc(p.dof||'')}"><span>${esc(U(p.lab))}${p.dof?`<br><small class="mu">${esc(U(p.dof))}</small>`:''}</span><button title="Modifier" ${p.rec?'':'disabled'} onclick="editOp(sel1(),${i})">✎</button><button class="dg" title="Supprimer" onclick="delOp(sel1(),${i})">✕</button></div>`).join(''):'<span class="mu">Aucune (tenon, mortaise, mi-bois…)</span>'}</div><button onclick="menuAt(this,asmItems(sel1()))">Assembler avec…</button> <button onclick="menuAt(this,[{l:'Fendre…',fn:()=>fendreWin()},{l:'Quart de bois…',fn:()=>quartWin()},{l:'Couper…',fn:()=>coupeWin()},{l:'Tailler en pointe…',fn:()=>pointeWin()}])">Façonner…</button> <button onclick="straighten('Z')" title="Remettre à l’aplomb">Redresser</button>`;
 else if(o.type=='ph')h+=`<button class="p" onclick="editObj(sel1())">Modifier…</button><p class="mu">PH décoratif : ${o.p.segs.length} cordes, ≈ ${fr(Math.round(phLen(o)/10)/100)} m de corde. Aucune fonction de structure.</p>`;
 else if(o.type=='cavalier')h+=`<p class="mu">Clou cavalier : fixe une claie sur son support.</p>`;
 else h+=`<label>Tours de corde<input type="number" min="2" max="20" value="${o.p.turns}" oninput="o_lash(+this.value)"></label><p class="mu">Corde estimée : ${fr(ropeLen(o)/1000)} m</p>`;
 h+=`<h4>Objet</h4><div class="r"><button onclick="dup()">Dupliquer</button><button onclick="toGround()">Poser au sol</button><button class="dg" onclick="delSel()">Supprimer</button></div>`+sumHTML();P.innerHTML=h;dlBuild()}
function o_lash(n){const o=sel1();if(!o||!(n>=2&&n<=20))return;o.p.turns=n;mk(o);touch()}
function setP(k,v){const o=sel1();if(!o)return;const p=o.p;if(!(v>(k=='ch'||k=='fi'?-1:0)))return;const old=p[k];p[k]=v;if(!okp(o)){p[k]=old;return}o.g=build(o);mk(o);gzCenter();dlBuild();touch()}
function setPos(i,v){const o=sel1();if(!o)return;const d=(v||0)-o.pos[i];moveTargets().forEach(x=>{x.pos[i]+=d;x.m.position.set(...x.pos)});ver++;gzCenter();touch()}
function setRot(i,v){const o=sel1();if(!o)return;o.rot[i]=v||0;o.m.rotation.set(...o.rot.map(d=>d*D));gzCenter();touch()}
function sumHTML(){if(!objs.length)return'';const b=bomData();return`<div class="sum" id="sum"><b>${objs.length}</b> pièces · <b>${b.nops}</b> assemblages · bois rond <b>${fr(b.tl)}</b> m${b.rope?` · corde ≈ <b>${fr(b.rope)}</b> m`:''}<br><a href="#" onclick="showBom();return false">Voir la liste du matériel</a></div>`}
/* ----- matériel : liste des pièces ----- */
function descOf(o,mm){const f=mm?v=>fr(Math.round(v*10)/10)+' mm':sm;if(o.type=='trav')return`Ø ${f(o.p.d)} × ${f(o.p.L)}`;if(o.type=='lash')return`${o.p.turns} tours, corde Ø ${f(o.p.rope)}`;if(o.type=='ph')return`${o.p.segs.length} cordes, Ø ${f(o.p.d)}`;if(o.type=='cavalier')return`${f(o.p.w)} × ${f(o.p.h)}`;const b=lbb(o);return[0,1,2].map(i=>f(b.max[i]-b.min[i])).join(' × ')}
function opsOf(o){return(o.ops||[]).map(p=>U(p.lab.replace(/ →.*| ←.*| avec .*/,''))).join(' ; ')}
function groups(L){const m=new Map();L.forEach(o=>{const k=SPEC[o.type].n+'|'+(o.type=='trav'||GL.includes(o.type)?o.type:o.name.replace(/\s*\d+$/,''))+'|'+descOf(o)+'|'+opsOf(o)+'|'+(o.mat||'');let e=m.get(k);if(!e){e={o,n:0,list:[]};m.set(k,e)}e.n++;e.list.push(o)});return[...m.values()]}
const desOf=o=>o.dsg?o.dsg:o.type=='trav'?(o.ops&&o.ops.some(p=>p.k=='point')?'Piquet':'Traverse'):o.type=='lash'?'Brêlage':o.type=='ph'?(o.p.kind=='filet'?'Filet de ficelle':o.p.kind=='corde'?'Cordes':'Cordes du PH (décoratif)'):o.type=='cavalier'?'Clou cavalier':o.type=='mesh'?o.name.replace(/\s*\d+$/,''):o.name.replace(/\s*\d+$/,'');
function bomData(){let tl=0,rope=0,nops=new Set();objs.forEach(o=>{if(o.type=='trav')tl+=o.p.L/1000;if(o.type=='lash')rope+=ropeLen(o)/1000;if(o.type=='ph')rope+=phLen(o)/1000;(o.ops||[]).forEach(p=>p.jid&&nops.add(p.jid))});return{tl,rope,nops:nops.size+objs.filter(o=>o.type=='lash').length,cav:objs.filter(o=>o.type=='cavalier').length,G:groups(objs)}}
function bomLines(){return bomData().G.map(g=>`${g.n} × ${desOf(g.o)} ${descOf(g.o)}`+(opsOf(g.o)?` (${opsOf(g.o)})`:''))}
function bomHTML(){const b=bomData();return`<h3>Liste du matériel</h3><p class="mu">${esc(meta.titre)} — ${new Date().toLocaleDateString('fr-FR')}</p>`+(objs.length?`<table class="bom">${b.G.map(g=>`<tr><td class="n">${g.n} ×</td><td>${esc(desOf(g.o))} ${esc(descOf(g.o))}${opsOf(g.o)?`<br><span class="mu">${esc(opsOf(g.o))}</span>`:''}${g.o.mat?` <span class="mu">· ${esc(g.o.mat)}</span>`:''}</td></tr>`).join('')}</table><p class="mu">Bois rond : ${fr(b.tl)} m au total · ${b.nops} assemblages${b.rope?' · corde ≈ '+fr(b.rope)+' m':''}${b.cav?' · '+b.cav+' clous cavaliers':''}.</p>`:'<p>Aucune pièce.</p>')}
function showBom(){modal(bomHTML()+`<div class="r"><button class="p" onclick="copyBom()">Copier la liste</button><button onclick="dlBom()">Fichier CSV</button><button onclick="closeMd()">Fermer</button></div>`)}
function copyBom(){const t=bomLines().join('\n');navigator.clipboard.writeText(t).then(()=>msg('Liste copiée.'),()=>{const r=document.createRange();r.selectNodeContents($('#mb'));getSelection().removeAllRanges();getSelection().addRange(r);msg('Sélectionnée : faites Ctrl+C')})}
function dlBom(){const b=bomData(),r=[['Quantité','Désignation','Dimensions','Opérations','Essence']];b.G.forEach(g=>r.push([g.n,desOf(g.o),descOf(g.o),opsOf(g.o),g.o.mat||'']));save('materiel.csv','﻿'+r.map(l=>l.map(x=>`"${String(x).replace(/"/g,'""')}"`).join(';')).join('\r\n'),'text/csv')}
/* ----- aide ----- */
function help(){modal(`<h3>CathIA : aide rapide</h3><ol><li><b>Opérations › Traverse</b> : ajoutez une traverse (bois rond), à l’aplomb au départ ; retournez-la avec les flèches de rotation. Réglez diamètre et longueur à gauche ou en cliquant les cotes orange.</li><li><b>Déplacer / tourner</b> : flèches droites (déplacement) et petites flèches courbes (rotation).</li><li><b>Opérations</b> : une fenêtre s’ouvre avec un aperçu 3D en direct et un schéma. Vous y choisissez le type (tenon classique à la hachette, tenon scié, tenon plat, 2 queues d’aronde, mi-bois, chevilles, brêlage) et les pièces.</li><li>Une pièce peut cumuler plusieurs assemblages. Chaque opération se modifie (✎) ou se supprime sans toucher aux autres.</li><li><b>Liaisons</b> : un assemblage lie les pièces, elles se déplacent ensemble. Édition › Désolidariser pour les séparer.</li><li><b>Fendre</b> en planches d’épaisseur choisie, en demi-rondins ou quartiers ; <b>Quart de bois</b> pour poser un plateau.</li><li><b>Répétition</b> linéaire ou circulaire, <b>Clayonnage</b> automatique entre des supports, contrôle des <b>collisions</b>.</li><li><b>Groupes</b> : Ctrl+G grouper, Ctrl+Maj+G dégrouper ; glisser-déposer dans la liste. Double-clic dans la liste : renommer ; dans la 3D : son assemblage.</li><li><b>Bibliothèque de modèles</b> : établi, banc, fauteuil, table, avec leurs dimensions réglables ; outil PH décoratif.</li><li>Les dimensions sont en <b>centimètres</b> (millimètres au choix dans Paramètres).</li><li><b>Mise en plan</b> : pages multiples, vues, capture 3D, nomenclature déplaçable, cartouche éditable en cliquant le texte, impression.</li></ol><p class="mu">Raccourcis : Ctrl+Z, Ctrl+Y, Ctrl+D, Suppr, Ctrl+S, F2, Échap. Règle du tiers : une mortaise ne dépasse pas le tiers du diamètre de la pièce. Le bouton Paramètres règle l’aimant, le jeu des mortaises, les liaisons…</p><div class="r"><button class="p" onclick="closeMd()">Compris</button></div>`)}
function settingsDlg(){dlg('Paramètres',[{k:'snap',l:'Aimant (déplacements et rotations par pas)',t:'chk',v:snapOn},{k:'un',l:'Unité de longueur',t:'sel',v:PREF.unit,o:[['cm','Centimètre (conseillé)'],['mm','Millimètre']]},{k:'st',l:'Pas de déplacement',t:'sel',v:stepT,o:[[1,'1 mm'],[5,'5 mm'],[10,'1 cm'],[50,'5 cm'],[100,'10 cm']]},{k:'sr',l:'Pas de rotation (°)',t:'sel',v:stepR,o:[1,5,15,45,90]},{k:'jeu',l:'Jeu des mortaises par défaut (mm)',t:'num',v:PREF.jeu},{k:'th',l:'Angle des queues d’aronde par défaut (°)',t:'num',v:PREF.theta},{k:'rigid',l:'Un assemblage lie les pièces (elles se déplacent ensemble)',t:'chk',v:PREF.rigid},{k:'dims',l:'Afficher les cotes 3D de la pièce sélectionnée',t:'chk',v:showDims},{k:'anim',l:'Rejouer en accéléré (≈ 5 s) la construction d’un modèle de référence',t:'chk',v:PREF.anim!==false},{k:'aut',l:'Nom du dessinateur (cartouche)',t:'txt',v:PREF.auteur||meta.des||''},{k:'ex',l:'Mode expert (esquisse, formes, booléens, traits cachés)',t:'chk',v:expert}],v=>{PREF.unit=v.un;snapOn=v.snap;stepT=v.st;stepR=v.sr;PREF.jeu=v.jeu;PREF.theta=v.th;PREF.rigid=v.rigid;PREF.anim=v.anim;showDims=v.dims;PREF.auteur=v.aut;if(v.aut&&!meta.des)meta.des=v.aut;if(v.ex!==expert)toggleExpert();savePrefs();dlBuild();buildRibbon();ui();if(document.body.classList.contains('dm'))draw()},'Enregistrer')}
function savePrefs(){try{localStorage.setItem('cathia.prefs',JSON.stringify({snapOn,stepT,stepR,showDims,PREF}))}catch(e){}}
function loadPrefs(){try{const p=JSON.parse(localStorage.getItem('cathia.prefs'));if(p){snapOn=p.snapOn!==false;stepT=p.stepT||10;stepR=p.stepR||15;showDims=p.showDims!==false;Object.assign(PREF,p.PREF||{})}}catch(e){}}

tree.addEventListener('dblclick',e=>{if(!modelMode())return;const r=e.target.closest('.it');if(!r||e.target.closest('[data-tg]'))return;const id=+r.dataset.id;if(r.dataset.t=='a'){const a=asms[id];if(a&&a.src&&a.src.t=='clay')clayWin(null,id);else dRename(null,id)}else{const o=objs.find(x=>x.id==id);editable(o)?editObj(o):dRename(o)}});
IC.prepa=IC.table;IC.cuisine=IC.table;IC.vaisselier=IC.table;IC.etagere=IC.table;IC.feu=IC.table;
/* ----- Bibliothèque de modèles : galerie de captures 3D (pas d'icônes) ----- */
const LIBC=Object.assign({},typeof LIBPRE!=='undefined'?LIBPRE:{}),LIBD={etabli:'Corps à 2 perches, pédale, palonnier',banc:'Rondin fendu sur 4 pieds',fauteuil:'Fauteuil carré à accoudoirs',bancdos:'Montants arrière inclinés, assise en 2 demi-rondins, dossier fendu',bancdiag:'Diagonales pied + dossier, assise rondin à tenons plats',table:'X, claies tressées / droites / filet',prepa:'Rondins fendus dessus, claies dessous',cuisine:'Plan 90 cm + colonne, étagères tous les 45 cm',etagere:'Claies, quart de bois, filet',vaisselier:'Largeur de bassine, filet de 3 cm',feu:'Pieds, cadre et planches'};
function libThumb(k){if(LIBC[k])return LIBC[k];const q={};EXQ[k].forEach(([id,,v,t])=>q[id]=t=='chk'?!!v:t=='sel'?String(v):+v);
 const items=buildTemp(k,{...q,pv:true}),r=new THREE.WebGLRenderer({antialias:true,preserveDrawingBuffer:true});r.setSize(360,270);const s2=new THREE.Scene();s2.background=new THREE.Color(0xf4f5f7);s2.add(new THREE.AmbientLight(0xffffff,.75));const dl=new THREE.DirectionalLight(0xffffff,.8);dl.position.set(500,-800,1000);s2.add(dl);
 const box=new THREE.Box3(),grp=new THREE.Group();s2.add(grp);
 for(const it of items){const m=new THREE.Mesh(it.tg,new THREE.MeshStandardMaterial({color:it.color,roughness:.75,metalness:.05,side:THREE.DoubleSide}));if(it.eg)m.add(new THREE.LineSegments(it.eg,new THREE.LineBasicMaterial({color:0x333333})));m.position.set(...it.pos);m.rotation.order='ZYX';m.rotation.set(...it.rot.map(d=>d*D));grp.add(m);box.expandByObject(m)}
 const c=box.getCenter(new THREE.Vector3()),sp=box.getBoundingSphere(new THREE.Sphere()),cam2=new THREE.PerspectiveCamera(35,360/270,10,200000);cam2.up.set(0,0,1);const d=new THREE.Vector3(.75,-1,.6).normalize(),dist=sp.radius/Math.tan(35*Math.PI/360)*1.05;cam2.position.copy(c).addScaledVector(d,dist);cam2.lookAt(c);
 r.render(s2,cam2);const url=r.domElement.toDataURL('image/png');r.dispose();try{r.forceContextLoss()}catch(e){}return LIBC[k]=url}

function viewPanel(){const e=$('#pvw');if(!e)return;e.innerHTML=`<h4>Affichage</h4><div class="r">${[['iso','Iso'],['front','Face'],['back','Arrière'],['right','Droite'],['left','Gauche'],['top','Dessus'],['bottom','Dessous']].map(([k,l])=>`<button onclick="setView('${k}')">${l}</button>`).join('')}<button onclick="fit()">Tout voir</button></div><label class="ck"><input type="checkbox" ${showDims?'checked':''} onchange="toggleDims()"> Cotes 3D de la pièce sélectionnée</label><label class="ck"><input type="checkbox" ${ghost?'checked':''} onchange="toggleGhost()"> Transparence</label><label class="ck"><input type="checkbox" ${gr.visible?'checked':''} onchange="toggleGrid()"> Grille et axes</label><label class="ck"><input type="checkbox" ${cam===camO?'checked':''} onchange="toggleProj();projLbl()"> Vue isométrique (orthographique)</label>`}
function gotoPage(i){planOn=true;tabClick('Mise en plan');if(i<0)addPage();else loadPage(i)}
function closePlanPage(i){loadPage(i);if(pages.length>1)delPage();else{pages=[];ensurePages();pages[0].views=[];planOn=false;tabClick('Créer')}vbarBuild()}
let planOn=false;
function planMenu(el){menuAt(el,[{l:'Nouvelle mise en plan (dessin technique)',ic:'plan',fn:()=>{planOn=true;gotoPage(pages.length&&planOn&&pages.some(p=>p.views.length)?-1:0)}},{l:'Modèles de référence',ic:'plateau',fn:()=>tabClick('Bibliothèque de modèles')},{l:'Modèles partagés',ic:'asm',fn:()=>tabClick('Modèles partagés')}])}
function vbarBuild(){const e=$('#vbar');if(!e||typeof pages=='undefined')return;ensurePages();if(pages.some(p=>p.views.length))planOn=true;const mdl=MODEL_TABS.includes(viewTab),b=(on,l,fn)=>`<button class="${on?'p':''}" onclick="${fn}">${l}</button>`;
 e.innerHTML=b(viewTab=='Accueil','Accueil',"tabClick('Accueil')")+b(mdl,'Modèle 3D',"tabClick(MODEL_TABS.includes(viewTab)?viewTab:'Créer')")+libTabBtn()+(expert?b(viewTab=='Nomenclature','Nomenclature',"tabClick('Nomenclature')"):'')
  +(planOn?pages.map((p,i)=>`<button class="${viewTab=='Mise en plan'&&i==curPage?'p':''}" onclick="gotoPage(${i})" ondblclick="renamePage(${i})" title="Double-clic : renommer">Plan · ${esc(p.name)}<span class="px" title="Fermer cette page" onclick="event.stopPropagation();closePlanPage(${i})">✕</span></button>`).join(''):'')+'<button onclick="planMenu(this)" title="Ajouter : mise en plan, bibliothèque de modèles">＋</button>'}

function editObj(o){if(!o)return;if(o.skSrc)return skEdit(o);if(o.type=='ph'){return o.p.kind=='filet'?(o.p.src?netWin(o):msg('Ce filet a été créé avant la fonction de modification : supprimez-le et recréez-le.',6000)):phWin(o)}if(o.type=='lash')return msg('Brêlage : supprimez-le et recréez-le avec les nouveaux réglages.');if(o.ops&&o.ops.some(p=>p.rec))return dOps();msg('Rien à modifier ici : utilisez le panneau Propriétés.')}
const editable=o=>o&&(o.type=='ph'||o.type=='lash'||o.skSrc);

const SPLIT={aronde:[{hd:'Choisir le type de queue d’aronde'},{l:'Classique (trapèze vu de face)',fn:()=>asmStart('aronde1')},{l:'À mi-bois (traversante)',fn:()=>asmStart('aronde2')},{l:'Trapézoïdale dans l’axe du cylindre (traversante)',fn:()=>asmStart('aronde3')}],
 lash:[{hd:'Choisir le type de brêlage'},{l:'Brêlage en X (pièces qui se croisent)',fn:()=>asmStart('lash-x')},{l:'Brêlage droit (pièces parallèles)',fn:()=>asmStart('lash-droit')}],
 equerre:[{hd:'Choisir le type d’équerre'},{l:'Demi-rondin tangent, chevillé',fn:()=>equerreWin('demi')},{l:'Rondin entier tangent, chevillé',fn:()=>equerreWin('plein')},{l:'Rondin incrusté (encoches jusqu’au milieu des pièces)',fn:()=>equerreWin('incruste')}],
 plateau:[{hd:'Choisir le type de plateau ou de paroi'},{l:'Claies tressées (plan horizontal, incliné ou vertical)',fn:()=>clayWin()},{l:'Claies droites en quart de bois (horizontal)',fn:()=>deckWin('claies')},{l:'Planches chevillées (horizontal)',fn:()=>deckWin('planches')},{l:'Filet de ficelle (plan horizontal, incliné ou vertical)',fn:()=>netWin()}],
 tenon:[{hd:'Choisir le type de tenon'},{l:'Tenon à la hachette (classique)',fn:()=>asmStart('hache')},{l:'Tenon scié (faux tenon)',fn:()=>asmStart('scie')},{l:'Tenon plat à la hachette (embase conique)',fn:()=>asmStart('plat')},{l:'Tenon plat scié',fn:()=>asmStart('platscie')}]};

/* ----- page d'accueil façon logiciel de CAO ----- */
function homeContent(){let saved=null;try{const st=JSON.parse(localStorage.getItem(KEY));if(st&&st.objs&&st.objs.length)saved=st}catch(e){}
 const card=(ic_,t,s,fn,big)=>`<div class="hmc${big?' big':''}" onclick="${fn}">${ic(ic_,38)}<div><b>${t}</b><small>${s}</small></div></div>`;
 const d=saved&&saved.date?new Date(saved.date).toLocaleString('fr-FR',{dateStyle:'short',timeStyle:'short'}):'';
 return `<h1>CathIA</h1><p class="mu">Conception 3D de mobilier et d’installations de froissartage : traverses, tenons, mi-bois, plans.</p>
 ${saved?`<h3>Reprendre</h3><div class="hmg">${card('open','Continuer le projet en cours',`« ${esc((saved.meta&&saved.meta.titre)||'Mon installation')} » · ${saved.objs.length} pièces · enregistré automatiquement ${d}`,"tabClick('Créer');fit()",1)}</div>`:''}
 <h3>Ouvrir</h3><div class="hmg">${card('open','Depuis cet appareil','Fichier .cathia.html, .json ou plan .svg','openProj()')}${gasOK()?card('drive','Mes projets (Google Drive)','Vos projets, dans votre propre Drive','openDrive()'):''}${card('asm','Modèles partagés','Réalisations de la communauté',"tabClick('Modèles partagés')")}${card('table','Modèles de référence','Établi, tables, bancs… et modèles vérifiés',"tabClick('Bibliothèque de modèles')")}</div>
 <h3>Créer</h3><div class="hmg">${card('perche','Nouveau modèle 3D','Partir d’une traverse, assembler, façonner',"objs.length?newProj():tabClick('Créer')")}${card('plan','Nouvelle mise en plan','Dessin technique coté du projet (vues, cotes, nomenclature)',"gotoPage(pages.some(p=>p.views.length)?-1:0)")}${card('table','Modèles de référence','Établi, tables, bancs… à régler, et modèles vérifiés',"tabClick('Bibliothèque de modèles')")}${card('asm','Modèles partagés','Réalisations de la communauté : tente, table, mât…',"tabClick('Modèles partagés')")}</div>
 <h3>Aide</h3><div class="hmg">${card('help','Comment ça marche ?','Les 5 gestes pour démarrer','help()')}</div>`}
const BS=[['accueil','Accueil','home'],['nouveau','Nouveau','new'],['ouvrir','Ouvrir','open'],['enregistrer','Enregistrer','html'],['exporter','Exporter','pdf'],['imprimer','Imprimer','print'],['params','Paramètres','gear'],['aide','Aide','help']];
function homeShow(){const L=$('#hmv');if(!L)return;L.style.padding='0';
 L.innerHTML=`<div class="bs"><nav><button class="bsb back" onclick="tabClick(prevTab)">← Retour au modèle</button>${BS.concat(gasOK()?[['compte','Compte','help']]:[]).map(([k,l,i])=>`<button class="bsb${fsec==k?' on':''}" onclick="bsGo('${k}')">${ic(i,18)}<span>${l}</span></button>`).join('')}</nav><section id="bsc"></section></div>`;bsGo(fsec)}
const bsAct=(i,t,s,fn)=>`<div class="hmc" onclick="${fn}">${ic(i,34)}<div><b>${t}</b><small>${s}</small></div></div>`;
function bsGo(k){fsec=k;document.querySelectorAll('#hmv .bsb').forEach(b=>b.classList.toggle('on',b.getAttribute('onclick')==`bsGo('${k}')`));const C=$('#bsc');if(!C)return;
 const h=(t)=>`<h2>${t}</h2>`;
 if(k=='accueil')C.innerHTML=homeContent();
 else if(k=='nouveau'){C.innerHTML=h('Nouveau')+`<div class="hmg">${bsAct('perche','Nouveau modèle 3D','Repartir d’une page vide',"objs.length?newProj():tabClick('Créer')")}${bsAct('table','Modèles de référence','Établi, tables, bancs… à régler, et modèles vérifiés',"tabClick('Bibliothèque de modèles')")}${bsAct('asm','Modèles partagés','Réalisations de la communauté',"tabClick('Modèles partagés')")}${bsAct('plan','Nouvelle mise en plan','Feuille vierge pour ajouter des projections',"gotoPage(pages.some(p=>p.views.length)?-1:0)")}</div>`}
 else if(k=='ouvrir')C.innerHTML=h('Ouvrir')+`<div class="hmg">${bsAct('open','Depuis cet appareil','Fichier .cathia.html, .json ou plan .svg','openProj()')}${gasOK()?bsAct('drive','Mes projets (Google Drive)',AUTH.tok?'Connecté : '+AUTH.email:'Connexion avec Google','openDrive()'):''}${bsAct('asm','Modèles partagés','Réalisations de la communauté',"tabClick('Modèles partagés')")}${bsAct('table','Modèles de référence','Établi, tables, bancs… et modèles vérifiés',"tabClick('Bibliothèque de modèles')")}</div>`;
 else if(k=='enregistrer')C.innerHTML=h('Enregistrer')+`<div class="hmg">${(gasOK()?bsAct('drive','Enregistrer dans mon Drive (privé)','Compte Google : dossier « nom.cathia » dans VOTRE Drive','saveCloud()')+bsAct('asm','Publier dans la communauté (public)','Visible et notable par tous, sans nom ni e-mail','saveCloud(true)'):'')+bsAct('html','Télécharger le projet (.cathia.html)','Fichier autonome qui s’ouvre dans un navigateur','saveProjFile()')}${bsAct('json','Projet (.json)','Pour sauvegarde ou partage','saveJSON()')}</div>`;
 else if(k=='exporter'){C.innerHTML=h('Exporter')+`<div class="bsx"><div class="bsl">${[['m3d','Image du modèle 3D (PNG)'],['m3p','Modèle 3D (PDF)'],['plan','Plan (PDF, toutes les pages)'],['pnp','Plan (PNG)'],['svg','Plan (SVG)'],['csv','Liste de matériel (CSV)']].map(([x,l])=>`<button class="bsb" onclick="bsPrev('${x}')">${l}</button>`).join('')}</div><div class="bsp" id="bsp"><p class="mu">Choisissez un format : l’aperçu s’affiche ici, tel qu’il sera exporté.</p></div></div>`}
 else if(k=='imprimer')C.innerHTML=h('Imprimer')+`<div class="hmg">${bsAct('print','Imprimer le plan','Toutes les pages de la mise en plan','printAll()')}</div>`;
 else if(k=='params')C.innerHTML=h('Paramètres')+`<div class="hmg">${bsAct('gear','Paramètres de l’application','Unités, aimant, jeu, corde…','settingsDlg()')}${bsAct('expert',expert?'Passer en mode simple':'Passer en mode expert','Afficher ou masquer les outils avancés','toggleExpert();bsGo(\'params\')')}${bsAct('gear','Thème de couleurs','Distinguer visuellement les types de pièces','themeDlg()')}${bsAct('html','Télécharger l’application complète','Un seul fichier, sans internet : bibliothèques externes et modèles inclus','dlApp()')}</div>`;
 else if(k=='compte')C.innerHTML=h('Compte')+(AUTH.tok?`<p>Connecté avec <b>${esc(AUTH.email)}</b>.</p><div class="hmg">${bsAct('drive','Mes projets','Les projets enregistrés dans mon Drive','openDrive()')}${bsAct('help','Se déconnecter','Cet appareil oubliera la connexion','authOut()')}</div>`:`<p class="mu">${AUTH_NOTE}</p><div class="hmg">${bsAct('help','Se connecter','Avec Google (ou code par e-mail pour publier)','authDlg()')}</div>`)
 else if(k=='aide')C.innerHTML=h('Aide')+`<div class="hmg">${bsAct('help','Comment ça marche ?','Les 5 gestes pour démarrer','help()')}</div>`}
async function bsPrev(x){const P=$('#bsp');if(!P)return;const btn=(l,fn)=>`<button class="p" onclick="${fn}">${l}</button>`;
 if(x=='m3d'||x=='m3p'){if(!objs.length){P.innerHTML='<p class="mu">Rien à exporter : créez d’abord un modèle.</p>';return}const c=snap3D();P.innerHTML=`<img src="${c.src}" alt="">`+btn('Exporter',x=='m3d'?'exPNG3()':'exPDF3()')}
 else if(x=='csv'){const b=bomData();P.innerHTML=`<p class="mu">${b.rows?b.rows.length:''} lignes de matériel.</p>`+btn('Télécharger le CSV','dlBom()')}
 else{ensurePages();if(!pages.some(p=>p.views.length)&&!views.length){P.innerHTML='<p class="mu">La mise en plan est vide : ajoutez d’abord une projection (onglet Mise en plan).</p>';return}const svg=svgDoc();P.innerHTML=`<img src="data:image/svg+xml;charset=utf-8,${encodeURIComponent(svg)}" alt="">`+btn('Exporter',{plan:'exPDF()',pnp:'exPNGplan()',svg:'dlSVG()'}[x])}}


function addTraverse(){if(!MODEL_TABS.includes(viewTab))tabClick('Créer');addT('Z')}

/* thèmes de couleurs : distinguer les types de pièces (marron + accents bleu ou rouge) */
const THEMES={marron:{n:'Marron naturel',pied:'#c8a06a',lisse:'#d2ab76',claie:'#b5894f',cheville:'#8a5a2b',util:'#d2ab76',usine:'#9bb07a'},
 bleu:{n:'Marron et bleu marine',pied:'#8b5a2b',lisse:'#2b4a8a',claie:'#dcc08e',cheville:'#c0272d',util:'#5a78b5',usine:'#9bb07a'},
 rouge:{n:'Marron et rouge',pied:'#7a4a24',lisse:'#c0272d',claie:'#d9b98a',cheville:'#1d3a73',util:'#a8553a',usine:'#9bb07a'}};
function roleOf(o){const n=o.name||'';if(o.type=='ph'||o.type=='lash')return null;if(o.peg||/Cheville|Tige|clou/i.test(n))return'cheville';if(/Élément à serrer|usiner/i.test(n))return'usine';if(/Claie|Planche|Rondin fendu|Assise|Plateau|Dossier/i.test(n)||o.type=='courbe')return'claie';if(/Pied|Poteau|Perche|Montant|Jambe/i.test(n))return'pied';if(/Lisse|Traverse|Support|Rail|Barre/i.test(n))return'lisse';return'util'}
function applyTheme(k,list){const T=THEMES[k]||THEMES.marron;(list||objs).forEach(o=>{const r=roleOf(o);if(!r)return;o.color=T[r];if(o.m&&o.m.material)o.m.material.color.set(T[r])});PREF.theme=k;try{savePrefs()}catch(e){}req()}
function themeDlg(){dlg('Thème de couleurs',[{k:'t',l:'Thème',t:'sel',v:PREF.theme||'marron',o:Object.keys(THEMES).map(k=>[k,THEMES[k].n])},{k:'i',t:'info',l:'Pieds, supports, claies/planches, chevilles et pièces à usiner reçoivent chacun une teinte.'}],v=>{applyTheme(v.t);touch()},'Appliquer')}

function chamf([a,b,d],c){const oct=(w,h)=>{const x=w/2,y=h/2;return[[-x+c,-y],[x-c,-y],[x,-y+c],[x,y-c],[x-c,y],[-x+c,y],[-x,y-c],[-x,-y+c]]};
 const pr=(w,h,l)=>J.extrusions.extrudeLinear({height:l},J.geometries.geom2.fromPoints(oct(w,h)));
 return intersect(translate([0,0,-d/2],pr(a,b,d)),transform([0,1,0,0,0,0,1,0,1,0,0,0,0,0,0,1],translate([0,0,-a/2],pr(b,d,a))),transform([1,0,0,0,0,0,1,0,0,1,0,0,0,0,0,1],translate([0,0,-b/2],pr(a,d,b))))}


/* =====================  Mise en plan  ===================== */
function edgesOf(pols){return featEdges(pols.map(p=>p.vertices))}
const SHID=()=>expert&&showHid,SAX=()=>expert&&showAx;
const DIRS={front:['Face',[0,1,0]],back:['Arrière',[0,-1,0]],right:['Droite',[-1,0,0]],left:['Gauche',[1,0,0]],top:['Dessus',[0,0,-1]],bottom:['Dessous',[0,0,1]],iso:['Isométrique',[-1,1,-1]]};
const NICE=[5,2,1,.5,.2,.1,1/15,.05,.04,1/30,.025,.02,1/75,.01,.005,.002,.001];
const key=p=>p.map(x=>Math.round(x*100)).join(','),fx=v=>+v.toFixed(2);
const scl=s=>s>=1?`${r1(s)}:1`:`1:${r1(1/s)}`;
const LP=(w,p)=>[(p[0]-w.u0)*w.s,(w.v1-p[1])*w.s],SP=(w,p)=>{const l=LP(w,p);return[w.x+l[0],w.y+l[1]]};
const CSS='.rp{fill:none;stroke:#8a6338;stroke-width:.18}.ha{fill:url(#hat);stroke:#555;stroke-width:.25;fill-opacity:.9}.e{fill:none;stroke:#111;stroke-width:.35;stroke-linecap:round}.hd{fill:none;stroke:#444;stroke-width:.2;stroke-dasharray:1.6 .9}.d{stroke:#0a58c8;stroke-width:.2;marker-start:url(#a);marker-end:url(#a)}.x{stroke:#0a58c8;stroke-width:.15}.hit{stroke:#fff;stroke-opacity:.01;stroke-width:3}text{fill:#111;font:3.4px Arial,sans-serif}.dim text{fill:#0a58c8}text.t{font-weight:bold;font-size:4px}.dim.on *{stroke:#e08a00}.dim.on text{fill:#e08a00;stroke:none}.pv{opacity:.65}.cl{fill:none;stroke:#111;stroke-width:.2;stroke-dasharray:7 1.2 1.2 1.2}line.z{stroke:#111;stroke-width:.25}text.z{font-size:3px;text-anchor:middle}text.sl{font-size:1.9px;fill:#555}text.sv{font-size:3.4px}text.tx.on{fill:#e08a00}';
const DEFS='<defs><pattern id="hat" width="2" height="2" patternUnits="userSpaceOnUse" patternTransform="rotate(45)"><path d="M0 0V2" stroke="#555" stroke-width=".25"/></pattern><marker id="a" viewBox="0 0 10 10" refX="10" refY="5" markerWidth="5" markerHeight="5" orient="auto-start-reverse"><path d="M0 0L10 5L0 10z" fill="#0a58c8"/></marker></defs>';
const isClaie=o=>o.type=='courbe'||/^Claie/.test(o.name);
let ECk='';
let TRo=[];
function edgesAll(only){const key=ver+'|'+(only?only.join(','):'');if(ECk!=key){const per=solids().filter(o=>(!only||only.includes(o.id))&&!isClaie(o)).map(o=>G.toPolygons(wg(o)));EC=per.flatMap((ps,i)=>edgesOf(ps).map(e=>(e.o=i,e)));TRo=[];TR=per.flatMap((ps,oi)=>ps.flatMap(pl=>{const v=pl.vertices,t=[];for(let i=1;i<v.length-1;i++){t.push([v[0],v[i],v[i+1]]);TRo.push(oi)}return t}));ECk=key}return EC}
function vdata(w){if(w.cv==ver&&w.hv===SHID()&&w.ax===SAX()&&w.ck===ECk)return w;edgesAll(w.only);w.ck=ECk;
 const f=nrm(DIRS[w.k][1]),h=Math.abs(f[2])>.99?[1,0,0]:nrm(cr(f,[0,0,1])),v=cr(h,f),P=p=>[dt(p,h),dt(p,v),dt(p,f)],T=TR.map(t=>t.map(P));
 let u0=1e9,u1=-1e9,v0=1e9,v1=-1e9,z0=1e9,z1=-1e9;
 for(const t of T)for(const p of t){u0=Math.min(u0,p[0]);u1=Math.max(u1,p[0]);v0=Math.min(v0,p[1]);v1=Math.max(v1,p[1]);z0=Math.min(z0,p[2]);z1=Math.max(z1,p[2])}
 const rope=[];objs.filter(o=>o.type=='ph'&&(!w.only||w.only.includes(o.id))).forEach(o=>o.p.segs.forEach(([A_,B_])=>{const a=P(A_),b=P(B_);rope.push([a[0],a[1],b[0],b[1]]);u0=Math.min(u0,a[0],b[0]);u1=Math.max(u1,a[0],b[0]);v0=Math.min(v0,a[1],b[1]);v1=Math.max(v1,a[1],b[1])}));
 const hat=[],byP=new Map();solids().filter(o=>isClaie(o)&&(!w.only||w.only.includes(o.id))).forEach(o=>byP.set(o.par,(byP.get(o.par)||[]).concat(o)));
 byP.forEach(L=>{const[mn,mx]=bounds(L);let a=1e9,b=-1e9,c=1e9,d=-1e9;const hp=[];for(const x of[mn[0],mx[0]])for(const y of[mn[1],mx[1]])for(const z of[mn[2],mx[2]]){const q=P([x,y,z]);hp.push([q[0],q[1]]);a=Math.min(a,q[0]);b=Math.max(b,q[0]);c=Math.min(c,q[1]);d=Math.max(d,q[1])}const hull=()=>{const p=hp.slice().sort((m,n)=>m[0]-n[0]||m[1]-n[1]),cr_=(o,a_,b_)=>(a_[0]-o[0])*(b_[1]-o[1])-(a_[1]-o[1])*(b_[0]-o[0]),lo=[];for(const q of p){while(lo.length>1&&cr_(lo[lo.length-2],lo[lo.length-1],q)<=0)lo.pop();lo.push(q)}const up=[];for(const q of p.slice().reverse()){while(up.length>1&&cr_(up[up.length-2],up[up.length-1],q)<=0)up.pop();up.push(q)}return lo.slice(0,-1).concat(up.slice(0,-1))};hat.push(hull(L));u0=Math.min(u0,a);u1=Math.max(u1,b);v0=Math.min(v0,c);v1=Math.max(v1,d)});
 if(!T.length&&!hat.length&&!rope.length){u0=u1=v0=v1=z0=z1=0}
 const N=640,px=Math.max(u1-u0,v1-v0,1)/(N-2),tol=Math.max(z1-z0,1)*.004+px,Z=new Float32Array(N*N).fill(1e30);
 const Z1=new Float32Array(N*N).fill(1e30),Z2=new Float32Array(N*N).fill(1e30),I1=new Int32Array(N*N).fill(-1);
 T.forEach(([a,b,c],ti)=>{const d=(b[1]-c[1])*(a[0]-c[0])+(c[0]-b[0])*(a[1]-c[1]);if(Math.abs(d)<1e-12)return;const oi=TRo[ti];
  const x0=Math.max(0,Math.floor((Math.min(a[0],b[0],c[0])-u0)/px)),x1=Math.min(N-1,Math.ceil((Math.max(a[0],b[0],c[0])-u0)/px)),y0=Math.max(0,Math.floor((v1-Math.max(a[1],b[1],c[1]))/px)),y1=Math.min(N-1,Math.ceil((v1-Math.min(a[1],b[1],c[1]))/px));
  for(let j=y0;j<=y1;j++)for(let i=x0;i<=x1;i++){const X=u0+(i+.5)*px,Y=v1-(j+.5)*px,l1=((b[1]-c[1])*(X-c[0])+(c[0]-b[0])*(Y-c[1]))/d,l2=((c[1]-a[1])*(X-c[0])+(a[0]-c[0])*(Y-c[1]))/d,l3=1-l1-l2;
   if(l1<-1e-9||l2<-1e-9||l3<-1e-9)continue;const z=l1*a[2]+l2*b[2]+l3*c[2],k=j*N+i;if(z<Z1[k]){if(I1[k]!==oi)Z2[k]=Z1[k];Z1[k]=z;I1[k]=oi}else if(oi!==I1[k]&&z<Z2[k])Z2[k]=z}});
 /* une arête est cachée si une AUTRE pièce se trouve devant elle ; la pièce elle-même ne cache que ses faces arrière (arêtes entre deux faces tournées vers le fond) */
 const hid=(u,vv,z,s)=>{const i=Math.round((u-u0)/px-.5),j=Math.round((v1-vv)/px-.5);let mx=-1e30;for(let dj=-1;dj<=1;dj++)for(let di=-1;di<=1;di++){const ii=i+di,jj=j+dj;if(ii<0||jj<0||ii>=N||jj>=N)continue;const k=jj*N+ii,q=I1[k]===s?Z2[k]:Z1[k];if(q>1e29)return false;mx=Math.max(mx,q)}return mx<z-tol};
 const vis=new Map(),hd=new Map(),pts=new Map(),kf=s=>s.map(q=>Math.round(q*10)).join(',');
 const near=new Map();
 for(const e of EC){if(e.n.length>=2){const d0=dt(e.n[0],f),d1=dt(e.n[1],f);if(!(dt(e.n[0],e.n[1])<.866||d0*d1<-1e-9||((Math.abs(d0)<1e-6||Math.abs(d1)<1e-6)&&Math.abs(d0)+Math.abs(d1)>1e-6)))continue}
  const a=P(e.p),b=P(e.q);if(Math.hypot(a[0]-b[0],a[1]-b[1])<.01)continue;
  const k1=kf([a[0],a[1],b[0],b[1]]),k2=kf([b[0],b[1],a[0],a[1]]),k=near.has(k2)?k2:k1,z=a[2]+b[2],o=near.get(k),sh=e.n.length>=2&&dt(e.n[0],f)>1e-9&&dt(e.n[1],f)>1e-9;if(!o||z<o.z)near.set(k,{a,b,z,s:e.o,sh})}
 for(const{a,b,s,sh}of near.values()){if(sh){const sg=[a[0],a[1],b[0],b[1]];hd.set(kf(sg),sg);continue}const L=Math.hypot(a[0]-b[0],a[1]-b[1]);
  for(const p of[a,b])pts.set(kf([p[0],p[1]]),[p[0],p[1]]);
  const n=Math.max(1,Math.ceil(L/(px*1.5)));let prev=false,cls=null,st=0;
  const flush=t1=>{if(cls===null)return;const m=cls?hd:vis,s=[a[0]+(b[0]-a[0])*st,a[1]+(b[1]-a[1])*st,a[0]+(b[0]-a[0])*t1,a[1]+(b[1]-a[1])*t1];if(Math.hypot(s[2]-s[0],s[3]-s[1])<(st==0&&t1==1?.01:5*px))return;const k1=kf(s),k2=kf([s[2],s[3],s[0],s[1]]);if(!m.has(k1)&&!m.has(k2))m.set(k1,s)};
  for(let i=0;i<=n;i++){const t=i/n,hh=hid(a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t,a[2]+(b[2]-a[2])*t,s);
   if(i>0){const c=n>1&&i==1?hh:n>1&&i==n?prev:prev&&hh;if(cls===null){cls=c;st=(i-1)/n}else if(c!==cls){flush((i-1)/n);cls=c;st=(i-1)/n}}prev=hh}
  flush(1)}
 for(const k of[...hd.keys()])if(vis.has(k))hd.delete(k);
 const cl=[];if(SAX())for(const o of solids())for(const A of axes3(o)){
  if(A.s){const c=P(A.c);cl.push({c:[c[0],c[1]],r:A.r});pts.set(kf(c),[c[0],c[1]]);continue}
  const a=P(A.a),b=P(A.b),L=Math.hypot(a[0]-b[0],a[1]-b[1]),L3=Math.hypot(A.b[0]-A.a[0],A.b[1]-A.a[1],A.b[2]-A.a[2]);
  if(L>L3*.01){cl.push({a:[a[0],a[1]],b:[b[0],b[1]]});[a,b].forEach(q=>pts.set(kf([q[0],q[1]]),[q[0],q[1]]))}
  else{const c=[(a[0]+b[0])/2,(a[1]+b[1])/2];cl.push({c,r:A.r});pts.set(kf(c),c)}}
 Object.assign(w,{hat,rope,segs:[...vis.values()],hsegs:[...hd.values()],cl,pts:[...pts.values()],u0,v1,W:u1-u0,H:v1-v0,cv:ver,hv:SHID(),ax:SAX()});if(w.det)Object.assign(w,{u0:w.det.u,v1:w.det.v+w.det.h,W:w.det.w,H:w.det.h});return w}
function haSVG(w){return(w.hat||[]).map(h=>{const pts=h.map(p=>LP(w,p)),cx=pts.reduce((a,p)=>a+p[0],0)/pts.length,cy=pts.reduce((a,p)=>a+p[1],0)/pts.length;return`<polygon class="ha" points="${pts.map(p=>fx(p[0])+','+fx(p[1])).join(' ')}"/><text class="sl" x="${fx(cx)}" y="${fx(cy)}" text-anchor="middle">claies</text>`}).join('')+((w.rope||[]).length?`<path class="rp" d="${w.rope.map(r=>{const p=LP(w,[r[0],r[1]]),q=LP(w,[r[2],r[3]]);return`M${fx(p[0])} ${fx(p[1])}L${fx(q[0])} ${fx(q[1])}`}).join('')}"/>`:'')}
function clSVG(w){return`<path class="cl" d="${(w.cl||[]).map(c=>{if(c.c){const p=LP(w,c.c),h=c.r*w.s+4;return`M${fx(p[0]-h)} ${fx(p[1])}L${fx(p[0]+h)} ${fx(p[1])}M${fx(p[0])} ${fx(p[1]-h)}L${fx(p[0])} ${fx(p[1]+h)}`}const a=LP(w,c.a),b=LP(w,c.b),l=Math.hypot(b[0]-a[0],b[1]-a[1])||1,d=[(b[0]-a[0])/l,(b[1]-a[1])/l];return`M${fx(a[0]-d[0]*4)} ${fx(a[1]-d[1]*4)}L${fx(b[0]+d[0]*4)} ${fx(b[1]+d[1]*4)}`}).join('')}"/>`}
function toggleAx(){showAx=!showAx;draw();buildRibbon()}
function mkView(k){const w={id:vid++,k,x:0,y:0,s:1};vdata(w);return w}
function addView(k){if(!objs.length)return msg('Créez d’abord des objets en 3D.');
 const w=mkView(k),n=views.length;w.s=n?views[0].s:(NICE.find(s=>w.W*s<=150&&w.H*s<=105)||.001);w.x=35+(n%3)*135;w.y=30+Math.floor(n/3)*105;views.push(w);selV=w;selD=selT=null;draw();drui()}
function autoViews(){if(!objs.length)return msg('Créez d’abord des objets en 3D.');
 views=['front','top','left'].map(mkView);dims=[];selV=selD=selT=null;const[f,t,l]=views,M=Math.max(f.W,f.H,t.H),g0=.3*M;
 const s=NICE.find(s=>(f.W+g0+l.W)*s<=330&&(f.H+g0+t.H)*s<=165)||.001,g=Math.max(24,g0*s);
 views.forEach(w=>w.s=s);f.x=35;f.y=30;t.x=35;t.y=f.y+f.H*s+g;l.x=f.x+f.W*s+g;l.y=f.y;draw();drui()}
function dval(d){if(d.t=='ang'){const q=angInfo(d);return q?q.deg/uk():0}return d.t=='h'?Math.abs(d.b[0]-d.a[0]):d.t=='v'?Math.abs(d.b[1]-d.a[1]):Math.hypot(d.b[0]-d.a[0],d.b[1]-d.a[1])}
const ln=(a,b,c,d,k)=>`<line x1="${fx(a)}" y1="${fx(b)}" x2="${fx(c)}" y2="${fx(d)}" class="${k}"/>`;
function angInfo(d){const I=(p,q,r,s)=>{const x=(p[0]-q[0])*(r[1]-s[1])-(p[1]-q[1])*(r[0]-s[0]);if(Math.abs(x)<1e-9)return null;const a=p[0]*q[1]-p[1]*q[0],b=r[0]*s[1]-r[1]*s[0];return[(a*(r[0]-s[0])-(p[0]-q[0])*b)/x,(a*(r[1]-s[1])-(p[1]-q[1])*b)/x]},X=I(d.a,d.b,d.c,d.e);if(!X)return null;const far=(p,q)=>Math.hypot(p[0]-X[0],p[1]-X[1])>=Math.hypot(q[0]-X[0],q[1]-X[1])?p:q,f1=far(d.a,d.b),f2=far(d.c,d.e),u=nrm([f1[0]-X[0],f1[1]-X[1],0]),v=nrm([f2[0]-X[0],f2[1]-X[1],0]);return{X,u,v,deg:Math.acos(Math.max(-1,Math.min(1,u[0]*v[0]+u[1]*v[1])))*180/Math.PI}}
function dimSVG(d,w,clean){if(d.t=='ang'){const q=angInfo(d);if(!q)return'';const X=LP(w,q.X),u=[q.u[0],-q.u[1]],v=[q.v[0],-q.v[1]],R=14,p1=[X[0]+u[0]*R,X[1]+u[1]*R],p2=[X[0]+v[0]*R,X[1]+v[1]*R],cz=u[0]*v[1]-u[1]*v[0],m=nrm([u[0]+v[0],u[1]+v[1],0]),tx=[X[0]+m[0]*(R+5),X[1]+m[1]*(R+5)];
  return`<g class="dim${!clean&&d===selD?' on':''}" data-d="${d.id}"><path class="d" style="marker-start:none;marker-end:none" d="M${fx(p1[0])} ${fx(p1[1])}A${R} ${R} 0 0 ${cz>0?1:0} ${fx(p2[0])} ${fx(p2[1])}"/><text x="${fx(tx[0])}" y="${fx(tx[1])}" text-anchor="middle">${esc(d.txt||r1(q.deg)+'°')}</text></g>`}
 const A=LP(w,d.a),B=LP(w,d.b),o=d.o;let r='',x1,y1,x2,y2,ang=0;
 if(d.t=='h'){x1=A[0];x2=B[0];y1=y2=o;const sa=o>A[1]?1:-1,sb=o>B[1]?1:-1;r=ln(A[0],A[1]+sa,A[0],o+2*sa,'x')+ln(B[0],B[1]+sb,B[0],o+2*sb,'x')}
 else if(d.t=='v'){y1=A[1];y2=B[1];x1=x2=o;ang=-90;const sa=o>A[0]?1:-1,sb=o>B[0]?1:-1;r=ln(A[0]+sa,A[1],o+2*sa,A[1],'x')+ln(B[0]+sb,B[1],o+2*sb,B[1],'x')}
 else{const dx=B[0]-A[0],dy=B[1]-A[1],l=Math.hypot(dx,dy)||1,n=[-dy/l,dx/l],sg=o>=0?1:-1;x1=A[0]+n[0]*o;y1=A[1]+n[1]*o;x2=B[0]+n[0]*o;y2=B[1]+n[1]*o;
  r=ln(A[0]+n[0]*sg,A[1]+n[1]*sg,x1+n[0]*2*sg,y1+n[1]*2*sg,'x')+ln(B[0]+n[0]*sg,B[1]+n[1]*sg,x2+n[0]*2*sg,y2+n[1]*2*sg,'x');ang=Math.atan2(y2-y1,x2-x1)*180/Math.PI;if(ang>90||ang<-90)ang+=180}
 r+=ln(x1,y1,x2,y2,'d')+ln(x1,y1,x2,y2,'hit');
 const txt=d.txt||((d.pre||'')+r1(dval(d)*uk())+(d.tol?' '+d.tol:''));
 return`<g class="dim${!clean&&d===selD?' on':''}" data-d="${d.id}">${r}<text transform="translate(${fx((x1+x2)/2)} ${fx((y1+y2)/2)}) rotate(${fx(ang)}) translate(0 -1.2)" text-anchor="middle">${esc(txt)}</text></g>`}

let EC=null,TR=[],ECv=-1,views=[],dims=[],texts=[],shots=[],tool='sel',vid=1,did=1,tid=1,sid=1,pend=null,selD=null,selV=null,selT=null,selS=null,selN=false,vb=[0,0,420,297],drag=null,showHid=true,showAx=true;
const meta={titre:'Mon installation',soc:'',des:'',date:new Date().toLocaleDateString('fr-FR'),mat:'',ref:'PL-001',ind:'A',feu:'1/1',ech:''};
let nom={asm:false,show:false,x:14,y:213,mode:'plat',cols:{rep:1,qty:1,des:1,dim:1,ops:0,mat:0},lock:false,anchor:'bl',title:'NOMENCLATURE',sz:3};
const SG=$('#sg'),HINT={sel:'Glissez une vue, un texte, la nomenclature ou une capture pour les déplacer. Cliquez un texte du cartouche pour le modifier. Molette : zoom. Clic droit : options.',dh:'Cote horizontale : cliquez 2 sommets d’une vue, puis la position de la cote.',dv:'Cote verticale : cliquez 2 sommets d’une vue, puis la position de la cote.',dd:'Cote alignée : cliquez 2 sommets d’une vue, puis la position de la cote.',dia:'Cote de diamètre (Ø) : cliquez 2 points opposés d’un cercle, puis la position.',tx:'Cliquez sur la feuille pour poser un texte.'};
const CSSX=CSS+'.nm text{font:2.9px Arial,sans-serif}.nm .h{font-weight:bold}.nm.on rect.fr{stroke:#e08a00}.sh.on rect{stroke:#e08a00}.mc{fill:#fff;fill-opacity:.01;cursor:text}.mc:hover{fill:#2f6fdb;fill-opacity:.12}text.vt{cursor:text}';
const visibleObjs=()=>objs.filter(o=>o.m&&o.m.visible!==false);
/* ----- nomenclature ----- */
function nomRows(){const R=[],C=nom.cols;const row=(g,rep,d)=>({d,cells:{rep,qty:g.n,des:desOf(g.o),dim:descOf(g.o),ops:opsOf(g.o),mat:g.o.mat||''}});
 if(nom.mode=='plat'||nom.only){groups(visibleObjs().filter(o=>!nom.only||nom.only.includes(o.id))).forEach((g,i)=>R.push(row(g,i+1,0)))}
 else{let rep=1;(function walk(par,d){groups(kidsP(par)).forEach(g=>R.push(row(g,rep++,d)));kidsA(par).forEach(a=>{R.push({grp:a.n,d});walk(a.id,d+1)})})(0,0)}
 return R}
const NCOL=[['rep','N°'],['qty','Qté'],['des','Désignation'],['dim','Dimensions'],['ops','Assemblages'],['mat','Essence']];
function nomBuild(){const rows=nomRows(),cols=NCOL.filter(([k])=>nom.cols[k]),f=nom.sz/3,cw=k=>Math.max(NCOL.find(c=>c[0]==k)[1].length,...rows.filter(r=>r.cells).map(r=>String(r.cells[k]).length))*1.75*f+3;
 const W=cols.map(([k])=>cw(k)),w=Math.max(W.reduce((a,b)=>a+b,0),(nom.title.length+2)*2.1*f),rh=nom.sz*1.5;let y=rh,s='';
 const hdr=`<rect x="0" y="0" width="${fx(w)}" height="${fx(rh)}" fill="#e9edf3" stroke="#111" stroke-width=".35"/><text class="h" x="1.5" y="${fx(rh*.72)}" style="font-size:${fx(nom.sz*1.05)}px">${esc(nom.title)}</text>`;
 let x=0;s+=cols.map(([k,l],i)=>{const t=`<text class="h" x="${fx(x+1.2)}" y="${fx(y+rh*.72)}">${esc(l)}</text>`;x+=W[i];return t}).join('')+`<line x1="0" y1="${fx(y+rh)}" x2="${fx(w)}" y2="${fx(y+rh)}" stroke="#111" stroke-width=".3"/>`;y+=rh;
 for(const r of rows){if(r.grp){s+=`<rect x="0" y="${fx(y)}" width="${fx(w)}" height="${fx(rh)}" fill="#f4f1ea"/><text class="h" x="${fx(1.2+r.d*3)}" y="${fx(y+rh*.72)}">▸ ${esc(r.grp)}</text>`}
  else{x=0;s+=cols.map(([k],i)=>{const t=`<text x="${fx(x+1.2+(k=='des'?r.d*3:0))}" y="${fx(y+rh*.72)}">${esc(r.cells[k])}</text>`;x+=W[i];return t}).join('')}
  s+=`<line x1="0" y1="${fx(y+rh)}" x2="${fx(w)}" y2="${fx(y+rh)}" stroke="#bbb" stroke-width=".15"/>`;y+=rh}
 x=0;const vl=cols.slice(0,-1).map(([k],i)=>{x+=W[i];return`<line x1="${fx(x)}" y1="${fx(rh)}" x2="${fx(x)}" y2="${fx(y)}" stroke="#666" stroke-width=".15"/>`}).join('');
 return{w,h:y,svg:`<rect x="0" y="0" width="${fx(w)}" height="${fx(y)}" fill="#fff"/>`+hdr+vl+s+`<rect class="fr" x="0" y="0" width="${fx(w)}" height="${fx(y)}" fill="none" stroke="#111" stroke-width=".5"/>`}}
function nomPlace(b){const A=nom.anchor;if(A=='bl'){nom.x=14;nom.y=283-b.h}else if(A=='br'){nom.x=408-b.w;nom.y=244-b.h}else if(A=='tl'){nom.x=14;nom.y=14}else if(A=='tr'){nom.x=408-b.w;nom.y=14}}
/* ----- feuille ----- */
const ANCH=[['bl','Bas gauche'],['br','Au-dessus du cartouche'],['tl','Haut gauche'],['tr','Haut droite'],['free','Libre']];
function statics(clean){
 let h='<rect width="420" height="297" fill="#fff"/><rect x="5" y="5" width="410" height="287" fill="none" stroke="#111" stroke-width=".35"/><rect x="10" y="10" width="400" height="277" fill="none" stroke="#111" stroke-width=".7"/>';
 const cw=400/9,rh=277/8;
 for(let i=0;i<9;i++){const x=10+cw*i;if(i)h+=ln(x,5,x,10,'z')+ln(x,287,x,292,'z');h+=`<text x="${fx(x+cw/2)}" y="8.6" class="z">${i+1}</text><text x="${fx(x+cw/2)}" y="291.3" class="z">${i+1}</text>`}
 for(let j=0;j<8;j++){const y=10+rh*j,L='ABCDEFGH'[j];if(j)h+=ln(5,y,10,y,'z')+ln(410,y,415,y,'z');h+=`<text x="7.5" y="${fx(y+rh/2+1)}" class="z">${L}</text><text x="412.5" y="${fx(y+rh/2+1)}" class="z">${L}</text>`}
 const X=230,Y=247,cell=(x,y,w,hh,l,v,big,key)=>`<rect x="${x}" y="${y}" width="${w}" height="${hh}" fill="none" stroke="#111" stroke-width=".35"/><text x="${x+1}" y="${y+2.7}" class="sl">${l}</text><text x="${x+1.2}" y="${y+hh-1.8}" class="${big?'t':'sv'}">${esc(v||'')}</text>`+(key&&!clean?`<rect class="mc" data-m="${key}" x="${x}" y="${y}" width="${w}" height="${hh}"/>`:'');
 const ech=meta.ech||(views.length&&views.every(w=>w.s==views[0].s)?scl(views[0].s):views.length?'Indiquée':'');
 h+=`<rect x="${X}" y="${Y}" width="180" height="40" fill="#fff" stroke="#111" stroke-width=".7"/>`+cell(X,Y,125,14,'TITRE',meta.titre,1,'titre')+cell(X+125,Y,55,14,'SOCIÉTÉ',meta.soc,0,'soc')
  +cell(X,Y+14,45,13,'DESSINÉ PAR',meta.des,0,'des')+cell(X+45,Y+14,45,13,'DATE',meta.date,0,'date')+cell(X+90,Y+14,45,13,'ÉCHELLE',ech,0,'ech')+cell(X+135,Y+14,45,13,'MATIÈRE',meta.mat,0,'mat')
  +cell(X,Y+27,45,13,'N° DE PLAN',meta.ref,0,'ref')+cell(X+45,Y+27,30,13,'INDICE',meta.ind,0,'ind')+cell(X+75,Y+27,30,13,'FEUILLE',(curPage+1)+'/'+Math.max(1,pages.length),0)+cell(X+105,Y+27,30,13,'FORMAT','A3')+cell(X+135,Y+27,45,13,'PROJECTION','')
  +`<path d="M${X+146} ${Y+32.5}L${X+156} ${Y+31}V${Y+38}L${X+146} ${Y+36.5}Z" fill="none" stroke="#111" stroke-width=".3"/><circle cx="${X+167}" cy="${Y+34.5}" r="3.4" fill="none" stroke="#111" stroke-width=".3"/><circle cx="${X+167}" cy="${Y+34.5}" r="1.8" fill="none" stroke="#111" stroke-width=".3"/>`;
 return h}
function sheet(clean){let h=statics(clean);{const pg=pages[curPage];if(pg&&pg.bg)h+='<g class="bgsvg">'+pg.bg+'</g>'}
 h+=shots.map(s=>`<g class="sh${!clean&&s===selS?' on':''}" data-s="${s.id}" transform="translate(${fx(s.x)} ${fx(s.y)})"><image href="${s.src}" width="${fx(s.w)}" height="${fx(s.h)}"/><rect x="0" y="0" width="${fx(s.w)}" height="${fx(s.h)}" fill="none" stroke="${!clean&&s===selS?'#e08a00':'#999'}" stroke-width=".3"/>${s.nm?`<text class="t" x="0" y="-1.5">${esc(s.nm)}</text>`:''}</g>`).join('');
 h+=views.map(w=>{vdata(w);const hl=!clean&&w===selV,pth=a=>a.map(g=>{const p=LP(w,[g[0],g[1]]),q=LP(w,[g[2],g[3]]);return`M${fx(p[0])} ${fx(p[1])}L${fx(q[0])} ${fx(q[1])}`}).join('');
  return`<g class="vw" data-id="${w.id}" transform="translate(${fx(w.x)} ${fx(w.y)})">${w.det?`<clipPath id="cpv${w.id}"><rect x="0" y="0" width="${fx(w.W*w.s)}" height="${fx(w.H*w.s)}"/></clipPath>`:''}<rect x="-3" y="-8" width="${fx(w.W*w.s+6)}" height="${fx(w.H*w.s+11)}" fill="#fff" fill-opacity=".01" stroke="${hl?'#2f6fdb':'none'}" stroke-dasharray="2"/><text class="t vt" data-vt="${w.id}" x="0" y="-3">${esc(w.nm||DIRS[w.k][0])} (${scl(w.s)})</text><g${w.det?` clip-path="url(#cpv${w.id})"`:''}><path class="hd" d="${SHID()?pth(w.hsegs):''}"/><path class="e" d="${pth(w.segs)}"/>${clSVG(w)}${haSVG(w)}</g>${dims.filter(d=>d.v==w.id).map(d=>dimSVG(d,w,clean)).join('')}</g>`}).join('');
 if(nom.show&&objs.length){const b=nomBuild();if(nom.anchor!='free')nomPlace(b);nom.bw=b.w;nom.bh=b.h;h+=`<g class="nm${!clean&&selN?' on':''}" data-nm="1" transform="translate(${fx(nom.x)} ${fx(nom.y)})">${b.svg}</g>`}
 if(nom.asm&&objs.length)h+=nomAsmSvg();
  if(!clean&&!views.length&&!shots.length&&!texts.length)h+=`<g class="addv" data-add="1" style="cursor:pointer"><rect x="150" y="95" width="120" height="70" rx="6" fill="#fff" fill-opacity=".01" stroke="#9aa3b0" stroke-width=".6" stroke-dasharray="3 2.5"/><text x="210" y="136" text-anchor="middle" style="font:300 30px sans-serif;fill:#9aa3b0">+</text><text x="210" y="152" text-anchor="middle" style="font:4px sans-serif;fill:#7b8594">Ajouter une projection</text></g>`;
 h+=texts.map(t=>`<text class="tx${!clean&&t===selT?' on':''}" data-t="${t.id}" x="${fx(t.x)}" y="${fx(t.y)}" style="font-size:${t.sz}px">${esc(t.t)}</text>`).join('');return h}
const sheetMade=()=>{ensurePages();const p=pages[curPage];return !!(p.made||views.length||shots.length||texts.length)};
function draw(){ensurePages();pgbar();if(!sheetMade()){SG.innerHTML=`<style>${CSSX}</style><g data-newsheet="1" style="cursor:pointer"><rect x="125" y="88" width="170" height="110" rx="10" fill="#fff" fill-opacity=".01" stroke="#9aa3b0" stroke-width=".7" stroke-dasharray="4 3"/><text x="210" y="142" text-anchor="middle" style="font:300 38px sans-serif;fill:#9aa3b0">+</text><text x="210" y="165" text-anchor="middle" style="font:600 6px sans-serif;fill:#6b7280">Créer une feuille</text><text x="210" y="175" text-anchor="middle" style="font:4px sans-serif;fill:#8a93a3">A3 avec cartouche ; ajoutez-y ensuite des projections</text></g><g id="go"></g>`;return}SG.innerHTML=`<style>${CSSX}</style>${DEFS}${sheet(false)}<g id="go"></g>`}
const svgDoc=()=>`<svg xmlns="http://www.w3.org/2000/svg" width="420mm" height="297mm" viewBox="0 0 420 297"><style>${CSSX}</style>${DEFS}${sheet(true)}</svg>`;
const pt=e=>{const q=SG.createSVGPoint();q.x=e.clientX;q.y=e.clientY;const r=q.matrixTransform(SG.getScreenCTM().inverse());return[r.x,r.y]};
function snap(p){let best=null,bd=8/SG.getScreenCTM().a;for(const w of views)for(const q of w.pts){const g=SP(w,q),d=Math.hypot(g[0]-p[0],g[1]-p[1]);if(d<bd){bd=d;best={w,q,g}}}return best}
function snapEdge(p){let best=null,bd=6/SG.getScreenCTM().a;for(const w of views)for(const g of w.segs||[]){const A=SP(w,[g[0],g[1]]),B=SP(w,[g[2],g[3]]),vx=B[0]-A[0],vy=B[1]-A[1],l2=vx*vx+vy*vy||1,t=Math.max(0,Math.min(1,((p[0]-A[0])*vx+(p[1]-A[1])*vy)/l2)),d=Math.hypot(A[0]+vx*t-p[0],A[1]+vy*t-p[1]);if(d<bd){bd=d;best={w,a:[g[0],g[1]],b:[g[2],g[3]],g}}}if(best)mergeEdge(best);return best}
function mergeEdge(E){const g=E.g,dx=g[2]-g[0],dy=g[3]-g[1],L=Math.hypot(dx,dy)||1,ux=dx/L,uy=dy/L,eps=Math.max(.5,L*.001),iv=[];for(const s of E.w.segs){const d1=Math.abs((s[0]-g[0])*uy-(s[1]-g[1])*ux),d2=Math.abs((s[2]-g[0])*uy-(s[3]-g[1])*ux);if(d1<eps&&d2<eps){const t1=(s[0]-g[0])*ux+(s[1]-g[1])*uy,t2=(s[2]-g[0])*ux+(s[3]-g[1])*uy;iv.push([Math.min(t1,t2),Math.max(t1,t2)])}}iv.sort((a,b)=>a[0]-b[0]);let lo=0,hi=L;let ch=true;while(ch){ch=false;for(const v of iv){if(v[0]<=hi+eps&&v[1]>hi+eps){hi=v[1];ch=true}if(v[1]>=lo-eps&&v[0]<lo-eps){lo=v[0];ch=true}}}E.a=[g[0]+ux*lo,g[1]+uy*lo];E.b=[g[0]+ux*hi,g[1]+uy*hi]}
function offs(d,lp){const w=d.w,A=LP(w,d.a),B=LP(w,d.b);if(d.t=='h')return lp[1];if(d.t=='v')return lp[0];const l=Math.hypot(B[0]-A[0],B[1]-A[1])||1;return(-(B[1]-A[1])*(lp[0]-A[0])+(B[0]-A[0])*(lp[1]-A[1]))/l}
function ov(p){const g=SG.querySelector('#go');if(!g)return;const hov=p&&tool!='sel'&&tool!='tx'?snap(p):null;let h='';
 if(p&&tool!='tx'&&tool!='det'&&!(pend&&pend.b)&&!hov){const E=snapEdge(p);if(E){const A=SP(E.w,E.a),B=SP(E.w,E.b);h+=`<line x1="${fx(A[0])}" y1="${fx(A[1])}" x2="${fx(B[0])}" y2="${fx(B[1])}" stroke="#e08a00" stroke-width=".8" stroke-linecap="round" pointer-events="none"/>`}}
 if(hov)h+=`<circle cx="${fx(hov.g[0])}" cy="${fx(hov.g[1])}" r="1.6" fill="none" stroke="#e08a00" stroke-width=".4"/>`;
 if(pend&&!pend.ang&&!pend.det){const w=pend.w;h+=`<g transform="translate(${fx(w.x)} ${fx(w.y)})" class="pv">`+(pend.b&&p?dimSVG({t:pend.t,pre:pend.pre,a:pend.a,b:pend.b,o:offs(pend,[p[0]-w.x,p[1]-w.y])},w,true):'')+[pend.a,pend.b].filter(Boolean).map(q=>{const l=LP(w,q);return`<circle cx="${fx(l[0])}" cy="${fx(l[1])}" r="1" fill="#e08a00"/>`}).join('')+'</g>'}
 g.innerHTML=h}
/* ----- zoom et déplacement limités : la feuille reste toujours visible ----- */
function clampVB(){const asp=297/420;let w=Math.max(60,Math.min(560,vb[2]));vb[3]=w*asp;vb[2]=w;vb[0]=Math.max(-w*.7,Math.min(420-w*.3,vb[0]));vb[1]=Math.max(-vb[3]*.7,Math.min(297-vb[3]*.3,vb[1]));SG.setAttribute('viewBox',vb.join(' '))}
function fitSheet(){vb=[0,0,420,297];SG.setAttribute('viewBox',vb.join(' '))}
SG.addEventListener('wheel',e=>{e.preventDefault();const p=pt(e),k=e.deltaY>0?1.15:1/1.15;vb=[p[0]-(p[0]-vb[0])*k,p[1]-(p[1]-vb[1])*k,vb[2]*k,vb[3]*k];clampVB()},{passive:false});
/* ----- édition directe des textes ----- */
function editAt(el,val,cb){const r=el.getBoundingClientRect(),ed=$('#ed');ed.style.display='block';ed.style.left=r.left+'px';ed.style.top=r.top+'px';ed.style.width=Math.max(r.width,140)+'px';ed.style.height=Math.max(r.height,26)+'px';ed.value=val;ed.focus();ed.select();let done=false;
 const fin=ok=>{if(done)return;done=true;ed.style.display='none';ed.onkeydown=ed.onblur=null;if(ok)cb(ed.value)};ed.onkeydown=e=>{e.stopPropagation();if(e.key=='Enter')fin(1);if(e.key=='Escape')fin(0)};ed.onblur=()=>fin(1)}
function editMeta(key,el){editAt(el,key=='ech'?(meta.ech):meta[key],v=>{meta[key]=v;draw();drui();touch()})}
/* ----- événements de la feuille ----- */
SG.onpointerdown=e=>{if(e.button==2)return;if(e.target.closest&&e.target.closest('[data-newsheet]')){pages[curPage].made=true;planOn=true;draw();drui();vbarBuild();msg('Feuille créée : ajoutez une projection avec le bouton +.');return}if(e.target.closest&&e.target.closest('[data-add]')){projWin();return}const p=pt(e);hideCm();
 if(tool=='sel'){const mc=e.target.closest('.mc');if(mc){e.preventDefault();return editMeta(mc.dataset.m,mc)}
  const dg=e.target.closest('.dim'),tg=e.target.closest('.tx'),vg=e.target.closest('.vw'),nm=e.target.closest('.nm'),sh=e.target.closest('.sh');selV=selD=selT=selS=null;selN=false;
  if(dg)selD=dims.find(d=>d.id==dg.dataset.d);
  else if(tg){selT=texts.find(t=>t.id==tg.dataset.t);drag={t:selT,dx:p[0]-selT.x,dy:p[1]-selT.y}}
  else if(nm){selN=true;if(!nom.lock)drag={n:1,dx:p[0]-nom.x,dy:p[1]-nom.y}}
  else if(sh){selS=shots.find(s=>s.id==sh.dataset.s);drag={s:selS,dx:p[0]-selS.x,dy:p[1]-selS.y}}
  else if(vg){selV=views.find(v=>v.id==vg.dataset.id);drag={w:selV,dx:p[0]-selV.x,dy:p[1]-selV.y}}
  else drag={pan:1,px:e.clientX,py:e.clientY,vb:[...vb],k:1/SG.getScreenCTM().a};
  SG.setPointerCapture(e.pointerId);draw();drui();return}
 if(tool=='tx'){texts.push({id:tid++,x:p[0],y:p[1],t:'Texte',sz:3.5});selT=texts[texts.length-1];setTool('sel');draw();drui();touch();return}
 /* cote entre deux arêtes parallèles : 1re arête choisie, puis clic sur une 2e arête parallèle */
 if(pend&&pend.edge&&!snap(p)){const E=snapEdge(p);if(E&&E.w===pend.w&&!(Math.hypot(E.a[0]-pend.edge.a[0],E.a[1]-pend.edge.a[1])<.01&&Math.hypot(E.b[0]-pend.edge.b[0],E.b[1]-pend.edge.b[1])<.01)){const u1=[pend.edge.b[0]-pend.edge.a[0],pend.edge.b[1]-pend.edge.a[1]],u2=[E.b[0]-E.a[0],E.b[1]-E.a[1]],l1=Math.hypot(...u1)||1,l2=Math.hypot(...u2)||1;
  if(Math.abs(u1[0]*u2[1]-u1[1]*u2[0])/(l1*l2)<.035){const m=[(pend.edge.a[0]+pend.edge.b[0])/2,(pend.edge.a[1]+pend.edge.b[1])/2],t2=((m[0]-E.a[0])*u2[0]+(m[1]-E.a[1])*u2[1])/(l2*l2),f=[E.a[0]+u2[0]*t2,E.a[1]+u2[1]*t2];pend.a=m;pend.b=f;delete pend.edge;msg('Distance entre les deux arêtes : cliquez pour placer la cote.');ov(p);return}}}
 if(pend&&pend.b){const w=pend.w;dims.push({id:did++,v:w.id,t:pend.t,pre:pend.pre,a:pend.a,b:pend.b,o:offs(pend,[p[0]-w.x,p[1]-w.y])});pend=null;draw();drui();touch();return}
 if(tool=='det'){const w=views.find(v=>p[0]>=v.x&&p[0]<=v.x+v.W*v.s&&p[1]>=v.y&&p[1]<=v.y+v.H*v.s);if(!w)return msg('Tracez le cadre à agrandir sur une vue (glisser).');pend={det:1,w,p0:p};SG.setPointerCapture(e.pointerId);return}
 if(tool=='ang'){const E=snapEdge(p);if(!E)return msg('Cliquez une première droite (arête), puis une seconde.');if(!pend)pend={ang:1,w:E.w,l1:E};else{if(E.w!==pend.w)return msg('Les deux droites doivent être sur la même vue.');dims.push({id:did++,v:E.w.id,t:'ang',a:pend.l1.a,b:pend.l1.b,c:E.a,e:E.b,o:0});pend=null;draw();drui();touch()}return}
 const s=snap(p);
 if(!s&&!pend){const E=snapEdge(p);if(E){const dx=Math.abs(E.b[0]-E.a[0]),dy=Math.abs(E.b[1]-E.a[1]),t=tool=='dh'?'h':tool=='dv'?'v':(tool=='dd'||tool=='dia')?'d':dy<dx*.05?'h':dx<dy*.05?'v':'d';pend={w:E.w,t,pre:tool=='dia'?'Ø':'',a:E.a,b:E.b,edge:{a:E.a,b:E.b}};msg('Cliquez pour placer la cote, ou cliquez une 2e arête parallèle pour coter l’écart entre les deux.',5000);ov(p);return}}
 if(!s)return msg('Cliquez sur une arête (ou près d’un sommet) du dessin.');
 if(!pend)pend={w:s.w,t:{dh:'h',dv:'v',dd:'d',dia:'d'}[tool]||'d',pre:tool=='dia'?'Ø':'',a:s.q};else{if(s.w!==pend.w)return msg('Les deux points doivent être sur la même vue.');pend.b=s.q}ov(p)};
SG.onpointermove=e=>{const p=pt(e);
 if(drag){if(drag.pan){vb[0]=drag.vb[0]-(e.clientX-drag.px)*drag.k;vb[1]=drag.vb[1]-(e.clientY-drag.py)*drag.k;clampVB()}
  else if(drag.t){const t=drag.t;t.x=p[0]-drag.dx;t.y=p[1]-drag.dy;const g=SG.querySelector('.tx[data-t="'+t.id+'"]');if(g){g.setAttribute('x',fx(t.x));g.setAttribute('y',fx(t.y))}}
  else if(drag.n){nom.anchor='free';nom.x=p[0]-drag.dx;nom.y=p[1]-drag.dy;const g=SG.querySelector('.nm');if(g)g.setAttribute('transform',`translate(${fx(nom.x)} ${fx(nom.y)})`)}
  else if(drag.s){const s=drag.s;s.x=p[0]-drag.dx;s.y=p[1]-drag.dy;const g=SG.querySelector('.sh[data-s="'+s.id+'"]');if(g)g.setAttribute('transform',`translate(${fx(s.x)} ${fx(s.y)})`)}
  else{const w=drag.w;w.x=p[0]-drag.dx;w.y=p[1]-drag.dy;const g=SG.querySelector('.vw[data-id="'+w.id+'"]');if(g)g.setAttribute('transform',`translate(${fx(w.x)} ${fx(w.y)})`)}return}
 ov(p)};
SG.onpointerup=e=>{if(pend&&pend.det){const w=pend.w,p=pt(e),q=a=>[(a[0]-w.x)/w.s+w.u0,w.v1-(a[1]-w.y)/w.s],A=q(pend.p0),Bq=q(p),u=Math.min(A[0],Bq[0]),v=Math.min(A[1],Bq[1]),ww=Math.abs(A[0]-Bq[0]),hh=Math.abs(A[1]-Bq[1]);pend=null;if(ww*w.s<4||hh*w.s<4){return msg('Cadre trop petit : glissez sur la zone à agrandir.')}
  const nv=mkView(w.k,w.only);nv.det={u,v,w:ww,h:hh};nv.cv=-1;vdata(nv);const raw=Math.min(150/ww,105/hh),f=[2,3,4,5,8,10,15,20,30,50].filter(f=>w.s*f<=raw).pop()||2;nv.s=w.s*f;nv.nm='Détail ×'+f;nv.x=Math.min(260,w.x+w.W*w.s+10);nv.y=Math.max(30,w.y+w.H*w.s*.5);views.push(nv);setTool('sel');selV=nv;draw();drui();touch();return}
 if(drag&&drag.w)drag.w.moved=true;if(drag&&!drag.pan){drui();touch()}drag=null};
SG.ondblclick=e=>{const tg=e.target.closest('.tx'),vt=e.target.closest('.vt'),dg=e.target.closest('.dim');
 if(tg){const t=texts.find(x=>x.id==tg.dataset.t);editAt(tg,t.t,v=>{t.t=v;draw();drui();touch()})}
 else if(vt){const w=views.find(x=>x.id==vt.dataset.vt);editAt(vt,w.nm||DIRS[w.k][0],v=>{w.nm=v;draw();drui();touch()})}
 else if(dg){const d=dims.find(x=>x.id==dg.dataset.d);editAt(dg.querySelector('text'),d.txt||((d.pre||'')+r1(dval(d)*uk())),v=>{d.txt=v;draw();drui();touch()})}}
SG.addEventListener('contextmenu',e=>{e.preventDefault();if(tool!='sel'){pend=null;setTool('sel');return}ctxSheet(e)});
function ctxSheet(e){const T=e.target,mc=T.closest('.mc'),dg=T.closest('.dim'),tg=T.closest('.tx'),vg=T.closest('.vw'),nm=T.closest('.nm'),sh=T.closest('.sh');let items;
 const adds=[{l:'Vue de face',ic:'view',fn:()=>addView('front')},{l:'Vue de dessus',ic:'view',fn:()=>addView('top')},{l:'Vue de gauche',ic:'view',fn:()=>addView('left')},{l:'Vue isométrique',ic:'view',fn:()=>addView('iso')},{l:'Capture de la vue 3D',ic:'cam',fn:addShot},{l:'Nomenclature',ic:'nom',fn:()=>{nom.show=true;draw();buildRibbon()}},{l:'Texte',ic:'txt',fn:()=>setTool('tx')}];
 selV=selD=selT=selS=null;selN=false;
 if(mc){const k=mc.dataset.m;items=[{hd:'Cartouche'},{l:'Modifier cette case',ic:'txt',fn:()=>editMeta(k,mc)},{l:'Vider',fn:()=>{meta[k]='';draw();drui();touch()}}]}
 else if(dg){const d=dims.find(x=>x.id==dg.dataset.d);selD=d;items=[{hd:'Cote'},{l:'Modifier le texte',ic:'txt',fn:()=>editAt(dg.querySelector('text'),d.txt||((d.pre||'')+r1(dval(d)*uk())),v=>{d.txt=v;draw();drui();touch()})},{l:'Préfixe Ø',fn:()=>{d.pre='Ø';draw();touch()}},{l:'Préfixe R',fn:()=>{d.pre='R';draw();touch()}},{l:'Retirer le texte imposé',fn:()=>{d.txt='';draw();touch()}},{sep:1},{l:'Supprimer',ic:'del',fn:delDraw}]}
 else if(tg){const t=texts.find(x=>x.id==tg.dataset.t);selT=t;items=[{hd:'Texte'},{l:'Modifier',ic:'txt',fn:()=>editAt(tg,t.t,v=>{t.t=v;draw();drui();touch()})},{l:'Plus grand',fn:()=>{t.sz*=1.25;draw();touch()}},{l:'Plus petit',fn:()=>{t.sz/=1.25;draw();touch()}},{sep:1},{l:'Supprimer',ic:'del',fn:delDraw}]}
 else if(nm){selN=true;items=[{hd:'Nomenclature'},{l:'Paramètres…',ic:'bom',fn:nomDlg},{l:nom.lock?'Déverrouiller':'Verrouiller la position',fn:()=>{nom.lock=!nom.lock;drui();touch()}},{l:'Placer',sub:ANCH.map(([k,l])=>({l,fn:()=>{nom.anchor=k;draw();drui();touch()}}))},{l:'Par assemblage (arborescence)',fn:()=>{nom.mode='arbo';draw();drui();touch()}},{l:'Liste groupée',fn:()=>{nom.mode='plat';draw();drui();touch()}},{sep:1},{l:'Masquer',ic:'del',fn:toggleNom}]}
 else if(sh){const s=shots.find(x=>x.id==sh.dataset.s);selS=s;items=[{hd:'Capture 3D'},{l:'Recapturer la vue 3D actuelle',ic:'cam',fn:()=>{const c=snap3D();s.src=c.src;s.h=s.w*c.h/c.w;draw();touch()}},{l:'Plus grande',fn:()=>{s.w*=1.2;s.h*=1.2;draw();touch()}},{l:'Plus petite',fn:()=>{s.w/=1.2;s.h/=1.2;draw();touch()}},{l:'Titre…',fn:()=>dlg('Titre de la capture',[{k:'n',l:'Titre',t:'txt',v:s.nm||''}],v=>{s.nm=v.n;draw();touch()})},{sep:1},{l:'Supprimer',ic:'del',fn:delDraw}]}
 else if(vg){const w=views.find(x=>x.id==vg.dataset.id);selV=w;items=[{hd:'Vue « '+(w.nm||DIRS[w.k][0])+' »'},{l:'Échelle…',fn:()=>dlg('Échelle de la vue',[{k:'s',l:'Échelle (1:n ou n:1)',t:'txt',v:scl(w.s)}],v=>{setScale(v.s)})},{l:'Renommer…',ic:'txt',fn:()=>dlg('Titre de la vue',[{k:'n',l:'Titre',t:'txt',v:w.nm||DIRS[w.k][0]}],v=>{w.nm=v.n;draw();touch()})},{l:'Cote horizontale',ic:'dh',fn:()=>setTool('dh')},{l:'Cote verticale',ic:'dv',fn:()=>setTool('dv')},{l:'Cote alignée',ic:'dd',fn:()=>setTool('dd')},{l:'Cote de diamètre',ic:'dia',fn:()=>setTool('dia')},{sep:1},{l:'Supprimer la vue',ic:'del',fn:delDraw}]}
 else items=[{hd:'Ajouter à la feuille'},...adds,{sep:1},{l:'Disposition automatique',ic:'plan',fn:autoViews},{l:'Cadrer la feuille',ic:'fit',fn:fitSheet},{l:showHid?'Masquer les traits cachés':'Afficher les traits cachés',ic:'hid',fn:toggleHid}];
 draw();drui();showCm(e.clientX,e.clientY,items)}
/* ----- capture de la vue 3D ----- */
function snap3D(){const oldBg=sc.background,g=GZ.visible,gv=[gr.visible,gr2.visible,axh.visible],W=1500,Hh=Math.round(W/vpA),oa=camP.aspect,otop=camO.top;
 sc.background=new THREE.Color(0xffffff);GZ.visible=false;gr.visible=gr2.visible=axh.visible=false;objs.forEach(o=>o.m.material.emissive.set(0));
 R.setPixelRatio(1);R.setSize(W,Hh,false);camP.aspect=vpA;camP.updateProjectionMatrix();camO.left=-camO.top*vpA;camO.right=camO.top*vpA;camO.updateProjectionMatrix();
 R.autoClear=true;R.render(sc,cam);const src=R.domElement.toDataURL('image/png');
 sc.background=oldBg;GZ.visible=g;[gr.visible,gr2.visible,axh.visible]=gv;R.setPixelRatio(Math.min(devicePixelRatio||1,2));rs();emi();return{src,w:W,h:Hh}}
function addShot(){if(!solids().length)return msg('Créez d’abord des pièces en 3D.');const c=snap3D(),w=130;shots.push({id:sid++,x:265-shots.length*6,y:30+shots.length*8,w,h:w*c.h/c.w,src:c.src,nm:'Vue 3D'});selS=shots[shots.length-1];draw();drui();touch();msg('Capture ajoutée : déplacez-la sur la feuille. Elle montre le modèle tel qu’il est affiché en 3D.')}
const toggleNom=()=>{nom.show=!nom.show;draw();drui();buildRibbon();touch()};
function nomDlg(){selN=true;nom.show=true;draw();drui();msg('Paramètres de la nomenclature dans le panneau de gauche.')}
function mkView(k,only){const w={id:vid++,k,x:0,y:0,s:1,only:only||null};vdata(w);return w}
function addView(k){if(!solids().length)return msg('Créez d’abord des pièces en 3D.');
 const w=mkView(k),n=views.length;w.s=n?views[0].s:(NICE.find(s=>w.W*s<=150&&w.H*s<=105)||.001);w.x=35+(n%3)*135;w.y=30+Math.floor(n/3)*105;views.push(w);selV=w;selD=selT=null;draw();drui();touch()}
function layout4(only){const vs=['front','top','left','iso'].map(k=>mkView(k,only)),[f,t,l,iso]=vs,g=18,H1=Math.max(f.H,l.H,iso.H),s=NICE.find(s=>(f.W+l.W+iso.W)*s+2*g<=345&&(H1+t.H)*s+g<=200)||.001;
 vs.forEach(w=>w.s=s);f.x=35;f.y=30;l.x=f.x+f.W*s+g;l.y=30;iso.x=l.x+l.W*s+g;iso.y=30;t.x=35;t.y=30+H1*s+g;return vs}
function autoViews(){if(!solids().length)return msg('Créez d’abord des pièces en 3D.');ensurePages();pages[curPage].made=true;views=layout4(null);layoutStd();dims=[];selV=selD=selT=null;draw();drui();touch()}
/* une feuille « Installation » (ensemble) + une feuille de détail par assemblage, chacune à son échelle */
function autoPages(){if(!solids().length)return msg('Créez d’abord des pièces en 3D.');
 const top=Object.values(asms).filter(a=>!a.par&&piecesOf(a.id).some(o=>!GL.includes(o.type)));
 autoViews();ensurePages();pages[curPage].name='Installation';
 const fill=(only,name)=>{savePage();pages.push({name,views:[],dims:[],texts:[],shots:[],nom:{...newNom(),show:typeof expert!='undefined'&&!!expert,only}});loadPage(pages.length-1);views=layout4(only);draw();drui()};
 if(top.length>1||(top.length==1&&solids().length>piecesOf(top[0].id).length))top.forEach(a=>fill(piecesOf(a.id).map(o=>o.id),a.n));
 loadPage(0);touch();msg(pages.length>1?'Feuille Installation + '+(pages.length-1)+' feuilles de détail créées (échelles adaptées à chaque élément).':'Feuille créée.')}
function setTool(t){tool=t;pend=null;SG.style.cursor=t=='sel'?'default':'crosshair';buildRibbon();drui();ov()}
function setScale(txt){const m=/^\s*([\d.]+)\s*:\s*([\d.]+)\s*$/.exec(txt);if(!m||!selV||!(+m[1]>0&&+m[2]>0))return msg('Format : 1:5 ou 2:1');selV.s=m[1]/m[2];draw();drui();touch()}
function toggleHid(){showHid=!showHid;draw();buildRibbon()}
function delDraw(){if(selD){dims=dims.filter(d=>d!==selD);selD=null}else if(selT){texts=texts.filter(t=>t!==selT);selT=null}else if(selS){shots=shots.filter(s=>s!==selS);selS=null}else if(selV){dims=dims.filter(d=>d.v!=selV.id);views=views.filter(v=>v!==selV);selV=null}else if(selN){nom.show=false;selN=false}else return msg('Sélectionnez une vue, une cote, un texte ou une capture.');draw();drui();touch()}
function drui(){
 const it=(on,fn,ico,l)=>`<div class="it${on?' on':''}" onclick="${fn};draw();drui()">${ic(ico,16)}<span class="nm">${esc(l)}</span></div>`;
 const dItem=d=>it(d===selD,`selDraw('d',${d.id})`,{h:'dh',v:'dv',d:'dd',ang:'ang'}[d.t]||'dd',(d.pre||'')+(d.t=='ang'?r1(dval(d)*uk())+'°':r1(dval(d)*uk())+' '+us())).replace('class="it','style="padding-left:26px" class="it');
 $('#ls').innerHTML=!sheetMade()?'<h4>Contenu de la feuille</h4><p class="mu">Aucune feuille : cliquez « + Créer une feuille » au centre.</p>':'<h4>Contenu de la feuille</h4>'+views.map(w=>it(w===selV,`selDraw('v',${w.id})`,'view',(w.nm||DIRS[w.k][0])+' ('+scl(w.s)+')')+dims.filter(d=>d.v==w.id).map(dItem).join('')).join('')+shots.map(s=>it(s===selS,`selDraw('s',${s.id})`,'cam',s.nm||'Capture 3D')).join('')+(nom.show?it(selN,`selDraw('n')`,'nom','Nomenclature'):'')
  +dims.filter(d=>!views.some(w=>w.id==d.v)).map(dItem).join('')+texts.map(t=>it(t===selT,`selDraw('t',${t.id})`,'txt',t.t)).join('')||'<p class="mu">Feuille vide : cliquez le + au centre pour ajouter une projection.</p>';
 if(!sheetMade()){$('#pr').innerHTML='';return}
 let h=`<p class="mu">${HINT[tool]}</p>`;
 if(selV)h+=`<h4>Vue</h4><label>Titre<input value="${esc(selV.nm||DIRS[selV.k][0])}" oninput="selV.nm=this.value;draw()"></label><label>Échelle (1:n ou n:1)<input value="${scl(selV.s)}" onchange="setScale(this.value)"></label><div class="r"><label>X (mm)<input type="number" value="${r1(selV.x)}" onchange="selV.x=+this.value;draw()"></label><label>Y (mm)<input type="number" value="${r1(selV.y)}" onchange="selV.y=+this.value;draw()"></label></div>`;
 if(selS)h+=`<h4>Capture 3D</h4><label>Titre<input value="${esc(selS.nm||'')}" oninput="selS.nm=this.value;draw()"></label><label>Largeur (mm)<input type="number" value="${r1(selS.w)}" onchange="selS.h=selS.h/selS.w*(+this.value||selS.w);selS.w=+this.value||selS.w;draw()"></label><button onclick="const c=snap3D();selS.src=c.src;selS.h=selS.w*c.h/c.w;draw()">Recapturer la vue 3D actuelle</button>`;
 if(selD)h+=`<h4>Cote</h4><label>Préfixe (Ø, R, M…)<input value="${esc(selD.pre||'')}" oninput="selD.pre=this.value;draw()"></label><label>Tolérance (ex. ±0,1)<input value="${esc(selD.tol||'')}" oninput="selD.tol=this.value;draw()"></label><label>Texte imposé (remplace la valeur)<input value="${esc(selD.txt||'')}" oninput="selD.txt=this.value;draw()"></label>`;
 if(selT)h+=`<h4>Texte</h4><label>Contenu<input value="${esc(selT.t)}" oninput="selT.t=this.value;draw()"></label><label>Hauteur (mm)<input type="number" value="${selT.sz}" oninput="selT.sz=+this.value||3.5;draw()"></label>`;
 if(selN||!selV&&!selS&&!selD&&!selT)h+=`<h4>Nomenclature</h4><label class="ck"><input type="checkbox" ${nom.show?'checked':''} onchange="nom.show=this.checked;draw();drui();buildRibbon()"> Afficher la nomenclature des pièces</label><label class="ck"><input type="checkbox" ${nom.asm?'checked':''} onchange="nom.asm=this.checked;draw();drui()"> Afficher la nomenclature des assemblages (tenons, mi-bois…)</label><label>Titre<input value="${esc(nom.title)}" oninput="nom.title=this.value;draw()"></label><label>Présentation<select onchange="nom.mode=this.value;draw()"><option value="plat"${nom.mode=='plat'?' selected':''}>Liste groupée</option><option value="arbo"${nom.mode=='arbo'?' selected':''}>Par assemblage (arborescence)</option></select></label>
  <div class="r" style="flex-wrap:wrap">${NCOL.map(([k,l])=>`<label class="ck" style="min-width:45%"><input type="checkbox" ${nom.cols[k]?'checked':''} onchange="nom.cols['${k}']=this.checked;draw()"> ${l}</label>`).join('')}</div>
  <label>Taille du texte (mm)<input type="number" step=".5" min="1.5" max="6" value="${nom.sz}" oninput="nom.sz=Math.max(1.5,Math.min(6,+this.value||3));draw()"></label><label>Position<select onchange="nom.anchor=this.value;draw();drui()">${ANCH.map(([k,l])=>`<option value="${k}"${nom.anchor==k?' selected':''}>${l}</option>`).join('')}</select></label><label class="ck"><input type="checkbox" ${nom.lock?'checked':''} onchange="nom.lock=this.checked"> Verrouiller (ne plus déplacer à la souris)</label>`;
 h+='<h4>Cartouche</h4><p class="mu">Cliquez directement un texte du cartouche sur la feuille, ou saisissez ici.</p>'+[['titre','Titre'],['soc','Société'],['des','Dessiné par'],['date','Date'],['mat','Matière'],['ref','N° de plan'],['ind','Indice'],['feu','Feuille'],['ech','Échelle (vide = auto)']].map(([k,l])=>`<label>${l}<input value="${esc(meta[k])}" oninput="meta.${k}=this.value;draw()"></label>`).join('');
 $('#pr').innerHTML=h}
function selDraw(t,id){selV=selD=selT=selS=null;selN=false;if(t=='v')selV=views.find(x=>x.id==id);else if(t=='s')selS=shots.find(x=>x.id==id);else if(t=='n')selN=true;else if(t=='d')selD=dims.find(x=>x.id==id);else selT=texts.find(x=>x.id==id)}
/* ----- exports du plan ----- */
function dlSVG(){if(!views.length&&!shots.length)return msg('Aucune vue sur la feuille.');save('plan.svg',svgDoc(),'image/svg+xml')}
async function svgCanvas(svg,px=3307){const url=URL.createObjectURL(new Blob([svg],{type:'image/svg+xml'})),img=new Image();await new Promise((ok,ko)=>{img.onload=ok;img.onerror=()=>ko(new Error('Rendu du plan impossible'));img.src=url});
 const c=document.createElement('canvas');c.width=px;c.height=Math.round(px*297/420);const x=c.getContext('2d');x.fillStyle='#fff';x.fillRect(0,0,c.width,c.height);x.drawImage(img,0,0,c.width,c.height);URL.revokeObjectURL(url);return c}
const sheetCanvas=px=>svgCanvas(svgDoc(),px);
const toBlob=(c,t,q)=>new Promise(ok=>c.toBlob(ok,t,q));
function pdfFromJpegs(P,pw,ph){const enc=new TextEncoder(),parts=[],offs=[];let pos=0;const push=b=>{if(typeof b=='string')b=enc.encode(b);parts.push(b);pos+=b.length},obj=(n,body)=>{offs[n]=pos;push(`${n} 0 obj\n${body}\nendobj\n`)};const N=P.length;
 push('%PDF-1.4\n%âãÏÓ\n');obj(1,'<< /Type /Catalog /Pages 2 0 R >>');obj(2,`<< /Type /Pages /Kids [${P.map((_,i)=>(3+i*3)+' 0 R').join(' ')}] /Count ${N} >>`);
 P.forEach((p,i)=>{const pg=3+i*3,im=pg+1,ct=pg+2;obj(pg,`<< /Type /Page /Parent 2 0 R /MediaBox [0 0 ${pw} ${ph}] /Resources << /XObject << /Im${i} ${im} 0 R >> >> /Contents ${ct} 0 R >>`);
  offs[im]=pos;push(`${im} 0 obj\n<< /Type /XObject /Subtype /Image /Width ${p.w} /Height ${p.h} /ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode /Length ${p.u.length} >>\nstream\n`);push(p.u);push('\nendstream\nendobj\n');
  const cs=`q ${pw} 0 0 ${ph} 0 0 cm /Im${i} Do Q`;obj(ct,`<< /Length ${cs.length} >>\nstream\n${cs}\nendstream`)});
 const xr=pos,tot=3+N*3;push(`xref\n0 ${tot}\n0000000000 65535 f \n`+[...Array(tot-1)].map((_,i)=>String(offs[i+1]).padStart(10,'0')+' 00000 n \n').join('')+`trailer\n<< /Size ${tot} /Root 1 0 R >>\nstartxref\n${xr}\n%%EOF\n`);return new Blob(parts,{type:'application/pdf'})}
const pdfFromJpeg=(jpg,w,h,pw,ph)=>pdfFromJpegs([{u:jpg,w,h}],pw,ph);
const allDocs=()=>{savePage();return pages.map((_,i)=>withPage(i,svgDoc))};
async function exPDF(){ensurePages();if(!pages.some(p=>p.views.length||p.shots.length)&&!views.length&&!shots.length)return msg('Ajoutez d’abord des vues à la mise en plan (onglet Mise en plan).');try{msg('Création du PDF…',8000);const P=[];for(const s of allDocs()){const c=await svgCanvas(s,3307),b=await toBlob(c,'image/jpeg',.92);P.push({u:new Uint8Array(await b.arrayBuffer()),w:c.width,h:c.height})}await save('plan.pdf',pdfFromJpegs(P,1190.55,841.89),'application/pdf')}catch(e){msg('PDF impossible : '+e.message)}}
async function exPNGplan(){if(!views.length&&!shots.length)return msg('Ajoutez d’abord des vues à la mise en plan.');try{const c=await sheetCanvas(3307);await save('plan.png',await toBlob(c,'image/png'),'image/png')}catch(e){msg('PNG impossible : '+e.message)}}
function printAll(){ensurePages();
 const d=document.createElement('div');d.id='pp';d.innerHTML=allDocs().join('');document.body.appendChild(d);document.body.classList.add('pr');const end=()=>{document.body.classList.remove('pr');d.remove();removeEventListener('afterprint',end)};addEventListener('afterprint',end);let fired=false;addEventListener('beforeprint',()=>fired=true,{once:true});setTimeout(()=>{try{print()}catch(e){}},80);setTimeout(()=>{if(!fired){end();msg('Impression directe bloquée par cette page (sécurité du navigateur). Ouvrez l’application hors ligne (index.html) pour imprimer directement, ou utilisez Fichier › PDF du plan.',10000)}},1800)}
async function c3d(){const c=snap3D(),img=new Image();await new Promise((ok,ko)=>{img.onload=ok;img.onerror=ko;img.src=c.src});const cv=document.createElement('canvas');cv.width=c.w;cv.height=c.h;cv.getContext('2d').drawImage(img,0,0);return cv}
async function exPNG3(){if(!objs.length)return msg('Rien à exporter.');try{await save('vue-3d.png',await toBlob(await c3d(),'image/png'),'image/png')}catch(e){msg('PNG impossible : '+e.message)}}
async function exPDF3(){if(!objs.length)return msg('Rien à exporter.');try{const cv=await c3d(),b=await toBlob(cv,'image/jpeg',.92),u=new Uint8Array(await b.arrayBuffer());await save('vue-3d.pdf',pdfFromJpeg(u,cv.width,cv.height,841.89,Math.round(841.89*cv.height/cv.width)),'application/pdf')}catch(e){msg('PDF impossible : '+e.message)}}

/* ----- pages multiples ----- */
let pages=[],curPage=0;
const newNom=()=>({asm:false,show:typeof expert!='undefined'&&!!expert,x:14,y:213,mode:'plat',cols:{rep:1,qty:1,des:1,dim:1,ops:0,mat:0},lock:false,anchor:'bl',title:'NOMENCLATURE',sz:3});
function ensurePages(){if(!pages.length){pages=[{name:'Page 1',views,dims,texts,shots,nom}];curPage=0}}
function savePage(){ensurePages();pages[curPage]={...pages[curPage],views,dims,texts,shots,nom}}
function setPageVars(p){views=p.views;dims=p.dims;texts=p.texts;shots=p.shots;nom=p.nom}
function loadPage(i){savePage();curPage=i;setPageVars(pages[i]);selV=selD=selT=selS=null;selN=false;fitSheet();draw();drui();touch()}
function withPage(i,fn){savePage();const sv=[views,dims,texts,shots,nom,curPage],p=pages[i];setPageVars(p);curPage=i;try{return fn()}finally{[views,dims,texts,shots,nom,curPage]=sv}}
function addPage(){savePage();pages.push({name:'Page '+(pages.length+1),made:true,views:[],dims:[],texts:[],shots:[],nom:{...newNom(),show:false}});loadPage(pages.length-1);msg('Page ajoutée. Utilisez « Nouvelle vue… » pour la remplir.')}
function delPage(){ensurePages();if(pages.length<2)return msg('Il faut garder au moins une page.');pages.splice(curPage,1);curPage=Math.min(curPage,pages.length-1);setPageVars(pages[curPage]);selV=selD=selT=selS=null;selN=false;draw();drui();touch()}
function pgbar(){vbarBuild()}
function renamePage(i){dlg('Nom de la page',[{k:'n',l:'Nom',t:'txt',v:pages[i].name}],v=>{pages[i].name=v.n||pages[i].name;pgbar();touch()})}
function viewDlg(){projWin()}
/* ----- projection : choisir les pièces et la direction de regard, avec aperçu 3D (d'où on regarde / ce qu'on obtient) ----- */
const pjIds=V=>V.sel=='all'?null:V.sel=='sel'?sel.filter(o=>solids().includes(o)||GL.includes(o.type)).map(o=>o.id):String(V.sel).startsWith('a')?piecesOf(+String(V.sel).slice(1)).map(o=>o.id):null;
function addOverallDims(w){vdata(w);const s=w.s,u0=w.u0,u1=w.u0+w.W,v1=w.v1,v0=w.v1-w.H;if(!(u1>u0&&v1>v0))return;
 dims.push({id:did++,v:w.id,t:'h',pre:'',a:[u0,v0],b:[u1,v0],o:(v1-v0)*s+7,auto:1});
 dims.push({id:did++,v:w.id,t:'v',pre:'',a:[u1,v0],b:[u1,v1],o:(u1-u0)*s+7,auto:1})}
/* disposition normalisée (méthode européenne) : face au centre, dessus en dessous, gauche à droite, droite à gauche, dessous au-dessus, arrière tout à droite, perspective en haut à droite */
const STD={front:[1,1],top:[1,2],bottom:[1,0],left:[2,1],right:[0,1],back:[3,1],iso:[3,0]};
function layoutStd(){const V=views.filter(w=>!w.det&&!w.moved);if(!V.length)return;V.forEach(vdata);const cell=w=>STD[w.k]||(String(w.k).startsWith('u')?[3,2]:[3,2]);
 const fit=s=>{const cw=[0,0,0,0],rh=[0,0,0];V.forEach(w=>{const[c,r]=cell(w);cw[c]=Math.max(cw[c],w.W*s);rh[r]=Math.max(rh[r],w.H*s)});return{cw,rh,W:cw.reduce((a,b)=>a+b,0)+24*cw.filter(Boolean).length,H:rh.reduce((a,b)=>a+b,0)+24*rh.filter(Boolean).length}};
 const s=V.find(w=>w.fixS)?V.find(w=>w.fixS).s:(NICE.find(s=>{const f=fit(s);return f.W<=370&&f.H<=200})||.001),f=fit(s);
 const cx=[],ry=[];let x=28;f.cw.forEach((w,i)=>{cx[i]=x;if(w)x+=w+24});let y=26;f.rh.forEach((h,i)=>{ry[i]=y;if(h)y+=h+24});
 V.forEach(w=>{const[c,r]=cell(w);w.s=s;w.x=cx[c]+(f.cw[c]-w.W*s)/2;w.y=ry[r]+(f.rh[r]-w.H*s)/2});
 dims.forEach(d=>{if(!d.auto)return;const w=views.find(v=>v.id==d.v);if(w)d.o=d.t=='h'?w.H*w.s+7:w.W*w.s+7})}
/* mise en page optimale d'un plan de référence : vues les plus grandes possibles qui tiennent sur la feuille
 * sans toucher la nomenclature, le cartouche ni les notes (échelles normalisées ; l'isométrique a sa propre échelle) */
const SCN=[5,2,1,.5,.4,.2,.1,1/15,.05,.04,1/30,.025,.02,1/60,1/75,.01,1/150,.005,.002,.001];
function layoutBest(vs,o){const[f,t,l,iso]=vs;vs.forEach(vdata);const A=[14,21,406,292],T=[228,247,412,292],obs=[T];
 if(o.nomBox)obs.push([10,Math.max(60,292-o.nomBox[1]-4),10+o.nomBox[0]+6,292]);if(o.notes)obs.push([(o.notesX||128)-3,247-5*o.notes-6,(o.notesX||128)+145,247]);
 const hit=(a,b)=>a[0]<b[2]&&b[0]<a[2]&&a[1]<b[3]&&b[1]<a[3],R=11,B=12,LBL=7,g=7;
 const lay=(id,s,si)=>{const F=[f.W*s,f.H*s],Tp=[t.W*s,t.H*s],Lf=[l.W*s,l.H*s],I=[iso.W*si,iso.H*si];
  if(id==0){const c1=Math.max(F[0],Tp[0])+R,c2=Lf[0]+R,c3=I[0]+4,r1=Math.max(F[1],Lf[1],I[1])+B+LBL,r2=Tp[1]+B+LBL;
   return{w:c1+c2+c3+2*g,h:r1+r2+g,P:(x,y)=>[[f,x+(c1-R-F[0])/2,y+LBL+(r1-B-LBL-F[1])/2],[l,x+c1+g+(c2-R-Lf[0])/2,y+LBL+(r1-B-LBL-Lf[1])/2],[iso,x+c1+c2+2*g,y+LBL+(r1-B-LBL-I[1])/2],[t,x+(c1-R-Tp[0])/2,y+r1+g+LBL]]}}
  const c1=Math.max(F[0],Tp[0])+R,c2=Math.max(Lf[0]+R,I[0]+4),r1=Math.max(F[1],Lf[1])+B+LBL,r2=Math.max(Tp[1]+B,I[1]+4)+LBL;
  return{w:c1+c2+g,h:r1+r2+g,P:(x,y)=>[[f,x+(c1-R-F[0])/2,y+LBL+(r1-B-LBL-F[1])/2],[l,x+c1+g+(c2-R-Lf[0])/2,y+LBL+(r1-B-LBL-Lf[1])/2],[t,x+(c1-R-Tp[0])/2,y+r1+g+LBL],[iso,x+c1+g,y+r1+g+LBL]]}};
 for(const s of SCN)for(const si of SCN.filter(v=>v<=s*2.01&&v>=s*.49)){for(const id of[0,1]){const L=lay(id,s,si);if(L.w>A[2]-A[0]||L.h>A[3]-A[1])continue;
   for(const[ax,ay]of[[A[0],A[1]],[A[2]-L.w,A[1]],[A[0],A[3]-L.h],[A[2]-L.w,A[3]-L.h]]){const box=[ax,ay,ax+L.w,ay+L.h];if(obs.some(r=>hit(box,r)))continue;
    L.P(ax,ay).forEach(([w,x,y])=>{w.x=x;w.y=y;w.s=w===iso?si:s});return true}}}
 const L=lay(0,.001,.001);L.P(14,21).forEach(([w,x,y])=>{w.x=x;w.y=y;w.s=.001});return false}
function pjAdd(k,only,cotes,sc){const w=mkView(k,only),n=views.length;w.s=n?views[0].s:(NICE.find(s=>w.W*s<=150&&w.H*s<=105)||.001);
 if(sc&&sc!='auto'){const m=/^(\d+):(\d+)$/.exec(sc);if(m)w.s=m[1]/m[2]}
 if(sc&&sc!='auto')w.fixS=1;views.push(w);pages[curPage].made=true;layoutStd();selV=w;selD=selT=null;if(cotes)addOverallDims(w);draw();drui();touch();return w}
const hull2=P=>{P=P.slice().sort((a,b)=>a[0]-b[0]||a[1]-b[1]);if(P.length<3)return P;const c=(o,a,b)=>(a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0]),lo=[],up=[];for(const q of P){while(lo.length>1&&c(lo[lo.length-2],lo[lo.length-1],q)<=0)lo.pop();lo.push(q)}for(const q of P.slice().reverse()){while(up.length>1&&c(up[up.length-2],up[up.length-1],q)<=0)up.pop();up.push(q)}return lo.slice(0,-1).concat(up.slice(0,-1))};
const pjVerts=o=>{const P=[];if(!o.m||!o.m.geometry)return P;o.m.updateMatrixWorld();const a=o.m.geometry.attributes.position,st=Math.max(1,Math.floor(a.count/250)),v=new THREE.Vector3();for(let i=0;i<a.count;i+=st){v.fromBufferAttribute(a,i).applyMatrix4(o.m.matrixWorld);P.push(v.toArray())}return P};
const pjBasis=f=>{const h=Math.abs(f[2])>.99?[1,0,0]:nrm(cr(f,[0,0,1]));return[h,cr(h,f)]};
const pjFace=[['front','Face'],['back','Arrière'],['left','Gauche'],['right','Droite'],['top','Dessus'],['bottom','Dessous'],['iso','Isométrique']];
let PJ=null;
function pjPick(k){if(!PJ)return;const V=PJ.V;if(PJ.dup(k))return msg('Cette vue est déjà sur la page.');V.ks=V.ks||{};V.ks[k]=!V.ks[k];if(V.ks[k])V.act=k;else if(V.act==k)V.act=Object.keys(V.ks).find(x=>V.ks[x])||k;const e=$('#f_sc');if(e)e.dispatchEvent(new Event('change',{bubbles:true}))}
function pjNet(V){if(!PJ)return'';const cell=(k,l,x,y,w=62,h=38)=>{const on=V.ks&&V.ks[k],dup=PJ.dup(k);return`<g onclick="pjPick('${k}')" style="cursor:${dup?'not-allowed':'pointer'}"><rect x="${x}" y="${y}" width="${w}" height="${h}" rx="4" fill="${on?'#e08a00':dup?'#d4d7dd':'#fff'}" stroke="${V.act==k?'#b06a00':'#8a93a3'}" stroke-width="${V.act==k?2.4:1.2}"/><text x="${x+w/2}" y="${y+h/2+4}" text-anchor="middle" style="font:600 11px system-ui;fill:${on?'#fff':'#333'};stroke:none">${l}${dup?' ✓':''}</text></g>`};
 return `<span style="display:block;font-size:12px;margin-bottom:2px">Regarder le modèle depuis… <small class="mu">(cliquez une ou plusieurs faces)</small></span><svg viewBox="0 0 270 190" style="width:100%;max-width:300px;display:block"><text x="135" y="10" text-anchor="middle" style="font:10px system-ui;fill:#888;stroke:none">Dessus</text>${cell('top','Dessus',104,14)}${cell('left','Gauche',40,56)}${cell('front','Face',104,56)}${cell('right','Droite',168,56)}${cell('bottom','Dessous',104,98)}${cell('back','Arrière',104,140)}${cell('iso','Iso',200,140,62,38)}${cell(PJ.ukey,'Écran',8,140,62,38)}</svg>`}
function projWin(){const S=solids();if(!S.length)return msg('Créez d’abord des pièces en 3D.');
 const asmO=Object.values(asms).filter(a=>piecesOf(a.id).length).map(a=>['a'+a.id,'Assemblage : '+a.n]),uv=(()=>{const v=new THREE.Vector3();cam.getWorldDirection(v);return v.toArray()})(),ukey='u'+(Date.now()%1000000),
  dirOf=k=>k==ukey?uv:DIRS[k][1],lab=k=>k==ukey?'Vue utilisateur (celle de l’écran)':DIRS[k][0],exists=(k,ids)=>views.some(w=>w.k==k&&JSON.stringify(w.only||null)==JSON.stringify(ids||null));
 DIRS[ukey]=['Vue utilisateur',uv];PJ={V:null,ukey,dup:k=>{const ids=pjIds(PJ.V);return exists(k,ids)}};
 const proj=(V)=>{const ids=pjIds(V);if(ids&&!ids.length)throw new Error('Sélectionnez d’abord des pièces, ou choisissez « Tout le modèle ».');const pcs=objs.filter(o=>!ids||ids.includes(o.id));return{ids,pcs}};
 opWin({title:'Ajouter une projection',intro:'Cochez à gauche, sur le schéma, la ou les faces depuis lesquelles on regarde. Dans l’aperçu 3D, un œil orange regarde le modèle et un écran de taille fixe, derrière, reçoit la projection en noir et blanc comme sur le plan.',ok:'Ajouter les vues',delay:150,
  init:{sel:sel.length?'sel':'all',ks:{front:1},act:'front',cotes:true,sc:'auto',nomp:!!nom.show,noma:!!nom.asm},
  fields:V=>(PJ.V=V,[{k:'net',t:'info',l:pjNet(V)},{k:'sel',l:'Pièces à projeter',t:'sel',o:[['sel','Les pièces sélectionnées ('+sel.length+')'],['all','Tout le modèle'],...asmO]},{k:'hs',t:'info',l:'Astuce : pour ne projeter que certaines pièces, fermez cette fenêtre, sélectionnez-les (Ctrl ou Maj + clic, dans la liste Objets ou dans la vue 3D), puis rouvrez-la. Rien de sélectionné = tout le modèle.'},{k:'cotes',l:'Ajouter les cotes principales (largeur et hauteur)',t:'chk'},{k:'nomp',l:'Afficher la nomenclature des pièces',t:'chk'},{k:'noma',l:'Afficher la nomenclature des assemblages (nombre de tenons, mi-bois…)',t:'chk'},{k:'sc',l:'Échelle',t:'sel',rb:1,o:[['auto','Automatique'],['1:1','1:1'],['1:2','1:2'],['1:5','1:5'],['1:10','1:10'],['1:20','1:20'],['1:50','1:50']]}]),
  preview:V=>{const{ids,pcs}=proj(V),items=pcs.map(o=>GL.includes(o.type)?{tg:o.type=='lash'?lashGeo(o):phGeo(o),pos:o.pos,rot:o.rot,color:o.color}:{g:geo(o),pos:o.pos,rot:o.rot,color:o.color}),[mn,mx]=bounds(pcs.length?pcs:objs),c=mn.map((v,i)=>(v+mx[i])/2),R=Math.max(...mx.map((v,i)=>v-mn[i]),200),lines=[],V3=[];pcs.forEach(o=>V3.push(...pjVerts(o)));
    const chosen=Object.keys(V.ks||{}).filter(k=>V.ks[k]);
    chosen.forEach(k=>{const f=nrm(dirOf(k)),[h,v]=pjBasis(f),eye=add(c,mul(f,-R*1.15)),act=k==V.act;
     const lens=[];for(let t=0;t<=16;t++){const a=Math.PI*t/16;lens.push(add(eye,add(mul(h,Math.cos(a)*R*.14),mul(v,Math.sin(a)*R*.07))))}
     for(let t=0;t<16;t++){const a=Math.PI*t/16,a2=Math.PI*(t+1)/16;lines.push([lens[t],lens[t+1],0xe08a00]);lines.push([add(eye,add(mul(h,Math.cos(a)*R*.14),mul(v,-Math.sin(a)*R*.07))),add(eye,add(mul(h,Math.cos(a2)*R*.14),mul(v,-Math.sin(a2)*R*.07))),0xe08a00])}
     lines.push([add(eye,mul(f,R*.02)),add(c,mul(f,-R*.55)),0xe08a00]);
     if(act&&V3.length){const z1=Math.max(...V3.map(p=>dot(p,f))),O=add(c,mul(f,R*.9)),W_=R*.9,H_=R*.675,M=new THREE.Matrix4().makeBasis(new THREE.Vector3(...h),new THREE.Vector3(...v),new THREE.Vector3(...f)),E=new THREE.Euler().setFromRotationMatrix(M,'ZYX');
      /* écran de projection : taille fixe, fond blanc ; le modèle y est projeté en noir et blanc, comme sur la mise en plan */
      items.push({tg:new THREE.PlaneGeometry(2*W_,2*H_),pos:O,rot:[E.x/D,E.y/D,E.z/D],color:'#ffffff',noedge:true});
      const q=[[1,1],[1,-1],[-1,-1],[-1,1]].map(s=>add(O,add(mul(h,s[0]*W_),mul(v,s[1]*H_))));q.forEach((p,i)=>lines.push([p,q[(i+1)%4],0x333333]));
      const cu=(Math.min(...V3.map(p=>dot(p,h)))+Math.max(...V3.map(p=>dot(p,h))))/2,cv=(Math.min(...V3.map(p=>dot(p,v)))+Math.max(...V3.map(p=>dot(p,v))))/2,sc=Math.min(1,W_*1.8/Math.max(1,Math.max(...V3.map(p=>dot(p,h)))-Math.min(...V3.map(p=>dot(p,h)))),H_*1.8/Math.max(1,Math.max(...V3.map(p=>dot(p,v)))-Math.min(...V3.map(p=>dot(p,v))))),pp=p=>add(O,add(mul(h,(p[0]-cu)*sc),mul(v,(p[1]-cv)*sc)));
      pcs.forEach(o=>{const H=hull2(pjVerts(o).map(p=>[dot(p,h),dot(p,v)]));H.forEach((p,i)=>{const n=H[(i+1)%H.length];lines.push([pp(p),pp(n),0x000000])})})}});
    return{items,extra:{lines},warn:[],view:{dir:add(mul(nrm(dirOf(V.act||'front')),-.55),[.6,-.5,.6]),center:c,radius:R*1.5}}},
  schema:V=>{const{pcs}=proj(V),k=V.act||'front',f=nrm(dirOf(k)),[h,v]=pjBasis(f),polys=pcs.map(o=>hull2(pjVerts(o).map(p=>[dot(p,h),-dot(p,v)])));let u0=1e9,u1=-1e9,v0=1e9,v1=-1e9;polys.forEach(H=>H.forEach(p=>{u0=Math.min(u0,p[0]);u1=Math.max(u1,p[0]);v0=Math.min(v0,p[1]);v1=Math.max(v1,p[1])}));const s=Math.min(280/Math.max(u1-u0,1),110/Math.max(v1-v0,1));
    return SV(`<g transform="translate(${160-(u0+u1)/2*s} ${75-(v0+v1)/2*s})" stroke-width="1" fill="rgba(200,160,100,.35)">${polys.map(H=>`<polygon points="${H.map(p=>(p[0]*s).toFixed(1)+','+(p[1]*s).toFixed(1)).join(' ')}"/>`).join('')}</g>${TXT(160,12,'Vue obtenue : '+lab(k))}`)},
  apply:V=>{const{ids}=proj(V),L=Object.keys(V.ks||{}).filter(k=>V.ks[k]&&!exists(k,ids));if(!L.length)throw new Error('Cliquez au moins un point orange (une face) qui n’est pas déjà sur la page.');planOn=true;L.forEach(k=>{const w=pjAdd(k,ids,V.cotes,V.sc);if(k==ukey){w.dv=uv;w.nm='Vue utilisateur'}});if(V.nomp||V.noma){nom.show=!!V.nomp;nom.asm=!!V.noma;nom.only=ids||null;draw();drui()}vbarBuild();msg(L.length+' vue(s) ajoutée(s) : déplacez-les sur la feuille, ou ajoutez-en d’autres avec le bouton « + ».')}})}
/* plan type d'un meuble de la bibliothèque : 4 vues cotées, nomenclature, détails par assemblage */
function libPlan(a,name){try{if(!solids().length)return;ensurePages();savePage();const used=pages.some(p=>p.views.length);if(used)pages.push({name:'Page '+(pages.length+1),made:true,views:[],dims:[],texts:[],shots:[],nom:newNom()});
  if(used)loadPage(pages.length-1);
  const ids=piecesOf(a.id).map(o=>o.id);pages[curPage].made=true;views=layout4(ids);nom.show=true;nom.asm=true;nom.only=ids;nom.mode='plat';meta.titre=name;pages[curPage].name=name;
  /* angles particuliers : pièces ni verticales ni horizontales, regroupées par nom */
  const ang={};piecesOf(a.id).forEach(o=>{if(o.type!='trav'||!isWood(o))return;const u=axisOf(o).u,v=Math.round(Math.acos(Math.min(1,Math.abs(u[2])))/D*10)/10;if(v>2&&v<88){const nm=o.name.replace(/ (gauche|droit|droite|avant|arrière)\b/g,'').replace(/ \d+$/,'');ang[nm+'|'+v]=1}});
  const AK=Object.keys(ang).slice(0,8);const bx1=nomBuild(),bx2=nomAsmBuild();const NX=Math.max(128,10+Math.max(bx1.w,bx2.w)+8);layoutBest(views,{nomBox:[Math.max(bx1.w,bx2.w),bx1.h+bx2.h+4],notes:AK.length,notesX:NX});dims=[];views.forEach(w=>{if(w.k!='iso')addOverallDims(w)});if(/pieds en X/.test(name))xDims(a);texts=[{id:tid++,x:28,y:15,t:'Plan type — '+name+' (cotes en '+us()+')',sz:4}];
  AK.forEach((k,i)=>{const[nm,v]=k.split('|');texts.push({id:tid++,x:NX,y:247-5*AK.length+i*5,t:'Angle : '+nm+' à '+v+'° de la verticale ('+r1(90-v)+'° du sol)',sz:3})});
  draw();drui();planOn=true;touch()}catch(e){console.error(e)}}
function planSettings(){dlg('Paramètres de la page',[...[['titre','Titre'],['soc','Société'],['des','Dessiné par'],['date','Date'],['mat','Matière'],['ref','N° de plan'],['ind','Indice']].map(([k,l])=>({k,l,t:'txt',v:meta[k]})),{k:'nm',l:'Afficher la nomenclature des pièces sur cette page',t:'chk',v:nom.show},{k:'asm',l:'Afficher la nomenclature des assemblages',t:'chk',v:!!nom.asm},{k:'mode',l:'Nomenclature',t:'sel',v:nom.mode,o:[['plat','Liste groupée'],['arbo','Par assemblage (arborescence)']]},{k:'hid',l:'Traits cachés (mode expert)',t:'chk',v:showHid},{k:'ax',l:'Axes (mode expert)',t:'chk',v:showAx}],v=>{['titre','soc','des','date','mat','ref','ind'].forEach(k=>meta[k]=v[k]);nom.show=v.nm;nom.asm=v.asm;nom.mode=v.mode;showHid=v.hid;showAx=v.ax;draw();drui();buildRibbon();touch()},'Enregistrer')}

/* ---------- Atelier Esquisse : contraintes façon FreeCAD ---------- */
const SS=$('#ss'),SKH={sel:'Cliquez un point, une ligne ou un cercle (Maj = plusieurs), puis une contrainte du ruban. Glissez un point pour le déplacer : les contraintes sont respectées.',poly:'Cliquez les sommets : accroche aux points et aux axes, H/V automatiques à ±5°. Clic sur le 1er point, double-clic ou Entrée : fermer.',rect:'Cliquez deux coins opposés (4 contraintes H/V posées automatiquement).',circ:'Cliquez le centre, puis un point du rayon.'};
let sk={P:{},sh:[],cons:[],sel:[],ss:null,tool:'poly',cur:null,step:5,cursor:null,len:100,ang:360,dof:0},skid=1,skvb=[-150,-110,300,220],skdrag=null;
const pp=id=>sk.P[id],shp=id=>sk.sh.find(s=>s.id==id);
function cornerize(P,ch,fi){if(!(ch>0||fi>0))return P;const n=P.length,out=[],len=(a,b)=>Math.hypot(a[0]-b[0],a[1]-b[1]);
 for(let i=0;i<n;i++){const C=P[i],A0=P[(i+n-1)%n],B0=P[(i+1)%n],lu=len(A0,C),lv=len(B0,C);if(lu<1e-9||lv<1e-9){out.push(C);continue}
  const u=[(A0[0]-C[0])/lu,(A0[1]-C[1])/lu],v=[(B0[0]-C[0])/lv,(B0[1]-C[1])/lv],ang=Math.acos(Math.max(-1,Math.min(1,u[0]*v[0]+u[1]*v[1])));
  if(ang<1e-3||ang>Math.PI-1e-3){out.push(C);continue}
  let t=fi>0?fi/Math.tan(ang/2):ch;t=Math.min(t,lu/2,lv/2);const A=[C[0]+u[0]*t,C[1]+u[1]*t],B=[C[0]+v[0]*t,C[1]+v[1]*t];
  if(!(fi>0)){out.push(A,B);continue}
  const r=t*Math.tan(ang/2),bs=nrm([u[0]+v[0],u[1]+v[1],0]),cd=r/Math.sin(ang/2),cen=[C[0]+bs[0]*cd,C[1]+bs[1]*cd],a0=Math.atan2(A[1]-cen[1],A[0]-cen[0]);let da=Math.atan2(B[1]-cen[1],B[0]-cen[0])-a0;
  while(da>Math.PI)da-=2*Math.PI;while(da<-Math.PI)da+=2*Math.PI;
  for(let k=0;k<=8;k++)out.push([cen[0]+r*Math.cos(a0+da*k/8),cen[1]+r*Math.sin(a0+da*k/8)])}
 return out}
function revolve(pts,ang){const A=ang*Math.PI/180,full=ang>=359.99,n=Math.max(8,Math.round(48*Math.min(ang,360)/360));
 let P=pts.map(p=>[Math.max(0,p[0]),p[1]]),ar=0;P.forEach((p,i)=>{const q=P[(i+1)%P.length];ar+=p[0]*q[1]-q[0]*p[1]});if(ar<0)P.reverse();
 const R=(p,t)=>[p[0]*Math.cos(t),p[0]*Math.sin(t),p[1]],polys=[],pl=J.geometries.poly3.create;
 const add=v=>{const u=v.filter((p,i)=>{const q=v[(i+1)%v.length];return Math.hypot(p[0]-q[0],p[1]-q[1],p[2]-q[2])>1e-9});if(u.length>=3)polys.push(pl(u))};
 for(let j=0;j<n;j++){const t0=A*j/n,t1=A*(j+1)/n;for(let i=0;i<P.length;i++){const p=P[i],q=P[(i+1)%P.length];if(p[0]<1e-9&&q[0]<1e-9)continue;add([R(p,t0),R(p,t1),R(q,t1),R(q,t0)])}}
 if(!full){add(P.map(p=>R(p,0)));add(P.slice().reverse().map(p=>R(p,A)))}
 return G.create(polys)}
function skPts(s){if(s.t=='circ'){const c=pp(s.c);return Array.from({length:48},(_,i)=>[c.x+s.r*Math.cos(i*Math.PI/24),c.y+s.r*Math.sin(i*Math.PI/24)])}return cornerize(s.ids.map(i=>[pp(i).x,pp(i).y]),s.ch,s.fi)}
/* --- solveur de contraintes (Levenberg-Marquardt) --- */
function gauss(M,b){const n=M.length,A=M.map((r,i)=>[...r,b[i]]);for(let c=0;c<n;c++){let p=c;for(let r=c+1;r<n;r++)if(Math.abs(A[r][c])>Math.abs(A[p][c]))p=r;if(Math.abs(A[p][c])<1e-12)return null;[A[c],A[p]]=[A[p],A[c]];for(let r=0;r<n;r++)if(r!=c){const f=A[r][c]/A[c][c];for(let k=c;k<=n;k++)A[r][k]-=f*A[c][k]}}return A.map((r,i)=>r[n]/r[i])}
function rankOf(M){const A=M.map(r=>[...r]),n=A.length,mx=Math.max(...A.map((r,i)=>Math.abs(r[i])),1e-12);let rk=0;for(let c=0;c<n&&rk<n;c++){let p=rk;for(let r=rk+1;r<n;r++)if(Math.abs(A[r][c])>Math.abs(A[p][c]))p=r;if(Math.abs(A[p][c])<1e-7*mx)continue;[A[rk],A[p]]=[A[p],A[rk]];for(let r=rk+1;r<n;r++){const f=A[r][c]/A[rk][c];for(let k=c;k<n;k++)A[r][k]-=f*A[rk][k]}rk++}return rk}
function skRes(c){const A=c.a&&pp(c.a),B=c.b&&pp(c.b),L=l=>{const a=pp(l[0]),b=pp(l[1]);return[b.x-a.x,b.y-a.y]},n=v=>Math.max(Math.hypot(v[0],v[1]),1e-6);
 switch(c.t){
  case'H':return[A.y-B.y];case'V':return[A.x-B.x];case'coin':return[A.x-B.x,A.y-B.y];
  case'par':{const u=L(c.l1),v=L(c.l2);return[(u[0]*v[1]-u[1]*v[0])/n(v)]}
  case'perp':{const u=L(c.l1),v=L(c.l2);return[(u[0]*v[0]+u[1]*v[1])/n(v)]}
  case'eq':return c.s1?[shp(c.s1).r-shp(c.s2).r]:[n(L(c.l1))-n(L(c.l2))];
  case'dist':return[Math.hypot(B.x-A.x,B.y-A.y)-c.v];case'dx':return[B.x-A.x-c.v];case'dy':return[B.y-A.y-c.v];
  case'ang':{const u=L(c.l1),v=L(c.l2);const d=Math.atan2(u[0]*v[1]-u[1]*v[0],u[0]*v[0]+u[1]*v[1])-c.v;return[Math.atan2(Math.sin(d),Math.cos(d))*50]}
  case'rad':return[shp(c.s).r-c.v];
  case'fx':return[A.x-c.v];case'fy':return[A.y-c.v];
  case'pol':{const a=pp(c.l[0]),b=pp(c.l[1]),d=[b.x-a.x,b.y-a.y];return[(d[0]*(A.y-a.y)-d[1]*(A.x-a.x))/n(d)]}}
 return[]}
function skSolve(drag){const V=[];for(const id in sk.P)V.push([sk.P[id],'x'],[sk.P[id],'y']);sk.sh.filter(s=>s.t=='circ').forEach(s=>V.push([s,'r']));const n=V.length;if(!n){sk.dof=0;return}
 const set=v=>V.forEach(([o,k],i)=>o[k]=v[i]),all=d=>{const r=[];for(const c of sk.cons)r.push(...skRes(c).map(q=>q*100));if(d){const p=pp(d.id);r.push(p.x-d.x,p.y-d.y)}return r},nm=r=>r.reduce((s,q)=>s+q*q,0);
 let x=V.map(([o,k])=>o[k]);const res=v=>{set(v);return all(drag)};let r=res(x),f=nm(r),lam=1e-3;
 const jac=(fn,x0,r0)=>{const J=[];for(let j=0;j<n;j++){const h=1e-6*(1+Math.abs(x0[j])),xp=[...x0];xp[j]+=h;J.push(fn(xp).map((q,i)=>(q-r0[i])/h))}return J};
 for(let it=0;it<60&&f>1e-16&&r.length;it++){const J=jac(res,x,r),A=J.map(a=>J.map(b=>a.reduce((s,q,i)=>s+q*b[i],0))),g=J.map(row=>row.reduce((s,q,i)=>s+q*r[i],0));let ok=false;
  for(let tr=0;tr<8&&!ok;tr++){const d=gauss(A.map((row,i)=>row.map((q,j)=>q+(i==j?lam*(1+q):0))),g.map(q=>-q));if(!d){lam*=10;continue}const xn=x.map((q,i)=>q+d[i]),rn=res(xn),fn=nm(rn);if(fn<f){x=xn;r=rn;f=fn;lam=Math.max(lam/3,1e-9);ok=true}else lam*=4}
  if(!ok)break}
 set(x);const r0=all(null);if(!r0.length){sk.dof=n;return}const J=jac(v=>{set(v);return all(null)},x,r0);set(x);sk.dof=n-rankOf(J.map(a=>J.map(b=>a.reduce((s,q,i)=>s+q*b[i],0))))}
/* --- édition --- */
function skPoint(s){if(s.id)return s.id;const id=skid++;sk.P[id]={x:s.p[0],y:s.p[1]};if(s.ax.x)sk.cons.push({t:'fx',a:id,v:0});if(s.ax.y)sk.cons.push({t:'fy',a:id,v:0});return id}
function skSnap(r){const tol=skvb[2]/60;let best=null,bd=tol;for(const id in sk.P){const q=sk.P[id],d=Math.hypot(q.x-r[0],q.y-r[1]);if(d<bd){bd=d;best={id:+id}}}if(best)return best;
 let x=Math.round(r[0]/sk.step)*sk.step,y=Math.round(r[1]/sk.step)*sk.step;const ax={};if(Math.abs(r[0])<tol){x=0;ax.x=1}if(Math.abs(r[1])<tol){y=0;ax.y=1}return{p:[x,y],ax}}
function skAuto(a,b){const p=pp(a),q=pp(b),ang=Math.atan2(Math.abs(q.y-p.y),Math.abs(q.x-p.x))*180/Math.PI;if(ang<5){q.y=p.y;sk.cons.push({t:'H',a,b})}else if(ang>85){q.x=p.x;sk.cons.push({t:'V',a,b})}}
function skHit(r){const tol=skvb[2]/70;
 for(const id in sk.P){const q=sk.P[id];if(Math.hypot(q.x-r[0],q.y-r[1])<tol*1.4)return{k:'p',id:+id}}
 for(const s of sk.sh){if(s.t=='circ'){const c=pp(s.c);if(Math.abs(Math.hypot(r[0]-c.x,r[1]-c.y)-s.r)<tol)return{k:'c',s:s.id}}
  else for(let i=0;i<s.ids.length;i++){const ia=s.ids[i],ib=s.ids[(i+1)%s.ids.length],a=pp(ia),b=pp(ib),dx=b.x-a.x,dy=b.y-a.y,t=Math.max(0,Math.min(1,((r[0]-a.x)*dx+(r[1]-a.y)*dy)/(dx*dx+dy*dy||1)));if(Math.hypot(a.x+t*dx-r[0],a.y+t*dy-r[1])<tol)return{k:'l',a:ia,b:ib,s:s.id}}}
 return null}
const same=(u,v)=>u.k==v.k&&u.id==v.id&&u.a==v.a&&u.b==v.b&&u.s==v.s&&!(u.k=='l'&&u.s!=v.s);
function skFinish(){const c=sk.cur;if(c&&c.t=='poly'){const ids=c.ids.filter((p,i,a)=>!i||p!=a[i-1]);if(ids.length>=3){sk.sh.push({id:skid++,t:'poly',ids,ch:0,fi:0,hole:false});sk.ss=skid-1}}sk.cur=null;skSolve();skDraw();skui()}
const skpt=e=>{const q=SS.createSVGPoint();q.x=e.clientX;q.y=e.clientY;const r=q.matrixTransform(SS.getScreenCTM().inverse());return[r.x,-r.y]};
SS.onpointerdown=e=>{const raw=skpt(e),T=sk.tool;
 if(T=='sel'){const h=skHit(raw);
  if(h){if(h.s)sk.ss=h.s;if(e.shiftKey){const i=sk.sel.findIndex(q=>same(q,h));i<0?sk.sel.push(h):sk.sel.splice(i,1)}else sk.sel=[h];if(h.k=='p')skdrag={pid:h.id}}
  else if(!e.shiftKey){sk.sel=[];skdrag={px:e.clientX,py:e.clientY,vb:[...skvb],k:1/SS.getScreenCTM().a}}
  SS.setPointerCapture(e.pointerId);skDraw();skui();return}
 const s=skSnap(raw);
 if(T=='poly'){const id=skPoint(s);const c=sk.cur||(sk.cur={t:'poly',ids:[]}),ids=c.ids;if(ids.length>=3&&id==ids[0])return skFinish();if(ids[ids.length-1]==id)return;if(ids.length&&!s.id)skAuto(ids[ids.length-1],id);ids.push(id)}
 else if(!sk.cur)sk.cur={t:T,a:skPoint(s)};
 else if(T=='rect'){const A=sk.cur.a,C=skPoint(s),a=pp(A),c=pp(C);if(a.x!=c.x&&a.y!=c.y){const B=skid++,D=skid++;sk.P[B]={x:c.x,y:a.y};sk.P[D]={x:a.x,y:c.y};sk.cons.push({t:'H',a:A,b:B},{t:'V',a:B,b:C},{t:'H',a:C,b:D},{t:'V',a:D,b:A});sk.sh.push({id:skid++,t:'poly',ids:[A,B,C,D],ch:0,fi:0,hole:false});sk.ss=skid-1}sk.cur=null}
 else{const c=pp(sk.cur.a),q=s.id?pp(s.id):{x:s.p[0],y:s.p[1]},r=Math.hypot(q.x-c.x,q.y-c.y);if(r>0){sk.sh.push({id:skid++,t:'circ',c:sk.cur.a,r,hole:false});sk.ss=skid-1}sk.cur=null}
 skSolve();skDraw();skui()};
SS.addEventListener('contextmenu',e=>{e.preventDefault();if(sk.tool!='sel')skTool('sel')});
SS.ondblclick=()=>{if(sk.tool=='poly')skFinish()};
SS.onpointermove=e=>{const raw=skpt(e);
 if(skdrag){if(skdrag.pid){skSolve({id:skdrag.pid,x:raw[0],y:raw[1]});skDraw()}else{skvb[0]=skdrag.vb[0]-(e.clientX-skdrag.px)*skdrag.k;skvb[1]=skdrag.vb[1]-(e.clientY-skdrag.py)*skdrag.k;SS.setAttribute('viewBox',skvb.join(' '));skDraw()}return}
 const s=skSnap(raw);sk.cursor=s.id?[pp(s.id).x,pp(s.id).y]:s.p;sk.hint=null;
 if(sk.tool=='poly'&&sk.cur&&sk.cur.ids.length&&!s.id){const q=pp(sk.cur.ids[sk.cur.ids.length-1]),a=Math.atan2(Math.abs(sk.cursor[1]-q.y),Math.abs(sk.cursor[0]-q.x))*180/Math.PI;sk.hint=a<5?'H':a>85?'V':null}
 skDraw()};
SS.onpointerup=()=>{if(skdrag&&skdrag.pid){skSolve();skDraw();skui()}skdrag=null};
SS.addEventListener('wheel',e=>{e.preventDefault();const q=SS.createSVGPoint();q.x=e.clientX;q.y=e.clientY;const r=q.matrixTransform(SS.getScreenCTM().inverse()),k=e.deltaY>0?1.15:1/1.15;skvb=[r.x-(r.x-skvb[0])*k,r.y-(r.y-skvb[1])*k,skvb[2]*k,skvb[3]*k];SS.setAttribute('viewBox',skvb.join(' '));skDraw()},{passive:false});
addEventListener('keydown',e=>{if(!document.body.classList.contains('sk')||/INPUT|SELECT/.test(document.activeElement.tagName))return;if(e.key=='Enter')skFinish();if(e.key=='Escape'){sk.cur=null;skDraw()}if(e.key=='Delete')skDel()});
function skTool(t){sk.tool=t;sk.cur=null;SS.style.cursor=t=='sel'?'default':'crosshair';buildRibbon();skDraw();skui()}
function skClean(){const used=new Set();sk.sh.forEach(s=>{if(s.t=='circ')used.add(s.c);else s.ids.forEach(i=>used.add(i))});for(const id in sk.P)if(!used.has(+id))delete sk.P[id];
 const ok=c=>[c.a,c.b].every(i=>i==null||sk.P[i])&&[...(c.l1||[]),...(c.l2||[]),...(c.l||[])].every(i=>sk.P[i])&&[c.s,c.s1,c.s2].every(i=>i==null||shp(i));sk.cons=sk.cons.filter(ok);sk.sel=[]}
function skDel(){sk.sh=sk.sh.filter(s=>s.id!=sk.ss);sk.ss=null;skClean();skSolve();skDraw();skui()}
function skClear(){sk.P={};sk.sh=[];sk.cons=[];sk.sel=[];sk.ss=null;sk.cur=null;sk.dof=0;skDraw();skui()}
function skRound(k){const s=shp(sk.ss);if(!s||s.t=='circ')return msg('Sélectionnez une ligne ou une forme (outil Sélection).');s[k]=s[k]||5;s[k=='ch'?'fi':'ch']=0;skui();skDraw()}
function skC(t){const S=sk.sel,pts=S.filter(s=>s.k=='p'),lns=S.filter(s=>s.k=='l'),cs=S.filter(s=>s.k=='c');let n=0;const add=c=>{sk.cons.push(c);n++},L=l=>[l.a,l.b];
 if(t=='H'||t=='V'){lns.forEach(l=>add({t,a:l.a,b:l.b}));if(!lns.length&&pts.length==2)add({t,a:pts[0].id,b:pts[1].id})}
 else if(t=='par'||t=='perp'){if(lns.length==2)add({t,l1:L(lns[0]),l2:L(lns[1])})}
 else if(t=='eq'){if(lns.length==2)add({t,l1:L(lns[0]),l2:L(lns[1])});else if(cs.length==2)add({t,s1:cs[0].s,s2:cs[1].s})}
 else if(t=='coin'){if(pts.length==2)add({t,a:pts[0].id,b:pts[1].id})}
 else if(t=='fx'||t=='fy')pts.forEach(p=>add({t,a:p.id,v:0}));
 else if(t=='lock')pts.forEach(p=>{add({t:'fx',a:p.id,v:pp(p.id).x});add({t:'fy',a:p.id,v:pp(p.id).y})});
 else if(t=='pol'){if(pts.length==1&&lns.length==1)add({t,a:pts[0].id,l:L(lns[0])})}
 if(!n)return msg('Sélection inadaptée à cette contrainte (voir l’aide à gauche).');skSolve();skDraw();skui()}
function skD(t){const S=sk.sel,pts=S.filter(s=>s.k=='p'),lns=S.filter(s=>s.k=='l'),cs=S.filter(s=>s.k=='c');let c,cur,lab;
 if(t=='dist'||t=='dx'||t=='dy'){let a,b;if(pts.length==2){a=pts[0].id;b=pts[1].id}else if(lns.length==1){a=lns[0].a;b=lns[0].b}else return msg('Sélectionnez 2 points ou 1 ligne.');const A=pp(a),B=pp(b);cur=t=='dist'?Math.hypot(B.x-A.x,B.y-A.y):t=='dx'?B.x-A.x:B.y-A.y;c={t,a,b};lab=t=='dist'?'Distance (mm)':t=='dx'?'Distance horizontale (mm)':'Distance verticale (mm)'}
 else if(t=='ang'){if(lns.length!=2)return msg('Sélectionnez 2 lignes.');const q=l=>{const a=pp(l.a),b=pp(l.b);return[b.x-a.x,b.y-a.y]},u=q(lns[0]),v=q(lns[1]);cur=Math.atan2(u[0]*v[1]-u[1]*v[0],u[0]*v[0]+u[1]*v[1])*180/Math.PI;c={t,l1:[lns[0].a,lns[0].b],l2:[lns[1].a,lns[1].b]};lab='Angle (°)'}
 else{if(cs.length!=1)return msg('Sélectionnez un cercle.');cur=shp(cs[0].s).r;c={t:'rad',s:cs[0].s};lab='Rayon (mm)'}
 dlg('Contrainte de cote',[{k:'v',l:lab,t:'num',v:r1(cur)}],r=>{if(t!='dx'&&t!='dy'&&t!='ang'&&!(r.v>0))return msg('Valeur invalide.');c.v=t=='ang'?r.v*Math.PI/180:r.v;sk.cons.push(c);skSolve();skDraw();skui()})}
function skCv(i,v){const c=sk.cons[i];c.v=c.t=='ang'?v*Math.PI/180:v;skSolve();skDraw()}
function skCdel(i){sk.cons.splice(i,1);skSolve();skDraw();skui()}
function skMove(id,x,y){skSolve({id,x,y});skSolve();skDraw()}
function skSet(k,v){const s=shp(sk.ss);if(!s)return;s[k]=v;k=='hole'?skui():0;skDraw()}
/* --- affichage --- */
const SYM={H:'H',V:'V',par:'∥',perp:'⊥',eq:'=',coin:'●',fx:'x=',fy:'y=',pol:'⌖'};
function skDraw(){const[x,y,w,h]=skvb,st=sk.step,gs=w/st>120?st*5:st,Y=v=>fx(-v),fs=w/70;let g='';
 for(let gx=Math.ceil(x/gs)*gs;gx<x+w;gx+=gs)g+=`<line x1="${gx}" y1="${y}" x2="${gx}" y2="${y+h}" stroke="currentColor" stroke-opacity="${gx%(gs*5)?.1:.25}" stroke-width=".25"/>`;
 for(let gy=Math.ceil(y/gs)*gs;gy<y+h;gy+=gs)g+=`<line x1="${x}" y1="${gy}" x2="${x+w}" y2="${gy}" stroke="currentColor" stroke-opacity="${gy%(gs*5)?.1:.25}" stroke-width=".25"/>`;
 g+=`<line x1="${x}" y1="0" x2="${x+w}" y2="0" stroke="#d33" stroke-width=".6"/><line x1="0" y1="${y}" x2="0" y2="${y+h}" stroke="#2a2" stroke-width=".6"/>`;
 const T=(p,s,c)=>`<text x="${fx(p[0])}" y="${Y(p[1])}" font-size="${fx(fs)}" fill="${c||'#c0392b'}" text-anchor="middle" dy="${fx(-fs*.4)}">${s}</text>`,M=(a,b)=>[(pp(a).x+pp(b).x)/2,(pp(a).y+pp(b).y)/2],on=s=>s.id==sk.ss;
 for(const s of sk.sh)g+=`<polygon points="${skPts(s).map(p=>fx(p[0])+','+Y(p[1])).join(' ')}" fill="${s.hole?'#e0556655':'#2f6fdb33'}" stroke="${on(s)?'#e08a00':'#2f6fdb'}" stroke-width="${on(s)?.9:.6}"/>`;
 for(const q of sk.sel){if(q.k=='l')g+=`<line x1="${pp(q.a).x}" y1="${Y(pp(q.a).y)}" x2="${pp(q.b).x}" y2="${Y(pp(q.b).y)}" stroke="#e08a00" stroke-width="1.6"/>`;else if(q.k=='c'){const s=shp(q.s),c=pp(s.c);g+=`<circle cx="${c.x}" cy="${Y(c.y)}" r="${s.r}" fill="none" stroke="#e08a00" stroke-width="1.6"/>`}}
 for(const c of sk.cons){
  if(c.t=='H'||c.t=='V')g+=T(M(c.a,c.b),c.t);
  else if(c.t=='par'||c.t=='perp'||(c.t=='eq'&&c.l1))g+=T(M(...c.l1),SYM[c.t])+T(M(...c.l2),SYM[c.t]);
  else if(c.t=='eq'){for(const i of[c.s1,c.s2]){const q=pp(shp(i).c);g+=T([q.x,q.y],'=')}}
  else if(c.t=='coin'||c.t=='fx'||c.t=='fy'||c.t=='pol'){const q=pp(c.a);g+=T([q.x+fs*(c.t=='fy'?1:0),q.y],SYM[c.t])}
  else if(c.t=='dist'||c.t=='dx'||c.t=='dy'){const A=pp(c.a),B=pp(c.b),a=c.t=='dy'?[B.x,A.y]:c.t=='dx'?[A.x,B.y]:[A.x,A.y],b=c.t=='dist'?[B.x,B.y]:c.t=='dx'?[B.x,B.y]:[B.x,B.y];
   g+=`<line x1="${fx(a[0])}" y1="${Y(a[1])}" x2="${fx(b[0])}" y2="${Y(b[1])}" stroke="#0a58c8" stroke-width=".35" stroke-dasharray="2 1"/>`+T([(a[0]+b[0])/2,(a[1]+b[1])/2],r1(Math.abs(c.v)),'#0a58c8')}
  else if(c.t=='rad'){const s=shp(c.s),q=pp(s.c);g+=T([q.x+s.r*.7,q.y+s.r*.7],'R'+r1(c.v),'#0a58c8')}
  else if(c.t=='ang')g+=T(M(...c.l1),r1(c.v*180/Math.PI)+'°','#0a58c8')}
 for(const id in sk.P){const q=sk.P[id],s=sk.sel.some(z=>z.k=='p'&&z.id==id);g+=`<circle cx="${fx(q.x)}" cy="${Y(q.y)}" r="${fx(w/170*(s?1.5:1))}" fill="${s?'#e08a00':'#2f6fdb'}"/>`}
 const c=sk.cur,m=sk.cursor;
 if(c&&m){if(c.t=='poly')g+=`<polyline points="${[...c.ids.map(i=>[pp(i).x,pp(i).y]),m].map(p=>fx(p[0])+','+Y(p[1])).join(' ')}" fill="none" stroke="#e08a00" stroke-width=".7"/>`;
  else if(c.t=='rect'){const a=pp(c.a);g+=`<rect x="${Math.min(a.x,m[0])}" y="${-Math.max(a.y,m[1])}" width="${Math.abs(m[0]-a.x)}" height="${Math.abs(m[1]-a.y)}" fill="none" stroke="#e08a00" stroke-width=".7"/>`}
  else{const a=pp(c.a);g+=`<circle cx="${a.x}" cy="${Y(a.y)}" r="${Math.hypot(m[0]-a.x,m[1]-a.y)}" fill="none" stroke="#e08a00" stroke-width=".7"/>`}}
 if(m&&sk.tool!='sel'){g+=`<circle cx="${m[0]}" cy="${Y(m[1])}" r="${fx(w/150)}" fill="none" stroke="#e08a00" stroke-width=".5"/>`;if(sk.hint)g+=T([m[0]+fs,m[1]+fs],sk.hint,'#e08a00')}
 SS.innerHTML=g}
/* --- panneau --- */
const CN={H:'Horizontale',V:'Verticale',par:'Parallèle',perp:'Perpendiculaire',eq:'Égalité',coin:'Coïncidence',fx:'Sur l’axe Y (x=)',fy:'Sur l’axe X (y=)',pol:'Point sur ligne',dist:'Distance',dx:'Distance horizontale',dy:'Distance verticale',ang:'Angle',rad:'Rayon'};
function skui(){const s=shp(sk.ss),N={poly:'Polygone',circ:'Cercle'},p1=sk.sel.length==1&&sk.sel[0].k=='p'?pp(sk.sel[0].id):null;
 $('#ls').innerHTML='<h4>Formes</h4>'+(sk.sh.map((q,i)=>`<div class="it${q.id==sk.ss?' on':''}" onclick="sk.ss=${q.id};skui();skDraw()">${ic(q.t=='circ'?'circ':'poly',16)}${N[q.t]} ${i+1}${q.hole?' (trou)':''}</div>`).join('')||'<p class="mu">Dessinez avec les outils du ruban.</p>');
 let h=`<p class="mu">${SKH[sk.tool]}</p><p style="font-weight:600;color:${sk.dof==0&&sk.sh.length?'#2a9d4a':'var(--tx)'}">${sk.sh.length?(sk.dof==0?'Entièrement contrainte ✔':'Degrés de liberté : '+sk.dof):''}</p><label>Pas de grille (mm)<select onchange="sk.step=+this.value;skDraw()">${[1,2,5,10,20].map(v=>`<option${sk.step==v?' selected':''}>${v}</option>`).join('')}</select></label>`;
 if(p1)h+=`<h4>Point sélectionné</h4><div class="r"><label>X<input type="number" value="${r1(p1.x)}" onchange="skMove(${sk.sel[0].id},+this.value,${p1.y})"></label><label>Y<input type="number" value="${r1(p1.y)}" onchange="skMove(${sk.sel[0].id},${p1.x},+this.value)"></label></div>`;
 if(s&&s.t!='circ')h+=`<h4>Forme sélectionnée</h4><label>Chanfrein (mm)<input type="number" min="0" value="${s.ch||0}" oninput="skSet('ch',+this.value)"></label><label>Congé : rayon (mm)<input type="number" min="0" value="${s.fi||0}" oninput="skSet('fi',+this.value)"></label>`;
 if(s)h+=`<label><input type="checkbox" ${s.hole?'checked':''} onchange="skSet('hole',this.checked)" style="width:auto"> Trou (soustraction)</label><button onclick="skDel()">Supprimer la forme</button>`;
 h+='<h4>Contraintes</h4>'+(sk.cons.map((c,i)=>`<div class="r" style="align-items:center;margin:3px 0"><span style="flex:2">${CN[c.t]}</span>${c.v!=null&&!/^f/.test(c.t)?`<input type="number" style="flex:1;width:60px" value="${r1(c.t=='ang'?c.v*180/Math.PI:c.v)}" oninput="skCv(${i},+this.value)">`:'<span></span>'}<button style="flex:0" onclick="skCdel(${i})">✕</button></div>`).join('')||'<p class="mu">Aucune.</p>');
 h+=`<h4>Fonctions</h4><label>Longueur d’extrusion (mm)<input type="number" value="${sk.len}" oninput="sk.len=+this.value"></label><label>Angle de révolution (°)<input type="number" value="${sk.ang}" oninput="sk.ang=+this.value"></label><p class="mu">Extrusion : l’esquisse (X,Y) est extrudée selon Z. Révolution : X = rayon, Y = hauteur, autour de l’axe Z.</p>`;
 $('#pr').innerHTML=h}
function skSolid(rev){const sh=sk.sh;if(!sh.some(s=>!s.hole))return msg('Dessinez au moins une forme pleine.');
 if(rev){if(!(sk.ang>0&&sk.ang<=360))return msg('Angle entre 1° et 360°.');if(sh.some(s=>skPts(s).some(p=>p[0]<-1e-9)))return msg('Révolution : toutes les formes doivent avoir X ≥ 0.')}
 else if(!(sk.len>0))return msg('Longueur d’extrusion invalide.');
 const mk=(s,hole)=>{const P=skPts(s);return rev?revolve(P,sk.ang):translate([0,0,hole?-1:0],J.extrusions.extrudeLinear({height:sk.len+(hole?2:0)},J.geometries.geom2.fromPoints(P)))};
 let g=null;sh.filter(s=>!s.hole).forEach(s=>{const o=mk(s,0);g=g?union(g,o):o});sh.filter(s=>s.hole).forEach(s=>g=subtract(g,mk(s,1)));
 if(!G.toPolygons(g).length)return msg('Résultat vide.');return g}
let skEditing=0;
const skStore=k=>JSON.parse(JSON.stringify({k,P:sk.P,sh:sk.sh,cons:sk.cons,len:sk.len,ang:sk.ang,step:sk.step}));
function skFinish2(o,src){o.skSrc=src;if(skEditing){const old=objs.find(x=>x.id==skEditing);if(old){o.pos=[...old.pos];o.rot=[...old.rot];o.name=old.name;o.color=old.color;o.par=old.par;o.mat=old.mat;mk(o);rmObjs([old])}skEditing=0}select([o])}
function skEdit(o){if(!o||!o.skSrc)return msg('Cet élément n’a pas d’esquisse enregistrée.');const s=JSON.parse(JSON.stringify(o.skSrc));sk.P=s.P;sk.sh=s.sh;sk.cons=s.cons;sk.len=s.len;sk.ang=s.ang;sk.step=s.step||5;sk.sel=[];sk.ss=null;sk.cur=null;skEditing=o.id;if(!expert){expert=true;try{localStorage.setItem('cathia.expert','1')}catch(e){}}tabClick('Esquisse');try{skSolve()}catch(e){}skDraw();skui();msg('Modifiez l’esquisse, puis cliquez « '+(s.k=='rev'?'Révolution':'Extruder')+' » : la pièce est mise à jour.',7000)}
function skExtrude(){const g=skSolid(false);if(g){const o=addObj('mesh',{},g,'Extrusion '+nid,'#b8bcc4',[0,0,0]);skFinish2(o,skStore('ext'));tabClick('Créer')}}
function skRevolve(){const g=skSolid(true);if(!g)return;const ys=sk.sh.flatMap(s=>skPts(s).map(p=>p[1])),rs=sk.sh.flatMap(s=>skPts(s).map(p=>p[0])),o=addObj('mesh',{},g,'Révolution '+nid,'#b8bcc4',[0,0,0]);o.revAx={a:[0,0,Math.min(...ys)],b:[0,0,Math.max(...ys)],r:Math.max(...rs)};skFinish2(o,skStore('rev'));tabClick('Créer')}


/* =====================  Bibliothèque de modèles : mobilier du livre aux dimensions réglables  ===================== */
const eul=u=>{const q=new THREE.Quaternion().setFromUnitVectors(new THREE.Vector3(0,0,1),new THREE.Vector3(...nrm(u))),E=new THREE.Euler().setFromQuaternion(q,'ZYX');return[E.x/D,E.y/D,E.z/D]};
const bar=(name,A,B,d,par,col)=>{const v=sub(B,A);return mkObj('trav',{d,L:len(v)},null,name,col||WC[nid%4],A,eul(v),par)};
let EXSTY='hache';
const TJ=(T,R,o)=>{const df=tenonDefaults(T,R);try{return mkTenon(T,R,Object.assign({style:EXSTY,d:Math.max(8,Math.round(df.d)),mort:'thru'},o))}catch(e){throw new Error(T.name+' → '+R.name+' : '+e.message)}};
function drill(o,P,u,d,lab){const A=axisOf(o),L=2*(len(sub(A.p1,A.p0))+crossMin(o));o.ops.push({k:'hole',o:w2l(o,P),u:dw2l(o,nrm(u)),s0:-L,s1:L,r:d/2,lab});refresh(o)}
function drillBlind(o,P,u,d,depth,lab){o.ops.push({k:'hole',o:w2l(o,P),u:dw2l(o,nrm(u)),s0:-150,s1:depth,r:d/2,lab});refresh(o)}
/* demi-rondin : rondin fendu dans son axe, face plate tournée vers nf (vecteur monde) */
function halfLog(name,A,B,d,nf,par,col){const o=bar(name,A,B,d,par,col),dl=dw2l(o,nf),[e1,e2]=bas([0,0,1]),th=Math.atan2(dot(dl,e2),dot(dl,e1))/D,res=fendre(o,{mode:'demi',start:th-90,gap:0}),c0=mul(add(A,B),.5);let best=null,bv=1e18;res.forEach(p=>{const[mn,mx]=bounds([p]),v=dot(sub(mul(add(mn,mx),.5),c0),nf);if(v<bv){bv=v;best=p}});res.filter(x=>x!==best).forEach(x=>rmObjs([x]));best.name=name;best.par=par;return best}
const EXN={etabli:'Établi de camp',banc:'Banc court',fauteuil:'Fauteuil carré',bancdos:'Banc à dossier',bancdiag:'Banc à dossier (diagonales)',table:'Table à pieds en X',prepa:'Table de prépa',cuisine:'Table de prépa avec étagère',etagere:'Étagère',vaisselier:'Vaisselier',feu:'Table à feu'};
const EXQ={
 etabli:[['ten','Tenons','hache','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['L','Longueur des perches du corps (mm)',2500],['dP','Diamètre des perches (mm)',100],['dPed','Diamètre de la pédale (mm)',60],['ang','Inclinaison du corps (°)',20],['ecart','Écartement des pieds au sol (mm)',1000]],
 banc:[['ten','Tenons','hache','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['L','Longueur du banc (mm)',1500],['dL','Diamètre du rondin (mm, 200 au maximum)',200],['h','Hauteur de l’assise (mm)',450],['fendu','Rondin fendu en deux (assise plate)',1,'chk']],
 bancdos:[['ten','Tenons','scie','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['L','Longueur du banc (mm)',1400],['hs','Hauteur d’assise (mm)',440],['prof','Profondeur d’assise (mm)',420],['Ht','Hauteur du dossier (mm)',850],['ang','Inclinaison des montants arrière (°)',12],['dP','Diamètre des pieds et montants (mm)',70],['dS','Diamètre des rondins d’assise (mm, fendus en deux)',180],['dd','Diamètre du rondin du dossier (mm, fendu en deux)',140]],
 bancdiag:[['ten','Tenons','scie','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['L','Longueur du banc (mm)',1400],['hs','Hauteur d’assise (mm)',440],['Ht','Hauteur du dossier (mm)',900],['ang','Inclinaison des diagonales (pied + dossier) depuis la verticale (°)',25],['angJ','Inclinaison des jambes arrière (°)',15],['dD','Diamètre des diagonales (mm)',70],['dS','Diamètre du rondin d’assise (mm)',180],['dd','Diamètre du rondin du dossier (mm, fendu en deux)',140]],
 fauteuil:[['ten','Tenons','hache','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['larg','Largeur d’assise (mm)',650],['prof','Profondeur d’assise (mm)',500],['hs','Hauteur de l’assise (mm)',400],['hd','Hauteur totale du dossier (mm)',900]],
 table:[['ten','Tenons','scie','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['long','Longueur du plateau (mm)',1800],['larg','Largeur du plateau (mm)',800],['h','Hauteur du dessus du plateau (mm)',750],['mode','Plateau','tresse','sel',[['tresse','Claies tressées (sous, sur, sous)'],['droit','Claies droites dans des quarts de bois'],['filet','Filet de ficelle (maille serrée)']]],['maille','Maille du filet (mm)',30],['dc','Diamètre des claies (mm)',20],['c0','Début du clayage après la 1ʳᵉ jambe (mm)',0],['cl','Longueur clayée (mm), 0 = jusqu’à la dernière jambe',0],['tenC','Tenons de la traverse basse centrale','hache','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]]],
 prepa:[['ten','Tenons','scie','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['asm','Assemblage du cadre','mixte','sel',[['mixte','Optimisé : mi-bois dans le cadre, tenons aux pieds'],['tenons','Tenons uniquement'],['mibois','Mi-bois dans le cadre (chevillé par les pieds)']]],['long','Longueur du plateau (mm)',1600],['larg','Largeur du plateau (mm)',700],['h','Hauteur du plan de travail (mm), 900 = standard cuisine',900],['dr','Diamètre des rondins fendus du dessus (mm)',70],['dc','Diamètre des claies du dessous (mm)',20],['bas','Dessous en claies tressées',1,'chk']],
 cuisine:[['ten','Tenons','scie','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['asm','Assemblage du cadre','mixte','sel',[['mixte','Optimisé : mi-bois dans le cadre, tenons aux pieds'],['tenons','Tenons uniquement'],['mibois','Mi-bois dans le cadre (chevillé par les pieds)']]],['long','Longueur du plan de travail (mm)',1800],['larg','Profondeur du plan et de la colonne (mm)',700],['lc','Largeur de la colonne étagère (mm)',600],['h','Hauteur du plan de travail (mm), 900 = standard cuisine',900],['ht','Hauteur de la colonne étagère (mm), ≈ 2× le plan',1800],['cote','Colonne étagère','droite','sel',[['droite','À droite du plan de travail'],['gauche','À gauche du plan de travail']]],['etage','Étagère intermédiaire (haut et bas : filets)','claies','sel',[['claies','Claies en mi-bois (quart de bois)'],['filet','Filet de ficelle']]],['dr','Diamètre des rondins fendus du dessus (mm)',70],['dc','Diamètre des claies (mm)',20]],
 etagere:[['ten','Tenons','scie','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['asm','Assemblage du cadre','mixte','sel',[['mixte','Optimisé : mi-bois dans le cadre, tenons aux pieds'],['tenons','Tenons uniquement'],['mibois','Mi-bois dans le cadre (chevillé par les pieds)']]],['long','Longueur (mm)',1000],['larg','Profondeur (mm)',500],['h','Hauteur totale (mm)',1600],['h1','Hauteur de l’étagère basse, claies tressées (mm)',400],['h2','Hauteur de l’étagère médiane, quart de bois (mm)',900],['dc','Diamètre des claies (mm)',20],['maille','Maille du filet du haut (mm)',30]],
 vaisselier:[['ten','Tenons','scie','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['long','Longueur du plateau (mm)',900],['larg','Largeur du plateau (mm), à ajuster à la bassine',380],['h','Hauteur du dessus (mm)',750],['maille','Maille du filet (mm)',30]],
 feu:[['ten','Tenons','scie','sel',[['hache','Tenons à la hachette'],['scie','Tenons sciés']]],['asm','Assemblage du cadre','mixte','sel',[['mixte','Optimisé : mi-bois dans le cadre, tenons aux pieds'],['tenons','Tenons uniquement'],['mibois','Mi-bois dans le cadre (chevillé par les pieds)']]],['long','Longueur du plateau (mm)',1000],['larg','Largeur du plateau (mm)',800],['h','Hauteur du dessus (mm)',700],['ep','Épaisseur des planches (mm)',30],['lp','Largeur des planches (mm)',100]]};
/* cadre supérieur : 2 lisses + 2 traverses de largeur. Mi-bois aux angles (chevillés par les pieds taillés en tenon) ou tenons dans les pieds */
function topFrame(P,a,q,c){const {x0,x1,y,zt,dl,dc,rp,pl}=c,mb=q.asm!='tenons',tx=c.tallX,e=mb?30:2,L=[],C=[],cz=mb?zt:(c.crossZ??zt),blindE=-(rp+5),opt=mb?{mort:'blind'}:{};
 [-1,1].forEach(s=>{const ea=tx===x0?blindE:e,eb=tx===x1?blindE:e,b=bar(c.nameL||'Lisse haute',P(x0-rp-ea,s*y,zt),P(x1+rp+eb,s*y,zt),dl,a.id);L.push(b);if(!mb){TJ(b,pl[x0+','+s]);TJ(b,pl[x1+','+s])}else{if(tx===x0)TJ(b,pl[x0+','+s],opt);if(tx===x1)TJ(b,pl[x1+','+s],opt)}});
 [x0,x1].forEach(x=>{const tall=x===tx,ee=tall?blindE:e,zc=tall?zt-28:cz,b=bar('Traverse haute (largeur)',P(x,-y-rp-ee,zc),P(x,y+rp+ee,zc),dc,a.id);C.push(b);if(!mb||tall){TJ(b,pl[x+',-1'],tall?opt:{});TJ(b,pl[x+',1'],tall?opt:{})}});
 if(mb)[0,1].forEach(i=>[0,1].forEach(j=>{if((j?x1:x0)===tx)return;try{mkMibois(L[i],C[j],{pc:50})}catch(e){console.error('mibois',e)}const post=pl[(j?x1:x0)+','+(i?1:-1)],td=Math.min(30,Math.round(crossMin(post)/3));
  /* le tenon du pied traverse les deux mi-bois et dépasse de 2 mm au-dessus : il les cheville */
  try{TJ(post,C[j],{mort:'thru',d:td});drill(L[i],P(j?x1:x0,(i?1:-1)*y,zt),[0,0,1],td+1,'Mortaise du tenon du pied Ø'+(td+1))}catch(e){console.error('tenon cadre',e)}}));
 L.C=C;return L}
/* plateau de claies droites posées dans des quarts de bois sur deux traverses, entre quatre pieds */
/* traverses porteuses entre deux paires de pieds ; au pied « haut » (tall) le tenon est borgne et court, pour laisser la place à l'autre côté */
function railsBetween(P,a,c,name,z,d){const {x0,x1,yt,rp,pl}=c,s0=c.tall===x0?x0+5:x0-rp-2,s1=c.tall===x1?x1-5:x1+rp+2;return[-1,1].map(s=>{const b=bar(name,P(s0,s*yt,z),P(s1,s*yt,z),d,a.id);TJ(b,pl[x0+','+s],c.tall===x0?{mort:'blind'}:{});TJ(b,pl[x1+','+s],c.tall===x1?{mort:'blind'}:{});return b})}
function deckBuild(P,a,q,c){const {x0,x1,yt,zt,dt,rp,pl,dc}=c,g=newAsm(c.nm?c.nm[0].toUpperCase()+c.nm.slice(1):'Plateau',a.id),ox=P(0,0,0)[0];
  const rails=c.rails||railsBetween(P,a,c,'Traverse '+(c.nm||'haute'),zt,dt),r0=rails[0].pos[0]-ox;
  const from=(x0+rp+2)-r0+2,zone=x1-x0-2*rp-8;rails.forEach((rl,i)=>applyPlan(planQuart(rl,{start:from,len:zone,pos:i?0:270,mode:'quart'})));
  if(c.logs){const w=c.logs.d,n2=Math.floor((zone-10)/w),xs=k=>r0+from+w/2+k*w+(zone-n2*w)/2,o=mkObj('trav',{d:w,L:2*yt},null,'Rondin',WC[0],P(xs(0),-yt,c.logs.z),eul([0,1,0]),g.id),dl=dw2l(o,[0,0,-1]),[e1,e2]=bas([0,0,1]),th=Math.atan2(dot(dl,e2),dot(dl,e1))/D,res=fendre(o,{mode:'demi',start:th-90,gap:0}),h=res[0];res.slice(1).forEach(x=>rmObjs([x]));h.name='Rondin fendu (demi)';h.par=g.id;const jm=new Map();for(let k=1;k<n2;k++){const[cp]=cloneObjs([h],xs(k)-xs(0),jm,null,false);cp.par=g.id}select([],null);return rails}
  const n=Math.floor(zone/dc);for(let k=0;k<n;k++){const x=r0+from+dc/2+k*dc+(zone-n*dc)/2;bar('Claie '+(k+1),P(x,-yt,zt+dc/2),P(x,yt,zt+dc/2),dc,g.id,'#b5894f')}return rails}
/* claies tressées (sous, sur, sous) entre deux traverses et une traverse fine centrale ; la traverse fine repose en mi-bois sur deux traverses de largeur */
function weaveDeck(P,a,q,c){const {x0,x1,yt,zt,dt,rp,pl,dc}=c,g=newAsm(c.nm[0].toUpperCase()+c.nm.slice(1),a.id);
  const rails=c.rails||railsBetween(P,a,c,'Traverse '+c.nm.split(' ')[0],zt,dt);
  const wz=zt-28,sh=c.wbars||[],wb=[x0,x1].map((x,i)=>{if(sh[i])return sh[i];const b=bar('Traverse de largeur ('+c.nm.split(' ')[0]+')',P(x,-yt-rp-2,wz),P(x,yt+rp+2,wz),40,a.id);TJ(b,pl[x+',-1']);TJ(b,pl[x+',1']);return b});
  const m0=sh[0]||c.half0?x0:x0-12,m1=sh[1]||c.half1?x1:x1+12,mid=bar('Traverse fine centrale',P(m0,0,zt),P(m1,0,zt),30,a.id,'#d2ab76');wb.forEach(b=>{try{mkMibois(mid,b,{pc:50})}catch(e){console.error('mi-bois traverse fine',e)}});
  const from=(x0+rp+6)-Math.max(rails[0].pos[0]-P(0,0,0)[0],m0),zone=x1-x0-2*rp-12;
  const pln=claiePlan([rails[0],mid,rails[1]],{d:dc,pm:'libre',pitch:dc,margin:0,from,zone,over:0,start:'sous',taper:true});pln.rods.forEach(r=>mkObj('courbe',{pts:r.pts,d0:r.d0,d1:r.d1,len:0},null,r.name,'#b5894f',r.pos,[0,0,0],g.id));rails.wb=wb;return rails}
const EXB={
 etabli(P,a,q){if(q.ecart<800)throw new Error('Établi instable : écartez les pieds d’au moins 80 cm au sol, sinon il bascule sur le côté quand on appuie sur la pédale.');
  const al=q.ang*D,dir=[Math.cos(al),0,Math.sin(al)],n0=[-Math.sin(al),0,Math.cos(al)],dp=q.dP,r=dp/2,L=q.L,web=30,yy=(dp+14)/2,z0=Math.max(r,q.dPed/2),base=y=>P(0,y,z0),at=(y,s)=>add(base(y),mul(dir,s));
  if(L<1600)throw new Error('Perches trop courtes (1,60 m au minimum).');
  /* CORPS : deux perches parallèles séparées par une fente (la pédale y entre par son bout plat) */
  const pe=[-1,1].map((s,i)=>bar(i?'Perche droite':'Perche gauche',base(s*yy),at(s*yy,L),dp,a.id));
  pe.forEach((p,i)=>{const sd=i?1:-1,Cw=at(sd*(yy-r+8),225);p.ops.push({k:'obox',c:w2l(p,Cw),e1:dw2l(p,[0,1,0]),e2:dw2l(p,dir),h:[10,225,r*.8],lab:'Encoche de 0,45 m pour le bout plat de la pédale'});refresh(p)});
  const td=32,tn='Cheville Ø32',tc='#8a5a2b';
  /* liaison basse des perches, et articulation de la pédale (à 0,15 m du bas) */
  bar(`${tn} (à 0,40 m du bas)`,at(-(yy+r+5),400),at(yy+r+5,400),td,a.id,tc);pe.forEach((p,i)=>drill(p,at((i?1:-1)*yy,400),[0,1,0],td+1,'Trou de '+tn.toLowerCase()+' Ø'+(td+1)));
  bar(`${tn} d’articulation (à 0,15 m du bas)`,at(-(yy+r+5),150),at(yy+r+5,150),td,a.id,tc);pe.forEach((p,i)=>drill(p,at((i?1:-1)*yy,150),[0,1,0],td+1,'Trou de l’articulation Ø'+(td+1)));
  /* PIEDS ×2 en A, tenonnés (borgne) dans les perches, juste sous la cheville du haut */
  const sc=L-50,sp=sc-160;[-1,1].forEach((s,i)=>{const T=at(s*yy,sp),F=[T[0]-60,P(0,s*q.ecart/2,0)[1],0],v=nrm(sub(T,F)),pied=bar(i?'Pied droit':'Pied gauche',F,add(T,mul(v,r*.4)),40,a.id);TJ(pied,pe[i],{d:28,mort:'blind'})});
  /* cheville de liaison des perches, à 5 cm du bout */
  bar('Cheville de liaison des perches',at(-(yy+r+12),sc),at(yy+r+12,sc),30,a.id,'#8a5a2b');pe.forEach((p,i)=>drill(p,at((i?1:-1)*yy,sc),[0,1,0],31,'Trou de la cheville de liaison Ø31 (à 5 cm du bout)'));
  /* ÉLÉMENT À USINER : rondin couché dans la gorge des deux perches, dans leur prolongement ; il dépasse de 10 cm au bout pour pouvoir le travailler */
  const rl=60,Ll=900,hz=Math.sqrt(Math.max(1,(rl+r)*(rl+r)-yy*yy)),sLo=L+100-Ll,Cl=add(at(0,sLo+Ll/2),mul(n0,hz));bar('Élément à usiner (rondin)',add(at(0,sLo),mul(n0,hz)),add(at(0,L+100),mul(n0,hz)),2*rl,a.id,'#9bb07a');
  /* chevilles d’arrêt : juste sous le bout bas du rondin, il ne peut pas glisser */
  [-1,1].forEach((sd,i)=>{const s=sLo-28,nt=nrm(add(n0,[0,sd*.25,0])),C=add(at(sd*yy,s),mul(nt,r*.55));drillBlind(pe[i],C,mul(nt,-1),26,50,'Trou de cheville d’arrêt Ø26');bar(`Cheville d’arrêt ${i+1}`,add(C,mul(nt,-45)),add(C,mul(nt,55)),24,a.id,'#8a5a2b')});
  /* PÉDALE : levier articulé en bas du corps ; son bout libre est à 15 cm du sol pour pouvoir appuyer dessus */
  /* la pédale va jusqu'un peu au-delà du bout haut de l'établi (place pour le pied) et commence 10 cm derrière son axe (la cheville d'articulation traverse bien le bois) */
  const Pv=at(0,150),xp=Cl[0],xe=Math.max(xp+180,at(0,L)[0]+60),zE=150,pz=x=>Pv[2]+(x-Pv[0])*(zE-Pv[2])/(xe-Pv[0]),xq=Pv[0]-100,ped=bar('Pédale',[xq,Pv[1],pz(xq)],[xe,Pv[1],zE],q.dPed,a.id,'#d2ab76');
  {const R=q.dPed/2+5,nl0=dw2l(ped,[0,1,0]);let nl=[nl0[0],nl0[1],0];nl=len(nl)>.1?nrm(nl):[1,0,0];const e2=cr([0,0,1],nl);
   [-1,1].forEach(sg=>{ped.ops.push({k:'obox',c:add(mul(nl,sg*(web/2+(R-web/2)/2)),[0,0,175]),e1:nl,e2,h:[(R-web/2)/2,R+5,175],lab:'Bout aplati (mi-plat) de 0,35 m : épaisseur '+web+' mm'})});refresh(ped)}
  drill(ped,Pv,[0,1,0],td+1,'Trou d’articulation de la pédale');
  /* PALONNIER : barre dans le plan de la pédale, sous les perches, à 20 cm au-dessus de la pédale ; ses bouts sont sous les deux boucles de ficelle */
  const lp=[-250,250].map(of=>add(Cl,mul(dir,of))),xa=lp[0][0],xb=lp[1][0],zPal=pz(xp)+q.dPed/2+200,Pp=[xp,0,zPal],pal=bar('Palonnier',[xa-30,0,zPal],[xb+30,0,zPal],40,a.id,'#d2ab76');
  [xa,xp,xb].forEach((x,k)=>drill(pal,[x,0,zPal],[0,0,1],10,'Trou de corde Ø10'+(k==1?' (centre, vers la pédale)':'')));
  const segs=[];
  /* deux boucles de ficelle autour du rondin : elles passent entre les perches et descendent aux bouts du palonnier */
  lp.forEach((Cc,k)=>{const pts=[];for(let t=0;t<=24;t++){const th=2*Math.PI*t/24;pts.push(add(Cc,add(mul(n0,Math.cos(th)*(rl+4)),[0,Math.sin(th)*(rl+4),0])))}for(let t=0;t<24;t++)segs.push([pts[t],pts[t+1]]);segs.push([[k?xb:xa,0,zPal],add(Cc,mul(n0,-(rl+4)))])});
  /* une seule corde du centre du palonnier vers la pédale : en appuyant, le rondin est serré contre les perches */
  segs.push([Pp,[xp,0,pz(xp)+q.dPed/2]]);
  if(!q.pv)mkObj('ph',{segs,d:8,kind:'corde'},null,'Cordes du palonnier','#cfc8b8',[0,0,0],[0,0,0],a.id)},
 banc(P,a,q){const dL=Math.min(q.dL,200),L=q.L,h=q.h,zc=q.fendu?h:h-dL/2;let seat=mkObj('trav',{d:dL,L},null,'Rondin du banc','#d2ab76',P(0,0,zc),[0,90,0],a.id);
  if(q.fendu){const parts=fendre(seat,{mode:'demi',start:0,gap:0});seat=parts.find(p=>(bounds([p])[0][2]+bounds([p])[1][2])/2<zc)||parts[1];parts.filter(p=>p!==seat).forEach(p=>rmObjs([p]));seat.name='Assise (demi-rondin)';seat.par=a.id}
  const f=dL*.9+60;[L*.14,L*.86].forEach(x=>[-1,1].forEach(s=>{const C=P(x,0,zc),F=P(x,s*f,0),T=add(F,mul(sub(C,F),(q.fendu?zc-20:zc)/zc)),pd=bar(`Pied ${x<L/2?'gauche':'droit'} ${s<0?'avant':'arrière'}`,F,T,50,a.id);TJ(pd,seat,{d:28,mort:'blind'})}))},
 prepa(P,a,q){const Lp=q.long,Wp=q.larg,H=q.h,dc=q.dc,dt=50,dr=q.dr||70,ep=dr/2,zt=H-ep,x0=60,x1=Lp-60,yt=(Wp-dt)/2,rp=35,mb=q.asm!='tenons';
  if(Lp<800||Wp<400||H<400)throw new Error('Table trop petite.');if(dc<8||dc>20)throw new Error('Diamètre des claies : de 8 à 20 mm.');
  const pl={};[[x0,-1],[x0,1],[x1,-1],[x1,1]].forEach(([x,s])=>pl[x+','+s]=bar(`Pied ${x<Lp/2?'gauche':'droit'} ${s<0?'avant':'arrière'}`,P(x,s*yt,0),P(x,s*yt,(x==x1&&q.tall)?q.tall:(mb?zt+27:zt+70)),70,a.id));
  const rails=topFrame(P,a,q,{x0,x1,y:yt,zt,dl:dt,dc:50,rp,pl,crossZ:zt-80,nameL:'Traverse du plateau',tallX:q.tall?x1:undefined}),C=rails.C;
  deckBuild(P,a,q,{x0,x1,yt,zt,dt,rp,pl,dc,nm:'plateau (rondins fendus)',logs:{d:dr,z:H},rails});
  [x0,x1].forEach(x=>{const b=bar('Traverse basse',P(x,-yt-rp-2,180),P(x,yt+rp+2,180),50,a.id);TJ(b,pl[x+',-1']);TJ(b,pl[x+',1'])});
  let under=null;if(q.bas)under=weaveDeck(P,a,q,{x0,x1,yt,zt:Math.round(H/2)-35,dt:40,rp,pl,dc,nm:'dessous (claies tressées)',tall:q.tall?x1:undefined,half1:!!q.tall});return{pl,x0,x1,yt,rp,H,C,under}},
 cuisine(P,a,q){const Wc=q.lc||600,H=q.h,ht=q.ht,dc=q.dc,ty=q.etage||'claies',ztop=ht-25;
  if(ht<H+500)throw new Error('La colonne doit dépasser le plan de travail d’au moins 50 cm.');
  /* plan de travail (table de prépa) ; ses pieds côté colonne montent jusqu'en haut de la colonne */
  const r=EXB.prepa(P,a,{...q,tall:ztop+27}),{pl,x1,yt,rp}=r,x2=x1+Wc,c={x0:x1,x1:x2,yt,rp,pl,tall:x1};
  [-1,1].forEach(s=>pl[x2+','+s]=bar(`Montant étagère ${s<0?'avant':'arrière'}`,P(x2,s*yt,0),P(x2,s*yt,ztop+27),70,a.id));
  [x2].forEach(x=>{const b=bar('Traverse basse étagère (largeur)',P(x,-yt-rp-2,180),P(x,yt+rp+2,180),50,a.id);TJ(b,pl[x+',-1']);TJ(b,pl[x+',1'])});
  /* étagères à intervalles réguliers : mi-hauteur du plan, dans le prolongement du plan de travail, puis une fois et demie */
  [H/2,H,1.5*H].filter(z=>z<ztop-250).forEach((z,i)=>{z=Math.round(z);const nm='étagère '+(i+1)+(Math.abs(z-H)<1?' (prolonge le plan de travail)':'');
   if(ty=='tresse'){const shx=Math.abs(z-Math.round(H/2))<1&&r.under?r.under.wb[1]:Math.abs(z-H)<1&&r.C&&q.asm!='tenons'?r.C[1]:null;weaveDeck(P,a,q,{...c,zt:z-35,dt:50,dc,nm:nm+' (claies tressées)',wbars:[shx,null],half0:true})}
   else if(ty=='filet'){railsBetween(P,a,c,'Traverse '+nm+' (filet)',z,50);const g2=newAsm('Filet '+nm,a.id),zr=z+26,pa=t=>P(x1+rp+4+t,yt,zr),pb=t=>P(x1+rp+4+t,-yt,zr);
    mkObj('ph',{segs:netSegsOn(pa,pb,0,x2-x1-2*rp-8,2*yt,{pitch:q.maille||30,pat:'carre'}),d:2,kind:'filet'},null,'Filet de ficelle','#cfc8b8',[0,0,0],[0,0,0],g2.id)}
   else deckBuild(P,a,q,{...c,zt:z-dc,dt:50,dc,nm:nm+' (claies droites)'})});
  /* dessus de la colonne : cadre en mi-bois chevillé par les tenons des montants, côté plan tenonné dans les pieds hauts ; claies droites dessus */
  const top=topFrame(P,a,q,{x0:x1,x1:x2,y:yt,zt:ztop,dl:50,dc:50,rp,pl,nameL:'Lisse haute étagère',tallX:x1,crossZ:ztop-80});
  deckBuild(P,a,q,{...c,zt:ztop,dt:50,dc,nm:'dessus de la colonne (claies droites)',rails:top});
  /* colonne à gauche : on tourne tout l'ensemble de 180° autour de la verticale (le plan est symétrique avant/arrière) */
  if(q.cote=='gauche'){const L=piecesOf(a.id),[mn,mx]=bounds(L),cc=[(mn[0]+mx[0])/2,(mn[1]+mx[1])/2,0],R=new THREE.Matrix4().makeTranslation(cc[0],cc[1],0).multiply(new THREE.Matrix4().makeRotationZ(Math.PI)).multiply(new THREE.Matrix4().makeTranslation(-cc[0],-cc[1],0));
   L.forEach(o=>{const M0=new THREE.Matrix4().compose(new THREE.Vector3(...o.pos),new THREE.Quaternion().setFromEuler(new THREE.Euler(o.rot[0]*D,o.rot[1]*D,o.rot[2]*D,'ZYX')),new THREE.Vector3(1,1,1));setMat(o,R.clone().multiply(M0))})}},
 etagere(P,a,q){const Lp=q.long,Wp=q.larg,H=q.h,dc=q.dc,x0=60,x1=Lp-60,yt=(Wp-40)/2,rp=35;if(H<q.h2+250||q.h2<q.h1+250)throw new Error('Hauteurs incohérentes : basse < médiane < hauteur totale.');
  const pl={};[[x0,-1],[x0,1],[x1,-1],[x1,1]].forEach(([x,s])=>pl[x+','+s]=bar(`Montant ${x<Lp/2?'gauche':'droit'} ${s<0?'avant':'arrière'}`,P(x,s*yt,0),P(x,s*yt,q.asm=='tenons'?H:H-63),70,a.id));
  [x0,x1].forEach(x=>{const b=bar('Traverse basse (largeur)',P(x,-yt-rp-2,Math.min(160,q.h1-120)),P(x,yt+rp+2,Math.min(160,q.h1-120)),50,a.id);TJ(b,pl[x+',-1']);TJ(b,pl[x+',1'])});
  weaveDeck(P,a,q,{x0,x1,yt,zt:q.h1-35,dt:50,rp,pl,dc,nm:'étagère basse (claies tressées)'});
  deckBuild(P,a,q,{x0,x1,yt,zt:q.h2-dc,dt:50,rp,pl,dc,nm:'étagère médiane (quart de bois)'});
  const zt=H-90;topFrame(P,a,q,{x0,x1,y:yt,zt,dl:50,dc:50,rp,pl});
  const g=newAsm('Filet du haut',a.id),zr=zt+26,pa=t=>P(x0+rp+4+t,yt,zr),pb=t=>P(x0+rp+4+t,-yt,zr),segs=netSegsOn(pa,pb,0,x1-x0-2*rp-8,2*yt,{pitch:q.maille||30,pat:'carre'});mkObj('ph',{segs,d:2,kind:'filet'},null,'Filet de ficelle','#cfc8b8',[0,0,0],[0,0,0],g.id)},
 vaisselier(P,a,q){EXB.table(P,a,{...q,mode:'filet',dc:20,c0:0,cl:0})},
 feu(P,a,q){const Lp=q.long,Wp=q.larg,H=q.h,x0=70,x1=Lp-70,y1=Wp/2-45,zt=H-40,rp=40,mb=q.asm!='tenons';if(q.ep<15||q.lp<40)throw new Error('Planches trop fines.');
  const pl={};[[x0,-1],[x0,1],[x1,-1],[x1,1]].forEach(([x,s])=>pl[x+','+s]=bar(`Pied ${x<Lp/2?'gauche':'droit'} ${s<0?'avant':'arrière'}`,P(x,s*y1,0),P(x,s*y1,mb?zt+27:H),80,a.id));
  const topFrame0=topFrame(P,a,q,{x0,x1,y:y1,zt,dl:60,dc:60,rp,pl,nameL:'Lisse longue'});
  /* plateau : rondins fendus posés à plat sur les lisses, assemblés en mi-bois avec elles */
  const lp=Math.max(40,q.lp),n=Math.floor((x1-x0-2*rp-6)/lp),X0=x0+rp+3+((x1-x0-2*rp-6)-n*lp)/2,lis=topFrame0;
  for(let i=0;i<n;i++){const o=mkObj('trav',{d:lp,L:Wp},null,'Rondin',WC[i%4],P(X0+lp/2+i*lp,-Wp/2,zt+8),eul([0,1,0]),a.id),dl=dw2l(o,[0,0,-1]),[e1,e2]=bas([0,0,1]),th=Math.atan2(dot(dl,e2),dot(dl,e1))/D,res=fendre(o,{mode:'demi',start:th-90,gap:0}),h=res[0];res.slice(1).forEach(x=>rmObjs([x]));h.name='Rondin fendu (demi)';h.par=a.id;
   lis.forEach(l=>{try{mkMibois(h,l,{pc:50})}catch(e){console.error('mi-bois planche',e)}})}},
 bancdos(P,a,q){const L=q.L,hs=q.hs,Ht=q.Ht,al=q.ang*D,ta=Math.tan(al),pr=q.prof,dS=q.dS,rS=dS/2,dP=q.dP,yy=L/2-110,zr=hs-rS+20,zl=150,zx=230;
  if(q.ang<6||q.ang>20)throw new Error('Inclinaison des montants arrière : entre 6° et 20°.');if(Ht<hs+300)throw new Error('Le dossier doit dépasser l’assise d’au moins 30 cm.');if(pr<2*dS+20)throw new Error('Profondeur d’assise trop faible pour deux demi-rondins de Ø'+dS+' mm.');
  /* montant arrière : pied arrière + support du dossier, d'un seul bâton incliné vers l'arrière ; à hauteur d'assise il est au fond du siège */
  const xr0=pr-zr*ta,xa=z=>xr0+z*ta;if(xr0<pr*.55+60)throw new Error('Banc instable : augmentez la profondeur ou réduisez l’inclinaison du dossier.');
  const side=[-1,1].map(s=>{const nm=s<0?'gauche':'droit',fl=bar(`Pied avant ${nm}`,P(0,s*yy,0),P(0,s*yy,zr+25+2),dP,a.id),rp=bar(`Montant arrière ${nm} (pied et dossier)`,P(xr0,s*yy,0),P(xa(Ht),s*yy,Ht),dP,a.id);
   /* traverse d'assise : le tenon du pied avant la traverse ; son bout arrière est tenonné dans le montant */
   const sr=bar(`Traverse d’assise ${nm}`,P(-45,s*yy,zr),P(xa(zr)+dP*.1,s*yy,zr),50,a.id);TJ(fl,sr,{d:24,mort:'thru'});TJ(sr,rp,{d:20,mort:'blind'});
   const lr=bar(`Traverse basse ${nm}`,P(dP*.1-dP/2+dP*.4,s*yy,zl),P(xa(zl)-dP*.1,s*yy,zl),40,a.id);TJ(lr,fl,{d:18,mort:'blind'});TJ(lr,rp,{d:18,mort:'blind'});
   return{fl,rp,sr}});
  /* entretoises de largeur (plus haut que les traverses basses pour ne pas se croiser dans les pieds) */
  [['avant',x=>0,'fl'],['arrière',xa,'rp']].forEach(([nm,fx,k])=>{const b=bar(`Entretoise ${nm}`,P(fx(zx),-yy+dP*.1,zx),P(fx(zx),yy-dP*.1,zx),40,a.id);TJ(b,side[0][k],{d:18,mort:'blind'});TJ(b,side[1][k],{d:18,mort:'blind'})});
  /* assise : deux demi-rondins, face plate en dessus, en mi-bois sur les traverses d'assise et chevillés */
  const xEnd=pr-dP/2-6,xs=[xEnd-3*rS-6,xEnd-rS];xs.forEach((x,i)=>{const h=halfLog(`Assise ${i+1} (rondin fendu)`,P(x,-L/2,hs),P(x,L/2,hs),dS,[0,0,1],a.id,'#d2ab76');side.forEach(sd=>{try{mkMibois(h,sd.sr,{pc:50});applyPlan(planCheville([h,sd.sr],{d:16,axis:'auto',lap:true}))}catch(e){console.error('assise',e)}})});
  /* dossier : demi-rondin devant les montants, face plate vers le dos, en mi-bois et chevillé */
  const zb=Math.min(Ht-q.dd/2-40,hs+280),off=(dP/2+q.dd/2)*.7,bk=halfLog('Dossier (rondin fendu)',P(xa(zb)-off,-(yy+dP),zb),P(xa(zb)-off,yy+dP,zb),q.dd,[-Math.cos(al),0,Math.sin(al)],a.id,WC[1]);
  side.forEach(sd=>{try{mkMibois(bk,sd.rp,{pc:50});applyPlan(planCheville([bk,sd.rp],{d:16,axis:'auto',lap:true}))}catch(e){console.error('dossier',e)}})},
 bancdiag(P,a,q){const L=q.L,hs=q.hs,Ht=q.Ht,al=q.ang*D,ta=Math.tan(al),be=q.angJ*D,tb=Math.tan(be),dD=q.dD,dS=q.dS,yy=L/2-60,yl=yy-110,zs=hs-dS/2,xs=zs*ta,xD=z=>z*ta;
  if(q.ang<18||q.ang>32)throw new Error('Inclinaison des diagonales : entre 18° et 32° (en dessous le dossier est trop droit, au-dessus le banc s’écrase).');if(q.angJ<5||q.angJ>25)throw new Error('Inclinaison des jambes arrière : entre 5° et 25°.');if(Ht<hs+300)throw new Error('Le dossier doit dépasser l’assise d’au moins 30 cm.');
  /* chaque côté : une diagonale qui part du sol à l'avant et monte vers l'arrière ; elle est à la fois pied avant et support du dossier */
  const Dg=[-1,1].map(s=>bar(`Diagonale ${s<0?'gauche':'droite'} (pied avant et dossier)`,P(0,s*yy,0),P(xD(Ht),s*yy,Ht),dD,a.id));
  /* assise : un rondin avec un tenon plat à chaque bout, dans les diagonales */
  const seat=bar('Assise (rondin)',P(xs,-yy,zs),P(xs,yy,zs),dS,a.id,'#d2ab76'),tp={style:'plat',d:Math.round(dS/4),W:Math.round(Math.min(dS*.5,dD*.8)),mort:'blind'};TJ(seat,Dg[0],tp);TJ(seat,Dg[1],tp);
  /* jambes arrière : peu inclinées, leur tenon entre par-dessous dans le rondin d'assise */
  const xr=xs+zs*tb,legs=[-1,1].map(s=>bar(`Jambe arrière ${s<0?'gauche':'droite'}`,P(xr,s*yl,0),P(xs,s*yl,zs),dD-10,a.id));legs.forEach(l=>TJ(l,seat,{d:24,mort:'blind'}));
  /* traverses basses de côté : ferment le triangle diagonale / jambe, l'angle ne peut plus s'ouvrir */
  const zl=170,xl=z=>xr+(xs-xr)*z/zs;[-1,1].forEach((s,i)=>{const b=bar(`Traverse basse ${s<0?'gauche':'droite'}`,P(xD(zl)+dD*.1,s*yy,zl),P(xl(zl)-dD*.1,s*yl,zl),40,a.id);TJ(b,Dg[i],{d:18,mort:'blind'});TJ(b,legs[i],{d:18,mort:'blind'})});
  const zr=Math.max(zl+40,zs-dS/2-40),st=bar('Entretoise arrière',P(xl(zr),-yl+12,zr),P(xl(zr),yl-12,zr),40,a.id);TJ(st,legs[0],{d:18,mort:'blind'});TJ(st,legs[1],{d:18,mort:'blind'});
  /* dossier : demi-rondin devant les diagonales, face plate vers le dos, en mi-bois et chevillé */
  const zb=Math.min(Ht-q.dd/2-30,hs+(Ht-hs)*.6),off=(dD/2+q.dd/2)*.7,bk=halfLog('Dossier (rondin fendu)',P(xD(zb)-off,-(yy+dD),zb),P(xD(zb)-off,yy+dD,zb),q.dd,[-Math.cos(al),0,Math.sin(al)],a.id,WC[1]);
  Dg.forEach(dg=>{try{mkMibois(bk,dg,{pc:50});applyPlan(planCheville([bk,dg],{d:16,axis:'auto',lap:true}))}catch(e){console.error('dossier',e)}})},
 fauteuil(P,a,q){const r=27.5,E=r+2,W=q.larg,Dp=q.prof,hs=q.hs,hd=q.hd,ar=1.425*hs,Hf=ar+30,ft={};
  [['avant',0,Hf],['arrière',Dp,hd]].forEach(([n,x,h])=>[['gauche',0],['droit',W]].forEach(([m,y])=>{ft[n+m]=bar(`Pied ${n} ${m}`,P(x,y,0),P(x,y,h),55,a.id)}));
  const sides=[[.325*hs,25,'Bâton de chaise bas'],[.675*hs,25,'Bâton de chaise haut'],[hs,50,'Support de siège']];
  [['gauche',0],['droit',W]].forEach(([m,y])=>{sides.forEach(([z,d,n])=>{const b=bar(`${n} ${m}`,P(-E,y,z),P(Dp+E,y,z),d,a.id);TJ(b,ft['avant'+m]);TJ(b,ft['arrière'+m])});
   const A_=bar('Accoudoir '+m,P(-100,y,ar),P(Dp+E,y,ar),50,a.id,'#d2ab76');TJ(ft['avant'+m],A_,{d:34});TJ(A_,ft['arrière'+m],{d:22})});
  [[0,.45*hs,30,'avant'],[Dp,.45*hs,30,'arrière'],[Dp,hd*.52,30,'arrière'],[Dp,hd*.83,30,'arrière'],[Dp,hd*.955,40,'arrière haut']].forEach(([x,z,d,n])=>{const b=bar(`Traverse ${n} ${Math.round(z)}`,P(x,-E,z),P(x,W+E,z),d,a.id);TJ(b,ft[(x?'arrière':'avant')+'gauche']);TJ(b,ft[(x?'arrière':'avant')+'droit'])});
  const sup=objs.filter(o=>o.name.startsWith('Support de siège')).slice(-2),n=Math.min(8,Math.floor((Dp-120)/70)+1);
  for(let i=0;i<n;i++){const x=60+i*70,b=bar('Bâton de siège '+(i+1),P(x,-27,hs),P(x,W+27,hs),25,a.id,'#d2ab76');TJ(b,sup[0],{d:14});TJ(b,sup[1],{d:14})}},
 table(P,a,q){const Lp=q.long,Wp=q.larg,H=q.h,dc=q.dc,dt=50,rt=dt/2,dm=30,straight=q.mode=='droit',fil=q.mode=='filet',zt=straight?H-dc:fil?H-rt-2:H-rt-dc,Hl=H,x1=Math.max(70,Math.round(Lp*.07)),x2=Lp-x1,zc=Hl/2;
  if(Lp<700||Wp<(fil?300:500))throw new Error('Plateau trop petit.');if(H<500||H>900)throw new Error('Hauteur du plateau : de 50 à 90 cm (75 cm pour une table).');if(dc<8||dc>20)throw new Error('Diamètre des claies : de 8 à 20 mm.');
  const k=2*zt/Hl-1,yt=(straight||fil)?(Wp-dt)/2:(Wp/2-70)*k,yw=yt/k,legsA=[],legsB=[];
  [x1,x2].forEach((x,i)=>{const A=bar(`X${i+1} pied montant`,P(x,-yw,0),P(x,yw,Hl),60,a.id),B=bar(`X${i+1} pied descendant`,P(x,yw,0),P(x,-yw,Hl),60,a.id);legsA.push(A);legsB.push(B);mkMibois(A,B,{pc:50})});
  const rails=[[yt,legsA,'Traverse haute 1'],[-yt,legsB,'Traverse haute 2']].map(([y,L,n])=>{const b=bar(n,P(x1-32,y,zt),P(x2+32,y,zt),dt,a.id);TJ(b,L[0],{d:20});TJ(b,L[1],{d:20});return b});
  const c=bar('Traverse basse centrale',P(x1-32,0,zc),P(x2+32,0,zc),40,a.id);TJ(c,legsA[0],{d:20,style:q.tenC});TJ(c,legsA[1],{d:20,style:q.tenC});drill(legsB[0],P(x1,0,zc),[1,0,0],22,'Trou de la traverse centrale');drill(legsB[1],P(x2,0,zc),[1,0,0],22,'Trou de la traverse centrale');
  /* 4ᵉ traverse, plus fine, à mi-distance des deux traverses du plateau, portée par des poteaux : les claies passent dessous / dessus / dessous */
  /* 4ᵉ traverse plus fine, à mi-distance des deux traverses du plateau : elle n’a pas besoin de support, la tension des claies la maintient */
  const zm=straight?zt-dm/2:zt,mid=fil?null:bar('Traverse fine centrale',P(x1-32,0,zm),P(x2+32,0,zm),dm,a.id,'#d2ab76');
  const lo=x1-32,from=66+(q.c0||0),zone=q.cl>0?q.cl:(x2-x1)-68,pitch=dc,ca=newAsm('Plateau de claies',a.id);
  if(fil){const zr=zt+rt+1,pa=t=>P(lo+t,yt,zr),pb=t=>P(lo+t,-yt,zr),segs=netSegsOn(pa,pb,from,zone,2*yt,{pitch:q.maille||30,pat:'carre'});mkObj('ph',{segs,d:2,kind:'filet'},null,'Filet de ficelle','#cfc8b8',[0,0,0],[0,0,0],ca.id)}
  else if(!straight){const pl=claiePlan([rails[0],mid,rails[1]],{d:dc,pm:'libre',pitch,margin:0,from,zone,over:0,start:'sous',taper:true});
   pl.rods.forEach(r=>mkObj('courbe',{pts:r.pts,d0:r.d0,d1:r.d1,len:0},null,r.name,'#b5894f',r.pos,[0,0,0],ca.id));
  }
  else{rails.forEach((rl,i)=>applyPlan(planQuart(rl,{start:Math.max(0,from-0),len:Math.min(zone,2*(x2-x1)),pos:i?270:0,mode:'quart'})));
   const n=Math.floor((zone-dc)/pitch)+1,N=Math.max(1,Math.round(q.cavN||3));
   for(let i=0;i<n;i++){const x=lo+from+dc/2+i*pitch;bar('Claie '+(i+1),P(x,-yt,zt+dc/2),P(x,yt,zt+dc/2),dc,ca.id,'#b5894f');}
  }}};
/* construit dans un espace temporaire pour l'aperçu, sans toucher au projet */
function buildTemp(k,q){EXSTY=q.ten||'hache';const sv={objs:objs.slice(),asms:{...asms},nid,aid,JID,sel:sel.slice(),selA},seen=new Set(objs);let items=[];
 try{const a=newAsm(EXN[k]);batch(()=>EXB[k]((x,y,z)=>[x,y,z],a,{...q,pv:true}));
  items=objs.filter(o=>!seen.has(o)).map(o=>{const ls=o.m.children.find(c=>c.isLineSegments);return{tg:o.m.geometry,eg:ls&&ls.geometry,pos:o.pos,rot:o.rot,color:o.color}})}
 finally{objs.filter(o=>!seen.has(o)).forEach(o=>sc.remove(o.m));objs=sv.objs;asms=sv.asms;nid=sv.nid;aid=sv.aid;JID=sv.JID;sel=sv.sel;selA=sv.selA;ui()}
 return items}
function exWin(k){const F=EXQ[k];
 opWin({title:EXN[k],intro:'Réglez les dimensions : l’aperçu est reconstruit. Les assemblages (tenons, mortaises, mi-bois) sont créés avec le meuble.',ok:'Créer le meuble',delay:500,
  fields:V=>F.map(([id,l,v,t,o])=>({k:id,l,t:t||'num',v,o,rb:t=='sel'||id=='cav'?1:0})).filter(f=>!(f.k=='cavN'&&!V.cav)).concat([{k:'mt',l:'Voir ensuite le montage pas à pas (geste par geste : créer, incliner, assembler)',t:'chk',v:false}]),
  preview:V=>{const q=exQ(k,V);const items=buildTemp(k,q);return{items,view:{dir:[.6,-.85,.6]},warn:[]}},
  apply:V=>exBuild(k,V)})}
const exQ=(k,V)=>{const q={};EXQ[k].forEach(([id,,v,t])=>q[id]=t=='chk'?!!V[id]:t=='sel'?String(V[id]):+V[id]);if(k=='banc'&&q.dL>200)throw new Error('Rondin de 200 mm de diamètre au maximum.');if(k=='banc'&&(q.L<500||q.h<250))throw new Error('Banc trop petit.');if(k=='fauteuil'&&(q.hd<q.hs*1.6||q.larg<400||q.prof<300))throw new Error('Dimensions du fauteuil incohérentes (dossier plus haut que 1,6 fois l’assise).');if(k=='etabli'&&(q.L<1200||q.dP<60||q.dP>140))throw new Error('Établi : perches de 1,2 m minimum, Ø 60 à 140 mm.');return q};
function exBuild(k,V){const q=exQ(k,V);msg('Construction de « '+EXN[k]+' » avec ses assemblages…',20000);
 setTimeout(()=>{EXSTY=q.ten||'hache';const ox=solids().length?freeSpot()[0]+400:0,a=newAsm(EXN[k]);try{batch(()=>EXB[k]((x,y,z)=>[x+ox,y,z],a,q));select([],null);if(PREF.theme)applyTheme(PREF.theme,piecesOf(a.id));touch();libPlan(a,EXN[k]);tabClick('Créer');selAsm(a.id);fit();msg('« '+EXN[k]+' » créé : '+piecesOf(a.id).length+' pièces. Clic sur une pièce pour la modifier, double-clic pour l’assemblage.',6000);if(V&&V.mt)setTimeout(()=>montage(a.id),400);else if(PREF.anim!==false)setTimeout(()=>montage(a.id,{fast:true}),300)}catch(e){console.error(e);delAsm(a.id,true);msg('Construction impossible : '+e.message,8000)}},40);return true}
const ex=exWin;
/* ===== Montage : rejoue la construction comme on la ferait à la main, d'après l'arborescence =====
 * Pour chaque pièce : on la CRÉE (elle apparaît à sa place), puis, quand les pièces d'un assemblage existent, on les
 * SÉLECTIONNE et on applique l'outil (tenon, mi-bois, cheville…) : la découpe de CET assemblage apparaît alors, pas les autres.
 * Une opération répétée n'est montrée en détail (curseur, outil) que la première fois : les suivantes passent très vite.
 * Mode accéléré : toute la construction se rejoue en ≈ 5 s. */
let MT=null;
const mtSleep=ms=>new Promise(r=>setTimeout(r,ms));
const MT_TOOLS=[['tenon','Tenon','Opérations'],['mibois','Mi-bois','Opérations'],['cheville','Chevilles','Opérations'],['quart','Quart de bois','Opérations'],['fendre','Fendre en planches','Opérations'],['claies','Plateau, claies, filet','Créer'],['corde','PH (cordes)','Créer'],['traverse','Traverse','Créer']];
function mtTool(o){if(o.type=='ph')return o.p.kind=='filet'?'claies':'corde';if(/Claie|Rondin fendu|Planche/.test(o.name)&&o.par)return/Rondin fendu|Planche/.test(o.name)?'fendre':'claies';
 if(/cheville/i.test(o.name)||o.peg)return'cheville';return'traverse'}
const mtJointTool=op=>{const k=(op.rec&&op.rec.k)||'',l=op.lab||'';return k=='mibois'||/^Mi-bois/.test(l)?'mibois':/cheville/i.test(k+l)?'cheville':/quart/i.test(l)?'quart':'tenon'};
const mtEase=k=>1-Math.pow(1-k,3);
const mtKey=o=>(o.name||'').replace(/ \d+$/,'');
function mtOrder(aid){const ord=a=>[...kidsP(a).sort((x,y)=>x.id-y.id),...kidsA(a).sort((x,y)=>x.id-y.id).flatMap(x=>ord(x.id))];return ord(aid).filter(o=>!GL.includes(o.type)&&o.m)}
function mtTilt(o){if(!o.rot.some(v=>Math.abs(v)>.5))return 0;let ang=0;try{const u=axisOf(o).u;ang=Math.round(Math.acos(Math.min(1,Math.abs(u[2])))/D)}catch(e){}return ang}
function mtSteps(L){const S=[],G={},made=new Set(),done=new Set();
 L.forEach(o=>(o.ops||[]).forEach(p=>{if(p.jid){const g=G[p.jid]||(G[p.jid]={jid:p.jid,ps:new Set(),op:p});g.ps.add(o)}}));
 const grp=Object.values(G).filter(g=>g.ps.size>1),hasJ=new Set();grp.forEach(g=>g.ps.forEach(o=>hasJ.add(o)));
 for(let i=0;i<L.length;i++){const o=L[i],key=mtKey(o),objs=[o];
  if(/Claie|Rondin fendu|Planche|Cheville/.test(key)&&!hasJ.has(o))while(i+1<L.length&&L[i+1].par==o.par&&mtKey(L[i+1])==key&&!hasJ.has(L[i+1]))objs.push(L[++i]);
  objs.forEach(x=>made.add(x));
  const ang=mtTilt(o),dim=o.type=='trav'&&o.p?` (Ø ${Math.round(o.p.d)} × ${Math.round(o.p.L)} mm)`:'';
  S.push({kind:'create',objs,tool:mtTool(o),txt:'Créer '+(objs.length>1?objs.length+' × '+key:o.name+dim)+(ang>=85?', posé à l’horizontale':ang>=3?', incliné de '+ang+'°':'')});
  grp.forEach(g=>{if(!done.has(g)&&[...g.ps].every(x=>made.has(x))&&objs.some(x=>g.ps.has(x))){done.add(g);const ps=[...g.ps],tl=mtJointTool(g.op),lab=((MT_TOOLS.find(x=>x[0]==tl)||[])[1]||'Assemblage'),ops=[...new Set(ps.map(p=>(p.ops||[]).find(q=>q.jid==g.jid)).filter(Boolean).map(q=>U(q.lab||'')).filter(Boolean))];
   S.push({kind:'joint',g,objs:ps,tool:tl,txt:'Sélectionner '+ps.slice(0,3).map(p=>'« '+p.name+' »').join(' et ')+(ps.length>3?'…':'')+', puis l’outil « '+lab+' »'+(ops.length?' : '+ops.slice(0,2).join(' ; '):'')})}})}
 const seen=new Set();S.forEach(s=>{const k=s.kind+':'+s.tool;s.rep=seen.has(k);seen.add(k);if(s.rep)s.txt+=' (même opération, accélérée)'});
 return S}
function mtMesh(o,g){const m=new THREE.Mesh(toGeo(g),o.m.material),ed=sharpEdges(polysOf(g)),pa=new Float32Array(ed.length*6);ed.forEach((e,i)=>pa.set([...e.p,...e.q],i*6));const lg=new THREE.BufferGeometry();lg.setAttribute('position',new THREE.BufferAttribute(pa,3));m.add(new THREE.LineSegments(lg,edgeMat()));m.position.copy(o.m.position);m.rotation.order='ZYX';m.rotation.copy(o.m.rotation);m.visible=false;sc.add(m);return m}
/* états d'une pièce : 0 = brute, j = après son j-ième assemblage, dernier = pièce finie (o.m). Chaque état ne contient que les découpes déjà « faites ». */
function mtStage(r,o,j){if(r.st[j])return r.st[j];let g=o.g;
 if(!MT.fast){const all=new Set(r.js.map(s=>s.g.jid)),ok=new Set(r.js.slice(0,j).map(s=>s.g.jid));
  for(const op of o.ops||[]){if(op.jid&&all.has(op.jid)&&!ok.has(op.jid))continue;try{const x=subtract(g,cutter(op));if(G.toPolygons(x).length)g=x}catch(e){}}}
 return r.st[j]=mtMesh(o,g)}
function mtPrep(fast){const S=MT.steps,os=new Map();let t=0;
 S.forEach(s=>{if(s.kind=='create')s.objs.forEach(o=>os.set(o,{cs:s,js:[],st:[],q1:new THREE.Quaternion().setFromEuler(o.m.rotation),tilt:!fast&&o.rot.some(v=>Math.abs(v)>.5)}))});
 S.forEach(s=>{if(s.kind=='joint')s.objs.forEach(o=>{const r=os.get(o);if(r)r.js.push(s)})});
 os.forEach((r,o)=>{if(fast)r.js=r.js.slice(0,1);if(!o.g)r.js=[];r.n=r.js.length;r.st[r.n]=o.m});
 const n=S.length,slot=Math.max(10,Math.min(350,5000/Math.max(1,n)));
 S.forEach((s,i)=>{if(fast){s.t0=i*slot;s.dur=Math.max(220,Math.min(700,slot*4))}else{s.dur=s.kind=='joint'?(s.rep?260:700):s.objs.some(o=>os.get(o).tilt)?(s.rep?260:800):(s.rep?160:420);s.t0=t;t+=s.dur+30}});
 MT.q0=new THREE.Quaternion();MT.os=os;MT.end=S.length?S[n-1].t0+S[n-1].dur+10:0}
function mtApply(T){const P=new Map();
 MT.steps.forEach(s=>{if(s.kind!='joint')return;const k=(T-s.t0)/s.dur;if(k<0||k>1)return;const e=.35+.65*Math.sin(Math.PI*k);s.objs.forEach(o=>P.set(o,Math.max(P.get(o)||0,e)))});
 MT.os.forEach((r,o)=>{const cs=r.cs,k=(T-cs.t0)/cs.dur,vis=T>=cs.t0;let idx=0;r.js.forEach(s=>{if(T>=s.t0+s.dur*.5)idx++});
  const cur=vis?mtStage(r,o,idx):null,pa=r.tilt?.45:1,sc_=!vis?1:k<1?Math.max(.001,mtEase(Math.min(1,Math.max(0,k/pa)))):1,qk=r.tilt&&vis&&k<1?mtEase(Math.min(1,Math.max(0,(k-.5)/.5))):1;
  r.st.forEach(m=>{if(!m)return;m.visible=m===cur;m.scale.setScalar(sc_);if(qk<1)m.quaternion.copy(MT.q0).slerp(r.q1,qk);else m.quaternion.copy(r.q1)});
  const e=P.get(o)||0;o.m.material.emissive.setRGB(.1*e,.3*e,.9*e)});req()}
function mtRun(a,b){return new Promise(res=>{const g=MT.gen,t0=performance.now();const st=()=>{if(!MT||g!=MT.gen)return res(false);const T=a+(performance.now()-t0);mtApply(Math.min(T,b));if(T<b)requestAnimationFrame(st);else res(true)};st()})}
function montage(aid,opt){stopMontage(true);opt=opt||{};const L=mtOrder(aid||0);if(!L.length)return msg('Rien à montrer.');
 const fast=!!opt.fast;MT={aid,steps:mtSteps(L),i:-1,play:true,L,gen:0,fast,off:[]};mtPrep(fast);select([],null);fit();mtApply(-1);
 if(fast){const kill=e=>{if(e.type=='keydown'&&e.key!='Escape')return;stopMontage()};['keydown','pointerdown'].forEach(t=>{document.addEventListener(t,kill,true);MT.off.push(()=>document.removeEventListener(t,kill,true))});
  msg('Construction en accéléré… (clic ou Échap pour passer)',5200);const g=MT.gen;mtRun(0,MT.end).then(ok=>{if(ok&&MT&&MT.gen==g)stopMontage()});return}
 const bar_=document.createElement('div');bar_.id='mtb';bar_.innerHTML=`<button onclick="mtGo(MT.i-1)" title="Étape précédente">⏮</button><button id="mtp" onclick="mtToggle()" title="Lecture / pause">⏸</button><button onclick="mtGo(MT.i+1)" title="Étape suivante">⏭</button><span id="mtt"></span><button onclick="montage(MT.aid,{fast:true})" title="Revoir toute la construction en 5 secondes">⏩ 5 s</button><button onclick="stopMontage()" title="Fermer et tout afficher">✕</button>`;document.body.appendChild(bar_);
 const cur=document.createElement('div');cur.id='mtc';cur.innerHTML='<svg width="22" height="22" viewBox="0 0 24 24"><path d="M3 2l7 19 2.5-7.5L20 11z" fill="#fff" stroke="#111" stroke-width="1.5" stroke-linejoin="round"/></svg><i></i>';document.body.appendChild(cur);
 const b=R.domElement.getBoundingClientRect();cur.style.left=(b.left+b.width/2)+'px';cur.style.top=(b.top+b.height/2)+'px';
 mtGo(0)}
function mtToggle(){if(!MT||MT.fast)return;MT.play=!MT.play;$('#mtp').textContent=MT.play?'⏸':'▶';if(MT.play&&!MT.busy)mtGo(MT.i+1)}
async function mtCursorTo(x,y,click){const c=$('#mtc');if(!c)return;c.style.left=x+'px';c.style.top=y+'px';await mtSleep(300);if(click){c.classList.add('clk');await mtSleep(110);c.classList.remove('clk')}}
function mtScreen(objs){const v=new THREE.Vector3(),b=R.domElement.getBoundingClientRect(),[mn,mx]=bounds(objs);v.set((mn[0]+mx[0])/2,(mn[1]+mx[1])/2,(mn[2]+mx[2])/2).project(cam);return[b.left+(v.x+1)/2*b.width,b.top+(1-v.y)/2*b.height]}
async function mtGo(i){if(!MT||MT.fast)return;const S=MT.steps;if(i<0)i=0;if(i>=S.length){MT.play=false;const p=$('#mtp');if(p)p.textContent='▶';$('#mtt').textContent='Montage terminé : '+S.length+' étapes.';mtApply(MT.end);return}
 const gen=++MT.gen;MT.i=i;MT.busy=true;const s=S[i];mtApply(s.t0-1);
 $('#mtt').textContent=`Étape ${i+1}/${S.length} : ${s.txt}`;
 const tool=async()=>{const [,lab,tab]=MT_TOOLS.find(t=>t[0]==s.tool)||MT_TOOLS[MT_TOOLS.length-1];if(curTab!=tab&&MODEL_TABS.includes(viewTab))tabClick(tab);await mtSleep(60);if((!MT||gen!=MT.gen))return false;
  const btn=[...document.querySelectorAll('#rp .rbt')].find(e=>(e.getAttribute('title')||'').startsWith(lab));if(btn){const r=btn.getBoundingClientRect();await mtCursorTo(r.left+r.width/2,r.top+r.height/2,true)}return !!MT&&gen==MT.gen};
 if(!s.rep){/* première fois : on montre le geste complet */
  if(s.kind=='create'){if(!await tool())return;const[sx,sy]=mtScreen(s.objs);await mtCursorTo(sx,sy,true)}
  else{for(const o of s.objs.slice(0,3)){const[sx,sy]=mtScreen([o]);await mtCursorTo(sx,sy,true);if((!MT||gen!=MT.gen))return;o.m.material.emissive.set(0x10285a);req()}if(!await tool())return}}
 if(!s.rep){const w=mtWin(s);await mtSleep(800);w.remove();if((!MT||gen!=MT.gen))return}
 if(s.kind=='joint'){s.objs.forEach(o=>{const r=MT.os.get(o),j=r.js.indexOf(s)+1;if(j<r.n)mtStage(r,o,j)})}/* prépare la découpe avant de l'animer */
 if((!MT||gen!=MT.gen))return;await mtRun(s.t0,s.t0+s.dur);if((!MT||gen!=MT.gen))return;MT.busy=false;await mtSleep(s.rep?60:250);if((!MT||gen!=MT.gen))return;if(MT.play)mtGo(i+1)}
function stopMontage(quiet){if(!MT){$('#mtb')&&$('#mtb').remove();$('#mtc')&&$('#mtc').remove();return}MT.gen++;MT.off.forEach(f=>f());
 MT.os.forEach((r,o)=>{r.st.forEach(m=>{if(m&&m!==o.m){sc.remove(m);m.geometry.dispose();m.children.forEach(c=>c.geometry&&c.geometry.dispose())}});if(o.m){o.m.visible=true;o.m.scale.setScalar(1);o.m.position.set(...o.pos);o.m.rotation.order='ZYX';o.m.rotation.set(...o.rot.map(d=>d*D))}});
 MT=null;$('#mtb')&&$('#mtb').remove();$('#mtc')&&$('#mtc').remove();$('#mtw')&&$('#mtw').remove();emi();req()}

/* =====================  Historique, sauvegarde, export, ouverture  ===================== */
let H=[],Hi=-1,hT=null,pending=false,gN=1,asWarn=0;const gId=new WeakMap(),gk=g=>{if(!g)return 0;if(!gId.has(g))gId.set(g,gN++);return gId.get(g)};
function bakeGL(){objs.forEach(o=>{if(!GL.includes(o.type))return;if(!o.pos.some(v=>Math.abs(v)>1e-6)&&!o.rot.some(v=>Math.abs(v)>1e-6))return;
 const M=new THREE.Matrix4().compose(new THREE.Vector3(...o.pos),new THREE.Quaternion().setFromEuler(new THREE.Euler(o.rot[0]*D,o.rot[1]*D,o.rot[2]*D,'ZYX')),new THREE.Vector3(1,1,1)),T=q=>new THREE.Vector3(...q).applyMatrix4(M).toArray();
 if(o.type=='ph')o.p.segs=o.p.segs.map(s=>[T(s[0]),T(s[1])]);else if(o.p.paths)o.p.paths.forEach(P=>P.pts=P.pts.map(T));else return;
 o.pos=[0,0,0];o.rot=[0,0,0];o._gk=null;mk(o)})}
function touch(){bakeGL();ver++;req();pending=true;clearTimeout(hT);hT=setTimeout(commit,350)}
const snapS=()=>({objs:objs.map(o=>({id:o.id,type:o.type,p:JSON.parse(JSON.stringify(o.p)),pos:[...o.pos],rot:[...o.rot],color:o.color,name:o.name,par:o.par,mat:o.mat,ops:JSON.parse(JSON.stringify(o.ops||[])),g:o.g,revAx:o.revAx,peg:o.peg,lk:o.lk&&[...o.lk],lc:o.lc&&[...o.lc],dsg:o.dsg,skSrc:o.skSrc})),asms:JSON.parse(JSON.stringify(asms)),nid,aid});
function commit(){clearTimeout(hT);pending=false;const s=snapS(),k=JSON.stringify(s,(kk,v)=>kk=='g'?gk(v):v);
 if(!(H[Hi]&&H[Hi].k==k)){H=H.slice(0,Hi+1);H.push({s,k});if(H.length>60)H.shift();Hi=H.length-1}
 autosave();buildRibbon();const e=$('#sum');if(e&&!document.body.classList.contains('dm'))e.outerHTML=sumHTML()}
function restore(s){objs.forEach(o=>{sc.remove(o.m);o.m.geometry.dispose()});objs=s.objs.map(o=>({...o,p:JSON.parse(JSON.stringify(o.p)),pos:[...o.pos],rot:[...o.rot],ops:JSON.parse(JSON.stringify(o.ops)),lk:o.lk&&[...o.lk]}));asms=JSON.parse(JSON.stringify(s.asms));nid=s.nid;aid=s.aid;objs.forEach(mk);sel=[];selA=null;gzCenter();emi();ver++;ui();req()}
function undo(){if(document.body.classList.contains('sk'))return;if(pending)commit();if(Hi<=0)return msg('Rien à annuler.');Hi--;restore(H[Hi].s);msg('Annulé')}
function redo(){if(document.body.classList.contains('sk'))return;if(pending)commit();if(Hi>=H.length-1)return msg('Rien à rétablir.');Hi++;restore(H[Hi].s);msg('Rétabli')}
/* ----- sérialisation ----- */
const KEY='cathia.projet.v2';
function serial(){return{app:'cathia',v:2,date:new Date().toISOString(),objs:objs.map(o=>{const r={id:o.id,type:o.type,p:o.p,pos:o.pos.map(v=>+v.toFixed(3)),rot:o.rot.map(v=>+v.toFixed(4)),color:o.color,name:o.name,par:o.par,mat:o.mat||'',ops:o.ops||[]};if(o.type=='mesh')r.poly=polysOf(o.g);if(o.revAx)r.revAx=o.revAx;if(o.peg)r.peg=1;if(o.lk)r.lk=o.lk;if(o.dsg)r.dsg=o.dsg;if(o.skSrc)r.sk=o.skSrc;return r}),asms,nid,aid,JID,meta,
 pages:(()=>{savePage();return pages.map(p=>({name:p.name,bg:p.bg||undefined,made:p.made||undefined,views:p.views.map(w=>({id:w.id,k:w.k,x:w.x,y:w.y,s:w.s,nm:w.nm,only:w.only||null,dv:w.dv||null})),dims:p.dims,texts:p.texts,shots:p.shots,nom:p.nom}))})(),curPage,vid,did,tid,sid,sk:{P:sk.P,sh:sk.sh,cons:sk.cons,len:sk.len,ang:sk.ang,step:sk.step},skid}}
function autosave(){try{localStorage.setItem(KEY,JSON.stringify(serial()))}catch(e){if(!asWarn++&&e&&e.name!=='SecurityError')msg('Sauvegarde automatique impossible (projet trop gros) : utilisez Fichier › Enregistrer.')}}
function load(d){if(!d||!Array.isArray(d.objs))throw new Error('ce n’est pas un projet CathIA');
 objs.forEach(o=>{sc.remove(o.m);o.m.geometry.dispose()});objs=[];sel=[];selA=null;const old=nid;
 for(const r of d.objs){if(!r||!SPEC[r.type])continue;const o={id:+r.id||nid++,type:r.type,p:{...SPEC[r.type].d,...r.p},pos:[0,1,2].map(i=>+(r.pos||[])[i]||0),rot:[0,1,2].map(i=>+(r.rot||[])[i]||0),color:r.color||'#c8a06a',name:String(r.name||SPEC[r.type].n),par:+r.par||0,mat:r.mat||'',ops:Array.isArray(r.ops)?r.ops:[]};
  if(r.revAx)o.revAx=r.revAx;if(r.peg)o.peg=true;if(r.lc)o.lc=r.lc;if(r.lk)o.lk=r.lk;if(r.dsg)o.dsg=r.dsg;if(r.sk)o.skSrc=r.sk;if(GL.includes(r.type)){}else{try{o.g=r.type=='mesh'?G.create((r.poly||[]).map(vs=>J.geometries.poly3.create(vs))):build(o)}catch(e){continue}if(!G.toPolygons(o.g).length)continue}objs.push(o);try{mk(o)}catch(e){objs.pop()}}
 asms=d.asms&&typeof d.asms=='object'?d.asms:{};nid=Math.max(+d.nid||1,...objs.map(o=>o.id+1));aid=Math.max(+d.aid||1,...Object.values(asms).map(a=>a.id+1));JID=Math.max(+d.JID||0,...objs.flatMap(o=>(o.ops||[]).map(p=>p.jid||0)));
 Object.assign(meta,{fiche:{},titre:'Mon installation',soc:'',des:'',mat:'',ref:'PL-001',ind:'A',feu:'1/1',ech:''},d.meta||{});
 if(Array.isArray(d.pages)&&d.pages.length){pages=d.pages.map(p=>({name:p.name||'Page',bg:p.bg,made:p.made??!!((p.views||[]).length||(p.texts||[]).length||(p.shots||[]).length),views:p.views||[],dims:p.dims||[],texts:p.texts||[],shots:p.shots||[],nom:Object.assign(newNom(),p.nom||{})}));curPage=Math.min(d.curPage||0,pages.length-1)}
 else{pages=[{name:'Page 1',views:Array.isArray(d.views)?d.views:[],dims:Array.isArray(d.dims)?d.dims:[],texts:Array.isArray(d.texts)?d.texts:[],shots:Array.isArray(d.shots)?d.shots:[],nom:Object.assign(newNom(),d.nom||{})}];curPage=0}
 pages.forEach(p=>p.views.forEach(w=>{if(w.dv)DIRS[w.k]=['Vue utilisateur',w.dv]}));setPageVars(pages[curPage]);const allv=pages.flatMap(p=>p.views),alld=pages.flatMap(p=>p.dims),allt=pages.flatMap(p=>p.texts),alls=pages.flatMap(p=>p.shots);
 vid=Math.max(+d.vid||1,...allv.map(w=>w.id+1));did=Math.max(+d.did||1,...alld.map(x=>x.id+1));tid=Math.max(+d.tid||1,...allt.map(x=>x.id+1));sid=Math.max(+d.sid||1,...alls.map(x=>x.id+1));selV=selD=selT=selS=null;selN=false;pend=null;
 const S=d.sk||{};Object.assign(sk,{P:S.P||{},sh:S.sh||[],cons:S.cons||[],sel:[],ss:null,cur:null,len:S.len||100,ang:S.ang||360,step:S.step||5});skid=+d.skid||1;ver++}
function afterLoad(){H=[];Hi=-1;commit();closeMd();if(viewTab=='Accueil'){viewTab=curTab='Opérations'}setMode(viewTab);gzCenter();if(objs.length)fit();ui();buildRibbon()}
const slug=t=>String(t).normalize('NFD').replace(/[\u0300-\u036f]/g,'').replace(/[^\w-]+/g,'-').replace(/^-|-$/g,'').toLowerCase()||'projet';
/* ----- enregistrement (navigateur, artifact Claude, Google Apps Script) ----- */
/* version en ligne : soit dans Google Apps Script, soit sur un site statique (GitHub Pages) qui appelle l'API Apps Script */
const CFG={api:'https://script.google.com/macros/s/AKfycbwsDESwtXlHJOU-sHXazFq6hwufGkglXVrggKR4xSUtpsutsUnfnBuKo1ufd2Y5hLTXkA/exec'},inGas=()=>!!(window.google&&google.script&&google.script.run),gasOK=()=>inGas()||(!!CFG.api&&/^https?:/.test(location.protocol));
async function save(filename,data,mime){let d=null;try{d=window.claude&&await claude.use('downloads')}catch(e){}
 if(d){try{await d.save({filename,data});return true}catch(e){if(e.code=='declined')return false;msg('Échec de l’enregistrement : '+(e.message||e.code));return false}}
 const blob=data instanceof Blob?data:new Blob([data],{type:mime||'application/octet-stream'});
 const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=filename;document.body.appendChild(a);a.click();setTimeout(()=>{a.remove();URL.revokeObjectURL(a.href)},2000);return true}
function saveJSON(){save(slug(meta.titre)+'.cathia.json',JSON.stringify(serial()),'application/json').then(ok=>ok&&msg('Projet enregistré'))}
function saveProj(){if(gasOK())return saveCloud();return saveProjFile()}
function saveProjFile(){if(!objs.length)return msg('Rien à enregistrer pour l’instant.');save(slug(meta.titre)+'.cathia.html',viewerHTML(),'text/html').then(ok=>ok&&msg('Projet enregistré (HTML : visionneuse 3D + projet réouvrable avec « Ouvrir »)',5000))}
function openProj(){$('#fo').click()}
$('#fo').onchange=e=>{const f=e.target.files[0];e.target.value='';if(!f)return;f.text().then(t=>openText(t,f.name))};
function openText(t,name,origin){try{if(/^\s*(<\?xml[^>]*>\s*)?(<!doctype[^>]*>\s*)?(<!--[\s\S]*?-->\s*)?<svg\b/i.test(t))return importSvg(t,name);let d;if(/^\s*</.test(t)){const m=/<script type="application\/json" id="cathia-projet">([\s\S]*?)<\/script>/.exec(t);if(!m)return openForeign(t,name);try{d=JSON.parse(m[1])}catch(e){return openForeign(t,name)}if(!d||d.app!='cathia'||!Array.isArray(d.objs))return openForeign(t,name);const mm=/<script type="application\/json" id="cathia-meta">([\s\S]*?)<\/script>/.exec(t);if(mm&&!origin){try{const x=JSON.parse(mm[1]);if(x.id&&String(x.id).indexOf('@@')<0)origin={id:x.id,name}}catch(e){}}}else d=JSON.parse(t);closeForeign();load(d);afterLoad();cloudOrigin(origin,name);msg('Projet ouvert : '+name)}catch(err){msg('Fichier invalide : '+err.message,6000)}}
function newProj(){modal(`<h3>Nouveau projet</h3><p>Effacer le projet en cours ?<br><span class="mu">Pensez à l’enregistrer avant si vous voulez le garder.</span></p><div class="r"><button class="p" onclick="closeMd();saveProj()">Enregistrer d’abord</button><button class="dg" onclick="load({objs:[]});afterLoad();tabClick('Créer')">Effacer</button><button onclick="closeMd()">Annuler</button></div>`)}
/* ----- visionneuse HTML (boutons de vues en haut) ----- */
const VIEWER_JS=`(function(){var D=JSON.parse(document.getElementById('cathia-geo').textContent),$=function(s){return document.querySelector(s)};
var R=new THREE.WebGLRenderer({antialias:true,preserveDrawingBuffer:true}),host=$('#v');host.appendChild(R.domElement);var sc=new THREE.Scene();sc.background=new THREE.Color(0xf4f5f7);
var cP=new THREE.PerspectiveCamera(45,1,1,400000),cO=new THREE.OrthographicCamera(-1,1,1,-1,1,1e6),cam=cP;cP.up.set(0,0,1);cO.up.set(0,0,1);var oc=new THREE.OrbitControls(cam,R.domElement);
sc.add(new THREE.AmbientLight(0xffffff,.65));var dl=new THREE.DirectionalLight(0xffffff,.8);dl.position.set(500,-800,1000);sc.add(dl);
var meshes=[],box=new THREE.Box3(),ghost=false;
function geom(v,ix){var n=ix.length,pos=new Float32Array(n*3),nor=new Float32Array(n*3),fn=[],map={},i,t;
 for(i=0;i<n;i+=3){var a=ix[i]*3,b=ix[i+1]*3,c=ix[i+2]*3,e1=[v[b]-v[a],v[b+1]-v[a+1],v[b+2]-v[a+2]],e2=[v[c]-v[a],v[c+1]-v[a+1],v[c+2]-v[a+2]],x=e1[1]*e2[2]-e1[2]*e2[1],y=e1[2]*e2[0]-e1[0]*e2[2],z=e1[0]*e2[1]-e1[1]*e2[0],l=Math.sqrt(x*x+y*y+z*z)||1;fn.push([x/l,y/l,z/l]);
  [a,b,c].forEach(function(p,j){var k=Math.round(v[p]*50)+','+Math.round(v[p+1]*50)+','+Math.round(v[p+2]*50);(map[k]=map[k]||[]).push(i/3);pos[(i+j)*3]=v[p];pos[(i+j)*3+1]=v[p+1];pos[(i+j)*3+2]=v[p+2]})}
 for(i=0;i<n;i++){var f=fn[(i/3)|0],s=[0,0,0],k=Math.round(pos[i*3]*50)+','+Math.round(pos[i*3+1]*50)+','+Math.round(pos[i*3+2]*50);map[k].forEach(function(q){var g=fn[q];if(f[0]*g[0]+f[1]*g[1]+f[2]*g[2]>.78){s[0]+=g[0];s[1]+=g[1];s[2]+=g[2]}});var l=Math.sqrt(s[0]*s[0]+s[1]*s[1]+s[2]*s[2])||1;nor[i*3]=s[0]/l;nor[i*3+1]=s[1]/l;nor[i*3+2]=s[2]/l}
 var g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.BufferAttribute(pos,3));g.setAttribute('normal',new THREE.BufferAttribute(nor,3));return g}
D.pieces.forEach(function(p,i){var g=geom(p.v,p.i),m=new THREE.Mesh(g,new THREE.MeshStandardMaterial({color:p.c,roughness:.75,metalness:.05,side:THREE.DoubleSide}));if(p.e&&p.e.length){var lg=new THREE.BufferGeometry();lg.setAttribute('position',new THREE.BufferAttribute(new Float32Array(p.e),3));m.add(new THREE.LineSegments(lg,new THREE.LineBasicMaterial({color:0x222222})))}sc.add(m);meshes.push(m);box.expandByObject(m);
 var path=p.n.split(' › '),nm=path.pop(),host=$('#lp'),ids='';path.forEach(function(seg,d){ids+='›'+seg;var g=document.getElementById('g'+ids);if(!g){g=document.createElement('div');g.id='g'+ids;g.className='grp';g.style.marginLeft=(d?12:0)+'px';var h=document.createElement('div');h.className='gh';h.textContent='▾ '+seg;h.onclick=function(){var c=g.querySelector('.gc');c.hidden=!c.hidden;h.textContent=(c.hidden?'▸ ':'▾ ')+seg};var c=document.createElement('div');c.className='gc';g.appendChild(h);g.appendChild(c);host.appendChild(g)}host=g.querySelector('.gc')});
 var li=document.createElement('div');li.className='it';li.style.marginLeft=(path.length?12:0)+'px';li.textContent=nm;li.onclick=function(){meshes.forEach(function(x,j){x.material.emissive.set(j==i?0x23407f:0)});[].forEach.call(document.querySelectorAll('.it'),function(e){e.classList.remove('on')});li.classList.add('on')};host.appendChild(li)});
var C=box.getCenter(new THREE.Vector3()),S=box.getSize(new THREE.Vector3()),Rr=Math.max(S.x,S.y,S.z,300);
var V={iso:[.6,-.85,.6],front:[0,-1,0],back:[0,1,0],right:[1,0,0],left:[-1,0,0],top:[0,0,1],bottom:[0,0,-1]};
function size(){var w=host.clientWidth,h=host.clientHeight;R.setPixelRatio(Math.min(devicePixelRatio||1,2));R.setSize(w,h);cP.aspect=w/h;cP.updateProjectionMatrix();cO.left=-cO.top*w/h;cO.right=cO.top*w/h;cO.updateProjectionMatrix()}
function view(n){var d=V[n],l=Math.hypot(d[0],d[1],d[2]),v=d.map(function(x){return x/l});if(!v[0]&&!v[1])v[1]=-.001;oc.target.copy(C);var r=Rr*1.8;cam.position.set(C.x+v[0]*r,C.y+v[1]*r,C.z+v[2]*r);if(cam===cO){var a=host.clientWidth/host.clientHeight;cO.zoom=1;cO.top=r*.414;cO.bottom=-r*.414;cO.left=-cO.top*a;cO.right=cO.top*a;cO.updateProjectionMatrix()}oc.update()}
window.vw=view;window.proj=function(){var t=oc.target.clone(),d=cam.position.clone().sub(t).normalize(),dist=cam.position.distanceTo(t);if(cam===cP){var a=host.clientWidth/host.clientHeight;cO.zoom=1;cO.top=dist*Math.tan(cP.fov*Math.PI/360);cO.bottom=-cO.top;cO.left=-cO.top*a;cO.right=cO.top*a;cO.position.copy(cam.position);cO.updateProjectionMatrix();cam=cO}else{var hh=(cO.top-cO.bottom)/2/cO.zoom;cP.position.copy(t).addScaledVector(d,hh/Math.tan(cP.fov*Math.PI/360));cam=cP}oc.object=cam;oc.update();$('#bp').textContent=cam===cO?'Orthogonale':'Perspective'};
window.gh=function(){ghost=!ghost;meshes.forEach(function(m){m.material.transparent=ghost;m.material.opacity=ghost?.35:1;m.material.depthWrite=!ghost;m.material.needsUpdate=true})};
addEventListener('resize',size);size();view('iso');(function an(){requestAnimationFrame(an);R.render(sc,cam)})();})();`;
const OCJS=String.raw`(function(){try{var m=JSON.parse(document.getElementById("cathia-meta").textContent),a=document.getElementById("oc");if(m.id&&String(m.id).indexOf("@@")<0&&m.app&&String(m.app).indexOf("@@")<0){a.href=m.app+(m.app.indexOf("?")<0?"?":"&")+"p="+encodeURIComponent(m.id);a.hidden=false}}catch(e){}})();`;
function viewerHTML(ph){const P=[];objs.forEach(o=>{if(!o.m)return;o.m.updateMatrixWorld(true);const g=o.m.geometry,pos=g.attributes.position,M=o.m.matrixWorld,idx=new Map(),V=[],I=[],v3=new THREE.Vector3();
  for(let i=0;i<pos.count;i++){v3.fromBufferAttribute(pos,i).applyMatrix4(M);const k=Math.round(v3.x*10)+','+Math.round(v3.y*10)+','+Math.round(v3.z*10);let j=idx.get(k);if(j==null){j=V.length/3;idx.set(k,j);V.push(+v3.x.toFixed(1),+v3.y.toFixed(1),+v3.z.toFixed(1))}I.push(j)}
  const E=[],ls=o.m.children.find(c=>c.isLineSegments);if(ls){const lp=ls.geometry.attributes.position;for(let i=0;i<lp.count;i++){v3.fromBufferAttribute(lp,i).applyMatrix4(M);E.push(+v3.x.toFixed(1),+v3.y.toFixed(1),+v3.z.toFixed(1))}}
  P.push({n:(o.par&&asms[o.par]?asmPath(o).join(' › ')+' › ':'')+o.name,c:o.color,v:V,i:I,e:E,l:o.type=='lash'?1:o.type=='ph'?2:0})});
 const b=bomData(),bom=b.G.map(g=>`<tr><td class="n">${g.n} ×</td><td>${esc(desOf(g.o))} ${esc(descOf(g.o))}${opsOf(g.o)?`<br><small>${esc(opsOf(g.o))}</small>`:''}</td></tr>`).join('');
 const J1=s=>JSON.stringify(s).replace(/</g,'\\u003c'),T='<'+'/script>';
 return`<!doctype html><html lang="fr"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>${esc(meta.titre)} – CathIA</title><style>
:root{--bg:#f1f2f4;--pn:#fff;--tx:#1d2330;--mu:#6b7280;--bd:#d5d8de;--ac:#2f6fdb}@media(prefers-color-scheme:dark){:root{--bg:#1b1e24;--pn:#262a33;--tx:#e6e8ec;--mu:#9aa1ad;--bd:#3a3f4b;--ac:#5b9bff}}
html,body{height:100%;margin:0}body{background:var(--bg);color:var(--tx);font:14px system-ui,sans-serif;display:flex;flex-direction:column}
#top{display:flex;gap:6px;align-items:center;flex-wrap:wrap;padding:8px 12px;background:var(--pn);border-bottom:1px solid var(--bd)}#top b{margin-right:8px}
button{background:var(--pn);color:var(--tx);border:1px solid var(--bd);border-radius:6px;padding:6px 10px;cursor:pointer}button:hover{border-color:var(--ac)}
#main{flex:1;display:grid;grid-template-columns:1fr;min-height:0}#main.open{grid-template-columns:1fr 330px}#side{display:none}#main.open #side{display:block}.gh{font-weight:600;padding:3px 4px;cursor:pointer}.grp{margin:2px 0}#v{min-height:300px;min-width:0}#v canvas{display:block}
#side{overflow:auto;padding:12px;background:var(--pn);border-left:1px solid var(--bd)}h4{margin:14px 0 6px;font-size:12px;text-transform:uppercase;letter-spacing:.05em;color:var(--mu)}h4:first-child{margin-top:0}
.it{padding:4px 6px;border-radius:6px;cursor:pointer}.it.on{background:color-mix(in srgb,var(--ac) 18%,transparent)}table{border-collapse:collapse;width:100%}td{border-bottom:1px solid var(--bd);padding:4px 6px;vertical-align:top}td.n{text-align:right;font-weight:600;white-space:nowrap}small{color:var(--mu)}
@media(max-width:760px){#main{grid-template-columns:1fr;grid-template-rows:60vh auto}#side{border-left:0;border-top:1px solid var(--bd)}}</style></head><body>
<div id="top"><b>${esc(meta.titre)}</b><button onclick="vw('iso')">Iso</button><button onclick="vw('front')">Face</button><button onclick="vw('back')">Arrière</button><button onclick="vw('right')">Droite</button><button onclick="vw('left')">Gauche</button><button onclick="vw('top')">Dessus</button><button onclick="vw('bottom')">Dessous</button><button id="bp" onclick="proj()">Perspective</button><button onclick="gh()">Transparence</button><button id="bt" onclick="document.getElementById('main').classList.toggle('open');dispatchEvent(new Event('resize'))">☰ Arborescence et matériel</button><a id="oc" hidden target="_blank" rel="noopener" style="margin-left:auto;background:var(--ac);color:#fff;border-radius:6px;padding:6px 12px;text-decoration:none;font-weight:600">Ouvrir avec CathIA</a></div>
<div id="main"><div id="v"></div><div id="side"><h4>Matériel</h4><table>${bom}</table><h4>Arborescence (cliquer une pièce pour la repérer)</h4><div id="lp"></div><p><small>Généré par CathIA. Vue en lecture seule : pour modifier, ouvrez ce fichier dans CathIA avec « Ouvrir ».</small></p></div></div>
<script type="application/json" id="cathia-projet">${J1(serial())}${T}<script type="application/json" id="cathia-geo">${J1({pieces:P})}${T}
<script type="application/json" id="cathia-meta">${J1({v:1,nom:meta.titre,id:ph?'@@CATHIA_ID@@':CLOUD.id||'',email:ph?'@@CATHIA_EMAIL@@':AUTH.email||'',app:ph?'@@CATHIA_APP@@':CLOUD.app||'',fiche:meta.fiche||{},date:new Date().toISOString()})}${T}
<script src="https://cdn.jsdelivr.net/npm/three@0.128.0/build/three.min.js">${T}<script src="https://cdn.jsdelivr.net/npm/three@0.128.0/examples/js/controls/OrbitControls.js">${T}<script>${VIEWER_JS}${T}<script>${OCJS}${T}</body></html>`}
/* ----- accueil ----- */
function welcome(){tabClick('Accueil')}
/* ----- clavier ----- */
addEventListener('keydown',e=>{if(e.key=='Escape'){if($('#md').classList.contains('on'))return closeMd();hideCm();if(pickMode){pickMode=null;R.domElement.style.cursor='';setHint();emi();gzCenter()}return}
 const k=e.key.toLowerCase(),ctrl=e.ctrlKey||e.metaKey;if(ctrl&&k=='s'){e.preventDefault();return saveProj()}
 if(ctrl&&k=='g'&&modelMode()&&!/INPUT|TEXTAREA|SELECT/.test(e.target.tagName)){e.preventDefault();return e.shiftKey?ungroup():groupSel()}
 if(/INPUT|SELECT|TEXTAREA/.test(document.activeElement.tagName))return;const M=document.body.classList,model=!M.contains('sk')&&!M.contains('dm');
 if(model){if(ctrl&&k=='z'&&!e.shiftKey){e.preventDefault();return undo()}if(ctrl&&(k=='y'||(k=='z'&&e.shiftKey))){e.preventDefault();return redo()}if(ctrl&&k=='d'){e.preventDefault();return dup()}if(ctrl&&k=='a'){e.preventDefault();return selAll()}
  if(e.key=='Delete'||e.key=='Backspace')return delSel();if(e.key=='F2'&&sel1()){e.preventDefault();dRename(sel1())}}
 else if(M.contains('dm')&&e.key=='Delete')delDraw()});


/* =====================  Assistant IA (artifact Claude uniquement)  ===================== */
const KB=`SYNTHÈSE FROISSARTAGE (Michel Froissart, "Froissartage", et livret de techniques scouts)
Principe : construire du mobilier et des installations de camp sans clou, vis ni ficelle, avec des perches de bois vert (gaules) assemblées par tenon-mortaise ou mi-bois. Couper avec l'accord du propriétaire/ONF, souche ≤ 20 cm, bois de feu ramassé au sol. Laisser le site propre.
Outils : hachette canadienne (500-600 g), scie à bûches pour bois vert (pas d'égoïne), plane (couper dans le sens du fil), tarière avec manche (mèches 16, 22, 30 mm ; 10 à 40 mm au total ; 7 mm pour chevilles), ciseau et bédane de 20 mm, râpe, maillet (bois sur bois, fer sur fer), mètre, crayon, équerre, compas, pierre à aiguiser. Sécurité : main libre toujours derrière l'outil, outils très affûtés, gants.
Règles : règle du tiers (trou ou mortaise ≤ 1/3 du diamètre de la pièce percée ; la pièce doit faire au moins 3 fois le diamètre du trou). Entre deux trous laisser au moins le rayon de la mèche (jamais tangents). Deux trous perpendiculaires proches affaiblissent la pièce : les décaler. Pas de nœud à l'endroit d'un tenon. Éviter le trièdre (3 trous au même point). Un triangle est indéformable : écharpes, étais ; un mât s'étaye dans au moins 3 directions ; l'échelle (montants parallèles + barreaux) est la structure de base ; les grandes surfaces (siège, plateau) sont des échelles clayonnées.
Tenons : tenon rond à la plane (cylindrique si chevillé, légèrement conique s'il tient par enfoncement) ; embase soit conique (taillée à la hache/plane), soit sciée (épaulement net : plus rapide mais zone de faiblesse, à éviter si l'effort porte sur l'embase). Tenon plat : épaisseur = diamètre de la mèche, largeur = mortaise de 2-3 trous joints au ciseau ; il travaille de champ, plus solide en flexion. Mors d'âne : tenon plat dissymétrique (hêtre, sapin cassants). Dans le bois vert : mortaise et tenon débouchants, coin en bois dur dans une fente perpendiculaire aux fibres de la pièce mortaisée ; ne fixer qu'après séchage. Cheville de bois dur seulement si le bois est sec. Faux tenon : trou en bout + cheville si le tenon casse.
Mi-bois : deux pièces qui se croisent, entaillées à moitié (ou moins : entaille moins profonde = pièces plus fortes). Équarrir légèrement pour travailler sur un plat. Scie + ciseau. Souvent un boulon ou clou rivé. Calvaire : scier le fût au tiers de son diamètre.
Queues d'aronde (CathIA) : trapézoïdale (le tenon garde toute son épaisseur, seulement 2 traits de scie inclinés au bout ; rainure traversante peu profonde dans l'autre pièce, environ un tiers du diamètre) et à mi-bois (languette de demi-épaisseur, côtés inclinés). La rainure ne doit jamais couper entièrement la pièce. Chevilles : trou chevillé traversant plusieurs pièces. Quart de bois : on retire un quartier de la traverse sur une longueur pour poser un plateau.
Clayonnage : claies jointives (entraxe = somme des rayons, donc le diamètre), diamètre de 8 à 20 mm, tressées sous et sur les supports, une claie sur deux inversée, alterner pied et tête de gaule ; rayon de courbure minimal estimé à 20-25 fois le diamètre (estimation, pas une règle du livre).
Autres : enfourchement (mortaise ouverte d'un côté), queue d'aronde (2 traits de scie inclinés en sens inverses, la languette trapézoïdale sautée au ciseau, tenon trapèze à la plane : résiste à la traction, ex. pieds de table qui s'écartent), encoches en sifflet pour pièces comprimées, mi-bois à surlure pour rabouter.
Percement : vérifier le parallélisme avec un bout de bois témoin ; trou perpendiculaire : témoin ; oblique à 45° : triangle rectangle isocèle ; contreventement : trous obliques (amorcer par une entaille) ; tous les assemblages se montent en même temps. Tracer les longues lignes à la cinglée.
Pièces jointes : l'utilisateur peut joindre des images (photos de réalisations, croquis, plans) et des documents texte ; décris ce que tu vois puis propose la construction en froissartage et utilise les outils.\nUnité d'affichage de CathIA : le centimètre (réglable en millimètres dans Paramètres) ; les outils de l'assistant restent en millimètres. Chevilles : elles ne se posent que sur des pièces qui se touchent et se croisent (jamais dans le plan des pièces) ; elles dépassent de 2 mm de chaque côté. Brêlage : seulement sur des pièces en contact. Clous cavaliers : petits U métalliques qui fixent les claies sur leurs supports (comptés dans la liste du matériel). PH (paraboloïde hyperbolique) : cordes tendues entre deux bords gauches, purement décoratif ; on règle le début, la longueur et l'espacement. Table : plateau fini à 75 cm du sol ; la hauteur d'axe des traverses tient compte du diamètre des claies ; 4ᵉ traverse plus fine au milieu pour le tressage dessous/dessus/dessous.
Mobilier du livre : établi de camp (2 perches Ø8-10 cm de 2-2,5 m, 1 cm d'écart, boulon, pieds de 80 cm dans trous de 22-30 mm, pieds écartés de 60 cm) ; tabouret tripode (3 pieds symétriques dans un demi-rondin) ; banc rustique (rondin refendu 1,5-2 m, 4 pieds) ; échelle ; chevalet à bûches (2 X en mi-bois reliés par un barreau) ; fauteuil carré (pieds avant 0,60 m, arrière 0,90 m, Ø50-60 mm ; bâtons de chaise Ø20-30 ; support de siège Ø40-57 ; accoudoir à 0,57 m).`;
const AI_SYS=`Tu es l'assistant de CathIA, un logiciel de CAO pour le froissartage scout. Réponds en français, de façon courte et concrète. Tu peux consulter et modifier le modèle 3D avec les outils fournis, mais ne modifie le modèle que si l'utilisateur le demande. Unités : millimètres. Repère : X et Y horizontaux, Z vers le haut. Une traverse est un bois rond (diamètre, longueur) défini par ses deux extrémités. Les pieds se tenonnent à la hachette (tenon classique). Pour un tenon, la pièce 'a' porte le tenon et la pièce 'b' reçoit la mortaise : le bout de 'a' doit pénétrer dans 'b'. Pour un mi-bois, les deux pièces doivent se croiser et se recouvrir. Quand tu proposes une dimension, applique la règle du tiers.`;
function md(t){const E=s=>s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'),IN=s=>E(s).replace(/`([^`]+)`/g,'<code>$1</code>').replace(/\*\*([^*]+)\*\*/g,'<b>$1</b>').replace(/__([^_]+)__/g,'<b>$1</b>').replace(/(^|[^*\w])\*([^*\s][^*]*?)\*(?!\w)/g,'$1<i>$2</i>').replace(/~~([^~]+)~~/g,'<s>$1</s>');
 const L=String(t).replace(/\r/g,'').split('\n'),out=[];let i=0,ls=[],para=[];
 const fp=()=>{if(para.length){out.push('<p>'+para.map(IN).join('<br>')+'</p>');para=[]}},fl=()=>{while(ls.length)out.push('</'+ls.pop().t+'>')};
 while(i<L.length){const l=L[i];
  if(/^```/.test(l)){fp();fl();const c=[];i++;while(i<L.length&&!/^```/.test(L[i]))c.push(L[i++]);i++;out.push('<pre><code>'+E(c.join('\n'))+'</code></pre>');continue}
  if(/^\s*\|.*\|\s*$/.test(l)&&i+1<L.length&&/^\s*\|?[\s:|-]+\|[\s:|-]*$/.test(L[i+1])){fp();fl();const row=r=>r.trim().replace(/^\||\|$/g,'').split('|').map(x=>IN(x.trim()));const h=row(l);i+=2;const b=[];while(i<L.length&&/^\s*\|/.test(L[i]))b.push(row(L[i++]));out.push('<table><tr>'+h.map(x=>'<th>'+x+'</th>').join('')+'</tr>'+b.map(r=>'<tr>'+r.map(x=>'<td>'+x+'</td>').join('')+'</tr>').join('')+'</table>');continue}
  let m;
  if(m=/^(#{1,6})\s+(.*)$/.exec(l)){fp();fl();out.push('<h5>'+IN(m[2])+'</h5>');i++;continue}
  if(/^\s*([-*_])\1{2,}\s*$/.test(l)){fp();fl();out.push('<hr>');i++;continue}
  if(m=/^(\s*)([-*+]|\d+[.)])\s+(.*)$/.exec(l)){fp();const ind=m[1].length,t=/\d/.test(m[2])?'ol':'ul';while(ls.length&&ls[ls.length-1].ind>ind)out.push('</'+ls.pop().t+'>');
   if(ls.length&&ls[ls.length-1].ind==ind&&ls[ls.length-1].t!=t)out.push('</'+ls.pop().t+'>');if(!ls.length||ls[ls.length-1].ind<ind){out.push('<'+t+'>');ls.push({ind,t})}out.push('<li>'+IN(m[3])+'</li>');i++;continue}
  if(/^\s*$/.test(l)){fp();fl();i++;continue}
  if(ls.length&&/^\s+\S/.test(l)){out.push('<div style="margin-left:14px">'+IN(l.trim())+'</div>');i++;continue}
  fl();para.push(l);i++}
 fp();fl();return out.join('')}
let aiTurns=[],aiCtl=null,aiBusy=false;
const findP=k=>objs.find(o=>String(o.id)==String(k))||objs.find(o=>o.name==k)||objs.find(o=>o.name.toLowerCase()==String(k).toLowerCase());
function projSummary(){if(!objs.length)return'Le projet est vide.';return objs.slice(0,70).map(o=>`#${o.id} ${o.name} [${SPEC[o.type].n}] ${descOf(o,1)} pos=(${o.pos.map(Math.round)}) rot=(${o.rot.map(Math.round)})${asms[o.par]?' assemblage:'+asms[o.par].n:''}${o.ops&&o.ops.length?' ops:'+o.ops.map(p=>p.lab).join(' ; '):''}`).join('\n')+(objs.length>70?'\n… ('+objs.length+' pièces)':'')}
const AI_TOOLS=()=>[
 {name:'lister_pieces',description:'Liste les pièces du projet (id, nom, dimensions, position, assemblage, opérations) et les collisions. À appeler avant de modifier.',execute:()=>projSummary()+'\nCollisions : '+(collisions().slice(0,15).map(c=>c.a.name+'/'+c.b.name+' '+Math.round(c.pen)+' mm').join(' ; ')||'aucune')},
 {name:'ajouter_traverse',description:'Ajoute une traverse (bois rond droit) entre deux points, en mm. Retourne son id.',inputSchema:{type:'object',properties:{nom:{type:'string'},diametre:{type:'number'},x1:{type:'number'},y1:{type:'number'},z1:{type:'number'},x2:{type:'number'},y2:{type:'number'},z2:{type:'number'}},required:['diametre','x1','y1','z1','x2','y2','z2']},
  execute:i=>{const A=[+i.x1,+i.y1,+i.z1],B=[+i.x2,+i.y2,+i.z2];if(!(+i.diametre>=10)||len(sub(B,A))<30)throw new Error('Diamètre (≥10) ou longueur invalide');const o=bar(i.nom||'Traverse '+nid,A,B,+i.diametre,0);select([o]);return`Traverse créée : id ${o.id}, ${o.name}, Ø${o.p.d} × ${Math.round(o.p.L)} mm`}},
 {name:'ajouter_courbe',description:'Ajoute une pièce courbe (claie, gaule) en tube lissé passant par des points (mm). diametre_debut et diametre_fin permettent une gaule conique. Avertit si le rayon de courbure est trop faible.',inputSchema:{type:'object',properties:{nom:{type:'string'},points:{type:'array',items:{type:'array',items:{type:'number'}},description:'liste de [x,y,z], au moins 2'},diametre_debut:{type:'number'},diametre_fin:{type:'number'}},required:['points','diametre_debut']},
  execute:i=>{const P=(i.points||[]).map(p=>p.map(Number));if(P.length<2||P.some(p=>p.length!=3||p.some(isNaN)))throw new Error('Il faut au moins 2 points [x,y,z]');const d0=+i.diametre_debut,d1=+(i.diametre_fin||d0);if(d0<8||d0>20||d1<8||d1>20)throw new Error('Diamètre d’une claie : de 8 à 20 mm');const o=mkObj('courbe',{pts:P.map(p=>sub(p,P[0])),d0,d1,len:0},null,i.nom||'Claie '+nid,'#b5894f',P[0],[0,0,0],0);select([o]);return`Courbe créée : id ${o.id}, longueur ≈ ${Math.round(o.p.len)} mm`}},
 {name:'ajouter_serie',description:"Répète une pièce en série. type 'lineaire' (direction X, Y, Z ou axe, avec pas en mm) ou 'circulaire' (axe X, Y ou Z, angle total en degrés, centre cx,cy,cz optionnel). nombre = total d'exemplaires, original compris.",inputSchema:{type:'object',properties:{piece:{type:'string'},type:{type:'string'},nombre:{type:'number'},direction:{type:'string'},pas:{type:'number'},inverser:{type:'boolean'},axe:{type:'string'},angle:{type:'number'},cx:{type:'number'},cy:{type:'number'},cz:{type:'number'}},required:['piece','type','nombre']},
  execute:i=>{const o=findP(i.piece);if(!o)throw new Error('Pièce introuvable');const n=Math.round(+i.nombre);if(!(n>=2&&n<=200))throw new Error('Nombre entre 2 et 200');const circ=String(i.type).startsWith('c'),[mn,mx]=bounds([o]),c=mn.map((v,k)=>(v+mx[k])/2);
   const V={type:circ?'circ':'lin',n,dir:i.direction||'X',mode:'pas',step:+(i.pas||200),inv:!!i.inverser,axis:i.axe||'Z',cx:i.cx??c[0],cy:i.cy??c[1],cz:i.cz??c[2],ang:+(i.angle||360),grp:true};const L=repApply([o],V);return L.length+' copies créées.'}},
 {name:'clayonner',description:'Crée un clayonnage : claies tressées sous et sur au moins 2 supports parallèles (noms ou ids). diametre de 8 à 20 mm, jointives par défaut.',inputSchema:{type:'object',properties:{supports:{type:'array',items:{type:'string'}},diametre:{type:'number'},pas:{type:'number',description:'optionnel : sinon jointives'},debut:{type:'number',description:'mm : décalage du début du clayage depuis l’extrémité des supports'},longueur:{type:'number',description:'mm : longueur clayée (0 ou absent = jusqu’au bout)'},cavaliers:{type:'number',description:'si > 0 : pose un clou cavalier toutes les N claies sur les croisements dessus'}},required:['supports','diametre']},
  execute:i=>{let S=(i.supports||[]).map(findP).filter(Boolean);if(S.length==2){const m=midPlan(S,30);S=[S[0],mkObj('trav',{d:m.d,L:m.L},null,'Traverse fine centrale','#d2ab76',m.p0,m.rot,S[0].par),S[1]]}const pl=claieApply(S,{d:+i.diametre,pm:i.pas?'libre':'joint',pitch:+(i.pas||0),margin:10,from:+(i.debut||0),zone:+(i.longueur||0),cav:+i.cavaliers>0,cavN:+i.cavaliers||3,over:0,start:'sous',taper:true});return pl.n+' claies créées.'+(pl.warn.length?' Attention : '+pl.warn.join(' '):'')}},
 {name:'assembler',description:"Assemble deux pièces. type : 'mibois', 'hache' (tenon classique à la hachette, à préférer), 'scie', 'plat', 'aronde1' (trapézoïdale : le bout du tenon est seulement coupé par deux traits de scie inclinés), 'aronde2' (à mi-bois, coupes inclinées), 'cheville'. Pour les tenons, 'a' porte le tenon. diametre : diamètre/épaisseur en mm (optionnel). profondeur_pct : mi-bois seulement.",inputSchema:{type:'object',properties:{type:{type:'string'},a:{type:'string',description:'id ou nom'},b:{type:'string',description:'id ou nom'},diametre:{type:'number'},profondeur_pct:{type:'number'},mortaise:{type:'string',description:"'thru' ou 'blind'"}},required:['type','a','b']},
  execute:i=>{const A=findP(i.a),B=findP(i.b);if(!A||!B)throw new Error('Pièce introuvable : '+(A?i.b:i.a));const k=i.type;let pl;if(k=='mibois')pl=planMibois(A,B,{pc:+i.profondeur_pct||50});else if(k=='cheville')pl=planCheville([A,B],{d:+i.diametre||20});else if(k.startsWith('aronde'))pl=planTenon(A,B,{style:'aronde',typ:+k.slice(6)||1,d:+i.diametre||undefined});else if(TEN_NAMES[k])pl=planTenon(A,B,{style:k,d:+i.diametre||undefined,mort:i.mortaise=='blind'?'blind':'thru'});else throw new Error('Type inconnu');applyPlan(pl);select([A,B]);return(pl.title||'Assemblage')+' créé.'+(pl.warn.length?' Attention : '+pl.warn.join(' '):'')}},
 {name:'modifier_piece',description:"Modifie une traverse : nom, diametre, longueur, ou ses deux extrémités (x1,y1,z1,x2,y2,z2 en mm).",inputSchema:{type:'object',properties:{piece:{type:'string'},nom:{type:'string'},diametre:{type:'number'},longueur:{type:'number'},x1:{type:'number'},y1:{type:'number'},z1:{type:'number'},x2:{type:'number'},y2:{type:'number'},z2:{type:'number'}},required:['piece']},
  execute:i=>{const o=findP(i.piece);if(!o)throw new Error('Pièce introuvable');if(i.nom)o.name=String(i.nom);if(o.type=='trav'){if(+i.diametre>0)o.p.d=+i.diametre;if(+i.longueur>0)o.p.L=+i.longueur;if(i.x1!=null&&i.x2!=null){const A=[+i.x1,+i.y1,+i.z1],B=[+i.x2,+i.y2,+i.z2];if(len(sub(B,A))<30)throw new Error('Longueur trop faible');o.pos=A;o.rot=eul(sub(B,A));o.p.L=len(sub(B,A))}o.g=build(o);mk(o);gzCenter();dlBuild()}touch();ui();return'Pièce modifiée : '+descOf(o)}},
 {name:'supprimer_piece',description:'Supprime une pièce du projet (id ou nom).',inputSchema:{type:'object',properties:{piece:{type:'string'}},required:['piece']},execute:i=>{const o=findP(i.piece);if(!o)throw new Error('Pièce introuvable');const n=o.name;rmObjs([o]);select([]);ui();return'Supprimée : '+n}}];
function aiToggle(){const p=$('#ai');p.hidden=!p.hidden;if(!p.hidden){if(!$('#aim').children.length)aiBubble('a','Bonjour ! Posez-moi une question sur le froissartage (tenons, mi-bois, règle du tiers, outils…) ou demandez-moi de construire une pièce ou un assemblage dans le modèle.');$('#aiq').focus()}}
function aiBubble(r,t){const b=document.createElement('div');b.className='bb '+r;if(r=='a')b.innerHTML=md(t);else b.textContent=t;$('#aim').appendChild(b);$('#aim').scrollTop=1e9;return b}
function aiClear(){aiTurns=[];$('#aim').innerHTML='';if(aiCtl)aiCtl.abort();aiBubble('a','Nouvelle conversation.')}
let aiFiles=[],AI_LIM=null;
function aiChips(){$('#aich').innerHTML=aiFiles.map((f,i)=>`<span class="mu" style="border:1px solid var(--bd);border-radius:10px;padding:1px 8px;font-size:11px">${f.img?'🖼':'📄'} ${esc(f.name.slice(0,22))} <a href="#" onclick="aiFiles.splice(${i},1);aiChips();return false">✕</a></span>`).join('')}
async function aiAttach(L){for(const f of L){if(f.type.startsWith('image/')){if(!(AI_LIM&&AI_LIM.images)){msg('Les images ne sont pas acceptées dans cette page (autorisation de l’assistant).');continue}if(aiFiles.filter(x=>x.img).length>=(AI_LIM.images.maxCount||3)){msg('Nombre maximal d’images atteint.');continue}aiFiles.push({name:f.name,img:true,blob:f})}else if(/\.(txt|md|csv|json|html|svg)$/i.test(f.name)||f.type.startsWith('text/')){const t=await f.text();aiFiles.push({name:f.name,text:t.slice(0,15000)})}else msg('Format non pris en charge : '+f.name+' (images, .txt, .md, .csv, .json, .html). Pour un PDF, joignez une capture d’écran.')}aiChips()}
async function aiSend(){const q=$('#aiq'),t=q.value.trim();if(aiBusy){if(aiCtl)aiCtl.abort();return}if(!t||!window.__ai)return;q.value='';const att=aiFiles.slice();aiFiles=[];aiChips();const imgs=att.filter(f=>f.img).map(f=>f.blob),docs=att.filter(f=>f.text).map(f=>`\n\n[Document joint : ${f.name}]\n${f.text}`).join(''),note=imgs.length?`\n\n[${imgs.length} image(s) jointe(s) à ce message : analysez-les (croquis, photo de modèle, plan) pour proposer la construction.]`:'';aiTurns.push({role:'user',content:t+note+docs});aiBubble('u',t+(att.length?'  📎 '+att.map(f=>f.name).join(', '):''));
 const b=aiBubble('a','Réflexion…'),btn=$('#aib');btn.textContent='Stop';aiBusy=true;aiCtl=new AbortController();
 const lead={role:'user',content:AI_SYS+'\n\n'+KB+'\n\nÉTAT DU PROJET :\n'+projSummary()},turns=aiTurns.slice(-12);
 let useTools=true;try{const l=await window.__ai.limits();useTools=!!l.tools;AI_LIM=l}catch(e){useTools=false}
 try{const r=await window.__ai([lead,...turns],{cache:false,signal:aiCtl.signal,modelTier:'default',tools:useTools?AI_TOOLS():undefined,images:imgs.length&&AI_LIM&&AI_LIM.images?imgs:undefined,onText:({text})=>{b.innerHTML=md(text);$('#aim').scrollTop=1e9}});b.innerHTML=md(r.text+(r.truncated?'\n\n*[réponse coupée]*':''));aiTurns.push({role:'assistant',content:r.text})}
 catch(e){const c=e&&e.code;if(c=='nokey'||c=='badkey'){b.innerHTML=md(c=='nokey'?'Pour utiliser l’assistant, ajoutez votre clé Gemini (gratuite) : une fenêtre s’ouvre.':'La clé Gemini est refusée'+(e.text?' ('+e.text+')':'')+'. Vérifiez-la ou créez-en une autre.');aiKeyDlg()}else if(c=='cancelled'){b.innerHTML=md((e.text||'')+'\n\n*[arrêté]*')}else if(c=='not_granted'||c=='sampling_disabled'||c=='not_declared'){b.innerHTML=md('L’assistant n’est pas autorisé pour cette page.');window.__ai=null;buildRibbon()}else if(c=='rate_limited')b.innerHTML=md((e.text||'')+'\n\nTrop de demandes : réessayez dans un moment.');else b.innerHTML=md((e.text||'')+'\n\nL’assistant est momentanément indisponible. Réessayez.')}
 finally{aiBusy=false;aiCtl=null;btn.textContent='Envoyer';$('#aim').scrollTop=1e9;ui()}}
(async()=>{try{if(window.claude&&claude.use){const s=await claude.use('sample');if(s){window.__ai=s;try{AI_LIM=await s.limits()}catch(e){}buildRibbon();const a=$('#aia');if(a&&AI_LIM&&!AI_LIM.images)a.title='Joindre un document texte (les images ne sont pas disponibles ici)'}}}catch(e){}})();

/* =====================  Démarrage  ===================== */
(function an(){requestAnimationFrame(an);if(!dirty||/\b(dm|sk)\b/.test(document.body.className))return;dirty=false;gzPlace();R.render(sc,cam);dlUpdate();
 const w=R.domElement.clientWidth,h=R.domElement.clientHeight;if(w<VC+16||h<VC+16)return;
 cc.position.set(cam.position.x-oc.target.x,cam.position.y-oc.target.y,cam.position.z-oc.target.z).normalize().multiplyScalar(10);cc.up.set(0,0,1);cc.lookAt(0,0,0);hlt.position.copy(cc.position);
 R.autoClear=false;R.clearDepth();R.setScissorTest(true);R.setViewport(w-VC-8,h-VC-8,VC,VC);R.setScissor(w-VC-8,h-VC-8,VC,VC);R.render(cs,cc);R.setViewport(0,0,w,h);R.setScissorTest(false);R.autoClear=true})();
addEventListener('error',e=>{try{msg('Oups : '+(e.message||'erreur'),6000)}catch(_){}});
addEventListener('unhandledrejection',e=>{try{msg('Oups : '+((e.reason&&e.reason.message)||'erreur'),6000)}catch(_){}});
loadPrefs();rs();
if(gasOK()){TABS['Fichier'][0][1].push(['plateau','Publier (public)','shareModel()'])}
let restored=false;try{const st=JSON.parse(localStorage.getItem(KEY));if(st&&st.objs&&st.objs.length){load(st);restored=true}}catch(e){console.warn(e)}
commit();viewTab=curTab='Accueil';setMode('Accueil');buildRibbon();ui();if(objs.length)fit();else setView('iso');
addEventListener('pagehide',autosave);document.addEventListener('visibilitychange',()=>{if(document.hidden)autosave()});
let lp=null;R.domElement.addEventListener('pointerdown',e=>{if(e.pointerType!='touch')return;lp=setTimeout(()=>{lp=null;const o=pickAt(e);ctx3d(e,o)},650)});['pointerup','pointermove','pointercancel'].forEach(t=>R.domElement.addEventListener(t,e=>{if(lp&&(t!='pointermove'||Math.hypot(e.movementX||0,e.movementY||0)>2)){clearTimeout(lp);lp=null}}));
