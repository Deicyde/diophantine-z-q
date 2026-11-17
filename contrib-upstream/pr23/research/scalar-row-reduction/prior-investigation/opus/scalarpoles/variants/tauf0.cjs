'use strict';
// Adapted from the Version 10 odd-product source, with credits retained below.
// Further changes: reciprocal complete charts and scaled logarithms, normalized poles,
// positive lambda witnesses, correction42, three contacts, and a field-norm anchor.
// Round eight: a uniform order12 pair and the refined-height anchor S=3^2364.
// A separately certified diagonal change balances coefficients without new coordinates.
// The changed local claims are separately reviewed; global source claim is inherited.
// See the proof note and package-root pr_dependency_inventory.json for proofs and scope.
// The original upstream builder independently reconstructed the Brox v3 formulas.
const fs=require('node:fs'), path=require('node:path'), crypto=require('node:crypto');
const OUT=__dirname;
function abs(a){return a<0n?-a:a;}
function gcd(a,b){a=abs(a);b=abs(b);while(b){let c=a%b;a=b;b=c;}return a;}
function Q(n,d=1n){n=BigInt(n);d=BigInt(d);if(!d)throw Error('zero rational denominator');if(d<0n){n=-n;d=-d;}let g=gcd(n,d);return[n/g,d/g];}
const qadd=(a,b)=>Q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const qmul=(a,b)=>Q(a[0]*b[0],a[1]*b[1]);
const qneg=a=>[-a[0],a[1]], qinv=a=>Q(a[1],a[0]);
const qstr=a=>`${a[0]}/${a[1]}`;
const key=(m,s=0)=>s+'|'+m.join(',');
function unpack(k){let [s,m]=k.split('|');return[Number(s),m?m.split(',').map(Number):[]];}
function term(c,m=[],s=0){c=Array.isArray(c)?c:Q(c);return c[0]?new Map([[key(m,s),c]]):new Map();}
const C=(n,d=1)=>term(Q(n,d)), zero=C(0), one=C(1);
function add(...ps){let r=new Map();for(let p of ps)for(let[k,c]of p){let v=qadd(r.get(k)||Q(0),c);if(v[0])r.set(k,v);else r.delete(k);}return r;}
function scale(p,c){c=Array.isArray(c)?c:Q(c);return new Map([...p].map(([k,a])=>[k,qmul(a,c)]).filter(([,a])=>a[0]));}
const sub=(a,b)=>add(a,scale(b,-1));
function mul(a,b){let r=new Map();for(let[k,c]of a)for(let[l,d]of b){let[sk,m]=unpack(k),[sl,n]=unpack(l);let z=key([...m,...n].sort((x,y)=>x-y),sk+sl);let v=qadd(r.get(z)||Q(0),qmul(c,d));if(v[0])r.set(z,v);else r.delete(z);}return r;}
const sq=a=>mul(a,a);
function degree(p){return Math.max(0,...[...p.keys()].map(k=>unpack(k)[1].length));}
function encode(p){return[...p].sort(([a],[b])=>a.localeCompare(b)).map(([k,c])=>{let[s,m]=unpack(k);return{monomial:m,sPower:s,coefficient:qstr(c)};});}
function signature(p){return JSON.stringify(encode(p));}
function constant(p){if(!p.size)return Q(0);if(p.size!==1||!p.has('0|'))return null;return p.get('0|');}
let coords=[],residuals=[],gates=[],values={},guards=[],cse=new Map(),divisionCse=new Map(),census=[];
let block='base', src=[2354,2487];
function fresh(name,kind='gate',protect=false){let id=coords.length;coords.push({id,name,kind,protected:protect,block,sourceLines:src});return term(1,[id]);}
function idof(p){let t=[...p];if(t.length!==1)throw Error('not variable');let[s,m]=unpack(t[0][0]);if(s||m.length!==1||qstr(t[0][1])!=='1/1')throw Error('not variable');return m[0];}
function residual(name,p,kind='structural'){if(degree(p)>2)throw Error(`${name} has degree ${degree(p)}`);let id=residuals.length;residuals.push({id,name,kind,block,sourceLines:src,terms:encode(p)});return id;}
function deps(...ps){return[...new Set(ps.flatMap(p=>[...p.keys()].flatMap(k=>unpack(k)[1])))].sort((a,b)=>a-b);}
function save(name,p){values[name]={terms:encode(p),block,sourceLines:src};return p;}
function saveF(name,a){save(name+'.0',a[0]);save(name+'.1',a[1]);return a;}
function assign(name,p){
 if(degree(p)>2)throw Error(`${name} assignment degree ${degree(p)}`);
 // Store semantic b itself to avoid raising its normalization scale to the
 // fourth power in the preparation conic; this is an affine coordinate change.
 if(name==='scalar.b' || name==='inputProduct'){
  const v=fresh(name+'.quadratic'),ri=residual(name+'.definition',sub(v,p),'gate');
  gates.push({coordinateId:idof(v),definitionResidualId:ri,operation:'quadratic_assignment',expression:encode(p),dependencies:deps(p),block,sourceLines:src});
  return save(name,v);
 }
 if(degree(p)<=1)return save(name,p);
 let h=new Map(),l=new Map();for(let[k,c]of p)(unpack(k)[1].length===2?h:l).set(k,c);
 let lead=[...h].sort(([a],[b])=>a.localeCompare(b))[0][1], norm=scale(h,qinv(lead)), sig=signature(norm), v=cse.get(sig);
 if(!v){v=fresh(name+'.quadratic');let ri=residual(name+'.definition',sub(v,norm),'gate');gates.push({coordinateId:idof(v),definitionResidualId:ri,operation:'quadratic_assignment',expression:encode(norm),dependencies:deps(norm),block,sourceLines:src});cse.set(sig,v);}
 return save(name,add(scale(v,lead),l));
}
const rm=(name,a,b)=>assign(name,mul(a,b));
const rsq=(name,a)=>assign(name,sq(a));
function rp(name,a,n){if(n===0)return one;if(n===1)return a;let v=rp(name+'.half',a,Math.floor(n/2));v=rsq(name+'.square',v);return n%2?rm(name+'.odd',v,a):v;}
function rquot(name,a,b,domain){
 let bc=constant(b);if(bc){if(!bc[0])throw Error('division by constant zero');return assign(name,scale(a,qinv(bc)));}
 if(degree(b)>1||degree(a)>2)throw Error('quotient degree');
 let sig='Q:'+signature(a)+'/'+signature(b),old=divisionCse.get(sig);if(old)return save(name,old);
 let v=fresh(name);let ri=residual(name+'.definition',sub(mul(b,v),a),'gate');gates.push({coordinateId:idof(v),definitionResidualId:ri,operation:'rational_quotient',numerator:encode(a),denominator:encode(b),domain,dependencies:deps(a,b),block,sourceLines:src});divisionCse.set(sig,v);return save(name,v);
}
function inv(name,a){let v=rquot(name,one,a,'equation_enforces_nonzero');guards.push({name,expression:encode(a),inverse:encode(v),sourceLines:src});return v;}
const F=(a,b=0)=>[Array.isArray(a)&&a[0] instanceof Map?a[0]:a instanceof Map?a:C(a),b instanceof Map?b:C(b)];
const fadd=(a,b)=>[add(a[0],b[0]),add(a[1],b[1])], fsub=(a,b)=>[sub(a[0],b[0]),sub(a[1],b[1])];
const fconj=a=>[a[0],scale(a[1],-1)];
const fc=(a,b=0)=>[Array.isArray(a)?term(a):C(a),Array.isArray(b)?term(b):C(b)];
const fscale=(a,c)=>[scale(a[0],c),scale(a[1],c)];
const rawFmul=(a,b)=>[add(mul(a[0],b[0]),scale(mul(a[1],b[1]),2)),add(mul(a[0],b[1]),mul(a[1],b[0]))];
function fmul(name,a,b){return saveF(name,[assign(name+'.0',add(mul(a[0],b[0]),scale(mul(a[1],b[1]),2))),assign(name+'.1',add(mul(a[0],b[1]),mul(a[1],b[0])))]);}
function fsq(name,a){return fmul(name,a,a);}
function fscalar(name,a,b){return saveF(name,[rm(name+'.0',a[0],b),rm(name+'.1',a[1],b)]);}
function fquot(name,a,b,domain){
 let b0=constant(b[0]),b1=constant(b[1]);
 if(b0&&b1){let norm=qadd(qmul(b0,b0),qneg(qmul(Q(2),qmul(b1,b1))));if(!norm[0])throw Error('field constant denominator zero');return fmul(name,a,[term(qmul(b0,qinv(norm))),term(qneg(qmul(b1,qinv(norm))))]);}
 let sig='FQ:'+signature(a[0])+','+signature(a[1])+'/'+signature(b[0])+','+signature(b[1]);let old=divisionCse.get(sig);if(old)return saveF(name,old);
 let z=[fresh(name+'.0'),fresh(name+'.1')];
 let eqs=[sub(add(mul(b[0],z[0]),scale(mul(b[1],z[1]),2)),a[0]),sub(add(mul(b[0],z[1]),mul(b[1],z[0])),a[1])];
 for(let j=0;j<2;j++){let ri=residual(name+'.definition.'+j,eqs[j],'gate');gates.push({coordinateId:idof(z[j]),definitionResidualId:ri,operation:'field_quotient_component',component:j,numerator:a.map(encode),denominator:b.map(encode),output:z.map(encode),domain,dependencies:deps(...a,...b),block,sourceLines:src});}
 divisionCse.set(sig,z);return saveF(name,z);
}
function finv(name,a){let z=fquot(name,fc(1),a,'equations_enforce_nonzero');guards.push({name,fieldExpression:a.map(encode),fieldInverse:z.map(encode),sourceLines:src});return z;}
function start(name,lines){block=name;src=lines;census.push({block,startCoordinates:coords.length,startResiduals:residuals.length});}
// Allocate the 61 base coordinates before arithmetic gates, including two positivity witnesses.
const X=fresh('input','input',true), names=['A','S','T','Z','H','UA','US','UT','UZ'];
let half={};for(let n of names)half[n]={x:[fresh(n+'.chart.h0','base'),fresh(n+'.chart.h1','base')],y:[fresh(n+'.chart.j0','base'),fresh(n+'.chart.j1','base')]};
const lambda=fresh('lambda','base');
const lambdaPositive=[fresh('lambda.positiveA','base'),fresh('lambda.positiveB','base')];
let poles=[];for(let r=0;r<3;r++)poles.push({e:fresh('detector'+r+'.normalized_e','base'),s:fresh('detector'+r+'.s','base'),p:fresh('detector'+r+'.p','base'),q:fresh('detector'+r+'.q','base')});
const scalar={u:fresh('scalar.preparationU','base'),v:fresh('scalar.preparationV','base'),e:fresh('scalar.normalized_e','base'),s:fresh('scalar.s','base'),p:fresh('scalar.p','base'),q:fresh('scalar.q','base')};
const anchor=[fresh('anchor.u','base',true),fresh('anchor.v','base',true),fresh('anchor.w','base',true)];
if(coords.length!==61)throw Error('base count '+coords.length);

// Odd-index root witnesses: Q in P+4E(K), with P=2R0, R0=(1+sqrt(2),2sqrt(2)).
// Oddness is now imposed by the packed 2/3-local anchor.
const oddChartWitnesses={};

const D=fc(11,-6), P={x:fc(Q(57,8),Q(-7,2)),y:fc(Q(-165,8),Q(417,32)),h:fc(-1,Q(7,4)),j:fc(Q(39,8),Q(-9,2))};
function double(name,Qp,withCurve=false){
 if(withCurve)throw Error('new double expects the already certified square-abscissa chart');
 const k=fquot(name+'.k',fadd(rawFmul(Qp.x,Qp.x),D),fscale(Qp.j,2),'nonzero_j_on_square_abscissa_chart');
 const h=fquot(name+'.h',k,Qp.h,'nonzero_h_on_square_abscissa_chart');
 const x=fsq(name+'.xSquare',h);
 const u=fquot(name+'.tSquare',rawFmul(Qp.j,Qp.j),fscale(Qp.x,2),'nonzero_x_on_square_abscissa_chart');
 const j=fsub(u,x),y=rawFmul(h,j);
 return {h:saveF(name+'.h',h),j:saveF(name+'.j',j),x:saveF(name+'.x',x),y:saveF(name+'.y',y)};
}
start('point_modules',[4311,4348]);
residual('lambda.positiveChart',sub(sub(lambda,C(32,1225)),add(sq(lambdaPositive[0]),sq(lambdaPositive[1]))));
// Square-abscissa Kummer chart; y=h*j is kept as an expression only.
const reciprocalCharts=new Set(['H','UA','US','UT','UZ']);
let points={};for(let n of names){
 const h=half[n].x,j=half[n].y,x=fsq(n+'.chart.x',h);
 if(n==='H'){
  // Joint H,H-P chart: half.H.y is s=g_H*tau, not l_H.
  points[n]={g:saveF(n+'.g',h),s:saveF(n+'.jointProduct',j),f:saveF(n+'.f',x)};
  continue;
 }
 if(reciprocalCharts.has(n)){
  // Here h,j are reinterpreted as g,l, with f=g^2 and l^2=1-D f^2.
  const g=h,l=j,f=x;
  const df2=rawFmul(D,rawFmul(f,f)),l2=rawFmul(l,l);
  for(let c=0;c<2;c++)residual(n+'.chart.equation.'+c,add(l2[c],df2[c],c===0?C(-1):zero));
  points[n]={g:saveF(n+'.g',g),l:saveF(n+'.l',l),f:saveF(n+'.f',f)};
  continue;
 }
 residual(n+'.chart.equation.0',add(sq(j[0]),scale(sq(j[1]),2),scale(sq(x[0]),-1),scale(sq(x[1]),-2),D[0]));
 residual(n+'.chart.equation.1',add(scale(mul(j[0],j[1]),2),scale(mul(x[0],x[1]),-2),D[1]));

 if(oddChartWitnesses[n]){
  const t=oddChartWitnesses[n].t,r=oddChartWitnesses[n].r;
  const tt=fsub(rawFmul(t,t),fscale(fadd(x,j),2));
  const aa=fsub(fadd(rawFmul(t,h),fadd(x,j)),rawFmul(fc(1,1),rawFmul(r,r)));
  for(let k=0;k<2;k++){
   residual(n+'.odd.halfParameter.'+k,tt[k]);
   residual(n+'.odd.halfAbscissaClass.'+k,aa[k]);
  }
 }
 const y=rawFmul(h,j);
 points[n]={h:saveF(n+'.h',h),j:saveF(n+'.j',j),x:saveF(n+'.x',x),y:saveF(n+'.y',y)};
}

start('direct_targets',[2394,2399]);
let four={P};for(let n of ['A','S','T','Z'])four[n]=points[n];
start('five_differences',[2394,2399]);
function subtractReciprocal(name,Qp,Rp){
 const F=fadd(Rp.x,rawFmul(D,Qp.f));
 const tau=fquot(name+'.inverseRoot',fsub(rawFmul(Rp.h,Qp.l),rawFmul(Qp.g,Rp.j)),F,'totally_positive_xR_plus_D_fU');
 const f=fsq(name+'.f',tau);
 const M=fquot(name+'.scaledK',fscale(rawFmul(Qp.g,fadd(Rp.x,rawFmul(D,f))),-1),tau,'zero_tau_contradicts_scaledK_equation');
 return {inverseRoot:tau,f:saveF(name+'.f',f),logDenominator:saveF(name+'.logDenominator',fsub(M,Rp.j)),logScale:Rp.h};
}
function subtractSharedJoint(name,Qp,Rp){
 const s=Qp.s,fU=Qp.f;
 const fV=fquot(name+'.f',rawFmul(s,s),fU,'joint_chart_equations_force_nonzero_fH');
 const Ds2=rawFmul(D,rawFmul(s,s)),js=rawFmul(Rp.j,s),xfV=rawFmul(Rp.x,fV),xfU=rawFmul(Rp.x,fU);
 const kH=fquot('primaryRatio',fsub(fc(1),fadd(xfU,js)),rawFmul(Rp.h,s),'joint_chart_equations_force_nonzero_s');
 const kV=fquot(name+'.k',fsub(fadd(xfV,js),fc(1)),rawFmul(Rp.h,s),'joint_chart_equations_force_nonzero_s');
 const curve=fadd(fadd(Ds2,rawFmul(Rp.x,fadd(fU,fV))),fscale(js,2));
 for(let c=0;c<2;c++)residual(name+'.jointCurve.'+c,sub(curve[c],c===0?one:zero));
 return {f:saveF(name+'.f',fV),k:saveF(name+'.k',kV),primaryRatio:kH};
}
function subtractRootConstantTau(name,Qp,Rp){
 const F=fadd(rawFmul(Rp.x,Qp.x),D);
 // w=(h_R h_Q j_Q - x_Q j_R)/F and x_Q=h_Q^2, so tau=w/h_Q has a linear numerator.
 const tau=fquot(name+'.tau',fsub(rawFmul(Rp.h,Qp.j),rawFmul(Qp.h,Rp.j)),F,'totally_positive_xP_xU_plus_D');
 return {tau:saveF(name+'.tau',tau),f:saveF(name+'.f',rawFmul(tau,tau))};
}
function subtractRootConstant(name,Qp,Rp){
 const F=fadd(rawFmul(Rp.x,Qp.x),D);
 const w=fquot(name+'.rootTimesInverseRoot',fsub(rawFmul(Rp.h,rawFmul(Qp.h,Qp.j)),rawFmul(Qp.x,Rp.j)),F,'totally_positive_xP_xU_plus_D');
 const f=fquot(name+'.f',rawFmul(w,w),Qp.x,'nonzero_root_square_abscissa');
 // f=(w/hS)^2. Its real coefficient is positive unless w=0.
 // This one rational inverse replaces the nonzero domain formerly forced by M.
 inv(name+'.nonzeroRealF',f[0]);
 const denominator=fadd(fadd(Rp.x,rawFmul(D,f)),rawFmul(Rp.j,w));
 return {f:saveF(name+'.f',f),w:saveF(name+'.w',w),ratioDenominator:saveF(name+'.ratioDenominator',denominator)};
}
const U=[points.H,points.UA,points.US,points.UT,points.UZ], R=[four.P,four.A,four.S,four.T,four.Z];
const V=U.map((p,i)=>i===0?subtractSharedJoint('V'+i,p,R[i]):subtractReciprocal('V'+i,p,R[i]));
start('parameters_and_logarithms',[2401,2411]);
function parameters(name,p){return{point:p,f:p.f||finv(name+'.f',p.x),z:(name.startsWith('V') || name.startsWith('U') || name==='Sscalar')?null:(p.h?fquot(name+'.z',fscale(p.h,-1),p.j,'nonzero_h_and_j_on_square_abscissa_chart'):fquot(name+'.z',fscale(p.x,-1),p.y,'finite_double_or_difference_nonzero_y_Brox4311_4348'))};}
const PU=U.map((p,i)=>parameters('U'+i,p)),PV=V.map((p,i)=>parameters('V'+i,p));
const aCoeffs=[Q(1),Q(-2,5)];for(let j=2;j<=12;j++)aCoeffs.push(qmul(aCoeffs[j-1],Q(4*j-5,4*j+1)));
// Complete a polynomial square: G12=a12*U6^2+R6.
// All coefficients are rational; U6 is monic with zero constant term.
const logSquareU=Array.from({length:7},()=>Q(0));logSquareU[6]=Q(1);
for(let d=11;d>=7;d--){
 let known=Q(0);for(let i=0;i<=6;i++){let j=d-i;if(j>=0&&j<=6)known=qadd(known,qmul(logSquareU[i],logSquareU[j]));}
 logSquareU[d-6]=qmul(qadd(qmul(aCoeffs[d],qinv(aCoeffs[12])),qneg(known)),Q(1,2));
}
const logSquareR=Array.from({length:13},(_,d)=>{
 let c=aCoeffs[d];for(let i=0;i<=6;i++){let j=d-i;if(j>=0&&j<=6)c=qadd(c,qneg(qmul(aCoeffs[12],qmul(logSquareU[i],logSquareU[j]))));}
 return c;
});
if(logSquareR.slice(7).some(c=>c[0]))throw Error('degree12 completion identity');
// Field polynomial helpers; high comparisons use degree-twelve completion.

function rawPolynomial6(coeff,basis){
 let out=fc(0);
 for(let k=0;k<coeff.length;k++){
  let term=k<=3?basis[k]:rawFmul(basis[3],basis[k-3]);
  out=fadd(out,fscale(term,coeff[k]));
 }
 return out;
}
function log(name,p,polynomialDegree){
 let w=fmul(name+'.w',D,fsq(name+'.fSquare',p.f));
 if(polynomialDegree===12){
  let w2=fsq(name+'.wPower2',w),w4=fsq(name+'.wPower4',w2);
  let basis=[fc(1),w,w2,rawFmul(w,w2),w4,rawFmul(w,w4),rawFmul(w2,w4)];
  let uraw=fc(0),remainder=fc(0);
  for(let j=0;j<=6;j++){
   uraw=fadd(uraw,fscale(basis[j],logSquareU[j]));
   remainder=fadd(remainder,fscale(basis[j],logSquareR[j]));
  }
  let u=saveF(name+'.squareRoot',uraw.map((v,j)=>assign(name+'.squareRoot.'+j,v)));
  let outraw=fadd(fscale(rawFmul(u,u),aCoeffs[12]),remainder),out=outraw.map((v,j)=>assign(name+'.polynomial.'+j,v));
  if(p.point.logDenominator){const eta=fquot(name+'.scaled',fscale(out,-1),p.point.logDenominator,'nonzero_root_h_times_y_over_x');return saveF(name,rawFmul(p.point.logScale,eta));}
  return p.point.k?fquot(name,fscale(out,-1),p.point.k,'nonzero_y_over_x'):p.z?fmul(name,p.z,out):fquot(name,fscale(rawFmul(p.point.h||p.point.x,out),-1),p.point.j||p.point.y,'nonzero_chart_j_or_difference_y');
 }
 let rawout=fadd(fadd(fc(aCoeffs[0]),fscale(w,aCoeffs[1])),fscale(rawFmul(w,w),aCoeffs[2]));
 let out=saveF(name+'.polynomial',rawout.map((v,j)=>assign(name+'.polynomial.'+j,v)));
 if(p.point.logDenominator){const eta=fquot(name+'.scaled',fscale(out,-1),p.point.logDenominator,'nonzero_root_h_times_y_over_x');return saveF(name,rawFmul(p.point.logScale,eta));}
 return p.point.k?fquot(name,fscale(out,-1),p.point.k,'nonzero_y_over_x'):p.z?fmul(name,p.z,out):fquot(name,fscale(rawFmul(p.point.h||p.point.x,out),-1),p.point.j||p.point.y,'nonzero_chart_j_or_difference_y');
}
const primaryRatio=V[0].primaryRatio,LV=PV.map((p,i)=>log('logV'+i,p,i===1?2:12));
let L=[],LP=[];for(let i=1;i<=4;i++){L[i]=fquot('L'+i,rawFmul(primaryRatio,PU[i].point.g),PU[i].point.l,'nonzero_l_on_reciprocal_quartic_chart');LP[i]=fconj(fquot('LP'+i,LV[i],LV[0],'global_reciprocal_log_nonvanishing_Brox4353_4360'));}
start('direct_tests_and_shared_symmetric_coefficients',[4575,4605]);
const inputProduct=assign('inputProduct',add(sq(X),X)),inputSquare=save('inputSquare',sub(inputProduct,X)),beta=save('beta',add(scale(inputProduct,11016),C(5155)));
const CC=fmul('Lucas.C',fsub(L[2],fc(2)),L[4]), AT=fmul('Lucas.AT',L[2],L[3]);
const FF=[assign('Lucas.F0',add(sq(L[3][0]),scale(sq(L[3][1]),2),scale(mul(AT[0],CC[0]),-1),scale(mul(AT[1],CC[1]),-2),sq(CC[0]),scale(sq(CC[1]),2),C(-1))),assign('Lucas.F1',add(scale(mul(L[3][0],L[3][1]),2),scale(mul(AT[0],CC[1]),-1),scale(mul(AT[1],CC[0]),-1),scale(mul(CC[0],CC[1]),2)))];
const tests=[...PU.map((p,i)=>({value:p.point.g,order:i===0?45:i===1?12:1})),...PV.map(p=>({value:fconj(p.f),order:1}))];
for(let i=1;i<=4;i++)tests.push({value:fsub(L[i],LP[i]),order:i===1?12:45});
tests.push({value:fsub(L[1],[beta,zero]),order:45},{value:FF,order:45});
tests.forEach((t,j)=>saveF('test'+j,t.value));
function polyProduct(name, ys) {
 if(ys.length===1)return [fc(1),ys[0]];
 let cut=Math.floor(ys.length/2),a=polyProduct(name+'.left',ys.slice(0,cut)),b=polyProduct(name+'.right',ys.slice(cut)),out=[fc(1)];
 for(let k=1;k<a.length+b.length-1;k++){
  let c=[zero,zero];
  for(let i=Math.max(0,k-b.length+1);i<=Math.min(k,a.length-1);i++){
   let u=a[i],v=b[k-i];
   c[0]=add(c[0],mul(u[0],v[0]),scale(mul(u[1],v[1]),2));
   c[1]=add(c[1],mul(u[0],v[1]),mul(u[1],v[0]));
  }
  out[k]=[assign(name+'.co'+k+'.0',c[0]),assign(name+'.co'+k+'.1',c[1])];
 }
 return out;
}
let squareTests={};for(let m of [1,12,45])squareTests[m]=tests.filter(t=>t.order===m).map((t,j)=>fsq('testSquare.'+m+'.'+j,t.value));
const mixedTest1=squareTests[12][0],mixedTest12=squareTests[12][1],mixedTestProduct=fmul('mixedTestProduct',mixedTest1,mixedTest12);
let coeffs={};for(let m of [1,45]){let sqtests=squareTests[m],sizes=m===1?[4,4]:[3,3],pos=0;coeffs[m]=sizes.map((n,b)=>{let co=polyProduct('symmetric.'+m+'.group'+b,sqtests.slice(pos,pos+n));pos+=n;return co;});}
start('fixed_height_scales',[3352,3405]);
let productX=fc(1);
for(let n of ['A','S','T','Z'])productX=fmul('heightProduct.'+n,productX,points[n].x);
saveF('heightProduct',productX);
const scales=[one,rsq('heightProduct.scale0',productX[0]),rsq('heightProduct.scale1',add(productX[0],productX[1]))];
// Algebraic abbreviations for the weights: e=(A*delta)^5/F,
// R=1/E, q1=e/delta, q12=q1*e^22, q45=q1*e^88; E=q1*delta^2.
function evalSym(name,blocks,q){
 let maxdeg=Math.max(...blocks.map(co=>co.length-1)),powers=[one,q];
 for(let k=2;k<=maxdeg;k++)powers[k]=rm(name+'.power'+k,powers[Math.floor(k/2)],powers[Math.ceil(k/2)]);
 let factors=blocks.map((co,b)=>{let out=fc(0);for(let k=0;k<co.length;k++)for(let j=0;j<2;j++)out[j]=add(out[j],mul(co[k][j],powers[k]));return [assign(name+'.block'+b+'.0',out[0]),assign(name+'.block'+b+'.1',out[1])];});
 let prod=fc(1);for(let b=0;b<factors.length;b++)prod=fmul(name+'.product'+b,prod,factors[b]);
 return saveF(name,prod);
}
function pole(name,b,p,prep,preparationBase=null){
 // All b are nonzero. Normalize old e,p,s,q as b*e,b*p,b*s,b^2*q.
 const B=scale(b,17),pp=rsq(name+'.p2',p.p);
 residual(name+'.firstConic',sub(mul(B,pp),mul(sub(C(17),p.e),add(C(17),scale(p.e,3)))));
 let T=preparationBase ? assign(name+'.preparationT',preparationBase) : b;
 if(prep){
  // T = U_old^2/b = b-V_old^2; U_old,V_old are unchanged.
  T=assign(name+'.preparationT',sub(preparationBase||b,sq(p.v)));
  residual(name+'.preparationConic',sub(sq(p.u),mul(b,T)));
  save(name+'.U',p.u);
 }
 const Bh=rm(name+'.Bh',p.e,sub(C(17),T)),ss=rsq(name+'.s2',p.s),qq=rsq(name+'.q2',p.q);
 residual(name+'.secondConic',sub(mul(B,qq),mul(sub(ss,Bh),add(ss,scale(Bh,3)))));
}
for(let r=0;r<3;r++){
 start('detector_'+r,[2424,2460]);let A=scales[r],t=rm('detector'+r+'.t',A,lambda),delta=sub(scale(t,98),one);
 let roots=[Q(0),Q(-1,49),Q(-1,50),Q(-1,2450),Q(-32,1225)],cs=[Q(1)];
 for(let root of roots){let nx=Array(cs.length+1).fill(null).map(()=>Q(0));for(let k=0;k<cs.length;k++){nx[k]=qadd(nx[k],qmul(root,cs[k]));nx[k+1]=qadd(nx[k+1],cs[k]);}cs=nx;}
 let t2=rsq('detector'+r+'.Fsquare',t),middle=assign('detector'+r+'.Fmiddle',add(mul(t2,add(t,term(cs[4]))),scale(t,cs[3]),term(cs[2]))),Fv=assign('detector'+r+'.F',add(mul(t2,middle),scale(t,cs[1]),term(cs[0])));
 let Ad=rm('detector'+r+'.Adelta',A,delta);
 // Contact-unit normalization: use delta*D as the semantic one-place test.
 // q_m=e^(2m-1)/delta=E^(m-1)*q1^m, where E=1/R; e need not be stored.
 let q1=rquot('detector'+r+'.q1',mul(rp('detector'+r+'.Adelta4',Ad,4),A),Fv,'positive_scale_and_guard_make_numerator_nonzero');
 const delta2=rsq('detector'+r+'.delta2',delta),eDelta=rm('detector'+r+'.eDelta',q1,delta2);
 let q1square=rsq('detector'+r+'.q1SquaredForWeights',q1),q1cube=rm('detector'+r+'.q1CubedForWeights',q1square,q1);
 // Fmiddle = t^3 + cs[4]*t^2 + cs[3]*t + cs[2].
 // Thus both t^3 and (98*t-1)^3 are affine in existing coordinates.
 const t3=sub(middle,add(scale(t2,cs[4]),scale(t,cs[3]),term(cs[2])));
 const delta3=save('detector'+r+'.deltaCubed',add(scale(t3,98**3),scale(t2,-3*98**2),scale(t,3*98),C(-1)));
 let e3=rm('detector'+r+'.eCubed',q1cube,delta3),
 e6=rsq('detector'+r+'.eSixth',e3),
 e12=rsq('detector'+r+'.eTwelfth',e6),
 q12=rquot('detector'+r+'.q12',sq(e12),eDelta,'positive_inverse_R');
 let mixedHigh=rsq('detector'+r+'.mixedHigh',q12);
 let q45=rquot('detector'+r+'.q45',sq(mixedHigh),q1cube,'positive_order_one_weight');
 // Both paired tests now have order12; mixedHigh=q12^2 is already stored.
 let mixedRaw=fadd(fc(1),fadd(rawFmul([q12,zero],fadd(mixedTest1,mixedTest12)),rawFmul([mixedHigh,zero],mixedTestProduct)));
 let mixed=saveF('detector'+r+'.mixed',mixedRaw.map((v,j)=>assign('detector'+r+'.mixed.'+j,v)));
 let pure=fmul('detector'+r+'.pure',evalSym('detector'+r+'.E1',coeffs[1],q1),evalSym('detector'+r+'.E45',coeffs[45],q45));
 let w=fmul('detector'+r+'.W',pure,mixed);
 let nw=rquot('detector'+r+'.normOver2w0',scale(sub(sq(w[0]),scale(sq(w[1]),2)),Q(1,2)),w[0],'positive_lambda_and_totally_positive_factor_product'),bv=rquot('detector'+r+'.B',sq(nw),eDelta,'positive_factor_product_forces_nonzero_norm');
 save('detector'+r+'.Bsemantic',bv);pole('detector'+r,bv,poles[r],false);
}
start('scalar_block',[2462,2489]);
const correction=C(42);
let r1=rm('scalar.rPair1',beta,sub(beta,one)),rr=save('scalar.r',rm('scalar.rThree',r1,add(scale(beta,32),C(343))));
let ri=inv('scalar.rInverse',rr);
// Three Laurent steps suffice: inverse weights on the right preserve scalar order 28.
const ri3=rquot('scalar.rInverse3',sq(ri),rr,'positive_scalar_contact_product'),
      ri7=rquot('scalar.rInverse7',sq(ri3),rr,'positive_scalar_contact_product'),
      ri15=rquot('scalar.rInverse15',sq(ri7),rr,'positive_scalar_contact_product');
const scalarPoint=subtractRootConstantTau('scalar.shiftedS',points.S,P);
const PS={f:scalarPoint.tau};
// At every consumed place, w*kQ is congruent to -hP. Since Re(-hP)=1,
// the real coefficient of kH*w has the same valuation as (a-1)/h.
const ratioProxyReal=assign('scalar.ratioProxyReal',add(mul(primaryRatio[0],scalarPoint.tau[0]),scale(mul(primaryRatio[1],scalarPoint.tau[1]),2)));
inv('scalar.shiftedS.nonzeroRealF',assign('scalar.shiftedS.f0',add(sq(scalarPoint.tau[0]),scale(sq(scalarPoint.tau[1]),2))));
const directLeaf=saveF('scalar.directLeaf',[rquot('scalar.ratioProxyLeaf',mul(ratioProxyReal,ri15),rr,'positive_scalar_contact_product'),zero]);
// Keep the four formal-place tests, placing the scalar proxy deepest.
function normTree(name,a,b,weight=rr){return assign(name,add(sq(a),mul(weight,rsq(name+'.rightSquare',b))));}
const chain3=normTree('scalar.chain3',PS.f[1],directLeaf[0],ri15);
const chain2=normTree('scalar.chain2',PS.f[0],chain3,ri15);
const chain1=normTree('scalar.chain1',PU[0].f[1],chain2,ri15);
const nCore=rquot('scalar.N',add(sq(PU[0].f[0]),mul(ri15,rsq('scalar.N.rightSquare',chain1))),rr,'positive_scalar_contact_product');
let nw=save('scalar.W',nCore);
// Absorb the known square W^2 into p,q and the preparation ordinate U.
// New p=W*p_old, q=W*q_old, U=U_old/W; W>=1 since r>0.
const rho=save('scalar.correctedR',scale(rr,42));
const Tq=rquot('scalar.preparationT',scale(sq(nw),42),ri,'rInverse_nonzero_since_r_times_rInverse_is_one');
save('scalar.Bsemantic',Tq);
pole('scalar',rho,scalar,false,Tq);
start('anchor',[4160,4178]);
// Use N(w), which measures the same local index depth at half the old exponent.
// Keep T itself as a coordinate: assign() would separate the S-linear part.
// The existing scale0 coordinate is C0^2; S*scale0 remains quadratic after lifting S.
const physicalExpression=add(sq(scalarPoint.tau[0]),scale(sq(scalarPoint.tau[1]),-2),scale(mul(term(1,[],1),scales[1]),50331648),scale(mul(term(1,[],1),inputSquare),-6));
let fa=fresh('anchor.physicalA.quadratic','gate',true);
for(const v of deps(scales[1],inputSquare))coords[v].protected=true;
const physicalRow=residual('anchor.physicalA.definition',sub(fa,physicalExpression),'gate');
gates.push({coordinateId:idof(fa),definitionResidualId:physicalRow,operation:'quadratic_assignment',expression:encode(physicalExpression),dependencies:deps(physicalExpression),block,sourceLines:src});
save('anchor.physicalA',fa);
const anchorRow=residual('anchor.equation',add(sq(anchor[0]),scale(sq(anchor[1]),6),scale(sq(anchor[2]),-2),scale(sq(fa),-3),term(2,[],2)));
save('anchor.physicalA',fa);
for(let i=0;i<census.length;i++){let c=census[i],next=census[i+1];c.newCoordinates=(next?next.startCoordinates:coords.length)-c.startCoordinates;c.newResiduals=(next?next.startResiduals:residuals.length)-c.startResiduals;}
const sourceName='sources/diophantine_optimization_20261106_v3.tex';
const inputSourceSha256='fc8bc7b8fae727e24f934ddd7de0a7cff8a005e89c3d0cac1ea14e5191b910ca';
const data={format:'brox-independent-quadratic-ir-v1',source:{path:sourceName,sha256:inputSourceSha256,reconstruction:'independent_from_displayed_formulas_not_original_gate_bytes',refinements:[{name:'shared_scalar_point',lines:[2946,3044]},{name:'fixed_scales',lines:[3352,3405]},{name:'comparison_precision52',lines:[4160,4279]},{name:'scalar_order32',lines:[4285,4306]},{name:'quotient_domains',lines:[4311,4405]},{name:'direct_lucas',lines:[4575,4605]}]},fixedParameter:{name:'S',value:'3^2130',coordinate:false},coordinates:coords,residuals,gates,values,guards,census,anchor:{rowId:anchorRow,privateCoordinateIds:anchor.map(idof),physicalA:encode(fa)},counts:{baseCoordinates:coords.filter(c=>c.kind==='base'||c.kind==='input').length,structuralResiduals:residuals.length-gates.length,coordinates:coords.length,residuals:residuals.length,gates:gates.length}};
data.variant={name:'round8_primary12_uniform_pair_anchor2364',status:'conditional',transformations:'pr_dependency_inventory.json',inputUnchanged:true};
fs.writeFileSync(path.join(OUT,'raw-ir.json'),JSON.stringify(data,null,2)+'\n');
// An equivalent translated system. This is 16 times the original anchor
// after u=S+(U-3V+3W)/4,v=S/2+V/4,w=3S/2+W/4.
let translated=JSON.parse(JSON.stringify(data));let[u,v,w]=anchor;
translated.residuals[anchorRow].terms=encode(add(scale(sq(fa),-48),sq(u),scale(mul(u,v),-6),scale(mul(u,w),6),scale(sq(v),15),scale(mul(v,w),-18),scale(sq(w),7),mul(term(8,[],1),u)));
translated.residuals[anchorRow].name='anchor.translatedEquation';translated.anchor.translation={oldU:'S+(U-3V+3W)/4',oldV:'S/2+V/4',oldW:'3S/2+W/4',newRowEquals:'16*oldRowAfterSubstitution',determinant:'1/64'};
translated.coordinates[anchor.map(idof)[0]].name='anchor.U';translated.coordinates[anchor.map(idof)[1]].name='anchor.V';translated.coordinates[anchor.map(idof)[2]].name='anchor.W';
fs.writeFileSync(path.join(OUT,'raw-translated-ir.json'),JSON.stringify(translated,null,2)+'\n');
fs.writeFileSync(path.join(OUT,'census.json'),JSON.stringify({counts:data.counts,blocks:census},null,2)+'\n');
console.log(JSON.stringify({counts:data.counts,census},null,2));
