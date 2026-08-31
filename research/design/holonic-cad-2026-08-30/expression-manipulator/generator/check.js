const sub=(a,b)=>[a[0]-b[0],a[1]-b[1],a[2]-b[2]];
const add=(a,b)=>[a[0]+b[0],a[1]+b[1],a[2]+b[2]];
const mul=(a,s)=>[a[0]*s,a[1]*s,a[2]*s];
const dot=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2];
function retarded(p,u,c){const r=sub(p,c);const A=1-dot(u,u);const B=-2*dot(r,u);const C=-dot(r,r);
 const disc=B*B-4*A*C;const t=(-B-Math.sqrt(disc))/(2*A);const rRet=add(r,mul(u,t));return{t,rRet,n:-t};}
function aberrate(rRet,n,beta,g){const b2=dot(beta,beta);if(b2===0)return rRet.slice();
 const bh=mul(beta,1/Math.sqrt(b2));const rPar=dot(rRet,bh);const rPerp=sub(rRet,mul(bh,rPar));
 return add(rPerp,mul(bh,g*(rPar+Math.sqrt(b2)*n)));}
function doppler(rRet,n,beta,g){return n/(g*(n+dot(beta,rRet)));}

// test 1: light-cone identity |rRet| == -t
let p=[7,-3,11],u=[0.2,-0.1,0.35],c=[1,2,3];
let {t,rRet,n}=retarded(p,u,c);
console.log("|rRet|-n =", Math.hypot(...rRet)-n);

// test 2: aberration matches cos th' = (cos th + b)/(1 + b cos th)
let beta=[0,0,0.8], g=1/Math.sqrt(1-dot(beta,beta));
let rP=aberrate(rRet,n,beta,g);
let b=0.8, cth=rRet[2]/n, cthp_formula=(cth+b)/(1+b*cth);
let cthp_vec=rP[2]/Math.hypot(...rP);
console.log("cos th' vec-formula =", cthp_vec-cthp_formula);
console.log("|r'| - g(n+beta.rRet) =", Math.hypot(...rP)-g*(n+dot(beta,rRet)));

// test 3: Doppler three equivalent forms
let D1=doppler(rRet,n,beta,g);
let D2=1/(g*(1+b*cth));                       // world-frame source dir
let D3=g*(1-b*cthp_vec);                      // observer-frame source dir
let D4=g*(1+b*(-cthp_vec));                   // observer-frame propagation dir (Weiskopf Eq.4 rhs)
console.log("D1,D2,D3,D4 =",D1,D2,D3,D4);

// test 4: solid angle Jacobian dcos(th')/dcos(th) == D^2  (world-frame angle, propagation convention)
let e=1e-7, cA=cth, cB=cth+e;
let f=(x)=>(x+b)/(1+b*x);
console.log("dcosth'/dcosth =",(f(cB)-f(cA))/e, " D^2 =", D1*D1);

// test 5: retarded tick integer for a Pythagorean lattice offset, static vertex
let {t:t5}=retarded([3,4,12],[0,0,0],[0,0,0]);
console.log("t for (3,4,12), |r|=13 ->", t5);
let {t:t6}=retarded([1,1,1],[0,0,0],[0,0,0]);
console.log("t for (1,1,1) ->", t6);

// test 6: OpenRelativity shader quadratic reproduces the same root (c=1 units)
let riw=sub(p,c), C6=-dot(riw,riw), B6=-2*dot(riw,u), D6=1-dot(u,u);
let tisw=(-B6-Math.sqrt(B6*B6-4*D6*C6))/(2*D6);
console.log("shader tisw - t =", tisw-t);
