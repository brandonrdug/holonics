// Finite chess flux lattice: commuting condensation, shared-square contact law, clique-polynomial
// spectrum, claw-freeness and the backward-heat threshold. Prints a receipt to stdout.
// Run: node lattice_spectrum.js > receipt.json
const fs = require('fs');
eval(fs.readFileSync(__dirname + '/flux_lattice_core.js', 'utf8') + ';global.X={menuList,relationTable,tracePrediction,cliquePolynomial,polyRoots,polyText,buildGraph,moveLabel,START,sharedSquares,contactLaw,applyMove,legalAt,keyOf,genMoves};');
const nm = m => X.moveLabel(m).split('  ')[0];
function heat(c, t){ const n=c.length-1, out=c.slice(); for (let k=0;k<=n;k++){ let v=0; for (let j=0;k+2*j<=n;j++){ let d=1; for (let i=1;i<=2*j;i++) d*=(k+i); v += Math.pow(-t,j)/fact(j)*c[k+2*j]*d; } out[k]=v; } return out; }
function fact(n){ let r=1; for (let i=2;i<=n;i++) r*=i; return r; }
// Durand--Kerner leaves ~1e-5 imaginary parts on repeated real zeros (the triple zero at 1 below); 1e-4 is the reality tolerance
const TOL = 1e-4;
function maxIm(c){ return Math.max(...X.polyRoots(c).map(z=>Math.abs(z[1]))); }
function lambda(c){ if (maxIm(c)<TOL) return 0; let lo=0, hi=1; while (maxIm(heat(c,hi))>TOL){ hi*=2; if (hi>1e6) return null; } for (let i=0;i<60;i++){ const m=(lo+hi)/2; if (maxIm(heat(c,m))>TOL) lo=m; else hi=m; } return hi; }
function hasClaw(n, dep){ for (let c=0;c<n;c++){ const nb=[]; for (let v=0;v<n;v++) if (v!==c&&dep(c,v)) nb.push(v); for (let a=0;a<nb.length;a++) for (let b=a+1;b<nb.length;b++) for (let d=b+1;d<nb.length;d++) if (!dep(nb[a],nb[b])&&!dep(nb[a],nb[d])&&!dep(nb[b],nb[d])) return [c,nb[a],nb[b],nb[d]]; } return null; }
const board = X.START.split('');
const receipt = { grade: 'established-bounded', evidence: ['computational-witness'],
  scope: 'Pseudo-legal chess without castling, en passant or check; fixed root menus of top-k moves plus two enabled moves per side; each generator used at most once; sides alternate; no captures are ever in a menu. Finite statements only.',
  engine: 'flux_lattice_core.js (same engine as the Flux Lattice canvas)', menus: [] };
for (const [kw, kb, depth] of [[4,3,8],[3,3,8],[2,2,8],[5,4,7],[6,5,7]]){
  const lw=X.menuList(board,'w',kw,2), lb=X.menuList(board,'b',kb,2), Rw=X.relationTable(board,'w',lw), Rb=X.relationTable(board,'b',lb);
  const g=X.buildGraph({depth,kw,kb,cap:20000,strict:true}); const shared=X.sharedSquares(lw,lb);
  const side=(list,R,name)=>{ const dep=(i,j)=>R[i][j].kind!=='commute'; const c=X.cliquePolynomial(list.length,(i,j)=>!dep(i,j)); const roots=X.polyRoots(c); const claw=hasClaw(list.length,dep);
    const kinds={}; for (let i=0;i<list.length;i++) for (let j=i+1;j<list.length;j++) kinds[R[i][j].kind]=(kinds[R[i][j].kind]||0)+1;
    return { side:name, generators:list.map(m=>nm(m)+(m.afters?' [after '+m.afters.map(nm).join(' or ')+']':'')), pairs:kinds, cliquePolynomial:X.polyText(c,'z'), coefficients:c, zeros:roots.map(z=>[+z[0].toFixed(6),+z[1].toFixed(6)]), allZerosReal: roots.every(z=>Math.abs(z[1])<TOL), dependenceGraphClawFree: !claw, claw: claw?claw.map(i=>nm(list[i])):null, backwardHeatThreshold: lambda(c) }; };
  const plies=[]; for (let p=0;p<=depth;p++){ const w=Math.ceil(p/2), b=Math.floor(p/2); const pw=X.tracePrediction(lw,Rw,w), pb=X.tracePrediction(lb,Rb,b); const layer=g.plies[p]||[]; let seq=0, prime=0, h=0; layer.forEach(n=>{ seq+=n.paths; if (n.paths===1) prime++; h+=Math.log2(n.paths); });
    plies.push({ ply:p, sequences:seq, pairwiseSequences:pw.sequences*pb.sequences, pairwiseBoards:pw.boards*pb.boards, boards:layer.length, contact:pw.boards*pb.boards-layer.length, sharedSquareLaw:X.contactLaw(lw,Rw,lb,Rb,shared,w,b), uniquePathBoards:prime, meanLog2Paths:layer.length?+(h/layer.length).toFixed(3):0 }); }
  receipt.menus.push({ white:kw, black:kb, depth, nodes:g.nodes.length, capped:g.capped, sharedSquares:shared.map(s=>s.square), sides:[side(lw,Rw,'white'),side(lb,Rb,'black')], plies, lawExactAtEveryPly: plies.every(r=>r.contact===r.sharedSquareLaw) });
}
receipt.realityTolerance = TOL;
receipt.summary = { lawExactEverywhere: receipt.menus.every(m=>m.lawExactAtEveryPly), allMenusClawFree: receipt.menus.every(m=>m.sides.every(s=>s.dependenceGraphClawFree)), allZerosRealEverywhere: receipt.menus.every(m=>m.sides.every(s=>s.allZerosReal)), thresholds: receipt.menus.map(m=>m.sides.map(s=>s.backwardHeatThreshold)) };
console.log(JSON.stringify(receipt, null, 2));
