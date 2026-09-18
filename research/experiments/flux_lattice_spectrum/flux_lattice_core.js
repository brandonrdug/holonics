// ===== Flux lattice core: chess generators as lattice vectors, causal graph, 3D projection =====
var START = 'rnbqkbnrpppppppp' + '................................' + 'PPPPPPPPRNBQKBNR';
var FILES = 'abcdefgh';
var RAYS4D = [[1,1],[1,-1],[-1,1],[-1,-1]];
var RAYS4A = [[1,0],[-1,0],[0,1],[0,-1]];
var RAYS8 = RAYS4D.concat(RAYS4A);
var KNIGHT = [[1,2],[2,1],[-1,2],[-2,1],[1,-2],[2,-1],[-1,-2],[-2,-1]];
var GEN = { N:{jumps:KNIGHT}, B:{rays:RAYS4D}, R:{rays:RAYS4A}, Q:{rays:RAYS8}, K:{jumps:RAYS8}, P:{} };
var VALUE = { P:1, N:3, B:3, R:5, Q:9, K:40 };
function isWhite(p){ return p >= 'A' && p <= 'Z'; }
function sq(i){ return FILES[i%8] + (8 - Math.floor(i/8)); }
function vec(m){ var c1=m.from%8, r1=Math.floor(m.from/8), c2=m.to%8, r2=Math.floor(m.to/8); return [c2-c1, r1-r2]; }

function genMoves(board, side){
  var w = side === 'w', moves = [];
  for (var i=0;i<64;i++){
    var p = board[i]; if (p === '.' || isWhite(p) !== w) continue;
    var t = p.toUpperCase(), c = i%8, r = (i-c)/8;
    var push = function(c2,r2){
      if (c2<0||c2>7||r2<0||r2>7) return false;
      var j=r2*8+c2, q=board[j];
      if (q==='.'){ moves.push({from:i,to:j,piece:p,cap:''}); return true; }
      if (isWhite(q)!==w) moves.push({from:i,to:j,piece:p,cap:q});
      return false;
    };
    if (t==='P'){
      var dir = w?-1:1, start = w?6:1, r1=r+dir;
      if (r1>=0&&r1<8&&board[r1*8+c]==='.'){
        moves.push({from:i,to:r1*8+c,piece:p,cap:''});
        if (r===start && board[(r+2*dir)*8+c]==='.') moves.push({from:i,to:(r+2*dir)*8+c,piece:p,cap:''});
      }
      for (var k=0;k<2;k++){ var c2=c+(k?1:-1); if (c2<0||c2>7||r1<0||r1>7) continue; var q=board[r1*8+c2]; if (q!=='.'&&isWhite(q)!==w) moves.push({from:i,to:r1*8+c2,piece:p,cap:q}); }
    } else if (GEN[t].rays){
      for (var a=0;a<GEN[t].rays.length;a++){ var d=GEN[t].rays[a], cc=c+d[0], rr=r+d[1]; while(push(cc,rr)){cc+=d[0];rr+=d[1];} }
    } else {
      for (var b=0;b<GEN[t].jumps.length;b++){ var e=GEN[t].jumps[b]; push(c+e[0], r+e[1]); }
    }
  }
  return moves;
}
// reach count per square for one side: every square a generator can carry a piece to (rays stop at first occupant, inclusive)
function reach(board, side){
  var w = side==='w', cnt = new Array(64); for (var i=0;i<64;i++) cnt[i]=0;
  for (var i=0;i<64;i++){
    var p=board[i]; if (p==='.'||isWhite(p)!==w) continue;
    var t=p.toUpperCase(), c=i%8, r=(i-c)/8;
    var mark=function(c2,r2){ if(c2<0||c2>7||r2<0||r2>7) return false; var j=r2*8+c2; cnt[j]++; return board[j]==='.'; };
    if (t==='P'){ var r1=r+(w?-1:1); mark(c-1,r1); mark(c+1,r1); }
    else if (GEN[t].rays){ for (var a=0;a<GEN[t].rays.length;a++){ var d=GEN[t].rays[a], cc=c+d[0], rr=r+d[1]; while(mark(cc,rr)){cc+=d[0];rr+=d[1];} } }
    else { for (var b=0;b<GEN[t].jumps.length;b++){ var e=GEN[t].jumps[b]; mark(c+e[0], r+e[1]); } }
  }
  return cnt;
}
function applyMove(board, m){
  var nb = board.slice(); nb[m.to] = nb[m.from]; nb[m.from]='.';
  var p = nb[m.to]; if (p==='P' && m.to<8) nb[m.to]='Q'; if (p==='p' && m.to>=56) nb[m.to]='q';
  return nb;
}
function keyOf(board, side){ return board.join('') + side; }
function score(m, board){
  var t=m.piece.toUpperCase(), c=m.to%8, r=Math.floor(m.to/8), fr=Math.floor(m.from/8);
  var cen = 3 - Math.max(Math.abs(c-3.5), Math.abs(r-3.5)) + 0.5;
  var s = cen;
  if ((t==='N'||t==='B') && (fr===0||fr===7)) s += 2.2;
  if (t==='P'){ if (c===3||c===4) s += 1.2; if (Math.abs(fr-r)===2) s += 0.4; }
  if (t==='Q') s -= 1.5; if (t==='K') s -= 4; if (t==='R') s -= 1;
  if (m.cap) s += VALUE[m.cap.toUpperCase()] * 0.6;
  return s;
}
function topK(board, side, k){
  var ms = genMoves(board, side).map(function(m,i){ return {m:m, s:score(m,board), i:i}; });
  ms.sort(function(a,b){ return b.s - a.s || a.i - b.i; });
  var out=[], pieces={};
  for (var i=0;i<ms.length && out.length<k;i++){ var f=ms[i].m.from; if (pieces[f] && out.length < k-1 && i < ms.length-1) continue; pieces[f]=1; out.push(ms[i].m); }
  return out;
}
function sameMove(a, b){ return a && b && a.from===b.from && a.to===b.to; }
function menuList(board, side, k, enabled){
  var seen = {}, list = [];
  var add = function(m){ var id=m.from+'-'+m.to; if(!seen[id]){ seen[id]=1; list.push(m); return true; } return false; };
  var first = topK(board, side, k); first.forEach(add);
  var added = 0;
  for (var i=0;i<first.length && added<enabled;i++){
    var nb = applyMove(board, first[i]);
    var nxt = topK(nb, side, k+2);
    for (var j=0;j<nxt.length && added<enabled;j++){ var mv = nxt[j]; if (add(mv)){ added++; if (!legalAt(board, side, mv)) mv.afters = []; } }
  }
  // every first move that opens a gated move is one of its enablers
  list.forEach(function(mv){ if (!mv.afters) return; first.forEach(function(f){ if (legalAt(applyMove(board, f), side, mv) && !mv.afters.some(function(e){ return sameMove(e, f); })) mv.afters.push(f); }); });
  return list;
}
function menuFor(board, side, k, enabled){
  var menu = {}; menuList(board, side, k, enabled).forEach(function(m){ menu[m.from+'-'+m.to] = 1; }); return menu;
}
// Build the causal lattice: nodes are boards, edges are moves; equal boards reached by different sequences merge.
function buildGraph(o){
  var depth=o.depth||4, kw=o.kw||4, kb=o.kb||3, cap=o.cap||520;
  var root = {id:0, board:START.split(''), side:'w', ply:0, key:keyOf(START.split(''),'w'), parents:[], children:[], paths:1, moveIn:null};
  var nodes=[root], byKey={}; byKey[root.key]=root;
  var wMenu = menuFor(root.board,'w',kw,2), bMenu = menuFor(root.board,'b',kb,2);
  var frontier=[root];
  for (var p=0;p<depth;p++){
    var next=[], nextKey={};
    for (var n=0;n<frontier.length;n++){
      var node=frontier[n], menu = node.side==='w'?wMenu:bMenu;
      var legal = genMoves(node.board,node.side);
      var cands = legal.filter(function(m){ return menu[m.from+'-'+m.to]; });
      if (!cands.length && !o.strict) cands = topK(node.board,node.side,2);
      for (var c=0;c<cands.length;c++){
        var m=cands[c], nb=applyMove(node.board,m), side=node.side==='w'?'b':'w', key=keyOf(nb,side);
        var child = nextKey[key];
        if (!child){
          if (nodes.length>=cap) continue;
          child = {id:nodes.length, board:nb, side:side, ply:p+1, key:key, parents:[], children:[], paths:0, moveIn:m};
          nodes.push(child); nextKey[key]=child; next.push(child);
        }
        child.parents.push({node:node, move:m}); child.paths += node.paths;
        node.children.push({node:child, move:m});
      }
    }
    frontier = next;
  }
  nodes.forEach(function(nd){
    nd.moves = genMoves(nd.board, nd.side);
    nd.rw = reach(nd.board,'w'); nd.rb = reach(nd.board,'b');
    var x=0; for (var i=0;i<64;i++) if (nd.rw[i]&&nd.rb[i]) x++; nd.cross = x;
    nd.H = nd.moves.length ? Math.log(nd.moves.length)/Math.LN2 : 0;
  });
  var plies=[]; nodes.forEach(function(nd){ (plies[nd.ply]=plies[nd.ply]||[]).push(nd); });
  for (var q=0;q<=depth;q++) plies[q]=plies[q]||[];
  var actual=depth; while (actual>0 && plies[actual].length===0) actual--;
  return {nodes:nodes, plies:plies, root:root, depth:actual, requested:depth, capped:nodes.length>=cap};
}
function legalAt(board, side, m){ return genMoves(board, side).some(function(q){ return q.from===m.from&&q.to===m.to; }); }
// Commutator of two same-side moves: g -(a)-> p1 -(x)-> p2 -(b)-> node versus g -(b)-> -(x)-> -(a)->

function findChild(node, m){ for (var i=0;i<node.children.length;i++){ var e=node.children[i]; if (e.move.from===m.from&&e.move.to===m.to) return e.node; } return null; }
function commutator(node){
  if (node.ply<3) return null;
  var P2=node.parents[0], p2=P2.node, b=P2.move;
  var P1=p2.parents[0], p1=P1.node, x=P1.move;
  var G=p1.parents[0], g=G.node, a=G.move;
  var out={a:a,x:x,b:b,g:g,p1:p1,p2:p2,alt:[g]};
  if (!legalAt(g.board,g.side,b)){ out.commutes=false; out.reason='gated: '+sq(b.from)+'→'+sq(b.to)+' is unavailable before '+sq(a.from)+'→'+sq(a.to); return out; }
  var s1=g.side==='w'?'b':'w', b1=applyMove(g.board,b); var n1=findChild(g,b); if(n1) out.alt.push(n1);
  if (!legalAt(b1,s1,x)){ out.commutes=false; out.reason='reply '+sq(x.from)+'→'+sq(x.to)+' is blocked in the swapped order'; return out; }
  var b2=applyMove(b1,x); var n2=n1?findChild(n1,x):null; if(n2) out.alt.push(n2);
  if (!legalAt(b2,g.side,a)){ out.commutes=false; out.reason='gated: '+sq(a.from)+'→'+sq(a.to)+' is blocked after '+sq(b.from)+'→'+sq(b.to); return out; }
  var b3=applyMove(b2,a); var n3=n2?findChild(n2,a):null; if(n3) out.alt.push(n3);
  out.commutes = keyOf(b3,node.side)===node.key;
  out.reason = out.commutes ? 'both orders reach this same board' : 'both orders exist but reach different boards';
  return out;
}
// Prediction cone over k plies: sequences vs distinct boards reached
function cone(node, k, cap){
  var seqs=0, distinct=0, keys={}, capHit=false;
  var rec=function(board, side, d){
    if (d===0){ seqs++; var kk=keyOf(board,side); if(!keys[kk]){keys[kk]=1;distinct++;} return; }
    if (seqs>=cap){ capHit=true; return; }
    var ms=genMoves(board,side), s2=side==='w'?'b':'w';
    for (var i=0;i<ms.length;i++){ if (seqs>=cap){capHit=true;return;} rec(applyMove(board,ms[i]), s2, d-1); }
  };
  rec(node.board,node.side,k);
  return {sequences:seqs, boards:distinct, capHit:capHit};
}
// ---- layout: ply along +y, lineage angle, radius by ply, precession twist ----
function layoutGraph(g, twist, rstep, ystep){
  var root=g.root; root.theta=0; root.rho=0; root.pos=[0,0,0];
  for (var p=1;p<g.plies.length;p++){
    var layer=g.plies[p];
    layer.forEach(function(nd){
      var sx=0, sy=0, rr=0;
      nd.parents.forEach(function(pr){
        var par=pr.node, sibs=par.children, m=sibs.length, j=0;
        for (var i=0;i<m;i++) if (sibs[i].node===nd){ j=i; break; }
        var sector = par.sector!==undefined ? par.sector : Math.PI*2;
        var th = par.theta + (j-(m-1)/2) * (sector/m);
        sx+=Math.cos(th); sy+=Math.sin(th); rr += par.rho;
      });
      var n=nd.parents.length;
      nd.theta = Math.atan2(sy/n, sx/n); nd.rho = rr/n + rstep;
      var par0=nd.parents[0].node; nd.sector = (par0.sector!==undefined?par0.sector:Math.PI*2)/Math.max(1,par0.children.length);
    });
    layer.forEach(function(nd){ var th = nd.theta + twist*p; nd.pos=[nd.rho*Math.cos(th), p*ystep, nd.rho*Math.sin(th)]; });
  }
}
// ---- camera / projection ----
function makeCam(){ return {yaw:0.7, pitch:0.62, dist:15, target:[0,2.6,0], fov:0.95}; }
function project(cam, p, w, h){
  var x=p[0]-cam.target[0], y=p[1]-cam.target[1], z=p[2]-cam.target[2];
  var cy=Math.cos(cam.yaw), sy=Math.sin(cam.yaw), x1=x*cy-z*sy, z1=x*sy+z*cy;
  var cp=Math.cos(cam.pitch), sp=Math.sin(cam.pitch), y2=y*cp-z1*sp, z2=y*sp+z1*cp;
  var d=z2+cam.dist; if (d<0.2) return null;
  var f=(h/2)/Math.tan(cam.fov/2);
  return [w/2 + x1*f/d, h/2 - y2*f/d, d, f/d];
}
function attachOrbit(canvas, cam, onChange){
  var drag=null;
  canvas.addEventListener('mousedown', function(e){ drag={x:e.clientX,y:e.clientY,yaw:cam.yaw,pitch:cam.pitch,moved:false}; });
  window.addEventListener('mousemove', function(e){ if(!drag) return; var dx=e.clientX-drag.x, dy=e.clientY-drag.y; if (Math.abs(dx)+Math.abs(dy)>3) drag.moved=true; cam.yaw=drag.yaw+dx*0.006; cam.pitch=Math.max(-1.4,Math.min(1.5,drag.pitch+dy*0.006)); if(onChange) onChange('orbit'); });
  window.addEventListener('mouseup', function(){ drag=null; });
  canvas.addEventListener('wheel', function(e){ e.preventDefault(); cam.dist=Math.max(4,Math.min(40,cam.dist*(1+e.deltaY*0.0012))); if(onChange) onChange('zoom'); }, {passive:false});
  var touch=null;
  canvas.addEventListener('touchstart', function(e){ if(e.touches.length===1){ var t=e.touches[0]; touch={x:t.clientX,y:t.clientY,yaw:cam.yaw,pitch:cam.pitch}; } }, {passive:true});
  canvas.addEventListener('touchmove', function(e){ if(touch&&e.touches.length===1){ var t=e.touches[0]; cam.yaw=touch.yaw+(t.clientX-touch.x)*0.006; cam.pitch=Math.max(-1.4,Math.min(1.5,touch.pitch+(t.clientY-touch.y)*0.006)); } }, {passive:true});
  canvas.addEventListener('touchend', function(){ touch=null; });
  return function(){ return drag && drag.moved; };
}
function hexA(hex, a){ var n=parseInt(hex.slice(1),16); return 'rgba('+(n>>16&255)+','+(n>>8&255)+','+(n&255)+','+a+')'; }
// glyph of a generator on a 2D canvas: vectors, never a piece icon
function drawGlyph(ctx, t, cx, cy, s, color){
  ctx.save(); ctx.strokeStyle=color; ctx.fillStyle=color; ctx.lineWidth=Math.max(1,s*0.09); ctx.lineCap='round';
  var L=s*0.42;
  var ray=function(dx,dy){ ctx.beginPath(); ctx.moveTo(cx,cy); ctx.lineTo(cx+dx*L,cy-dy*L); ctx.stroke(); };
  if (t==='R'){ RAYS4A.forEach(function(d){ray(d[0],d[1]);}); }
  else if (t==='B'){ RAYS4D.forEach(function(d){ray(d[0],d[1]);}); }
  else if (t==='Q'){ RAYS8.forEach(function(d){ray(d[0],d[1]);}); }
  else if (t==='K'){ ctx.beginPath(); ctx.rect(cx-L*0.6,cy-L*0.6,L*1.2,L*1.2); ctx.stroke(); ctx.beginPath(); ctx.arc(cx,cy,s*0.08,0,6.283); ctx.fill(); }
  else if (t==='N'){ KNIGHT.forEach(function(d){ ctx.beginPath(); ctx.arc(cx+d[0]*L*0.5, cy-d[1]*L*0.5, s*0.07,0,6.283); ctx.fill(); }); ctx.beginPath(); ctx.arc(cx,cy,s*0.1,0,6.283); ctx.fill(); }
  else if (t==='P'){ ctx.beginPath(); ctx.moveTo(cx,cy+L*0.5); ctx.lineTo(cx,cy-L*0.5); ctx.stroke(); ctx.beginPath(); ctx.moveTo(cx-L*0.3,cy-L*0.2); ctx.lineTo(cx,cy-L*0.55); ctx.lineTo(cx+L*0.3,cy-L*0.2); ctx.stroke(); }
  ctx.restore();
}
// full 2D board with flux and generator glyphs
function drawBoard2D(ctx, node, size, colors, lastMove){
  var s=size/8; ctx.clearRect(0,0,size,size);
  for (var i=0;i<64;i++){ var c=i%8, r=Math.floor(i/8); ctx.fillStyle=((c+r)%2)?colors.dark:colors.light; ctx.fillRect(c*s,r*s,s,s); }
  for (var i=0;i<64;i++){ var c=i%8, r=Math.floor(i/8), w=node.rw[i], b=node.rb[i];
    if (w&&b){ ctx.fillStyle=hexA(colors.cross,0.22+0.1*Math.min(3,w+b)); ctx.fillRect(c*s,r*s,s,s); ctx.strokeStyle=hexA(colors.cross,0.9); ctx.lineWidth=1; ctx.beginPath(); ctx.moveTo(c*s+s*0.3,r*s+s*0.3); ctx.lineTo(c*s+s*0.7,r*s+s*0.7); ctx.moveTo(c*s+s*0.7,r*s+s*0.3); ctx.lineTo(c*s+s*0.3,r*s+s*0.7); ctx.stroke(); }
    else if (w){ ctx.fillStyle=hexA(colors.white,0.14+0.12*Math.min(3,w)); ctx.fillRect(c*s,r*s,s,s); }
    else if (b){ ctx.fillStyle=hexA(colors.black,0.14+0.12*Math.min(3,b)); ctx.fillRect(c*s,r*s,s,s); }
  }
  ctx.strokeStyle=colors.grid; ctx.lineWidth=1; ctx.beginPath();
  for (var k=0;k<=8;k++){ ctx.moveTo(k*s+0.5,0); ctx.lineTo(k*s+0.5,size); ctx.moveTo(0,k*s+0.5); ctx.lineTo(size,k*s+0.5); } ctx.stroke();
  if (lastMove){ var c1=lastMove.from%8, r1=Math.floor(lastMove.from/8), c2=lastMove.to%8, r2=Math.floor(lastMove.to/8);
    var col = isWhite(lastMove.piece)?colors.white:colors.black;
    ctx.strokeStyle=hexA(col,0.95); ctx.lineWidth=3; ctx.lineCap='round'; ctx.beginPath(); ctx.moveTo(c1*s+s/2,r1*s+s/2); ctx.lineTo(c2*s+s/2,r2*s+s/2); ctx.stroke();
    ctx.fillStyle=hexA(col,0.95); ctx.beginPath(); ctx.arc(c2*s+s/2,r2*s+s/2,s*0.12,0,6.283); ctx.fill(); }
  for (var i=0;i<64;i++){ var p=node.board[i]; if (p==='.') continue; var c=i%8, r=Math.floor(i/8);
    drawGlyph(ctx, p.toUpperCase(), c*s+s/2, r*s+s/2, s, isWhite(p)?colors.white:colors.black); }
}
// draw a flat 8x8 board in 3D (grid + occupancy dots [+ flux quads])
function drawBoard3D(ctx, cam, node, size, w, h, colors, showFlux, alpha){
  var c=node.pos, hs=size/2, pts=[], ok=true;
  var P=function(x,z){ var q=project(cam,[c[0]+x,c[1],c[2]+z],w,h); if(!q) ok=false; return q; };
  var g=[]; for (var k=0;k<=8;k++){ var t=-hs+k*size/8; g.push([P(t,-hs),P(t,hs),P(-hs,t),P(hs,t)]); }
  if (!ok) return;
  if (showFlux){
    for (var i=0;i<64;i++){ var cc=i%8, rr=Math.floor(i/8), wv=node.rw[i], bv=node.rb[i]; if(!wv&&!bv) continue;
      var x0=-hs+cc*size/8, z0=-hs+rr*size/8, a=P(x0,z0), b=P(x0+size/8,z0), d=P(x0+size/8,z0+size/8), e=P(x0,z0+size/8); if(!a||!b||!d||!e) continue;
      ctx.fillStyle = (wv&&bv)?hexA(colors.cross,0.55*alpha):wv?hexA(colors.white,0.3*alpha):hexA(colors.black,0.3*alpha);
      ctx.beginPath(); ctx.moveTo(a[0],a[1]); ctx.lineTo(b[0],b[1]); ctx.lineTo(d[0],d[1]); ctx.lineTo(e[0],e[1]); ctx.closePath(); ctx.fill(); }
  } else {
    var a=g[0][0], b=g[8][0], d=g[8][1], e=g[0][1];
    ctx.fillStyle=hexA(colors.face, 0.55*alpha); ctx.beginPath(); ctx.moveTo(a[0],a[1]); ctx.lineTo(b[0],b[1]); ctx.lineTo(d[0],d[1]); ctx.lineTo(e[0],e[1]); ctx.closePath(); ctx.fill();
  }
  ctx.strokeStyle=hexA(colors.gridHex, (showFlux?0.5:0.28)*alpha); ctx.lineWidth=1; ctx.beginPath();
  for (var k=0;k<=8;k++){ var q=g[k]; ctx.moveTo(q[0][0],q[0][1]); ctx.lineTo(q[1][0],q[1][1]); ctx.moveTo(q[2][0],q[2][1]); ctx.lineTo(q[3][0],q[3][1]); } ctx.stroke();
  var dot = Math.max(1.2, g[0][0][3]*size*0.05);
  if (g[0][0][3]*size < 7) return;
  for (var i=0;i<64;i++){ var p=node.board[i]; if (p==='.') continue; var cc=i%8, rr=Math.floor(i/8);
    var q=P(-hs+(cc+0.5)*size/8, -hs+(rr+0.5)*size/8); if(!q) continue;
    ctx.fillStyle=hexA(isWhite(p)?colors.white:colors.black, 0.95*alpha); ctx.fillRect(q[0]-dot/2,q[1]-dot/2,dot,dot); }
}
function moveLabel(m){ var v=vec(m); return m.piece.toUpperCase()+' '+sq(m.from)+'→'+sq(m.to)+'  ('+(v[0]>=0?'+':'')+v[0]+', '+(v[1]>=0?'+':'')+v[1]+')'+(m.cap?' ×':''); }

// run fn at ~30fps while the canvas is on screen and the document is visible
function runLoop(canvas, fn){
  var visible = true, last = 0, raf = 0;
  if (typeof IntersectionObserver === 'function' && canvas){
    try { new IntersectionObserver(function(es){ visible = es[0] ? es[0].isIntersecting : true; }).observe(canvas); } catch (e) {}
  }
  var tick = function(t){ raf = requestAnimationFrame(tick); if (!visible || document.hidden) return; if (t - last < 30) return; last = t; fn(); };
  raf = requestAnimationFrame(tick);
  return function(){ cancelAnimationFrame(raf); };
}

// ---- spectrum: pairwise relations, clique polynomial, roots, once-only trace prediction ----
// Relation of two same-side moves at a board (the opponent passes): commute / gated / exclusive / divergent
function pairRelation(board, side, a, b){
  var la = legalAt(board, side, a), lb = legalAt(board, side, b);
  var ab = la && legalAt(applyMove(board, a), side, b);
  var ba = lb && legalAt(applyMove(board, b), side, a);
  if (ab && ba){
    var same = keyOf(applyMove(applyMove(board, a), b), side) === keyOf(applyMove(applyMove(board, b), a), side);
    return { kind: same ? 'commute' : 'divergent' };
  }
  if (ab) return { kind: 'gated', first: a, second: b };
  if (ba) return { kind: 'gated', first: b, second: a };
  return { kind: 'exclusive' };
}
// Evaluate each pair after the enablers both moves need (an enabler that is the partner stays a gate)
function relationTable(board, side, list){
  var n = list.length, R = [];
  for (var i=0;i<n;i++){ R.push([]); for (var j=0;j<n;j++) R[i].push(null); }
  for (var i=0;i<n;i++) for (var j=i+1;j<n;j++){
    var a=list[i], b=list[j], ctx=board, done=[];
    [a, b].forEach(function(mv){ var other = mv===a ? b : a; if (!mv.afters) return; if (mv.afters.some(function(e){ return sameMove(e, other); })) return; var e = mv.afters[0]; if (done.some(function(d){ return sameMove(d,e); })) return; if (legalAt(ctx, side, e)){ ctx = applyMove(ctx, e); done.push(e); } });
    var r = pairRelation(ctx, side, a, b); R[i][j]=r; R[j][i]=r;
  }
  return R;
}
// Cartier--Foata: P(z) = sum over cliques of the commutation graph of (-1)^|C| z^|C|
function cliquePolynomial(n, commutes){
  var c = []; for (var k=0;k<=n;k++) c.push(0);
  for (var mask=0; mask<(1<<n); mask++){
    var bits=[]; for (var i=0;i<n;i++) if (mask>>i&1) bits.push(i);
    var ok=true; for (var x=0;x<bits.length&&ok;x++) for (var y=x+1;y<bits.length;y++) if (!commutes(bits[x],bits[y])){ ok=false; break; }
    if (ok) c[bits.length] += (bits.length%2 ? -1 : 1);
  }
  return c;
}
function polyRoots(c){
  var d = c.length-1; while (d>0 && c[d]===0) d--; if (d<=0) return [];
  var a = []; for (var k=0;k<=d;k++) a.push(c[k]/c[d]);
  var roots = []; for (var i=0;i<d;i++){ var ang = 2*Math.PI*i/d + 0.37; roots.push([0.6*Math.cos(ang), 0.6*Math.sin(ang)]); }
  var evalP = function(z){ var re=0, im=0; for (var k=d;k>=0;k--){ var nre=re*z[0]-im*z[1]+a[k], nim=re*z[1]+im*z[0]; re=nre; im=nim; } return [re,im]; };
  for (var it=0; it<500; it++){
    var maxd=0;
    for (var i=0;i<d;i++){
      var num=evalP(roots[i]), den=[1,0];
      for (var j=0;j<d;j++){ if (j===i) continue; var dz=[roots[i][0]-roots[j][0], roots[i][1]-roots[j][1]]; den=[den[0]*dz[0]-den[1]*dz[1], den[0]*dz[1]+den[1]*dz[0]]; }
      var dd=den[0]*den[0]+den[1]*den[1]; if (dd<1e-30) continue;
      var q=[(num[0]*den[0]+num[1]*den[1])/dd, (num[1]*den[0]-num[0]*den[1])/dd];
      roots[i]=[roots[i][0]-q[0], roots[i][1]-q[1]]; maxd=Math.max(maxd, Math.hypot(q[0],q[1]));
    }
    if (maxd<1e-13) break;
  }
  return roots;
}
function polyText(c, v){
  var parts=[]; for (var k=0;k<c.length;k++){ if (c[k]===0) continue; var mag=Math.abs(c[k]); var term = k===0 ? String(mag) : ((mag===1?'':mag)+v+(k>1?'^'+k:'')); parts.push((c[k]<0?'\u2212 ':(parts.length?'+ ':''))+term); }
  return parts.join(' ');
}
function combos(n, m){ var out=[]; var rec=function(start, cur){ if (cur.length===m){ out.push(cur.slice()); return; } for (var i=start;i<n;i++){ cur.push(i); rec(i+1,cur); cur.pop(); } }; rec(0,[]); return out; }
function permutations(S){ var out=[]; var rec=function(rest, cur){ if (!rest.length){ out.push(cur.slice()); return; } for (var i=0;i<rest.length;i++){ var nr=rest.slice(); var x=nr.splice(i,1)[0]; cur.push(x); rec(nr,cur); cur.pop(); } }; rec(S,[]); return out; }
// Once-only prediction from the pairwise relation alone: admissible orderings, merged along commuting adjacent swaps
function tracePrediction(list, R, m){
  var n = list.length, seqs = 0, boards = 0;
  if (m > n) return { sequences: 0, boards: 0 };
  var admissible = function(p){
    for (var i=0;i<p.length;i++){ var es=list[p[i]].afters; if (es){ var ok=false; for (var h=0;h<i;h++) if (es.some(function(e){ return sameMove(list[p[h]], e); })) ok=true; if (!ok) return false; } }
    for (var i=0;i<p.length;i++) for (var j=i+1;j<p.length;j++){ var r=R[p[i]][p[j]]; if (r.kind==='exclusive') return false; if (r.kind==='gated' && r.first!==list[p[i]]) return false; } return true; };
  combos(n, m).forEach(function(S){
    var keys=[], adm={};
    permutations(S).forEach(function(p){ if (admissible(p)){ adm[p.join(',')]=1; keys.push(p); } });
    seqs += keys.length;
    var parent={}; keys.forEach(function(p){ parent[p.join(',')]=p.join(','); });
    var find=function(x){ while (parent[x]!==x){ parent[x]=parent[parent[x]]; x=parent[x]; } return x; };
    keys.forEach(function(p){ for (var i=0;i<p.length-1;i++){ if (R[p[i]][p[i+1]].kind==='commute'){ var q=p.slice(); var t=q[i]; q[i]=q[i+1]; q[i+1]=t; var kq=q.join(','); if (adm[kq]){ var a=find(p.join(',')), b=find(kq); if (a!==b) parent[a]=b; } } } });
    var seen={}; keys.forEach(function(p){ seen[find(p.join(','))]=1; }); boards += Object.keys(seen).length;
  });
  return { sequences: seqs, boards: boards };
}
function choose(n, k){ if (k<0||k>n) return 0; var r=1; for (var i=1;i<=k;i++) r=r*(n-k+i)/i; return Math.round(r); }

function tracesContaining(list, R, m, required){
  var n = list.length, boards = 0;
  if (m > n) return 0;
  var admissible = function(p){
    for (var i=0;i<p.length;i++){ var es=list[p[i]].afters; if (es){ var ok=false; for (var h=0;h<i;h++) if (es.some(function(e){ return sameMove(list[p[h]], e); })) ok=true; if (!ok) return false; } }
    for (var i=0;i<p.length;i++) for (var j=i+1;j<p.length;j++){ var r=R[p[i]][p[j]]; if (r.kind==='exclusive') return false; if (r.kind==='gated' && r.first!==list[p[i]]) return false; } return true; };
  combos(n, m).forEach(function(S){
    if (required.some(function(q){ return S.indexOf(q) < 0; })) return;
    var keys=[], adm={};
    permutations(S).forEach(function(p){ if (admissible(p)){ adm[p.join(',')]=1; keys.push(p); } });
    var parent={}; keys.forEach(function(p){ parent[p.join(',')]=p.join(','); });
    var find=function(x){ while (parent[x]!==x){ parent[x]=parent[parent[x]]; x=parent[x]; } return x; };
    keys.forEach(function(p){ for (var i=0;i<p.length-1;i++){ if (R[p[i]][p[i+1]].kind==='commute'){ var q=p.slice(); var t=q[i]; q[i]=q[i+1]; q[i+1]=t; var kq=q.join(','); if (adm[kq]){ var a=find(p.join(',')), b=find(kq); if (a!==b) parent[a]=b; } } } });
    var seen={}; keys.forEach(function(p){ seen[find(p.join(','))]=1; }); boards += Object.keys(seen).length;
  });
  return boards;
}
// Squares both menus move into; each is a contact: the two traces cannot both use it
function sharedSquares(lw, lb){
  var out = [];
  lw.forEach(function(a, i){ lb.forEach(function(b, j){ if (a.to === b.to) out.push({ square: sq(a.to), wi: i, bi: j }); }); });
  return out;
}
// Inclusion-exclusion over the shared squares: pairs of traces that are jointly infeasible
function contactLaw(lw, Rw, lb, Rb, shared, w, b){
  var total = 0, k = shared.length;
  for (var mask = 1; mask < (1 << k); mask++){
    var W = [], B = [], bits = 0;
    for (var i=0;i<k;i++) if (mask >> i & 1){ bits++; W.push(shared[i].wi); B.push(shared[i].bi); }
    var term = tracesContaining(lw, Rw, w, W) * tracesContaining(lb, Rb, b, B);
    total += (bits % 2 ? 1 : -1) * term;
  }
  return total;
}
