#import "@preview/cetz:0.3.4"
#import "geometry.typ": primary-color
#import "../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-rule
#let manifold-data=json("manifold-example.json")
#let N=manifold-data.N
#let tau=manifold-data.edge_heat_step.at(0)/manifold-data.edge_heat_step.at(1)
#let rat(v)=v.at(0)/v.at(1)
#let weights(c)=(1/(c+4),2/(c+4),c/(c+4),1/(c+4))
#let modes=((1,0),(0,1),(1,1),(1,-1))
#let index(i,j)=calc.rem(j+N,N)*N+calc.rem(i+N,N)
#let phase(i)=2*calc.pi*i/N
#let value(c,i,j,k:0)={
 let w=weights(c)
 let out=0
 for (l,m) in modes.enumerate() {
  let ev=6-2*calc.cos(phase(m.at(0)))-2*calc.cos(phase(m.at(1)))-2*calc.cos(phase(m.at(0)+m.at(1)))
  out+=w.at(l)*calc.pow(1-tau*ev,k)*calc.cos(phase(m.at(0)*i+m.at(1)*j))
 }
 out
}
#let torus-point(c,i,j,k:0)={
 let t=phase(i);let p=phase(j)
 let r=1+value(c,i,j,k:k)/4
 ((2+r*calc.cos(p))*calc.cos(t),(2+r*calc.cos(p))*calc.sin(t),r*calc.sin(p))
}
#let screen(p)=(p.at(0)-p.at(1),p.at(2)-(p.at(0)+p.at(1))/2)
#let minus(a,b)=array.zip(a,b).map(((x,y))=>x - y)
#let cross(a,b)=(a.at(1)*b.at(2)-a.at(2)*b.at(1),a.at(2)*b.at(0)-a.at(0)*b.at(2),a.at(0)*b.at(1)-a.at(1)*b.at(0))
#let dot(a,b)=array.zip(a,b).map(((x,y))=>x*y).sum()
#let current(c,i,j,dir,k,kind)={
 let d=((1,0),(0,1),(1,1)).at(dir)
 let w=weights(c)
 let j0=value(c,i+d.at(0),j+d.at(1),k:k)-value(c,i,j,k:k)
 if kind!="exact" {j0+=w.at(0)*d.at(0)/N+w.at(1)*d.at(1)/N}
 if kind=="full" {j0+=w.at(2)*rat(manifold-data.kappa_heat.at(k).at(3*index(i,j)+dir))}
 j0
}
#let torus(c:3,k:0,kind:"full",side:90mm,loops:false,difference:none)=cetz.canvas(length:side/9,padding:1/10,{
 import cetz.draw: *
 let vertices=range(N).map(j=>range(N).map(i=>torus-point(if difference==none {c} else {3},i,j,k:k)))
 let pos(i,j)=vertices.at(calc.rem(j+N,N)).at(calc.rem(i+N,N))
 let faces=()
 for j in range(N) {for i in range(N) {
  let a=pos(i,j);let b=pos(i+1,j);let q=pos(i+1,j+1);let d=pos(i,j+1)
  for (pts,g) in (((a,b,q),(N*current(c,i,j,0,k,kind),N*current(c,i+1,j,1,k,kind))),((a,q,d),(N*current(c,i,j+1,0,k,kind),N*current(c,i,j,1,k,kind)))) {
   let normal=cross(minus(pts.at(1),pts.at(0)),minus(pts.at(2),pts.at(0)))
   if dot(normal,(1,1,1)) > 0 {
    faces.push((depth:pts.map(p=>p.sum()).sum()/3,points:pts.map(screen),color:if difference==none {primary-color(..g)} else {rgb("ecebe5")}))
   }
  }
 }}
 for f in faces.sorted(key:f=>f.depth) {
  line(..f.points,close:true,fill:f.color,stroke:(1pt/7)+rgb("49494f"))
 }
 if loops {
  for (axis,color) in ((0,by-blue),(1,by-red)) {
   let points=range(N+1).map(i=>screen(if axis==0 {pos(i,0)} else {pos(0,i)}))
   line(..points,stroke:1pt+color,mark:(end:">"))
  }
 }
 if difference!=none {
  let denom=if difference==2 {42} else {56}
  for j in range(0,N,step:int(N/4)) {for i in range(0,N,step:int(N/4)) {
   let base=pos(i,j)
   let delta=minus(torus-point(difference,i,j),base)
   // Denominator and 8 derive from the exact coefficient difference and its l1 bound.
   let arrow=delta.map(x=>x*denom/(8*(1/4)))
   let endpoint=array.zip(base,arrow).map(((a,b))=>a+b)
   if dot(arrow,arrow) > 0 {
    let sign=value(difference,i,j)-value(3,i,j)
    line(screen(base),screen(endpoint),stroke:1.4pt+(if sign>0 {by-blue} else {by-red}),mark:(end:">"))
   }
  }}
 }
})

#let cube-net(renamed:false)=cetz.canvas(length:6mm,padding:1/5,{
 import cetz.draw: *
 let cube=manifold-data.cube
 let positions=((2,4),(2,0),(2,2),(6,2),(4,2),(0,2))
 for (f,p) in positions.enumerate() {for row in range(2) {for col in range(2) {
  let old=cube.state.s.at(4*f+2*row+col)
  let label=if renamed {cube.rename.at(old)} else {old}
  let x=p.at(0)+col;let y=p.at(1)+1-row
  rect((x,y),(x+9/10,y+9/10),fill:rgb(cube.colors.at(label)),stroke:.4pt+by-black)
  content((x+9/20,y+9/20),text(size:8pt,fill:if label in (0,1) {by-black} else {white})[#cube.letters.at(label)])
 }}}
})

#let root-action()=cetz.canvas(length:15mm,padding:1/5,{
 import cetz.draw: *
 circle((0,0),radius:1,stroke:.6pt+by-rule)
 for k in range(16) {
  let p=(calc.cos(phase(k)),calc.sin(phase(k)))
  circle(p,radius:1/30,fill:by-black,stroke:none)
 }
 for k in (1,5,9,13) {
  let a=(calc.cos(phase(k)),calc.sin(phase(k)))
  let b=(calc.cos(phase(calc.rem(5*k,16))),calc.sin(phase(calc.rem(5*k,16))))
  line(a,b,stroke:.8pt+by-blue,mark:(end:">"))
  content((a.at(0)*7/5,a.at(1)*7/5),text(size:9pt)[#k])
 }
})

#let overlap()=cetz.canvas(length:16mm,padding:1/3,{
 import cetz.draw: *
 let axes=((1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1))
 for (center,color) in ((-1,by-blue),(1,by-red)) {
  let vertices=axes.map(p=>(2*p.at(0)+center,2*p.at(1),2*p.at(2)))
  for a in range(6) {for b in range(a+1,6) {
   if (a,b) not in ((0,1),(2,3),(4,5)) {
    line(screen(vertices.at(a)),screen(vertices.at(b)),stroke:.55pt+color)
   }
  }}
 }
 for (center,color) in ((-1,by-blue),(1,by-red)) {
  for p in ((center,0,1),(2*center,0,0),(center,center,0)) {
   let j=(p.at(0)-center,p.at(1),p.at(2))
   let end=array.zip(p,j).map(((a,b))=>a+b/3)
   line(screen(p),screen(end),stroke:1pt+color,mark:(end:">"))
  }
 }
 let faces=()
 for row in manifold-data.flux {
  let s=row.signs
  let pts=((s.at(0),0,0),(0,s.at(1),0),(0,0,s.at(2)))
  if s.sum() > 0 {faces.push((depth:s.sum()/3,points:pts.map(screen),value:row.difference))}
 }
 for f in faces.sorted(key:f=>f.depth) {
  line(..f.points,close:true,fill:if f.value>0 {rgb("d4e3f4")} else {rgb("f4daca")},stroke:.8pt+by-black)
 }
 // The interior path is dashed where it crosses the solid; the surface path follows its edges.
 line(screen((-1,0,0)),screen((1,0,0)),stroke:(paint:by-black,thickness:1pt,dash:"dashed"),mark:(end:">"))
 line(screen((-1,0,0)),screen((0,1,0)),screen((1,0,0)),stroke:1.5pt+by-yellow,mark:(end:">"))
 content(screen((-1-1/4,0,0)),$P$)
 content(screen((1+1/4,0,0)),$Q$)
 content(screen((0,1+1/4,0)),$R$)
 content(screen((-3,0,0)),text(fill:by-blue)[$V_L$])
 content(screen((3,0,0)),text(fill:by-red)[$V_R$])
})
#let flux-faces()=cetz.canvas(length:13mm,padding:1/4,{
 import cetz.draw: *
 for (k,row) in manifold-data.flux.enumerate() {
  let x=calc.rem(k,4)*3/2;let y=if row.signs.at(0) < 0 {3/2} else {0}
  let v=row.difference
  line((x,y),(x+6/5,y),(x+3/5,y+1),close:true,fill:if v>0 {by-blue.lighten(85%)} else {by-red.lighten(85%)},stroke:.6pt+by-black)
  content((x+3/5,y+2/5),text(size:11pt,weight:"semibold")[#if v>0 [+1] else [−1]])
  content((x+3/5,y - 1/5),text(size:8pt)[#row.signs.map(s=>if s>0 {"+"} else {"−"}).join("")])
 }
})
