#import "@preview/cetz:0.3.4"
#import "geometry.typ": primary-color
#import "../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-rule
#let law-data=json("law-geometry.json")
#let rat(x)=if type(x)==array {x.at(0)/x.at(1)} else {x}
#let sub(a,b)=array.zip(a,b).map(((x,y))=>x - y)
#let cross(a,b)=(a.at(1)*b.at(2)-a.at(2)*b.at(1),a.at(2)*b.at(0)-a.at(0)*b.at(2),a.at(0)*b.at(1)-a.at(1)*b.at(0))
#let screen(p)=(p.at(0)-p.at(1)*3/5,p.at(2)+(p.at(0)+p.at(1))/3)
#let motion(p,t)=(p.at(0)+t*p.at(2),p.at(1),p.at(2))
#let linked-bodies(t:0,side:82mm)=cetz.canvas(length:side/8,padding:1/8,{
 import cetz.draw: *
 let faces=()
 for mesh in (law-data.link.mesh_a,law-data.link.mesh_b) {
  let vertices=mesh.vertices.map(p=>motion(p.map(rat),t))
  for face in mesh.faces {
   let ps=face.map(i=>vertices.at(i))
   let n=cross(sub(ps.at(1),ps.at(0)),sub(ps.at(2),ps.at(0)))
   let a=ps.at(0);let b=ps.at(1);let c=ps.at(2)
   let order=int(rat(law-data.link.clearance)/rat(law-data.link.radius))
   let vertex(i,j)=range(3).map(k=>a.at(k)+(b.at(k)-a.at(k))*i/order+(c.at(k)-a.at(k))*j/order)
   for i in range(order) {for j in range(order - i) {
    let triangles=((vertex(i,j),vertex(i+1,j),vertex(i,j+1)),)
    if i+j+1 < order {triangles.push((vertex(i+1,j),vertex(i+1,j+1),vertex(i,j+1)))}
    for triangle in triangles {
     faces.push((depth:triangle.map(p=>p.at(0)*(-3/5)-p.at(1)+p.at(2)*8/15).sum(),points:triangle.map(screen),color:primary-color(n.at(0)+n.at(2),n.at(1)+n.at(2))))
    }
   }}
  }
 }
 for face in faces.sorted(key:f=>f.depth) {
  line(..face.points,close:true,fill:face.color,stroke:(1pt/7)+by-black)
 }
 // Full centerline traces deliberately expose the interior, including occluded portions.
 for curve in (law-data.link.a,law-data.link.b) {
  let ps=curve.map(p=>screen(motion(p.map(rat),t)))
  line(..ps,close:true,stroke:(paint:white,thickness:1pt,dash:"dashed"))
  for i in range(ps.len()) {circle(ps.at(i),radius:1/24,fill:by-yellow,stroke:.4pt+by-black)}
 }
})

#let swept-triangle()=cetz.canvas(length:11mm,padding:1/5,{
 import cetz.draw: *
 let vertices=((0,0,0),(2,0,0),(0,2,0),(0,0,2),(2,0,2),(0,2,2))
 let screen(p)=(p.at(0)+p.at(2)*2/3,p.at(1)+p.at(2)/3)
 for f in ((0,1,2),(3,4,5)) {
  line(..f.map(i=>screen(vertices.at(i))),close:true,fill:by-blue.lighten(90%),stroke:.7pt+by-blue)
 }
 let seen=()
 for tet in law-data.prism.tetrahedra {for i in range(4) {for j in range(i+1,4) {
  let e=(tet.at(i),tet.at(j)).sorted()
  if not seen.contains(e) {
   seen.push(e)
   line(screen(vertices.at(e.at(0))),screen(vertices.at(e.at(1))),stroke:.5pt+by-rule)
  }
 }}}
 content((-1/3,-1/3),[$K_s$])
 content((7/2,5/2),[$K_t$])
 line((0,-2/3),(4/3,0),stroke:.8pt+by-red,mark:(end:">"))
 content((1,-3/4),text(size:9pt)[local clock])
})
