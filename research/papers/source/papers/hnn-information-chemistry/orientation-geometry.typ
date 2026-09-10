#import "@preview/cetz:0.3.4"
#import "geometry.typ": primary-color
#import "../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-rule
#let orientation-data=json("orientation-example.json")
#let sub(a,b)=array.zip(a,b).map(((x,y))=>x - y)
#let add(a,b)=array.zip(a,b).map(((x,y))=>x+y)
#let vscale(a,s)=a.map(x=>s*x)
#let cross(a,b)=(a.at(1)*b.at(2)-a.at(2)*b.at(1),a.at(2)*b.at(0)-a.at(0)*b.at(2),a.at(0)*b.at(1)-a.at(1)*b.at(0))
#let screen(p)=(p.at(0)-p.at(1),p.at(2)-(p.at(0)+p.at(1))/2)
#let band-frame(t,twist,band)={
 let s=calc.sin(t);let c=calc.cos(t)
 if band=="b" {((0,-c,-2*s),(1,0,0))} else {
  let len=calc.sqrt(s*s+4*c*c)
  ((-c,0,2*s),if twist {(-2*s*c/len,c,s*s/len)} else {(0,1,0)})
 }
}
#let point(tag,twist)={
 let (kind,i,j)=tag
 if kind=="disk" {(orientation-data.grid.at(i)/6,orientation-data.grid.at(j)/6,0)} else {
  let (c,e)=band-frame(calc.pi*i/orientation-data.L,twist,kind)
  add(c,vscale(e,(j - 2)/6))
 }
}
#let ribbon-surface(kind:"shorts",side:85mm,frames:true)=cetz.canvas(length:side/5,padding:1/8,{
 import cetz.draw: *
 let source=orientation-data.surfaces.at(kind)
 let twist=kind!="annulus"
 let vertices=source.tags.map(t=>point(t,twist))
 let faces=source.faces.map(f=>{
  let ps=f.map(i=>vertices.at(i))
  let normal=cross(sub(ps.at(1),ps.at(0)),sub(ps.at(2),ps.at(0)))
  (depth:ps.map(p=>p.sum()).sum(),points:ps.map(screen),color:primary-color(normal.at(0)+normal.at(2),normal.at(1)+normal.at(2)))
 })
 // One-sided surfaces have no global outward normal. Render every face.
 for f in faces.sorted(key:f=>f.depth) {
  line(..f.points,close:true,fill:f.color,stroke:(1pt/7)+rgb("363744"))
 }
 // Boundary is a complete topological trace; occluded pieces are intentional.
 for loop in source.topology.boundary_loops {
  line(..loop.map(i=>screen(vertices.at(i))),close:true,stroke:.8pt+by-black)
 }
 if frames {
  for band in (if kind=="shorts" {("a","b")} else {("a",)}) {
   let pts=range(orientation-data.L+1).map(i=>screen(band-frame(calc.pi*i/orientation-data.L,twist,band).at(0)))
   line(..pts,stroke:1pt+white)
   line(..pts,stroke:.45pt+by-black,mark:(end:">"))
   for k in (1,3,5,7) {
    let (c,e)=band-frame(calc.pi*k/8,twist,band)
    line(screen(add(c,vscale(e,-1/4))),screen(add(c,vscale(e,1/4))),stroke:1pt+white)
    line(screen(add(c,vscale(e,-1/4))),screen(add(c,vscale(e,1/4))),stroke:.6pt+by-red,mark:(end:">"))
   }
  }
 }
})

#let cover-seam()=cetz.canvas(length:11mm,padding:1/5,{
 import cetz.draw: *
 for (y,label) in ((1,[$+$]),(-1,[$-$])) {
  rect((0,y - 1/3),(5,y+1/3),fill:by-blue.lighten(94%),stroke:.5pt+by-blue)
  content((-1/2,y),label)
  let ends=if y>0 {((1/3,y),(14/3,y))} else {((14/3,y),(1/3,y))}
  line(..ends,stroke:.6pt+by-blue,mark:(end:">"))
 }
 bezier((5,1),(5,-1),(6,1),(6,-1),stroke:.8pt+by-red,mark:(end:">"))
 bezier((0,-1),(0,1),(-1,-1),(-1,1),stroke:.8pt+by-red,mark:(end:">"))
 content((5/2,0),text(size:10pt)[$tau:(x,+) arrow.r (x,-)$])
 content((5/2,-2),text(size:9pt)[One circuit exchanges local orientation.])
})

#let thickened-shorts(side:70mm)=cetz.canvas(length:side/5,padding:1/8,{
 import cetz.draw: *
 let source=orientation-data.surfaces.shorts
 let mesh=source.cover_mesh
 let base=source.tags.map(t=>point(t,true))
 let raw=mesh.base_vertices.map(v=>base.at(v))
 let normals=raw.map(p=>(0,0,0))
 for f in mesh.faces {
  let normal=cross(sub(raw.at(f.at(1)),raw.at(f.at(0))),sub(raw.at(f.at(2)),raw.at(f.at(0))))
  for v in f {normals.at(v)=add(normals.at(v),normal)}
 }
 let vertices=array.zip(raw,normals).map(((p,n))=>add(p,vscale(n,(1/12)/calc.sqrt(n.map(x=>x*x).sum()))))
 let faces=()
 for (family,fs) in (("cover",mesh.faces),("rim",mesh.rim)) {for f in fs {
  let ps=f.map(v=>vertices.at(v))
  let n=cross(sub(ps.at(1),ps.at(0)),sub(ps.at(2),ps.at(0)))
  faces.push((depth:ps.map(p=>p.sum()).sum(),points:ps.map(screen),color:if family=="rim" {by-yellow} else {primary-color(n.at(0)+n.at(2),n.at(1)+n.at(2))}))
 }}
 for f in faces.sorted(key:f=>f.depth) {
  line(..f.points,close:true,fill:f.color,stroke:(1pt/8)+by-black)
 }
})

#let transport-square()=cetz.canvas(length:17mm,padding:1/5,{
 import cetz.draw: *
 let pts=(((0,1),[$(1,2)$]),((3,1),[$(1,-2)$]),((0,-1),[$(-2,1)$]),((3,-1),[$(2,1) != (-2,-1)$]))
 for (p,t) in pts {
  content(p,box(inset:3pt,fill:white,stroke:.5pt+by-rule)[#t])
 }
 line((1/2,1),(5/2,1),stroke:.7pt+by-red,mark:(end:">"))
 content((3/2,5/4),[$A$])
 line((0,2/3),(0,-2/3),stroke:.7pt+by-blue,mark:(end:">"))
 content((-1/4,0),[$B$])
 line((3,2/3),(3,-2/3),stroke:.7pt+by-blue,mark:(end:">"))
 content((13/4,0),[$B$])
 line((1/2,-1),(2,-1),stroke:.7pt+by-red,mark:(end:">"))
 content((3/2,-5/4),[$A$])
})
