#import "@preview/cetz:0.3.4"
#import "../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-rule

// Original geometric constructions; dimensionless illustrative charts.
#let ink = by-black
#let pale = rgb("eef2f7")
#let mesh(stroke: by-rule) = {
  import cetz.draw: *
  for j in range(5) { line((0,j/4), (1,j/4), stroke: .35pt + stroke) }
  for i in range(5) { line((i/4,0), (i/4,1), stroke: .35pt + stroke) }
}
#let solid(kind, color: by-blue) = cetz.canvas(length: 13mm, padding: .1, {
  import cetz.draw: *
  let pts = ()
  let bonds = ()
  if kind == "tetra" {
    pts = ((0,0), (1.6,0), (.8,1.38), (.75,.45))
    bonds = ((0,1),(1,2),(2,0),(0,3),(1,3),(2,3))
  } else if kind == "cube" {
    pts = ((0,0),(1.1,0),(1.1,1.1),(0,1.1),(.45,.4),(1.55,.4),(1.55,1.5),(.45,1.5))
    bonds = ((0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4),(0,4),(1,5),(2,6),(3,7))
  } else {
    pts = ((0,.6),(.8,.25),(1.6,.6),(.8,.95),(.8,1.7),(.8,-.45))
    bonds = ((0,1),(1,2),(2,3),(3,0),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2),(5,3))
  }
  for (a,b) in bonds { line(pts.at(a),pts.at(b),stroke: .85pt + color) }
  for p in pts { circle(p,radius:.04,fill:color,stroke:none) }
})

#let simplex() = cetz.canvas(length: 26mm, padding: .2, {
  import cetz.draw: *
  let a=(0,0); let b=(2,0); let c=(1,calc.sqrt(3))
  line(a,b,c,close:true,stroke:.8pt+ink,fill:rgb("f5f7fa"))
  for t in (.25,.5,.75) {
    line((t,calc.sqrt(3)*t),(2-t,calc.sqrt(3)*t),stroke:.35pt+by-rule)
    line((2*t,0),(1+t,calc.sqrt(3)*(1-t)),stroke:.35pt+by-rule)
  }
  // s=(lambda,0,0); barycentric p=(exp(lambda),1,1)/Z.
  let path=()
  for t in range(41) {
    let z=calc.exp(t/10); let den=z+2
    path.push(((2+1)/den,calc.sqrt(3)/den))
  }
  line(..path,stroke:1.5pt+by-blue,mark:(end:">"))
  for lam in (0,1,2,4) {
    let z=calc.exp(lam); let den=z+2
    circle((3/den,calc.sqrt(3)/den),radius:.035,fill:by-blue,stroke:none)
  }
  content((-.13,-.16),$e_1$);content((2.13,-.16),$e_2$);content((1,1.93),$e_3$)
  content((1.42,.53),text(size:10pt)[$p_i>0$])
})

#let chambers() = cetz.canvas(length: 21mm, padding: .3, {
  import cetz.draw: *
  let a=(-1.5,-1.15);let b=(1.5,-1.15);let c=(1.5,1.3);let d=(-1.5,1.3)
  line((0,0),(-1.5,0),a,(0,-1.15),close:true,fill:by-yellow.lighten(80%),stroke:none)
  line((0,0),(0,-1.15),b,c,(1.3,1.3),close:true,fill:by-blue.lighten(86%),stroke:none)
  line((0,0),(1.3,1.3),d,(-1.5,0),close:true,fill:by-red.lighten(87%),stroke:none)
  // logit chart s=(a,b,0): three top-1 cones.
  line((0,0),(0,-1.15),stroke:.85pt+ink)
  line((0,0),(-1.5,0),stroke:.85pt+ink)
  line((0,0),(1.3,1.3),stroke:.85pt+ink)
  content((.85,.15),$s_1 " wins"$)
  content((-.65,.65),$s_2 " wins"$)
  content((-.65,-.6),$s_3 " wins"$)
  content((1.1,1.45),text(size:9pt)[$s_1=s_2$])
})

#let relu-fold() = cetz.canvas(length: 20mm, padding: .3, {
  import cetz.draw: *
  rect((-1.1,-1.1),(1.1,1.1),fill:rgb("fafafa"),stroke:none)
  line((-1.1,0),(1.15,0),stroke:.65pt+by-rule,mark:(end:">"))
  line((0,-1.1),(0,1.15),stroke:.65pt+by-rule,mark:(end:">"))
  for i in range(1,5) {
    let t=i/5
    line((t,0),(t,1),stroke:.7pt+by-blue)
    line((0,t),(1,t),stroke:.7pt+by-blue)
    line((-t,0),(0,0),stroke:.5pt+by-red)
    line((0,-t),(0,0),stroke:.5pt+by-red)
  }
  circle((0,0),radius:.04,fill:by-red,stroke:none)
  content((.58,.58),box(fill:white,inset:2pt)[$"rank " 2$])
  content((-.62,.6),text(size:10pt)[$"rank " 1$])
  content((.62,-.6),text(size:10pt)[$"rank " 1$])
  content((-.6,-.6),text(size:10pt)[$"rank " 0$])
})

#let lattice-bits = 4
#let lattice-count = int(calc.pow(2,lattice-bits))
#let source-drives = (10,7,5)
#let mode(i,j,m,n,N)=calc.sin(m*calc.pi*i/(N+1))*calc.sin(n*calc.pi*j/(N+1))
#let wave-tile(kind, side: 39mm) = cetz.canvas(length: side/lattice-count, padding: 0, {
  import cetz.draw: *
  let N=lattice-count
  let beta=source-drives.at(1)/source-drives.at(0)
  let gamma=source-drives.at(2)/source-drives.at(0)
  let intensity-bound=calc.pow(1+beta+gamma,2)
  for j in range(N) { for i in range(N) {
    let u=mode(i+1,j+1,1,1,N)
    let v=mode(i+1,j+1,2,1,N)
    let w=mode(i+1,j+1,1,2,N)
    let z=if kind==1 {u} else if kind==2 {v} else if kind==3 {w} else if kind==4 {calc.pow(u + beta*v + gamma*w,2)/intensity-bound} else {calc.pow(u - beta*v + gamma*w,2)/intensity-bound}
    let col=if kind<=3 {
      if z>=0 {by-blue.lighten((1-calc.min(z,1))*100%)} else {by-red.lighten((1-calc.min(-z,1))*100%)}
    } else {ink.lighten((1-calc.min(z,1))*100%)}
    rect((i,j),(i+1.01,j+1.01),fill:col,stroke:none)
  }}
  rect((0,0),(N,N),stroke:.5pt+by-rule)
})

// Exact 3D values are supplied by arithmetic-example.json. Only this exterior
// camera forgets depth: (x,y,z) |-> (x+z/2,y+z/4).
#let arithmetic-data=json("arithmetic-example.json")
#let rational-vector(w)=w.num.map(k=>k/w.den)
#let camera(v)=(v.at(0)+v.at(2)/2,v.at(1)+v.at(2)/4)
#let tetrahedron-example()=cetz.canvas(length:26mm,padding:.35,{
  import cetz.draw: *
  let v=arithmetic-data.vertices
  let p=v.map(camera)
  for i in range(4) {for j in range(i+1,4) {
    line(p.at(i),p.at(j),stroke:.6pt+by-rule)
  }}
  let ac=camera(array.zip(v.at(0),v.at(2)).map(((x,y))=>(x+y)/2))
  let bc=camera(array.zip(v.at(1),v.at(2)).map(((x,y))=>(x+y)/2))
  line(p.at(3),ac,bc,close:true,fill:by-blue.lighten(90%),stroke:.9pt+by-blue)
  for i in range(4) {circle(p.at(i),radius:.035,fill:ink,stroke:none)}
  content((1.75,1.4),$v_a$)
  content((.6,-1.5),$v_b$)
  content((-1.75,.9),$v_c$)
  content((-.85,-.8),$v_r$)
  let offsets=((.28,-.16),(.2,.15),(-.3,.12))
  for (k,row) in arithmetic-data.rows.enumerate() {
    let loc=camera(rational-vector(row.point))
    let col=if row.residual==0 {by-blue} else {by-red}
    circle(loc,radius:.035,fill:col,stroke:none)
    let label=(loc.at(0)+offsets.at(k).at(0),loc.at(1)+offsets.at(k).at(1))
    line(loc,label,stroke:.4pt+col)
    content(label,box(fill:white,inset:1pt)[#text(fill:col,weight:"semibold")[#row.label]])
  }
})

// A finite Dirichlet lattice realization of the tetrahedron's four port weights.
// The rational source weights are exact in the receipt; sine/cosine evaluation
// happens only in this exterior renderer. The stencil is u'=(sum four neighbors)/4.
#let field-value(weights,i,j,steps,N) = {
  let total=0
  for (k,pair) in arithmetic-data.field.basis_modes.enumerate() {
    let (m,n)=pair
    let eta=(calc.cos(m*calc.pi/(N+1))+calc.cos(n*calc.pi/(N+1)))/2
    total += weights.at(k)*calc.pow(eta,steps)*mode(i,j,m,n,N)
  }
  total
}
#let string-field(weights-wire,steps,side:32mm,intensity:false,comparison:none,gain:1,display-reference:1)=cetz.canvas(length:side/lattice-count,padding:0,{
  import cetz.draw: *
  let N=lattice-count
  let weights=rational-vector(weights-wire)
  let other=if comparison==none {none} else {rational-vector(comparison)}
  for j in range(N) {for i in range(N) {
    let u=field-value(weights,i+1,j+1,steps,N)
    let value=if intensity {u*u} else {u}
    if other!=none {
      let v=field-value(other,i+1,j+1,steps,N)
      value -= if intensity {v*v} else {v}
    }
    value *= gain/display-reference
    let col=if intensity and other==none {
      ink.lighten((1-calc.min(value,1))*100%)
    } else if value>=0 {
      by-blue.lighten((1-calc.min(value,1))*100%)
    } else {
      by-red.lighten((1-calc.min(-value,1))*100%)
    }
    rect((i,j),(i+1+1/100,j+1+1/100),fill:col,stroke:none)
  }}
  rect((0,0),(N,N),stroke:.5pt+by-rule)
})


// Shared display receivers. They change image contrast only, not field evolution.
#let intensity-reference = {
  let peak=0
  let population=arithmetic-data.rows.map(r=>r.barycentric)+arithmetic-data.field.reflection_cases
  for wire in population {
    let weights=rational-vector(wire)
    for j in range(1,lattice-count+1) {for i in range(1,lattice-count+1) {
      let u=field-value(weights,i,j,lattice-count,lattice-count)
      peak=calc.max(peak,u*u)
    }}
  }
  peak
}
#let intensity-difference-reference = {
  let peak=0
  let a=rational-vector(arithmetic-data.field.reflection_cases.at(3))
  let b=rational-vector(arithmetic-data.field.reflection_cases.at(2))
  for j in range(1,lattice-count+1) {for i in range(1,lattice-count+1) {
    let u=field-value(a,i,j,lattice-count,lattice-count)
    let v=field-value(b,i,j,lattice-count,lattice-count)
    peak=calc.max(peak,calc.abs(u*u - v*v))
  }}
  peak
}
