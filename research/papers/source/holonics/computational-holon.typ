// Reusable presentation of docs/HOLON.md and docs/HNN_FORMULA.md.
// These equations render the maintained contracts; they do not define another runtime.
#import "@preview/cetz:0.3.4": canvas, draw
#import "../lib/dirac.typ": ket, bra, braket, ketbra
#import "../packages/holonic-engraving/lib.typ": engrave
#import "../papers/hnn-information-chemistry/manifold-geometry.typ": torus

// Use the established Information Chemistry geometry and receiver packets directly.
// The displayed currents/phase colors retain the original source and receiver laws.
#let chemistry-scenes = json("../papers/hnn-information-chemistry/receiver-scenes.json")
#let chemistry-knots = json("../papers/hnn-information-chemistry/knot-scenes.json")
#let geometric-face(name,width:90mm,height:auto,mode:"phase") = engrave(chemistry-scenes.at(name),width:width,height:height,mode:mode,line-width:1pt/4)
#let knot-face(name,width:90mm,height:auto,mode:"phase") = engrave(chemistry-knots.at(name),width:width,height:height,mode:mode,line-width:1pt/2)
#let woven-face(name,width:90mm) = image("../../rendered/receiver-engraving/"+name+".svg",width:width)
#let toroidal-modes(kind:"full",k:0,width:90mm) = torus(c:3,k:k,kind:kind,side:width,loops:true)

#let chemistry-style(body) = {
  set page(width:320mm,height:210mm,margin:(x:15mm,y:12mm),fill:white,
    footer:context [
      #set text(size:8pt,fill:rgb("555555"))
      HOLONICS #h(1fr) INFORMATION CHEMISTRY · ELEMENTARY HOLONS #h(1fr) #counter(page).display("1 / 1",both:true)
    ])
  set text(font:"Libertinus Serif",size:11pt,fill:black)
  set par(leading:0.55em,spacing:0pt)
  body
}
#let chemistry-title(n,body,sub)=[
  #text(size:9pt,tracking:1pt)[PLATE #n]
  #v(2mm)#text(size:26pt,weight:"semibold")[#body]
  #v(2mm)#text(size:11pt)[#sub]
  #v(6mm)
]
#let chemistry-note(body)=text(size:9pt,fill:rgb("444444"),body)

// Recover the Holonic entity mark and the corpus's role-typed Dirac operations.
// Frames carry the declared port axes and pairings; these are computational tensor charts.
#let marked(body)=math.attach(math.limits(body,inline:true),b:$tilde$)
#let hk(body)=ket(marked(body))
#let holon-state-equation=$#hk($H$)_F = sum_I H_F^I #ket($e_I$)_F$
#let holon-coordinate-equation=$#hk($H$)_F = mat(h_1;h_2;dots.v;h_n)_F, quad H^(i_1 dots i_p)_(j_1 dots j_q)$
#let holon-transport-equation=$#hk($H'$)_(F')=hat(G)_(F' arrow.l F) #hk($H$)_F$
#let holon-interaction-equation=$#hk($C$)_F=cal(I)_(K,Theta) (#hk($A$)_F,#hk($B$)_F), quad C^c=I^c_(a b)A^a B^b$
#let holon-generation-equation=$#ket($X(tau)$)=cal(U)_(Theta,K)^(tau arrow.l tau_0) (#ket($Xi$),h), quad y_F=#bra($r_F$) b_H (#ket($X(tau)$))$
#let interaction-vertex()=canvas(length:8mm,padding:1/3,{
  import draw: *
  line((-3,1),(0,0),stroke:3pt/5+black,mark:(end:">"))
  line((-3,-1),(0,0),stroke:3pt/5+black,mark:(end:">"))
  line((0,0),(3,0),stroke:3pt/5+black,mark:(end:">"))
  circle((0,0),radius:1/6,fill:black,stroke:none)
  content((-7/2,1),hk($A$));content((-7/2,-1),hk($B$))
  content((7/2,0),hk($C$));content((0,2/3),$I^c_(a b)$)
})

// An exact rational IFS displayed at a finite depth. This is a geometric generator,
// not a fitted neural basin or a dimension estimate from pixels.
#let cantor-dust(level,width:76mm)={
  let cells=((0,0,1),)
  for depth in range(level) {
    let next=()
    for (x,y,s) in cells {for i in (0,2) {for j in (0,2) {
      next.push((x+s*i/3,y+s*j/3,s/3))
    }}}
    cells=next
  }
  canvas(length:width,padding:1/80,{
    import draw: *
    for (x,y,s) in cells {
      line((x,y),(x+s,y),(x+s,y+s),(x,y+s),close:true,fill:black,stroke:none)
    }
    line((0,0),(1,0),(1,1),(0,1),close:true,stroke:1pt/4+rgb("777777"))
  })
}

#let operator-commutator()=canvas(length:57mm,padding:1/3,{
  import draw: *
  let x=(0,0);let ax=(1/2,0);let bx=(0,1/2)
  let bax=(1/2,3/4);let abx=(3/4,1/2)
  line(x,ax,bax,stroke:3pt/5+black,mark:(end:">"))
  line(x,bx,abx,stroke:3pt/5+black,mark:(end:">"))
  line(abx,bax,stroke:(paint:black,thickness:1pt/2,dash:"dashed"),mark:(end:">"))
  content((-1/10,-1/10),hk($H$));content((3/5,-1/10),$hat(A)#hk($H$)$)
  content((-1/5,1/2),$hat(B)#hk($H$)$)
  content((1/2,9/10),$hat(B)hat(A)#hk($H$)$)
  content((11/10,1/2),$hat(A)hat(B)#hk($H$)$)
})


#let scattering-equation = $(I+D D^*)v=2(u+D b), quad w=v-u, quad b^+=D^*v-b$
#let tangent-equation = $(I+D D^*)delta v=2 delta u+2 delta D b+2 D delta b-(delta D D^*+D delta D^*)v$
#let diffusion-equation = $x_t=sqrt(overline(alpha)_t)x_0+sqrt(1-overline(alpha)_t)epsilon$
#let memory-equation = $dot(r)=(D-K B)r+(C+D K-K A-K B K-dot(K))x+g-K f$

// Normalized constraint modes and active faces. Maintained source contracts:
// docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md and docs/HNN_FORMULA.md.
#let constraint-mode-equation=$cal(E)'=cal(E), quad cal(E)(0)=1, quad cal(E)(z+w)=cal(E)(z)cal(E)(w), quad e=cal(E)(1)$
#let multiplicative-lorentz-equation=$gamma_k=(k+k^(-1))/2, quad xi_k=(k-k^(-1))/2, quad gamma_k^2-xi_k^2=1, quad cal(E)(r)=k$
#let observer-stress-face-equation=$e_U=T_(mu nu)U^mu U^nu, quad j_U^mu=-T^(mu nu)U_nu, quad cal(F)_U=c j_U^mu n_mu$
