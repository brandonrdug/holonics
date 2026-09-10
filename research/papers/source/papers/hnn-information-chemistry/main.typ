#import "@preview/fletcher:0.5.8": diagram, node, edge
#import "../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-rule, by-muted
#import "geometry.typ": solid, simplex, chambers, relu-fold, wave-tile

#set document(title: "HNN - Information Chemistry", author: "Brandon Duggan / Holonics", description: "Five diagram plates: Athena, Eros, layer maps, geometric strata, and Soulkiller.")
#set page(width: 320mm, height: 210mm, margin: (x:16mm,y:13mm), footer: context {
  set text(size:8pt,fill:by-muted)
  [HOLONICS #h(1fr) HNN / INFORMATION CHEMISTRY #h(1fr) #counter(page).display("1") / 5]
})
#set text(font: "Libertinus Serif", size:11pt, fill:by-black)
#set math.equation(numbering:none)
#set par(leading:.55em, spacing:0pt)
#let eq(m)=block(above:2mm,below:2mm,math.equation(m.body,block:true))
#let caption(body)=text(size:9pt,fill:by-muted,body)
#let title(n,t,sub)=[
  #text(size:9pt,fill:by-blue,tracking:1pt)[PLATE #n]
  #v(2mm)
  #text(size:25pt,weight:"semibold")[#t]
  #v(2mm)
  #text(size:11pt,fill:by-muted)[#sub]
  #v(6mm)
]
#let n(pos,name,t,m,tone:by-blue,width:61mm)=node(pos,align(center)[
  #text(size:10pt,weight:"semibold")[#t] #v(2.5mm) #text(size:10pt,m)
],name:name,width:width,height:16mm,fill:tone.lighten(94%),stroke:.7pt+tone,inset:2.5mm,corner-radius:1mm)
#let arr(a,b,..args)=edge(a,b,"->",..args)
#let card(t,m,d,effect)=block(width:100%,height:51mm,inset:(x:4mm,y:3mm),stroke:(top:.7pt+by-rule))[
  #text(size:12pt,weight:"semibold")[#t]
  #v(1mm)
  #v(2mm)
  #align(center,m)
  #v(3mm)
  #align(center,d)
  #v(3mm)
  #text(size:9.5pt)[#effect]
]

#title("01","Athena conducts. Eros develops.","One continuing body; explicit current paths and a joined developmental return.")
#align(center,diagram(
  edge-stroke:.8pt+by-black,label-size:9pt,node-outset:1pt,
  n((0mm,0mm),<x>,[Occurrence],$x_t$),
  n((83mm,0mm),<a>,[Athena: material, state, incidence],$A_t=(M_t,z_t,K_t)$),
  n((166mm,0mm),<v>,[Actual received comparison],$(s,v;"producer")$,tone:by-red),
  n((0mm,22mm),<s>,[Transport to local charts],$(s_j,c_i)=(r_j x_t,r_i z_t)$),
  n((0mm,44mm),<j>,[Join interacting currents],$phi(s,c)=(s,c,s ⊗ c)$),
  n((0mm,66mm),<l>,[Apply the learned relation],$Y={y:(phi,y) in M_t}$),
  n((0mm,88mm),<r>,[React and read the boundary],$z^+=rho_(M_t)(z_t,Y), quad y=b(z^+)$),
  n((166mm,22mm),<f>,[Eros: compatible conditions],$F={c:(phi(s,c),v) in M}$,tone:by-red),
  n((166mm,44mm),<p>,[For $F=a+V$: retain free directions],$c'=a+P_(V)(c-a)$,tone:by-red),
  n((166mm,66mm),<m>,[Form reusable material],$M'=op("span")(M union {(phi(s,c'),v)})$,tone:by-red),
  n((83mm,110mm),<next>,[One complete successor],$A_(t+1)=(M',z',K')$,tone:by-black),
  n((0mm,110mm),<out>,[Emission],$y_t$),
  arr(<r>,<out>),arr(<x>,<s>),arr(<a>,<s>),arr(<s>,<j>),arr(<j>,<l>),arr(<l>,<r>),
  edge("->",vertices:(<a>,(83mm,66mm),<l>)),
  arr(<v>,<f>),arr(<a>,<f>),arr(<f>,<p>),arr(<p>,<m>),arr(<m>,<next>),arr(<r>,<next>),
  edge("-->",vertices:(<next>,(124mm,110mm),(124mm,0mm),<a>),label:[$"next occurrence"$],label-side:right),
))
#v(4mm)
#grid(columns:(1fr,1fr),gutter:8mm,
  caption([*Definition / source-inspected binding.* Blue: conduct. Red: Eros's local relation/condition update. Source, material and the comparison retain their actual producing cut.]),
  caption([*Interpretation: full assembly.* Local passages compose over admitted incidence. The bilinear relation above is an existing binding; complete contextual assembly remains in progress.]),
)

#pagebreak()
#title("02","What a layer does to a space","Finite vector charts: the operation, its categorical role, and the distinctions it retains.")
#grid(columns:(1fr,1fr,1fr),gutter:(7mm,4mm),
 card([Linear map / “projection”],$x mapsto W x$,
  diagram(spacing:8mm,node((0,0),$V$),node((1,0),$op("im")W$),arr((0,0),(1,0),label:[$W$])),
  [Linear morphism. Fibres are $x+ker W$; rank controls the image. It is a projection only when $W^2=W$ on one space.]),
 card([Concatenate / retain both],$(x,y) mapsto x ⊕ y$,
  diagram(spacing:7mm,node((0,0),$V$),node((0,1),$U$),node((1,.5),$V ⊕ U$),arr((0,0),(1,.5),label:[$i_V$]),arr((0,1),(1,.5),label:[$i_U$])),
  [Biproduct injections retain both components. Combining their storage does not yet identify them.]),
 card([Add / superpose],$(x,y) mapsto x+y$,
  diagram(spacing:8mm,node((0,0),$V ⊕ V$),node((1,0),$V$),arr((0,0),(1,0),label:[$nabla$])),
  [The codiagonal identifies $(x+h,y-h)$. Opposed contributions can cancel at this receiver.]),
 card([Tensor / interact],$(x,y) mapsto x ⊗ y$,
  diagram(spacing:8mm,node((0,0),$V times U$),node((1,0),$V ⊗ U$),arr((0,0),(1,0),label:[$⊗$])),
  [Universal bilinear interaction. A bilinear response factors through a linear map out of $V ⊗ U$. Gating adds a declared nonlinearity.]),
 card([Softmax / relative participation],$p_i=frac(e^(s_i),sum_j e^(s_j))$,
  diagram(spacing:6mm,node((0,0),$RR^n slash ⟨1⟩$),node((1,0),$op("int")Delta^(n-1)$),arr((0,0),(1,0),label:[$tilde(sigma)$])),
  [Smooth bijection of the score-difference chart with the simplex interior. All $p_i>0$; common score shifts disappear.]),
 card([Normalize / choose a section],$N_(0)(x)=sqrt(d) x/norm(x)$,
  diagram(spacing:6mm,node((0,0),$(RR^d without {0}) slash RR_(>0)$),node((1,0),$S_(sqrt(d))^(d-1)$),arr((0,0),(1,0))),
  [Zero-offset RMS normalization chooses one point per positive ray. Layer centering additionally removes the common-value direction.]),
)
#v(3mm)
#eq[$N_(epsilon)(x)=x/sqrt(norm(x)^2/d+epsilon), quad epsilon>0: quad RR^d tilde.eq {y:norm(y)<sqrt(d)}$]
#caption([*Proved-standard, stated finite charts.* Positive $epsilon$ retains radial scale before learned gains: stabilized RMS normalization is not the exact ray quotient above. Zero gain coordinates can erase further information.])

#pagebreak()
#title("03","Smooth redistribution, selection walls, rank changes","A geometric distinction between moving within a chart and changing the active continuation.")
#grid(columns:(1fr,1fr,1fr),gutter:10mm,
 [#text(size:14pt,weight:"semibold")[Softmax stays inside the simplex]
  #v(5mm)#align(center,simplex())#v(4mm)
  $s=(lambda,0,0), quad p=frac(1,exp(lambda)+2) (exp(lambda),1,1)$
  #v(2mm)#caption([Every finite $lambda$ keeps three positive shares. The blue path approaches a vertex only in the limit.])],
 [#text(size:14pt,weight:"semibold")[Hard selection crosses a wall]
  #v(5mm)#align(center,chambers())#v(4mm)
  $E(s)=op("argmax")_i s_i, quad s=(a,b,0)$
  #v(2mm)#caption([The maximal-score tie walls divide parameter space into regions with different active indices. A tie convention is part of the map.])],
 [#text(size:14pt,weight:"semibold")[A nonlinear map changes local rank]
  #v(5mm)#align(center,relu-fold())#v(4mm)
  $r(x)_i=max(0,x_i), quad D r=op("diag")(1_(x_i>0))$
  #v(2mm)#caption([The four sign chambers form a support lattice. Whole negative directions collapse; the derivative changes at its walls.])],
)
#v(8mm)
#align(center,diagram(spacing:(17mm,7mm),label-size:10pt,
 node((0,0),$emptyset$),node((1,-.5),${1}$),node((1,.5),${2}$),node((2,0),${1,2}$),
 arr((0,0),(1,-.5)),arr((0,0),(1,.5)),arr((1,-.5),(2,0)),arr((1,.5),(2,0)),
 node((3.6,0),$M_t=mat(1,0;0,t)$),node((5,0),$op("rank")M_t=cases(2 & "if " t != 0,1 & "if " t=0)$),arr((3.6,0),(5,0)),
))
#v(4mm)
#caption([*Proved-derived finite charts; interpretation of phase.* Smooth participation, active-set change and rank loss are different events. Information Chemistry calls a change of the continuing transport class a phase transition; a physical phase claim additionally requires its constitutive law.])

#pagebreak()
#title("04","Information Chemistry: elements into compounds","Typed ports compose; relative phase changes the receiver image of the same constituent modes.")
#align(center,diagram(spacing:(12mm,8mm),node-inset:3mm,edge-stroke:.8pt+by-black,
 node((0,0),[#solid("tetra")\ $E_1$]),
 node((1,0),[#solid("cube",color:by-red)\ $E_2$]),
 node((2,0),[#solid("octa",color:by-yellow)\ $E_3$]),
 node((3.5,0),[$E_1 ⊗ E_2 ⊗ E_3$\ #text(size:9pt)[retain the joint source]],stroke:.6pt+by-rule),
 node((5,0),[$C=mu_(c)(E_1,E_2,E_3)$\ #text(size:9pt)[join ports; retain boundary]],stroke:.6pt+by-rule),
 node((6.5,0),[$b_(R)(C)$\ #text(size:9pt)[receiver image]],stroke:.6pt+by-blue),
 arr((0,0),(3.5,0),bend:30deg),arr((1,0),(3.5,0),bend:18deg),arr((2,0),(3.5,0)),arr((3.5,0),(5,0),label:[$mu_c$]),arr((5,0),(6.5,0),label:[$b_R$]),
))
#v(3mm)
#caption([*Interpretation.* Polyhedra depict ported boundary cells, not semantic labels. The lattice tiles below give a separate explicit realization of constituent composition.])
#v(5mm)
#grid(columns:(1fr,1fr,1fr,1.15fr,1.15fr),gutter:5mm,align:center,
 [$psi_(1,1)$#v(3mm)#wave-tile(1)],
 [$psi_(2,1)$#v(3mm)#wave-tile(2)],
 [$psi_(1,2)$#v(3mm)#wave-tile(3)],
 [$I_0$#v(3mm)#wave-tile(4,side:43mm)],
 [$I_pi$#v(3mm)#wave-tile(5,side:43mm)],
)
#v(4mm)
#eq[$psi_(m,n)(i,j)=sin((m pi i)/17)sin((n pi j)/17), quad i,j in {1,dots,16}$]
#eq[$u_theta=psi_(1,1)+0.7 e^(i theta)psi_(2,1)+0.5 psi_(1,2), quad I_theta=abs(u_theta)^2$]
#eq[$abs(a+b)^2=abs(a)^2+abs(b)^2+2 op("Re")(a overline(b))$]
#caption([*Definition / computational illustration.* Dirichlet square-lattice modes, dimensionless; shared intensity scale $0$ to $4.84$. Blue/red mark positive/negative amplitude. Interference changes the output without changing the three modes.])
#v(3mm)
#text(size:10pt)[*Conjecture to develop:* one reusable family of typed, parameterized generators can compose every admitted behavioral class. A pattern is a whole diagram modulo its declared future receivers, not a unique solid or a stored output image.]

#pagebreak()
#title("05","When diagrams agree, Soulkiller can lift their maps","Compare complete transitions; then restrict at an explicitly declared receiver family.")
#grid(columns:(1fr,1fr),gutter:16mm,
 [#text(size:14pt,weight:"semibold")[A commuting architecture]
  #v(6mm)
  #align(center,diagram(spacing:(24mm,17mm),edge-stroke:.8pt+by-black,label-size:11pt,
   node((0,0),$A times X_A$),node((1,0),$Y_A times T_A times A$),
   node((0,1),$B times X_B$),node((1,1),$Y_B times T_B times B$),
   arr((0,0),(1,0),label:[$F_A$]),arr((0,1),(1,1),label:[$F_B$]),
   arr((0,0),(0,1),label:[$q_("in")$],label-side:left),arr((1,0),(1,1),label:[$q_("out")$]),
  ))
  #v(4mm)
  #eq[$q_("out") F_A=F_B q_("in")$]
  #v(2mm)
  #text(size:10pt)[Invertible maps: re-expression.\ Noninvertible maps: retained fibres.\ Unequal paths: explicit defect.]
  #v(4mm)
  #eq[$X arrow.l W_f arrow.r Y arrow.l W_g arrow.r Z$]
  #v(2mm)
  #eq[$W_(g compose f)=W_f times_Y W_g$]
  #v(2mm)
  #caption([*Definition / proved-derived composition.* Serial joining retains the actual occurrence pullback. The same state map appears before and after each transition.])
 ],
 [#text(size:14pt,weight:"semibold")[Soulkiller: realization, then restriction]
  #v(6mm)
  #align(center,diagram(spacing:(14mm,10mm),label-size:10pt,node-inset:2mm,
   node((0,0),[Source diagram\ $D_S$]),node((1,0),[Native realization\ $D_N$]),node((2,0),[Retained body\ $D_R$]),
   arr((0,0),(1,0),label:[$i$]),arr((1,0),(2,0),label:[$r$]),
   node((1,1),[Excite and intervene\ #text(size:9pt)[actual receiver/history family]]),
   arr((1,0),(1,1)),arr((1,1),(2,0)),
   node((0,2),[Cold witness]),node((1,2),[Native material]),node((2,2),[Insufficiency]),
   arr((1,1),(0,2)),arr((1,1),(1,2)),arr((1,1),(2,2)),
   node((1,3),[Eros $arrow.r$ successor Athena]),arr((1,2),(1,3)),
  ))
  #v(3mm)
  #eq[$F_N i=i F_S, quad r F_N=F_R r$]
  #v(2mm)
  #eq[$therefore F_(R)(r i)=(r i)F_S$]
  #v(2mm)
  #caption([*Conditional lift.* The equations state the required scope. Existing SKE evidence covers its declared families; a full V4.1 binding remains open.])
 ],
)
#v(6mm)
#eq[$"Development also owes: " q(U_(A)(M,v))=U_(B)(q(M),v)$]
#caption([*Conditional.* Equal inference maps need not have equal learning updates. State, shared parameters, producing factors and the update metric travel with the developmental square.])
#v(5mm)
#text(size:8.5pt,fill:by-muted)[
  Sources: *Categorical Holonics*; *Elements of Holonics*; the July 19 Information Chemistry record; the August 9 crystal/receiver record; current HNN composition and source owners.\
  Diagrams: #link("https://typst.app/universe/package/fletcher/")[Fletcher 0.5.8], with the repository's geometric notation and CeTZ. Mathematical interpretations and conjecture do not change implementation grades.
]
