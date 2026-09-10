#import "@preview/fletcher:0.5.8": diagram, node, edge
#import "../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-rule, by-muted
#import "geometry.typ": solid, simplex, chambers, relu-fold, wave-tile, tetrahedron-example, arithmetic-data, string-field, lattice-count, intensity-reference, intensity-difference-reference, surface-tile, primary-color

#import "manifold-geometry.typ": torus, cube-net, root-action, overlap, flux-faces, manifold-data
#import "orientation-geometry.typ": ribbon-surface, cover-seam, thickened-shorts, transport-square, orientation-data

#import "law-geometry.typ": linked-bodies, swept-triangle

#set document(title: "HNN - Information Chemistry", author: "Brandon Duggan / Holonics", description: "Twenty diagram plates: HNN, equational transport, manifold differences, non-orientable bridges, and moving polygonal world tubes.")
#set page(width: 320mm, height: 210mm, margin: (x:16mm,y:13mm), footer: context {
  set text(size:8pt,fill:by-muted)
  [HOLONICS #h(1fr) HNN / INFORMATION CHEMISTRY #h(1fr) #counter(page).display("1") / 20]
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
#eq[$b=4, quad N=2^b, quad (i,j)=(k+1,l+1), quad k,l in {0,dots,N-1}$]
#eq[$psi_(m,n)(i,j)=sin((m pi i)/(N+1))sin((n pi j)/(N+1)), quad N+1=2^4+1=17$]
#eq[$u_theta=psi_(1,1)+frac(7,10) e^(i theta)psi_(2,1)+frac(1,2) psi_(1,2), quad I_theta=abs(u_theta)^2$]
#eq[$abs(a+b)^2=abs(a)^2+abs(b)^2+2 op("Re")(a overline(b))$]
#caption([*Definition / declared source chart.* Four bits address $N$ interior sites per axis; the two Dirichlet boundaries are $N+1$ steps apart. Declared drives $(10,7,5)$ relative to the first give $(1,7/10,1/2)$; the shared intensity bound is $(1+7/10+1/2)^2=121/25$.])
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
#eq[$"Face-conserving development: " q(U_(A)(M,v))=U_(B)(q(M),v)$]
#caption([*Definition: compatibility law.* The two routes preserve the same declared faces when their full difference vanishes. Plates 6 to 9 follow actual string fields through diffusion, images, geometric projection and an exact induced update.])
#v(5mm)
#text(size:8.5pt,fill:by-muted)[
  Sources: *Categorical Holonics*; *Elements of Holonics*; the July 19 Information Chemistry record; the August 9 crystal/receiver record; current HNN composition and source owners.\
  Diagrams: #link("https://typst.app/universe/package/fletcher/")[Fletcher 0.5.8], with the repository's geometric notation and CeTZ. Mathematical interpretations and conjecture do not change implementation grades.
]

#pagebreak()
#title("06","Real strings diffuse into different images","A covariant port-to-mode binding, opaque relational color, and the signed current as height.")
#grid(columns:(34mm,1fr,1fr,1fr,1fr),gutter:(6mm,4mm),align:center,
 [Source inscription],[$u_0$],[$u_(N/4)$],[$u_N$],[$I_N/I_star$],
 ..arithmetic-data.rows.map(row=>(
   [#text(size:12pt,weight:"semibold")[#raw(row.source)]#v(2mm)#caption([chart weight $m=$#row.mass])],
   surface-tile(row.barycentric,0,side:37mm),
   surface-tile(row.barycentric,lattice-count/4,side:37mm),
   surface-tile(row.barycentric,lattice-count,side:37mm),
   string-field(row.barycentric,lattice-count,intensity:true,display-reference:intensity-reference),
 )).flatten(),
)
#v(4mm)
#eq[$lambda=frac((a,b,c,1),a+b+c+1), quad u_0=lambda_a psi_(2,1)+lambda_b psi_(1,2)+lambda_c psi_(1,1)+lambda_r psi_(2,2)$]
#eq[$(D u)_(i,j)=frac(u_(i-1,j)+u_(i+1,j)+u_(i,j-1)+u_(i,j+1),4), quad u_k=D^k u_0$]
#caption([*Definition / explicit lattice realization.* $N=2^4$; exterior samples vanish at the Dirichlet boundary. The factor $1/4$ comes from four neighboring ports. Columns show $0$, $N/4=4$, and $N=16$ steps. Height: signed current. Opaque color: the quadratic local-gradient receiver on plate 10. Gray: $I_N/I_star$, with fixed $I_star=1$ for every source and time. This calibration is independent of the plotted population.])

#pagebreak()
#title("07","Reflection and union are visible in the images","Same four modes, same diffusion, different source combinations. The difference is retained as a field.")
#let rc=arithmetic-data.field.reflection_cases
#grid(columns:(1fr,1fr,1fr,1fr,1fr),gutter:5mm,align:center,
 [*Received*\ #raw("1+2=4")],
 [*Reflected*\ #raw("1+2=2")],
 [*Transported union*\ #raw("1+2=3")],
 [*Ordinary chart mean*\ $(1,2,20/7)$],
 [*Difference field*\ $"ordinary" - "transported"$],
)
#v(4mm)
#text(size:10pt,fill:by-muted)[Current as a triangulated surface at the initial cut]
#v(2mm)
#grid(columns:(1fr,1fr,1fr,1fr,1fr),gutter:5mm,align:center,
 surface-tile(rc.at(0),0,side:42mm),surface-tile(rc.at(1),0,side:42mm),
 surface-tile(rc.at(2),0,side:42mm),surface-tile(rc.at(3),0,side:42mm),
 [#string-field(rc.at(3),0,side:38mm,comparison:rc.at(2),gain:arithmetic-data.field.current_difference_display_gain)\ $42 Delta u_0$],
)
#v(3mm)
#text(size:10pt,fill:by-muted)[Receiver intensity after $N$ diffusion steps]
#v(2mm)
#grid(columns:(1fr,1fr,1fr,1fr,1fr),gutter:5mm,align:center,
 string-field(rc.at(0),lattice-count,side:38mm,intensity:true,display-reference:intensity-reference),string-field(rc.at(1),lattice-count,side:38mm,intensity:true,display-reference:intensity-reference),
 string-field(rc.at(2),lattice-count,side:38mm,intensity:true,display-reference:intensity-reference),string-field(rc.at(3),lattice-count,side:38mm,intensity:true,display-reference:intensity-reference),
 [#string-field(rc.at(3),lattice-count,side:38mm,intensity:true,comparison:rc.at(2),display-reference:intensity-difference-reference)\ $frac(Delta I_N,norm(Delta I_N)_infinity)$],
)
#v(3mm)
#eq[$u_(3,k)=frac(8u_(4,k)+6u_(2,k),14), quad Delta u_k=frac(u_(4,k)+u_(2,k),2)-u_(3,k)$]
#caption([*Proved-derived / exact coefficient witness.* Here $c=2,3,4$ selects the displayed output port and $k$ counts diffusion steps. Linear diffusion preserves the weighted union at every step. Intensity is read after currents combine. The signed difference retains the blue/red comparison gauge. The last column shows $42 Delta u_0$ and $frac(Delta I_N,norm(Delta I_N)_infinity)$; gray uses the same $I_star$ as plate 6. The exact bound $norm(Delta lambda)_1=1/42$ gives $abs(Delta u_k)<=1/42$ and $abs(Delta I_k)<=1/21$.])

#let qpoint(w)=math.frac(math.vec(..w.num.map(k=>[#k])),[#w.den])
#pagebreak()
#title("08","Real strings as a tetrahedral current","Actual inscriptions supply the stimulus; the chart differentiates their input, output and reference ports.")
#grid(columns:(132mm,1fr),gutter:12mm,
 [
  #align(center,tetrahedron-example())
  #v(3mm)
  #eq[$v_a=(1,1,1), quad v_b=(1,-1,-1)$]
  #eq[$v_c=(-1,1,-1), quad v_r=(-1,-1,1)$]
  #caption([*Regular tetrahedron.* $v_k dot v_k=3$ and $v_k dot v_l=-1$ for $k != l$; every squared edge length is $8$. The shaded section carries the addition constraint.])
 ],
 [
  #text(size:12pt,weight:"semibold")[Three source inscriptions, one explicit codec]
  #v(3mm)
  #table(columns:(10mm,35mm,1fr,12mm,12mm),inset:2mm,stroke:(bottom:.5pt+by-rule),align:(center,left,center,center,center),
   [],[String],[$p=q(a,b,c)$],[$m$],[$delta$],
   ..arithmetic-data.rows.map(row=>(
     [#text(weight:"semibold",fill:if row.residual==0 {by-blue} else {by-red})[#row.label]],
     [#raw(row.source)], [#qpoint(row.point)], [#row.mass], [#row.residual],
   )).flatten(),
  )
  #v(3mm)
  #eq[$tilde(h)=(a,b,c,1), quad m=a+b+c+1, quad lambda=tilde(h)/m$]
  #eq[$q(a,b,c)=lambda_a v_a+lambda_b v_b+lambda_c v_c+lambda_r v_r$]
  #eq[$lambda_k=frac(1+v_k dot p,4), quad (a,b,c)=frac((lambda_a,lambda_b,lambda_c),lambda_r)$]
  #caption([*Definition / exact source chart.* Canonical strings #raw("a+b=c") enter at integer currents. The chart extends to $h=(a,b,c) in QQ_(>=0)^3$. The reference weight $1$ makes $lambda_r>0$, so the triple is recoverable. Parsing remains exterior.])
 ],
)
#v(4mm)
#eq[$delta(a,b,c)=a+b-c, quad hat(delta)(p)=frac(1+3p_x-p_y+p_z,1-p_x-p_y+p_z)=delta(q^(-1)(p))$]
#eq[$delta=0 quad ⇔ quad lambda_a+lambda_b=lambda_c quad ⇔ quad 1+3p_x-p_y+p_z=0$]
#caption([*Proved-derived / exact rational witness.* A and B share the addition face but retain different geometric points. C has defect $-1$. The drawing uses camera $(x,y,z) mapsto (x+z/2,y+z/4)$; the complete rational 3D points remain in the table and source receipt.])

#pagebreak()
#title("09","Reflection closes the same face in both charts","The integration law is explicit; the normalized geometric chart transports its weights.")
#grid(columns:(1fr,1fr),gutter:14mm,
 [
  #text(size:13pt,weight:"semibold")[Hold the two inputs; reflect the output current]
  #eq[$S_(A)(a,b,c)=(a,b,2(a+b)-c), quad S_A^2=I$]
  #eq[$U_A=frac(I+S_A,2), quad U_(A)(a,b,c)=(a,b,a+b)$]
  #align(center,diagram(spacing:(17mm,7mm),node-inset:3mm,label-size:10pt,
    node((0,0),[$(1,2,4)$\ #raw("1+2=4")],stroke:.7pt+by-red),
    node((1,0),[$(1,2,2)$\ #text(size:9pt)[reflected current]],stroke:.7pt+by-rule),
    node((.5,1),[$(1,2,3)$\ #raw("1+2=3")],stroke:.7pt+by-blue),
    arr((0,0),(1,0),label:[$S_A$]),
    arr((0,0),(.5,1),label:[$1/2$]),arr((1,0),(.5,1),label:[$1/2$]),
  ))
  #eq[$delta(S_A h)=-delta(h), quad delta(U_A h)=0$]
  #caption([*Proved-derived.* The arithmetic reflection reverses the signed defect. Its midpoint closes the relation while retaining $a$ and $b$. This example integrates a current under a supplied addition law.])
 ],
 [
  #text(size:13pt,weight:"semibold")[The complete square now commutes]
  #align(center,diagram(spacing:(25mm,15mm),label-size:10pt,node-inset:2mm,
    node((0,0),$(1,2,4)$),node((1,0),$(1,2,3)$),
    node((0,1),$p_4=frac((-1,1,-2),4)$),node((1,1),$p_3=frac((-1,1,-3),7)$),
    arr((0,0),(1,0),label:[$U_A$]),arr((0,1),(1,1),label:[$U_B$]),
    arr((0,0),(0,1),label:[$q$],label-side:left),arr((1,0),(1,1),label:[$q$]),
  ))
  #eq[$p_2=q(1,2,2)=frac((0,0,-1),3)$]
  #eq[$U_(B)(q(h))=frac(m(h) q(h)+m(S_A h) q(S_A h),m(h)+m(S_A h))$]
  #eq[$U_(B)(p_4)=frac(8p_4+6p_2,14)=p_3$]
  #eq[$m_4=1+2+4+1=8, quad m_2=1+2+2+1=6$]
  #caption([*Proved-derived.* Normalization changes affine averaging. For $h$ and $S_A h$ in the admitted chart, the weights follow from their source currents and reference port.])
 ],
)
#v(5mm)
#grid(columns:(1fr,1fr),gutter:14mm,
 [
  #text(size:12pt,weight:"semibold",fill:by-blue)[Face-conserving integration]
  #eq[$Delta_(q)(h)=q(U_A h)-U_(B)(q(h))=0$]
  #eq[$hat(delta)(U_(B)(q(h)))=delta(U_A h)=0$]
  #caption([Same source, same declared comparison, same resulting face. The induced geometric update is now exhibited, rather than left as an unspecified condition.])
 ],
 [
  #text(size:12pt,weight:"semibold",fill:by-red)[An untransported midpoint leaves a defect]
  #eq[$p_("naive")=frac(p_4+p_2,2), quad q^(-1)(p_("naive"))=(1,2,20/7)$]
  #eq[$hat(delta)(p_("naive"))=1+2-20/7=1/7 != 0$]
  #caption([The Euclidean midpoint in this chart represents a different update. Retaining the chart weights restores the commuting square.])
 ],
)
#v(4mm)
#caption([*Exact rational witness.* #raw("arithmetic-example.py") generates the source receipt used by the figure and verifies reconstruction, reflection, closure, and the $1/7$ control. This is an exterior arithmetic construction, not a claim of learned HNN parsing or a general native training algorithm.])

#pagebreak()
#title("10","Color from relations; depth from the current","An opaque realization of the existing quadratic color receiver, over oriented triangular faces.")
#grid(columns:(1fr,1.2fr,1fr),gutter:10mm,
 [#text(size:13pt,weight:"semibold")[Same field, top view]
  #v(4mm)#align(center,surface-tile(arithmetic-data.rows.at(0).barycentric,0,side:150mm,flat:true))
 ],
 [#text(size:13pt,weight:"semibold")[Signed height $z=u$]
  #v(7mm)#align(center,surface-tile(arithmetic-data.rows.at(0).barycentric,0,side:95mm))
 ],
 [#text(size:13pt,weight:"semibold")[One declared receiver]
  #eq[$g=(partial_x u,partial_y u), quad A=g_x+upright(i)g_y$]
  #eq[$P=(g_x^2,g_y^2,(g_x+g_y)^2)$]
  #eq[$C=frac(P,max_j P_j)$]
  #grid(columns:(1fr,1fr),gutter:4mm,
    [#rect(width:13mm,height:6mm,fill:primary-color(1,0),stroke:none)\ $(g_x,g_y)=(1,0)$],
    [#rect(width:13mm,height:6mm,fill:primary-color(0,1),stroke:none)\ $(0,1)$],
    [#rect(width:13mm,height:6mm,fill:primary-color(1,-1),stroke:none)\ $(1,-1)$],
    [#rect(width:13mm,height:6mm,fill:primary-color(1,1),stroke:none)\ $(1,1)$],
  )
  #v(4mm)#caption([Base-chart slopes on each affine triangle combine before the quadratic response. No hue is assigned by string or correctness. Zero slope is neutral; opacity is fixed.])
 ],
)
#v(5mm)
#grid(columns:(1fr,1fr),gutter:12mm,
 [#eq[$partial [a,b,c]=[b,c]-[a,c]+[a,b], quad partial^2=0$]
  #caption([*Source-inspected construction.* Two oriented triangles per grid square, sharing the original samples. The graph has height $u$; its diagonal seams are presentation edges, not added diffusion contacts. An intrinsic simplicial solver would also need its incidence, metric and Hodge weights.])],
 [#eq[$r_j=frac(P_j,kappa+sum P), quad sum r_j=alpha, quad alpha+tau=1$]
  #caption([*Existing receiver law.* This is the one-current specialization of #raw("ExactReceiverPrimaryDoctrine"). The opaque display removes coverage and calibrates chromatic ratios. $C(g)=C(-g)$ remains an exhibited color fibre; height and the retained current carry the missing distinction.])],
)
#v(5mm)
#caption([*Interpretation / exterior realization.* Color shows a receiver-relative relation between face slopes, not physical wavelengths. The camera is $(x,y,z) mapsto (x-y,z-(x+y)/2)$. Source owners: #raw("dimensional_wave.rs"), #raw("presentation_gauge.rs"), and #raw("simplicial.rs"). Changing this color gauge changes no source coefficient or transition.])

#pagebreak()
#title("11","Transport the camera and the dynamics together","The repaired input binding makes addition's input swap an actual geometric symmetry.")
#grid(columns:(1fr,1fr,1fr),gutter:10mm,align:center,
 [*1+2=3: reference view*\ #surface-tile(arithmetic-data.rows.at(0).barycentric,lattice-count,side:80mm)],
 [*2+1=3: same fixed camera*\ #surface-tile(arithmetic-data.rows.at(1).barycentric,lattice-count,side:80mm)],
 [*2+1=3: transported view and receiver*\ #surface-tile(arithmetic-data.rows.at(1).barycentric,lattice-count,side:80mm,rechart:true)],
)
#eq[$u_(a,b,c)=frac(a psi_(2,1)+b psi_(1,2)+c psi_(1,1)+psi_(2,2),a+b+c+1)$]
#eq[$E P=J E, quad (J u)(i,j)=u(j,i), quad D J=J D, quad rho_B J=rho_A$]
#caption([*Proved-derived / exact incidence witness.* Here $E$ maps port weights to fields and $P$ swaps the inputs. Their modes have equal decay, $eta_(2,1)=eta_(1,2)$. The earlier binding exchanged $psi_(1,1)$ and $psi_(2,1)$, whose decay differs; camera motion alone could not repair that. Reindexing the face chart also transports the two color channels.])
#v(3mm)
#grid(columns:(1fr,1fr,1fr),gutter:10mm,align:center,
 [*1+2=2*\ #surface-tile(arithmetic-data.field.reflection_cases.at(1),8*lattice-count,side:50mm,leading-normalized:true)],
 [*1+2=3*\ #surface-tile(arithmetic-data.field.reflection_cases.at(2),8*lattice-count,side:50mm,leading-normalized:true)],
 [*1+2=4*\ #surface-tile(arithmetic-data.field.reflection_cases.at(0),8*lattice-count,side:50mm,leading-normalized:true)],
)
#eq[$frac(u_k,lambda_c eta_(1,1)^k) arrow.r psi_(1,1), quad eta_(m,n)=frac(cos(m pi/(N+1))+cos(n pi/(N+1)),2)$]
#caption([*Counterexample to fusion as an arithmetic test.* For $lambda_c>0$, this lower diagnostic divides by the stated leading mode. All three cases approach the same normalized shape; raw amplitude decays to zero. The mesh remains one disk throughout. Visible level sets are not its outer boundary, and scalar-gradient circulation is $d(d u)=0$: curved contours alone do not establish vortical current.])

#pagebreak()
#title("12","Diffusion, stimulus, and learned reconstruction","The informative comparison is what changes a conditional continuation, and what the retained state preserves.")
#grid(columns:(1fr,1fr),gutter:16mm,
 [#text(size:14pt,weight:"semibold")[The present exact field family]
  #align(center,diagram(spacing:(16mm,12mm),label-size:10pt,
    node((0,0),[$lambda$\ four port weights]),node((1,0),[$u=E lambda$\ current field]),
    node((0,1),[$H lambda$\ retained modes]),node((1,1),[$D u$\ diffused field]),
    arr((0,0),(1,0),label:[$E$]),arr((0,0),(0,1),label:[$H$]),
    arr((1,0),(1,1),label:[$D$]),arr((0,1),(1,1),label:[$E$]),
  ))
  #eq[$D E=E H, quad H=op("diag")(eta_(2,1),eta_(1,2),eta_(1,1),eta_(2,2))$]
  #eq[$E^+=frac(4,(N+1)^2)E^top, quad E^+ E=I_4$]
  #caption([*Proved-derived.* Four coefficients retain this complete admitted field family and its future diffusion. Finite sine orthogonality gives the displayed decoder, exact on $op("im")E$. Other modes are outside this family. The RGB image is a further quotient.])
  #v(5mm)
  #text(size:12pt,weight:"semibold")[What “noise” means here]
  #v(2mm)
  #text(size:10pt)[The inscription is actual stimulus. Its unseparated distinctions are relative to the receiver. This example supplies an arithmetic chart and a diffusion law; it does not learn the chart or a denoising law from exposure.]
 ],
 [#text(size:14pt,weight:"semibold")[Classical learned diffusion]
  #align(center,diagram(spacing:(18mm,10mm),label-size:10pt,
    node((0,0),[$x_0$\ observed data]),node((1,0),[$x_t$\ corrupted state]),
    node((1,1),[$epsilon_(theta)(x_t,t,c)$\ learned conditional response]),
    node((0,1),[$x_(t-1)$\ next generated state]),
    arr((0,0),(1,0),label:[declared corruption]),arr((1,0),(1,1)),arr((1,1),(0,1),label:[reverse step]),
  ))
  #eq[$x_t=sqrt(overline(alpha)_t)x_0+sqrt(1-overline(alpha)_t)epsilon, quad epsilon tilde cal(N)(0,I)$]
  #eq[$overline(alpha)_t=product_(s=1)^t (1-beta_s)$]
  #text(size:10pt)[DDPM trains the reverse response across noise levels. Its success comes from the learned data-dependent return, not the forward smoothing alone. Probability-flow ODEs also admit deterministic generation once the initial state is fixed.]
  #v(3mm)
  #text(size:10pt)[Cold Diffusion studies learned reversal of deterministic corruptions, including blur. Latent diffusion learns an autoencoder, then models the latent distribution; reconstruction quality alone does not certify topology or future-state equivalence.]
 ],
)
#v(7mm)
#align(center,diagram(spacing:(14mm,7mm),node-inset:2mm,
 node((0,0),[Actual stimulus]),node((1,0),[Conditioned local relation]),node((2,0),[Returned difference]),node((3,0),[Eros: changed reusable conduct]),
 arr((0,0),(1,0)),arr((1,0),(2,0)),arr((2,0),(3,0)),
))
#v(5mm)
#caption([*Interpretation to develop.* A meaningful “fusion” must be founded by the admitted interaction, changing incidence or compatible continuation. It can guide generator recovery and Holonic Compression when the relevant future faces survive. Generic blur, visual roundness and byte reconstruction do not supply that law.])
#v(5mm)
#text(size:8.5pt,fill:by-muted)[Primary comparisons:
 #link("https://arxiv.org/abs/2006.11239")[Ho et al., DDPM] /
 #link("https://arxiv.org/abs/2011.13456")[Song et al., score SDEs / probability flow] /
 #link("https://arxiv.org/abs/2208.09392")[Bansal et al., Cold Diffusion] /
 #link("https://arxiv.org/abs/2112.10752")[Rombach et al., latent diffusion].
 Local recovery: July 13 color law; August 9 spectral-receiver synthesis; August 18 geometric-autoencoder review; #raw("HolonicDiffusionCharts.lean").]

#pagebreak()
#title("13","A face state survives a change of alphabet","Recover the held cube's actual n = 17; carry the null, generators, ordering and face receiver together.")
#grid(columns:(1fr,1fr,1fr),gutter:12mm,align:center,
 [#text(size:13pt,weight:"semibold")[The original face map]\
  #v(5mm)#cube-net()\
  #v(4mm)
  #text(size:10pt)[#raw(manifold-data.cube.face_word)]
 ],
 [#text(size:13pt,weight:"semibold")[Re-encoded colors and letters]\
  #v(5mm)#cube-net(renamed:true)\
  #v(4mm)
  $rho^(-1)" decodes the same state"$
 ],
 [#text(size:13pt,weight:"semibold")[The action travels too]
  #eq[$r(g dot s)=(r g r^(-1)) dot r(s)$]
  #eq[$phi'=rho compose phi compose r^(-1)$]
  #v(3mm)#caption([*Recovered computational witness.* The board returns #raw("R U'") at index 17 and birth moment 2. A color relabeling moves no source sticker. A spatial rechart conjugates the move alphabet. The enumeration order travels when the numerical address is retained.])
 ],
)
#v(8mm)
#grid(columns:(1fr,2fr),gutter:16mm,
 [#align(center,root-action())],
 [#text(size:13pt,weight:"semibold")[An actual Galois action on the geometric coefficients]
  #eq[$K=QQ(zeta_(16)), quad zeta_(16)^8=-1, quad sigma_5:zeta_(16) mapsto zeta_(16)^5$]
  #eq[$sigma_5^4=I, quad sigma_(5)(u v)=sigma_(5)(u)sigma_(5)(v)$]
  #caption([*Exact cyclotomic witness.* The visible orbit is $1 arrow.r 5 arrow.r 9 arrow.r 13 arrow.r 1$. This field automorphism preserves the rational relations used on plate 15. It acts on coefficients and is not assumed to preserve geometric distance.])
 ],
)
#v(5mm)
#caption([*Definition.* God's number is the maximal shortest-word distance for the declared finite group and move alphabet. The board's 17 is an enumeration address. Its generator-relative depth is 2. Sources: the recovered #raw("RubikBoard.dc.html"), the August 30 action/shell records, and #link("https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Cyclotomic/Gal.html")[Mathlib's cyclotomic Galois construction].])

#pagebreak()
#title("14","Closed cartography carries independent circulation","A periodic triangular complex: no outer square boundary, two noncontractible cycles, and a local curl return.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Exact current*\ $j=d f$\
  #v(3mm)#torus(kind:"exact",side:72mm)],
 [*Add the two cycle currents*\ $j=d f+p omega_theta+q omega_phi$\
  #v(3mm)#torus(kind:"cycles",side:72mm,loops:true)],
 [*Add a coexact local current*\ $j=d f+p omega_theta+q omega_phi+s kappa$\
  #v(3mm)#torus(kind:"full",side:72mm,loops:true)],
)
#eq[$V=N^2=256, quad E=3N^2=768, quad F=2N^2=512, quad chi=V-E+F=0, quad partial K=0$]
#eq[$∮_(gamma_theta) omega_theta=∮_(gamma_phi) omega_phi=1, quad d omega_theta=d omega_phi=0, quad kappa=partial_2[f_0]$]
#eq[$U_e=e^(2 pi upright(i) j_e), quad cal(H)_f=product_(e in partial f) U_e^(epsilon_(f,e))=e^(2 pi upright(i)(d j)_f)$]
#v(3mm)
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Edge heat: k = 0*\
  #torus(k:0,side:43mm)],
 [*k = 1*\
  #torus(k:1,side:43mm)],
 [*k = 4*\
  #torus(k:4,side:43mm)],
)
#eq[$j_(k+1)=(I-L_1/10)j_k, quad L_1=partial_1^top partial_1+partial_2 partial_2^top$]
#caption([*Exact incidence/Hodge witness; curved realization.* Indices are periodic modulo $N$, with angles $2 pi i/N$. Unit cochain metric; $10$ is the derived absolute-row-sum bound. The harmonic coordinates $(p,q)=(1/7,2/7)$ use Gram matrix $mat(2,1;1,2)$ against $(omega_theta,omega_phi)$ and survive; the local curvature diffuses. Initially $d kappa$ has values $(3,-1,-1,-1)$ on four faces. Color reads intrinsic edge components; blue/red traces mark complete cycles, including occluded segments. The embedding follows $f_k$; its induced metric is separate from this unit cochain metric and is compared on plate 15.])

#pagebreak()
#title("15","Compare the manifolds themselves","One source-addressed torus carrier; retain signed displacement, induced metric change, and the full comparison.")
#grid(columns:(1fr,1fr),gutter:14mm,align:center,
 [*Difference from 1+2=3 to 1+2=2*\ $Delta X_2=X_2-X_3$\
  #torus(difference:2,side:90mm)],
 [*Difference from 1+2=3 to 1+2=4*\ $Delta X_4=X_4-X_3$\
  #torus(difference:4,side:90mm)],
)
#eq[$X_(c)(theta,phi)=((R+r_c cos phi)cos theta,(R+r_c cos phi)sin theta,r_c sin phi), quad R=2, quad r_c=1+f_c/4$]
#eq[$f_c=frac(cos theta+2cos phi+c cos(theta+phi)+cos(theta-phi),c+4), quad c in {2,3,4}$]
#eq[$6X_2+8X_4=14X_3, quad Delta X_2=-frac(4,3)Delta X_4$]
#caption([*Proved-derived / exact cyclotomic witness.* The embeddings are compared at the same source parameters. The declared reference has tube radius $1$ and $R=2$, with $epsilon=1/(2R)=1/4$; $3/4<=r_c<=5/4<R$ keeps the smooth family embedded. Blue arrows point outward, red inward; lengths are explicitly magnified by $42/(8 epsilon)$ and $56/(8 epsilon)$ with $epsilon=1/4$. These are differences of parametrized embeddings, not subtraction of unlabeled point sets.])
#v(4mm)
#grid(columns:(1fr,1fr),gutter:12mm,
 [#text(size:12pt,weight:"semibold")[The metric keeps the nonlinear remainder]
  #eq[$g_c=(D X_c)^top D X_c, quad Q=(D Delta X_2)^top D Delta X_2$]
  #eq[$Delta g_4+frac(3,4)Delta g_2=frac(21,16)Q$]
  #caption([Point displacement is proportional, but metric change also contains the quadratic term. The exact nonzero matrix is retained in the source receipt.])],
 [#text(size:12pt,weight:"semibold")[The rational relation survives Galois transport]
  #eq[$sigma_(5)(Delta X_2)=-frac(4,3)sigma_(5)(Delta X_4)$]
  #caption([At the 16th-root mesh, the coordinates lie in $QQ(zeta_(16))$ and $sigma_5$ fixes the rational comparison coefficients. All 256 sampled vector identities and the metric remainder at one declared point are checked exactly.])],
)

#pagebreak()
#title("16","Intersecting fields: interior paths and boundary faces","Two source volumes meet in an actual overlap. A declared local operation relates their currents there.")
#grid(columns:(1.15fr,1fr),gutter:14mm,
 [#align(center,overlap())
  #eq[$V_L={abs(x+1)+abs(y)+abs(z)<=2}, quad V_R={abs(x-1)+abs(y)+abs(z)<=2}$]
  #eq[$K=V_L inter V_R={abs(x)+abs(y)+abs(z)<=1}, quad op("Vol")(K)=4/3$]
 ],
 [#text(size:13pt,weight:"semibold")[The full signed face map]
  #v(4mm)#align(center,flux-faces())
  #eq[$J_L=(x+1,y,z), quad J_R=(x-1,y,z), quad Delta J=(-2,0,0)$]
  #eq[$Phi_(L)(sigma)=frac(1+sigma_x,2), quad Phi_(R)(sigma)=frac(1-sigma_x,2)$]
  #eq[$Delta Phi(sigma)=-sigma_x, quad sum_sigma Delta Phi(sigma)=0$]
  #caption([Every triangle retains its outward sign triple. Four faces read $+1$ and four read $-1$ although the aggregate vanishes. The declared overlap operation can retain the pair, add it, or read this difference.])
 ],
)
#v(4mm)
#grid(columns:(1fr,1fr),gutter:14mm,
 [#text(size:12pt,weight:"semibold")[Gauss: volume source to surface flux]
  #eq[$integral_K nabla dot J_L dif V=3(4/3)=4=integral_(partial K) J_L dot n dif A$]
  #eq[$partial[V_L]+partial[V_R]=partial[V_L union V_R]+partial[K]$]
  #caption([*Exact polyhedral calibration.* Common refinement cancels internal faces with their orientations. The same identity gives flux 8 for $J_L+J_R$ and 0 for $Delta J$.])],
 [#text(size:12pt,weight:"semibold")[Stokes: compare actual paths with the same ends]
  #eq[$integral_(gamma_("inside")) Delta J dot dif l=integral_(gamma_("surface")) Delta J dot dif l=-4$]
  #eq[$Delta J=nabla(-2x), quad ∮_(partial S) Delta J dot dif l=0$]
  #caption([The dashed diameter $P arrow.r Q$ and the surface path $P arrow.r R arrow.r Q$ have the same integral because this difference field is exact. Zero total flux alone would not establish this path equality or reconstruct the interior.])],
)
#v(3mm)
#caption([*Proved-derived / exact rational witness.* Dimensionless Euclidean volumes; outward area vectors $sigma/2$ and face centroids $sigma/3$. Source, overlap, operation and receiver are explicit. The exterior script verifies all eight face returns, the volume identity and both path integrals.])

#pagebreak()
#title("17","A bridge can reverse the frame it carries","The same disk-and-ribbon construction: preserve incidence, then change the attachment and the available loops.")
#grid(columns:(1fr,1fr,1fr),gutter:7mm,align:center,
 [*Annulus: an untwisted passage*\
  #v(3mm)#ribbon-surface(kind:"annulus",side:78mm)\
  $chi=0, quad b=2, quad epsilon(a)=+1$],
 [*Möbius band: an orientation-reversing passage*\
  #v(3mm)#ribbon-surface(kind:"mobius",side:78mm)\
  $chi=0, quad b=1, quad epsilon(a)=-1$],
 [*Möbius shorts: add a second loop*\
  #v(3mm)#ribbon-surface(kind:"shorts",side:78mm)\
  $chi=-1, quad b=1, quad (epsilon(a),epsilon(b))=(-1,+1)$],
)
#v(3mm)
#grid(columns:(1fr,1fr),gutter:12mm,
 [#text(size:12pt,weight:"semibold")[Read the reversal from adjoining triangles]
  #eq[$epsilon_g=-h_(f e)h_(g e)epsilon_f, quad epsilon(gamma)=product_(e in gamma)(-h_(f e)h_(g e))$]
  #caption([*Exact incidence witness.* Shared-edge signs $h$ transport local face orientation. A loop product $-1$ prevents a global choice; it does not break local transport. Black traces show the complete boundary; red cross-arrows show the ribbon frame. The upper ribbon is $a$, the lower added ribbon is $b$.])],
 [#text(size:12pt,weight:"semibold")[The “bridge” has declared contact ports]
  #eq[$X arrow.l W arrow.r Y, quad T_gamma:V_X arrow.r V_Y, quad det(T_a)=-1$]
  #caption([*Construction.* Mark attachment arcs as ports. The passage retains its local charts and reversing transport. Shorts have one boundary component: its two apparent legs are independent loops. The disk and both ribbons are embedded in three dimensions; a projected crossing introduces no new contact.])],
)
#v(4mm)
#eq[$c_a(t)=(-cos t,0,2sin t), quad e_a(t)=(frac(-2sin t cos t,ell),cos t,frac(sin^2 t,ell)), quad ell=sqrt(sin^2 t+4cos^2 t)$]
#eq[$c_b(t)=(0,-cos t,-2sin t), quad e_b=(1,0,0), quad X_a=c_a+v e_a, quad X_b=c_b+v e_b, quad abs(v)<=1/3$]
#caption([*Defined realization.* $0<=t<=pi$; the untwisted control uses $e_a=(0,1,0)$. Half-width $w=1/3$ is a declared embedding parameter. The ribbons meet the disk only at their attachments. Opaque color reads the unoriented face-normal line through $g=(n_x+n_z,n_y+n_z)$ and the prior primary response: $C(n)=C(-n)$. Both sides are drawn. Color therefore retains local shape while its sign fibre remains explicit. Möbius shorts are a Klein bottle with an open disk removed: #link("https://archive.bridgesmathart.org/2020/bridges2020-121.pdf")[Bridges 2020, figure 11].])

#pagebreak()
#title("18","One-sided interior, orientable surrounding boundary","Carry orientation as transport data; thicken the embedded object when the receiver needs an ordinary outward flux.")
#grid(columns:(1fr,1fr,1fr),gutter:9mm,align:center,
 [*The orientation cover*\
  #v(6mm)#cover-seam()\
  #eq[$pi:tilde(S) arrow.r S, quad tau^2=I$]
  #caption([A Möbius circuit exchanges sheets. For shorts the connected cover is a torus with two boundary circles: $chi=-2$, $g=1$, $b=2$. The sheets record local orientation over one object.])],
 [*Close the cover's two rims*\
  #thickened-shorts(side:65mm)\
  #eq[$partial N(S)=tilde(S) union_(partial tilde(S)) (partial S times I)$]
  #caption([The boundary of a regular neighborhood of shorts is a closed orientable genus-2 surface. Yellow triangles join the cover along the original boundary. The chosen offset is $w/4=1/12$ for $w=1/3$, not a recovered thickness law. Plate 20 continues into actual volumes and world tubes.])],
 [*Two paths can return different currents*\
  #v(4mm)#transport-square()\
  #eq[$A=mat(1,0;0,-1), quad B=mat(0,-1;1,0)$]
  #eq[$(B A-A B)(1,2)=(4,2)$]
  #caption([*Exact declared connection.* The two returns are $(2,1)$ and $(-2,-1)$. Both have squared norm 5 and the same quadratic primary color. The retained oriented difference separates them.])],
)
#v(5mm)
#grid(columns:(1fr,1fr),gutter:12mm,
 [#text(size:12pt,weight:"semibold")[Generalize through a transported local system]
  #eq[$T:Pi_1(S) arrow.r "Vect", quad T_(gamma_2 gamma_1)=T_(gamma_2)T_(gamma_1)$]
  #eq[$epsilon:pi_1(S) arrow.r {+1,-1}, quad z(theta+2pi)=-z(theta)$]
  #eq[$L tau^*=tau^* L, quad tau^*u=plus.minus u ⇒ tau^*((I-h L)u)=plus.minus (I-h L)u$]
  #caption([*Construction / exact incidence witness.* $L$ is the cover's unit vertex Laplacian, $h=1/(2d_(max))$ from its maximal degree. Diffusion preserves even scalars or odd orientation-valued coefficients. A continuous real odd section on a reversing loop must have a zero. The flat connection $T$ carries paths; its noncommutativity is not forced by reversal alone.])],
 [#text(size:12pt,weight:"semibold")[Gauss survives with the appropriate carrier]
  #eq[$integral_S op("div")J dif mu=integral_(partial S) ⟨J,nu⟩ dif s$]
  #eq[$integral_(N(S)) nabla dot J dif V=integral_(partial N(S)) J dot n dif A$]
  #caption([*Proved-derived.* Riemannian intrinsic divergence uses a density and outward boundary conormal $nu$, so it needs no global surface normal. Ambient Gauss uses the orientable shell of the thickening. Orientation-valued forms on $S$ can be represented on its cover with the corresponding deck sign.])],
)
#v(4mm)
#caption([*Source-inspected precedent.* #link("https://www.nature.com/articles/s41586-023-06022-7")[Guo et al., Nature 618 (2023)] construct non-orientable order and order-sensitive mechanical responses. The matrices here are a separate exterior calibration. *HNN interpretation:* retain the path, local frame and return through the addressed passage; a condensation owes $q_Y T_gamma=U_gamma q_X$ for the admitted future family. Source incidence and the orientation cover establish topology; no learned semantic bridge is inferred from a rendering.])

#pagebreak()
#title("19","The compared response keeps its producing state","Equational congruence becomes useful architecture equality through typed sources, receivers and successor transport.")
#align(center,diagram(
 node-outset:1pt,edge-stroke:.7pt+by-black,label-size:9pt,
 n((0mm,0mm),<source19>,[Incoming source section],$o$,width:46mm),
 n((66mm,0mm),<state19>,[Act on the actual joint],$z_s=T_(M,o) z$,width:52mm),
 n((132mm,0mm),<predict19>,[Generate its response],$hat(v)=c_s+M phi(z_s)$,width:58mm),
 n((204mm,0mm),<emit19>,[Read the emitted face],$y=b(hat(v))$,width:54mm,tone:by-red),
 n((66mm,-25mm),<producer19>,[Retain the producing passage],$(z_s,M,b,kappa)$,width:57mm,tone:by-red),
 n((204mm,-25mm),<observed19>,[Addressed observed return],$(v,b_v;"producer")$,width:54mm,tone:by-red),
 n((132mm,-50mm),<difference19>,[Compare in the common chart],$delta=b_(v)(v)-b(hat(v))$,width:59mm,tone:by-red),
 n((66mm,-75mm),<develop19>,[Develop one complete successor],$(M^+,z^+,cal(F)^+,kappa^+)$,width:65mm,tone:by-red),
 arr(<source19>,<state19>),arr(<state19>,<predict19>),
 edge(<state19>,<producer19>,"-->",stroke:by-red),
 edge(<predict19>,<emit19>,"-->",stroke:by-red),
 edge(<emit19>,<observed19>,"-->",stroke:by-red),
 edge(<observed19>,<difference19>,"-->",stroke:by-red),
 edge(<producer19>,<difference19>,"-->",stroke:by-red),
 edge(<difference19>,<develop19>,"-->",stroke:by-red),
 edge("-->",vertices:(<develop19>,(0mm,-75mm),(0mm,-25mm),<state19>),stroke:by-red,label:[next occurrence]),
))
#v(2mm)
#caption([*Source-inspected architecture / construction.* Blue boxes have returned local owners. Red paths name the next composed receiver/development binding. A later correction of $hat(v)$ retains its producing $z_s$; the current #raw("receive(v)") method instead means an actual next current. The same ordinary occurrence can carry source and comparison with one final successor.])
#v(4mm)
#grid(columns:(1fr,1fr),gutter:12mm,
 [*One observed value, two different causal equations*
  #eq[$z=(0,1), quad P=(1/2,1/2,0), quad hat(v)=2, quad v=3$]
  #eq[$P_("correction")^+=(7/10,7/10,0), quad P_("next")^+=(1/2,3/8,-1/8)$]
  #caption([*Exact normal-reference witness.* Prior $phi_0=(1,1,0),eta_0=3/2$ gives $H=I+phi_0 phi_0^top$, $P=B H^(-1)$. Correction uses $phi=(1,1,0),eta=2$; next-current reception uses $phi=(1,2,1),eta=1$.])],
 [*A law survives only in the right carrier*
  #eq[$a diamond b=(a+b)/2, quad (0 diamond 0)diamond 4=2 != 1=0 diamond(0 diamond 4)$]
  #eq[$(s,m)+(t,n)=(s+t,m+n), quad q(s,m)=s/m, quad m,n>0$]
  #caption([*Exact witness.* Means are commutative but lose associativity when weight is discarded. Retaining weight restores the join. #link("https://github.com/teorth/equational_theories")[ETP] supplies implication/congruence and explicit countermodels; our future-receiver law supplies the admitted dynamic scope.])],
)

#pagebreak()
#title("20","Polygonal bodies continue as world tubes","Exact vertices, triangular faces, an internal material current, and a source law that moves the complete body.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Two linked polyhedral bodies*\ $tau=0$\
  #linked-bodies(t:0,side:72mm)],
 [*Material shear*\ $tau=1/2$\
  #linked-bodies(t:1/2,side:72mm)],
 [*Same linking; changed embedding*\ $tau=1$\
  #linked-bodies(t:1,side:72mm)],
)
#eq[$F_(tau)(x,y,z)=(x+tau z,y,z), quad det D F_tau=1, quad u=(z,0,0), quad p="constant"$]
#eq[$partial_tau u+(u dot nabla)u=-nabla p+nu Delta u=0, quad nabla dot u=0$]
#caption([*Proved-derived / exact rational witness.* Both centerlines are integral rectangles; one pierces the other's oriented spanning disk once, so $op("lk")=-1$. Minimum $ell_infinity$ separation is $d=1$; choose $r=d/4$ with $2r<d$. Each shell encloses a solid torus, with volumes $4$ and $5/2$. White dashed lines expose the interior loops; yellow vertices are their actual corners. Triangles subdivide exact planar faces; color reads the same unoriented normal receiver as plate 17.])
#v(3mm)
#grid(columns:(.8fr,1.2fr),gutter:12mm,
 [#align(center,swept-triangle())
  #eq[$partial W=K_t-K_s+Sigma_("lat"), quad partial^2 W=0$]
  #caption([*Exact chain witness.* A swept triangular face contains three tetrahedra. Internal faces cancel; the two end caps and six lateral triangles remain. A swept spatial volume is one dimension higher.])],
 [*The same current through changing sections*
  #eq[$W={ (tau,x):s<=tau<=t, x in K_tau }$]
  #eq[$integral_(K_t) rho-integral_(K_s)rho+integral_(Sigma_("lat"))J dot n=integral_W op("div")_(tau,x)J$]
  #eq[$∮_(F_tau A)u dot dif l=0, quad ∮_(F_tau B)u dot dif l=-6$]
  #caption([*Conditional Stokes; explicit shear realization.* The lateral flux includes boundary motion. For this shear, polygonal circulation is constant because its change is $tau ∮ z dif z=0$. These are material loops. The example is a local/whole-space Euler–NS source, not periodic finite-energy Millennium data.])],
)
#v(2mm)
#caption([*Recovered owners.* #raw("WorldTube") and #raw("WorldTubePotential") carry addressed clocks and full boundary faces; #raw("ConstitutiveWorldTube") and #raw("FourTorusParametronCurrent") carry their actual current realization. A Möbius band thickens to a solid torus; shorts thicken to a genus-two handlebody. Spatial framing and motion live inside the corresponding world tube. #link("https://www.cs.columbia.edu/cg/rods/")[Discrete Elastic Rods] provides a polygonal-frame dynamics precedent.])
