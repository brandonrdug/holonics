#import "@preview/fletcher:0.5.8": diagram, node, edge
#import "../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-rule, by-muted
#import "geometry.typ": solid, simplex, chambers, relu-fold, wave-tile, tetrahedron-example, arithmetic-data, string-field, lattice-count, intensity-reference, intensity-difference-reference, surface-tile, primary-color

#set document(title: "HNN - Information Chemistry", author: "Brandon Duggan / Holonics", description: "Twelve diagram plates: HNN, relational color, simplicial surfaces, covariant diffusion, reflection, and learned diffusion models.")
#set page(width: 320mm, height: 210mm, margin: (x:16mm,y:13mm), footer: context {
  set text(size:8pt,fill:by-muted)
  [HOLONICS #h(1fr) HNN / INFORMATION CHEMISTRY #h(1fr) #counter(page).display("1") / 12]
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
