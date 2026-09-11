#import "@preview/fletcher:0.5.8": diagram,node,edge
#import "../../packages/holonic-engraving/lib.typ": engrave
#import "../../packages/holonic-receiver/lib.typ": receiver,primary-response
#import "receiver-diagrams.typ": event-cone,pinhole,receiver-slice
#let scenes=json("receiver-scenes.json")
#set document(title:"HNN — Information Chemistry: receiver edition",author:"Brandon Duggan / Holonics",description:"Eleven plates: receiver-derived engraving, complex flow, orientation, entropy, causal frames and shadows.")
#set page(width:320mm,height:210mm,margin:(x:15mm,y:12mm),fill:white,footer:context [
 #set text(size:8pt,fill:rgb("555555"))
 HOLONICS #h(1fr) INFORMATION CHEMISTRY · RECEIVER EDITION #h(1fr) #counter(page).display("1") / 11
])
#set text(font:"Libertinus Serif",size:11pt,fill:black)
#set par(leading:0.55em,spacing:0pt)
#let title(n,body,sub)=[
 #text(size:9pt,tracking:1pt)[PLATE #n]
 #v(2mm)#text(size:26pt,weight:"semibold")[#body]
 #v(2mm)#text(size:11pt)[#sub]
 #v(6mm)
]
#let eq(m)=block(above:2mm,below:2mm,math.equation(m.body,block:true))
#let note(body)=text(size:9pt,fill:rgb("444444"),body)
#let fig(name,width:85mm,mode:"phase",stroke:1pt/4)=engrave(scenes.at(name),width:width,mode:mode,line-width:stroke)
#let boxnode(pos,name,body)=node(pos,body,name:name,width:53mm,height:15mm,stroke:(3pt/5)+black,fill:white,inset:2mm)

#title("01","The receiver gives the figure its face","One geometric carrier; line engraving, discrete stippling and coherent phase response are different readings.")
#grid(columns:(1fr,1fr,1fr),gutter:10mm,align:center,
 [*Field contours and foreshortening*\ #v(2mm)#fig("sphere_mono",mode:"mono")],
 [*Intersections of the same level families*\ #v(2mm)#fig("sphere_stipple",mode:"mono",stroke:2pt/5)],
 [*The complex current, read on black*\ #v(2mm)#fig("sphere_phase")],
)
#v(4mm)
#eq[$(K,Z,U) arrow.r R arrow.r ("visible fibre",chi_0,chi_1,P) arrow.r "engraved face"$]
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The geometry is upstream of the texture.*
 #v(2mm)#note([Exact rational stations and triangular incidence define the finite carrier. Hatches are level traces of supplied receiver fields. The dot pattern uses intersections of those traces; no random seed places structure. The visible mesh is a finite realization of the rational sphere chart.])],
 [*The image keeps a source behind it.*
 #v(2mm)#note([The packet retains complex vertices, currents, face addresses, the receiver and display error. Opaque-surface visibility is decided before paint. A black or unmarked region can be a zero response, an occlusion or a receiver omission; these remain different source records.])],
)
#v(4mm)
#note([*Method recovered.* Fiziko varies stroke width, generator families and visibility to engrave curved objects; vintage-latex separates contours, texture and labels. These are original Typst packages using the existing Holonic receiver laws. White paper is fixed; phase frames are pure black. Sources: #link("https://github.com/jemmybutton/fiziko")[Fiziko], #link("https://github.com/Foadsf/vintage-latex")[vintage-latex].])

#pagebreak()
#title("02","Curvature, folding and orientation have different sources","Curved rational ribbon charts preserve their attachments; the receiver carries their local current into an image.")
#grid(columns:(1fr,1fr,1.3fr),gutter:12mm,align:center,
 [*Möbius shorts · monochrome*\ #v(2mm)#fig("shorts_mono",width:62mm,mode:"mono")],
 [*The same packet geometry · phase*\ #v(2mm)#fig("shorts_phase",width:62mm)],
 [*A closed orientable carrier*\ #v(4mm)#fig("torus_phase",width:104mm)\
  #eq[$chi("torus")=0, quad chi("shorts")=-1$]
  #note([The torus is orientable. Shorts have one boundary and an orientation-reversing loop. Their appearance under projection proves neither fact; the incidence witness does.])],
)
#v(3mm)
#eq[$epsilon_g=-h_(f e)h_(g e)epsilon_f, quad product_(gamma)(-h_(f e)h_(g e))=-1$]
#grid(columns:(1fr,1fr),gutter:12mm,
 [#note([*Exact finite construction.* The ribbon uses a rational transverse frame whose squared length is $1-frac(3sin^4 t,4)$. Its width therefore varies along the curved chart. The earlier unit-normal ribbon and its chosen $1/12$ shell offset remain in the companion atlas.])],
 [#note([*Receiver distinction.* A polyhedral source has curvature concentrated at its edges. A projection may flatten a curved source. Intrinsic nonorientability is a separate failure of global orientation, while local transport and receiver-relative orientation remain available.])],
)

#pagebreak()
#title("03","A complete complex current drives the motion","An exact holomorphic Euler–NS source on C³; no Fourier-reality condition discards the imaginary field.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*$tau=0$*\ #v(2mm)#fig("flow_0_1",width:90mm)],
 [*$tau=1/2$*\ #v(2mm)#fig("flow_1_2",width:90mm)],
 [*$tau=1$*\ #v(2mm)#fig("flow_1_1",width:90mm)],
)
#eq[$A=mat(0,0,1;0,0,upright(i);1,upright(i),0), quad A^3=0, quad U(Z)=A Z, quad P(Z)=-frac(1,2)(Z_1+upright(i)Z_2)^2$]
#eq[$F_tau=I+tau A+frac(tau^2,2)A^2, quad F_(-tau)F_tau=I, quad det_(CC)F_tau=1$]
#eq[$(U dot nabla)U=A^2 Z=-nabla P, quad Delta U=0, quad nabla dot U=0$]
#v(2mm)
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The two fields interact.*
  #eq[$a_t+(a dot nabla)a-(b dot nabla)b=nu Delta a-nabla p$]
  #eq[$b_t+(a dot nabla)b+(b dot nabla)a=nu Delta b-nabla q$]
 ],
 [#note([*Proved-derived.* $U=a+upright(i)b$, $P=p+upright(i)q$; advection is complex-bilinear. The holomorphic differential is $Delta=sum_j partial_(Z_j)^2$. This polynomial field satisfies the displayed equation for every declared viscosity. The receiving image is a real projection of the full complex flow; the camera and drawing scale are held fixed.])],
)

#pagebreak()
#title("04","A singular image can have a regular source","Keep the complex fibre when a receiver loses directions. A second receiver can expose them again.")
#grid(columns:(1fr,1fr),gutter:12mm,align:center,
 [*Real receiver · $tau=7/5$*\ #v(2mm)#fig("near_fold",width:130mm)],
 [*Changed receiver · same source and clock*\ #v(2mm)#fig("reopened",width:130mm)],
)
#eq[$R_0 F_tau=op("Re")F_tau, quad det_(RR)(R_0F_tau)=lr((1-frac(tau^2,2)))^2$]
#eq[$R_(a,b)(Z)=a op("Re")Z+b op("Im")Z, quad (a,b)=(3/5,4/5)$]
#grid(columns:(1fr,1fr),gutter:12mm,
 [#note([*Proved-derived.* At $tau^2=2$ this real receiver has rank one, while $F_tau$ is invertible. The picture uses rational $tau=7/5$ near that exact singular cut. The source is not replaced by the nearly collapsed image; its complex coordinates and current are retained.])],
 [#note([*Actual folded source.* On the real slice, $a=(x_3,0,x_1)$ and $b=(0,x_3,x_2)$. Dropping $b$ with the same declared real pressure drops $(b dot nabla)b=(0,x_2,x_3)$. This is why the complex evolution cannot generally be continued from its present real face alone.])],
)

#pagebreak()
#title("05","Current and curl have separate receivers","Add a declared rotational current to the same complex source family; read circulation through actual face boundaries.")
#grid(columns:(1fr,1fr),gutter:12mm,align:center,
 [*$lambda=1/2$, $tau=7/5$*\ #v(2mm)#fig("curl_1_2",width:124mm)],
 [*$lambda=1$, $tau=7/5$*\ #v(2mm)#fig("curl_1_1",width:124mm)],
)
#eq[$v=(1,upright(i),0), quad K Z=v times Z, quad A_lambda=S+lambda K, quad U_lambda=A_lambda Z$]
#eq[$A_lambda^2=(1+lambda^2)S^2, quad A_lambda^3=0, quad op("curl")U_lambda=2lambda v$]
#eq[$j_(p q)=frac(U_lambda(p)+U_lambda(q),2) dot (q-p), quad sum_(e in partial f)j_e=op("curl")U_lambda dot "area"_f$]
#note([*Exact complex Stokes instance.* $S$ is the matrix on plate 3; $P_lambda=(1+lambda^2)P_0$. On the oriented triangle $(1,0,0) arrow.r (0,1,0) arrow.r (0,0,1)$, the boundary return is $lambda(1+upright(i))$. Both channels are retained. The hatches/colors read the supplied current, while this independent edge integral reads its curl. The source geometry, rotational contribution and receiver are explicit; a triangle outline alone is no flux measurement.])

#pagebreak()
#title("06","The cross-hatching carries a receiver differential","The line families can read current phase or distributed cross-entropy. Their source functions determine the marks.")
#grid(columns:(1fr,1fr),gutter:14mm,align:center,
 [*Complex-current level families*\ #v(2mm)#fig("torus_phase",width:124mm)],
 [*Distributed cross-entropy families*\ #v(2mm)#fig("torus_entropy",width:124mm)],
)
#eq[$P=(a^2,b^2,(a+b)^2), quad C=P/(kappa+sum_j P_j), quad sum_j C_j+frac(kappa,kappa+sum_j P_j)=1$]
#eq[$q_i=frac(kappa/3+P_i,kappa+sum_j P_j), quad p_i=1/3, quad h_i=-p_i log q_i, quad H=sum_i h_i$]
#grid(columns:(1fr,1fr),gutter:12mm,
 [#eq[$d H=sum_(i) (q_i-p_i) dif s_i quad (q=op("softmax")(s))$]
  #note([*Defined receiver.* The right field uses $h_0,h_1$ as two level families, with the third contribution retained by the source law. Positive support makes the logs defined. Station logs carry rational enclosures; the rendered field is their declared affine triangle reading.])],
 [#eq[$integral_gamma d chi=chi(b)-chi(a)=Delta N+r_b-r_a, quad abs(r_b-r_a)<Delta$]
  #note([*Proved-derived.* Signed crossings of levels $k Delta$ count the quantized potential flux. Endpoint remainders retain what finite line density omits. No hatch direction is assigned by semantic label, and a geometric slope is not silently renamed cross-entropy.])],
)

#pagebreak()
#title("07","The receiver is situated at an event","World-lines, cone membership, orientation and ordered frame changes belong to the reading.")
#grid(columns:(1fr,1fr),gutter:14mm,
 [#align(center,event-cone())
  #eq[$g(u,u)=-1, quad g(k,k)=0, quad omega_R=-g(k,u)$]
  #note([*Declared Lorentz receiver.* A time-oriented metric, observer world-line and tetrad determine the received frequency and direction. Cone membership permits causal influence; actual incidence determines whether that influence occurs.])],
 [#text(size:14pt,weight:"semibold")[The gyroparallelogram retains the order]
  #eq[$L_x=mat(5/4,-3/4,0;-3/4,5/4,0;0,0,1)$]
  #eq[$L_y=mat(5/3,0,-4/3;0,1,0;-4/3,0,5/3)$]
  #eq[$L_y L_x != L_x L_y, quad L^top eta L=eta$]
  #eq[$B_(L_y L_x e_0)L_y L_x=op("diag")lr((1,mat(35/37,-12/37;12/37,35/37)))$]
  #note([*Exact rational return.* The canonical return boost removes the final velocity; a spatial rotation remains. The 37 is produced by the two supplied boosts. This is a flat-spacetime frame instance; a curved GR receiver uses its supplied metric and connection.])],
)
#v(5mm)
#text(size:13pt,weight:"semibold")[A curved metric changes the received frequency]
#eq[$f(r)=1-2/r, quad g=op("diag")lr((-f,f^(-1),r^2,r^2)), quad k=(f^(-1),1,0,0)$]
#eq[$r_("near")=25/8, quad r_("far")=50/9, quad omega_("near")=5/3, quad omega_("far")=5/4, quad frac(omega_("far"),omega_("near"))=3/4$]
#note([*Exact Schwarzschild receiver instance.* $G=c=M=1$ at the equatorial slice; static tetrads are orthonormal, and the radial null ray has unit conserved Killing energy. Its two nontrivial geodesic equations cancel exactly. The frequency ratio follows from the metric and observer; no color is assigned to manufacture a redshift.])
#v(4mm)
#eq[$nabla_a a-nabla_b b, quad nabla_a b+nabla_b a$]
#note([*Complex/GR interface.* Complexifying a declared connection gives these two coupled advection terms. A holomorphic C³ differential is a different chart from a Lorentzian space-time derivative. Their comparison retains the real restriction, tetrad, pressure/source return and any connection defect. No image supplies a stress-energy tensor or Einstein solution by appearance.])

#pagebreak()
#title("08","A shadow retains a path behind its face","Projection, analytic continuation and a physical Feynman diagram have their own source maps.")
#grid(columns:(1fr,1fr),gutter:12mm,
 [#align(center,pinhole())
  #eq[$f(t)=frac(t,1+t/2), quad op("cr")(0,1,2,3)=op("cr")(0,2/3,1,6/5)=4/3$]
  #note([*Exact projective instance.* A noncollapsed line retains its cross-ratio. The pinhole denominator has a pole at $t=-2$; the source point remains defined. Projection does not preserve arbitrary lengths or reconstruct its fibre.])],
 [#text(size:14pt,weight:"semibold")[A hypergeometric face with a retained branch]
  #eq[$F(z)=""_2 F_1(1,1;2;z)=-frac(log(1-z),z)$]
  #align(center,diagram(spacing:(28mm,15mm),
   node((0,0),$(z,w)$),node((1,0),$(z,w+1)$),
   node((0,1),$F_w$),node((1,1),$F_w-2pi upright(i)/z$),
   edge((0,0),(1,0),"->",label:[around 1]),edge((0,0),(0,1),"->"),
   edge((1,0),(1,1),"->"),edge((0,1),(1,1),"->"),
  ))
  #eq[$F_w=F_0-frac(2pi upright(i) w,z), quad w in ZZ$]
  #note([*Derived continuation.* A positive loop around 1 changes the logarithm by $2pi upright(i)$. The winding integer and source branch generate the family; the endpoint $z$ alone does not identify it. Source: #link("https://dlmf.nist.gov/15.4.E1")[DLMF 15.4.1].])],
)
#v(5mm)
#note([*Recovered context.* The August 20 “Shadows of Holonic Interactions” deposit refers to Tufte's physical shadows of Feynman-diagram sculptures. Our formal owner proves polarity and conjugate-line identities. Hypergeometric monodromy supplies the separate analytic example above. Actual Feynman amplitudes require their propagators, couplings and integration/regularization data; a projected drawing does not supply them.])

#pagebreak()
#title("09","The packet carries the construction","A reusable receiver package and an engraving package replace picture-specific paint rules.")
#align(center,diagram(
 node-outset:1pt,edge-stroke:(3pt/5)+black,label-size:9pt,
 boxnode((0mm,0mm),<source>,[Complex vertices, current, incidence]),
 boxnode((72mm,0mm),<receiver>,[Receiver, domain, phase, clock]),
 boxnode((144mm,0mm),<marks>,[Visible level traces and remainders]),
 boxnode((216mm,0mm),<output>,[Typst vectors · SVG · raster face]),
 edge(<source>,<receiver>,"->"),edge(<receiver>,<marks>,"->"),edge(<marks>,<output>,"->"),
))
#v(7mm)
#grid(columns:(1fr,1fr),gutter:14mm,
 [*holonic-receiver*
  #v(3mm)#note([Exact rational companion: source projection, affine or reciprocal-depth visibility, level intersection, coherent primary response and enclosed entropy stations. Pure Typst helpers expose receiver maps and the softmax cross-entropy differential. The packet keeps source and omitted/degenerate populations.])
  #v(4mm)#align(center,fig("torus_pinhole",width:100mm))
 ],
 [*holonic-engraving*
  #v(3mm)#note([CeTZ draws supplied marks. Line width, stippling and paint are explicit display choices; clipping and source identity are already in the packet. Phase colors are transferred without a contrast boost. The monochrome mode changes paint, not the supplied geometry.])
  #v(4mm)#align(center,fig("torus_mono",width:100mm,mode:"mono"))
 ],
)
#eq[$q T_w=U_w q, quad r T_w=tilde(r) U_w q$]
#eq[$C(A)=C(-A), quad C(A+1)!=C(-A+1) quad (A=1+2upright(i))$]
#note([*Future-receiver condition.* A cached image is sufficient only for the receivers and continuations it preserves. A generator, current and retained fibre can describe indefinitely many later configurations without storing all pictures. ETP's substitution/congruence discipline applies to admitted passages; identical current pixels do not establish it. The companion twenty-plate composition atlas retains the prior HNN/Athena architecture and its exact examples.])

#pagebreak()
#title("10","One link changes the motion of the other","Consequential boundary coupling: normal grip, tangential slip, and energy carried into the shared interface.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Initial slip · $a=1$*\ #v(2mm)#fig("friction_1_1",width:90mm)],
 [*Coupled motion · $a=1/2$*\ #v(2mm)#fig("friction_1_2",width:90mm)],
 [*Reduced slip · $a=1/8$*\ #v(2mm)#fig("friction_1_8",width:90mm)],
)
#eq[$a=e^(-2t), quad s=e_y+e_z, quad v_A=a s, quad v_B=-a s, quad c_A=frac(1-a,2)s, quad c_B=-c_A$]
#eq[$f_A=-2a s=-f_B, quad E_("kin")=2a^2, quad P_("friction")=8a^2, quad Q=2(1-a^2)$]
#grid(columns:(1fr,1fr),gutter:12mm,
 [*A real shared patch constrains the movement.*
  #eq[$g>=0, quad N>=0, quad g N=0, quad g=0, quad N=1$]
  #note([*Exact guided-body model.* Two unit-mass rounded links have disjoint interiors and a shared square of area $1/4$. Opposed normal preloads are balanced by contact reactions. Guides hold their rotations; tangential motion follows unit viscous contact. This is a declared contact law, not an unconstrained elastic-knot solver.])],
 [*Grip and turn are measured together.*
  #eq[$A_R=frac(r dot F,upright(E)_0)+upright(i)frac((r times F)dot n_R,upright(E)_0)$]
  #note([The body hatches read this work/turn pair with $E_0=2$, $F_A=-N n+f_A$ and $F_B=-F_A$. Color follows the same primary law. The links retain linking number $-1$; no surface passes through another. The buried contact is read separately on the next plate by an interface receiver.])],
)
#v(4mm)
#note([*Recovered meaning.* The Turn tablet defines friction as the consequential coupling itself, with grip and slip as two faces. The positive heat return here belongs to this particular viscous constitutive law. At the displayed phases, $t=-log(a)/2$; positions, forces and energy are exact ratios, rather than an interpolated animation.])

#pagebreak()
#title("11","Friction drives a complex interface current","Momentum transfer and heat propagate through the actual boundary adjacency of the contact patch.")
#grid(columns:(1fr,1fr,1fr),gutter:10mm,align:center,
 [*Early contact · $a=255/256$*\ #v(2mm)#fig("contact_255_256",width:84mm)],
 [*Propagation · $a=15/16$*\ #v(2mm)#fig("contact_15_16",width:84mm)],
 [*Distributed return · $a=1/2$*\ #v(2mm)#fig("contact_1_2",width:84mm)],
)
#eq[$L=mat(2,-1,0,-1;-1,2,-1,0;0,-1,2,-1;-1,0,-1,2), quad ell=2r=1/2, quad D/ell^2=4$]
#eq[$dot(theta)=-4L theta+8a^2 e_0, quad dot(Psi)=-4L Psi+2(1+upright(i))a e_0, quad Psi in CC^4$]
#eq[$sum_i theta_i=2(1-a^2), quad sum_i Psi_i=(1+upright(i))(1-a), quad E_("kin")+sum_i theta_i=2$]
#note([*Exact finite propagation.* Four boundary nodes have unit thermal capacity and unit diffusivity at their actual spacing. Frictional power enters one declared port; the operator transports it along contact edges. $Psi$ is the complex diffusing response to transmitted tangential force, with its sum equal to the delivered impulse. It is a history receiver, not an additional uncounted mechanical energy store.])
#v(3mm)
#note([*Declared interface image.* Four fan triangles interpolate the boundary readings; the center is their mean, not a fifth dynamical state. Ink reads normalized impulse rate together with stored heat. The fixed receiver aperture is the per-node quarter-area $1/16$, and the field-level spacing is $1/256$. This internal receiver has access to the contact patch; the outer views on plate 10 do not pretend to see through opaque bodies. The finite interface law accompanies the C³ bulk constructions above without claiming a complete continuum fluid/contact solver.])
