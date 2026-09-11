#import "@preview/fletcher:0.5.8": diagram,node,edge
#import "@preview/cetz:0.3.4": canvas,draw
#let field(name,width:90mm)=image("../../../rendered/receiver-engraving/"+name+".svg",width:width)

#let woven-plates(title,eq,note)=[
#pagebreak(weak:true)
#title("19","Many circulating fields give a body its visible surface","Fifteen toroidal channels, actual overlap ports, and one coherent receiver; the visible skin is returned by their interaction.")
#grid(columns:(1fr,1fr),gutter:10mm,align:center,
 [*The circulating channels*\ #v(2mm)#field("woven_cores",width:120mm)],
 [*Their joint intensity horizon*\ #v(2mm)#field("woven_0",width:120mm)],
)
#eq[$A_v=sum_(i) Psi_i K_(i)(v)g_(i)(v), quad A_h=sum_a lambda_a A_(v_a), quad I_h=sum_a lambda_a abs(A_(v_a))^2, quad Sigma_R={x : I_(h)(x)=1/3}$]
#eq[$I_h-abs(A_h)^2=sum_(a<b) lambda_a lambda_b abs(A_(v_a)-A_(v_b))^2>=0, quad lambda_a>=0, quad sum_a lambda_a=1$]
#grid(columns:(1fr,1fr),gutter:12mm,
 [#note([*Definition.* Three orientation families each carry five rational torus sections. Their full field supports overlap; the thinner lines on the left display the channels. $K_i$ is a compact toroidal kernel, $g_i$ a unit phase plate, and $Psi_i$ the transported mode. No source incidence is created by a screen crossing.])],
 [#note([*Exact finite receiver.* $I_h$ interpolates the measured nodal intensities on a radially layered tetrahedral atlas. The surface is exact for that finite chart. Intensity averaging retains the displayed phase-variance defect; it is not silently replaced by squaring the averaged amplitude. A dark face need not mean the carrier vanished.])],
)

#pagebreak()
#title("20","An ecology persists through supplied and returned current","Three illumination ports sustain the woven field; contact transports phase, redistributes amplitude and deposits heat.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Initial occurrence · $k=0$*\ #v(2mm)#field("woven_0")],
 [*Returned contact · $k=6$*\ #v(2mm)#field("woven_6")],
 [*Continued ecology · $k=12$*\ #v(2mm)#field("woven_12")],
)
#eq[$delta_e=y-u_e x, quad x'=x+alpha overline(u_e)delta_e, quad y'=y-alpha delta_e, quad abs(u_e)=1, quad alpha=1/4$]
#eq[$E'-E=-2alpha(1-alpha)abs(delta_e)^2, quad Q_e=2alpha(1-alpha)abs(delta_e)^2>=0$]
#eq[$sum_i abs(Psi_i^k)^2+sum_i H_i^k=E_0+sum_(ell <= k) W_ell, quad W_ell=abs(Psi+s)^2-abs(Psi)^2$]
#grid(columns:(1fr,1fr),gutter:12mm,
 [#note([*Proved-derived · Lean and exact source.* The passive contact law keeps transported sum and energy plus heat. Each clock admits a matching of independent contacts. Their unit phases are read at common support nodes. The atlas also follows plate 14’s fluid map at $tau=k/M$, with $M=13$ returned matchings; optical amplitude is carried as a scalar.])],
 [#note([*Declared drive.* One input port per orientation family supplies a coherent unit amplitude at each clock. The initial three-family pulse enters one channel. The signed source-work cross term is retained; the energy is port storage, not a presumed integral of the image. In the closed-pulse comparison, wave energy becomes heat and the optical horizon can fall below threshold while the channels remain.])],
)

#pagebreak()
#title("21","Changing contact and changing the receiver have different returns","The same incoming source and threshold; counterfactual contacts expose what makes the collective face.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Admitted contact · $k=12$*\ #v(2mm)#field("woven_12")],
 [*Contact disabled · same drive*\ #v(2mm)#field("woven_off")],
 [*One reversing seam · same drive*\ #v(2mm)#field("woven_twist")],
)
#eq[$u_(i j)=epsilon_(i j)g_(i)(w)overline(g_(j)(w)), quad product_(gamma_a)u_e=-1, quad product_(gamma_b)u_e=+1$]
#eq[$tilde(x)=g x, quad tilde(y)=h y, quad tilde(u)=h u overline(g), quad "contact"(tilde(x),tilde(y);tilde(u))=(g x',h y')$]
#grid(columns:(1fr,1fr),gutter:12mm,
 [#note([*Proved-derived · Lean.* A coordinated receiver reorientation transports the same contact. Altering one seam while retaining the other ports changes the closed return instead. On the selected common-site spine, the phase-plate factors telescope; the declared sheet sign remains.])],
 [#note([*Exact separating instance.* A parallel section on $y=x$, $z=y$, $x=-z$ must be zero. The all-positive cycle admits every constant section. Driven current can still traverse the reversing passage; its incompatible local differences and heat remain visible. The source field, not a knot label, determines the image.])],
)

#pagebreak()
#title("22","The intersection contains an orientation-reversing passage","A Möbius-shorts field is embedded inside four actual torus supports; its central disk follows the measured local plane.")
#grid(columns:(1fr,1fr),gutter:10mm,align:center,
 [*The containing field · $w$ locates the shared source*\ #v(2mm)#field("woven_contact_locator",width:116mm)],
 [*The supported passage · magnified receiver*\ #v(2mm)#field("woven_bridge",width:116mm)],
)
#eq[$X(x,y,z)=w+epsilon(x b_1+y b_2+z n), quad b_1 parallel nabla F_i times nabla F_j, quad b_2 parallel n times b_1, quad n parallel nabla F_i$]
#grid(columns:(1fr,1fr),gutter:12mm,
 [#note([*Established-bounded.* Strict rational interval bounds place the whole mapped mesh inside all four toroidal supports. Its source incidence returns $chi=-1$, one boundary and two loop signs $(-1,+1)$. The affine frame has positive determinant. The disk is tangent to the first field level at the contact and retains the shared tangent direction.])],
 [#note([*A derived aperture.* The physical scale $epsilon=3/512$ is the first admitted dyadic scale from the declared search and its whole-box certificate. It is a conservative fitting result, not a universal thickness law. The locator marks the buried source; the inset has its own local receiver. Magnification and full embedding are retained. The fluid horizon and the embedded nonorientable passage remain separate geometric objects.])],
)

#pagebreak()
#title("23","A local plane carries a law within its measured aperture","Optical tangential transport, a nearly constant gravity reading and a cosmological parameter each retain their own remainder.")
#grid(columns:(1fr,1fr),gutter:16mm,
 [*Snell transport resolves the normal return.*
 #v(4mm)
 #align(center,canvas({
  import draw: *
  set-style(stroke:3pt/5)
  line((-3,0),(3,0))
  line((0,-2),(0,2),stroke:(dash:"dashed",paint:black,thickness:1pt/3))
  line((-12/5,9/5),(0,0));line((0,0),(9/5,-12/5));line((0,0),(12/5,9/5))
  content((-5/2,11/5),[$w_1=3$]);content((2,-5/2),[$w_2=4$])
  content((-2,4/5),[incoming]);content((2,4/5),[reflected]);content((1/2,3/2),[$n$])
 }))
 #eq[$3sin(theta_1)=4sin(theta_2)=12/5, quad (cos(theta_1),cos(theta_2))=(3/5,4/5)$]
 #eq[$N_1=9/5, quad N_2=16/5, quad N_2-N_1=7/5$]
 #eq[$r=frac(N_1-N_2,N_1+N_2)=-7/25, quad t=frac(2sqrt(N_1 N_2),N_1+N_2)=24/25, quad r^2+t^2=1$]
 #note([*Conditional optical chart.* Isotropic lossless TE interface with equal magnetic permeability; $t$ is power-normalized. The Snell owner preserves the tangential receiver while retaining the normal fibre. A reflected phase sign alone does not prove a Möbius surface; the preceding passage also carries its actual gluing incidence.])],
 [*Near a surface, variation can be small and bounded.*
 #eq[$frac(g(R+h),g(R))=frac(1,(1+h/R)^2), quad s=h/R>=0$]
 #eq[$frac(g(R)-g(R+h),g(R))=frac(s(2+s),(1+s)^2)<=2s$]
 #note([*Proved-derived comparison.* In the spherical Newtonian exterior, “constant surface gravity” is a local aperture approximation with this exact relative defect. It does not make $g$ constant away from the source. The woven contact plane likewise retains its polynomial Taylor remainder over its finite neighborhood.])
 #v(5mm)
 *A constant $Lambda$ can have changing receiver coordinates.*
 #eq[$f(r)=1-frac(2G M,c^2 r)-frac(Lambda r^2,3), quad g_("weak")=frac(G M,r^2)-frac(Lambda c^2 r,3)$]
 #eq[$Omega_(Lambda)(z)=frac(Lambda c^2,3H(z)^2)$]
 #note([*Conditional physical chart.* The first line is the static spherical Schwarzschild–de Sitter metric factor and its weak-field inward-positive radial acceleration. A constant geometric $Lambda$ does not imply constant $Omega_Lambda$ when the expansion chart changes. Our cosmological inference owner retains those plural source/receiver fibres and dimensions.])
 #v(3mm)#note([Sources: #link("https://www.damtp.cam.ac.uk/user/tong/gr/gr.pdf")[Tong, GR]; the August 25 cosmological receiver record; `HolonicSnellInteraction` and the paired phase receiver.])],
)

#pagebreak()
#title("24","A remote fold responds through its constitutive contact","Two contorted domains form a small abstract allosteric machine: one is driven, while the other moves through the shared response.")
#grid(columns:(1fr,1fr),gutter:10mm,align:center,
 [*Initial domains · $q_1=q_2=0$*\ #v(2mm)#field("lobes_0",width:134mm)],
 [*After four returned steps · contact admitted*\ #v(2mm)#field("lobes_4",width:134mm)],
)
#v(4mm)
#grid(columns:(1fr,1fr),gutter:12mm,
 [*Same drive, contact removed: the remote domain stays at rest.*
 #align(center,field("lobes_off",width:115mm))
 #note([*Established-bounded.* The image reads conformation and generalized force on each actual rotated domain. $q$ parametrizes the rational rotation; it is not a literal angle. The contact-off return keeps $q_2=0$, while the admitted contact gives $q_2<0$.])],
 [#eq[$c_i=1/2+q_i^2, quad E=frac(c_1^2+c_2^2,2)+frac((q_1+q_2)^2,2)-q_1$]
 #eq[$q'=q-frac(1,8)nabla E, quad H=F Delta q_1-Delta U=E-E'>0$]
 #eq[$K_i^"domain"=2(a+3q_i^2)=k(2q_i)^2+2k(a+q_i^2) quad (k=1)$]
 #note([*Proved-derived · exact instance.* The existing conformation owner separates material stiffness and prestress; the finite source keeps the contact cross term. Every displayed step stays within $abs(q_i)<=1/2$ and returns positive finite dissipation. The even receiver $q^2$ can agree while the oriented responses are opposite.])
 #v(3mm)#note([*Biological interpretation.* This recovers the protein constraint ecology: chains, contact cells, flexible modes, self-stress and an active-site receiver. The construction models remote mechanical consequence and changing constraints. Plates 25–28 now add sequence-conditioned folding and reaction kinetics to this programme.])],
)
]
