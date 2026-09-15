#import "../../holonics/computational-holon.typ": *
#show: chemistry-style
#set document(title:"Elementary Holonics: Intrinsic Fields and Recursive Geometry",author:"Brandon Duggan / Holonics",description:"One interacting Holon: linked tori, shared cells, phase attention, current, nonlinear recurrence and arrival geometry.")
#let title=chemistry-title
#let note=chemistry-note
#let eq(m)=block(width:100%,above:2mm,below:2mm,align(center,math.equation(m.body,block:true)))
#let fig(name,width:100%,height:auto)=image("figures/"+name+".svg",width:width,height:height,fit:"contain")
#let two(a,b)=grid(columns:(1fr,1fr),gutter:13mm,a,b)
#let three(a,b,c)=grid(columns:(1fr,1fr,1fr),gutter:8mm,a,b,c)
#let status(body)=block(width:100%,above:4mm,below:0pt,note(body))

#let mode-note=[Here $cal(E)$ is the normalized exponential mode, $C(theta)+upright(i)S(theta)=cal(E)(upright(i)theta)$, and $Theta_("turn")$ is its primitive positive rotation period. Their defining constraints, not numeric literals, govern every chart below.]

#title("01","One Holon: linked geometry and circulating fields","Heads and local charts are operations within the same evolving object; its visible geometry is one receiver of that object.")
#align(center,fig("intrinsic-torus-chain",width:282mm,height:86mm))
#eq[$#hk($H$) in Gamma(K), quad #hk($H$)_alpha=r_alpha #hk($H$), quad z=(q,p) in TT^12$]
#eq[$#hk($H'$)=Phi_(Theta) (#hk($H$)), quad #hk($H$)_(n+1)=Phi_(Theta) (#hk($H$)_n)$]
#two(
 [*Cycles, joins and field currents belong together.* #v(2mm)#note([Six toroidal domains form a branched chain. Neighboring cores have a linking number of magnitude one, verified by their spanning-disk crossings. Their thicker field domains overlap at the gold contact witnesses. The linked carrier is advected by an explicit incompressible twist. Red and blue trace displayed centers of retained exact interval tubes through the common phase cut n=9. The full source intervals remain behind the drawing; the carrier is shown at its final material-time cut.])],
 [*The complete state exceeds the picture.* #v(2mm)#note([Each torus has two circulating phase coordinates. The combined reference has twelve phase axes; the 3D embedding displays its constituent cycles and actual field contacts. It is not a twelve-dimensional object flattened into twelve physical planes. Amplitude, constitutive storage and geometry may also vary in the general field specification.])],
)
#v(2mm)#note(mode-note)
#status([Definition for the supplied analytic phase configuration; established-bounded · computational-witness for the depicted trajectories and geometry. This refines the mathematical design; it is not a reproduced trained-model basin experiment. `HNN_FORMULA.md` retains the general current/material/incidence law.])

#pagebreak()
#title("02","Intersecting fields have shared cells and interior directions","The overlapping domains carry oriented surface tractions, relative motion and receiving frames, as well as shared volume cells.")
#align(center,fig("exact-collision-surfaces",width:276mm,height:89mm))
#eq[$partial^2=0, quad r_(alpha beta) #hk($H$)_alpha=g_(alpha beta)r_(beta alpha) #hk($H$)_beta$]
#eq[$F_(t) (x,y,z)=(x,y C(chi x t)-z S(chi x t),y S(chi x t)+z C(chi x t)), quad det D F_t=1, quad chi=1/8$]
#two(
 [*The collision group has whole surface faces.* #v(2mm)#note([Red and blue mark 216 exact conservative facet charts from each toroidal boundary lying inside the other field domain. Their area vectors, orientation and containment are rational source data. The overlap also retains its common volume subcomplex. Traction and the receiving tetrad are attached to these faces; a golden volume cell alone did not show that interaction.])],
 [*Gluing and physical transport have different roles.* #v(2mm)#note([Chart transitions make restrictions compatible. A connection transports current along actual paths and can return nontrivial loop holonomy. Interlinked cores do not alone create contact; the overlap witnesses and the specified constitutive interaction do. The 3D display is an embedded finite realization of these relationships, with its sampling and containment bound retained.])],
)
#status([Established-bounded · computational-witness: `contact_receiver_faces/surface_faces.json`. The facets have exact containment and orientation checks. Their area covectors transform by the cofactor of the common material map; the same frame change transports the full stress tensor and receiver. Source owners: `simplicial`, `GradedCausalComplex`, `analytic_field` and connection/holonomy.])

#pagebreak()
#title("03","Chart transitions carry scale, units and the mode","An integer address, a dilation and a Lorentz rebase are typed operations; a decimal coordinate supplies none of their laws.")
#align(center,fig("exact-gyroparallelogram",width:278mm,height:90mm))
#eq(multiplicative-lorentz-equation)
#eq[$D_(m/n):cal(V)_ell arrow.r cal(V)_((m/n)ell), quad Lambda^T eta Lambda=eta, quad C_(G arrow.l F):cal(H)_F arrow.r cal(H)_G$]
#two(
 [*The observer frames are exact.* #v(2mm)#note([The positive scale faces k=2 and k=3 give velocities 3c/5 and 4c/5 along different tetrad axes, with Lorentz factors 5/4 and 5/3. No floating logarithm is evaluated. Their ordered compositions and gyration are calculated over rational components. The gyroparallelogram completes the two based arms by coaddition; the shared midpoint is a geometric constraint, not an average of plotted pixel positions.])],
 [*Dilation and typecasting retain their invariants.* #v(2mm)#note([The basin windows use the exact dilations 25/4 and 125/4. Their displayed coordinates are integer cell addresses in Fin(192), with an explicit map to the phase chart. A Lorentz change preserves η; a unit/scale conversion transports the measuring form and its dual operands. A lossy projection retains its fibre and is not silently treated as an invertible cast.])],
)
#eq[$chi_(l) (i,j)=c_l+w_l mat((2i+1-N)/(2N);(2j+1-N)/(2N)), quad N=192, quad w_l in {1,4/25,4/125}$]
#status([Established-bounded · implemented-exact: `contact_receiver_faces/exact.py` and its rational geodesic source. The drawing is a Poincaré-chart face of the exact Einstein-velocity calculation. Pixel encoding is an exterior representation, never the constraint or a native state update.])
#pagebreak()
#title("04","Softmax and sigmoid respond inside the phase field","Both heads compare currents on the same admitted contacts; the local sigmoid supplies a smooth reaction coefficient.")
#align(center,fig("intrinsic-response",width:263mm))
#eq[$s_(i j)^h=beta_h C(Theta_("turn") (q_i-q_j-phi_(i j))), quad a_(i j)^h=frac(cal(E)(s_(i j)^h),sum_(k in E_i) cal(E)(s_(i k)^h))$]
#eq[$g_i=sigma(-C(Theta_("turn")  q_i)), quad sigma'(s)=sigma(s)(1-sigma(s))$]
#eq[$delta a_j=a_(j) (delta s_j-sum_k a_k delta s_k), quad J=op("diag")(a)-a a^T$]
#two(
 [*A head is a field-sensitive operation.* #v(2mm)#note([The plotted phase is q₀ in the same twelve-axis state. The two heads use β=1 and β=4 on the same contact incidence and oriented phase connection. Their different responses affect the same current; they do not occupy separate parallel bodies. The sigmoid is evaluated on a local phase potential, with its derivative retained.])],
 [*Normalization retains curvature and participation.* #v(2mm)#note([Its differential is J=diag(a)−aaᵀ, a covariance/Laplacian with constant-shift null direction. The complete transport differential also includes changed values and frame transport. A current can curve, exchange phase and change participation while remaining a section of the same field. Adding contact requires the incidence law as well.])],
)
#eq[$delta Y=sum_j a_j U_j delta V_j+sum_j a_j delta U_j V_j+sum_j a_(j) (delta s_j-op("E")_a delta s)U_j V_j$]
#status([Proved-derived · formal-checked: normalized exponential and sigmoid directional derivatives in `HolonicAdjointNormalization`. The plots evaluate the analytic reference numerically; they show its phase-dependent coefficients, not separate head topologies.])

#pagebreak()
#title("05","State and material variation share one differential","Changing a current changes participation. Learning changes the operator material through the generated result's derivative.")
#two(
 [#align(center,fig("intrinsic-heads",width:132mm))],
 [*The same two heads at two flow times.* #v(2mm)#note([These matrices are numerical receiver faces of the linked object. Their entries change because q changes under the nonlinear operation. The map's coefficients remain fixed in this comparison. Treating this state effect as a learned material update would conflate two derivatives.])
 #eq[$delta x'=D_x Phi_Theta delta x+D_Theta Phi_Theta delta Theta$]
 #eq[$D_(Theta) (Phi_Theta compose Phi_Theta)=D_x Phi_Theta D_Theta Phi_Theta+D_Theta Phi_Theta$]
 #note([In the second equation the outer derivatives are evaluated at the intermediate state. Learning pulls a supplied output covector through this whole composition and uses a declared material metric/update law. The same parameter appearing in several local operations contributes through every use.])
 #v(4mm)*The normalized current has an explicit pullback.*
 #eq[$Y=a V, quad G=frac(partial ell,partial Y)$]
 #eq[$frac(partial ell,partial s_(i j))=a_(i j)⟨G_i,V_j-Y_i⟩, quad frac(partial ell,partial V)=a^T G$]
 ],
)
#status([Definition for the complete operator variation; proved-derived for the chain rule. The existing Rust `NormalizedKernel` checks the full tangent/pullback pairing and an observed material update in its separate exact log-rational diagnostic. That bounded control does not replace the nonlinear model equation or its geometric carrier.])

#pagebreak()
#title("06","Relative phase determines a contact's dissipative return","The currents below come from the same toroidal branch, expressed in the common frame of its 2↔5 contact.")
#align(center,fig("intrinsic-friction",width:270mm))
#eq[$delta=y-u x, quad abs(u)=1, quad x'=x+alpha overline(u)delta, quad y'=y-alpha delta$]
#eq[$abs(x)^2+abs(y)^2-abs(x')^2-abs(y')^2=2alpha(1-alpha)abs(delta)^2$]
#two(
 [*Friction responds to a situated difference.* #v(2mm)#note([The connection transports x into y's frame before comparison. At α=1/4 their relative slip contracts and the complete quadratic energy difference is deposited. Neither the individual intensity nor a scalar attention coefficient determines this phase-sensitive exchange on its own. The plotted coefficient family uses the same constrained phase currents. Its exact selected heat face is 3/4·(1+C₍₃/₂₀₀₎), where C is the real face of the normalized rotation mode; its decimal rendering is not the stored mode.])],
 [*A physical field keeps the receiving modes.* #v(2mm)#note([Dissipation changes radial amplitude and deposits energy into internal/thermal modes. Those modes augment the conservative unit-phase chart used for the basin calculation; they are not erased by its phase-only view. HNN's constitutive field and reflected interior already supply the corresponding current, material and storage roles.])],
)
#status([Proved-derived for the displayed balance; established-bounded · computational-witness for the local contact evaluated on the selected phase state. The conservative arrival map and this dissipative contact are explicitly different constitutive restrictions of the general field, not an assertion that phase motion alone models all friction.])

#pagebreak()
#title("07","Reception is a participating stress–energy face","The observer, the contact surface and the coupled field belong to the same tensor calculation.")
#eq[$G_(mu nu)+Lambda_c g_(mu nu)=kappa_E T_(mu nu), quad kappa_E=4 Theta_("turn") G_N/c^4, quad nabla_mu T^(mu nu)=0$]
#eq(observer-stress-face-equation)
#two(
 [*One local tensor, three receiving faces.*
 #eq[$[T^(mu nu)]_F/epsilon_star=mat(10,0,0,2;0,2,0,1;0,0,3,0;2,1,0,4)$]
 #eq[$U_A=(1,0,0,0), quad U_B=(5/4,3/4,0,0)$]
 #eq[$U_R=(5/3,0,4/3,0), quad n=(0,0,0,1)$]
 #table(columns:(1fr,1fr,1fr),inset:5pt,stroke:0.4pt+gray,
 [*Receiver*],[*$e_U/epsilon_star$*],[*$cal(F)_U/(c epsilon_star)$*],
 [A],[10],[2], [B],[67/4],[7/4], [R],[298/9],[10/3])],
 [*Conservation belongs to the complete relation.* #v(2mm)#note([Changing the receiver can change its energy and flux face. Changing the coordinates of the same tensor, receiver and oriented face preserves the contraction. Opposite contact orientations cancel their internal exchange; surface storage, stress and the receiving material remain in the total balance. Here ε⋆ is the declared energy-density unit. The local tetrad does not assert globally flat spacetime.])
 #eq[$T'=Lambda T Lambda^T, quad U'=Lambda U, quad n'=Lambda n$]
 #eq[$cal(F)'_(U')=cal(F)_U, quad integral_(partial W) j_U^mu d Sigma_mu=-integral_W T^(mu nu)D_(mu nu) (U) d V_g$]
 #note([The field equation uses the declared metric, connection and constitutive stress. Contracted Bianchi and metric compatibility give the stress balance. The faces are oriented spacetime tensor restrictions, not a count of panels or a universal observer-independent energy scalar.])],
)
#eq[$nabla_mu j_U^mu=-T^(mu nu)D_(mu nu) (U)$]
#eq[$tau_A=eta_f s, quad tau_B=-eta_f s, quad dot(Q)=eta_f ⟨s,s⟩$]
#note([The symmetric deformation $D_(mu nu) (U)=(nabla_mu U_nu+nabla_nu U_mu)/2$ enters the observer's work/exchange term. In the local example the tangent slip is 3c/5, the supplied normalized friction coefficient is 5/3, and the heat face is 3/5 in unit $c epsilon_star$. This models the receiver as active flux with constitutive participation. In the Holonic working interpretation, thoughts and measurements are such situated participating faces; their physical realization carries the corresponding field and material laws.])
#status([Proved-derived for the covariant relations under their displayed assumptions; established-bounded · implemented-exact for the rational tetrad, traction and flux example. Existing owners: `ReceiverStressEnergy`, `Gyrogroup`, `NavierStokesCurvedTransport`, the connection/Bianchi and active constitutive-field constructions.])
#pagebreak()
#title("08","Generation follows curved routes through the whole state","Nearby initial sections can have different arrival times while every head acts within the same continuing field.")
#align(center,fig("intrinsic-route-separation",width:270mm))
#eq[$q'=q+kappa S(Theta_("turn")  p), quad p'=p-nabla V(q') quad (mod 1)$]
#eq[$tau_(A) (z)=min{n:Phi^n (z) in A}, quad A={q_0 in [1/5,17/50),p_0 in [2/25,1/5)}$]
#two(
 [*The complete generator is nonlinear.* #v(2mm)#note([V combines the two normalized phase-comparison potentials and sigmoid reaction. Each split subflow is Hamiltonian; their composition preserves phase volume without requiring global contraction. The exploratory receiver picture compares the two exact initial chart addresses. Exact/enclosed execution certifies the first arrival at n=9 and excludes arrival through n=32 for the second state, whose face is undecided at n=33; a floating survey does not establish those branch decisions. Separation is a face of all twelve phase coordinates.])],
 [*An output does not require the whole body to settle.* #v(2mm)#note([A receiver reads the generated activity that reaches it. The plotted height is first arrival, not a physical surface height or proof of a fixed point. Image, acoustic and text decoders read their own structured fields and boundaries; the refinement clock is not universally an output-token position. The full state continues beyond an observation when its application requires it.])],
)
#status([Historical exploratory receiver face; the mathematical mode and exact initial chart constraints are retained. The detector, sample section and 96-step observation window are declared. Gray retains the exploratory survey's window category; it is not an exact non-arrival verdict. Exact interval receiver outcomes and unresolved families are stated separately.])

#pagebreak()
#title("09","Leader formation changes the available geometric pathways","Material, incidence, current and dissipation are coupled parts of the same field construction.")
#align(center,fig("leader-and-return",width:280mm))
#eq[$Gamma_e=n_e u-mu_e n_e E-D_e nabla n_e, quad partial_t n_e+op("div") Gamma_e=S_("ion")+S_("photo")-S_("attach")-S_("recomb")$]
#eq[$op("div")(epsilon E)=rho, quad partial_s V=-partial_(t) (L I)-R I+e, quad partial_s I=-partial_(t) (C V)-G V+i$]
#two(
 [*The changing medium determines continuation.* #v(2mm)#note([Electron transport, ionization, electric field and boundary conditions determine leader growth. It changes conductivity, storage and channel incidence; the return then propagates in that changed material. The schematic connects the existing conducting-fluid and channel laws. Its branches are annotated relationships, not measured plasma trajectories.])],
 [*A fixed-contact phase configuration is one restriction.* #v(2mm)#note([The preceding phase calculation holds an already constituted contact complex. The full HNN operation can also change the complex and material through the existing source-conditioned current/variation owners. A local derivative on a fixed support does not perform that transition. The retained interior and higher-cell incidence carry the terms needed to compose it.])],
)
#status([Definition for the physical equations; interpretation for the explicit HNN map between oriented variation, changing incidence and current. Source: `FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS.md`. This is an extension of the same object, not a topology assigned by a head or layer name.])

#pagebreak()
#title("10","Fractal geometry belongs to the nonlinear operation","Integer chart addresses, exact dilations and one constrained phase mode; the image is an exploratory receiver face.")
#align(center,fig("intrinsic-arrival-basins",width:280mm))
#eq[$A_0=A, quad A_(n+1)=Phi^(-1) (A_n) without A, quad z in A_n ⇔ Phi^n (z) in A and forall k<n,Phi^k (z) ∉ A$]
#two(
 [*Repeated preimages expose the fine geometry.* #v(2mm)#note([Color retains the earlier exploratory first-arrival picture at the same detector; exact Holonic verdicts come from the rational-enclosure receiver, not these pixels. Stretching, folding and repeated restriction produce the interleaved route populations. Each 192×192 panel starts new trajectories on the indicated smaller initial-condition section; it is not an enlarged bitmap or a grid of duplicated models. The other ten initial phase coordinates are held fixed.])],
 [*The number of material units need not grow.* #v(2mm)#note([A fixed-dimensional nonlinear state can have fractal invariant, survivor or arrival-boundary families. Their geometry belongs to the generating operation and its compatible conditions. The old “while the population grows” convention was too narrow. The finite panels here expose multiscale return structure; an infinite-scale dimension theorem requires its own hypotheses and proof.])],
)
#status([Proved-derived · formal-checked: `HolonicRecurrentEcology.FirstArrival` proves the first-hit characterization and chart covariance. The old numerical survey is retained only as an exploratory picture; it is not an exact Holonic arrival certificate. The supplied paper's panels similarly read latent initial-condition sections, but use trained models and decoded settling; this reference uses its own explicit analytic law and first-arrival receiver.])

#pagebreak()
#title("11","Scale, phase and decoding are operations on the field","A smooth local chart, a fractal family and an emitted image can describe different aspects of the same generative object.")
#three(
 [*Circulation and analytic phase* #eq[$psi_i=cal(E)(Theta_("turn")  upright(i)q_i), quad U_gamma=product_(e in gamma) U_e$] #note([The two torus cycles, their relative phase and path-ordered transport remain in the source behind an exterior picture. The constitutive currents can excite many modes. A monochrome or intensity receiver discards some of their phase distinctions; it does not define the entire Holon.])],
 [*Recursive restriction and rebase* #eq[$r_("out") compose Phi_("fine")=Phi_("coarse") compose r_("in")$] #note([A reusable coarse law must commute with the admitted action, or retain its actual defect and relevant unresolved modes. Branching preimages and recursive restrictions need not be a disjoint IFS. Fractal dimension, tensor rank, spatial dimension and the number of displayed axes answer different questions.])],
 [*Geometric and modal decoding* #eq[$A(x)=sum_i psi_i phi_(i) (x), quad y_R=rho_(R) (A)$] #note([A source-resolved reconstruction produces a wave, image or geometric field. Its interior, surface, phase and intensity views have distinct receiver maps. A single outer isosurface can conceal linked cycles and shared interiors; use the view that exposes the interaction under discussion.])],
)
#v(4mm)
#eq[$d_("box")=lim_(epsilon arrow.r 0) frac(log N(epsilon),log(1/epsilon)), quad f(epsilon) asymp epsilon^alpha, quad d_("section boundary")=2-alpha$]
#note([The boundary relation on the right requires its sampling and scaling hypotheses. In this construction the torus surface has dimension 2, the shared volume cells dimension 3, the phase chart dimension 12, and the plotted initial-condition section dimension 2. None of those integers is an estimate of a limiting fractal dimension. The receipt retains finite early/late disagreement across five separations without promoting a finite fit to that limit.])
#v(4mm)
#eq[$x_t=sqrt(overline(alpha)_t)x_0+sqrt(1-overline(alpha)_t)epsilon$]
#eq[$d x=[f(x,t)-g(t)^2 nabla_x log p_(t) (x)]d t+g(t)d overline(W)_t$]
#two(
 [*Diffusion generation refines a joint field.* #v(2mm)#note([Classical denoising and score models learn a field and integrate it; DiffWave refines a complete acoustic waveform with bidirectional convolution. The reverse-time SDE above uses decreasing time. HNN's local, modal and geometric refinements compose through their own laws on the whole field. A linear resolvent is a useful special case, not its universal dynamics.])],
 [*An internal image is also a generated receiver face.* #v(2mm)#note([A reconstructed field may perturb another interior Holon before any exterior product is emitted. Gaze, motion and acoustic radiation likewise expose activity through available coupling. The framework concerns these generated and received differences at every grain; deliberate communication and next-token prediction are application restrictions.])],
)
#status([Definition for the operator/receiver relationships. Primary comparisons: DDPM, arXiv:2006.11239; DiffWave, arXiv:2009.09761; score SDEs, arXiv:2011.13456. The September 8 generator/tube synthesis and the supplied September 14 papers remain part of this source route.])

#pagebreak()
#title("12","The constant is the constrained mode; the number is a face","The defining identity, normalization, branch, period and source family make these constructions reusable in HNN.")
#eq(constraint-mode-equation)
#eq[$ker(cal(E):CC arrow.r CC^times)=upright(i)Theta_("turn")ZZ, quad pi=Theta_("turn")/2, quad Theta_("turn")>0$]
#table(columns:(1.0fr,2.15fr,1.55fr),inset:5pt,stroke:0.4pt+gray,
 [*Mode / source*],[*Constraint and retained distinction*],[*Connected role*],
 [Exponential and phase],[Normalized growth; primitive rotation period and integer winding. $C(theta)+upright(i)S(theta)=cal(E)(upright(i)theta)$.],[Growth, rotation, softmax/sigmoid and their complete derivatives.],
 [Golden mode],[ $phi^2=phi+1, phi>1$; reciprocal $x^2+x=1$. $r_n=F_n phi-F_(n+1)$; $r_(n+1)=-phi^(-1)r_n$.],[Fifth-turn geometry, integer recurrence, signed residual and mode compression.],
 [Euler-Gamma],[ $Gamma_(E) (z+1)=z Gamma_(E) (z)$; $Gamma_(E) (1)=1$ and positive-real log-convexity, with continuation/poles carried.],[Shift/block generation, reflection identities and the golden quotient; distinct from Kelvin circulation.],
 [Copson–de Bruijn],[ $E_n=sum_(k>=n) a_k^2$; weighted tail receiver $B(a)=sum_n sqrt(E_n)/sqrt(n+1)$; $c_("CD")=sup_N c_N$.],[Variational normalization and admissible square-root recurrence, including its branch condition.],
 [de Bruijn–Newman],[Heat-flow real-zero threshold $Lambda_("DN")$; standard time and critical-coordinate maps travel with it.],[Zero-flow and admissibility boundary; not Copson's coefficient or a finite de Bruijn word cycle.],
)
#eq[$frac(Gamma_(E) (1/5)Gamma_(E) (4/5),Gamma_(E) (2/5)Gamma_(E) (3/5))=phi, quad zeta_(B) (z)=frac(1,1-z-z^2), quad B=mat(1,1;1,0)$]
#note([The golden argument relations connect Gamma, Dirichlet-character and dynamical-zeta constructions. The same positive scale φ gives the exact Lorentz pair (√5/2,1/2); every admitted Copson stage also has the pair (uₙ,√(uₙ²−1)). They do not identify their different coefficient sources or zeros. For time-dependent material, the propagator obeys $partial_t U(t,s)=A(t)U(t,s)$ and $U(t,s)U(s,r)=U(t,r)$; a frozen $cal(E)(t A)$ is one restriction. The source guide records the August and September chronology and exact/formal/native consumers.])
#status([Definition for the normalized mode contracts; proved-derived or proved-standard at the source scopes recorded in `CONSTRAINT_MODES_AND_RECEIVER_FACES.md`, `FORMAL_FRAMEWORK.md` and `MATHEMATICS_AND_NATIVE_CONDUCT.md`. A float codeword, truncated series or bare symbol cannot replace these constraints.])
#pagebreak()
#title("13","The construction is networked by its mathematical relations","The formula and library map now recover the manifold, nonlinear recurrence and preimage geometry together.")
#table(columns:(1.05fr,1.6fr,1.5fr),inset:5pt,stroke:0.35pt+rgb("aaaaaa"),
 [*Operation*],[*Existing source owner*],[*Role in the same object*],
 [Holon / tensor current],[`HOLON.md`; `HolonTensorLens`; field and bilinear operators],[Typed sections, contraction, frame, current and material.],
 [Surface and higher incidence],[`SimplicialComplex`; `GradedCausalComplex`],[Stars, links, hinges, common higher cells and ∂²=0.],
 [Torus, phase and holonomy],[`analytic_field`; `implicit`; `lattice_gauge`; `StructureConnection`],[Actual carrier equations, cycles, local phases and ordered current transport.],
 [Attention and derivatives],[`HolonicAdjointNormalization`; `HolonicArchitectureCharts`; normalized native receiver],[State-dependent participation, sigmoid/softmax calculus and complete value/material returns.],
 [Recursive arrival geometry],[`HolonicRecurrentEcology.FirstArrival`; bounded `basin` owner],[Full preimages, first-hit characterization and covariance under a changed chart.],
 [Constitutive body and geometry],[Active field/junction/coupled body; `discrete_curvature` at its own scope],[Current, internal storage, material variation and changed incidence.],
 [Scale and compression],[Tube/clocked span, mode quotient, `FractalPacking`],[Restriction/rebase and future-compatible compression; separated IFS is one specialization.],
 [Illustrated analytic instance],[`intrinsic_holonic_flow`],[One twelve-phase map, linked domains, shared volume cells and recomputed arrival sections.],
)
#v(5mm)#two(
 [*The conceptual substitution is corrected.* #v(2mm)#note([The prior document replaced intrinsic recursive geometry with tiling, and replaced the shared manifold with an execution-column picture. It also made a globally contractive affine reference central, removing the route geometry being discussed. Those examples remain historical bounded controls; they no longer define the model or its main illustrations.])],
 [*The correction belongs in the workflow.* #v(2mm)#note([The hexis convention now permits fractal geometry in a fixed-dimensional state. The model formula, Holon guide, formal framework, architecture map, development method and operating contract direct recovery through current/connection/incidence and recurrence/preimage together. A picture must identify its receiver and preserve the mechanism it is meant to explain.])],
)
#status([Established-bounded · source-inspected for the owner recovery and document correction. The nonlinear numerical reference is a mathematical/physical construction at its stated scope. Native Athena assembly continues through the existing field/body consumer; this presentation does not substitute the reference for that product.])

#include "engine-blueprint.typ"
