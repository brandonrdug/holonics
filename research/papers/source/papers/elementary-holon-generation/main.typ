#import "../../holonics/computational-holon.typ": *
#show: chemistry-style
#set document(title:"Elementary Holonics: Generation and Geometric Fields",author:"Brandon Duggan / Holonics",description:"Ten Information Chemistry plates: computational Holons, toroidal fields, contact, generation and modal representation.")
#let title=chemistry-title
#let note=chemistry-note
#let eq(m)=block(width:100%,above:2mm,below:2mm,align(center,math.equation(m.body,block:true)))

#title("01","The Holon has geometry, current and many faces","The same torus can be read as a surface or as a current; nested tori form a larger field.")
#grid(columns:(1fr,1fr,1fr),gutter:10mm,align:center,
 [*The geometric carrier*\ #v(2mm)#geometric-face("torus_mono",width:90mm,height:72mm,mode:"mono")],
 [*Its complex-current face*\ #v(2mm)#geometric-face("torus_phase",width:90mm,height:72mm)],
 [*Nested circulating constituents*\ #v(2mm)#woven-face("woven_cores",width:75mm)],
)
#eq(holon-state-equation)
#eq(holon-coordinate-equation)
#eq(holon-transport-equation)
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The numerical chart belongs to an object.*
 #v(2mm)#note([The marked ket is the computational Holon in frame F. Its vector/matrix/tensor coordinates carry the declared port axes; an operator acts on this object without reopening its foundational definition. The first two panels use the same rational torus carrier with different readings. The third is a separate fifteen-channel toroidal composition. These are existing Information Chemistry source constructions.])],
 [*Whole and part are relative to the interaction.*
 #v(2mm)#note([A constituent's boundary activity can enter another constituent; the larger compound exposes its own exterior. The occurrence population can be represented by a generator or constraint family. It is not a requirement to enumerate or archive every past state.])],
)
#v(4mm)#note([Formal specification: `docs/HOLON.md`; `Foundation/Holon` and `HolonTensorLens`. Rendering: the existing `holonic-receiver` and `holonic-engraving` packages. White paper, monochrome geometry and unchanged phase colors on black follow the receiver edition.])

#pagebreak()
#title("02","Generation develops a joint geometric field","A boundary surface is produced by interacting modes; no output coordinate is a generation clock.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Initial field · $k=0$*\ #v(2mm)#woven-face("woven_0",width:90mm)],
 [*Coupled field · $k=6$*\ #v(2mm)#woven-face("woven_6",width:90mm)],
 [*Continued field · $k=12$*\ #v(2mm)#woven-face("woven_12",width:90mm)],
)
#eq[$A_v=sum_i Psi_i K_i (v) g_i (v), quad I_h=sum_a lambda_a abs(A_(v_a))^2, quad Sigma_R={x:I_h (x)=1/3}$]
#eq(holon-generation-equation)
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The displayed field has an actual evolution.*
 #v(2mm)#note([These retained finite scenes use fifteen toroidal channels, prescribed input ports, phase-transported contact and a tetrahedral intensity receiver. They illustrate a constituted whole-field component; they are not a newly trained denoising model. The skin follows the field rather than being drawn as an output template.])],
 [*Noise and generation have different roles.*
 #v(2mm)#note([Image diffusion uses a learned noise/score field; acoustic DiffWave refines a complete waveform with bidirectional convolution. Their refinement steps differ from pixels, audio samples or text positions. Zero, unseen, uncertain and noisy regions remain different operands.])],
)
#eq(diffusion-equation)
#note([The whole-field generation contract is in `docs/HNN_FORMULA.md`. The latent/corruption relation above is the classical comparison; the figures retain the existing woven-field law. References: DDPM, arXiv:2006.11239; DiffWave, arXiv:2009.09761; score-based SDEs, arXiv:2011.13456.])

#pagebreak()
#title("03","Composition occurs through actual contact","Linked bodies, a shared patch and its internal field make the joining relation physical.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Initial tangential slip · $a=1$*\ #v(2mm)#geometric-face("friction_1_1",width:90mm,height:72mm)],
 [*Coupled motion · $a=1/2$*\ #v(2mm)#geometric-face("friction_1_2",width:90mm,height:72mm)],
 [*Interior contact patch · $a=15/16$*\ #v(2mm)#geometric-face("contact_15_16",width:90mm,height:72mm)],
)
#eq(holon-interaction-equation)
#eq[$a=e^(-2t), quad f_A=-2a(e_y+e_z)=-f_B, quad E_("kin")=2a^2, quad Q=2(1-a^2)$]
#grid(columns:(1fr,1fr),gutter:14mm,
 [*Geometry restricts; constitutive contact acts.*
 #v(2mm)#note([The retained guided-link construction has a real common patch, balanced normal preload and unit viscous tangential response. Heat and complex impulse diffuse along its four-node interface. The inside panel uses an interface receiver; the exterior panels do not see through opaque bodies.])],
 [*An interaction vertex is an executable map.*
 #align(center,interaction-vertex())
 #note([Incoming lines carry Holons; the vertex carries the interaction tensor and the outgoing line its generated Holon. Joining vertices contracts compatible port axes. A screen crossing alone is not a vertex.])],
)
#v(3mm)#note([Figures and force/heat law are reused from Information Chemistry plates 10–11. The contact law is a declared physical construction, not inferred merely from the appearance of linked tori.])

#pagebreak()
#title("04","Released activity travels through the body and beyond","Counterpropagating currents on a trefoil show kinetic release as an evolving geometric operation.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Prepared impulse · $k=0$*\ #v(2mm)#knot-face("trefoil_3_1_0",width:90mm,height:72mm)],
 [*Propagated joint field · $k=12$*\ #v(2mm)#knot-face("trefoil_3_1_12",width:90mm,height:72mm)],
 [*Later field and moving carrier · $k=24$*\ #v(2mm)#knot-face("trefoil_3_1_24",width:90mm,height:72mm)],
)
#eq[$R=mat(3/5,-4/5;4/5,3/5), quad d=15/16, quad sum_i (P_i^k+Q_i^k)=2$]
#eq[$#ket($u_B$)=hat(C)_(B A)b_A (#ket($x_A$)), quad y_B=#bra($r_B$)b_B (#ket($x_B$))$]
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The geometric instance.*
 #v(2mm)#note([The existing source transports two complex wave ports along incident edges, with the displayed scattering, attenuation and explicit heat deposition. An invertible material flow carries the knot. The figures show this finite field law; they do not assert that a crow is implemented by a trefoil.])],
 [*The communicating ecology.*
 #v(2mm)#note([A bird's gaze, calls and movement can expose its attention without a deliberate message. Other birds receive the actual light/sound cues. The laboratory recovered social learning of dangerous human faces; gaze alone as sufficient teaching is a further hypothesis. The same boundary relation applies between internal model regions.])],
)
#v(3mm)#note([No intent flag is required for a physical coupling. Avoidance and inhibition change pathways and responses; they do not undo an interaction that occurred. Sources: the retained knot-wave construction; the July 21 laboratory crow account; Cornell, Marzluff & Pecoraro, 2011.])

#pagebreak()
#title("05","A collapsed image need not exhaust the interior","The same complex torus field becomes distinguishable through another receiver.")
#grid(columns:(1fr,1fr),gutter:12mm,align:center,
 [*Nearly collapsed real face · $tau=7/5$*\ #v(2mm)#geometric-face("near_fold",width:139mm,height:80mm)],
 [*Changed receiver · same field and clock*\ #v(2mm)#geometric-face("reopened",width:139mm,height:80mm)],
)
#eq[$F_tau=I+tau A+frac(tau^2,2)A^2, quad A^3=0, quad det_(CC) F_tau=1, quad det_(RR)(op("Re")F_tau)=(1-frac(tau^2,2))^2$]
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The full generating object continues.*
 #v(2mm)#note([The retained complex polynomial flow is invertible. Its real receiver loses rank at $tau^2=2$; the displayed rational cut is nearby. The second receiver exposes distinctions the first attenuated. The source geometry and imaginary current were not replaced by the first image.])],
 [*Recall is reconstruction from available modes.*
 #v(2mm)#note([A cue can recruit a partial field and direct refinement toward a noticed discrepancy. This does not require a stored screenshot. If two compatible interiors share the cue but differ at a requested detail, that cue alone cannot determine the detail; a further interaction can separate them.])],
)
#eq[$q(x_1)=q(x_2) and rho(x_1)!=rho(x_2) => not exists d, rho=d compose q$]
#note([Existing criterion: `ReceiverTransformer.excludesInsufficiency`. The user's imagery account motivates the construction, not a neurological measurement. A physical event horizon additionally restricts which signals are accessible.])

#pagebreak()
#title("06","Torus currents expose the lattice–mode distinction","Potential, circulation and local curvature are different components of the same situated field.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Exact potential current · $k=0$*\ #v(2mm)#toroidal-modes(kind:"exact",k:0,width:84mm)],
 [*Full current and period cycles · $k=0$*\ #v(2mm)#toroidal-modes(kind:"full",k:0,width:84mm)],
 [*Full current after four steps*\ #v(2mm)#toroidal-modes(kind:"full",k:4,width:84mm)],
)
#eq[$#ket($j$)=d #ket($phi$)+#ket($h$)+#ket($kappa$), quad #ket($xi$)=hat(E)#hk($H$), quad E_(k+1)T_k=U_k E_k$]
#eq[$dot(xi)=dot(E)x+E dot(x)$]
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The geometry carries a specified finite current.*
 #v(2mm)#note([These original composition-atlas functions use the 16×16 periodic carrier, four shape modes, two period directions and the retained local-curvature current. The exact-current panel omits the latter two terms by its declared reading. The full panels retain them and their supplied evolution.])],
 [*A mode representation must conduct the same effect.*
 #v(2mm)#note([A closed modal action executes without expanding the lattice. A new contact can expose an omitted direction; its residual identifies the needed mode. Encoder motion contributes the displayed derivative. Exact invisibility, tolerated error and dissipation are different calculations.])],
)
#eq(memory-equation)
#note([The last equation uses $dot(x)=A x+B z+f$, $dot(z)=C x+D z+g$, $z=K x+r$. Existing owners: reflected boundary memory, joint receiver descent and kernel reduction. New binding: `Holon.ofEvolution_receive_eq_encoded`.])

#pagebreak()
#title("07","A local drive changes a coupled geometric interior","Constitutive contact connects the field equation to the model's material differential.")
#grid(columns:(1fr,1fr,1fr),gutter:8mm,align:center,
 [*Initial interacting domains*\ #v(2mm)#woven-face("lobes_0",width:90mm)],
 [*Contact admitted · four steps*\ #v(2mm)#woven-face("lobes_4",width:90mm)],
 [*Same drive · contact removed*\ #v(2mm)#woven-face("lobes_off",width:90mm)],
)
#eq[$c_i=1/2+q_i^2, quad E=frac(c_1^2+c_2^2,2)+frac((q_1+q_2)^2,2)-q_1, quad q'=q-frac(1,8)nabla E$]
#eq(scattering-equation)
#grid(columns:(1fr,1fr),gutter:14mm,
 [*Existing constitutive geometry instance.*
 #v(2mm)#note([The retained lobe construction carries its contact cross term: driving one domain moves the other when contact participates. This supplies a mechanical instance of differential coupling. The scattering equation below it is the separate existing native boundary/interior operator, with its own declared chart.])],
 [*The native model consumes its own operators.*
 #v(2mm)#note([Resident sections are numerical views; relation, frame and field owners supply their structure. The selected body must compose transport, learned reaction, joint generation and the adjoint on the same material. A separate fitted field surrogate remains a different application.])],
)
#eq(tangent-equation)
#note([Formal/software design: `docs/HOLON.md`, `docs/HNN_FORMULA.md`, Rust library guide and Athena blueprint. The existing geometric sources are reused here; this document does not claim a new native image, acoustic or language model run.])

#pagebreak()
#title("08","The elementary algebra remains attached to its geometry","Reusable formal statements and geometric renderers describe the same construction plan.")
#grid(columns:(1.85fr,1fr),gutter:14mm,
 [#set text(size:10pt)
  #table(columns:(1.05fr,2.3fr),inset:3mm,stroke:0.4pt+rgb("888888"),
   table.header([*Holonic operation*],[*Computational notation*]),
   [Receive / contract],[$#braket($r$,$H$) quad "(a face)"$],
   [Compose operators],[$hat(G)_2 hat(G)_1 #hk($H$)$],
   [Rebase],[$#hk($H$)_(F')=hat(T)_(F' arrow.l F)#hk($H$)_F$],
   [Tensor-interact],[$#hk($C$)=cal(I)(#hk($A$) ⊗ #hk($B$))$],
   [Pull back a differential],[$#bra($delta H$)=#bra($delta H'$)D cal(I)_H$],
   [Generate],[$#ket($X(tau)$)=cal(U)_(Theta,K) (#ket($Xi$),h)$],
   [Encode / reconstruct],[$#ket($xi$)=hat(E)#hk($H$), quad #hk($H$)=hat(D)#ket($xi$)+#ket($r$)$],
   [Receive then emit],[$(#ketbra($B$,$r$))#hk($A$)=#braket($r$,$A$)#hk($B$)$],
  )
  #v(4mm)#note([*Verified formal return.* Generated sections and tensor readings use the existing Holon. The encoded-generation square, serial seed equivalence and Core consumer passed Lean. The scalar `Face` documentation now correctly allows noninvertible transformations.])
 ],
 [*Current and information are different readings*\ #v(2mm)
  #geometric-face("torus_entropy",width:82mm,height:67mm)
  #v(3mm)#note([The same toroidal geometry carries an entropy-level receiver. Its hatches are computed from supplied field values; a geometric slope is not automatically an information measure. Geometry, current, receiver and declared units travel together.])
 ],
)
#v(4mm)#note([This synopsis reuses the Information Chemistry receiver, engraving, knot-wave, woven-field and torus-mode sources. The shared presentation module exports those functions and the model equations. The maintained specification is `docs/HOLON.md`; the formula is `docs/HNN_FORMULA.md`; the roadmap alone orders implementation. The September 14 generation/Holon record retains research sources, audit scope and checks.])

#pagebreak()
#title("09","A fractal is a recursive geometric construction","Scale, branching and dimensionality belong to the operator, not to a picture's apparent complexity.")
#grid(columns:(1fr,1fr,1fr),gutter:10mm,align:center,
 [*One composition · four cells*\ #v(3mm)#cantor-dust(1)],
 [*Two compositions · sixteen cells*\ #v(3mm)#cantor-dust(2)],
 [*Four compositions · 256 cells*\ #v(3mm)#cantor-dust(4)],
)
#eq[$F_(i j) (u,v)=lr((frac(u+2i,3),frac(v+2j,3))), quad i,j in {0,1}, quad cal(S)(H)=union_(i,j) F_(i j) (H)$]
#eq[$H=cal(S)(H), quad 4 dot 3^(-D)=1, quad D=frac(log 4,log 3)$]
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The generator is smaller than its resolved geometry.*
 #v(2mm)#note([Four rational maps and a depth specify the displayed Cantor-dust family. Listing its cells requires $4^n$ cells; choosing one particular cell still requires branch information. Under the separation hypothesis, its similarity dimension is the displayed exact logarithmic ratio. The render is a finite cut of that construction.])],
 [*A neural basin is a different fractal question.*
 #v(2mm)#note([The latent-reasoning paper measures settling-time boundaries on finite two-dimensional slices. Basin entropy, a dimension estimate, tensor rank and dynamical sensitivity are distinct. Those findings motivate recursive operator analysis; they do not make every long trajectory necessary for every solver.])],
)
#eq[$#ket($X_(n+1)$)=cal(F)_Theta (#ket($X_n$),h), quad J_(n+1)=D cal(F)_Theta (X_n,h)J_n$]
#note([Existing source routes: `FractalPacking`, scale/phase and generator recurrence owners. Paper: Lai et al., arXiv:2609.04963. The geometric IFS above is an explicit construction, not a rendering of that paper's neural measurements.])

#pagebreak()
#title("10","Analytic generators retain phase, scale and order","Exponential transport, logarithmic dimension and a noncommuting interaction square are operations on Holons.")
#grid(columns:(1fr,1fr),gutter:14mm,align:center,
 [*Two operator orders produce different geometry*\ #v(7mm)#operator-commutator()],
 [*A periodic field has an actual phase carrier*\ #v(2mm)#geometric-face("torus_phase",width:112mm,height:80mm)],
)
#eq[$A=mat(1,1/2;0,1), quad B=mat(1,0;1/2,1), quad H=mat(1;1), quad (B A-A B)H=mat(-1/4;1/4)$]
#eq[$cal(U)_t=exp(t L), quad exp(upright(i)(theta+2pi))=exp(upright(i)theta), quad Gamma(z+1)=z Gamma(z)$]
#grid(columns:(1fr,1fr),gutter:14mm,
 [*The functional law is the construction.*
 #v(2mm)#note([Exponential transports a linear field; nilpotence can terminate its series. Logarithms turn scale ratios into additive lengths and dimension identities. Gamma recurrence carries an analytic generator with its domain and remainder. These do not enter the model merely as floating-point literals.])],
 [*The papers specify usable operators, with scopes.*
 #v(2mm)#note([Tai: split field evolution. Liang: transport/reaction and their complete differentials. Su–Liu: a tropical routing approximation with a finite-temperature defect. Lai et al.: recursive latent dynamics and measured basin structure. The model must compose the actual vector/tensor operations, phase and scale maps.])],
)
#v(3mm)#note([The square uses two exact rational shears and the vector $(1,1)$; it shows order dependence, not a full nonlinear truncation bound. The torus reuses the original geometric/phase receiver. Four-paper analysis and explicit counterexamples: the September 14 transformer-fields/tropical-cells/fractal-generators record.])
