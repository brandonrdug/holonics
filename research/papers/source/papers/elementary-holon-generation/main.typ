#import "../../holonics/computational-holon.typ": *
#show: chemistry-style
#set document(title:"Elementary Holonics: Connected Attention, Learning and Generation",author:"Brandon Duggan / Holonics",description:"Computational Holons through normalized heads, gradients, contact, whole-field integration and geometric decoding.")
#let title=chemistry-title
#let note=chemistry-note
#let eq(m)=block(width:100%,above:2mm,below:2mm,align(center,math.equation(m.body,block:true)))
#let fig(name,width:100%)=image("figures/"+name+".svg",width:width)
#let two(a,b)=grid(columns:(1fr,1fr),gutter:13mm,a,b)
#let three(a,b,c)=grid(columns:(1fr,1fr,1fr),gutter:8mm,a,b,c)
#let status(body)=block(width:100%,above:4mm,below:0pt,note(body))

#title("01","A Holon through an entire generating computation","The figures follow one fifteen-channel complex field through two heads, two layers and an integrated release.")
#three(
 [*Incident field* #v(2mm)#fig("input-geometry")],
 [*After the two-layer interaction* #v(2mm)#fig("layer_two-geometry")],
 [*Integrated field, geometrically decoded* #v(2mm)#fig("integrated-geometry")],
)
#eq[$#hk($H$)_F=sum_i psi_i #ket($phi_i$)_F, quad #hk($H_2$)_F=hat(L)_Theta^2 #hk($H_0$)_F$]
#eq[$x^*=(I-lambda L_Theta^2)^(-1)(1-lambda)h, quad A(x)=sum_i psi_i phi_i (x), quad Sigma_R={x:I_h (x)=1/3}$]
#two(
 [*The picture is downstream of the computation.* #v(2mm)#note([The field amplitudes are produced by the Rust operator chain. The existing toroidal basis then constructs a coherent complex amplitude; an intensity receiver produces the polyhedral surface. None of these panels imports an old rendered scene. The same decoder and threshold are used throughout.])],
 [*The supplied and inferred parts are visible.* #v(2mm)#note([The geometric incidence and two positive kernel charts are supplied. A recorded physical field observation changes head A through the declared gradient step. The new material changes both layers and their integrated field. This is an exact finite CPU reference construction; it does not claim a completed native Athena model.])],
)
#v(3mm)#status([Established-bounded · implemented-exact. Source: `connected_holonic_field/result.json`; the geometric receiver rounds complex coordinates to 24 fractional bits before its exact level-set construction. It retains the rounding bound and original coefficients; no topological equivalence to the unrounded surface is asserted.])

#pagebreak()
#title("02","Heads are parallel charts; layers compose their actions","A current keeps its channel, frame and phase through the whole chain. The displayed edges come from the computed layer matrix.")
#align(center,fig("interaction-chain",width:245mm))
#eq[$Q_h=X W_(Q h), quad K_h=X W_(K h), quad V_h=X W_(V h), quad s_(h i j)=beta op("Re") ⟨ Q_(h i),K_(h j) ⟩+b_(h i j)$]
#eq[$Y_(h i)=sum_(j in E(i)) a_(h i j) U_(h i j) V_(h j), quad Z=X+op("Concat")_h (Y_h)W_O$]
#eq[$X'=N[Z+sigma(G Z+c) ⊙ R_Theta (Z)]$]
#two(
 [*General computational interface.* #v(2mm)#note([Q/K are comparison charts, V carries current, U transports its frame, and E restricts actual participation. Output contraction, residual addition, a gated local reaction and normalization compose a full block. A head is not a new engine; a layer is not a biological scale. Joining these operators is tensor contraction and function composition.])],
 [*The plotted specialization.* #v(2mm)#note([Each of the two layers uses the same two normalized spatial heads, identity value charts, an averaging output map and a sigmoid residual gate. The phase-sensitive contact C follows that mix. Circle area measures current magnitude; color distinguishes phase; line width follows the real two-axis block norm. Sharing the layers is a declared restriction, not a claim that every network must tie its weights.])],
)
#status([Definition for the general block; established-bounded · implemented-exact for the displayed specialization. The full Transformer comparison comes from the supplied field-operator paper, arXiv:2510.03989. The native earlier operator atlas already contains Q/K/V, RoPE, multihead contact, residuals and a gated reaction.])

#pagebreak()
#title("03","Softmax and sigmoid have explicit geometry","Normalization redistributes a whole admitted population; a binary gate is the same operation on two channels.")
#align(center,fig("sigmoid-and-participation",width:250mm))
#eq[$a_j=frac(exp(s_j),sum_k exp(s_k)), quad J=op("diag")(a)-a a^T, quad delta a_j=a_j (delta s_j-sum_k a_k delta s_k)$]
#eq[$sigma(s)=frac(exp(s),exp(s)+1), quad sigma'(s)=sigma(s)(1-sigma(s)), quad J bold(1)=0$]
#two(
 [*Attention is a changing transport relation.* #v(2mm)#note([The right plot varies one log-potential on an actual contact of head A. Increasing it changes every normalized weight in that receiver row. The resulting current also depends on values, relative phase and receiver sensitivity. A common score shift is invisible to this chart; it is not the same as losing all information in the participating Holon.])],
 [*Finite softness is not a hard selector.* #v(2mm)#note([The smooth differential is a covariance/Laplacian. Low-temperature score cells give the tropical comparison under the paper's fixed-key and margin hypotheses. Finite-temperature attention still blends values and carries a nonzero differential. The contact support is supplied separately; a derivative on that support cannot create a missing channel.])],
)
#eq[$delta Y=sum_j a_j U_j delta V_j+sum_j a_j delta U_j V_j+sum_j a_j (delta s_j-op("E")_a delta s)U_j V_j$]
#status([Proved-derived · formal-checked: `HolonicAdjointNormalization`; exact rational specialization: `NormalizedKernel`. Here K is positive rational and s=log K, so no general exponential is rounded into a rational identity. Analytic curves are exterior floating-point plots.])

#pagebreak()
#title("04","Learning changes the operator that transports the field","Both the value current and the comparison material receive the derivative; the source matrices below are actual computed returns.")
#align(center,fig("heads-and-gradient",width:280mm))
#eq[$Y=a V, quad G=frac(partial ell,partial Y), quad frac(partial ell,partial s_(i j))=a_(i j) ⟨ G_i,V_j-Y_i ⟩, quad frac(partial ell,partial V)=a^T G$]
#eq[$ell=frac(1,2) norm(Y-Y_("obs"))^2, quad K'=K-eta frac(partial ell,partial K), quad frac(partial ell,partial K_(i j))=frac(1,K_(i j)) frac(partial ell,partial s_(i j))$]
#two(
 [*One measured material change.* #v(2mm)#note([The observed next complex field comes from the retained toroidal-contact experiment. The library takes a declared Euclidean step on positive K at rate 1/64; it refuses a step crossing the present positive support. The example checks that this receiver loss falls and that the changed kernel changes the integrated output. It does not claim that the observation is exactly representable by one convex attention head.])],
 [*The sign convention matters.* #v(2mm)#note([With p predicted and q observed, cross-entropy has logit gradient p−q; q−p is the descent direction. For half squared probability discrepancy the descent return is Jₚ(q−p). Those are distinct objectives. A scalar loss supplies a covector through its differential; it does not replace the full directional return.])],
)
#status([Established-bounded · implemented-exact. `NormalizedKernel::pullback` returns both operands; its test checks exact tangent–cotangent duality, the gauge null and absent-contact behavior. The new record retains numerical loss and material/output differences.])

#pagebreak()
#title("05","Curved gradients and friction act on the same complex current","The left panel is a two-potential slice of the measured objective; the right is the actual phase contact inside the layer.")
#two(fig("gradient-flow"),fig("friction-current"))
#eq[$delta=y-u x, quad abs(u)=1, quad x'=x+alpha overline(u)delta, quad y'=y-alpha delta$]
#eq[$abs(x)^2+abs(y)^2-abs(x')^2-abs(y')^2=2alpha(1-alpha)abs(delta)^2$]
#two(
 [*The gradient is not a scalar instruction.* #v(2mm)#note([Contours show half squared complex-current discrepancy for receiver 5 while two log-potentials vary. Arrows are the analytic negative gradient in this declared Euclidean chart. A constitutive metric changes the corresponding gradient vector. The full return also includes transported values and frame/material derivatives; these are not implied by drawing one arrow on a loss surface.])],
 [*The contact uses relative phase.* #v(2mm)#note([For the selected witnessed contact 5↔10, u=−i and α=1/4. The arrows compare both currents in the same phase frame. The library matrix contracts their relative slip, and the example verifies the complete quadratic balance exactly. The deposited amount is the computational energy difference; electrical or mechanical units require their specified constitutive calibration.])],
)
#eq[$L=C[(1-g)I+frac(g,2)(A+B)⊗I_2], quad g=sigma(log(1/3))=1/4$]
#status([Established-bounded · implemented-exact for the contact and observed chart; definition for the chosen unit metric and kernel charts. Softmax participation and physical conductance are related through a declared constitutive map, not identified by their being positive numbers.])

#pagebreak()
#title("06","Generation integrates a whole field, then decodes it","The refinement clock is separate from every output coordinate. The final implicit solve and the iterated field obey the same equation.")
#align(center,fig("convergence-and-learning",width:280mm))
#eq[$x_(k+1)=lambda L^2 x_k+(1-lambda)h, quad lambda=1/2, quad (I-lambda L^2)x^*=(1-lambda)h$]
#eq[$(I-lambda L^2)delta x^*=lambda[(delta L)L+L(delta L)]x^*+(1-lambda)delta h$]
#two(
 [*The release converges under stated conditions.* #v(2mm)#note([Each normalized head is a convex current combination; the unit-phase contact and residual mix are nonexpansive in the maximum complex-channel norm. The forced map therefore contracts by at most 1/2. Its fixed point is unique. The plot reports Euclidean receiver norms; these are measurements, not the proof's norm. The exact implicit residual and its material-sensitivity residual are zero.])],
 [*A surface is a decoded product.* #v(2mm)#note([The integrated coefficients excite the toroidal basis, its coherent field creates nodal intensity, and a declared level set produces a new surface. A waveform uses an acoustic reconstruction basis; an image uses spatial channels; text requires its own structured output codec. Decoding these faces does not turn the shared generating law into next-token prediction.])],
)
#status([Proved-derived for the finite contraction under the displayed hypotheses; established-bounded · implemented-exact for the calculated solution and differential. The material step is local supervised learning; the later contraction is inference/integration. Their distinct roles are connected through the same changed L.])

#pagebreak()
#title("07","Leader formation changes what the return can traverse","The physics connection joins material evolution, admissible incidence, flux and dissipation. This plate is a coupled-law diagram.")
#align(center,fig("leader-and-return",width:286mm))
#eq[$Gamma_e=n_e u-mu_e n_e E-D_e nabla n_e, quad partial_t n_e+op("div") Gamma_e=S_("ion")+S_("photo")-S_("attach")-S_("recomb")$]
#eq[$op("div")(epsilon E)=rho, quad partial_s V=-partial_t (L I)-R I+e, quad partial_s I=-partial_t (C V)-G V+i$]
#two(
 [*A new channel is a material event.* #v(2mm)#note([Electron transport, ionization, the electric field and boundary conditions determine leader growth. It changes the channel's conductivity, storage and geometric incidence. The return stroke then propagates current in that altered material; variable L and C contribute their own energy terms. A branching line alone illustrates none of those laws.])],
 [*The computational consequence is specific.* #v(2mm)#note([A fixed-support attention gradient changes present participation; it cannot express birth of a new edge. HNN's corresponding construction must pull its oriented potential/current variation into its existing incidence and material-change owners, then integrate on that changed operator. The fifteen-channel example supplies the fixed-incidence subcase. The active native field supplies constituted scattering and material returns.])],
)
#status([Definition for the displayed conducting-fluid/channel equations; interpretation for the HNN map from leader growth to incidence formation. Source: `FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS.md`. This is not a simulated plasma trajectory or a claim that electrical conductance equals an attention weight.])

#pagebreak()
#title("08","Recursive scale acts on the computational object","A scale map can place the same generated local field at nested sites; its mass and current must transform together.")
#align(center,fig("recursive-field",width:276mm))
#eq[$F_(a b)(x)=frac(x+(2a,2b),3), quad a,b in {0,1}, quad cal(H)=union_(a,b) F_(a b)(cal(H)), quad d=frac(log 4,log 3)$]
#eq[$m_C=sum_(j in C)mu_j, quad p_C=sum_(j in C)mu_j V_j, quad Y_i=frac(sum_C k_(i C)p_C,sum_C k_(i C)m_C)$]
#two(
 [*Dimension comes from a generating relation.* #v(2mm)#note([The displayed hierarchy uses four separated similarities of ratio 1/3. The local field is the newly computed integrated field; the outer arrangement is a declared recursive construction. The support's similarity dimension solves 4·3⁻ᵈ=1. This is a derived chart property, not a dimension inferred from the number of colored pixels or from every HNN's topology.])],
 [*Compression follows the requested action.* #v(2mm)#note([When copies are kernel-equivalent for a receiving head, carry their summed mass and signed/complex current. The exact normalized output then follows the class formula above. Keeping only a mean loses the denominator's role. If a later head or frame separates the copies, refine the class or retain the missing difference; do not assert equivalence from identical appearance.])],
)
#status([Definition for the four-map construction; proved-standard for its similarity dimension under separation; proved-derived · formal-checked for the mass/current attention quotient. This plate connects `FractalPacking`, `AttentionModeCompression` and the same decoded field without claiming learned fractal morphology.])

#pagebreak()
#title("09","Exponentials and modes generate the field","The transcendental operations already appear in phase, participation, scale and integrated motion.")
#three(
 [*Phase and participation* #eq[$u=exp(i theta), quad a=op("softmax")(s), quad s=log K$] #note([Phase changes interference before an intensity measurement. The normalized exponential changes participation. Its logarithmic chart makes multiplicative material ratios additive without deleting the signed/complex transported values.])],
 [*Continuous integration* #eq[$dot(x)=(lambda L^2-I)x+(1-lambda)h$] #eq[$x(t)=x^*+exp(t(lambda L^2-I))(x(0)-x^*)$] #note([For this frozen linear field the exponential propagates every mode together. The implicit fixed point on plate 6 is shared by the discrete and continuous relaxations. Varying operators require their ordered evolution; one matrix exponential would no longer suffice.])],
 [*Recursive scale* #eq[$4 r^d=1, quad d=-frac(log 4,log r)$] #note([At r=1/3 this recovers plate 8. Scale changes the measure used by transport and compression. Fractal dimension and effective rank answer different questions; neither is an arbitrary network width or a count of saved states.])],
)
#v(8mm)
#eq[$x_t=sqrt(overline(alpha)_t)x_0+sqrt(1-overline(alpha)_t)epsilon$]
#eq[$d x=[f(x,t)-g(t)^2 nabla_x log p_t (x)]d t+g(t)d overline(W)_t$]
#two(
 [*Classical generative diffusion supplies a learned field.* #v(2mm)#note([DDPM learns a denoising/noise relation. Score-based models learn a score and integrate the corresponding reverse-time process; the displayed SDE uses decreasing time. DiffWave's bidirectional convolution refines an entire acoustic waveform. The fifteen-channel calculation is a deterministic forced-field reference, not a trained score model. Its integration/decoder interface is the common structural connection.])],
 [*The output can remain internal.* #v(2mm)#note([A reconstructed image or acoustic mode can be received by another interior Holon before any external artifact is emitted. A gaze or motion can also perturb an external observer without a deliberate communication action. In both cases the relevant operation is generated activity crossing an actual coupling boundary; intent and token positions are not universal operands.])],
)
#status([Definition for the frozen linear chart; proved-standard for its exponential solution. External comparisons: DDPM, arXiv:2006.11239; DiffWave, arXiv:2009.09761; score SDEs, arXiv:2011.13456. The supplied Transformer and fractal papers are analyzed in the September 14 research record.])

#pagebreak()
#title("10","The formula must point to the operations that consume it","This synopsis is a view of the mathematical/library contract. Its diagrams do not substitute for that construction.")
#table(columns:(1.0fr,1.55fr,1.55fr),inset:5pt,stroke:0.35pt+rgb("aaaaaa"),
 [*Operation*],[*Mathematical / executable owner*],[*Concrete role*],
 [Holon and tensor interaction],[`HOLON.md`; `HolonTensorLens`; bilinear and resident section operators],[Typed current, tensor/contraction ports, frame, incidence and executable material.],
 [Heads, blocks and covariance],[`HolonicArchitectureCharts`; `HolonicAdjointNormalization`; `AttentionModeCompression`],[Admitted attention, normalized differential, sigmoid derivative, complete mass/current quotient.],
 [Exact reference transport],[`exponentiated_ratio::NormalizedKernel`],[Vector forward action, log-potential/value tangent, adjoint and positive material step.],
 [Native normalized current],[`field/receiver/normalized.rs` and its material pullback],[Grouped exponential, binary restriction, complete discrepancy and returns to both producing arguments.],
 [Native layer graph],[Earlier `operative_atlas`, `NativeFullOperatorSession`],[Q/K/V, phase, multihead contact, residual/gated reaction and their retained carriers.],
 [Contact and integration],[Active operative field/current/material owners; coupled body],[Current and material dynamics on actual incidence; the public model must consume their composed action.],
 [Geometric decoding],[`connected_holonic_field`; existing toroidal basis and exact receiver compiler],[Generated coefficients → coherent amplitude → declared intensity receiver → displayed topology.],
 [Changing incidence and scale],[Physical leader/material guide; `FractalPacking`; mode and recurrence owners],[Derive the contact transition and its transported current; choose a quotient from its future action.],
)
#v(5mm)
#two(
 [*The source-navigation failure was real.* #v(2mm)#note([The formal normalization calculus, architecture block, native old graph, active field adjoints and physical leader construction were documented separately. The previous synopsis imported geometry without making any of those operations consume it. `HNN_FORMULA.md` now supplies a connected operation-level path, and the same path is linked from `HOLON.md`, `RUST_FRAMEWORK.md` and the architecture map.])],
 [*The native assembly has a precise consuming equation.* #v(2mm)#note([The active body must execute its field's current/material action and its output differential on the same changing incidence, then encode the repeated action it actually uses. Existing helpers and the CPU reference do not establish that call. Conversely, this absent consumer does not make softmax, sigmoid, gradients, fractal restriction or learning absent mathematics.])],
)
#v(4mm)#status([Established-bounded · source-inspected for the owner audit. Reproduction and exact numerical returns: `research/experiments/connected_holonic_field/README.md`. Formal and library edits, checks and source continuity: the September 14 connected attention/learning/generation record.])
