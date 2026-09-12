# Prediction as prepared transport; release as boundary current

[project-postulate] Brandon's September 12 continuation asks for physical prediction: the
preparation and release of a throw, leap, gait or communicative action, with energy, motion,
observer volumes, Einstein coupling, higher derivatives and statistical receivers derived
together. His phrase “compression is intelligence is navigation” identifies the constructive
programme. It does not request a trajectory archive, an authored confidence/reach governor,
or a new engine. The returned mathematical operators below serve that programme directly.

## 1. Recover the Leap, without restoring the retired mechanism

[historical; source-inspected] The laboratory source is
`/home/b/Workspaces/laboratory/src/holobrochos/INTUITIONS/lineages/the-swing-leap-friction.md`
(64 lines), especially the June 28–30 source coordinates `da61487c` and `47c0dddb`. It joins
the preparatory swing, an outward leap across unresolved propagated turns, and rebasing at
the next contact. It explicitly rejects carrying reach as a counter. The same thread already
survives in this repository's July 13 `THE_MEDIUM_CLOSES_THE_STROKE` and
`THE_FLOCK_THE_JOINT_AND_THE_FOLD` records, the July 21 communicating-field correction, and
the September 8 boundary-flux construction. “Leap” was not absent from this repository.

[definition] The recovered useful relation is preparation through a contemporary grip,
release into a mode of propagation, and renewed contact. A grip includes body geometry,
material, contact partner and medium. The historical bit-width/reach counters, master-pole
and scalar flock-confidence constructions are not this relation and are not restored.
The old capitalized primitive inventory records agent terminology at its historical date;
Brandon's present lowercase leap/throw names the physical construction being developed.

## 2. Deterministic prediction is prospective transport of a source family

[definition] Let z contain the situated body, relevant medium/field conditions and current;
let a denote a supplied preparation/release configuration, and let
`Φ_(t,t₀)^a(z)` be the admitted deterministic evolution. A receiver R reads

`B_(t,t₀)^a(z)=R_t Φ_(t,t₀)^a(z)`.

For an actual observation o, the prediction is the image of the compatible source fibre
`F_o={z:O(z)=o}` under B. This is already `ReceiverPotential.outcomes`; a dynamical law and
its reduced sufficient state describe it without storing a sequence of past states. Prediction
does not require selecting a source from F_o. A point, family, constraint or enclosure is an
appropriate result according to what the supplied conditions determine.

[definition] A physical predictive model has its own material current and a declared encoding,
decoder and source correspondence. Its comparison is
`R_world Φ_world(z) - D Φ_model(Ez)`, with the complete residual before a loss is read.
The neural/electrical representation is a physical process; the prospective external event
need not already have occurred. This distinguishes a realized predictive current from a
claim that an imagined object has been physically created outside the organism.

[proved-derived; formal-checked] The standing quotient relation `qT=Uq` makes such a reduced
prediction exact for its admitted future family. A presently output-null direction need not
be future-null. New `MarkovKernel.expectation_dirac` in `HolonicDiffusionCharts` proves

`E_(B_*μ)[f]=E_μ[f∘B]`

for a finite deterministic map B, using the existing pushforward owner. Thus a declared
measure μ on unresolved sources induces probabilities by transport:
`Pr(landing∈A)=μ(B⁻¹A)`. No random choice is needed to execute B or compute this probability.
The measure and its support/conditioning remain declared; no uniform distribution is imposed
on an arbitrary fibre.

[definition] Selecting an action can be a deterministic source synthesis problem
`a∈{a:B^a(F_o) meets the requested constraints}`. Robust containment, an expected objective,
or an admitted risk tolerance are different tasks. None is a mandatory universal certainty
gate for generation. A release condition can instead be a constitutive contact transition
of the actual body. There is no requirement that every choice be a scalar argmax.

## 3. Deriving the coupled Einstein and observer-volume balance

[definition] Use Lorentz signature (-,+,+,+), coordinates x⁰=ct, metric-compatible
Levi–Civita connection ∇, and a matter action with its constitutive fields and boundary data.
On a suitable smooth domain write

`S = c³/(16πG) ∫(R-2Λ_cos)√(-g)d⁴x + S_m + S_boundary`,

`δS_m = -(1/(2c)) ∫ T_μν δg^(μν)√(-g)d⁴x`.

The gravitational boundary term or compactly supported variation supplies the boundary
condition; the derivative term may not silently be discarded when the boundary varies.
π, c and G retain their mathematical/unit roles; π is not replaced by a floating literal.

[proved-standard] Expanding the variation gives
`δ√(-g)=-(1/2)√(-g)g_μν δg^(μν)` and
`g^(μν)δR_μν=∇_α V^α`. After the matched boundary variation, the bulk coefficient is

`δS_bulk = c³/(16πG) ∫[G_μν+Λ_cos g_μν-(8πG/c⁴)T_μν]δg^(μν)√(-g)d⁴x`.

Arbitrary admitted metric variations therefore give
`G_μν+Λ_cos g_μν=(8πG/c⁴)T_μν`. Contracted Bianchi, ∇g=0 and constant nonzero coupling
give `∇_μ T^(μν)=0`. This couples geometry to matter; the matter/constitutive equations
still come from S_m. [Einstein–Hilbert and matter variations](https://www.damtp.cam.ac.uk/user/tong/gr/grhtml/S4.html).

[proved-derived; formal-checked] The existing `EinsteinFluidDynamics` in
`NavierStokesCurvedTransport` already derives the conservation consequence from its supplied
field equation, Bianchi and metric-compatible divergence. Its interface is abstract: it
does not itself construct a spacetime metric/connection or calibrate every stress law.
`ReceiverStressEnergy` and `HolonicMassShellFace` supply the finite observer and Lorentz
algebra. Those returned constructions are reused rather than promoted to a solved GR model.

[proved-derived] Contract with an actual observer vector field U, lowered by g:
`J_U^μ=-T^(μν)U_ν`. For symmetric T and a subsystem source `∇_μT^(μν)=f^ν`, the product rule gives

`∇_μJ_U^μ=-f^νU_ν-T^(μν)∇_(μ U_ν)`.

Proof: differentiate both factors; exchange μ,ν in the antisymmetric part of ∇U and use
T symmetry to cancel it. If U is Killing, the second term vanishes. For a general moving,
accelerating or deforming observer it remains: energy is an observer-dependent contraction,
not a universally conserved scalar attached to a coordinate box.

[proved-derived; formal-checked] New `Physics/ObserverBoundaryCurrent` proves that symmetric
contraction and reduces the explicit product-derivative jet to the displayed force/observer
terms. It also proves the Killing specialization and cancellation of a matched internal
interface between two local balances. Its finite derivative arrays are supplied covariant
jets in the chosen chart; it does not claim a new manifold integration theorem.

[proved-derived] For an oriented worldtube W with initial/final caps and lateral boundary B,
covariant Gauss applied to this vector current gives the complete release balance

`∫_(∂W) J_U^μ dΣ_μ = -∫_W[f·U+T:sym(∇U)]dV_g`.

Equivalently, using oriented cap charges, endpoint change plus outward lateral flux equals
the bulk source/observer work. Partition W into adjacent subvolumes: their shared interface
contributions cancel only when the same current is evaluated with opposite orientation;
surface storage or interaction sources must be retained when present. This gives the nested
interior/exterior construction without treating an arbitrary silhouette as an isolated body.

[proved-derived] In a 3+1 local chart, start with `∂_t a+div j=s`. For a volume moving with
boundary velocity w, Reynolds transport adds its sweep term:

`d/dt ∫_(Ω(t))a = ∫_Ω ∂_t a + ∫_(∂Ω)a w·n`

`= -∫_(∂Ω)(j-a w)·n + ∫_Ω s`.

This recovers the September 8 boundary-flux law. **Release is outward current relative to
the moving boundary, not necessarily positive pointwise divergence.** A conserved current
can enter and leave a region with zero local production. Energy, momentum, charge and entropy
have their own densities/fluxes, with entropy production retained rather than assumed zero.

## 4. From stress and contact to prepared motion

[definition] In a local mechanical chart, momentum density is ρv and Cauchy stress is σ.
The moving-volume momentum law is

`d/dt ∫_Ωρv = -∫_(∂Ω)ρv[(v-w)·n] + ∫_(∂Ω)σn + ∫_Ω f_body`.

Time-integrating its traction and source gives impulse, including advective momentum crossing
the boundary. Splitting body, medium and field stress gives interaction forces f_i whose sum
cancels in the complete closed system; no instantaneous isolated two-body action is assumed.

[proved-derived] Articulated coordinates q and body inertia M(q) give the mechanical kinetic
energy `K=(1/2)q̇ᵀM(q)q̇`. For potential V and Rayleigh dissipation D, the Euler–Lagrange
equation with contact is

`d/dt(∂K/∂q̇)-∂K/∂q+∂V/∂q+∂D/∂q̇ = B(q)u+J_c(q)ᵀλ`.

Pair it with q̇. The chain rule for K and V gives

`d(K+V)/dt = uᵀBᵀq̇ + λᵀJ_c q̇ - q̇ᵀ∂D/∂q̇ + ∂_t V - ∂_t K`

where the explicit-time term in K uses its partial derivative holding q,q̇ fixed. The last
two terms vanish for time-independent material/forcing potentials. Thus the preparation
cycle distributes supplied work into motion, elastic/electrical storage, contact work and heat;
it is not one neuron crossing one immutable activation-energy barrier.

[definition] A unilateral contact chart can impose `g_c(q)≥0`, `λ≥0`, `λg_c=0`, with its
impact/friction law. Release changes the admitted contact relation; for smooth separating
motion, the supporting contact force becomes zero and the gap opens. Walking may maintain
other contacts, swimming requires continuing viscous actuation, and speech is often sustained
rather than a single impulse. “Release” here is broader than a force-free projectile.

[proved-derived] For a contact point r(q), virtual work gives
`δW=f·δr=(J_rᵀf)·δq`; torque about a reference is `r×f` and rotational power is `τ·ω`.
A supplied slip law `f_A=-c(v_A-v_B)`, `f_B=-f_A`, c≥0, dissipates
`c||v_A-v_B||²`; the relative mode relaxes while the complete momentum mode survives.
This is the existing two-body boundary example. Gear/lever changes exchange torque and
angular velocity at the corresponding power balance; they do not amplify energy.

[definition] Torus/link geometry and gyroparallelograms supply frames, moment arms, contact
incidence and noncommuting orientation maps. Force magnitudes additionally require stiffness,
preload, constitutive friction and source data. Material rod twist, Frenet torsion, gyrogroup
gyration and spacetime connection torsion are distinct typed constructions. Ordinary GR's
Levi–Civita torsion is zero while bodies can twist and carry angular momentum. The existing
four-force-sector and gyrogroup owners are therefore used at their stated scopes, not as an
unsupported universal tribological formula.

## 5. Capacitance is a boundary operator with material work

[proved-derived] In a quasistatic dielectric domain with specified permittivity and sources,
varying `U[φ]=(1/2)∫_Ω ε|∇φ|²` yields `div(ε∇φ)=0` in a source-free interior and the
conormal boundary current. Integrating by parts gives
`U=(1/2)∫_(∂Ω)φ ε∂_nφ`. The Dirichlet-to-Neumann map takes boundary potential to this
oriented boundary flux; the physical surface-charge sign follows the chosen domain normal.
Its finite network version is the existing Schur map

`C_eff=L_BB-L_BI L_II⁻¹L_IB`,

with interior sources added when present. Constant-potential gauge/null directions are
quotiented or grounded explicitly. At finite propagation rates the interior's stored energy,
phase and dynamic admittance/memory remain; the static map is not instantaneous universal
communication across the volume.

[proved-derived] For a symmetric positive capacitance chart C and charge Q,
`U=(1/2)QᵀC⁻¹Q`, `V=C⁻¹Q`. Differentiating `CC⁻¹=I` gives
`(C⁻¹)'=-C⁻¹C'C⁻¹`, hence

`U'=VᵀI-(1/2)VᵀC'V`,   `I=Q'`.

Changing geometry/material participates in the work balance. At fixed charge, a generalized
mechanical force is `-(∂U/∂q)=(1/2)Vᵀ(∂C/∂q)V`. These are the explicit coupling terms
behind the capacitance intuition; a naked surface label does not determine C.

[proved-derived; formal-checked] The existing `PortEnergyHeat` now derives the scalar form
`U=(1/2)k(t)Q(t)²`, `U'=VQ'+(1/2)k'Q²`, with `V=kQ` and k an inverse-capacitance
coefficient. Both derivatives are supplied and differentiated by the chain rule. Its previous
conductance/heat balance remains intact. The new term is not absorbed into a vague energy
or activation score.

## 6. Free propagation, mass, charge, spin and higher jets

[proved-standard] For a neutral, spinless test body, variation of proper-time action gives
`Du^μ/dτ=0`, or `ẍ^μ+Γ^μ_(αβ)u^αu^β=0`. A zero proper acceleration can therefore coexist
with nonzero coordinate acceleration. In a stationary weak field,
`g_00≈-(1+2Φ/c²)` and the slow-motion equation reduces to `ẍ=-∇Φ`.
This is the domain of the exact local release chart below.
[Geodesic derivation](https://www.damtp.cam.ac.uk/user/tong/gr/grhtml/S1.html).

[proved-derived] With the consistent weak, static metric
`g_00=-(1+2Φ/c²)`, `g_ij=(1-2Φ/c²)δ_ij`, negligible anisotropic stress and Λ_cos=0,
the leading field equation has `G_00=2∇²Φ/c²` and `T_00≈ρc²`; hence
`∇²Φ=4πGρ`. Together with `ẍ=-∇Φ`, this supplies the source/trajectory coupling.
The application's uniform g is a local prescribed-field specialization of that relation,
not a solution for the entire gravitating source or its backreaction.

[definition] A charged released body instead has Lorentz forcing, and an extended spinning
body has curvature/multipole coupling. At pole-dipole order a standard form is
`Dp^μ/dτ=-(1/2)R^μ_(ναβ)u^νS^(αβ)+f_ext^μ`,
`DS^(μν)/dτ=2p^[μu^ν]+N^(μν)`, with a spin supplementary condition and any electromagnetic
force/torque included in f_ext,N. Spinful release is not automatically geodesic. The source
conditions of these equations matter; no classical rotating torus is assumed to explain every
intrinsic quantum spin. [A contemporary explicit MPD realization](https://arxiv.org/html/2601.21438v1).

[proved-derived; formal-checked] The existing mass-shell owner and positive rest branch give
`E_U²=c²||p_U||²+m²c⁴` and `E_rest=mc²`.

[proved-derived] In the low-velocity chart,
`E_U=mc²+||p_U||²/(2m)+…`. A body's rest mass includes its internal energy; exchanges can
change that mass, and open-body momentum also has boundary flux. The product identity
`(mv)'=mv'+m'v` is not by itself the full external-force law for a body losing matter.

[definition] In one fixed time chart, the position jets are
`v=x'`, `a=x''`, `j=x'''`, `s=x⁽⁴⁾`, `crackle=x⁽⁵⁾`, `pop=x⁽⁶⁾`.
`HolonicPantographicSwingJets` already retains their ordered time-axis and dimension
relations, including the corresponding force derivatives. Along curved spacetime, replace
ordinary derivatives by the appropriate covariant derivatives and retain frame terms.

[proved-derived] For constant m, `F=mx''` implies `F⁽r⁾=m x⁽r+2⁾`; variable m instead gives
`D^rF=Σ_(k=0)^(r+1) binom(r+1,k)m⁽k⁾x⁽r+2-k⁾` for F defined as `(mx')'`.
The same product rule yields

`K'=m v·a`,
`K''=m(a·a+v·j)`,
`K'''=m(3a·j+v·s)`,
`K⁽⁴⁾=m(3j·j+4a·s+v·crackle)`,
`K⁽⁵⁾=m(10j·s+5a·crackle+v·pop)`.

Higher jets therefore measure how the work rate changes through the coordinated motion;
their names alone add no new force or independent activation mechanism.

[proved-standard] A C⁷ motion admits
`x(t+h)=Σ_(k=0)^6 h^k x⁽k⁾(t)/k! + ∫₀^h (h-r)^6 x⁽⁷⁾(t+r)dr/6!`.
A bound on the seventh derivative bounds the remainder by `M|h|⁷/7!`. At an ideal impulse
the smooth-jet hypothesis fails; retain the momentum jump and piecewise dynamics instead
of assigning a finite “pop” to a singularity. Exact π and exp remain mathematical identities
or certified representations. In particular the release operator below is
`exp(tN)=I+tN+t²N²/2` because `N³=0`: no floating approximation to e is involved.

## 7. A derived release/landing operator and its tolerance

[proved-derived; formal-checked] New `Physics/ReleasedMotion` works in a real inner-product
space. For a constant acceleration g,

`x(t)=x₀+t v₀+(t²/2)g`,   `v(t)=v₀+tg`.

It proves serial flow composition, release `v⁺=v+J/m` for m>0, momentum increment J, and

`K(v⁺)-K(v)=v·J+||J||²/(2m)`.

For `U(x)=-m g·x`, it also proves `K(v(t))+U(x(t))=K(v₀)+U(x₀)`. The entire kinetic/potential
exchange is retained even when the total energy receiver stays constant.

[proved-derived; formal-checked] Its full endpoint difference is
`δx(T)=δx₀+Tδv₀+(T²/2)δg`, with norm bounded by
`||δx₀||+|T|||δv₀||+(T²/2)||δg||`. Thus a release's prospective reach depends on the
source uncertainty, time and receiver tolerance. It is not a stored range or probability
counter. Correlated source conditions remain correlated before this norm bound is taken.

[proved-derived] At fixed T>0, the impulse required to reach r is
`J=m[(r-x₀)/T-v₀-(T/2)g]`. For launch from rest with displacement d and variable T,

`K_launch(T)=(m/2)[||d||²/T²-d·g+||g||²T²/4]`.

The square `(||d||/T-||g||T/2)²≥0` gives
`K_launch≥(m/2)(||g||||d||-d·g)`, attained at `T²=2||d||/||g||` when both norms are
positive. This is a derived energy/time constraint for the declared ballistic family,
not a universal metabolic activation threshold or a collision-free path certificate.

## 8. From logarithmic energy to physical statistics

[definition] A physical Gibbs chart has an actual energy H(g), temperature and reference
measure: `p(g)∝exp(-βH(g))`, β=1/(k_B T). The earlier ζ family becomes this chart if a
constituted mode energy is `H(n)=ε₀ ln n`, giving exponent `σ=βε₀`. That energy law must
be supplied/derived for the realization; the words “logarithmic energy” alone do not identify
an arbitrary code length with joules.

[proved-derived] For `Z(a)=Σ_g exp(-βH_a(g))`, differentiating gives
`∂_a ln Z=-β E[∂_aH]`: the derivative of free energy is the expected generalized force
with its negative-gradient convention. For inverse temperature,
`∂²_β ln Z=Var(H)`. The same normalized partition law therefore connects physical response,
Shannon information and source uncertainty once the energy/unit map is present. Deterministic
transport can push this distribution without drawing a random sample.

[definition] Microscopic determinism of every physical process is the project's ontological
postulate, not a theorem derived here from Einstein's equations or a neural experiment.
The returned algorithms are deterministic exactly at their declared source law. Biological
variability, statistical inference and quantum probability keep their stated observation
charts; none supplies an unannounced second native learning mechanism.

## 9. Biokinetics, webs, flocks and communication

[established-bounded; source-inspected] Churchland et al. measured population dynamics during
monkey reaching, with movement-related phase/amplitude organized by preparatory activity.
Kaufman et al. studied preparation in muscle-output-null dimensions. These support a concrete
comparison: changing internal modes need not immediately emit muscle action, yet can prepare
later output. The inspected abstracts/indexed methods do not establish a universal motor
algorithm or physiological determinism. [Churchland et al.](https://pmc.ncbi.nlm.nih.gov/articles/PMC3393826/),
[Kaufman et al.](https://www.nature.com/articles/nn.3643).

[interpretation] A model source has neural dynamics, neuromuscular actuation, body geometry and
world contact as coupled equations. The proposed correspondence is preparatory section →
constitutive release → physical propagation → receiving contact. Its test is prediction of
actual outcome differences under changed preparations and contacts. A presently output-null
mode that affects a later release falsifies a proposed present-only condensation; it is not
discarded merely because no movement was observed yet.

[definition] For spiders, the web supplies tension, stiffness, inertia and contact-dependent
wave transport; it is part of the computation's physical medium. For flocks, local sensory
and mechanical couplings supply a changing interaction graph and propagation delays, not a
central destination register. The existing medium-dependent gait connection and active
interior/boundary records retain these distinctions. Measured turning propagation in starling
flocks provides a relevant external comparison, not an identity between bird heading and
mechanical momentum. [Attanasi et al.](https://pubmed.ncbi.nlm.nih.gov/25264452/).

[interpretation] Speaking releases structured acoustic current; writing releases a structured
electrical/material communication into another system's transport. “Throwing” and “catching”
are useful because the receiving medium and decoder determine the consequence. A reply is
another sourced action, not literally an equal-and-opposite semantic vector. Mechanical
reaction balance applies to the complete body/field exchange. The common computation is
prepared structure becoming externally propagating conduct.

## 10. The P versus NP connection and actual returned product

[definition] This supplies a useful complexity question: can a required target be reached by
a compact executable generator whose preparation, precision, propagation and decoding costs
are uniformly controlled? A short physical trajectory need not be easy to synthesize, and
a short formula can require expensive evaluation or resolution. The existing
`PVersusNPCausalLengthBridge` anchors claimed bounds to a fixed input encoding, machine and
actual step population. Local analytic release synthesis is a constructive intelligence
result; it does not settle all NP witness search. [Official problem scope](https://www.claymath.org/millennium/p-vs-np/).

[established-bounded; implemented-exact] New `exact_linear/released_motion.rs` exports
`ConstantAccelerationRelease` and its domain errors. The immutable chart builds exact
release, flow, position and impulse-receiver matrices. It composes the standing exact
matrix/preimage/factor owners; it owns no trajectory, learned reach counter or mutable
organism. Signed time is available for algebraic comparison; physical forward use declares
nonnegative time. Positive inertial mass and coordinate extent are validated.

[established-bounded; computational-witness] The `predictive_release` application supplies
m=2 kg, g=(0,-10) m/s², starting position (0,1) m, zero initial velocity and a target (4,1) m
after 1 s. The shared solver infers J=(8,10) kg·m/s and launch velocity (4,5) m/s. Launch
work is 41 J. At times 0,1/2,1, the kinetic/potential pairs are (41,20), (16,45), (41,20) J;
total energy is exactly 61 J. Flow compositions agree without stepping through a stored path.
This is a declared uniform-gravity chart, not an Earth calibration or a brain/GR simulator.

[established-bounded; computational-witness] Three unresolved horizontal impulse deviations
(-1/5,0,1/5) kg·m/s, with masses (1/4,1/2,1/4), deterministically land at x=(39/10,4,41/10) m.
The mean is exactly on target, but only mass 1/2 lands within 1/20 m. Expected launch kinetic
energy is 8201/200 J and source entropy is 3/2 bits. A position-only initial receiver also
returns a concrete invisible velocity direction exposed by the future receiver. The
[complete exact receipt](2026-09-12_predictive_release_receipts/predictive-release.json) retains
the source conditions, release and receiver differences; no random sampling is performed.

[established-bounded; process-audit] The focused Cargo `exact_linear` selection passed all
37 tests, including three new release tests. The application completed all assertions.
`bash tools/lean_check.sh ElementaryHolonics.Framework.Physics ElementaryHolonics.Framework.Computation`
completed successfully under Lean 4.33.0 (9107 jobs, mostly replayed), integrating released
motion, changing-capacitance, observer-current and deterministic-measure laws. Final completion
and axiom output are retained in the [formal receipt](2026-09-12_predictive_release_receipts/formal-terminal.txt).
An initial released-motion draft had computability, notation and norm-simplification errors;
these were repaired before accepting the integrated result. Native GPU semantics and the
historical laboratory body are unchanged.
