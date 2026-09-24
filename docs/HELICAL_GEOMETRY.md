# Helical geometry: screw generators, paired faces and continuing transport

[project-postulate] Brandon's September 19 question concerns **two parametric helical objects**,
their elementary configurations, either object's independent degeneration, and the interaction
they sustain. The subsequent audit returns this subject to elementary Holonics and its Rust/Lean
library. Proteins are one possible material instance, not the definition or the active consumer.
[THE_REBUILD](plans/THE_REBUILD.md) schedules construction; this guide states the mathematics.
Here **generator** keeps its Lie sense, the screw generator `ξ=(ω,v)`; the object that carries a
generator with an initial configuration, a clock and a carry is a **navigator**
([elementary objects §3](ELEMENTARY_OBJECTS.md#3-navigator)).

## The objects that must be kept together

[definition] [Situated navigator inference](HOLON.md#situated-generator-inference-dormant-modes-and-action)
uses these helical objects as reusable action/material, including their inactive availability
and later receiving use. Rotor-state transport and knot manipulation provide concrete source
comparisons in the [September 21 synthesis](../research/records/2026-09-21_SITUATED_GENERATORS_RETAIN_MODES_AND_RELEASE_ACTION.md).
A rotor is the finite specialization of this object: fixed material carried by a phase shift,
with a discrete torus of states and stepping as a winding. An articulated body is an ordered
chain of these objects. [The pair below is a Holonic Interaction contact](#the-pair-is-a-holonic-interaction-contact)
states both. Homeostasis refers to the actual driven return/stability law. The existing
[`Horizon.smith`](../lean/Holonics/Millennium/Horizon.lean)
and [`RatioPresentation.blockTransport`](../lean/Holonics/Geometry/CrossRatio.lean)
connect projective charting to ordered cascades, while the prototype's
[`traversible_chain`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/traversible_chain.rs) kept the physical
port normalization and reflected remainder. These source maps make the Flash testimony's
useful bilateral reading available without refounding the chart or merging distinct operands.

[definition] In a declared oriented Euclidean frame F, a constant screw generator is
`ξ = (ω,v)` and its action on a situated point is `V_ξ(x) = ω × x + v`. The continuing object is
a navigator: the generator **and an initial configuration**, with its parameter/clock and receiver:

```text
|H_a(s)⟩_F = Ĝ_a(s)|H_a(0)⟩_F,       Ĝ_a(s) = exp(s ξ̂_a).
ξ̂_a = [[ [ω_a]× , v_a ], [ 0 , 0 ]].
```

[definition] One pair has two navigators: two generators, two initial configurations and
parameters `(s,t)`.
An actual incidence or synchronization law specifies which `(s,t)` can interact. Do not silently
identify the parameters because two helices are drawn next to each other. Radii, relative phase,
axis offset, aperture, retained winding and material all affect the receiver. The rotational and
translational components of **one** generator, the two **objects**, and the two factors of a
split algebra are three different decompositions. None substitutes for another.

[established-bounded; source-inspected] `RatVec3`, `RatMat3` and `AffineMap3` in `holonics::geometry` own these coordinate/frame operations. The
[`screw`](../crates/holonics/src/geometry/screw.rs) specialization uses them for a generator,
its orbit jets and paired quadrance; it adds no new frame system or protein codec. The formal
companion is
[`Geometry/ScrewGeometry.lean`](../lean/Holonics/Geometry/ScrewGeometry.lean).
It checks the bracket, translation covariance, invariant pairings, polynomial two-jet and moment
specialization. Axis extraction and general proper rotational recharting currently have exact
Rust tests; they are not silently included in that Lean proof scope.

## A helix and its independent collapses

[proved-derived] Let `(e,f,n)` be a positively oriented orthonormal frame, with `e×f=n`.
For radius `r≥0`, angular rate `a`, axial rate `b`, phase `φ` and axis point c, one orbit is

```text
x(s) = c + r[e cos(as+φ) + f sin(as+φ)] + bs n,
ω = a n,                 v = b n − ω×c.
```

Differentiation gives `x′=ω×x+v`, `x″=ω×x′`, so this is the stated generating law. For `a≠0`
the reduced pitch is `h=b/a`; pitch is not meaningful as that quotient when a vanishes.
Every row below can occur independently on either object of the pair.

| Source conditions | Received orbit |
|---|---|
| `r>0`, `a≠0`, `b≠0` | circular helix |
| `r>0`, `a≠0`, `b=0` | circle |
| `a=0`, `b≠0` | translated line through the initial transverse point |
| `r=0`, `b≠0` | line on the screw axis, even if the generator still rotates other points |
| `b=0` and either `r=0` or `a=0` | stationary point |

[proved-derived] The speed squared is `r²a²+b²`. On the nondegenerate rotating curve,
`κ = r a²/(r²a²+b²)` and `τ = a b/(r²a²+b²)`. In the angular parameter chart these become
`κ=r/(r²+h²)` and `τ=h/(r²+h²)`, hence `r+ih=1/(κ−iτ)` when the denominator is nonzero.
At a line or point the Frenet torsion is not supplied by taking this quotient: the Frenet frame
has degenerated. Keeping the screw generator avoids inventing a torsion for that collapsed face.

[proved-derived] Without normalizing ω or taking a square root, a rotating generator returns
`c_⊥=(ω×v)/(ω·ω)` and `h=(ω·v)/(ω·ω)`, with `c_⊥·ω=0` and
`v=−ω×c_⊥+hω`. For `ω=0`, return the translation or stationary case. These are exact rational
operations in the current library. A whole-generator reversal `(ω,v)↦(−ω,−v)` preserves h;
chirality and traversal direction are not the same face.

## Frame transport, pair invariants and noncommuting passages

[proved-standard] For a proper rigid frame change `x′=Rx+p`,

```text
Ad_(R,p)(ω,v) = (Rω, Rv + p×Rω),
V_Adξ(Rx+p) = R V_ξ(x).
```

This is the adjoint realization of a twist; see the authors' [Modern Robotics account](https://modernrobotics.northwestern.edu/nu-gm-book-resource/3-3-2-twists-part-2-of-2/).
The native constructor checks `RᵀR=I` and `det R=1`. An improper frame needs the corresponding
pseudovector convention; an arbitrary affine map is not silently accepted as a Euclidean one.

[proved-derived] In that frame, the two invariant bilinear faces are
`K(ξ,η)=ω·η_ω` and `R(ξ,η)=ω·η_v+v·η_ω`. Translation invariance of R follows from cancellation
of its two scalar triple products; rotation invariance follows from R's orthogonality. K is a
chosen normalization proportional to the rotational Killing form. R is the Klein reciprocal
form with split `(3,3)`: setting `u=ω+v`, `z=ω−v` gives
`R(ξ,ξ)=(u·u−z·z)/2` in a compatible unit chart. Its null cone includes zero-pitch rotations
and pure translations. A geometric line is a nonzero projective Plücker datum with its own
incidence/domain conventions; the entire cone is not automatically an ordinary finite line.

[definition] A physical wrench is the dual operand `⟨τ,f|`, with power
`⟨τ,f|ξ⟩=τ·ω+f·v`. Identifying one screw-coordinate operand with that wrench is additional
material/unit data. Reciprocity of two abstract twists does not itself establish a measured
zero power current. See [Murray–Li–Sastry's screw and wrench definitions](https://www.cds.caltech.edu/~murray/mlswiki/index.php/Rigid_Body_Motion).

[proved-derived] The commutator generator is

```text
[ξ,η] = (ω×η_ω,  ω×η_v − η_ω×v).
```

It records the infinitesimal order defect; a finite holonomy is the corresponding composed word,
not the Lie bracket alone. Two pure translations commute even along different directions, so
“two helices commute exactly when coaxial” is false without nondegeneracy hypotheses. With both
angular parts nonzero, zero bracket forces parallel angular directions and the compatible
transverse-axis relation; pitches can differ. Use the complete bracket criterion through the
degenerate cases. The existing `TransportWord` and connection/curvature laws own ordered
composition and the finite-versus-infinitesimal distinction.

## The actual interaction face and its variation

[definition] At a declared contact population use `Δ=x_a(s)−x_b(t)` and the receiver
`Q=⟨Δ|Δ⟩_F`. This is a quadrance face, not an assertion that the sources are equal when Q agrees.
The source retains both generators, orbit points, parameters and material. Write velocities
`v_a=V_ξa(x_a)`, `v_b=V_ξb(x_b)` and accelerations `a_a=ω_a×v_a`, `a_b=ω_b×v_b`.

[proved-derived] The exact local contact differential and second variation are

```text
D Q = (2Δ·v_a, −2Δ·v_b),
D²Q = [[2v_a·v_a+2Δ·a_a, −2v_a·v_b],
       [−2v_a·v_b,       2v_b·v_b−2Δ·a_b]].
```

These follow by differentiating the same Q in its two parameters. The library's
`PairQuadranceJet` returns this gradient and Hessian; its pullback transports a receiving
covector into the two parameter ports. The `Δ·a` terms matter: omitting them turns the actual
second variation into a Gram approximation. A common rigid motion of both points leaves Q
constant, which supplies a strong invariance check of both orders. The formal rigidity owner's
`constraint_expansion` is the first-order/quadratic displacement source; this specialization
composes it with the generating orbit's velocity and acceleration.

[conditional] An interaction energy `U=Φ(Q)` gives
`D U=Φ′(Q)D Q` and `D²U=Φ″(Q)(D Q)*D Q+Φ′(Q)D²Q`. The second term is the geometric/prestress
return already distinguished by `MechanicalReceiver` and `ConstitutiveModulation`. A dissipative
face has a declared slip map J and material `D=D*⪰0`, with power `⟨J q̇,D J q̇⟩` and force
pullback `−J*D J q̇`. The contact form of `Transport/HolonicInteraction` consumes these operands.
Area, normal reaction, medium, clocks and units supply the physical realization; a linking number
alone supplies none of them. This is how the helical object reaches the Holonic Interaction.

<a id="the-pair-is-a-holonic-interaction-contact"></a>

### The pair is a Holonic Interaction contact

[definition] The slip map of a pair is its relative velocity on the two parameters,
`J=[v_a | −v_b]` with `Δ̇=J(ṡ,ṫ)`. It is the face slip `J_f` of the contact form
`contactForm w J D` (`Transport/HolonicInteraction`); the face's `D_f`, weight and clock remain
declared material. A Holonic Interaction whose declared rate ports carry the pair parameter rates
and whose faces take this slip map is the
[helical pair interaction unit](HOLON.md#the-helical-pair-interaction-unit), the site of an HNN
and the contact of an articulated body.

[proved-derived; formal-checked] [`Transport/HelicalPairInteraction.lean`](../lean/Holonics/Transport/HelicalPairInteraction.lean)
proves, over ℚ at one configuration:

```text
pairSlip_mulVec                J(ṡ,ṫ)=ṡ v_a−ṫ v_b
pairSlip_transpose_mulVec      J*Δ=(Δ·v_a, −Δ·v_b),  so DQ=2J*Δ
pair_face_power                ⟨u,(w J*DJ)u⟩ = w⟨Ju, D Ju⟩
pair_face_power_eq_zero_iff    with null-definite D, zero power ⇔ ṡ v_a=ṫ v_b
pair_face_power_eq_zero_iff_material_null
                               with D symmetric PSD and w>0, zero power ⇔ D J u=0
pairQuadranceTwoJet_eq_slip_contact_geometric
                               Q₂ = ⟨Δ|Δ⟩ + 2(s,t)·J*Δ + ⟨(s,t),J*J(s,t)⟩ + (s²Δ·a_a − t²Δ·a_b)
bilinear_score_eq_polarized_quadrance
                               ⟨a|b⟩=(⟨a|a⟩+⟨b|b⟩−⟨a−b|a−b⟩)/2
```

For positive weight and material definite on attainable slips, the zero-power kernel is
synchronized passage. A semidefinite response can be blind to nonzero slip; preserve that
material kernel. An instantaneous lock is a local rate relation, not proof of periodic closure
or attraction. The two parameters remain independent.
The second variation is the isotropic contact form of the same slip map plus each object's own
`Δ·a` term. A bilinear participation score is the pair quadrance up to the two self-energies,
so the unit-phase chart `β cos(2π(q_i−q_j−φ_ij))` is this pair with zero advance and unit radii.

[definition] The pair parameter rate `u`, spatial slip `J u`, and resident current `q` are
separate charts. A port map `C` from medium co-state to pair rates gives
`M_medium=C* J*D_f J C` and medium dissipation at `J C Gz`. This does not identify `Gz` with
physical configuration velocity. The pair contact owner (`holon::contact`, rebuild step 1)
declares those units and maps.
For features `(Δ,Q,DQ)`, the parameter pullback is
`J*λ_Δ + λ_Q DQ + (D²Q)*λ_DQ`; `PairQuadranceJet::pullback` supplies only `λ_Q DQ`.
Geometry/material/clock derivatives and the chart from field current are additional terms.
A conjugated physical return `A⁻¹FA` agrees with an adjoint construction only under the declared
isometry/duality; the HNN field uses the full derivative adjoint.

[definition] **Winding.** A torus chart reads a phase modulo its closure. The helix
`x(s)=(r e^{i(as+φ)}, bs)` is the lift that retains the winding: two parameters one full turn
apart agree on the circle and differ by `b·2π/a` along the axis. For a coaxial pair the
quadrance is `|r_a e^{iα}−r_b e^{iβ}|²+(b_a s−b_b t+c)²`, the periodic and axial parts
together; a general pair reads both through the same `Δ` with its axis offset and inclination.
`RationalPhase` carries a rational Cayley half-angle and `extra_turns`; its coordinate is
not a rational turn rate. `lifted_winding` and `closes_after` check a supplied finite period,
which a general rational Cayley point need not possess. Order and distance along a source passage are read through the advance, not
through a separate site per occurrence.

[proved-derived; formal-checked] **Phase-carried material.** In any group, fixed material `P`
carried by a phase shift `S` is `phaseTransport S P d=S⁻ᵈPSᵈ`. Stepping conjugates the carried
material (`phaseTransport_add`); a closing shift gives the toroidal chart
(`phaseTransport_add_period`); n uniform steps through fixed material P compose to `(PS⁻¹)ⁿSⁿ`
(`steppedWord_eq_generator_power`). Source-dependent materials or nonuniform steps retain
their ordered word unless a separate action-descent law compresses it.
A forward passage with reflection returns through the producing operands, `A⁻¹FA`, involutive
and fixed-point-free when the reflection is (`reflectedReturn_involutive`,
`reflectedReturn_no_fixed_point`). A closed path of observed boundary relations under one
unknown boundary map closes exactly when the known stage word fixes the boundary image
(`menu_loop_closure`). These are the rotor and Bombe laws without an alphabet. The stepped
machine's state evolution is retained; the fixed-state involution is not a claim about it.

[definition] **Serial chain.** An articulated body is an ordered family of `SituatedScrew`s
with parameters `θ_i`. Its configuration is the ordered product of the finite motions applied to
the initial configuration; column i of its Jacobian is `ScrewGenerator::rechart` of `ξ_i` by the
preceding motion; revolute, prismatic and screw joints are the zero-advance, zero-angular and
general rows of the collapse table; joint space is the torus chart of the revolute phases with
a line per prismatic parameter; `reciprocal_pairing` is wrench–twist power; each link–link or
link–object contact is one pair interaction. Exact finite motions remain supplied `AffineMap3`
actions with their `RationalPhase`; a general affine action is not identified with `exp(tξ)`.
For a continuous chain Jacobian, each supplied finite motion must also satisfy its
generator/parameter differential law; an arbitrary proper rigid matrix with a phase label does
not establish that correspondence. The native chain consumer is #27 and the face derivation #28; their formal counterparts are #62.

[definition] The [winding guide](WINDING_CARRY_AND_PLACEMENT.md) continues these laws: the
carry cocycle behind the winding (`Geometry/PhaseCarry`), a lock as the zero-power direction with
its Farey address and mediant cost (`Geometry/PairResonance`), the determinant, trace sequence
and transfer determinant that phase carriage conserves (`Transport/GeneratorTraceFaces`), and
the holonomy of a cell with harmonic standing relative to node/cell receivers (`Transport/CellHolonomy`).
`holonics::geometry::winding` (phase, carry, odometer, cell holonomy) and `holonics::navigator::{address,trace}` (lock addresses, trace faces) are their exact Rust owners.

[established-bounded; implemented-exact] **The prototype's Rust consumers** (history; rebuild
step 1 ports them to `holon::contact`). At `13f8c734`,
[`holonic_interaction/helical.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_interaction/helical.rs)
constructed `J C` and the checked contact face, medium contact and interaction with an explicit
medium-block split, PSD response, weight, units and clock. It exposed the full `(Δ,Q,DQ)` return
and both kernels; `rank(D J C)=rank(J C)` checks definiteness on the attained slip image.
[`holonic_chain/serial.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_chain/serial.rs)
validated Cayley/prismatic finite charts against their unit-parameter generators and kept clock
rates separate. Its prefix is the local-joint product `base ∘ T₀ ∘ T₁…`, matched by
`SerialScrewChain.serialFoldl_eq_configuration`. Link contacts form one full `J_chain* D J_chain`
including cross-joint terms; the all-prismatic target preimage keeps its nullspace, limits and
endpoint equation. Broader finite screw flows and the generic continuous Jacobian proof remain
open. The [return and receipts](../research/records/2026-09-21_PAIR_CONTACT_SERIAL_KINEMATICS_AND_THE_RESIDENT_QUADRANCE_RETURN.md)
give the exact controls.

## Two-sided angles are an algebraic chart of this construction

[definition] The record's two-sided algebra `A_k=ℝ[ι]/(ι²−k)` and the conic
`C_k²+kS_k²=1` use related but different generators: the trigonometric exponential is generated
by `iι`, whose square is `−k`. Stating that distinction avoids swapping the circular and
hyperbolic signs. The existing half-angle chart is
`C_k=(1−kt²)/(1+kt²)`, `S_k=2t/(1+kt²)`, with denominator domain retained. Its addition law is
`(C,S)(C′,S′)=(CC′−kSS′,SC′+CS′)`.

[established-bounded; source-inspected] `Geometry/TwoSidedIdentityAtlas` and the prototype's
[`identity_atlas`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/identity_atlas.rs) return bounded polynomial
identities of these declared charts. At `k=0`, the algebraic conic contains
both `C=1` and `C=−1`; the connected normalized flow through `(1,0)` occupies only the first.
An identity can be correct on that physical branch and false on the entire algebraic fibre.
The receiver's domain decides which claim is being made. A test of omitted-component coverage
does not mean an exact algorithm spontaneously invented a false relation on its supplied domain.

[definition] The Gram chart `G=K+ιR` is a compact pair/triple receiver for screw data. Its
adjugate/Jacobi polynomial identities are valid where evaluated, but it omits orbit radius and
relative phase. Two objects' independent line/circle/point collapses must be read from their
navigators (generators and initial points), not inferred from two idempotents of one `A_+1`
element. Specialization can add identities; do not call a generic Gröbner basis the complete
special-fibre ideal without checking it. The prototype's `identity_atlas::screw_gram_point`
consumed the shared screw pairings.

[interpretation] Constant-curvature, Lorentzian and double-rotation extensions remain maps to
derive through the existing metric/connection owners. A generic double rotation on S³ has a
torus orbit; it closes as a torus knot only for commensurate rates with the appropriate nonzero
radii. Changing the algebra's parameter alone does not construct every curved-space action or
all nine Cayley–Klein geometries. This refinement retains the broader question while identifying
the action and metric needed for each extension.

## Landmarks and Holonic Compression already have owners

[established-bounded; source-inspected] The source chain predates this helical discussion:

| Required relation | Existing owner and consuming use |
|---|---|
| Phase closure, windings and arithmetic landmarks | `LandmarksAndModuli`, `Farey`, `Polarity`, the retired [`winding_inertia`](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/geometry/winding_inertia.rs); period/modulus and doubled-angle relations already connect finite navigators to exact algebraic faces |
| π/e as normalized generating constraints | `PiIterationConstraint`, `MachinPhaseConstraint`, the retired [`exact_analysis`](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/geometry/exact_analysis.rs); [September 11 recovery](../research/records/2026-09-11_PI_AND_E_CONSTRAINT_IDENTITIES_HAVE_ORIENTED_GENERATOR_FACES.md) retains branch, winding, independent navigators and remainder |
| Named critical parameter | The actual `CopsonDeBruijn*` or `RH/DeBruijn*` source family; [the maintained distinction](CONSTRAINT_MODES_AND_RECEIVER_FACES.md) prevents conflating the two constants |
| Inferred navigator/factor family | `GeneratorInference`, `GeneratorFactorization`, `GeneratorObservationScope`, `holonics::ratio::linear` factor owners (the bilinear owner is [history](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/exact_linear/bilinear.rs)); supplied navigators and inferred parameters are stated separately |
| Lossless continuation at the admitted receivers | `ReceiverHistoryCompression`, `GeneratorModeQuotient`, `JointReceiverDescent`, the retired [receiver factorization](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/exact_linear/contextual.rs); preserve `E T_g=U_g E` and the decoder, not merely a present rank |
| Cost, mass and tolerance | `ReceiverCodeCost`, `AttentionModeCompression`, `AccumulatedReceiverDefect`; retain encoding/decoder work, complete class mass and transported residuals |

[proved-derived] A useful helical compression bridge can be written now. For two situated initial
configurations let `y=(x_a,1,x_b,1)` be the eight-coordinate concatenation of their two
homogeneous four-vectors. Each admitted finite affine motion acts on its corresponding block.
Their quadrance is `Q=yᵀS_h y`, where `S_h` embeds the six-coordinate spatial receiver
`S=[[I,−I],[−I,I]]` at indices `(0,1,2,4,5,6)` and has zero rows/columns at the two homogeneous
positions `(3,7)`. The initial moment is symmetric rank one and both homogeneous coordinates
are fixed to one. The product-current identity `Z=y⊗y` and its finite transport are
the existing moment receiver's source relation. An invariant receiving row space supplies an exact
reduced recurrence. This does not derive an exponential from a screw generator: a finite map is
accepted only as an exact proper affine action supplied by the caller, and a phase label is bound
only by the supported Cayley z-rotation/identity-partner relation.
This follows by the product rule and introduces no new learner or enumeration of a trajectory.
The phase adapter treats the caller's integer as extra full turns per elementary Cayley passage.
For a closed period it retains the polygon winding and returns the lifted value
`polygon + period·extra_turns`; a nonclosed chart period returns its exact endpoint discrepancy
instead of a winding. An ordered-word witness retains the complete admitted word, including
repeated generators.
The receiver factorization is already
`HolonicQuadraticMomentCondensation.contract_quadraticMoment_eq_enumerateQuadraticReceiver`:
take a singleton support of weight 1, source current `(x_a,x_b)`, and the block receiver
`S=[[I,−I],[−I,I]]`. `ScrewGeometry.pair_quadrance_is_existing_moment_contraction` checks
this concrete specialization. The dynamic product-rule equation above is a derived relation
here, not a claim that the new Lean file proves an analytic flow theorem or that a new HNN
device reduction was executed.

[conditional] For an exact discrete transport T of that product current, the existing receiver
factorization constructs U precisely when `E T=U E`, equivalently `ker E⊆ker(E T)`. Otherwise
its separator is explicitly scoped to the ambient linear moment space; it is not automatically a
physically realizable screw-pair variation, because symmetry, rank-one, homogeneous and source
clock constraints still apply. `ReceiverHistoryCompression` extends the commuting square through
every admitted ordered word. A changed navigator or receiver contributes `Ė+E L−U E`, already
owned by `ChangingReceiver`; the omitted interior cannot be deleted merely because the current Q
agrees. This gives the actual join between helical navigators, identity relations and continuing
compression.

[definition] Geometric landmarks include axis/rank degeneracy, zero bracket, contact-boundary
events, commensurate phase closure and changes of admissible receiver. Each is a constraint with
a source and branch, not an authored salience score. The polynomial atlas can infer algebraic
relations among selected faces; existing recurrence, phase and analytic owners carry their
generating conduct. No one chart promises to enumerate all constants or all identities of all
function classes.

## Connection to HNN and scope of the returned construction

[definition] The [pair interaction](#the-pair-is-a-holonic-interaction-contact) is the HNN's
site. Its navigators (generators with initial configurations) are the field's junctions, its
admitted pairs the arcs, its phases the context, its slip map and jet the participation/contact
operands and its pullback the local adjoint of [HNN_FORMULA](HNN_FORMULA.md). The prototype's
incident field executed only the zero-advance, unit-radius collapse of this pair, on a ring with
one site per source cell; the
[design record](../research/records/2026-09-21_THE_HELICAL_PAIR_INTERACTION_IS_THE_HNN_SITE_AND_PHASE_CARRIES_CONTEXT.md)
records that audit and the prototype's [machine contract](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#situated-generator-and-receiving-composition)
the packets meant to replace it. The constant-navigator closure is the exact reusable
specialization; changing material, noncommuting contacts and nonlinear refinement retain their
source equations and residuals through the same unit.

[established-bounded; source-inspected] `holonics::geometry::screw` holds the Euclidean screw
generator, the local pair differential and the frame/degeneration controls. They do not claim a
trained conversation return, a calibrated molecular force law, all curved-space motor
actions, or a global closure of every nonlinear field. Those boundaries identify further
mathematical terms, not a reason to reset the framework's already returned capabilities.

## The bracket as an inferred relation

[established-bounded; computational-witness] The prototype's
[helical field consumer](../research/records/2026-09-20_NATIVE_INCIDENCE_FORMS_AND_REUSES_THE_HELICAL_GENERATOR.md)
used `ScrewGenerator::bracket` to supply exact reference observations in a declared common frame.
Incidence constructed `s=ξ`, `c=η−ξ`, and one field body formed their relation and normal
material. The held pair returned the exact bracket `(−24,−22,7,47,52,6)` through its inferred
contextual section, while the normal prediction kept its finite-prior residual. The section was
reused on another condition, and the inferred two-direction condition fibre, transported to
another source, yielded plural output. Orbit configurations, finite motion, closure and physical
material keep their owners and hypotheses above. In the [HNN formula](HNN_FORMULA.md#the-incident-word)
the same dependency enters the standing/difference reaction with matching port/material
recharting; the bracket is not replaced by an authored operator.
