# Helical geometry: generators, paired faces and continuing transport

[project-postulate] Brandon's September 19 question concerns **two parametric helical objects**,
their elementary configurations, either object's independent degeneration, and the interaction
they sustain. The subsequent audit returns this subject to elementary Holonics and its Rust/Lean
library. Proteins are one possible material instance, not the definition or the active consumer.
The [roadmap](plans/THE_ROADMAP.md) schedules construction; this guide states the mathematics.

## The objects that must be kept together

[definition] In a declared oriented Euclidean frame F, a constant screw generator is
`ξ = (ω,v)` and its action on a situated point is `V_ξ(x) = ω × x + v`. The continuing object is
the generator **and an initial configuration**, with its parameter/clock and receiver:

```text
|H_a(s)⟩_F = Ĝ_a(s)|H_a(0)⟩_F,       Ĝ_a(s) = exp(s ξ̂_a).
ξ̂_a = [[ [ω_a]× , v_a ], [ 0 , 0 ]].
```

[definition] One pair has two generators, initial configurations and parameters `(s,t)`.
An actual incidence or synchronization law specifies which `(s,t)` can interact. Do not silently
identify the parameters because two helices are drawn next to each other. Radii, relative phase,
axis offset, aperture, retained winding and material all affect the receiver. The rotational and
translational components of **one** generator, the two **objects**, and the two factors of a
split algebra are three different decompositions. None substitutes for another.

[established-bounded; source-inspected] The existing `RatVec3`, `RatMat3`, `AffineMap3`,
`LocalFrame` and `FrameRelation` own these coordinate/frame operations. The new
[`screw`](../crates/relational-geometry/src/screw.rs) specialization uses them for a generator,
its orbit jets and paired quadrance. It is exposed through `holonics::geometry`; it does not
add an engine, a new frame system or a protein codec. The formal companion is
[`Geometry/ScrewGeometry.lean`](../formal/elementary-holonics/ElementaryHolonics/Geometry/ScrewGeometry.lean).
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
pullback `−J*D J q̇`. The existing contact/constitutive/adjoint owners consume these operands.
Area, normal reaction, medium, clocks and units supply the physical realization; a linking number
alone supplies none of them. This is how the helical object reaches the Holonic Interaction.

## Two-sided angles are an algebraic chart of this construction

[definition] The record's two-sided algebra `A_k=ℝ[ι]/(ι²−k)` and the conic
`C_k²+kS_k²=1` use related but different generators: the trigonometric exponential is generated
by `iι`, whose square is `−k`. Stating that distinction avoids swapping the circular and
hyperbolic signs. The existing half-angle chart is
`C_k=(1−kt²)/(1+kt²)`, `S_k=2t/(1+kt²)`, with denominator domain retained. Its addition law is
`(C,S)(C′,S′)=(CC′−kSS′,SC′+CS′)`.

[established-bounded; source-inspected] `identity_atlas` and `TwoSidedIdentityAtlas.lean` return
bounded polynomial identities of these declared charts. At `k=0`, the algebraic conic contains
both `C=1` and `C=−1`; the connected normalized flow through `(1,0)` occupies only the first.
An identity can be correct on that physical branch and false on the entire algebraic fibre.
The receiver's domain decides which claim is being made. A test of omitted-component coverage
does not mean an exact algorithm spontaneously invented a false relation on its supplied domain.

[definition] The Gram chart `G=K+ιR` is a compact pair/triple receiver for screw data. Its
adjugate/Jacobi polynomial identities are valid where evaluated, but it omits orbit radius and
relative phase. Two objects' independent line/circle/point collapses must be read from their
generators and initial points, not inferred from two idempotents of one `A_+1` element.
Specialization can add identities; do not call a generic Gröbner basis the complete special-fibre
ideal without checking it. The native `screw_gram_point` now consumes the shared screw pairings.

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
| Phase closure, windings and arithmetic landmarks | `LandmarksAndModuli`, `Farey`, `Polarity`, `winding_inertia`; period/modulus and doubled-angle relations already connect finite generators to exact algebraic faces |
| π/e as normalized generating constraints | `PiIterationConstraint`, `MachinPhaseConstraint`, `relational_geometry::exact_analysis`; [September 11 recovery](../research/records/2026-09-11_PI_AND_E_CONSTRAINT_IDENTITIES_HAVE_ORIENTED_GENERATOR_FACES.md) retains branch, winding, independent generators and remainder |
| Named critical parameter | The actual `CopsonDeBruijn*` or `RH/DeBruijn*` source family; [the maintained distinction](MATHEMATICS_AND_NATIVE_CONDUCT.md#constraint-defined-modes-and-named-de-bruijn-boundaries) prevents conflating the two constants |
| Inferred generator/factor family | `GeneratorInference`, `GeneratorFactorization`, `GeneratorObservationScope`, native bilinear/factor/preimage owners; supplied generators and inferred parameters are stated separately |
| Lossless continuation at the admitted receivers | `ReceiverHistoryCompression`, `GeneratorModeQuotient`, `JointReceiverDescent`, `exact_linear::factor_receiver`; preserve `E T_g=U_g E` and the decoder, not merely a present rank |
| Cost, mass and tolerance | `ReceiverCodeCost`, `presentation_cost`, `AttentionModeCompression`, `AccumulatedReceiverDefect`; retain encoding/decoder work, complete class mass and transported residuals |

[proved-derived] A useful helical compression bridge can be written now. For two fixed affine
generators under a declared common clock, let `y=(x_a,x_b,1)` and `ẏ=L y`. Their quadrance is a
quadratic receiver `Q=yᵀS y`. The symmetric product current `Z=y⊗y` obeys
`Ż=(L⊗I+I⊗L)Z`; Q is linear on Z. Thus derivatives of Q are generated by repeated action of
one finite operator. An invariant receiving row space supplies an exact reduced recurrence.
This follows by the product rule; it introduces no new learner or enumeration of a trajectory.
The receiver factorization is already
`HolonicQuadraticMomentCondensation.contract_quadraticMoment_eq_enumerateQuadraticReceiver`:
take a singleton support of weight 1, source current `(x_a,x_b)`, and the block receiver
`S=[[I,−I],[−I,I]]`. `ScrewGeometry.pair_quadrance_is_existing_moment_contraction` checks
this concrete specialization. The dynamic product-rule equation above is a derived relation
here, not a claim that the new Lean file proves an analytic flow theorem or that a new HNN
device reduction was executed.

[conditional] For an exact discrete transport T of that product current, the existing receiver
factorization constructs U precisely when `E T=U E`, equivalently `ker E⊆ker(E T)`. Otherwise
its separator is the direction a later receiver needs retained. `ReceiverHistoryCompression`
extends the commuting square through every admitted ordered word. A changed generator or
receiver contributes `Ė+E L−U E`, already owned by `ChangingReceiver`; the omitted interior cannot
be deleted merely because the current Q agrees. This gives the actual join between helical
generators, identity relations and continuing compression.

[definition] Geometric landmarks include axis/rank degeneracy, zero bracket, contact-boundary
events, commensurate phase closure and changes of admissible receiver. Each is a constraint with
a source and branch, not an authored salience score. The polynomial atlas can infer algebraic
relations among selected faces; existing recurrence, phase and analytic owners carry their
generating conduct. No one chart promises to enumerate all constants or all identities of all
function classes.

## Connection to HNN and scope of the returned construction

[definition] The same pattern enters HNN as source-conditioned transport, shared local material,
joint field variation, receiving restriction and an economical continuing representation. The
helical geometry supplies explicit examples of the generator/contact/adjoint equations in
[HNN_FORMULA](HNN_FORMULA.md), while its constant-generator closure identifies an exact reusable
specialization. Changing material, noncommuting contacts and nonlinear refinement retain their
existing source equations and residuals. A screw chart does not replace the whole HNN model.

[established-bounded; source-inspected] This increment returns the shared Euclidean generator,
local pair differential, frame/degeneration controls and its Gram-chart consumer. It does not
claim a trained conversation return, a calibrated molecular force law, all curved-space motor
actions, or a global closure of every nonlinear field. Those boundaries identify further
mathematical terms, not a reason to reset the framework's already returned capabilities.
