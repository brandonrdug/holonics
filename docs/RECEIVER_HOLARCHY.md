# The receiving Holon: perspective, flux and compression

[project-postulate] Brandon's September 14 correction places the receiver inside the
construction. It is another Holon with a frame, material, current, internal state and possible
continuations. Its perspective determines an interaction and a face; it is not the human
viewing camera silently placed outside every mathematical diagram. This guide joins the
[computational Holon](HOLON.md), [field architecture](HNN_FORMULA.md),
[active stress faces](CONSTRAINT_MODES_AND_RECEIVER_FACES.md) and
[fluid construction](HOLONIC_FLUID_CONSTRUCTION.md). It specifies their common operation,
not another model owner or construction schedule.

[definition] The [foveation, spatial-audio and music synthesis](../research/records/2026-09-14_HEAR_THE_MUSIC_SITUATED_RELEASE_AND_SELF_MOTION.md)
connects receiver resolution, morphology-dependent transfer, self-motion and whole-section
predictive release. It recovers the chord class/performance distinction and gives a concrete
relative-motion equation and phase-sensitive receiving comparison.

[definition] The [Butler/Koestler comparison](../research/records/2026-09-14_BUTLER_KOESTLER_AND_HOLONIC_CONSTRUCTION.md)
recovers whole/part and receiving-role distinctions, the actual dependence in the CI octant table,
and typed projection/return requirements. Its independent connection and projected-step checks
separate a meaningful geometric proposal from its claimed proof. External invocation/covenant
rules do not replace the physical reception or the HNN law.

## The object, the receiving operation and the displayed face

[definition] The [situated navigator/action law](HOLON.md#situated-generator-inference-dormant-modes-and-action)
makes communication and motor release the same kind of receiving construction. Emitting a word,
an acoustic field or a joint command creates a face; its effect on a participating receiver
depends on that receiver's current, material, frame and available modes. Inferring an action
from a desired effect retains those operands and any compatible alternatives. An observed
response can develop the producing relation without being treated as a universally correct target.

[definition] Relevance can make a retained mode participate again. Current silence establishes
only the current face; the `Standing` and `CausalRelevance` owners quantify over future admitted
transports and receivers. When the question concerns sustained or returning function, the
receiver can read a trajectory, contact sequence or return section rather than one endpoint.
Its clock and viability conditions remain explicit; a policy reset is not evidence of recurrence.

[definition] A receiver is a role of a participating Holon H_R. In a declared contact C,

```text
I_C : (|H_S⟩,|H_R⟩) ↦ (|H_S'⟩,|H_R'⟩,F_R).
```

The receiving map `ρ_R` describes the face of that operation at its stated scope. It does
not replace H_R. An intensity, tensor contraction, file read, geometric projection or
normalized distribution is one possible face. The receiver's state and material determine
what it couples to, how it responds, and which other distinctions it could receive.
The same Holon can be a receiver at one interface and an emitter at another; nesting gives
the [Holarchy](ELEMENTARY_OBJECTS.md#11-holarchy), whose quantities belong to the receiver. No
universal exterior or single privileged I/O axis is selected.

[definition] A field section `Ψ∈Γ(K,E)` can be continuous. Samples, finite coefficients,
factorizations and local jets represent restrictions of it. The generating relation and
its retained parameters/fibres determine further admissible evaluations. Neither the Holon
nor its receiver is exhausted by the particular points displayed. The original
`Foundation/Holon` occurrence/interface/receiver maps and preimage fibre already support
this distinction; the public tensor notation encapsulates its computational presentations.

[proved-derived] Let z=(x_S,x_R) be a local chart of the coupled state and let y=ρ(z,τ).
For differentiable trajectories, the chain rule gives

```text
ẏ = D_Sρ · F_S + D_Rρ · F_R + ∂_τρ.
```

The source and receiver rates include the actual interaction when it changes their states.
A prescribed receiver trajectory is a useful specialization with its motion supplied.
For a linear receiving chart this reduces to `ẏ=q̇x+qẋ`, already proved by
[ChangingReceiver](../lean/Holonics/Transport/ChangingReceiver.lean).
Replacing the receiving Holon by a fixed row vector suppresses a term whenever that row
actually changes. Conversely, a fixed receiver map remains a valid stated specialization.

## No object has one intrinsic face: the receiver atlas

[definition] No object has one intrinsic face
([atlas plan](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md#the-governing-correction)).
Isospectral objects exist, so one global spectrum cannot identify an arbitrary source. Identity is
carried by the organized family of responses under admitted probes, the **response family**

```text
A(X) = { y_{u,R}(t) : u ∈ admitted sources, R ∈ admitted receivers, t ≥ 0 }.
```

The goal is never to assign each object its chord. It is a reproducible, source-accountable,
actively explorable family of responses whose invariances and separations correspond to declared
relations; active local probing separates what one passive global reading cannot.
[proved-derived; formal-checked] `Foundation/CausalChord.spectrum_does_not_determine_response`
exhibits the failure of the spectrum. `Foundation/ReceiverAtlas.fullProbeAtlas_separates` proves
that the full probe atlas (every Markov parameter at every excitation, readout and time) separates
the exact linear systems of bounded dimension, and `theEmbeddingIsNotOneVector` exhibits an atlas
whose every chart is inhabited while no coherent placement exists.

<a id="the-causal-chord"></a>

[definition] **The causal chord.** For a local linearization `ẋ = A_x x + B_x u`, `y = C_x x`, the
receiver-relative transfer object and its chord are

```text
H_x(s) = C_x (sI − A_x)⁻¹ B_x
C_R(x) = { (ω_j, σ_j, support_j, residue_{R,j}) }_j,      λ_j = σ_j + iω_j.
```

It carries more than the spectrum of `A_x`: the poles give modal frequency and decay or growth,
`B_x` says which modes the source can excite, `C_x` which modes the receiver observes, and the
residues weight each source–mode–receiver path. For a non-normal `A_x` the eigenvalues omit
transient amplification, so the receiver reads the resolvent `C_x(iωI − A_x)⁻¹B_x` or its singular
modes. [proved-derived; formal-checked] `Foundation/CausalChord` proves the resolvent identity,
poles ⊆ eigenvalues with strict inclusion for an unexcited or unobserved mode
(`cancellation_is_strict`), and invariance of the whole transfer object under a chart change
(`rebase_transfer`).

[definition] **Its Rust realization is retired.** `holonics::receiver::causal_chord` built
`H(s) = C adj(sI − A) B / det(sI − A)` exactly over `ℚ`. Once `hnn::modes` retired (U2) it had no
library caller, and it was retired at U3's second loop, September 28
([history at `c10acca9`](https://github.com/brandonrdug/holonics/blob/c10acca9/crates/holonics/src/receiver/causal_chord.rs)).
Its pole readings re-entered `ratio::polynomial`, which stays their owner. The laws only it carried
are kept here, so that an owner which needs the chord can re-enter them:
- [proved-standard] **The exact construction.** One Faddeev–LeVerrier recurrence returns both halves
  of `C adj(sI − A) B / det(sI − A)`. With `M_0 = 0`, `M_k = A M_(k−1) + c_(n−k+1) I` and
  `c_(n−k) = −tr(A M_k)/k` for `k = 1, …, n`, it gives `det(sI − A) = Σ_k c_k s^k` and
  `adj(sI − A) = Σ_(k=1..n) M_k s^(n−k)`. The scalar half is
  `ratio::linear::ExactRatMatrix::characteristic_polynomial`. The certificate is the matrix
  polynomial identity `(sI − A)·adj(sI − A) = det(sI − A)·I`, checked in each of its `n + 1`
  coefficients. The closing coefficient is Cayley–Hamilton, the one equation the recurrence does
  not produce by construction. One point is not a certificate: an adjugate corrupted by
  `D·s − 3D` agrees with the true one at `s = 3`.
- [proved-standard] **Cancellation is reported, never lost.** The common factor of
  `C_i adj(sI − A) B_j` and `det(sI − A)` is the modes that source `j` cannot excite or receiver `i`
  cannot observe. `det(sI − A)` divided by the least common multiple of the reduced entry
  denominators is the population the whole declared atlas does not see. At a simple eigenvalue `λ`
  with right eigenvector `v` and left eigenvector `w`, the residue of entry `(i, j)` is
  `(C_i v)(w B_j)/(w v)`, so `λ` is its pole exactly when `C_i v ≠ 0` and `w B_j ≠ 0` (Hautus).
  With `A = diag(1, 2)`, `B = e₁` and `C = e₁ᵀ`, the factor `s − 2` cancels. Widening the readout
  to `C = I` with `B = (1, 1)ᵀ` recovers it: the cancellation belongs to the declared atlas, not to
  the operator.
- [definition] **A pole is named by its factor.** The squarefree decomposition of the reduced
  denominator carries each pole's multiplicity as an index. A rational pole is an exact rational
  (`ratio::polynomial::{rational_root_census, rational_roots_by_lifting}`). Every other pole is
  named by the exact squarefree factor it is a root of, and its Sturm isolating interval is only a
  readout. The half-plane population, with multiplicity, is `ratio::polynomial::half_plane_count`
  (Routh–Hurwitz in its Sturm form). For a symmetric `A` it is Sylvester's inertia of `A`
  (`ratio::linear::inertia::inertia`), and `ratio::polynomial`'s tests hold the two to exact
  agreement.
- [proved-standard] **Residues.**
  - At a simple rational pole `a`, the residue of `N/D` is `N(a)/D′(a)`: both residues of
    `1/(s − 1) + 1/(s − 2)` are one.
  - At a pole of order `m`, the Laurent head carries `m` coefficients:
    `1/((s − 1)²(s + 3)) = 1/(4(s − 1)²) − 1/(16(s − 1)) + …`.
  - At an irrational pole the residue is an element of `ℚ[x]/(f)` for its factor `f`, and it
    specializes at every root at once: `1/(s² − 2)` has the residue `x/4`, which is
    `√2/4 = 1/(2√2)` at `√2`.
- [proved-standard] **The resolvent at a Gaussian-rational point, and the index.**
  - `(sI − A)⁻¹` at `s = σ + iω` is exact over `ℚ` through the realification
    `[[σI − A, −ωI], [ωI, σI − A]]`, inverted exactly and re-checked to a zero residual.
  - The resolvent's order of growth at an eigenvalue is the eigenvalue's index (its largest Jordan
    block), not its multiplicity. The realifications of `[[i, 1], [0, i]]` and `diag(i, i)` are
    `4 × 4` rational matrices, both with characteristic polynomial `(s² + 1)²`; their minimal
    polynomials are `(s² + 1)²` and `s² + 1`.
  - Probed at `s = i + δ` for `δ = 1/10, 1/100, 1/1000`, the defective resolvent's squared
    Frobenius norm grows by more than `10³` a decade (`δ^(−4)`), and the semisimple one's by less
    (`δ^(−2)`). Some coordinate probe of the defective operator has a reduced denominator of
    degree 4; every probe of the semisimple one stays at degree 2.
  - Semisimplicity is decided exactly: the minimal polynomial equals its squarefree part
    (`ratio::linear::ExactRatMatrix::minimal_polynomial`). The semisimple realification has a
    positive definite conserving receiver (`AᵀG + GA = 0`) and the defective one has none (Lean
    `semisimple_imaginary_has_conserving_receiver`, `jordan_has_no_conserving_receiver`). The
    converse is owed in #62.
- [counterexample; measured] **A cospectral pair the response atlas separates.**
  - The two graphs on six vertices have the contacts `(0,2) (0,3) (0,4) (0,5) (1,4) (1,5) (2,3)`
    and `(0,2) (0,4) (0,5) (1,2) (1,4) (1,5) (2,3)`. Their degree sequences, `(4,2,2,2,2,2)` and
    `(3,3,3,2,2,1)`, differ, so they are not isomorphic.
  - Their negative Laplacians `A = −L` share `det(sI − A) = s⁶ + 14s⁵ + 73s⁴ + 176s³ + 192s² + 72s`.
  - Their driving-point numerators at vertex 0 are `s⁵ + 10s⁴ + 37s³ + 62s² + 46s + 12` and
    `s⁵ + 11s⁴ + 43s³ + 73s² + 52s + 12`.
  - The full coordinate atlas (`B = C = I`) separates them at 32 of its 36 probe/readout pairs.
    `Foundation/ReceiverAtlas.spectralTopologicalInsufficiency` carries the driving-point pair as
    data.

[proved-derived] **Rate as a receiver reading.** With a differentiable Hermitian positive metric
`G(t)` and `ẋ = A(t)x + s(t)`, the reading `E_G = x*Gx/2` obeys

```text
Ė_G = Re(x* G s) + x* Σ_G x / 2,        Σ_G = A*G + GA + Ġ.
```

The first term is supplied port work. `Σ_G` measures the source-free change of the reading and may
carry positive, negative and null directions at once; a discrete transport has `T*G_next T − G`.
Under a constant invertible chart `Σ_G` transforms by congruence (`CausalChord.rateForm_congruence`),
so its signature, not the eigenvalues of `A`, is the invariant content; `holonics::ratio::linear::inertia`
(`inertia`, `congruence`; the pullback bound is in [history](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/inertia.rs)) reads it exactly. Integrating, differentiating,
concentrating, maintaining, exploring and releasing are situated roles of one current at a declared
metric, source, receiver and clock, not intrinsic capacities. A rise in a receiver intensity or in
coarse entropy is not heat: physical homeostasis also owes storage, incoming and outgoing power and
a dissipation law (`Physics/{PortEnergyHeat,TwoCellEntropyTransport}`).

<a id="the-reflection-algebra-shared-by-seam-and-swing"></a>

### The reflection algebra shared by seam and junction scattering

[proved-derived] The graph projection `P_D` and its junction scattering `R_D = 2P_D − I` (a
[half-turn about a subspace](ELEMENTARY_OBJECTS.md#the-swing): lossless, doing no work, of determinant
`(−1)^codim`) distribute a one-port current into two shares and recombine them, conserving the
joint norm while individual receivers gain and lose. Self-adjointness is a declared realization
condition (`D_t = Dᵀ`, `K = I + DDᵀ`), not a consequence of an arbitrary `D`
(`Computation/HolonicConstitutiveCirculation`). Centering the conjugate reflection at one half gives
`J = 2P_+ − I`: the invariant component is the seam and the anti-invariant one the transverse defect.

[proved-derived; formal-checked] `L*G + GL = G` holds exactly when `L − I/2` is `G`-skew; this is the
seam `Σ_G = 0` (`CausalChord.seam_iff_gSkew`). For positive definite `G` a `G`-skew operator has
purely imaginary spectrum, so every eigenvalue of `L` has `Re λ = ½`
(`gSkew_eigenvalue_re_eq_zero`, `seam_eigenvalue_re_eq_half`). An indefinite conserving form does
not give that placement. [proved-standard] The converse needs semisimplicity: a positive definite
`G` making `A` `G`-skew exists exactly when `A` is semisimple with purely imaginary spectrum. The
remaining obstruction to a seam theorem is the absent spectral realization, not the rate algebra.

[established-bounded; formal-checked] The atlas's other receivers are Lean owners: Hodge
(`Foundation/HodgeReceiver`), rigidity (`Foundation/RigidityReceiver`), topology
(`Foundation/TopologicalReceiver`), width and release (`Foundation/ReceiverRelease`, with
[`holonics::receiver::release`](../crates/holonics/src/receiver/release.rs)), the separating atlas
(`Foundation/ReceiverAtlas.Separates`), acoustic (`Foundation/AcousticReceiver`) and
physicochemical (`Foundation/PhysicochemicalReceiver`). Their other Rust owners are in history at
`13f8c734`.

<a id="width-and-release"></a>

## Width and release

[definition] Release has one owner, [`holonics::receiver::release`](../crates/holonics/src/receiver/release.rs)
(Lean `Foundation/ReceiverRelease`), whose module doc states the contract: every emission is a
`ReleaseReturn` of one decision law, whose arms are the threshold commit, the certified draw, the
probe and the typed refusal. [proved-derived; formal-checked] The certified draw is the law at
tolerance zero on a key's class reading (`Compression/Landmark/Context/Population.{certified_draw_is_released_at_zero_tolerance,
plural_draw_is_held}`). This section keeps the laws of the Rust carriers retired on September 28
(U3; history at `1bdacc8f`, `crates/holonics/src/receiver/release.rs` and
`crates/holonics/src/receiver/population/health.rs`), for an owner that needs them to re-enter
them from here.
- [proved-standard] **The zonotope enclosure.** An exact zonotope
  `Z = {c + G e : e ∈ [−1, 1]^k}` over `ℚ` maps under an exact linear `M` to the exact zonotope
  `{Mc + (MG) e}`. Under `x_(t+1) = A x_t + B u_t`, the `h`-step image of a box of compatible
  states `Z_x` with a fresh box of admitted inputs `Z_u` at every step is
  `A^h Z_x ⊕ ⨁_(k<h) A^(h−1−k) B Z_u`, with `k_x + h·k_u` generators. Its sup-norm diameter is
  `2·max_i Σ_j |G_ij|`, exact and linear in the generator count, and it bounds the width of every
  compatible set it encloses (`width_le_of_bounds`). The squared-Euclidean diameter is attained at a
  vertex of the generator cube, so computing it exactly enumerates `2^k` sign patterns; an enclosure
  width is declared in the sup norm.
- [definition] **The probe searches** (`Ask`). Over an enclosure, observing one generator exactly
  removes it, and the probe is the generator whose removal leaves the least sup-norm diameter. Over
  an enumerated fibre, a declared observation partitions the fibre into its level sets; its survivor
  is the largest width the target reading keeps inside one level set, never more than the whole
  width (`width_mono`), and the probe is the observation with the least survivor. The live probe
  criterion is information, not a survivor width: the chaser's probe (`receiver::population::chaser`,
  U3's second loop) partitions its fibre the same way and is offered as
  `receiver::release::ProbePartition`, the partition's information
  `I = log₂|Θ| − (1/|Θ|) Σ_c |c| log₂|c|` compared exactly as `∏_c |c|^|c|`
  (`Population.partitionInformation_lt_iff`).
- [definition] **The coarsening tower search** (`releaseCoarser`). Up a declared tower of readings,
  finest first, each step's factoring through the step below is checked over the fibre: two
  members the finer reading identifies must be identified by the coarser one
  (`coarser_receiver_factors`; the core factor descent of `holon::restriction`). The coarser
  invariant to release is the first step whose width is inside tolerance, carried with the
  tolerance it was searched under, so it cannot be offered against a narrower one. A coarser reading
  `g ∘ R` is narrower only when `g` is non-expansive (`width_nonExpansive_factor`;
  `expansive_factor_increases_width` is the counterexample).
- [proved-standard] **A mixture face's variation.** A family-to-class map `A_fc = P_f(c)` with
  nonnegative columns that each sum to one is L1-nonexpansive (`‖A‖₁ = 1`), so the mixture faces of
  any two normalized posteriors inside interval bounds differ by at most `Σ_f (upper_f − lower_f)`
  in L1. The release reads the class enclosure itself, and a class enclosure that covers the whole
  simplex never certifies a draw: every key is held. F5's numerical health (radius, robust count,
  operator bound, contraction) is still a missing term.

<a id="the-retired-byte-tree-text-line"></a>

## The retired byte-tree text line

[definition] THE_REBUILD U6's order (item C.5) retired the byte-tree text line from
`receiver::population` and `compression::landmark::context` on September 30 (history at
[`f5fd8f3b`](https://github.com/brandonrdug/holonics/tree/f5fd8f3b); the
[antipattern record](../research/records/2026-09-29_ANTIPATTERN_CATERED_MACHINERY_A_TASKS_SOLUTION_ROUTINE_NEVER_STANDS_IN_FOR_LEARNING.md),
instance 3). Its catered layers carry no law forward: the depth-limited context window read as a
family (`TreeFamily`, with its address per aeon and its curated typed address `Sections`), the part
clock's sentence counter (`boundary`), and the copy stage with its located span (`admitted`,
`context::spans`: the longest recurring suffix). The laws the line stated, and where each is kept:
- [proved-derived; formal-checked] **The staged face** (the boundary egg and the admitted
  receivers): `q_t(c) = h_t(σ c) · r_t(c)` is a face, and its code is the stage's code plus the
  conditioned code (Lean `Compression/Landmark/Context/Composition.{stagedFace_nonneg,
  stagedFace_sum_one, staged_chain_rule, staged_code}`). The hazard's and the copy stage's faces are
  KT faces over a declared partition (`Tree.{ktFace, ktFace_pos, ktFace_sum}`).
- [proved-derived; formal-checked] **The hazard's learned partition** was the merge law read on the
  hazard's cells: a priced merge adopted only where the complete code falls (Lean
  `Merge.{merge_cost_mass_iff, restaurant_merge_ratio}`; `receiver::population::merge::Blocks`,
  which stays).
- [definition] **The release of a population.** The release view copies the scored face,
  `P_release(c | request, Θ) = P_scored(c | request, Θ)` for every class, the stopping class
  included. The family draw reads the mixture as the marginal of a once-chosen family and its
  whole future path, `Σ_f w_f P_f(y) = P_population(y)` (Lean `Population.population_mixture`): a
  family drawn once from the posterior enclosure by the certified draw (`receiver::release::draw`,
  which stays) is `Unresolved` where the enclosure leaves it plural, so the released submeasure
  proves no equality of full distributions. A response is one certified draw a cell under either
  law; it stops at the first drawn section letter, which is emitted, and a byte drawn when the
  aperture keeps no room for the stop is not emitted (`NoContinuationBridges`). The exterior text
  chart's square is `D(UTF8(s)) = s` and `UTF8(s ◦ c) = UTF8(s) ◦ UTF8(c)`.
- [definition] **A face's family provenance**: `q(c) = Σ_f w_f P_f(c)`, each family's share
  enclosed by the outward bounds of `w_f P_f(c)` (a dead family's is zero). The mixture attributes
  mass to families only: the producing key and the causal source stay missing terms.
- [definition] **A partition's reading**: the passage's cells declared into parts, each part's
  population code `Σ_(t∈P_j) (−log₂ W_(t+1) + log₂ W_t)` and each family's
  `−log₂ ∏_(t∈P_j) P_f(x_t | past)`, the parts summing to the passage's codes (the telescope of
  `Population.population_mixture`). A receipt, never a record.
- [definition] **A future branch and a native checkpoint** are consequences of the retention law
  ([objects §8](ELEMENTARY_OBJECTS.md#8-deposition); Lean `Foundation/Standing`), not new laws: a
  branch continues each family's contemporary constitution, `face(branch H) = face(H)`, and never
  reconstructs by replay; an exact codec satisfies `D(E(Θ)) = Θ`, `face(D(E(Θ))) = face(Θ)` and
  `E(receive(D(E(Θ)), x)) = E(receive(Θ, x))`.
- [definition] **The planned incidence and the present retention** (a request's relation planned
  before its target part, a port's run held in its aeon) were the admitted receivers' plumbing and
  leave with them. Dataset roles stay exterior codec information (the notebook's `exterior.rs`).

The atlas keeps each expression with its history owner (`receiver.population-*`,
`context.span-located`, `receiver.native-standing-checkpoint`, `receiver.text-boundary-square`).

## A displayed body is a cut; its plates can be continuing bodies

[definition] A rendered frame is a present spatial/receiving cut of a world-tube and its
field sections. The chosen window can be bounded without establishing a physically closed
body or a definite value for every unobserved interior. An exposure may integrate a finite
interval rather than one instantaneous slice. The complete source retains its evolution,
incoming boundary conditions and relevant unobserved modes.

[definition] Brandon's subsequent plate-chain clarification makes the interface itself
active: a membrane/plate Σ(t) can carry surface charge, tangential current, material state,
deformation and its own internal modes. It participates as a Holon, receives from the
adjacent fields and conducts/emits into others. A smooth manifold is a local plate chart;
junctions, branching and singular contacts can require the existing stratified/cellular
description. Geometry supplies the incidence and metric; capacitance additionally requires
its constitutive storage–potential relation. A drawn surface alone does not specify C.

[proved-derived] For a moving volume with boundary velocity w, a conserved bulk density ρ
and laboratory current j obey the relative-flux balance

```text
d/dt ∫_(Ω(t)) ρ = −∫_(∂Ω(t)) (j−ρw)·n + ∫_(Ω(t)) source.
```

For a smooth membrane separating minus/plus bulk fields, normal n points from minus to plus.
Here ρ_± and j_± are charge densities and charge currents. With surface charge σ,
tangential conduction j_Σ and material derivative D_t^Σ,

```text
D_t^Σ σ + σ div_Σ w + div_Σ j_Σ
 = [(j_-−ρ_-w)−(j_+−ρ_+w)]·n.
```

These continuum identities use the actual moving surface/volume transport theorem. Surface
sources add their declared term. Under `σ=C_m V`, V the potential jump, the left side includes
`C_m D_t^Σ V + V D_t^Σ C_m + C_m V div_Σ w`. Its geometry/material and area terms are part of
the receiver's response. They cannot be removed by holding the rendered plate stationary.

[definition] For several coupled plates, capacitance is generally an operator from relative
potentials to stored charges, not one coefficient per drawn surface. In an isolated
electrostatic chart its common-potential direction is a gauge; grounded/reference charts
restrict that direction explicitly. The shared difference and normalization patterns are
reusable in attention, but the actual constitutive law decides the participation/current.

[proved-derived] In a lumped two-sided membrane restriction, `q=C V` and
`I=C V_dot+C_dot V+g V`. Its power identity is
`V I=d(CV²/2)/dt+gV²+C_dot V²/2`. The last term is exchange with changing geometry/material.
The existing port-energy and conducting-channel laws supply its inductive/current extension;
`HolonicMembraneActionTransport` and `ConstitutiveWorldTube` supply addressed membrane and
constitutive scope. The [exact symbolic join](https://github.com/brandonrdug/holonics/blob/13f8c734/research/experiments/mfr_entropy_heat_current/moving_plate_and_burgers.json)
checks the lumped identity and a separating omission of `C_dot V`. It is not a calibrated
biological membrane or a proof of the full continuum surface law by finite algebra.

[definition] A context stack is usefully read as live nested causal couplings and continuations:
active ports, storage, current, phase, constraints and pending interactions. A call stack is
one restricted ordering; biological and field interactions can be cyclic, branched and
asynchronous. Their causal memory can reside in material, modes and an evolution kernel.
It does not prescribe a literal stack trace or archive of every past source. Eliminating an
interior produces the existing memory term `B U(t,s) C` and its initial-state contribution.
The retained state must realize those future boundary effects.

[proved-standard] The classical Hodgkin–Huxley membrane is a concrete biological
restriction: capacitive storage is coupled to ionic conductances whose states respond to
voltage and time. It illustrates an active receiving boundary rather than a passive viewing
plane. Its particular constitutive equations are not a universal HNN law.
[Original membrane-current construction](https://physoc.onlinelibrary.wiley.com/doi/10.1113/jphysiol.1952.sp004764).

## Perspective is a physical relation before it becomes screen coordinates

[definition] In a relativistic realization, the receiver has a world-tube χ_R and a
future-directed unit velocity U_R, `g(U_R,U_R)=−1`. Local spatial axes and a receiving face
normal belong to its tetrad. A photon has future null momentum k; its received energy is
`E_R=−g(k,U_R)`. With symmetric stress T, the receiver current and oriented flux are

```text
j_R^μ = −T^{μν} U_R,ν,
F_R = j_R^μ n_R,μ,
∇_μj_R^μ = −(∇_μT^{μν})U_R,ν − T^{μν}∇_μU_R,ν.
```

[proved-derived; formal-checked] The existing
[ObserverBoundaryCurrent](../lean/Holonics/Physics/ObserverBoundaryCurrent.lean)
derives that divergence from its source jet and contracts the symmetric observer deformation
with T. Einstein/Bianchi supplies conserved stress under its field assumptions. The receiver
therefore participates through its trajectory, orientation and constitutive boundary, rather
than receiving an unexplained scalar energy or a canvas-normal arrow.

[definition] A local normal is meaningful relative to its metric and receiving surface.
Flux may also have tangent components. Vorticity, material twist, winding and connection
holonomy preclude assuming one globally perpendicular I/O direction. A rest-space foliation `U♭=a dt` requires `U♭∧dU♭=0`: expand
`a dt∧d(a dt)` and use `dt∧dt=0`. Such a foliation is an additional geometric condition,
not a property of every observer. Material/Frenet torsion is distinct from affine
connection torsion. Ordinary torsion-free GR still has curvature, vorticity and holonomy.

[definition] Geometric-optical rays follow the characteristic Hamiltonian of the declared
medium. In vacuum, `H(x,k)=g^{μν}(x)k_μk_ν/2=0`, with
`ẋ=∂_kH` and `k̇=−∂_xH`. A material dispersion relation replaces H when appropriate.
Ray/group direction and phase normal need not coincide in an anisotropic medium. Local
refraction, polarization and attenuation require that medium's constitutive map; drawing
an arc alone supplies none. Existing `HolonicSnellInteraction`, polarized transport and
receiver ray/conic/torus owners retain those source-qualified constructions.

[proved-derived] Coordinated recharting transports k, U, T, normals and dual receivers
together and preserves their contractions. Moving or rotating the physical receiver while
holding the source fixed generally changes its face. A rotated plotting camera is a third
operation, downstream of both. The September 12 directional-optics construction already
separates common state/analyzer transport from moving the analyzer relative to the state.
The moving-aperture control illustrates this distinction at a fixed source. It does not
represent the changing source field and was incorrectly presented as completing that synthesis.

## Induction includes the moving receiving surface

[definition] Fix orientation by writing the magnetic two-form as `β=ι_B vol` and electric
one-form as e=E♭. For the material flow χ_t with velocity v, pullback differentiation gives
`d(χ_t*β_t)/dt=χ_t*(∂_tβ+L_vβ)`. With `dβ=0`, `∂_tβ=−de` and Cartan's formula,

```text
d/dt ∫_(S_t) β = ∮_(∂S_t) (−e+ι_vβ),
EMF = ∮_(∂S_t) (e−ι_vβ) = −d/dt ∫_(S_t) β.
```

[proved-derived] Here `(ι_vβ)(w)=B·(v×w)=(B×v)·w`, so
`e−ι_vβ=(E+v×B)♭`. This sign depends on the stated contraction convention.
It retains the motional EMF even when the magnetic field has no explicit time change.
For a rectangle of width w and length L(t) in constant B_z, the moving right edge contributes
`−B_z w L̇`; its flux derivative is `B_z w L̇`. Rigid translation of a closed loop in the
same uniform field instead has cancelling edge contributions. Motion alone is not an
additional universal dissipation law. This is the conventional transported-flux construction;
see [Feynman, laws of induction](https://www.feynmanlectures.caltech.edu/II_17.html).

[proved-derived] The finite analogue keeps both changing field and changing face:

```text
r₁(B₁)−r₀(B₀) = r₀(ΔB)+Δr(B₀)+Δr(ΔB).
```

The last term is a genuine finite mixed difference. The existing
[discrete induction](../lean/Holonics/Physics/HolonicDiscreteInduction.lean)
retains oriented face circulation and the full EMF fibre on its fixed carrier. Moving-face
transport must supply the additional map; a new scalar flux label would not implement it.
The exact bilinear difference/pullback library now exposes the corresponding elementary
operations. The moving-continuum EM surface consumer remains a specific implementation join.

## Fractal dynamics are received through a changing family of cuts

[definition] Let Φ_(k,0) transport the complete source/receiver state and let A_k denote
the receiving event region at the kth admitted clock cut. Its first-arrival population is

```text
F_n = Φ_(n,0)⁻¹(A_n) \ union_(k<n) Φ_(k,0)⁻¹(A_k).
```

The nonlinear operation can stretch/fold these preimages into fractal boundaries. A receiver
changes which set is cut, and its state can also alter the operation through interaction.
A sampled basin image depicts evaluations of this construction; it does not replace its
full populations, parametric modes or unresolved interiors.

[proved-derived; formal-checked] The new `ClockedFirstArrival` join in
[HolonicRecurrentEcology](../lean/Holonics/Computation/HolonicRecurrentEcology.lean)
uses the original autonomous first-arrival owner on `(x,k)↦(T_kx,k+1)`.
It proves the actual iterate `(evolution T k n x,k+n)` and then the first-hit/exclusion
identity for moving sets A_(k+n). An endogenous receiver belongs in x with its source
coupling. This does not require moving a physical receiver to preserve its old faces.

[definition] For a receiving partition P_(R,k), the observed history partition is
`join_(k<n) Φ_(k,0)⁻¹P_(R,k)`. Probabilities require a declared measure μ; its cell masses
are μ(B). The Shannon entropy of this partition, its refinement rate, a basin-boundary
dimension, phase-space dimension and heat production are distinct receivers of the same
underlying construction. A scale law or limiting dimension needs its actual family and
limit, not the number of plotted tiles. The [fluid synthesis](HOLONIC_FLUID_CONSTRUCTION.md)
retains harmonic modes and the source-specific spectral scaling relation.

## Probability is a receiver geometry

[definition] Probability is a receiver's normalized face of a declared measure on a certified
partition, `p_i = μ(A_i ∩ F)/μ(F)`. It is never ontic chance, a governor or a sampler. The
laboratory settled this ontology: "probability appears only where a declared observer compresses an
unavailable interior". The faces carry this geometry
([record](../research/records/2026-09-27_PROBABILITY_IS_A_RECEIVER_GEOMETRY_BAYES_IS_THE_RATIOS_TRANSLATION_AND_THE_EGGS_PERIOD_IS_HYPERGEOMETRIC.md); the identities are graded there, and their Lean is owned or owed
in #62):
- [proved-derived; formal-checked: `HolonicAdjointNormalization.{bayes_logOdds_twoSwings, bayes_eq_face,
  bayes_eq_discrete_replicator}`] **Bayes is the quotient rule under refinement.** In the ratio's additive chart it is a translation:
  `log(p′_i/p′_j) = log(p_i/p_j) + log(L_i/L_j)`, which is two half-turns `S_b S_0` with
  `b = ½ log(L_i/L_j)`, a chart identity (the Lean name `bayes_logOdds_twoSwings` keeps the
  half-turn's older name). It is the softmax of `log p + log L`. The softmax ratio
  family `r_ij` keeps every pair's ratio and forgets only the common origin, the evidence, which is a
  gauge (`Computation/HolonicAdjointNormalization.face_add_common`), and the discrete replicator
  over candidates. [agent-inferred] The same normalization is the attend row of the Holonic
  Interactions.
- [established-classical] **The amplitude sphere.** `p ↦ √p` puts the faces on the positive orthant of a sphere. The Fisher
  metric is four times its pullback, and Fisher–Rao distance is `2 arccos Σ√(p_i q_i)`. The complex
  Born chart adds the phase that the loss's winding keeps.
- [proved-derived] **The Laplacian return is the Fisher information** of the categorical family in its natural chart:
  `β(diag(p) − ppᵀ)`, with `vᵀJv = (β/2)Σ p_i p_j (v_i − v_j)²`
  (`HolonicAdjointNormalization.quadratic_laplacianReturn`).
- [established-classical; the join agent-inferred and conditional] **Chentsov.** On finite sample spaces the Fisher metric is, up to scale, the one metric invariant
  under congruent Markov embeddings, the sufficient maps. A general Markov map contracts it. A
  sufficient statistic is a retention only when every admitted future face factors through it and
  the admitted transports descend (`Foundation/Standing.standingLaw_exists_iff_future_factors`).
- [established-classical; the egg reading an interpretation] **The hyperbolic face.** A
  location–scale family's Fisher geometry is a constant multiple of the hyperbolic half-plane (for
  the Gaussian, a Fisher radius `R` is the hyperbolic radius `r = R/√2`). An equal-distance circle
  about `(x₀, y₀)` of hyperbolic radius `r` is the Euclidean circle of centre `(x₀, y₀ cosh r)` and
  radius `y₀ sinh r`, lopsided toward larger `y`. It is lopsided toward diffusion only when the
  receiver declares `y` a diffusion width; its likeness to an egg is an interpretation.
- [established-classical; the joins graded in the record] **Hypergeometry.**
  - The Gauss equation's Schwarz map with exponent differences `(0, 1/2, 1/3)` has monodromy
    `(2,3,∞) = PSL(2,ℤ)`, the half-turn with the third-turn.
  - The Hügelschäffer curve's period is `K(√λ) = (π/2)₂F₁(½,½;1;λ)` (owed in #62). Its modular
    `j(λ)` meets the half-turn point `j = 1728` once on the real curves
    (`HolonicsResearch/Geometry/EggModular.egg_j_of_legendre_lambda`, formal-checked).
  - The node law's beta-binomial generating function is the terminating `₂F₁(−n, α; α+β; 1 − t)`.
- [established-classical; `kt_eq_dirichlet_half` formal-checked] **Counting faces.** A type class is a count face of a passage, with
  `(n+1)^(−m) 2^(nH) ≤ |T(P)| ≤ 2^(nH)`. The receiving tree's KT node law is the Dirichlet-½
  (Pólya-urn) predictive. A finite exchangeable law is a mixture of the uniform laws on its count
  classes (Diaconis–Freedman).
- [proved-derived; formal-checked: `Physics/Wave/Interference.{intensity_eq,
  resolved_intensity_eq}`] **Coherent reception.** Classes interfere exactly when their amplitudes reach one receiving mode
  with a retained relative phase: `|Σa_j|² = Σ|a_j|² + 2Σ_(j<k) Re(a_j ā_k)`. Resolved modes or
  distinguishing tags give the incoherent sum. An aperture transmitting `L_i` gives Bayes's
  conditional face, and its rejected flux belongs in the receipt.

## The calculus of entropy also contains receiver motion

[proved-derived] In a smooth flat chart, suppose a density obeys `∂_tρ+div J=s`, and a
receiving cell A_i(t) moves with boundary velocity v_i. For received mass
`m_i=∫_(A_i)ρ`, Reynolds transport gives

```text
ṁ_i = −∫_(∂A_i) (J−ρv_i)·n + ∫_(A_i) s.
```

This follows by adding the boundary-motion term to the density derivative and applying
the divergence theorem. The flux relative to the receiving boundary, rather than J alone,
determines the change in that cell's reading. On moving/curved geometry use the transported
density form, retaining the volume and connection contributions.

[proved-derived] An aperture may receive only part of the source. Its conditional
probabilities have `Z=Σm_i>0` and `p_i=m_i/Z`, so the quotient rule adds
`ṗ_i=(ṁ_i−p_i Ż)/Z`. The moving normalization cannot be omitted when the admitted
current changes. For a complete probability partition, Z=1 is the corresponding
specialization. The optical example normalizes the exact admitted current at every cut.

[proved-derived] On a fixed positive-support stratum with normalized p,

```text
H_R = −Σ_i p_i log p_i,       Ḣ_R = −Σ_i ṗ_i log p_i,
C(p,q) = −Σ_i p_i log q_i,
Ċ = −Σ_i ṗ_i log q_i − Σ_i p_i q̇_i/q_i.
```

The derivatives follow from the chain rule and `Σṗ_i=0`. Moving support boundaries use
their one-sided/measure transport rather than differentiating through an undefined log.
Both the measured distribution and its reference may change. The logarithms are their
normalized mode/ratio functions, not stored floating identities. Entropy changes induced
by a moving aperture do not establish physical entropy production. The existing
`TwoCellEntropyTransport` and current-balance owners derive production under their explicit
constitutive flux laws.

## Compression, storage and reconstruction are receiver-relative conduct

[definition] Let z contain the source, the relevant receiver state and any required shared
conditions. An encoding C admits decoder d_j and descended navigator U_i when
`ρ_j=d_j C` and `C T_i=U_i C` for the admitted receiver and navigator family. The retained
fibre describes differences behind the encoded face; it need not enumerate raw states.
The existing `CausalRelevance`, `NavigatorModeQuotient`, boundary-scale and receiver-history
owners provide these relations at their stated domains.

[proved-derived] Equality at one current receiver is insufficient if an admitted later
receiver or interaction separates the states. Conversely, a change in representational
coordinates with all compensating maps transported need not require more stored information.
This follows directly by composing the decoder and navigator equations through a word.
Tolerance-based compression carries its actual propagated difference and receiver family.
It does not add a universal certainty condition before emitting a joint or unresolved face.

[definition] A drive write is a material interaction that changes the receiving device;
a subsequent read applies its codec and physical response. A saved file is a serialized
chart of the resulting state. A display similarly receives encoded material, generates an
optical field and participates in later reception. Their full physical laws differ, but
the common abstraction is the receiving Holon plus its interaction, frame, admissible
readouts and reconstruction. Neither a filename nor one measured voltage is that entire
object. Navigator/constraint representations can retain the required consequences without
an event archive or perfect reconstruction of every earlier microscopic state.

## The moving receiver's owners and the retired optical control

[established-bounded; source-inspected] **Current owners.** The moving receiver's rate is
`receiver::reception::FaceMotion` (Lean `Holarchy/Reception.moving_receiver_rate_of_law`): over a
solved joint step the face's change splits exactly into the source's motion, the receiver's own
motion and the chart's explicit motion, `Δy = C_S Δx_S + C_R Δx_R + h c`. Boosts on aeon clocks, the
Lorentz map and the observer current are `physics::spacetime` (`LightCone`, `DopplerBoost`,
`LorentzMap`; Lean `Physics/Spacetime`). No current owner projects a receiver point through a
moving chart or assembles the optical diagram below; the moving electromagnetic surface, the
receiver's material response and their encoding consumers remain owed.

[established-bounded; implemented-exact; history] **The retired optical control.** The retired [`geometry::projection`](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/geometry/projection.rs) exposed
`project_receiver_point_rate` for its four projections and `project_point_with_motion` through the
declared source→receiver route. The latter computes `p_R=Lp+b`, `ṗ_R=Lṗ+L̇p+ḃ`, then the actual
projection derivative. The chart rates are supplied kinematic operands; two frame snapshots alone
do not determine them. The receiver object there is a spatial chart; the full participating
material and current belong to its containing construction.

[established-bounded; implemented-exact] The retired
[`optical_receiver_frames`](https://github.com/brandonrdug/holonics/blob/814157ad/crates/holonic-engine/examples/optical_receiver_frames.rs)
example consumed that interface and [`EnergyMomentum::{photon,boost_x}`](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/exact_linear/energy_momentum.rs)
to form the diagram's 65 exact proper-time cuts. Its receiver world-tube is

```text
χ_R(τ,u,v)=(γτ+γβu, γβτ+γu, v, 8),
β=3/5, γ=5/4, u²+v²≤4.
```

Its tangent time/spatial vectors have the correct Lorentz pairings. Three stationary null
ray currents intersect this moving aperture. Received packet energies are `4/5`, `20/13`
and `17/10` in E₀. The local spot rate is `du/dτ=−3/5`; accepted ray indices change from
{2,3} to {1,2,3} to {1}. The exact source driver retains momentum, frame, orientation,
intersections and conditional current weights. A fixed external viewing camera displays
these returns; it does not supply their I/O direction.

[definition] The ray example is a local Minkowski specialization with supplied inertial
motion and null-stress channels. The optical face and moving-aperture entropy are calculated.
It does not claim a curved ray solution, calibrated photodetector response or a field
assembly.

## Continuing-field correction

[definition] The [analytic flux construction](ANALYTIC_FLUX_AND_RECEIVING_BASINS.md) makes
the subsequent source/receiver synthesis explicit: `F_s v=-F-u_dot F_u` joins source change
to residual release, and `T^R_n=e_(n+1) T_n e_n^-1` carries the relative evolving field through
changing receiver charts. Its first-arrival populations use the actual partial navigator and
moving receiving regions. Potential/phase one-forms, inverse-branch Jacobians and contour
periods supply analytic measurements; moving a view or measuring entropy alone supplies none
of those dynamics. The source guide separates coordinate reexpression from physical coupling.

[project-postulate] The fixed-ray example above is a local optical control. Brandon rejected
its use as the HNN field illustration because the field itself must continue relative to R.
The [replacement construction](https://github.com/brandonrdug/holonics/blob/13f8c734/research/experiments/hnn_field_architecture/CONTINUING_FIELD.md)
evolves the complex currents, thermal modes and their common nonuniform material transport,
then reconstructs the full receiver volume. The geometric carriers and field are generated
from that same state. This corrects the omitted source-evolution contribution without claiming
that one supplied constitutive example completes the general HNN/physics synthesis.

## Landmarks constrain one continuing interior

[project-postulate] Brandon's September 15 horizon example poses an engineering construction:
use before, intermediate and contemporary observations to infer the dynamics of an incompletely
observed interior. Phase transitions are informative landmarks. The same question appears in
perception, recollection, inverse physical problems and HNN formation. It belongs to the shared
receiver/field objects, without prescribing a stored trace of every intermediate state.

[definition] Let Ω be an admitted family of possible evolutions, retaining the constitutive
laws, participating receivers, clocks, conservation constraints and phase-transition maps.
At landmark i, `p_i:Ω→X_i` reads its situated state and `ρ_i:X_i→Y_i` its observing face.
For available observation regions `O_i⊆Y_i`, the compatible family and a requested future face are

```text
F_I = ⋂_(i∈I) (ρ_i ∘ p_i)^(-1)(O_i)  ⊆ Ω,
Y_* = (ρ_* ∘ p_*)(F_I).
```

[definition] This is a joint pullback on one family. Correlations between landmarks travel
through Ω; independently matching three marginal observations does not construct their common
evolution. A deterministic realization can instead use transported states `p_i=Φ_i`, including
its parameters and receiver state in the common source. Relations and changing state spaces
remain available when a phase change is not expressed by one fixed global coordinate map.
The triad is a useful selected set of cuts, not a required three-step engine or global clock.

[proved-derived; source-inspected] Adding an intermediate constraint gives
`F_{0,1,2}⊆F_{0,2}`, hence `Y_*^{0,1,2}⊆Y_*^{0,2}`. This is the existing
[`ReceiverPotential.additional_observation_refines`](../lean/Holonics/Transport/ReceiverPotential.lean)
construction on a product receiver; `image_receiver_restriction` covers source/target regions.
`outcomes_singleton_of_factor` supplies the useful stronger case: a future face can be uniquely
determined by the observations while the compatible source interior remains plural. The
existing shrinking-receiver theorem gives the corresponding convergence under its bounds.

[definition] “Inevitable” refers to a consequence forced throughout the applicable family.
Useful generation can also return a compatible face or a bounded family under its requested
conditions. Neither form requires claiming that all hidden microscopic history is recoverable.
An observation used at the contemporary cut need not have been available to a historical
prediction; the occurrence/receiver chronology retains that distinction.

[proved-derived; source-inspected] The existing
[`ReflectedBoundaryMemory.boundary_reduction_iff`](../lean/Holonics/Physics/ReflectedBoundaryMemory.lean)
makes interior omission precise in a linear chart. For arbitrary boundary x and interior z,

```text
E_next(Ax+Bz)=U(Ex)  for all x,z
    iff  E_next A=U E  and  E_next B=0.
```

[definition] If the interior coupling contributes to an admitted future face, retain its modes,
joint constraints, memory law or bounded residual in the representation. A richer encoding can
carry that contribution economically. This specialization joins the general dynamic quotient
`q_next T=U q`; it does not impose boundary-only state on a nonlinear coupled field.
`ClockedSpan.comp`, `WorldTube` and `JointReceiverHistory.quotient` supply existing source,
clock, obstruction, interior/radiation and receiver-family owners for the same composition.

[definition] Conservation across these faces retains their orientations and actual material/
exchange laws. Shared boundary contributions join through the declared incidence and transport;
changing coarse charts carry their boundary-square defect when nonzero.
[`ExteriorBoundary.pullback_coboundary_defect`](../lean/Holonics/Geometry/ExteriorBoundary.lean)
and the [active stress-face law](CONSTRAINT_MODES_AND_RECEIVER_FACES.md#the-overlap-has-stress-bearing-faces)
make those obligations explicit. An active plate stores and changes current, material and frame;
its receiving face is one projection of that continuing physical/mathematical construction.
