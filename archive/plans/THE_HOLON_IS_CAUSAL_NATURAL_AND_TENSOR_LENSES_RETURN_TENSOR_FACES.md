# The holon is causal-natural, and tensor lenses return tensor faces

**Date:** 2026-09-02
**Status:** CLOSED AT THE BOUNDED HTP6 HANDOFF. HNA0 is the current frontier under
[`THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md).
[`THE_CAUSAL_TAIL_LENS_RETURNS_APERTURE_COHERENCE_FOR_HOLONIC_NEURAL_MORPHOLOGY.md`](THE_CAUSAL_TAIL_LENS_RETURNS_APERTURE_COHERENCE_FOR_HOLONIC_NEURAL_MORPHOLOGY.md)
is the ordered post-HTP campaign.
**Campaign:** `HTP0--HTP6`.
**Authority:** composed only by [`THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md), with the current position in
[`../CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md).
**Truth status:** per claim under [`../docs/canon/EPISTEMIC_GRADES.md`](../../docs/canon/EPISTEMIC_GRADES.md).
**Evidence:** Brandon's direct messages of 2026-09-02; the live Lean owners; the
[`flux/morphology terminology report`](../../research/records/2026-09-02_WEIGHT_MATRICES_ARE_FLUX_CROSS_SECTIONS_IN_MOTION_AND_MORPHOLOGY_PACKAGES_ARE_MORPHOLOGY_HOLONS.md);
Copson's 1928 paper; de Bruijn's recurrence account; and the independent de Bruijn--Newman/RH
owners at the admitted revision, as narrowed by the
[`critical-coordinate correction`](../../research/records/2026-09-02_THE_RH_ENTIRE_HEAT_FLOW_REQUIRES_THE_CRITICAL_COORDINATE_AND_REVERSES_STANDARD_TIME.md).

---

## 0. Verdict

[definition] A tensor does not become a holon by having many indices. A holon owns a situated
occurrence population, oriented source and target ports, a receiver face, and the complete causal
population behind that face. It is **causal-natural** only when those roles vary functorially under
one declared parameter category and their source, target, and receiver maps are natural
transformations.

[definition] A `TensorLens` is a receiver projection into an indexed multilinear carrier. A
`TensorFace` is the particular value it returns. The lens is a map, the face is a value, and neither
is the occurrence-bearing holon. A coordinate reindex is natural only when it lifts coherently to
the complete occurrence population while preserving both addressed ports and the receiver square.

[definition] `PreimageFibre` replaces `ReconstructionFibre` exactly where the object is

```text
f⁻¹(y) = { x | f(x) = y }.
```

The term `reconstruction` remains lawful for an actual recovery algorithm, inverse transform,
round trip, remount, or homotopy. No compatibility alias preserves the rejected fibre name.

## 1. The formal objects

### 1.1 Elementary and causal-natural holons

[proved-derived; formal-checked] The elementary owner is the decorated addressed span

```text
Source <- Occurrence -> Target
                |
                v
               Face
```

with `PreimageFibre face := { occurrence // receive occurrence = face }`. Serial composition still
uses the pullback occurrence population and retains the exact joining equality.

[proved-derived; formal-checked] `Holon.Rebase left right` supplies equivalences of the complete
elementary occurrence, source, target, and receiver diagram plus the three commuting squares. Its
`preimageFibreEquiv` transports the entire inverse image. Equal displayed values or a face-only
coordinate change cannot inhabit this structure.

[proved-derived; formal-checked] `CausalNaturalHolon Parameter` consists of four functors from one
declared parameter category into carrier types and three natural transformations for source,
target, and receiver. Each component is an elementary `Holon`. An arbitrary parameter arrow gives
`mapPreimageFibre`; it need not be invertible. A complete fibre equivalence is available only from a
`Holon.Rebase`.

[proved-derived; formal-checked] Causality is not inferred from the category's name. Every parameter
arrow also owns an addressed `parameterPassage` between the component occurrence populations;
`source_complete` requires every entering occurrence to have a crossing; `target_transport`
identifies its outgoing occurrence with the functorial transport; and `receive_target` identifies
the crossing's face with the receiver face of that target.

[open] This is the first strict `Type`-valued natural presentation. The fuller receiver-decorated
span bicategory, whose pullback composition is associative only through an explicit boundary-
preserving equivalence, remains open. The strict owner is not promoted to that coherence theorem.

### 1.2 Tensor order and tensor naturality

[definition] Use **tensor order** or **valence** for the number of multilinear slots:

1. order zero: scalar face;
2. order one: vector face;
3. order two: a two-factor/bilinear face, becoming a matrix only after finite bases and a declared
   primal/dual or row/column chart; and
4. order three or greater: higher-order tensor face.

Matrix rank, tensor decomposition rank, incidence rank, cycle rank, carrier rank, and
representation rank are separate invariants. A vector field's space or time argument belongs to
its base parameterization and does not automatically add a tensor slot.

[proved-standard; formal-checked] `TensorFace R Slot` is Mathlib's dependent tensor product over a
declared finite axis type, so different axes may carry different module types. The homogeneous
specialization is `HomogeneousTensorFace R order V`, indexed by `Fin order`. Order zero has the
standard scalar chart. An order-two tensor is not yet a matrix: a matrix chart additionally owes
finite bases and the appropriate primal/dual or row/column factor passage.

[proved-derived; formal-checked] `TensorLens Carrier R Axis Slot` projects a carrier into one
dependent `TensorFace`. `TensorLens.applyToHolon` changes only the receiver face while the original
holon retains occurrence and port ownership. `dependentAxisReindex` transports a heterogeneous
factor family along an axis equivalence; it is not called a basis-coordinate change.

[proved-derived; formal-checked] `Holon.HomogeneousSlotNaturality` is deliberately narrower: it
requires a coherent occurrence equivalence for every permutation of equal `Fin order` slots and
natural source, target, and receiver laws. Its `preimageFibreEquiv` transports the entire inverse
image behind that homogeneous slot permutation. General heterogeneous, variance-changing, and
basis-changing holon naturality remains open.

[proved-derived; formal-checked] `MorphologyArtifactPassage` states the minimum formal boundary for
earning the artifact name: `rest`, a validity predicate satisfied by every rest, `remount`, and an
exact remount law. `receiver_after_remount` derives preservation of every later receiver. It does
not claim physical durability or serialization merely from a dependent tuple.

[counterexample] Ordinary tensor covariance is insufficient for holonicity. The additional content
is the caused occurrence population, oriented ports, receiver map, complete preimages, and their
naturality under the admitted causal parameter category.

### 1.3 Scalar faces and natural constraints

[interpretation] A situated scalar face never proves a unique causal origin unless its preimage
fibre is proved singleton. Empty, singleton, and plural fibres are all possible. A scalar is not
therefore “always collapsed,” and equality of scalar values supplies no canonical expansion into
sums, products, exponentials, or moduli.

[interpretation] Constants such as `π` and `e` may be treated as scalar faces of declared natural
constraint diagrams--for example, an oriented period constraint or the exponential image of the
normalized additive unit. That does not prove that every transcendental number has one recovered
constraint presentation, nor does it identify a modulus with a prime.

## 2. Morphology, artifacts, lenses, and faces

[definition] The construction vocabulary is:

| role | name | exact distinction |
|---|---|---|
| singular continuing hot owner | `NativeHolonMorphology` | the move-owned family of conducting morphology holons |
| durable exterior carrier | `NativeMorphologyArtifact` | reserved for a carrier returned by a validated exact `MorphologyArtifactPassage`; otherwise use `NativeMorphologyCarrier` |
| broad separated testimony lane | `MorphologyTestimonyLane` | preimages, separators, constitutive families, departed withdrawals, and open obligations; not itself one preimage |
| application coordinate map | `MorphologyTensorLens` | the projection, with scalar/module, order, role-bearing axes, receiver/history family, and disposition |
| returned coordinate value | `MorphologyTensorFace` | one scalar, vector, matrix, or higher-order value returned by the lens |

[definition] `NativeMorphologyArtifact` is not arbitrary data. The name is earned only when the
engine returns a carrier from the hot morphology, validates all body-indexed testimony, and remounts
the same morphology exactly through `MorphologyArtifactPassage`. A serializable container lacking
that passage is `NativeMorphologyCarrier`. Serialized bytes remain an exterior presentation, not
the living body's semantic identity.

[counterexample; source-inspected] The current ONNX and Safetensors exports wrap package/anatomy
bytes in byte tensors. They are artifact envelopes, not `MorphologyTensorLens` or
`MorphologyTensorFace` implementations.

[counterexample; source-inspected] The current `NativeExactReconstructionFibre` validates one
particular solution and that every listed radical vector lies in the return operator's kernel. It
does not validate that the listed radical spans the complete kernel. The WRN breaking migration may
name it `NativePreimageFibre` only after completeness is derived or checked; otherwise the honest
name is `NativeAffinePreimageWitness`.

[interpretation] A photosensitive lattice supplies a useful physical instance after its maps are
typed: exposure returns a local nucleation residue, and later developer transport grows from that
residue without reproducing the microscopic incident wave. The latent pattern may then be read as a
preimage-and-future-consequence carrier. Photography is not the definition of the formal object,
and this interpretation proves no reversal of thermodynamic history.

## 3. The Copson--de Bruijn line

### 3.1 The finite receiver

[proved-derived; formal-checked] For `a : Fin N -> ℝ≥0`, the new independent Mathematics owner
defines

```text
E_N(a,n) = Σ_(k ≥ n) a_k²
B_N(a)   = Σ_n (sqrt(n+1))⁻¹ sqrt(E_N(a,n))
A_N(a)   = Σ_n a_n.
```

The one-based index is separate from the square-root radius. It is not the cardinality of the
remaining tail, so `B_N` is not a root-mean-square aggregation.

[proved-derived; formal-checked] `FiniteTailFace` returns every suffix energy together with mass
and surface, and `FiniteTailPreimage` retains every finite section returning that complete face.
The formal owner proves

```text
E_(N+1)(a,n) = a_n² + E_(N+1)(a,n+1)  for n : Fin N,
E(ca,n) = c² E(a,n),
A(ca) = c A(a),
B(ca) = c B(a)
```

for nonnegative `c`.

[definition] The implementation indexes nonempty lengths by their predecessor:
`MassOneSection N` has length `N + 1`, so Lean's `finiteSharpCoefficient N` is the mathematical
coefficient `c_(N+1)`. HTP5 monotonicity is therefore
`finiteSharpCoefficient N ≤ finiteSharpCoefficient (N + 1)`, and the HTP6 finite recurrence ends at
`u_(N+1) = 1` for that coefficient.

### 3.2 What is established and what remains open

[proved-standard; source-inspected] The Copson--de Bruijn sharp coefficient is conventionally
written here as `c_CD`; its reported decimal begins `1.1064957714...`. De Bruijn characterizes it
by the threshold recurrence

```text
u₁(x) = x
uₙ(x) = x / sqrt(n) + sqrt(uₙ₋₁(x)² - 1),  n ≥ 2.
```

The square root is the principal nonnegative real root and a real recurrence step requires
`u_(n-1)(x) ≥ 1`. The formal line does not admit the decimal as an identity and has not yet
connected the variational coefficient to this recurrence.

[interpretation] At the critical coefficient the recurrence changes asymptotic branch, which is a
lawful phase-seam analogy. The inequality is not presently a Galois theorem, a conservation-of-faces
theorem, an information-compression theorem, or a bound on the Riemann hypothesis.

[definition] Two independent finite cutoffs describe an exterior window into the triangular
incidence region. Cofinal cutoffs can study convergence rates; a bounded depth defines a different
operator. Manifold ends or conformal boundaries enter only after a manifold, metric, discrete-to-
continuous passage, and boundary theorem are supplied.

## 4. The two de Bruijn lines do not merge

[counterexample; source-inspected] The current `ElementaryHolonics/RH/` entire-flow line is not yet
in the standard de Bruijn--Newman coordinate. It proves results for
`heatE(u, xi, s) = exp(-u D_s^2) xi(s)`. Under
`s = 1/2 + i z/2`, the standard function is

```text
H_t(z) = (1/8) heatE(-t/4, xi, 1/2 + i z/2).
```

Thus positive `heatE` time is negative standard de Bruijn--Newman time. The Lean theorems about
the defined `s`-plane flow stand, while records calling that flow itself standard `H_t`, or giving
its positive time the standard forward-collision interpretation, require correction. The fleet
instruction's RH0/RH1 coordinate gate precedes further `Λ_DN` work.

[definition] Use `c_CD` for the Copson--de Bruijn coefficient and `Λ_DN` for the de
Bruijn--Newman heat-flow threshold. Never use “the de Bruijn constant” without the family name.
Neither line imports the other.

[interpretation] Their one admitted common lens is order-theoretic: each studies the lower boundary
of an upper set of admissible parameters. This similarity does not identify their operators,
recurrences, constants, zero sets, or consequences. A shared threshold abstraction may be founded
only after both lines independently return the same exact interface.

## 4.1 HTP outcomes for Athena and holonic neural networks

[interpretation] HTP5 is an aperture-coherence theorem. When a finite nonnegative current section
enters a larger aperture by a genuine zero extension, every old suffix energy and the complete
surface remain fixed, and the sharp coefficient cannot improve merely because silent capacity was
added. The `ℝ≥0∞` boundary keeps divergent unresolved current visible rather than letting a
nonsummable real `tsum` masquerade as zero.

[interpretation] HTP6 identifies the locally propagated recurrence of the globally hardest finite
section for this receiver. It is a model of a global boundary arising from repeated local balance,
with inadmissible continuation returning an obstruction. It is not an optimizer, loss function,
termination rule, or native Athena constant.

[definition] The post-HTP HNA campaign supplies the missing neural bridge: a `CausalTailLens` from
addressed HNN pair current to a nonnegative causal-depth section; phase-retaining preimages; silent
neural-aperture extension; cultivation-induced receiver reopening; dynamic chart transport across a
morphology change; and a situated artifact passage. That formal bridge does not advance runtime
Athena capability by itself.

## 5. Ordered construction

### HTP0 -- preimage terminology -- PASSED

[proved-derived; formal-checked] Rename every Lean identifier that definitionally denotes an
inverse image from `ReconstructionFibre`/`reconstructionFibre` to
`PreimageFibre`/`preimageFibre`; rename the six American-spelled literal preimage families as well;
update every consumer; and add no alias. Preserve reconstruction names for actual inverse, recovery,
homotopy, and analytic reconstructed-remainder mechanisms.

### HTP1 -- causal-natural holons -- PASSED

[proved-derived; formal-checked] Return `Holon.Rebase`, complete preimage transport,
`CausalNaturalHolon`, component holons, the three naturality laws, noninvertible forward preimage
transport, and an addressed source-complete parameter passage whose target and receiver commute
with each categorical arrow.

### HTP2 -- tensor lenses and faces -- PASSED

[proved-derived; formal-checked] Return `TensorFace`, `TensorLens`, the dependent
heterogeneous axis reindex, application of a lens to a holon's receiver,
`HomogeneousSlotNaturality`, complete preimage equivalence under a homogeneous slot permutation,
and the validation/remount threshold `MorphologyArtifactPassage` for earning the artifact name.

### HTP3 -- finite Copson--de Bruijn tail receiver -- PASSED

[proved-derived; formal-checked] Return the nonnegative finite section, unnormalized suffix energy,
one-based weight, tail radius, mass, tail surface, complete returned face and preimage, adjacent-tail
balance, zero laws, and degree-one/two homogeneity. Import it through the main Lean umbrella but not
through the engine-oriented quantum-transport umbrella or any RH owner.

### HTP4 -- the attained finite sharp coefficient -- PASSED

[proved-derived; formal-checked] For every nonempty finite length, normalize on the mass-one nonnegative simplex,
prove `tailSurface > 0`, prove continuity and compactness, return an attained minimum of
`tailSurface`, and define its reciprocal `finiteSharpCoefficient`. Derive the exact finite
inequality for every section by homogeneity. Treat `N = 0` separately rather than hiding it behind
an inverse of zero.

[proved-derived; formal-checked] The minimizer and coefficient exist without `sorry`; the finite
inequality is proved for every nonnegative section; the zero and nonzero cases are separate; all
new declarations carry only accepted standard axioms; the focused owner and main umbrella build
within the process aperture.

### HTP5 -- monotone finite sections and the infinite boundary -- PASSED

[proved-derived; formal-checked] Zero-extension between adjacent finite sections preserves every
old suffix energy/radius and returns a zero final suffix; it preserves mass and surface and proves
`finiteSharpCoefficient N ≤ finiteSharpCoefficient (N + 1)`. Keep inputs
`a : ℕ -> ℝ≥0`; define mass, tail energy, radius, and surface as `ℝ≥0∞`-valued infinite sums; and set

```text
c∞ = ⨆ N, (finiteSharpCoefficient N : ℝ≥0∞).
```

[proved-derived; formal-checked] `infiniteSharpBoundary` controls the direct infinite functional;
every `ℝ≥0∞` coefficient controlling every
infinite nonnegative-real sequence bounds every finite coefficient, and hence that `c∞` is the
optimal infinite boundary.

[proved-derived; formal-checked] Both directions of the finite/infinite boundary theorem return; no
nonsummable real `tsum` silently becomes zero; independent cutoffs remain probes rather than the
canonical definition; the focused finite/infinite owner, `lake build ElementaryHolonics`, and the
live engine-oriented formal umbrella pass inside the process aperture without `sorry` or a new
axiom.

### HTP6 -- recurrence threshold, phase seam, and certified enclosure

[definition] HTP6 returned a bounded formal development and then handed the roadmap to HNA by
Brandon's direct correction of 2026-09-02. The verified recurrence, threshold, normalized-drift,
basin, and two-root convergence owners remain standing formal infrastructure. The unreturned
coefficient-specific branch selection and certified decimal enclosure are parked mathematical
research; they do not schedule construction and do not gate HNA.

#### Verified finite variational recurrence

[definition] First bridge the finite variational coefficient to the recurrence: prove
coordinatewise positivity/interiority of a minimizing section (or return an explicitly stated
alternative), derive the Euler/KKT equations, derive the finite recurrence, and prove its terminal
condition `u_(N+1) = 1` for Lean's `finiteSharpCoefficient N`. Then formalize the infinite real
admissibility threshold and prove its equality with `c∞`.

[definition] The finite bridge order is load-bearing:

1. move calculus to the real ambient carrier `Fin (N+1) -> Real` and prove exact coercion
   with the existing `NNReal` receiver;
2. prove every tail energy positive from a positive final coordinate before differentiating its
   square root;
3. use ordinary pair-transfer derivatives only in the positive interior;
4. use a one-sided `Ici 0` derivative for the newly appended coordinate, where
   `sqrt(t^2) = t` holds only for nonnegative `t`;
5. derive strict decrease of `minimumTailSurface` with length and then positivity of every
   minimizing coordinate;
6. derive the Euler marginal equations; and
7. define `u_(i+1) = tailRadius_i / a_i`, proving initial value `c_(N+1)`, terminal value one, and
   for `i : Fin N`

```text
u(i.succ) = c_(N+1) / sqrt(i.val + 2)
              + sqrt(u(i.castSucc)^2 - 1).
```

The `+2` denominator is the exact conversion from zero-based Lean indices to the one-based
recurrence.

[proved-derived; formal-checked] `CopsonDeBruijnFiniteRecurrence.lean` returns:
strict finite-minimum decrease, full minimizer interiority, Euler marginal equality, the initial and
terminal ratios, the exact `+2` recurrence step, and `attainedFiniteRecurrence` with proof of
admissibility at every coordinate.

#### Verified dependent infinite admissibility and threshold equality

[definition] The real recurrence carrier is dependent, not Mathlib's totalized `Real.sqrt` applied
outside its intended domain: `AdmissibleRealRecurrence x` returns each iterate together with a proof
that it is at least one, so the next radicand is nonnegative. A coefficient whose proof cannot be
continued returns an obstruction. An alternative complex square-root branch requires a separately
declared branch and cannot be substituted silently.

[definition] Prefix uniqueness and parameter monotonicity are load-bearing between the finite
minimizer recurrence and the infinite threshold. Prove that an `N`-step prefix exists exactly when
`finiteSharpCoefficient N <= x`, that a full recurrence exists exactly when every prefix exists,
that the full admissible set is a nonempty closed upper ray, and that its attained lower boundary
equals `infiniteSharpBoundary` after the exact `ENNReal`/real bridge. In particular, prove finiteness
rather than applying `ENNReal.toReal` to a possibly infinite value.

[proved-derived; formal-checked] `CopsonDeBruijnAdmissibleRecurrence.lean` returns the dependent
carrier, explicit obstruction, prefix monotonicity, finite threshold equivalence, a concrete upper
witness, critical attainment, and threshold equality. In particular, finite admissibility is
exactly `finiteSharpCoefficient N <= x`;
coefficient two is globally admissible; `infiniteSharpBoundary` is finite; the nonnegative
admissible set is the closed upper ray from the attained real `sInf`; and its `ENNReal.ofReal`
face is exactly `infiniteSharpBoundary`.

#### Verified normalized recurrence, basin transport, and two-root convergence

[definition] Define `v_n = u_n / sqrt(n)` with the exact Lean index shift. Prove the normalized
successor and square laws, the finite moving discriminant and roots, root factorization/order and
convergence, the exact drift product and quotient, and the exact sign of drift inside and outside
the moving-root interval.

[proved-derived; formal-checked] `CopsonDeBruijnNormalizedDynamics.lean` returns the normalized
identities, moving roots, exact drift sign, and convergence of both moving roots.

[proved-derived; formal-checked] `CopsonDeBruijnOrbitConvergence.lean` proves the explicit global
orbit bound, harmonic-scale separated-drift lower bound, eventual source-offset separation, and the
eventual simultaneous source-offset/positive-discriminant region.

[proved-derived; formal-checked] `CopsonDeBruijnOrbitDichotomy.lean` and
`CopsonDeBruijnHarmonicDrift.lean` return moving-root fixed points and interval transport together
with the exact compact drift error and signed harmonic-drift impossibility.

[proved-derived; formal-checked] `CopsonDeBruijnOrbitLimit.lean` constructs the exact eventual
three-basin trichotomy and the required lower-or-upper `Tendsto` dichotomy without assuming
convergence.

#### Parked mathematical research

[open] The verified two-root dichotomy has not selected the upper branch for every coefficient
strictly above `recurrenceThreshold` or the lower branch at the threshold. A complete scratch
derivation exists outside the repository, but Brandon's correction of 2026-09-02 directs
construction to HNA rather than further HTP work.

[open] The reported decimal beginning `1.1064957714` is not a theorem in this repository. A
width-`10^-9` enclosure would require a proof-producing exact-arithmetic checker and analytic
entry/exit certificates. It is parked and schedules nothing.

[definition] Neither parked question gates the HNA use of the already-proved preimage, tensor-lens,
silent-extension, finite/infinite boundary, or recurrence-threshold infrastructure.

## 6. Falsifiers

[counterexample] A `TensorFace` presented without the occurrence and port diagram is not a holon.

[counterexample] A face reindex that lacks an occurrence lift or either port square is not tensor
naturality.

[counterexample] Calling every scalar collapsed, or claiming a canonical causal expansion from its
value alone, exceeds the preimage theorem.

[counterexample] Naming an affine witness a complete `NativePreimageFibre` without proving that its
radical spans the full kernel overstates the engine contract.

[counterexample] Calling the Copson surface an RMS, merging `c_CD` with `Λ_DN`, or importing Copson
into RH because both names contain “de Bruijn” refutes the separation of the two lines.

[counterexample] A photography, entropy, Galois, compression, or RH analogy promoted above
interpretation without a typed passage and theorem refutes the epistemic boundary.
