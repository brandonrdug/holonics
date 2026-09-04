# Tensor lenses return tensor faces, and causal-natural holons retain preimage fibres

**Date:** 2026-09-02
**Scope:** HTP0--HTP4 construction and the HTP5--HTP6 roadmap.
**Authority:** Brandon's direct instruction of 2026-09-02, composed by
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) under
[`blueprint/THE_HOLON_IS_CAUSAL_NATURAL_AND_TENSOR_LENSES_RETURN_TENSOR_FACES.md`](../../archive/plans/THE_HOLON_IS_CAUSAL_NATURAL_AND_TENSOR_LENSES_RETURN_TENSOR_FACES.md).
**Truth status:** per claim under [`canon/EPISTEMIC_GRADES.md`](../../docs/canon/EPISTEMIC_GRADES.md).

## 1. Return

[proved-derived; formal-checked] HTP0--HTP4 passed. The Lean API now calls a literal inverse image
`PreimageFibre`; the elementary holon has a complete-diagram rebase; a causal-natural family varies
occurrences, both ports, and receiver faces functorially; tensor lenses and tensor faces are distinct
objects; and the finite Copson--de Bruijn tail receiver returns exact suffix balance and
homogeneity. The finite surface is continuous and positive on the compact mass-one simplex; its
attained minimum returns the optimal finite coefficient and the homogeneous inequality. The main
`ElementaryHolonics` umbrella rebuilt 9,771 jobs under Lean 4.33 without a new axiom or `sorry` in
the new owners.

[definition] HTP5 is the next deed: return zero-extension monotonicity and both directions of the
finite/infinite `ℝ≥0∞` boundary for `ℕ -> ℝ≥0` inputs, with the infinite coefficient explicitly the
supremum of the finite coefficients. HTP6 owns the finite Euler/recurrence bridge, infinite
threshold equivalence, two stated asymptotic branches, and a width-`10^-9` rational enclosure.

## 2. The terminology split is semantic

[definition] `PreimageFibre` means exactly

```text
f⁻¹(y) = { x | f(x) = y }.
```

[proved-derived; source-inspected; formal-checked] Every Lean identifier containing
`ReconstructionFibre` or `reconstructionFibre` was definitionally such an inverse image. The
coordinated breaking rename updated 157 matched lines across 36 existing Lean files, then extended
the new API. A second classified tranche updated 45 American-spelled literal-preimage lines across
six files, including measured-difference, granular-boundary, membrane, port-history, finite-depth,
and projective-transport preimages. Analytic quantities whose names use `ReconstructionFiber` for an
actually reconstructed remainder or tail retain that name. No old-name alias remains.

[definition] The broader word `reconstruction` was not globally replaced. It remains appropriate
for actual inverse transforms, Fourier recovery, exact decoder and round-trip results, remount,
restoration, and homotopy. This distinction prevents a preimage population from implying an
executable inverse while preserving names for operations that genuinely recover another
presentation.

## 3. The formal holon boundary

[proved-derived; formal-checked] `Foundation/Holon.lean` now provides
`Holon.Rebase left right`. It requires equivalences of the complete elementary occurrence, source,
target, and receiver diagram and commuting source, target, and receive squares.
`Rebase.preimageFibreEquiv` proves that
the complete population behind a face travels through that full diagram equivalence.

[proved-derived; formal-checked] `Foundation/CausalNaturalHolon.lean` provides a strict
`Type`-valued family over a declared parameter category:

```text
Occurrence, Source, Target, Face : Parameter ⥤ Type
source  : Occurrence ⟶ Source
target  : Occurrence ⟶ Target
receive : Occurrence ⟶ Face.
```

Each component is an elementary `Holon`. Naturality of all three transformations is exposed
pointwise, and an arbitrary parameter arrow maps the complete preimage forward without fabricating
an inverse.

[proved-derived; formal-checked] The causal adjective is carried by additional structure, not the
category's name. Every parameter arrow owns an addressed `parameterPassage`; every entering
occurrence has a crossing; its target equals functorial occurrence transport; and its returned face
equals the receiver face of that target.

[open] The receiver-decorated span bicategory remains a stronger future owner. Pullback passage
composition is associative through a boundary-preserving equivalence, so its associator and unitor
coherence are not silently claimed by the strict first presentation.

## 4. TensorLens and TensorFace

[proved-standard; formal-checked] `TensorFace R Slot` is Mathlib's dependent tensor product over a
finite axis type. Different axes may carry different module types. The equal-factor specialization
is `HomogeneousTensorFace R order V`, indexed by `Fin order`; its order-zero case has the standard
scalar chart. An order-two face is a two-factor tensor, not a matrix until finite bases and the
relevant primal/dual or row/column chart are supplied. Tensor order is separate from matrix rank,
tensor decomposition rank, incidence rank, cycle rank, carrier rank, and representation rank.

[proved-derived; formal-checked] `Foundation/HolonTensorLens.lean` defines:

```text
TensorLens Carrier R Axis Slot
  project : Carrier -> TensorFace R Slot.
```

`TensorLens.applyToHolon` changes only the receiver face. The original holon continues to own its
occurrences and oriented ports. `dependentAxisReindex` carries a heterogeneous factor family along
an axis equivalence; it is not a basis-coordinate theorem. The narrower
`Holon.HomogeneousSlotNaturality` requires every permutation of equal `Fin order` slots to lift to
a coherent occurrence equivalence while preserving source, target, and receive. Its
`preimageFibreEquiv` transports the entire inverse image behind that slot permutation.

[proved-derived; formal-checked] The same owner defines `MorphologyArtifactPassage` as the minimum
contract required for the artifact name: every `rest` validates, `remount` returns the same
morphology exactly, and `receiver_after_remount` preserves every later receiver. It does not infer
durability or serialization from a dependent tuple.

[counterexample] Classical tensor covariance alone does not provide the occurrence population,
caused incidence, addressed ports, receiver map, preimages, or causal-parameter naturality. A
tensor therefore does not become a holon merely by acquiring a natural-looking index order.

## 5. The finite Copson--de Bruijn receiver

[proved-derived; formal-checked] `Mathematics/CopsonDeBruijnFiniteTail.lean` defines, for a
nonnegative `a : Fin N -> ℝ≥0`,

```text
E_N(a,n) = Σ_(k ≥ n) a_k²
B_N(a)   = Σ_n (sqrt(n+1))⁻¹ sqrt(E_N(a,n))
A_N(a)   = Σ_n a_n.
```

The complete `FiniteTailFace` retains every suffix energy along with mass and surface;
`FiniteTailPreimage` retains every section returning that face. The owner proves adjacent-tail
balance, all zero laws, degree-two homogeneity of energy, and degree-one homogeneity of radius,
mass, and surface.

[proved-derived; formal-checked] `Mathematics/CopsonDeBruijnFiniteSharp.lean` defines the
nonnegative mass-one simplex at every length `N + 1`, proves continuity and strict positivity of
`tailSurface`, and returns an attained positive minimum by compactness. Its reciprocal
`finiteSharpCoefficient N` controls every finite section after normalization. The chosen minimizer
attains equality, and any coefficient controlling every section is proved at least this large.

[definition] The index shift is explicit: Lean's `finiteSharpCoefficient N` is the mathematical
`c_(N+1)`. The next monotonicity law compares `finiteSharpCoefficient N` with
`finiteSharpCoefficient (N + 1)`, and the later finite recurrence terminates at `u_(N+1) = 1` for
that coefficient.

[definition] HTP6 must not totalize a failed real recurrence with `Real.sqrt`. Its
`AdmissibleRealRecurrence x` is a dependent family whose iterates carry proofs that they are at
least one; failure to continue returns an obstruction. Before the infinite threshold theorem it
must derive coordinate positivity/interiority, the Euler/KKT equations, the finite recurrence, and
the terminal condition. Its numerical pass boundary is the explicit width-`10^-9` enclosure

```text
1106495771 / 10^9 < c_CD < 1106495772 / 10^9.
```

[counterexample; source-inspected] This is not a root-mean-square: `n+1` is the one-based starting
index, not the cardinality of the suffix. The finite canonical aperture is triangular. Independent
width/depth cutoffs are exterior probes and require a cofinality theorem to recover the same
infinite functional.

[proved-standard; source-inspected] The reported sharp coefficient is
`c_CD = 1.1064957714...`; its floating decimal is measured testimony rather than a formal identity.
The primary inequality source is [Copson (1928)](https://doi.org/10.1112/jlms/s1-3.1.49), and the
threshold recurrence is recorded in [de Bruijn, *Asymptotic Methods in
Analysis*](https://archive.org/details/asymptoticmethod00brui_284).

[interpretation] The recurrence's critical branch change supports a phase-seam reading. No theorem
here identifies the inequality with Galois theory, conservation of faces, information compression,
or a Riemann-hypothesis bound.

## 6. The two de Bruijn lines

[counterexample; source-inspected] A later coordinate audit corrected this paragraph's initial
interpretation. The concurrent `ElementaryHolonics/RH/` work returned the entire `s`-plane flow
`heatE(u, xi, s)`, its backward heat equation, conjugation/reflection symmetries, zero-count
stability, simple-zero persistence, and a continuous local zero curve. Under the standard
critical-line chart, however,

```text
H_t(z) = (1/8) heatE(-t/4, xi, 1/2 + i z/2).
```

Positive `heatE` time is negative standard de Bruijn--Newman time. The Lean theorems stand at their
defined scope; the direct identification of their positive-time flow with standard `H_t` is
retracted pending the RH0/RH1 bridge. Copson remains in `Mathematics/` and imports no RH or
Millennium owner.

[definition] Use `c_CD` for the Copson--de Bruijn coefficient and `Λ_DN` for the de
Bruijn--Newman threshold. Their only admitted common lens is interpretation-grade: each is the
lower boundary of an upper admissibility set. The original heat-flow source is [de Bruijn
(1950)](https://doi.org/10.1215/S0012-7094-50-01720-0); modern RH-line context includes
[Rodgers--Tao](https://arxiv.org/abs/1801.05914). No cross-theorem was introduced.

## 7. Engine and blueprint consequence

[counterexample; source-inspected] `NativeExactReconstructionFibre::validate()` currently checks
that the particular solution maps to the returned covector and that every listed radical vector is
annihilated by the return operator. It does not check that those vectors span the complete kernel,
or that they are independent. Constructors often derive a kernel basis, but the public serialized
owner does not enforce that fact.

[definition] The parked WRN migration therefore gates
`NativeExactReconstructionFibre -> NativePreimageFibre` on a complete-kernel-span validation. If
that proof is not returned, the lawful name is `NativeAffinePreimageWitness`. The broad
`MorphologyReconstructionLane` becomes `MorphologyTestimonyLane`, not `MorphologyPreimageLane`,
because it also contains separators, constitutive families, departed withdrawals, and open
obligations.

[definition] The refined application vocabulary is map/value/container:

1. `MorphologyTensorLens` is the application-owned coordinate map;
2. `MorphologyTensorFace` is the returned coordinate value; and
3. `NativeMorphologyArtifact` is a valid rested carrier that remounts the same hot morphology and
   its body-indexed testimony exactly; a serializable carrier without that passage is
   `NativeMorphologyCarrier`.

[interpretation] A latent photographic nucleation pattern can instantiate this law only after an
exposure map, lattice residue, later developer passage, and receiver are supplied. It can constrain
future growth without reproducing the incident microscopic wave. That physical reading does not
define every preimage or imply reversal of thermodynamic history.

## 8. Validation

[established-bounded; formal-checked; measured] The following returned on 2026-09-02:

- `bash tools/lean_check.sh ElementaryHolonics.Foundation.CausalNaturalHolon` -- 3,010 jobs,
  passed;
- `bash tools/lean_check.sh ElementaryHolonics.Foundation.HolonTensorLens` -- 3,015 jobs, passed;
- `bash tools/lean_check.sh ElementaryHolonics.Mathematics.CopsonDeBruijnFiniteTail` -- 3,016
  jobs, passed;
- `bash tools/lean_check.sh ElementaryHolonics.Mathematics.CopsonDeBruijnFiniteSharp` -- 3,017
  jobs, passed;
- `timeout 180s lake build ElementaryHolonics` -- 9,771 jobs, passed;
- `bash tools/lean_check.sh` -- 3,772-job live engine-oriented umbrella, passed;
- `bash tools/gates.sh formal source-shape epistemic-tags claim-index document-law` -- five passed,
  zero failed; and
- exact search for `ReconstructionFibre|reconstructionFibre` in live Lean -- zero occurrences; the
  six classified American-spelled literal-preimage families are also absent under their old names,
  while separately classified analytic reconstructed-tail identifiers remain.

[established-bounded; process-audit] `claim-index` initially reported the expected disagreement
after the new September records entered the tree. The index was regenerated only after this receipt
was present, and the five named gates then passed. HTP5 remains the current frontier
in both the roadmap and construction state; no Rust implementation owner or capability grade moved
in HTP0--HTP4.
