# Mathematics and native conduct

[definition] This note joins recent moving-frame, Navier–Stokes, heat-current and Riemann-source
work to live native HNA owners. It records reusable relations and grades without scheduling
construction or promoting mathematics into a product capability. Source was inspected at
`6f547c4a`; formal grades below retain the cited records' check scopes, without rerunning proofs.

[definition] The [September 8 NS/Euler review](../research/records/2026-09-08_THE_NS_EULER_REVIEW_EXPOSES_THE_GENERATOR_GAP_IN_AC1.md)
adds the external theorem-scope comparison and an exact transported-phase Euler generator.
Two initial fields with equal modal energies and mean covariance produce opposite new low-mode
currents. The complete solution has a convergent generator unfolding; its recovery from limited
observations remains an AC1 question. The external blowup claims have not been independently
kernel-checked here. Machine-learning construction is paused for this mathematical work.

## Standing distinction

[definition] The native HNA foundation is the bounded local rational-linear phase ecology owned by
[`NativeConstitutiveEcology`](../crates/holonic-engine/src/native_ecology/constitutive_fibre.rs)
and exposed through [`NativeSession`](../crates/holonics-hna/src/native.rs). It forms relations
from actual paired currents, retains outside-domain and plural readings, and advances one owner.

[established-bounded; measured] NCF0–NCF4 establish that foundation, contextual receiver controls,
process continuation, and persistent world/model state at their recorded scopes. See
[`NATIVE_HNA.md`](NATIVE_HNA.md) and the
[NCF4 integrated return](../research/records/2026-09-06_NCF4_THE_WORLD_AND_NATIVE_ECOLOGY_CONTINUE_TOGETHER_AND_THE_CONSUMER_COSTS_ARE_MEASURED.md).

[project-postulate] This is a native contextual foundation, not Athena-alpha. The current
position explicitly records that Athena-alpha has not been attained
([`CONSTRUCTION_STATE.md`](../CONSTRUCTION_STATE.md)). Formal mathematics, native local
formation, and product-level language usefulness remain separate evidence scopes.

[definition] Lean is an exterior research verification surface. Its definitions and checked
theorems may specify or explain a relation; a live Lean parser, kernel, theorem emitter or verdict never enters a cultivation/inference
pipeline. Mathematical constructions are reused through native implementations of their actual
relations. Lean text already in the conversation data remains ordinary material.

## Oriented fluid current

[proved-derived; formal-checked] The live fluid current is

```text
C(u) = u × curl(u).
```

[`velocityVorticityCurrent`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesLambCurrentEvolution.lean)
defines this current from one actual velocity field and its actual curl. The same file defines
[`velocityVorticitySource`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesLambCurrentEvolution.lean),
which retains pressure, stretching, force, curl-force, and mixed-diffusion contributions.

[proved-derived; formal-checked] On a smooth interior slab,

```text
∂t C + (u · ∇)C = ν ΔC + S_C.
```

[`smoothSolutionOn_velocityVorticityCurrent_equation`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesLambCurrentEvolution.lean)
derives this from the actual momentum and vorticity equations. The component form
[`smoothSolutionOn_current_component_balance`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesLambCurrentEvolution.lean)
provides the local divergence form. The actual cell/face integration is separately carried by
[`NavierStokesLambCurrentCell`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesLambCurrentCell.lean).

[proved-derived; formal-checked] The nonlinear decomposition is not a scalar split. For
`u = v + w`,

```text
C(u) = C(v) + v × curl(w) + w × curl(v) + C(w).
```

[`velocityVorticityCurrent_add`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesLambCurrentEvolution.lean)
retains both mixed currents and the unresolved term. This is the mathematical counterpart of
retaining a complete incoming fibre before selecting a receiver face.

[proved-derived; formal-checked] The differential product rule also retains both mixed spatial
terms. [`laplacian_cross`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesCrossCurrentCalculus.lean)
states

```text
Δ(f × g) = (Δf) × g + f × (Δg)
          + 2 Σᵢ (∂ᵢf × ∂ᵢg).
```

The mixed term is part of the current source. It cannot be removed by taking a magnitude,
component mean, or energy receiver.

## Temporal null and reopening

[proved-derived; formal-checked] The heat instance provides an exact temporal null example.
[`entropyHeatJ`](../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicEntropyHeatCurrent.lean)
and [`entropyHeatK`](../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicEntropyHeatCurrent.lean)
are initially aligned, so

```text
χ(J,K) = J₀K₁ − J₁K₀ = 0 at t = 0,
```

while [`entropyHeatCrossCurrent_nonzero`](../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicEntropyHeatCurrent.lean)
shows reopening for `ν > 0`, `t > 0`, and `sin(x) ≠ 0`. Here `J` and `K` are
four-axis sections, and `χ` is their oriented 0–1 receiver, not a three-vector cross product.

[proved-derived; formal-checked] The relation itself has a source:

```text
∂t χ(J,K) − ν ∂x² χ(J,K) = −2ν χ(∂x J, ∂x K).
```

[`entropyHeatCrossCurrent_sourced_heat_equation`](../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicEntropyHeatCurrent.lean)
keeps that source on the null fibre. The general oriented receiver and its alignment fibre are
owned by [`HolonicEntropyActionInduction`](../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicEntropyActionInduction.lean),
including `entropyAxisCrossCurrent` and `EntropyAxisCrossFiber`.

[definition] For native conduct, a temporal null requires the complete situated fibre that
produced it and the generator action that transports it. Equal scalar readings do not identify
occurrences. Discarding its distinctions as a dynamic condensation requires that each admitted generator
preserve the receiver equivalence. Otherwise retain the distinguishing material or report the
condensation obstruction; ordinary uncondensed operation can still continue.

## Contact, condensation and cultivation

[established-bounded; measured] The live contact operation is
[`NativeConstitutiveEcology::advance`](../crates/holonic-engine/src/native_ecology/constitutive_fibre/circulation.rs).
It derives source sections from the incoming and held phase currents; an actual emitted-source
handle attaches a later receiving current. It stages one device operation, and returns `Unique`, `OutsideDomain`, or `Plural` through
[`ConstitutiveReading`](../crates/holonic-engine/src/native_ecology/constitutive_fibre.rs).
The formed pivot and successor rank are observations of that local relation, not semantic
identity, reward, or quality.

[interpretation] The reusable bilinear contact correspondence is: preserve `C(v)`, both
mixed currents, and `C(w)` as separately addressed contributions until the declared receiver
has joined them. A native contact may then read a chosen face, while its complete source,
target, orientation, lineage, and unresolved remainder remain available for reconstruction.
The specific comparison is preservation of the complete bilinear expansion under the declared
source-to-native map; a missing mixed term refutes that correspondence within this comparison. This is not a claim that every native
contact follows the fluid PDE.

[proved-derived; formal-checked] The formal resident-restriction owner
[`HolonicResidentRestriction`](../formal/elementary-holonics/ElementaryHolonics/Computation/HolonicResidentRestriction.lean)
proves that omitted rows decode to zero, retained rows are exact, and an additive overlay changes
the successor only through its actual supported rows. `decoded_successor_with_overlay` and
`current_delta_unchanged_outside_rows` are reusable finite laws for this contact ordering.

[established-bounded; source-inspected] The native condensation owner
[`recurrent_condensation.rs`](../crates/holonic-engine/src/native_ecology/recurrent_condensation.rs)
stores compact standing, an executable decoder, retained preimage fibres, and shortest
separating histories. Its `CondensedRecurrentRest::validate` checks the admitted bounded
one-generator passage and refuses malformed fibres or separators.

[proved-derived; formal-checked] The general quotient law is
[`DynamicReceiverChart.everyOrderedWordExact`](../formal/elementary-holonics/ElementaryHolonics/Computation/MachineLearningChart.lean):
an admitted quotient must commute with every ordered word in its declared generator family.

[established-bounded; source-inspected] The native [`HeterogeneousFusionRest`](../crates/holonic-engine/src/native_ecology/heterogeneous_fusion.rs)
retains generator names, boundary fibres, and `NaturalitySquare` receipts for its narrower
shared-generator passage.

[definition] Condensation remains lawful only for its declared future receiver family. A dynamic
fluid condensation would preserve the source/remainder fibre and verify each generator's
commuting square. The finite one-generator native condensation has no general PDE scope.

[established-bounded; source-inspected] A finite causal-adjoint cultivation owner is
[`CultivationContinuationRest`](../crates/holonic-engine/src/native_ecology/continuation.rs).
`LocalMetricAdjointReturn` derives a local metric return. `LocalFactorDelta::right_changes`
carries the exact right-coordinate difference; `ReconstructionFibre` records Boolean receipts
for the declared preservation and ablation checks, rather than containing the entire difference.
The inherited full-operator runtime stages deposits during the reverse traversal in
`operative_backward.rs`, through the retained forward morphology including earlier overlays.
`full_operation.rs` publishes the accumulated deltas only after `adjoint_return` succeeds; see the
[adjoint repair](../research/records/2026-09-04_THE_AUDIT_REPAIRS_THE_RECURRENT_ADJOINT_AND_RECONCILES_THE_OPERATING_CONTRACT.md).

[definition] A fluid residual can inform cultivation only as a returned, situated difference
with its oriented components and declared receiver conditions. A scalar residual norm, pressure
value, rank change, or proof verdict cannot select a deposit or author a successor.

## Changing frames and historical adjoints

[proved-derived; formal-checked] The anisotropic frame owner
[`NavierStokesAnisotropicFrame.lean`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesAnisotropicFrame.lean)
defines `diagonalFrame`, `inverseFrame`, `metricFrame`, `gridRate`, and
`physicalReconstruction`. Its `diagonalFrame_fibre` retains every source pair mapped to the same
frame output, including singular-factor cases; `diagonalFrame_det` records the determinant.

[established-bounded; measured] Native recharting is owned by
[`circulation/rechart.rs`](../crates/holonic-engine/src/native_ecology/constitutive_fibre/circulation/rechart.rs)
and exposed by [`NativeSession::rechart`](../crates/holonics-hna/src/native.rs). It transports
held phase and incoming incidence in one continuing ecology. Old emissions retain their source
frames, and a later reception crosses the actual old-to-current passage.

[definition] An adjoint or residual is evaluated in its production frame, then transported
through the declared map; raw coordinates from two frames are not directly comparable. Native
phase rechart realizes this discipline at bounded scope, without anisotropic scale, metric,
determinant, or physical PDE reconstruction.

[proved-derived; formal-checked] The pressure side follows the same receiver order.
[`NavierStokesPressureEvolution.lean`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesPressureEvolution.lean)
defines `pressureTimeJetAtOrder`, while
[`NavierStokesPressureJetReceivers.lean`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesPressureJetReceivers.lean)
defines `pressureWordReceiver`, its spatial derivative identity, and its time derivative through
the actual pressure source. The source remains complete before point or derivative projection.

## Residual source and local shape

[proved-derived; formal-checked] The anisotropic quartic owner
[`NavierStokesAnisotropicQuarticCurrent.lean`](../formal/elementary-holonics/ElementaryHolonics/Millennium/NavierStokesAnisotropicQuarticCurrent.lean)
proves that the complete current's null fibre is exactly `kappa = b = c = 0`, while the raw
pressure chart has the weaker `epsilon * D = b = c = 0`. A zero first jet therefore does not
erase the higher current fibre.

[established-bounded; computational-witness] The viscous-core and pressure-evolution records
show that matching a first-gradient rate can still leave nonzero cubic pressure currents and
nonzero relative-strain curvature. See the
[viscous-core return](../research/records/2026-09-05_MFR3_THE_VISCOUS_CORE_RETURNS_ITS_PERIODIC_STRAIN_SOURCE_AND_CUBIC_RESPONSE.md)
and [pressure-evolution return](../research/records/2026-09-05_MFR3_THE_PRESSURE_TIME_SOURCE_RETURNS_THE_MOVING_QUARTIC_CHART_AND_RELATIVE_STRAIN_CURVATURE.md).

[definition] Equality at one local jet or terminal row is not equality of continuing
morphology. For a declared higher spatial/temporal receiver, its source terms must survive the
projection or its lost distinction remains explicit.

[open] Quantitative localized residual control, nonlinear stability, terminal continuation, and
full physical continuation remain open at the MFR records' declared scopes.

## RH source transport as a robustness pattern

[proved-derived; formal-checked] MFR2's
[`FoldedSource`](../formal/elementary-holonics/ElementaryHolonics/RH/FoldedSource.lean)
constructs the folded source family with its full complex receiver. Its derivative, Gaussian
tail, and zero-count owners retain the omitted population and eventual cutoff conditions:
[`FoldedSourceBounds`](../formal/elementary-holonics/ElementaryHolonics/RH/FoldedSourceBounds.lean),
[`FoldedSourceDerivative`](../formal/elementary-holonics/ElementaryHolonics/RH/FoldedSourceDerivative.lean),
and [`FoldedSourceZeros`](../formal/elementary-holonics/ElementaryHolonics/RH/FoldedSourceZeros.lean).

[proved-derived; formal-checked] DB5 records the exact threshold equivalence
`RiemannHypothesis ↔ Λ_DN = 0`; RT6 establishes `0 ≤ Λ_DN` at its three stated axioms. The
remaining arithmetic sign is still open. See the
[DB5 record](../research/records/2026-09-03_DB5_THE_LAST_PORT_IS_DISCHARGED_RH_IS_LAMBDA_DN_EQUALS_ZERO_WITH_NO_PORT_AND_THE_TREE_TIME_IS_THE_STANDARD_TIME_OVER_FOUR.md)
and [MFR2 record](../research/records/2026-09-04_MFR2_THE_FOLDED_SOURCE_RETURNS_EVERY_HEAT_TIME_WITH_A_GAUSSIAN_REMAINDER_AND_ZERO_COUNT_RECEIVERS.md).

[definition] The reusable HNA consequence is source/tail/receiver robustness: preserve the
complete source population, oriented remainder, receiver domain, and conditions for commuting
finite projection. A zero count, symmetry, threshold, or proof equivalence remains a receiver
result, not a generic neural theorem.

## Native boundary summary

[established-bounded; measured] The native path joins actual currents, local relation formation,
frame-aware recharting, successor persistence, and bounded receiver fibres through the owners in
[`ARCHITECTURE_MAP.md`](ARCHITECTURE_MAP.md).

[definition] The mathematics supplies disciplined carrier shapes for comparison: oriented current,
full mixed source, transported frame, historical fibre, explicit residual, and receiver conditions.
Any comparison remains subject to the exact native owner, declared receiver family, and grade.
