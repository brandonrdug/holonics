# Universal Lean–Rust–CUDA catalog

**Status:** descriptive navigation maintained with owner changes. This catalog schedules nothing,
grades nothing by itself, and has no generator or release gate. The roadmap and construction state
remain the only scheduling authorities.

## Reading rule

[definition] The public framework entry point is `crates/holonics/src/lib.rs`. `structure` and
`geometry` re-export their existing crates without default features; default `native` includes
the engine and application owners. See [the Rust guide](RUST_FRAMEWORK.md). Its ground-up HNN
adapter is `crates/holonics-hna/src/native.rs`; the earlier inherited-operator adapter is `hna.rs`
in that crate. Shared delivery is `stream.rs`; CLI entry points are
`applications/holonics-workbench/src/{adapters/hna,session_stream}.rs`. These compose the native
owners below. See [native HNN](NATIVE_HNA.md), [Athena](ATHENA.md) and
[interoperability](INTEROPERABILITY.md) for their distinct artifact boundaries.

The [mathematical synthesis](MATHEMATICS_AND_NATIVE_CONDUCT.md) explains recent cross-line
consequences, and [hardware/modality boundaries](HARDWARE_AND_MODALITY_BOUNDARIES.md) locates
future Apple and acoustic composition. These are source comparisons, not implemented backends
or a Lean runtime inside HNN.

Each row connects one mathematical relation to its live formal and executable presentations.

- **exact** means the named implementation owns the same stated carrier/law in the row's declared
  scope;
- **partial** means the implementation owns a receiver projection or strict subset;
- **formal-only** means no Rust/CUDA realization is admitted;

Paths are stable owner addresses, not line citations. A hash, filename, count, output artifact, or
test result never upgrades a correspondence.

## Formal framework entry points

[definition] [`ElementaryHolonics.Framework`](../formal/elementary-holonics/ElementaryHolonics/Framework.lean)
is the default formal import/build face. Its Core, Geometry, Dynamics, Information, Physics and
Computation subjects compose the existing owners; the complete `ElementaryHolonics` research
umbrella additionally retains all problem-specific modules. The
[framework guide](FORMAL_FRAMEWORK.md) connects molecular conformation, active tube interiors,
phase, geometry, physical boundaries and computation at their declared scopes.

| Relation | Implementation owner | Historical namespace / import compatibility |
|---|---|---|
| Ordered generator action and endpoint order blindness | `Foundation/TransportWord.lean` | `Millennium.Chronology` retains its applied material and imports this owner |
| Future-exact receiver compression | `Foundation/ReceiverHistoryCompression.lean` | `Millennium.LineageCompression` forwards the import |
| Clocked addressed spans and returned world-tubes | `Transport/WorldTube.lean` | `Millennium.HolonicSensoryWorldTube` forwards the import |
| Complex phase carrier, locked sheets and winding fibres | `Physics/PhaseCarrier.lean` | `Millennium.HolonicParametron` forwards the import |
| Oriented incidence, coupled response and phase-bearing holons | `Physics/CoupledIncidence.lean` | `Millennium.HolonicComplexParametron` forwards the import |
| Quadratic port dynamics and retained heat | `Physics/PortEnergyHeat.lean` | Chain-rule storage/source/dissipation balance; nonnegative conductance and explicit heat law |
| Partitioned Hodge/complex energy and paired cut boundaries | `Physics/PartitionedHodgeEnergy.lean` | Arbitrary finite section mixed-energy law; exact four-cycle harmonic/exact and diffusion reference; imported by `Framework.Physics` |
| Complex scattering power and attenuation return | `Physics/ScatteringWaveHeat.lean` | Two-port norm preservation and complementary heat; finite constitutive channel |
| Phase-connected contact, reorientation and intensity defect | `Physics/PhaseContactPassage.lean` | Passive seam/heat and transported sum, gauge covariance, signed-cycle section and amplitude/intensity interpolation difference |
| Biochemical reaction current and joint fold/occupancy receiver | `Physics/ReactionCurrent.lean` | Stoichiometric enzyme/substrate conservation, positive mass-action rates, equal-marginal binding separator and distinct labeled emissions from the same body return |
| Observer stress, angular derivative jets and positive rest energy | `Physics/ReceiverStressEnergy.lean` | Both Lorentz indices, perfect-fluid and boosted dust/vacuum readings; mass-shell owner reused |
| Complete finite change of incidence, material and internal state | `Physics/ConstitutiveModulation.lean` | New `Soma.Holonics.Physics.ConstitutiveModulation` theorems over the existing `coupledResponse`; formal-only |

[definition] Paths in this table are relative to `formal/elementary-holonics/ElementaryHolonics/`.
Declaration namespaces remain stable. These source extractions preserve old imports without
retaining duplicate definitions. Endpoint commutation does not identify carrying histories.
The finite modulation return supplies no automatic native response law or molecular calibration.

[definition] The continuing unification adds `Transport/ChangingReceiver.lean` for addressed
finite and moving differential receiver defects; `Physics/ConformationResponse.lean` and
`Physics/MechanicalReceiver.lean` instantiate prestress and changing-grain mechanical response;
`Physics/FluidReceiverClosure.lean` instantiates the same defect with the existing finite
Galerkin Navier–Stokes source. `Physics/ConstitutiveModulation.lean` additionally composes the
moving receiver with stress/strain pullback. These are formal owners; they add no native engine.
Their statements and limits are in the
[continuation](../research/records/2026-09-08_CHANGING_CONSTITUTION_AND_RECEIVERS_SHARE_ONE_DEFECT_CALCULUS.md).

[definition] The [construction programme](plans/THE_REALITY_OF_DIFFERENCE_IN_CONSTRUCTION.md)
now uses `Transport/ReceiverPotential.lean` for complete compatible future images, refinement,
rebase and useful tolerance/convergence; `Foundation/JointReceiverDescent.lean` constructs the
canonical additive joint quotient and its exact generator criterion; `Geometry/SwingPotential.lean`
transports those families and quotient words through the existing affine Swing.
`Physics/MechanicalReceiver.lean` supplies the plural-source/exact-future use, and
`Computation/JointReceiverWitness.lean` formalizes the recorded bit-marginal counterexample.
These are formal owners, not a new native decoder or a claimed implementation of the whole
programme. Paths are under `formal/elementary-holonics/ElementaryHolonics/`.

[definition] The continuing current construction adds the following owners. Its
[record](../research/records/2026-09-08_CLOCKED_TORUS_CURRENTS_CONTINUE_THROUGH_A_RETAINED_FIBRE.md)
and [exact executable comparison](../research/experiments/four_torus_current/README.md) retain
the geometry, clock, source family, full-current decoder, blind fibre and costs.

| Relation | Formal owner under `ElementaryHolonics/` | Executable scope |
|---|---|---|
| Complete clocked resegmentation and boundary-family images | `Transport/WorldTubePotential.lean` | Formal-only equivalence of addressed fibres and carried future families |
| Rational cut/current chart and full four-cut remainder | `Physics/FourTorusCurrentChart.lean` | Exact rational axis/square incidence in `holonic-engine/examples/four_torus_current.rs` |
| Explicit material response and fixed-source uniqueness | `Physics/TwoFaceConstitutive.lean` | Exact two-face advance in the same exterior example |
| Six-coordinate extraction, decoder and retained joint kernel | `Physics/ConstitutiveCurrentReduction.lean` | Exact extraction and cold residual checkpoint; full reference uses public `exact_linear::ExactRatMatrix` |
| Actual square Gram/cut matrices and constitutive chart | `Physics/FourTorusTwoFace.lean` | Formal and computational certificates at grains 1 and 2 |
| Real cast into existing Parametron coupled response | `Physics/FourTorusParametronCurrent.lean` | Rational response chart; no complete LC/phase-network execution claim |
| Actual constitutive steps with complete-state pullback joins | `Physics/ConstitutiveWorldTube.lean` | Example retains rational chronology and source inputs; exact fresh-process continuation comparison |
| Typed scale passage and all-input-word future receiver family | `Physics/ConstitutiveScale.lean` | Formal all-word law; finite varying-input comparison in the same exterior example |
| Accumulated normal residual, finite source drift and square completion | `Physics/AccumulatedNormalResponse.lean` | Exact cold `normal_geometry_review.rs` controls over the public matrix/paired owners; the active `field/material_transport/normal.rs` remains the native normal realization |

[definition] These executable correspondences concern a finite exterior constitutive experiment.
No Lean/runtime binding, new HNN engine or anatomical/continuum identity is introduced.

[definition] `Geometry/ExteriorBoundary.lean` exposes the cochain/boundary pairing, induced
pullback naturality, square-zero under the chain condition, and the exact boundary-transport
defect. It reuses `LinearMap.dualMap` and imports Mathlib's smooth `extDeriv_pullback` owner.
The [Stokes/pullback return](../research/records/2026-09-09_STOKES_AND_PULLBACK_NATURALITY_ARE_FRAMEWORK_LAWS.md)
connects these to addressed boundaries, four-torus currents and the existing smooth flux sources.

[definition] The [relevance/loss foundation return](../research/records/2026-09-09_RELEVANCE_LOSS_AND_REALIZED_CLASSES.md)
adds `Foundation/CausalRelevance.lean` (greatest stable future relation and additive kernel),
`Foundation/ComparisonLoss.lean` (situated comparison gauges), and
`Foundation/InformationReceiver.lean` (the moved generic information implementation; old names
and `Computation.HolonicInformationTheory` import preserved). `Physics/InformationDifference.lean`
proves the baseline/KL and finite Gibbs free-energy relation; `Physics/TwoCellEntropyTransport.lean`
proves mass and logarithmic entropy returns for actual constitutive trajectories. These formal
owners add no native learner or physical identity outside their stated hypotheses.

[definition] `Foundation/SituatedInformationRate.lean`, imported by `Framework.Information`,
owns finite measured-occurrence information rates, transported-measure invariance, conserved
subdivision and nats/bits conversion. The existing `holonic_engine::surprisal` owner retains
exact prime-log forms and code-missing fibres. `eta_atlas::derive_ordinate_relations` reads
interval marks directly; `holonic-engine/examples/zeta_information.rs` composes atlas phase,
gap, Swing and information receivers as exterior Hephaestus apparatus. The
[measured return](../research/records/2026-09-11_ZETA_PHASE_SWING_AND_INFORMATION_RATES_ARE_MEASURED.md)
records the exact analytic and verifier scopes; these are not native formation owners.
`examples/support/phase_signature.rs` shares that enclosure receiver with
`examples/eta_generator_comparison.rs`, which compares existing analytic routes and retains
prime/phase lifts, analytic tails and a literal exterior prefix-code packet. Its code-length
and remainder observations feed operator reuse without installing a native tokenizer.

[definition] `Foundation/ReceiverCodeCost.lean`, imported by `Framework.Information`, composes
code/cost balances through `Holon.Interaction`, bounds cost from endpoint/residual bounds, and
transports a feasible optimum under a cost-preserving candidate equivalence. The exterior
`holonic-engine/examples/receiver_code_cost.rs` instantiates unequal-cost channel paths and
transported clock readings. The [boundary return](../research/records/2026-09-11_RELATIVE_CODE_COST_HAS_AN_ADDRESSED_BOUNDARY_LAW.md)
connects it to the existing addressed causal-length, physical and complexity owners.

## Foundation and transport

[definition] `Mathematics/GeneratorFactorization.lean` owns the arbitrary finite commutative-ring
bilinear coefficient certificate, selected three-product identity, ratio-block matrix bridge,
shift/coordinate commutator and first-jet product composition. `Framework.Computation` imports
it. `crates/holonic-engine/examples/generator_factorization.rs` performs bounded exterior
algorithm/route synthesis using `ExactRatMatrix::preimage_fibre` and its obstruction/verification
owners; it is not a native HNN synthesizer. The
[solver return](../research/records/2026-09-11_HOLONIC_SOLVER_NAVIGATES_EXACT_GENERATOR_FACTORIZATIONS.md)
retains its grammar, exact factors, coefficient fibres and work scope.

[definition] `RH/ThresholdRefinement.lean` derives square-closure equivalence on the actual
seam-time set and the conditional halving limit. Its quadratic control is the existing polynomial
heat operator, with explicit off-real roots below its sharp time. It proves no improved ξ bound.
The [toolkit return](../research/records/2026-09-11_THRESHOLD_REFINEMENT_AND_PARTITIONED_ENERGY_RETURN_HOLONIC_TOOLKITS.md)
connects this to partitioned energy, the stronger external bound and the physical/arithmetical routes.

[definition] `Computation/GeneratorObservationScope.lean` supplies finite-observation ambiguity,
exact identification within a declared multiplier family, and excitation of a previously blind
generator difference. The [causal-entanglement/interface return](../research/records/2026-09-11_CAUSAL_ENTANGLEMENT_NEEDS_FUTURE_INTERFACES_AND_FOUNDED_GENERATORS.md)
connects those scopes to the existing future-receiver and compression owners.

[definition] `Mathematics/RatioSeriesTransport.lean` owns exact signed ratio-series block
composition, preserved clocks, arctangent recurrence and parameterized alternative routes with
the same complete action. The [September 11 study](../research/records/2026-09-11_ATHENA_STATUS_RETURNS_TO_TRANSCENDENTAL_GENERATOR_COMPRESSION.md)
connects it to recovered transcendental/compression material.
`Mathematics/RadixWindowReceiver.lean` owns interval-floor certification, integer-shift
invariance and the exact fractional-phase sector receiver; `Mathematics/MachinPhaseConstraint.lean` connects the lifted π identity to Gaussian
closure; `Mathematics/PiIterationConstraint.lean` owns the sine iteration's fixed points,
period transport, interval branches and local derivatives. The
[π/e return](../research/records/2026-09-11_PI_AND_E_CONSTRAINT_IDENTITIES_HAVE_ORIENTED_GENERATOR_FACES.md)
links these to the existing torus/prime owners and exact exterior window observations in
`research/experiments/transcendental_constraint_windows/exact_windows.py`. Complete analytic
tail/block/decoder composition and whole-decoder cost comparisons remain open.

[definition] `constitutive_fibre/law_rest.rs` owns `ConstitutiveFibreRest`, the learned local
relation's source chart, basis and chronology without an occurrence archive. It remounts into
`ResidentConstitutiveFibre`; existing resident current/condition ports conduct the learned law.
`circulation/rest.rs` owns the shared exact point-section wire used by both local-law and older
field rests. `Computation/HolonicConstitutiveFibreCollapse.lean` supplies the local vertical-span/
mass-fibre theorem used by the [fixed-condition audit](../research/records/2026-09-11_FIXED_CONDITION_COLLAPSE_IS_EXACT_AND_ITS_PROJECTION_IS_REUSABLE.md).
The audit checks the actual saved law and signed source witnesses; it does not change native
incidence or assume arbitrary observations form a single global linear chart. The [Rust guide](RUST_FRAMEWORK.md) and public `native_generator` example expose
this scoped generator construction.

[definition] `constitutive_fibre/resident/image.rs` owns full current-family images and received
source refinements. `constitutive_relation_image.cuh` composes the existing fibre/affine row
calculus; `surface_fibre_image.rs` validates and records its resident passage. Condition-image
coverage parsing and homogenized reception are shared with the original condition owner.
`ResidentConditionPreimage::refined_by` checks the actual source before returning constraints
to the existing `ResidentConditionCurrent::contact`; it adds no new metric or learner.

[definition] `constitutive_fibre/resident/neighborhood.rs` owns a continuing set of local learned
relations with explicitly shared condition standing. `resident/read.rs` queries the existing law
without material deposition. `condition_contact.rs` prepares contact against the actual immutable
predecessor and commits only to that owner. `neighborhood/rest.rs`, `condition_contact/rest.rs`
and `preimage/rest.rs` store laws/current/epoch/latest evidence; the last decoder reuses the resident
constraint query. The public `native_neighborhood` example calls these owners directly. No new
CUDA learning rule, token lookup or historical predictor enters this composition.

[definition] `field/material_transport/normal/direct.rs` exposes `ResidentNormalMaterial` and
`ResidentNormalReturn`, the existing accumulated normal law with supplied resident currents.
`surface_direct_normal.rs` validates the passage; `direct_normal_material.cuh` adapts its operands
to the existing normal increment/fit and bounded linear response. `normal.rs` now shares the
report/state decoders with the old field owner. No historical-source adapter is needed by this
direct local response. `normal/direct/enclosure.rs` now carries bounded output into later native
input; `normal/direct/section.rs` integrates supplied sections and retains actual operator cuts.
`surface_normal_section.rs` records those passages and the generic current difference receiver.
`normal_material_section.cuh` shares the existing observation increment, fit and response helpers;
`current_difference_section.cuh` constructs local differences with their comparands.

[definition] `constitutive_fibre/resident/section.rs` owns addressed point-current section views;
`section/difference.rs` retains their original path and local comparison fields. The source
attachment in `holonics-hna::native::section_input` uses the existing exterior `SymbolAlphabet`.
The public `conversation_difference_field` example calls these native owners directly. Its
published source run is a local normal-response construction, not a completed generative ecology.

[definition] `normal/direct/wave.rs` owns the fixed difference-generator word and its actual
current joins; `normal_wave.cuh` compiles the source-plane action and bounds its composed powers.
`normal/direct/wave/receive.rs` and `normal_wave_receive.cuh` join a received current to the
preceding joint family, stage its normal-material update and rebase to an enclosed/exact seed.
The receipt retains the producing fibre; the continuing wave does not retain a receipt chain.
`normal/direct/wave/develop.rs` stages whole-section normal development with joint-seed rebase
while preserving current occurrence identity. The section owner separates preparation from
publication; `crates/holonics-hna/examples/conversation_wave.rs` composes the native body with
exterior source/chart/cursor I/O.

[definition] `normal/direct/wave/comparison.rs` now owns `NormalProducingHandle`, `predict` and
`receive_prediction`: an addressed return keeps the actual producing joint/material while
incrementing contemporary material and preserving current occurrence identity. The shared
`normal_wave_receive.cuh` helper has separate producing/contemporary inputs for this comparison;
ordinary next-current reception keeps its original ABI. `wave/rest.rs` v5 stores active producing
cuts, rejects malformed lineage and reconstructs their source words across process exit. Completed
or released handles leave the active population; legacy normal-only rests remain supported.

[definition] `NormalWaveTransport` distinguishes the stored-M applied word from the wider
normal-reference family. Source and numerical-rounding bounds remain in both; the M/P comparison
is not reinjected into the applied source. `wave/reference.rs` reads one reference continuation
without creating a current occurrence. Rest v6 records the scope, including mixed pending cuts;
scope changes rebase the complete held enclosure without narrowing it. `field_normal_material.cuh`
now also caps its reference-operator error by the unit-prior target-energy law in
`Physics/AccumulatedNormalResponse.lean`, using the existing exact integer norm owner. The fitted
coefficients and moments are unchanged; cold validation accepts legacy and tightened certificates.

[definition] `normal/direct/wave/basis.rs` owns the read-only `NormalWaveBasisChart` and
`NormalWaveBasisFace`; `resident_section/surface_normal_wave_basis_face.rs` records its exact
projection/selection in `normal_wave_basis_face.cuh`. The native report carries selected address,
score, tie population, robust separation and shared radius; the full source/fibre remains resident.
`holonics-hna/src/native/section_input.rs` supplies the exterior symbol chart and spelling.
`native/normal_wave.rs` owns the moved wave, emission/re-entry phase and complete session rest;
`stream.rs::pump_wave` and the workbench `session_stream.rs` reuse the existing delivery owner.

[definition] `wave/source.rs` and `normal_wave_source.cuh` retain the shared `(c−p,c,p)` map;
`wave/family.rs` carries its anchor ball beside a complete homogeneous affine relation.
`resident/wave_relation.rs` and `constitutive_wave_relation.cuh` derive the fixed-condition
pullback and reuse `resident/image.rs` for serial family composition. `resident.rs` stages an
individual basis through `PreparedConstitutiveFormation`; `resident/neighborhood.rs` stages the
complete member/condition return before publication. These foundations do not yet replace the
normal wave's current by themselves; the coupled owner below now binds them.

[definition] `wave/family/receiver.rs`, `surface_normal_family_receiver.rs` and
`normal_family_receiver.cuh` own constrained-family support and the declared minimum-norm joint
receiver. `wave/family/rest.rs` and `resident/wave_relation/rest.rs` retain the original source,
anchor, affine relation and last map through process exit. These are exact family interfaces;
the continuing owner below now retains them; its public session is described below.

[definition] `wave/coupled.rs` transfers the neighborhood into a typed continuation of
`ResidentNormalWave`, owns its current family and admitted source/member bindings, and publishes
prepared local material/condition with the complete next family. `normal_coupled.cuh` checks
source-plane and family-support admission. `wave/coupled/rest.rs` and `wave/rest.rs` v7 persist
that owner, including its distinct normal bank and pending normal comparisons. Rest validates and
rebinds current contacts through their restored member/condition; it does not run a second learner.

[definition] `WaveSourceReceiver` in `resident/wave_relation.rs` declares the local source chart.
`Direct` keeps the original pullback; `UnitRealSum` applies the common-real-offset section to the
source of L and retains the raw residual state. The native derivation checks zero real returned
increment; `normal_coupled.cuh` checks observed unit-source reception. Relation rest v2 retains
and validates the chart and its complete gauge directions; coupled remount derives the saved map
from its actual material/condition. The relation derivation and generic affine-image kernels
use resident workspace sections rather than per-block shared scratch for their working vectors.

[definition] `resident/condition_contact/affine.rs` exposes the existing unit-admittance
reaction of actual standing with a complete affine return. `resident/wave_relation/source.rs`,
`surface_wave_source.rs` and `constitutive_wave_source.cuh` join the learned arrival, retain the
original prediction, realize that source reaction, and derive its total passive source-union map.
An empty learned arrival retains the actual offered current and its original obstruction.
`ResidentSourcePairs` prepares every adjacent field pair; `wave/coupled.rs` stages the ordered
field under one public successor and returns all local prediction fibres. Relation rest v3 and
coupled remount reconstruct the source reaction/map and rebind it to the actual restored local
law. These source maps preserve the original anchor, and are distinct from conditional joins.

[definition] `condition_contact/affine.rs::ResidentWaveSourceGeometry` compiles the producing
law's target-vertical matrix and its Gram projection. `ResidentWaveRelation` shares that derived
geometry through a lazy immutable holder. `constitutive_condition_contact.cuh` and
`surface_condition.rs` check every incoming direction and reuse the graph in the complete affine
contact; empty evidence preserves standing. The cache is rebuilt from actual law material on
remount and adds no semantic rest fields.

[definition] `resident/wave_relation/observation.rs` and `section_wave_observed_next` derive the
total actual-next-current graph `(p,c)→(c,v)` while preserving lambda and anchor. The family reuses
the exact total-map image. `wave/coupled.rs::receive_contact_next` stages that current-only
observation under one admitted source cut; its step retains both the predecessor family and
observed map. Relation rest v4 persists the actual observation and reconstructs the graph.
`NativeCoupledWaveSession::receive_next_symbol` binds the explicit `receive-next-symbol` stream
command. This is distinct from delayed observed-symbol material development, which remains open.

[definition] `wave/family/basis.rs::NormalFamilyBasisFace` retains the complete producing family
beside its projected minimum-norm joint receiver. `section_family_basis_face` in
`normal_wave_basis_face.cuh` selects a real unit-basis score on device; its free-direction flags
are not robust-winner bounds. `native/coupled_wave.rs::NativeCoupledWaveSession` owns conditional
generation, actual symbol-pair source re-entry, pending phases and complete coupled session rest.
`stream.rs::pump_coupled_wave` and `session_stream.rs::run_coupled_wave_session_stream` expose
that same owner. Pure `project-symbol` reads the current; `emit-symbol` first advances the
conditional law. `wave/coupled/comparison.rs` now retains producing handles and maps the complete source's
ordered parameters into paired Ψ/η coefficients through `section_wave_source_family_comparison`.
Wave rest v8 and coupled session v2 retain those pending cuts and their actual image lineage.
`compare-symbol` prepares the comparison; producing-family material development remains open.

[definition] `normal/direct/wave/actuate.rs` owns fixed-material source action. The
`normal_source_actuation.cuh` source word reuses the learned normal response and the enclosed
finite contact in `passive_current_ball.cuh`. Source union retains the incoming current;
the queried joint section changes under one owner. The exact H/B/M zero-subspace certificate
refines a source-specific bound without declaring global irrelevance or replacing applied M.
Rest v4 retains both seed-component epochs after this transport.
`surface_normal_wave.rs` records the resident passages. `normal/direct/rest.rs` and
`wave/rest.rs` own complete normal material and generator/seed/word persistence.
`inertia/source_energy.rs` checks positive source geometry, source-kernel compatibility and
target energy by fraction-free Schur elimination, cancelling admissible common dyadic content.
Cold rest and normal-state validation share `normal.rs`'s exact wire-scale numerical witness.
`normal/direct/refine.rs` and the normal
kernel refine numerical realization without changing exact moments or source-family bounds.

[historical] The SDK field/model wrapper, text adapters and eight alpha examples were
[retired recoverably](../archive/implementations/2026-09-09-byte-field-cultivation/README.md).
Core field/operative/receiver owners below remain mathematical and diagnostic constructions;
references to alpha text drivers name historical consumers, not current cultivation entrypoints.

[established-bounded; source-inspected] The [representation audit](../research/records/2026-09-09_THE_BYTE_CLOCK_AND_OCCURRENCE_EXPANSION_ARE_NOT_GENERATOR_CULTIVATION.md)
qualifies these owners: `OperativeState::prepare` allocates per observed contact,
`prepare_contextual_work` mounts historical predictors, and `NativeFieldRest` retains the input
and numerical history. Generic access is not a learned generator organization; the audit maps
the existing shared-mode, observable-form, leader/rebase and cycle/scale constructions to that gap.

[definition] Contextual execution stages reside in `kernels/field_contextual_material.cuh`:
independent historical weight rows and receiver coordinates follow the prepared current profile.
`section_constitutive_field_context_finish` in `constitutive_field.cuh` completes bounds and
commits the field once. `resident_section/surface_passage.rs` records all stages in one ordered
device passage; `field/material_transport/contextual.rs::ContextualWork` retains their scratch.
These are execution owners for the same source-qualified joint operation, not a second ecology.

[definition] **Preimage Fibre** is the governing term for compatible-source families. Some older
source symbols retain reconstruction names; those names do not require an inverse or raw-state
archive for learning. The [September 7 synthesis](../research/records/2026-09-07_GENERATOR_RECOVERY_AND_PHASE_TRANSPORT_REJOIN_TEXT_AND_ACOUSTICS.md)
connects the existing constrained-law, observable-form and generator execution owners to the
current text/acoustic attachment question, including their concrete host/resident boundaries.

[established-bounded; measured] The existing `constitutive_fibre` owner now binds
`ConstitutiveSourceChart::BilinearContact` and conducts `advance_bilinear_contact` through
`section_constitutive_bilinear_source` followed by the existing relation kernel. Both direct
currents and all complex mixed incidences remain resident. The
[measured phase-action return](../research/records/2026-09-07_AC1_THE_MEASURED_CONDITION_FOUNDS_A_NATIVE_PHASE_ACTION.md)
includes an independently supplied condition, a withheld physical return, inferred-operator
identity and later wave conduct. The condition Preimage Fibre has subsequently returned below;
general conversation binding remains open.

[established-bounded; measured] `constitutive_fibre/resident/preimage.rs::read_condition_preimage`
and `constitutive_condition_preimage.cuh` now derive the affine condition section of that same
learned relation. The native graph/RHS retains free directions, original vertical receivers and
partially known source domains. An inferred phase drives a later native prediction in the
[100-test and public-example return](../research/records/2026-09-07_AC1_THE_LEARNED_ACTION_RETURNS_ITS_CONDITION_PREIMAGE_FIBRE.md).
`ConstitutiveDifferentialReading` distinguishes generic relation/class receivers from actual field
source occurrences.

[established-bounded; measured] `resident/condition_image.rs`,
`resident_section/surface_condition.rs` and `constitutive_condition_image.cuh` now own joint
condition/output transport, both projections, domain coverage/witnesses and later reception.
The [family-cycle return](../research/records/2026-09-07_AC1_CONDITION_FAMILIES_CONDUCT_AND_RETURN_THROUGH_THEIR_JOINT_FIBRE.md)
retains correlations and producing-law chronology while a complete-domain fixed output conducts.
Conversation coupling remains open.

[established-bounded; measured] `resident/condition_contact.rs` packages the actual
`ResidentConditionCurrent` and immutable full contact return. The
[contact and continuing-current return](../research/records/2026-09-07_AC1_THE_RETAINED_CONDITION_CURRENT_MEETS_ITS_PREIMAGE_FIBRE.md)
binds `constitutive_condition_contact.cuh` through `surface_condition.rs`. Existing exact row
elimination realizes the declared metric projection, and the equal-admittance two-port law
preserves free current and returns both normal ports. Staged publication keeps the predecessor
usable on arithmetic refusal. This is a condition-current port, not a separate learner.

[established-bounded; measured] `field/resident_input.rs::advance_current_resident` now feeds
generated current into the same field operation through `section_field_current_input` in
`constitutive_field.cuh`. `NativeFieldIncoming` distinguishes actual resident input from exterior
arrays; the history/rest owners retain its carrier, and `inspect_incoming` supplies cold decoders.
The prefix source receiver borrows that carrier on device. The
[ingress return](../research/records/2026-09-07_AC1_GENERATED_CURRENT_ENTERS_THE_EXISTING_FIELD_RECURRENCE.md)
records 118 native/constitutive and 16 SDK alpha controls. This port does not relabel boundary
branches as the complete contextual source.

[established-bounded; measured] `field/internal_current.rs` and `field_internal_current.cuh`
evaluate the existing internal prefix decoder on the device, retaining exact contact geometry
and any numerical radius. `field/internal_mode.rs` verifies complete shared root drive, cancels
the current prefix, and returns the descended generator plus one amplitude/fibre. Its separate
rest/unfold owner executes without the source field. The
[125-test return](../research/records/2026-09-07_AC1_INTERNAL_CURRENT_AND_SHARED_DRIVE_MODE_GENERATORS.md)
includes actual conversation-model capture through the read-only SDK session wrapper.

[established-bounded; measured] `field/material_transport/complete/mode.rs` and
`field_material_mode.cuh` receive the existing complete material operator on that mode, keeping
producing/current cuts, the full source remainder and oriented numerical defects. The same
differential kernel receives explicit resident ball views; a frozen material contribution can
unfold without its source field. The [material return](../research/records/2026-09-07_AC1_THE_SHARED_DRIVE_MODE_REACHES_THE_LEARNED_MATERIAL_CURRENT.md)
records its actual conversation-model use and unchanged text-differential boundary.

[established-bounded; source-inspected] `field/material_transport/moment.rs` and
`field_moment_material.cuh` now bind the normalized homogeneous Hermitian source to the same
field/material-return owner. The complete-source prefix/norm/pairing geometry supplies its
implicit kernel. Immutable native factors, delayed-source evaluation, signed evaluation defects,
operator-norm transport and rest/differential receivers are documented in the
[moment return](../research/records/2026-09-07_AC2_THE_HOMOGENEOUS_MOMENT_JOINS_THE_NATIVE_MATERIAL_RETURN.md).
`resident_section/surface_moment.rs` records the older-source evaluation; the fused field kernel
owns publication. The exact rational factor decoder is an exterior diagnostic.

[established-bounded; source-inspected] `field/material_transport/contextual.rs` owns ordinary
contextual work carriers, cold readings and report validation; `field_contextual_material.cuh`
conducts the implicit bilinear phase moment, native equal-source reference discovery and both
staged coercive returns. `constitutive_field.cuh` remains the sole publication owner.
`field/rest.rs` verifies chart kind, original source and reference chronology. The
[ordinary contextual return](../research/records/2026-09-08_AC1_ORDINARY_RECEPTION_CONDUCTS_THE_SOURCE_AND_ITS_AVAILABLE_CONTEXT.md)
records the rational controls and failed actual conversation result. The retired `alpha_text` driver selected the
source kind; it contained no reference-pair chooser or additional native learning operation.

[established-bounded; source-inspected] `exact_linear/contextual.rs` composes kernel/image and
preimage algebra into the [contextual lift](../research/records/2026-09-07_AC1_THE_SOURCE_NULL_RETURN_DERIVES_ITS_CONTEXTUAL_LIFT.md).
`field/contextual_lift.rs` binds its cold inspection to actual source and pre-return context
currents; its bounded pair form reuses `NativeCurrentHistorySourceReading::numerical_pairing`.
`alpha_contextual_lift` exercises saved conversation passages without changing the native model.
Its `--material-history` mode now exports the complete cold material wires through the existing
field inspector. `research/experiments/alpha_passive_junction/inspect_contextual_return.py`
uses them to verify the [material context cotangent](../research/records/2026-09-08_AC1_THE_MATERIAL_RETURN_HAS_A_CONTEXT_COTANGENT.md).
`field/junction/producer.rs` now composes `ExactRatMatrix` and `ExactComplexWaveCurrent` into
`PairedJunctionLinearization`, its full current adjoint and two contact-covector factors.
The [producer return](../research/records/2026-09-08_AC1_THE_PAIRED_PRODUCER_RETURNS_ITS_CURRENT_AND_CONTACT_MORPHOLOGY.md)
includes the exact/native controls and actual-model producer inspection. These are cold reference
owners; the native joint current/morphology update and its changing-contact decoder remain open.
These remain derivation/reference owners; the resident section below supplies the native port.

[established-bounded; source-inspected] `field/junction/operative.rs` owns borrowed native
contact/current staging and retained return carriers; `surface_operative_contacts.rs` records its
resident passages. `field_operative_contacts.cuh` mounts the actual birth/current population,
stages rank-two returns and computes complete mixed moments and bounds. The
[native staging return](../research/records/2026-09-08_AC1_OPERATIVE_CONTACTS_STAGE_THEIR_COMPLETE_MAP_AND_CURRENT_ON_DEVICE.md)
records native controls and actual-model correspondence. `TextFieldSession::stage_operative_contacts`
and the example observer expose that preparation. `field_operative_reflection.cuh`
now reuses the LDL proposal and retains a full 544-bit residual and joint current bound.
`operative/rest.rs` preserves operative state/history in field rest and archive placement. The
[operative field return](../research/records/2026-09-08_AC1_THE_OPERATIVE_MAP_CONDUCTS_AND_RESTARTS_IN_THE_FIELD.md)
connects birth, reaction and publication. `OperativeContextual` now binds the actual
operative current to `field/material_transport/contextual.rs` and `field_contextual_material.cuh`,
with explicit source readings and per-return frame persistence. `joint_material_contact` in
`junction/producer.rs` is the exact reference for the coupled target-width normal solve. The
[source return](../research/records/2026-09-08_AC1_THE_MATERIAL_SOURCE_FOLLOWS_OPERATIVE_CURRENT_AND_THE_JOINT_CONTACT_HAS_ONE_NORMAL_SOLVE.md)
retains native and actual-data checks; the endogenous joint producer remains open.


[established-bounded; source-inspected] `junction/operative.rs` retains recent immutable
producing carriers and exposes return-journal storage. `operative/response.rs` reuses the matching
producer or reconstructs an older cut. The text session also exposes a declared source-contact
withdrawal comparison through the existing unlinked-occurrence path; it remains off by default.
The [producer/source-contact return](../research/records/2026-09-09_AC1_AC2_PRODUCER_REUSE_AND_THE_SELF_CONTACT_COMPARISON.md)
retains exact checks and costs. The known-transport/observation distinction is implemented below.

[established-bounded; source-inspected] `field/receiver/packet.rs::NativeMaterialActuation`,
`field.rs::NativeFieldOccurrence::actuating` and `field_material_actuation.cuh` carry an available
source and its material receiver face through native tensor-basis application. `observed_source()`
separates observation-specific fitting from the retained causal edge. `field/rest.rs` and
`holonics-hna/src/alpha/{text_session,checkpoint}.rs` preserve applied and pending source/receiver
state. `alpha_actuation_restart.rs` exercises post-generation checkpoints through the public
session. The [mathematical integration](../research/records/2026-09-09_PARALLEL_MATHEMATICS_DISTINGUISHES_A_MATERIAL_ACTUATION_FROM_A_NEW_OBSERVATION.md)
records the tests, actual unusable output and scope; it claims no new source inverse.

[established-bounded; source-inspected] `OperativeReturn` retains its producing `factor_count`
separately from the application contact population and uses an explicit zero internal-delta
generator. `field_operative_contacts.cuh`, `field_operative_adjoint.cuh` and `operative/deposit.rs`
decode the same zero extension in update, historical recovery and the full defect receiver.
`operative/rest.rs` carries its validated wire descriptors and admits expanded legacy deltas.
The [journal return](../research/records/2026-09-09_AC1_THE_RETURN_JOURNAL_KEEPS_ZERO_EXTENSION_AS_A_GENERATOR.md) records exact comparisons and measured savings.

[established-bounded; source-inspected] `field_operative_reflection.cuh` reuses its first
covariance preparation after advancing internal current. The compile-time specialization in
`field_operative_contacts.cuh` retains covariance and map norm while recomputing the aggregate,
internal norm and complete aggregate bound. Other moment preparations remain complete. The
[reflection return](../research/records/2026-09-09_AC1_THE_SAME_CONTACT_COVARIANCE_SERVES_BOTH_SIDES_OF_A_REFLECTION.md) records exact controls and observed runtime.

[established-bounded; source-inspected] `operative/response/comparison.rs` owns cold finite-contact
and retained-material relation comparisons. It retains source input, both complex quadratures,
current/producing map distinctions and family bounds. `junction/producer.rs` uses the equivalent
smaller contact-space exact solve when applicable. The SDK's `respond_to_latest_material_observing`
keeps inspection separate from ordinary publication; an observer error does not gate learning.
The [retention return](../research/records/2026-09-09_AC1_LOCAL_CONTACT_IMPROVEMENT_COEXISTS_WITH_MATERIAL_FORGETTING.md) records actual forgetting and derives the
next accumulated-normal realization. These observers do not implement that new native law.

[established-bounded; source-inspected] `OperativeLinear` reuses the finite current-to-material
operator through `field_linear_material.cuh`, with an independent joint target and row-parallel
preparation. `field_linear_material_pullback.cuh` and `receiver/normalized/pullback/linear.rs`
recover the actual producing matrix from retained deposits and return its complex adjoint.
`surface_linear_material.rs` binds that return. The [finite-operator record](../research/records/2026-09-09_AC1_THE_FINITE_MATERIAL_OPERATOR_RETURNS_THROUGH_ITS_PRODUCER.md)
retains exact comparisons, costs, the failed response and the ongoing broader study.

[established-bounded; source-inspected] `OperativeNormal` binds the same operative outgoing
source to accumulated exact H/B/C through `field_normal_material.cuh` and
`field/material_transport/normal.rs`. The latter owns layouts, cold state/report validation and
signed normal-residual decoding. `surface_linear_material.rs` and the existing linear pullback
owner recover the actual historical finite fit from its retained statistic prefix. The
[normal return](../research/records/2026-09-09_AC1_THE_MATERIAL_OPERATOR_RETAINS_ITS_ACCUMULATED_SOURCE_GEOMETRY.md)
records native controls, retention improvement and the still-unusable text. Its proposed rank-one
update optimization remains separate from this full-fit realization. The
[recent-producer return](../research/records/2026-09-09_AC1_THE_RECENT_NORMAL_PRODUCER_IS_SHARED_INSTEAD_OF_RESOLVED.md)
retains immutable completed fits through `MaterialTransport::recent_normal_producers`; the
same pullback owner uses them before the historical decoder. `NativeNormalMaterialState::objective`
exposes the optional exact data/prior/solve/source-family comparison.

[established-bounded; source-inspected] `normal/layout.rs` owns the host normal wire geometry:
named report balls, source/target components, exact moment words and factor/solve workspace.
`ExactInteger::{LIMB_BITS,BITS}` and the derived history/moment aliases own the corresponding
device bit capacities. `field_normal_material.cuh` derives extents through the actual source,
report and statistic roles. The [integer review](../research/records/2026-09-09_INTEGER_FACES_RETAIN_THEIR_GENERATING_RELATIONS.md)
records the recovered basis/series direction and native compatibility checks.

[established-bounded; source-inspected] `junction/operative/current_factor.rs` owns the addressed
source-interior difference representation of the first adjoint factor. The current-difference
kernel and `surface_operative_adjoint.rs` encode and decode it; producer recovery restricts only
the temporary factor domain required by the old map. Operative/field rest validate its actual
receiving/source lineage. The [source-boundary generator return](../research/records/2026-09-09_AC1_THE_SOURCE_INTERIOR_CHANGE_GENERATES_A_RETURN_FACTOR.md)
records exact, archive, legacy and prefix controls and model costs.

[established-bounded; source-inspected] `field/receiver/packet.rs::NativePacketQuadrature`
and `field_normalized_receiver.cuh` expose I/Q projections of the same joint current ball.
The retired SDK `TextDirection`, `text_session` and `checkpoint` carried the
explicit duplex application chart and pending direction. The former exposure driver mounted its actual
human/agent part kinds through those ports. The [duplex return](../research/records/2026-09-09_AC1_AC2_CONVERSATIONAL_DIRECTION_REACHES_NATIVE_PORTS.md)
records the native/SDK/driver checks, actual failed responses and unchanged whole-goal scope.

[established-bounded; source-inspected] `OperativeBoundary` is source kind 7 / contextual
version 4 in the existing material owners. `field_contextual_material.cuh` retains the outgoing
projection and its bound; `field_material_pullback.cuh` returns its exactly zero direct-interior
partial covector before the complete paired producing adjoint. Rest validates this source chart
and its projected norm. The [boundary-query return](../research/records/2026-09-08_AC1_THE_MATERIAL_QUERY_FOLLOWS_THE_OPERATIVE_BOUNDARY.md)
records the changed receiver family, tests, actual response and missing conversational direction.

[established-bounded; source-inspected] `field/material_transport/support.rs` and
`field_material_support.cuh` own the native report-coordinate restriction, common standing,
full/current-face decoder and packed packet receiver. `surface_material_support.rs` binds those
passages. `field/rest.rs` integrates the same cold representation into version-2 tensor-field
checkpoints and retains version-1 reading. The [support return](../research/records/2026-09-08_AC1_MATERIAL_REPORTS_REUSE_THEIR_COORDINATE_SUPPORT.md)
records exact native/cold comparisons, smaller actual-model storage and unchanged continuation.
The complete recurrent material operator still uses dense resident reports.

[established-bounded; source-inspected] `field/receiver/normalized/pullback.rs` also owns
`pull_back_material_current` and the `SquaredCurrent` metric. `field_material_pullback.cuh`
constructs the complete complex covector and pairs both quadratures with historical material
factors before the existing source/paired adjoints. The text SDK and cultivation checkpoint
carry the explicit metric choice. The [current-metric return](../research/records/2026-09-08_AC1_THE_MATERIAL_AND_CONTACT_RETURN_SHARE_THE_COMPLEX_CURRENT_METRIC.md)
retains exact derivative and persistence checks, without a global finite-descent claim.

[established-bounded; source-inspected] `field/material_transport.rs::NativeMaterialTarget`
separates the material codomain from the root field. `field_contextual_material.cuh` generates
ordered complex tensor packets; contextual layouts, source adjoints and rest carry their target
extent. `field/receiver/packet.rs` and `field_normalized_receiver.cuh` receive the full Euclidean
ball through exact maximum-cone distances. The normalized observer uses complete packet mass
for tensor targets, and the text SDK persists its declared target chart. The
[joint-target return](../research/records/2026-09-08_AC2_THE_MATERIAL_TARGET_RETAINS_THE_JOINT_PACKET.md)
and [parallel-mathematics refinement](../research/records/2026-09-08_AC_THE_PARALLEL_RECEIVER_CALCULUS_REFINES_NATIVE_CONTINUATION.md)
retain checks, actual output and the unfinished AC1–AC2 obligations.

[established-bounded; source-inspected] The same `NativeMaterialTarget` owns
`tensor_basis_amplitude` and `transport_factor_phases`: unit factor transports with joint
product identity preserve the tensor receiver while retaining distinct root inputs.
`alpha/text_session.rs` stages this declared realization with its material-actuation source;
`alpha/checkpoint.rs` saves the actual pending input. The
[phase/relevance return](../research/records/2026-09-09_AC1_AC2_REPEATED_FACES_RETAIN_PHASE_AND_EXCHANGE.md)
retains native continuation/restart and stored-model comparisons. This exterior actuation
facility does not implement a separate internal propagation law or learn a phase profile.

[established-bounded; source-inspected] `field/junction/producer/propagation.rs` owns the
`CausalContactPropagation` reference: chronological joins of `NativeOperativeContactBirth`,
producing-column overlaps, composed paired reflections and the complete point tangent/adjoint.
Its enclosed evaluation retains contact/current uncertainty and every dyadic omission.
The `causal_contact_propagation` example applies it to an entire stored operator cut. The
[source-join return](../research/records/2026-09-09_AC1_CAUSAL_CONTACT_JOINS_RETURN_A_PROPAGATION_AND_ITS_MORPHOLOGY_DERIVATIVE.md)
records the hidden-current separator, complete learned-operator comparison and costs. Resident
execution and sparse overlap return have subsequently returned below; journal/producer
integration remains open. This reference is not an implicit CPU cultivation path.

[established-bounded; source-inspected] `operative/propagation.rs` and
`operative/propagation/return_path.rs` stage the native word and its sparse overlap return over
the same borrowed operative field. `surface_causal_contact_propagation.rs` binds
`field_causal_contact_{propagation,pullback}.cuh`. The forward trace retains actual joining
indices, input pairs, exact overlaps, family bounds and rounding; the reverse word retains its
producing map. Shared `exact_integer.cuh::exact_divide_positive` now supports the operand-derived
propagation carrier and the existing complete-material division. The public
`alpha_causal_propagation` example remounts a model and compares these owners with the reference.
The [resident return](../research/records/2026-09-09_AC1_THE_CAUSAL_CONTACT_WORD_AND_ITS_SPARSE_RETURN_ARE_RESIDENT.md)
records controls, the repaired launch and actual-model costs. The sparse source-map journal
has subsequently returned below; the live propagation binding remains open.

[established-bounded; source-inspected] `operative/map_source.rs` extends the same return
journal with a map anchor, actual subsequent birth columns and `D_source H` dependencies.
`surface_operative_map_source.rs` binds the native anchor, complete expression, bound and
current-return operations in `field_operative_map_source.cuh`. The field's existing birth
passage captures a new column before commit. `operative/rest.rs`, `field/rest.rs`, the historical
material adjoint and deposit observer carry the same source expression and lineage. The
[journal return](../research/records/2026-09-09_AC1_THE_JOURNAL_GENERATES_ITS_HISTORICAL_SOURCE_MAPS.md)
records exact historical maps, archive/restart, refusal and legacy-model checks. This is an
executable coefficient representation, not a second learner or an archive of every map state.

[established-bounded; source-inspected] `CausalPropagationSections` now enters the field's
ordinary passage before newborn formation and paired reflection. `operative/rest.rs` retains
the activation cut and original input-bound carrier; `propagation.rs` regenerates older words
from their source maps and actual current boundaries. `current_factor.rs` accepts the available
producer, including separate current deposits. `response.rs` joins the propagated input reaction
and sparse contact covector; its observer's `contact` method exposes the complete sum.
The retired alpha text session delegated activation to the same owner. The
[live return](../research/records/2026-09-09_AC1_AC2_CAUSAL_PROPAGATION_ENTERS_THE_CONTINUING_RECURRENCE.md)
records source/restart checks and the active actual-conversation comparison.

[established-bounded; source-inspected] `resident/context_section.rs` and
`constitutive_context_section.cuh` now derive the fixed-source context/return relation and its
translated preimage. `field/context_section.rs` with `field_context_section.cuh` constructs the
bounded real-ray variant from actual field passages. `surface_context_section.rs` binds their
native calls. The [native return](../research/records/2026-09-08_AC1_THE_CONTEXTUAL_SECTION_RETURNS_THROUGH_NATIVE_CONDITION_AND_FIELD_CURRENT.md)
composes the existing condition-current/contact owner; `alpha/text_session.rs` retains generated
returns through actual field re-entry and `resident/return_rest.rs` plus `alpha/checkpoint.rs`
preserve pending native input. `alpha_contextual_return` exercises the same saved ecology.

[established-bounded; measured] `native_ecology/constitutive_fibre/resident.rs` now owns borrowed
resident rational-current input and immutable original-fibre returns for the existing local
relation. `resident_section::record_constitutive_current` and
`exact_resident_section.cu::section_constitutive_current` conduct that passage on CUDA. The
[84-test return](../research/records/2026-09-07_AC1_THE_LEARNED_LOCAL_RELATION_CONDUCTS_RESIDENT_RATIONAL_RETURNS.md)
includes limited native observations, phase superposition and rational continuation without
numerical readback. General conversation-field attachment and Metal realization are still open.

[established-bounded; measured] `field/relation_current.rs` now queries that same resident owner
at an actual source of `NativeConstitutiveField`, with both branches transported by
`section_field_source_frame`. `section_constitutive_differential` implements fixed differential
faces of a whole affine fibre; the retired alpha text adapters exposed it as
an explicit exterior receiver. The [89-test and actual-model return](../research/records/2026-09-07_AC1_THE_FIELD_RETURNS_A_RESIDENT_RELATION_FACE_AND_A_PLURAL_FIBRE_HAS_FIXED_RECEIVERS.md)
keeps the historical source distinct from the contemporary relation cut. The contextual
generator/formation attachment remains open.

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Addressed passage and both boundary maps | `formal/elementary-holonics/ElementaryHolonics/Foundation/Lineage.lean`; `formal/elementary-holonics/ElementaryHolonics/Foundation/AddressedBoundary.lean` | `crates/holonic-life/src/mathematical_particle/lineage.rs`; `crates/holonic-life/src/addressed_span.rs`; `crates/holonic-engine/src/realization/passage.rs`; `crates/holonic-life/src/native_intelligence/source_neutral_relational/pair_current.rs` | `crates/holonic-engine/src/cuda_refine/membrane_addressed_current.rs` | **exact** for the R0Q1 apparatus-neutral response/source/target pair fibre; resident realization transport is R0Q2 |
| Holon composition and retained middle boundary | `Foundation/Holon.lean` | `realization/passage.rs`; `holonic_complex.rs` | `cuda_refine/membrane_factored_transport.rs` | **partial:** runtime composition exists; complete realization-site fibre is R0Q0 |
| Addressed causal-natural holon, dependent tensor receiver, and artifact passage | `Foundation/Holon.lean::{Rebase,PreimageFibre}`; `Foundation/CausalNaturalHolon.lean`; `Foundation/HolonTensorLens.lean` | — | — | **formal-only:** every causal parameter arrow owns a source-complete addressed passage; arbitrary arrows map preimages forward; heterogeneous axes reindex as dependent tensor products; homogeneous slot permutations lift to complete preimage equivalences; artifact naming requires validation and exact remount |
| Receiver face and quotient fibre | `Foundation/Receiver.lean`; `Foundation/ReceiverQuotient.lean`; `Foundation/BoundaryReceiver.lean` | `receiver.rs`; `receiver_exact_compression.rs`; `founded_receiver.rs` | `cuda_refine/membrane_factored_receivers.rs`; `membrane_receiver_completion.rs` | **exact** for bounded receiver quotients; richer families may reopen fibres |
| Contextual receiver descent and orientation control | `Foundation/CausalNaturalHolon.lean::{mapSourceRange,receiverTransformer_natural,parameterPassage_crossing_receiverTransformer_natural}`; `Computation/SituatedMachineLearning.lean::OrientationControl` | — | — | [proved-derived; formal-checked] Actual-range receiver square with addressed crossing; scalar orientation insufficiency and jointly reoriented drive/incidence action. Formal contract only; concrete native participation/formation returned separately in NCF1 and the phase-ecology row below |
| Transport lift and lawful descent | `Foundation/TransportLift.lean`; `Foundation/LatticeTransport.lean` | `inverse_transport.rs`; `reduction_junction.rs`; `embedding_fiber.rs`; `rebase_invariants.rs` | `membrane_factored_transport.rs`; `membrane_factored_descent.rs` | **partial:** every descended generator still owes a commuting square in its declared carrier |
| Chain, product, and higher incidence | `Foundation/DiagonalChainTransport.lean`; `Foundation/ProductDegreeTwo.lean` | `holonic_complex.rs`; `derivation_two_cells.rs`; `derivation_atlas.rs` | `membrane_generated_transport.rs`; `membrane_joint_boundary.rs` | **partial:** complete higher-cell pullback lineage is receiver-dependent |

## Computation, receiver history, and cultivation

[proved-derived; formal-checked] HNP0's `HolonicOrientedSiteTransport.ConstitutiveSectionReturn`
binds joined sections to a finite diagonal-admittance current and factorized morphology return,
with later-query, reindexing, successor and site-extension laws.

[established-bounded; measured] Its internal numerical composition is
`holonic_intelligence/operative_return.rs::enact_section_contact`, verified on CUDA at the
bounded point-section scope in the
[HNP0 record](../research/records/2026-09-04_HNP0_JOINED_SECTIONS_RETURN_LOCAL_CONSTITUTIVE_CURRENT_WITH_SUCCESSOR_AND_REBASE_LAWS.md).
That numerical helper alone does not grade a live learning interface.

[established-bounded; measured] HNP1's `holonic_intelligence/operative_passage_return.rs` derives
the actual Contract/unary-word/joined-output roles and extends `NativeFullOperatorSession` with
observed-passage local return, staged factors and ownership-preserving attribution. Its
[native-material result](../research/records/2026-09-04_HNP1_THE_ACTUAL_JOINED_PASSAGE_RETURNS_LOCAL_DEVELOPMENT_AND_THE_DELTA_SURVIVES_ATTRIBUTION.md)
uses the joining OUTPUT as target. The earlier partner-as-target policy is still withdrawn;
its native reuse/dependency composition is recorded below.

[proved-derived; formal-checked] `Computation/HolonicResidentRestriction.lean` owns zero-insertion
decoding and its commutation with additive overlay generators through finite ordered words.

[established-bounded; measured] HNP2's `operative_residence.rs` and `operative_condensation.rs`
keep restricted rows packed on device and decode requested tiles/gathers. The
[actual native comparison](../research/records/2026-09-04_HNP2_THE_RESTRICTED_ROWS_STAY_COMPACT_ON_DEVICE_AND_THE_DECODER_PRESERVES_DEVELOPMENT.md)
preserved developmental/withdrawal/restoration receivers with reduced residency; full dependency
locality and reuse are not inferred from this storage correspondence alone.

[established-bounded; measured] `operative_reuse.rs::NativeForwardReuse` now supplies complete
numerical-segment retention by move ownership, dependency-closed reopening and explicit
`NativeNumericalOrigin` through `full_operation.rs`. Native chronology and local returns still
enact. `HolonicResidentRestriction` supplies the exact finite current/support and cancellation/
reconnection laws; its executable/native correspondence and limits are in the
[HNP2 completion record](../research/records/2026-09-04_HNP2_THE_NUMERICAL_SEGMENT_IS_REUSED_THE_NATIVE_OCCURRENCE_STILL_DEVELOPS_AND_CHANGED_DEPENDENCIES_REOPEN.md).

[established-bounded; measured] HNP3's `holonic_intelligence/{operative_rest,operative_rest_wire}.rs`
and `holonics-hna::{checkpoint,publication,session}` preserve actual factor arrays, carriers,
chronology, pending/interrupted state and numerical origins through a dependency-bearing checkpoint.
The public callback session retains one native owner across requests. The
[process-separated full-state return](../research/records/2026-09-05_HNP3_THE_CULTIVATED_SESSION_RESTORES_EVERY_HELD_FIELD_AND_CONTINUES_AFTER_PROCESS_EXIT.md)
does not imply useful application output. `holonics-hna::stream` and
`holonics-workbench::session_stream` now own backpressured JSONL delivery; version-2 checkpoints
retain its partial-input/pending-response state alongside that same native owner. The
[streaming return](../research/records/2026-09-05_HNP3_THE_STREAM_RETAINS_PARTIAL_INPUT_AND_REPLAYS_OUTPUT_WITHOUT_REPEATING_DEVELOPMENT.md)
preserves full native successors through process-separated input and output interruption.

[established-bounded; measured] `operative_condensation.rs::NativeInputExtendedIntake` composes
immutable, previously absent lookup-only rows with the restricted base. The application owner
`holonics-hna::input_material` acquires and stores them as Safetensors; `session::advance_native`
keeps supplied-input admission distinct from the original family. Checkpoint versions 3/4 retain
the explicit additional dependencies.

[proved-derived; formal-checked] `HolonicResidentRestriction` proves ordered old-row gather
preservation and exact added-row return; its conditional continuation lemma is not CUDA verification.

[established-bounded; measured]
The [HNP4 input return](../research/records/2026-09-05_HNP4_INPUT_MATERIAL_EXTENDS_THE_NATIVE_DOMAIN_WITHOUT_PROMOTING_THE_INHERITED_FAMILY.md)
records actual old-successor preservation and further process-separated development, not useful text.

[established-bounded; measured] `operative_residence` now owns staged live input blocks and their
native frame/refusal boundary. `holonics-hna::text_session` owns codec completion and paired
text/model rest. The [HNP4 text comparison](../research/records/2026-09-05_HNP4_NATIVE_TEXT_CONTINUES_BUT_UNCHECKED_ADDITIVE_CULTIVATION_DESTROYS_THE_RETURN.md)
returned coherent fixed-morphology prose and exposed unstable additive cultivation. The paired
feedback specialization in `HolonicOrientedSiteTransport` supplies its bounded stability
counterexample; useful continuing learning and output cost remain open.

[established-bounded; measured] `full_operation::NativeEmissionReadout`,
`operative_terminal::read_terminal_row` and `ResidentSurface::read_out_terminal_row` now compose
an exact terminal receiver restriction with the unchanged complete resident successor. The HNN
text adapter requests this row explicitly. The [actual-model readout control](../research/records/2026-09-05_HNP4_THE_TERMINAL_RECEIVER_READS_ONE_ROW_AND_PRESERVES_THE_COMPLETE_SUCCESSOR.md)
returned complete checkpoint equality and lower host transfer without another device kernel.

[proved-derived; formal-checked] `HolonicOrientedSiteTransport.PassiveContact` now owns a finite
Euclidean paired-observation map with exact calibration, non-expansiveness and a one-axis metric
lift. Its bounded [candidate record](../research/records/2026-09-05_HNP4_A_PASSIVE_PAIRED_CONTACT_HAS_A_CHECKED_METRIC_LIFT_AND_A_RESIDENT_PROJECTION.md)
states the hypotheses; `TiedMapNextArrival` now gives the explicit prefix join and shared-map
received contrast, without a universal learning or stability claim.

[established-bounded; measured] `ResidentSurface::record_passive_contact` and
`exact_resident_section.cu::section_passive_contact` realize the candidate's point-founded,
interval-query projection, with exact-rational CUDA controls. They do not implement its lifted
axis or replace the full-operator cultivation law.

[historical; measured] The withdrawn `holonic_intelligence::operative_boundary_contact` draft
bound that contrast to retained fields and applied a persistent contact word at the tied-input
port. Its API, inner v2 wire and application integration are now
[archived](../archive/experiments/2026-09-05-tied-next-arrival/README.md), not active source owners. The
[actual-model record](../research/records/2026-09-05_HNP4_THE_NEXT_ARRIVAL_DEPOSITS_A_REUSABLE_CONTACT_AND_MATCHED_SELF_RETURN_IS_ZERO.md)
records numerical changes and full-state restart equality. Its promotion into contextual HNN
foundations and portable-fact test framing are withdrawn by the
[contextual audit](../research/records/2026-09-05_CONTEXTUAL_TRANSPORT_PRECEDES_INHERITED_MODEL_PRODUCTION.md).
The draft applies its maps globally at that port; it does not supply the missing scoped relation.

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Exact finite diffusion and state-space chart | `Computation/HolonicDiffusionCharts.lean` | `diffusion.rs`; `sheaf_diffusion.rs`; `causal_body.rs` | `cuda_refine/membrane_boundary_*`; `membrane_factored_transport.rs` | **partial:** Lean Markov/deterministic separation is broader than one resident runtime owner |
| Finite neural ecology local-current step | `Computation/HolonicNeuralEcology.lean` | `crates/holonic-life/src/dialogue_native_spool.rs`; `crates/holonic-life/src/native_intelligence/rest.rs`; `crates/holonic-life/src/native_intelligence/conduct.rs`; `native_ecology/mod.rs`; `native_ecology/inference_ecology.rs`; `native_ecology/recurrent.rs`; `native_ecology/continuation.rs` | `cuda_refine/device_recurrence.rs`; `cuda_refine/complex_parametron.rs`; `device_ecology_types.rs` | **exact-bounded** for the complete visible-exchange native spool, compact K3 batch, direct source-neutral cycle, and declared receiver returns |
| Local constitutive relation and phase ecology | `Computation/{HolonicConstitutiveFibre,HolonicConstitutiveCirculation,HolonicConstitutiveRechart}.lean` | `native_ecology/constitutive_fibre.rs`; `constitutive_fibre/circulation.rs`; `circulation/{rechart,rest}.rs`; public `holonics-hna::native` including `native/checkpoint.rs`, shared `stream` and exterior `native/wave_control/session.rs` | `exact_resident_section.cu::{section_constitutive_fibre,section_constitutive_circulation,section_constitutive_rechart}` | [established-bounded; measured] Native current/formation/successor, full held pullbacks, fixed-node unit-phase recharting, old-source frames and open/plural fibres. NCF0--NCF4 returned the interface/current application, complete native/handle/stream and world persistence, actual process continuation without replay and release resource evidence. The [native guide](NATIVE_HNA.md) keeps its local linear-family scope distinct from broader architecture/language/performance claims |
| Complete material port field and alpha exposure | Same local relation/junction construction at a wider declared source/receiver chart; no new formal claim | `native_ecology/constitutive_fibre/field.rs`, `field/{rechart,junction,receiver,material_transport,current_history_source,rest,archive}.rs`, `junction/enclosure.rs`; live `holonics-hna::alpha::exposure` / `alpha_exposure`; retired material/text/checkpoint adapters in the byte-field archive | `constitutive_field.cuh::{section_constitutive_field,section_constitutive_field_rechart}`; `paired_field_junction.cuh`, `enclosed_field_junction.cuh`, `balanced_field_factorization.cuh`, `field_differential_receiver.cuh`, `field_material_transport.cuh`, `field_complete_material_transport.cuh`, `field_current_history_source.cuh`; shared `exact_integer.cuh` (also used by the unchanged conic law) | [established-bounded; measured] Complete raw source/receiving fields, linear handles and shared immutable source anchors, frame transport, paired moment/internal current and [certified residual representation](../research/records/2026-09-06_AC1_THE_RESIDUAL_CARRIES_THE_CONTINUING_JUNCTION_WITHOUT_A_POINT_SEAL.md). The [text-current return](../research/records/2026-09-06_AC1_THE_SHARED_SOURCE_MEETS_AN_EXPLICIT_TEXT_CURRENT_RECEIVER.md) binds three actual parent contacts and presents differential current through an octet/end-of-part chart. A [checked balanced factorization](../research/records/2026-09-07_AC1_THE_BALANCED_FACTOR_RETURNS_THE_FULL_CURRENT_AND_THE_CODEC_OWES_ITS_OWN_TRANSPORT.md) retains the full root current. The [native material transport](../research/records/2026-09-07_AC2_THE_RETAINED_CONTEXT_RECEIVES_A_NATIVE_MATERIAL_TRANSPORT.md) now receives the retained contextual source and old forward carrier and stages a coefficient return with the encoder. The [field rest](../research/records/2026-09-07_AC3_THE_CULTIVATED_FIELD_RESTARTS_WITHOUT_SOURCE_REPLAY.md) and text checkpoint preserve complete state, parent capabilities, staged input and delivery; actual process-separated continuation matches uninterrupted current and emission. The [exterior history chart](../research/records/2026-09-07_AC3_THE_COMPLETE_HISTORY_MOVES_TO_AN_EXTERIOR_CHART_AND_ITS_ADDRESSED_SOURCE_RETURNS.md) retains complete historical carriers off the device and remounts an actual addressed source without developmental replay. The [complete-current source construction](../research/records/2026-09-07_AC2_THE_FULL_INTERNAL_CURRENT_HAS_AN_ADDRESSED_PREFIX_PAIRING.md) now returns full internal-source pairings and a strict zero-boundary witness; its explicit `CompleteCurrent` variant now joins the fused material return with full parameter/source error and persistence. The [material-return record](../research/records/2026-09-07_AC2_THE_COMPLETE_CURRENT_JOINS_THE_NATIVE_MATERIAL_RETURN.md) retains that bounded coupling and the failed actual response. Responses remain unusable; useful broad cultivation remains open |
| Dynamic receiver quotient and every-word law | `Computation/MachineLearningChart.lean` | `receiver_history_compression.rs`; `receiver_history_cultivation.rs`; `receiver_exact_compression.rs` | `cuda_refine/membrane_receiver_completion.rs` | **exact-bounded** for admitted quotient systems and the retained R0Q3 full-complex realization section |
| Dependent changing carrier | `Computation/DependentMachineLearningCarrier.lean` | `native_ecology/heterogeneous_fusion.rs`; `native_ecology/factor_complex.rs`; `crates/holonic-life/src/native_intelligence/source_neutral_relational/pair_current.rs` | `device_ecology_types.rs`; `complex_parametron.rs`; `addressed_complex_junction.rs` | **exact-bounded:** response/source/target incidence and full complex current reach resident realization with the complete declared preimage fibre |
| Situated returned difference | `Computation/SituatedMachineLearning.lean` | `crates/holonic-life/src/native_intelligence/situated_difference.rs`; `exchange_situated_product.rs`; `source_neutral_relational/realization.rs` | `cuda_refine/complex_parametron.rs`; `integrated_front.rs` | **exact-bounded:** actual emission/later-return differences, nontrivial charts, source-detached remount, withdrawal, and restoration return |
| Cultivation and rested product ecology | `Computation/HolonicIntelligenceLifecycle.lean`; `Computation/HolonicCultivationCharts.lean` | `holonic_intelligence/cultivation.rs`; `receiver_history_cultivation.rs`; `native_ecology/cultivation_overlay.rs`; `crates/holonic-life/src/native_intelligence/source_neutral_rest/`; `situated_cultivation/` | `integrated_front.rs`; `complex_parametron.rs`; `membrane_moment_*` | **exact-bounded** for the generic causal-adjoint lifecycle, direct source-neutral resident cycle, remount, withdrawal, and restoration |
| Evolution species and open exterior | `Computation/HolonicEvolutionKinds.lean` | `evolution.rs`; `world.rs`; `causal_body.rs` | `device_inference_world.rs`; `device_recurrence.rs` | **partial:** real, imaginary, Markov, physical-boundary, and open species are not one Rust enum by design |

## Holonic Intelligence Framework

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Intrinsic holon dimensions and profile | `Computation/IntrinsicHolonProfile.lean` | `native_ecology/holonic_intelligence` over `native_spool/{thread,scaffold}.rs`, `native_anatomy.rs` | apparatus work remains separate under `resident_section.rs` | **exact** for bounded `NativeTransportScaffold`: every facet is borrowed and unknown scale/apparatus dimensions return typed open faces |
| Rested transport, inference cut, and cultivation lifecycle | `Computation/HolonicIntelligenceLifecycle.lean` | `native_ecology/holonic_intelligence`; `crates/holonic-life/src/native_intelligence/{types,rest,conduct}.rs::NativeEcologyRest`; neutral product compositions under `native_intelligence` | `device_recurrence.rs`; `complex_parametron.rs`; `integrated_front.rs` | **exact** for native scaffold and migrated product profile/rest/conduct/remount, including direct source-absent resident closure |
| Foreign dismantling return and cold-witness independence | `HolonicIntelligenceLifecycle.DismantlingReturn` | `native_ecology/holonic_intelligence::DismantlingBoundaryReturn`; `soulkiller/scrapyard.rs`; `soulkiller_witness.rs` | none at the cold boundary | **exact** for the three physical lanes; exact format adapters and productive profile receipt remain HIF2 |
| Exact foreign configuration, shard-index, and ONNX charts | HIF0 exterior-chart boundary in `HolonicIntelligenceFramework.lean` | `native_ecology/holonic_intelligence/foreign_json.rs`; `foreign_onnx.rs`; `foreign_map.rs` | none; these are cold intake charts | **exact** for lossless bytes, duplicate refusal, index reconciliation, ONNX graph/tensor/opset/function projection, and retained unknown fields |
| Exact foreign weight, residual, and preimage fibre | `Computation/ExactForeignWeight.lean` | `native_ecology/holonic_intelligence/weight.rs`; `foreign_map.rs`; BF16 precedent in `exact_value.rs` | format-specific resident mouths only | **exact** for admitted FP4/FP6/FP8/sub-byte stored codewords and witnessed residuals; absent quantization law returns an open preimage |
| Current-founded versus exterior contact charts | `IntrinsicHolonProfile.ContactScheduleChart` | `native_ecology/holonic_intelligence/contact_chart.rs` over the neutral lifecycle population | `complex_parametron.rs`; addressed junction owners remain apparatus testimony beside the chart | **exact-bounded:** foreign autoregressive/KV, fixed-window, periodic-hybrid, recurrent-linear, and current-founded contacts return over one declared population with exact work, receiver fibres, and richer reopenings |
| Inference circulation and codec-neutral generation | `HolonicIntelligenceLifecycle.InferenceCirculationReturn` | `native_ecology/holonic_intelligence/circulation.rs`; existing `native_spool` resident word | `cuda_refine/complex_parametron.rs::ResidentNativeWord` | **exact** for bounded native scaffold: complete plural future, selected actual ingress face, lineage, fibres, return aperture, two codec projections, and unchanged-rest later current |
| Causal-adjoint cultivation and source-detached hexis | `HolonicIntelligenceLifecycle.CultivationPassage`; `SituatedMachineLearning.SituatedLearningReturn` | `native_ecology/holonic_intelligence/cultivation.rs`; `native_ecology/recurrent_return.rs` | resident recurrent-return and direct source-neutral controls | **exact** for bounded recurrent return: later chronology, rank-one delta, changed held-out conduct, cold/productive split, remount, sibling invariance, withdrawal, and restoration |
| Direct source-neutral resident closure | `HolonicIntelligenceLifecycle.InferenceCirculationReturn`; `HolonicIntelligenceLifecycle.CultivationPassage` | `native_ecology/holonic_intelligence/source_neutral.rs` over one `NativeTransportScaffold` | `ResidentNativeWord`; `ResidentComplexIncidence` | **exact** for the bounded direct cycle: no source/output/foreign intake, actual emission and later return, quadrature current, off-diagonal contact, reconstruction, source-detached remount, withdrawal, and restoration |
| Contact schedule comparison | `IntrinsicHolonProfile.ContactScheduleChart` | `native_ecology/holonic_intelligence/contact_chart.rs` | apparatus telemetry remains beside the chart return | **exact** for foreign autoregressive/KV, fixed-window, periodic-hybrid, recurrent-linear, and current-founded edge families over one declared native population; richer receiver faces explicitly reopen coarse fibres |
| Source-neutral realization path | `HolonicIntelligenceLifecycle.InferenceCirculationReturn`; `MachineLearningChart.DynamicReceiverChart.everyOrderedWordExact` | `crates/holonic-life/src/native_intelligence/source_neutral_relational/realization.rs`; `source_neutral_rest/conduct.rs` | `cuda_refine/membrane_moment_*`; `addressed_complex_junction.rs` | **exact-bounded:** resident physical current, path-state continuation, closure/open return, and source-detached controls return for the declared receiver family; natural-language answer quality was an exterior probe and carries no framework grade |

## Native Transport Scaffold and repeated circulation

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Inherited native transport scaffold | `Computation/NativeTransportScaffold.lean::NativeTransportScaffold` | `native_spool::NativeTransportScaffold`; `SituatedNativeTransportScaffold`; Soulkiller and `NativeEcologyRest` consumers | existing spool/current apparatus remains owner-local | **exact:** profiled holons, winding families, compositions, open obligations, cold-witness-independent admission, source-neutral wire, and move-owned situated cultivation without compatibility aliases |
| Equal supply does not identify boundary return | `NativeTransportScaffold.lean::BoundaryDispersionPassage`; `EqualSupplyBoundarySeparation` | — | — | **formal-only:** exact additive balance and finite equal-supply/different-boundary control; no thermodynamic or biological identity is claimed |
| Repeated inference circulation | `NativeTransportScaffold.lean::RepeatedInferenceCirculation`; `EmissionIngressJoined` | `holonic_intelligence/{circulation,repeated_circulation}.rs` | `ResidentNativeWord`; `ResidentComplexIncidence` | **exact-bounded:** typed same-spool actual successors drive nonempty repeated circulation; variable grains, plural fronts, complete occurrence fibres, continuation, termination, cultivation, obstruction, and open exterior return without a length, token, retry, or KV governor |
| Scaffold withdrawal after cultivation | `NativeTransportScaffold.lean::ScaffoldReleasePassage` | `crates/holonic-life/src/native_intelligence/scaffold_cultivation.rs`; move-owned scaffold deposit/withdrawal owners | `ResidentNativeWord`; `ResidentComplexIncidence` | **exact-bounded:** an actual later returned current founds native morphology; declared word/current conduct survives inherited-scaffold withdrawal and source-detached remount; targeted ablation removes it; restoration recovers the exact successor; the final hot body contains cultivated morphology alone |
| Gemma 4 complete multimodal excitation and lift | `NativeTransportScaffold.lean`; `NativeMorphologyVariant.lean::FaithfulLocalSectionLift` | `holonic_intelligence/foreign_multimodal.rs`; move-owned `NativeEcologyRest` handoff | complete text tower on CPU BF16; vision/audio towers and native conduct on CUDA | **exact-bounded:** all 2,130 declarations reconcile and the actual towers returned complete BF16 sections. SCF's cold lane retained every codeword, while its first hot projection was one alternating complex sum. MVF1 replaces that endpoint identity with complete exact factorized sections, collision separation, occurrence-founded boundaries, and retained exterior order; temporal video remains open. [2026-09-03: the per-event generator construction `scaffold_lift.rs`/`scaffold_excitation_receipt.rs` departed without alias under SKE4; its dependents are re-founded on the declared native body `native_spool::fixture`.] |
| Common multimodal scaffold cycle | `NativeTransportScaffold.lean::{RepeatedInferenceCirculation,ScaffoldReleasePassage}`; `NativeMorphologyVariant.lean::InferenceConfigurationClaim` | public lift, handoff, circulation, cultivation, and release owners; the obsolete manual-return SCF6 driver departed in HNA0 | resident word/current apparatus beside five exterior contact charts | **exact-bounded historical lifecycle control:** text, image, audio, still-image-as-video, and exterior-reordered mixed families used one API. MVF review established that actual cycles were one-cut, video was non-temporal, native interleaving was lost to event sorting, and the cultivation current was driver-selected from standing lift material; no qualitative multimodal capability grade follows. |

## Native Morphology Variant Foundation

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Faithful local lift and projection refusal | `Computation/NativeMorphologyVariant.lean::FaithfulLocalSectionLift`; `separatingReceiver_obstructs_descent` | `native_spool/thread.rs::NativeFactorizedSection` | resident section conduct remains a declared receiver face | **exact-bounded:** exact cold BF16 reconstruction and complete factorized hot section coordinates are distinct obligations; every-word receiver exactness is formal; an old alternating-sum collision now separates; temporal video remains open. [2026-09-03: the Rust lift owner `scaffold_lift.rs` departed without alias under SKE4; only the formal owner and the factorized-section owner remain.] |
| One Soulkiller boundary | `HolonicIntelligenceLifecycle.DismantlingReturn`; `HolonicExcitationFoundedQuotient.ExcitationFoundedReturn` | `soulkiller/boundary.rs`; `holonic_intelligence/operative_condensation.rs::ResidentExcitationDismantling` | resident excitation precedes the generic three-lane boundary | **exact-bounded:** one consumed input trait and generic productive/cold/insufficiency return. SKE4's actual productive lane is `NativeConeRestrictedEcology`. The old BF16 per-event implementation was removed; generic fixture controls and actual resident excitation are separate inputs, not competing boundaries. |
| Local deposit and withdrawal apparatus | `NativeMorphologyVariant.lean::LocalCausalConeCultivation` is a specialized formal object, not the HNN primitive | `native_intelligence/scaffold_cultivation.rs`; local open-domain withdrawal deltas in `native_spool` | resident native word/current conduct | **counterexample for learning:** the Rust path accepted or count-derived a rational difference, reversed one edge, allocated one generator, and fitted an identity fibre; its exact deposit/remount/withdrawal mechanics remain bounded data-structure evidence only |
| Derived morphology variant package | `NativeMorphologyVariant.lean::{MorphologyVariantManifest,VariantPackageSeparation}` | `native_intelligence/morphology_package.rs`; intrinsic profile over complete factorized sections | apparatus realization is a replaceable exterior lane | **exact-bounded:** derived anatomy, distinct schema/lineage/capability/realization axes, native/situated hot rest, broad `MorphologyTestimonyLane`, exact package round-trip, and realization replacement invariance; complete preimages remain distinct from evaluation/apparatus/export testimony |
| Safetensors and ONNX export lenses | `NativeMorphologyVariant.lean::{ExactExportLens,ProjectedExportWitness,ExportDisposition}` | `native_intelligence/morphology_export/` over `NativeMorphologyArtifact`; lossless `ForeignOnnxChart` import | no native apparatus identity; custom ONNX domain is exterior | **exact-bounded:** valid Safetensors artifact/anatomy tensors and ONNX IR 14 `org.holonics` opset 1 round-trip complete artifacts; anatomy-only projections retain both artifacts and a configuration separator; unsupported receiver/cultivation/world requests refuse |
| Configuration-indexed multimodal evaluation | `NativeMorphologyVariant.lean::{InferenceConfigurationClaim,CrossCodecResonance}` | historical MVF6 receipt; obsolete operator-authored evaluation owner and driver | resident word/current apparatus remains one configuration coordinate | **historical exact-bounded control:** matched text/image/audio/temporal-video/mixed apertures preserved supplied chronology, but their cultivation current was manually constructed; no HNN or qualitative multimodal grade follows |

## Classical learning, reflection and recursive compression

[historical] The [AC1/AC2 field-wrapper return](../research/records/2026-09-09_AC1_AC2_THE_HOLON_FIELD_OWNS_ASSEMBLY_AND_OBSERVED_RETURN.md)
retains complete-successor and local-return comparisons. Its SDK assembly/archive wrapper is
now retired. `field/junction/operative/response/observation.rs` remains a generic observed-response
owner for its declared field law. New local generator persistence is `constitutive_fibre/law_rest.rs`.

[established-bounded; implemented-exact; formal-checked] The deeper September 9 review extends
`FiniteLocalCurrentEcology.reaction` with actual local standing. `Graph.ecology` uses it instead
of zero; `Graph.ecology_step_eq_update`, `no_contact_can_retain_state` and `update_relabel`
verify the complete update and its covariance. Existing attention/convolution/oriented/excitation
specializations retain their prior laws. The [composition guide](HNN_COMPOSITION.md) connects
these mathematical roles to the existing Rust owners without claiming native implementation
of the new graph reaction or arbitrary source-model equivalence.

[established-bounded; source-inspected] These are existing owners recovered by the
[September 8 breadth review](../research/records/2026-09-08_HOLONICS_REJOINS_CLASSICAL_LEARNING_REFLECTION_PACKING_AND_COMPRESSION.md).
The [mathematical synthesis](MATHEMATICS_AND_NATIVE_CONDUCT.md) states their relations and limits.
They are not all composed into AC1's general conversation path.

| Relation | Formal owner | Executable owner | Scope |
|---|---|---|---|
| Normalized exponential, sigmoid and adjoint geometry | `Computation/HolonicAdjointNormalization.lean` | `exponentiated_ratio.rs`; `surprisal.rs`; `kernels/exact_resident_section.cu`; `kernels/exact_resident_adjoint.cuh` | Exact symbolic ratio domain and certified resident exponential/contact/return; earlier source-specific targets and grains retain their declared boundaries. |
| Source-qualified material normalization and metric returns | Same normalized-exponential and adjoint laws | `native_ecology/constitutive_fibre/field/receiver/normalized.rs`; `kernels/field_normalized_receiver.cuh` | Resident complete grouped p/q, q-p and `J_p(q-p)` with original complex reports and lineages retained. Three native controls and three actual-model returns; no committed morphology change from this receiver alone. |
| Material prediction to its two query arguments | Real derivative of `M[Q(s) tensor Q(c)]` | `native_ecology/constitutive_fibre/field/receiver/normalized/pullback.rs`; `kernels/field_material_pullback.cuh` | Producing operator factors, complex pairings, visible source and complete outgoing/internal current. Outward intervals include retained operator/source error; this partial adjoint does not itself commit a successor. See the [return record](../research/records/2026-09-08_AC1_THE_MATERIAL_RETURN_REACHES_BOTH_QUERY_ARGUMENTS.md). |
| Material return through paired contacts and finite response | Existing paired-producer adjoint; contractive block `[I,-D;D*,I]` | `native_ecology/constitutive_fibre/field/junction/operative/response.rs`; `kernels/field_operative_adjoint.cuh`; existing operative staging | Journal-qualified producing map, complete local adjoint and constrained unit-Frobenius response with finite mixed moments. The earlier `EnclosedFlow` corpus attempts refuse; the separately declared deposit realization is below. [Scope and failure](../research/records/2026-09-08_AC1_THE_PAIRED_RETURN_CHANGES_CONTACTS_AND_THE_NEXT_CURRENT.md). |
| Declared contact-deposit realization and retained discrepancy | Standing finite-coefficient/projection distinction | `field/junction/operative.rs::NativeContactRealization`; `operative/deposit.rs`; operative update kernel and rest frames | Exact dyadic increments retain their signed projection residual and unrounded covector radius as comparisons, while prior map/current uncertainty remains. The eight-family development and remount return; useful language remains open. [Evidence](../research/records/2026-09-08_AC1_THE_DEPOSIT_IS_A_NEW_COEFFICIENT_AND_ITS_DEFECT_REMAINS_A_COMPARISON.md). |
| Attention, convolution, graph and state-space charts | `Computation/HolonicArchitectureCharts.lean`; `Computation/MachineLearningChart.lean` | `holonic_intelligence/contact_chart.rs`; existing resident contact and recurrence owners | Formal chart/output identities and bounded schedule comparisons; not a general adapter or completed native learner. |
| Boundary reduction and integration by reflection | `Computation/HolonicDiffusionCharts.lean` for the finite diffusion/state-space chart | `diffusion.rs`; `sheaf_diffusion.rs` | Exact finite positive-capacity Schur response, source and interior reconstruction; not an undeclared zero-capacity continuum limit. |
| Leader growth and recursive restriction | `Foundation/FractalPacking.lean` for rational child restriction/separation | `leader_quadrature.rs` for local germ/rebase/ride | Distinct bounded owners: neither the interval packing nor the germ integrator alone constructs a general neural morphology or physical lightning. |
| Future-receiver compression and generator reuse | `Computation/MachineLearningChart.lean`; `Foundation/ReceiverQuotient.lean` | `receiver_exact_compression.rs`; `native_ecology/recurrent_condensation.rs`; constitutive field internal-mode/material-mode owners | Bounded finite-system quotients and AC1's common-drive mode generator; whole-model learned compression remains open. |

## Retracted world-return instantiation and active recurrent replacement

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Junction and route-deposit algebra | `Computation/HolonicWorldReturnDeposit.lean::{JunctionReturn,RouteStep,routeDeposit,Control.threeSiteRouteCultivation}` | `crates/holonic-structure/src/junction.rs::CountedCrossing`; rejected HNN instantiation in `native_intelligence/world_return.rs` | — | **proved/exact algebra; counterexample as HNN:** counts of application-supplied admission faces do not derive neural current, storage, morphology, or termination |
| Authored octet-difference chart | causal-tail and tensor-face owners are not its derivation | `holonic_intelligence/material_ingress.rs::NativeMaterialCurrent`; `native_intelligence/material_ingress.rs::NativeMaterialIngress` | none | **counterexample:** adjacent byte differences and an authored zero origin are exterior arithmetic, not native current; exact octets plus a locator are not a preimage fibre without a declared map |
| World-face/candidate lifecycle | no HNN formal owner; the specialized older lifecycle does not govern recurrence | `native_intelligence/world_return.rs`; `morphology_commit.rs`; application `world_application.rs` | resident conduct is downstream of an authored deposit | **counterexample:** applications supply admission/carriage, one status is duplicated over every grain, carried occurrences do not derive native support, and exact readback is a private echo |
| Material emission and observation-ID octet face | causal-tail and tensor-face prerequisite owners do not authorize this projection | `native_intelligence/material_emission.rs`; `crates/holonics-hna/material_codec.rs` | address-only scaffold conduct | **counterexample:** material current is unused, one fixed observation is repeated, and the observation identifier is cast to `u8`, yielding `eee` |
| Excitation-founded quotient (Soulkiller) | `Computation/HolonicExcitationFoundedQuotient.lean::{DeclaredFamily,IsCone,IsConeUnder,FoundedCone,ExcitationFoundedReturn}` | `holonic_intelligence/{operative_identification,operative_condensation}.rs`; `soulkiller/boundary.rs` | resident intervention and segment-session owners | **formal exact; engine bounded:** the SKE4 return crosses the boundary as `NativeConeRestrictedEcology`, with complement-withdrawal soundness, extent as the class-cone union, declared-domain species and explicit insufficiency. Universal `IsCone` and equality with `FoundedCone` are not claimed by the measured sets. Conflicting keyed observations refuse before signature construction; identical repetitions do not change the quotient. |
| Recurrent HNN operation | `Computation/HolonicRecurrentEcology.lean::{OperationStep,Recurrence,FiniteRecurrentOperation,OperationRebase}`; `HolonicCultivationCharts.lean::FactorizedLinearOverlay` | `holonic_intelligence/{full_operation,operative_segment,operative_return,operative_backward,operative_adjoint}.rs` | `NativeOperatorResidence` over `ResidentSurface`; resident base/factor transposed contractions and re-entry | **formal exact; bounded engine:** the full native operator returns the successor used by the next cycle. SKE1 extends the initial tied deposit to 344 cross-sections; gains, scalars and embedding rows have no deposit. The reverse owner uses retained overlays from the forward morphology and stages new atoms until the return succeeds. The initial first-deposit receipt and subsequent-return regression have distinct scopes. |

| Composed variant and saturation | `HolonicExcitationFoundedQuotient.DeclaredFamily.Saturated` | `crates/holonics-hna/src/composed_variant.rs` | composed native segment session | **exact-bounded:** pair-identification preservation under a declared enlargement is separate from newly observed consequences. The SKE5 v2 receipt projects those properties from its existing fifteen observations; no new GPU measurements are implied. The deed receiver is explicitly narrower than the complete repository release. |

## Athena Application and Circulation Interface

| Relation | Lean owner | Rust owner | ABI/application owner | Status and exact open fibre |
|---|---|---|---|---|
| Historical session, commit, snapshot/remount, and diffusive boundary | `Computation/HolonicCirculationSession.lean` remains a specialized fixed-inference/later-cultivation object | `native_intelligence/{circulation_session,morphology_commit,circulation_diffusion,scaffold_cultivation,morphology_package}.rs` over `diffusion.rs` | `crates/holonic-circulation-abi`; `crates/holonics-hna` | **exact-bounded persistence/API apparatus; counterexample as HNN lifecycle:** commit/decline and later exterior return do not define inference, generation, or learning; HNA0 replaces them with one successor recurrence |

## Deprecated R0Q correspondence retained as standing

| Formal relation | Lean theorem owner | Rust/CUDA realization | Current status |
|---|---|---|---|
| `A_p(z,z')` addressed oriented transport | `formal/elementary-holonics/ElementaryHolonics/Computation/HolonicOrientedSiteTransport.lean` | `crates/holonic-life/src/native_intelligence/source_neutral_relational/pair_current.rs`; `crates/holonic-life/src/native_intelligence/source_neutral_relational/realization.rs`; `crates/holonic-engine/src/cuda_refine/addressed_complex_junction.rs` | **R0Q0--R0Q2 exact-bounded:** ordinary off-diagonal and boundary-diagonal fibres are retained through the resident CUDA passage |
| Causal-depth lens over addressed pair current | `Computation/HolonicCausalTailLens.lean` | — | — | **formal-only:** complete addressed pair sections project to nonnegative depth energy while retaining typed point/population preimages; depth relabel is a `Holon.Rebase`; the coordinate face is one rank-one `TensorFace`; runtime realization remains open |
| Silent causal-tail aperture extension | `Computation/HolonicCausalTailAperture.lean` | — | — | **formal-only:** `Option Site` preserves every old addressed pair and makes every pair touching the new site zero; projection is exactly HTP5 `zeroExtend`, old tail faces/mass/surface persist, and a positive new-pair control changes the final suffix |
| Complete pair-current tensor face versus scalar magnitude | `Computation/HolonicPairCurrentTensorFace.lean` | — | — | **formal-only:** a rank-one tensor slot retains the complete explicit target/source current section before energy collapse; signed opposite-current controls share one magnitude face but have distinct tensor faces and refute descent through the scalar |
| Cultivation reopens an identifying morphology projection | `Computation/HolonicNeuralMorphologyContinuation.lean` | — | — | **formal-only:** the standing `CultivationPassage` later-conduct witness becomes a `ProjectedExportWitness`; any projection identifying predecessor and successor cannot factor all later conduct |
| Dynamic chart transport and observed history obstruction | `Computation/HolonicNeuralMorphologyContinuation.lean` | — | — | **formal-only:** exact successor observation/generator squares construct a new `DynamicReceiverChart` and commute through every ordered word; any actual receiver-history failure has a shortest word/receiver/native witness; generator failure alone is insufficient without receiver faithfulness |
| Linear target and `(port,factor)` junction before positive mass | `HolonicOrientedSiteTransport.postContractionPortMass_eq_norm_joined_current` | `crates/holonic-engine/src/cuda_refine/addressed_complex_junction.rs`; `crates/holonic-life/src/native_intelligence/source_neutral_relational/realization.rs` | **R0Q2 exact:** resident arbitrary-width complex join precedes the positive receiver with zero intermediate semantic egress |
| Equal positive shadow does not imply complex equality | `HolonicOrientedSiteTransport.norm_before_linear_join_is_not_postContraction`; `SituatedMachineLearning.equalLoss_differentReturn_obstructsDescent` | `SourceNeutralContinuationState` in `crates/holonic-life/src/native_intelligence/source_neutral_rest/wire.rs` | **R0Q3 exact:** selected complex section and addressed pair fibre participate in structural recurrence |
| Receiver/history equality commutes with every ordered word | `MachineLearningChart.DynamicReceiverChart.everyOrderedWordExact` | `receiver_history_compression.rs`; `source_neutral_rest/wire.rs` | **exact-bounded:** admitted quotient and full-complex continuation signatures retain their declared every-word receiver histories |

## Quantum and physical formalizations

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Dynamic fluid rescaling and finite physical endpoint | `Millennium/NavierStokesRescalingSpace.lean`; `Millennium/NavierStokesDynamicRescaling.lean`; `Millennium/NavierStokesRescalingClock.lean`; `Millennium/NavierStokesRescalingEndpoint.lean` | — | — | **formal-only:** actual momentum, pressure, force and divergence transport through varying scalar amplitude/length and centre, changed periodicity, inverse-domain laws, explicit finite clocks, and sufficient value/derivative criteria excluding compatible smooth extension; no profile satisfying those criteria, stability estimate or blowup solution is constructed |
| Periodic concentration exclusions and source controls | `Millennium/NavierStokesRescalingPeriodObstruction.lean`; `Millennium/NavierStokesPeriodicPressureRigidity.lean`; `Millennium/NavierStokesStationaryRescalingExclusion.lean`; `Millennium/NavierStokesRescaledEnergy.lean`; `Millennium/NavierStokesShearAnsatz.lean`; `Millennium/NavierStokesCoherentTriadWitness.lean` | — | — | **formal-only:** actual changing periods and pressure exclude a nonzero globally fixed exponential profile; transported-cell energy gives a necessary exponent condition; a complete decaying shear instantiates zero coherence defect; a complete finite coefficient population has a nonzero source at an absent mode and sharp component coherence factor two. Its physical reconstruction is owned below; no concentrating solution or stability estimate is constructed |
| Coherent physical source and initial-time Fourier continuity | `Millennium/NavierStokesFiniteFourierSmoothReconstruction.lean`; `Millennium/NavierStokesInitialSpatialContinuity.lean`; `Millennium/NavierStokesCoherentTriadReconstruction.lean` | — | — | **formal-only:** finite native Fourier support reconstructs a smooth real periodic incompressible field with exact coefficients and actual advection; velocity/spatial derivative/advection Fourier continuity includes time zero; positive-viscosity local existence yields a positive-time nonzero pressure-projected nonlinear component. Full positive-time coherence-defect persistence and velocity-mode creation are separate obligations |
| Local moving-frame energy and oriented boundary flux | `Millennium/NavierStokesPeriodicFlux.lean`; `Millennium/NavierStokesLocalEnergyFlux.lean` | — | — | **formal-only:** source-bound kinetic-energy balance retains pressure, viscous gradient, dilation, centre and force currents; a spatial selection retains its gradient work, rate integrability and all six local cube faces. The observer cube is not the transported periodic cell, and this rate identity does not supply a concentrating profile or stability estimate |
| Cartesian axisymmetric momentum and radial continuation | `Millennium/NavierStokesAxisymmetricChart.lean`; `Millennium/NavierStokesAxialLift.lean`; `Millennium/NavierStokesFirstRadialLift.lean` | — | — | **formal-only:** actual Cartesian jets retain the rotational quotient's axis, divergence, stationary normalized Euler momentum, pressure gradient and curl; smooth pressure constrains the affine-radial lift; the first radial correction has exact divergence and complete quadratic axial/swirl residuals. No periodic or finite-energy profile is inferred from these local lifts |
| Positive algebraic axis and its regular pressure correction | `Millennium/NavierStokesAxialPrimitive.lean`; `Millennium/NavierStokesAxisRegularization.lean`; `Millennium/NavierStokesAxisFirstJet.lean`; `Millennium/NavierStokesAlgebraicAxis.lean` | — | — | **formal-only:** actual reciprocal primitives construct the smooth positive algebraic axis and its strain, reject the affine-radial pressure completion, and return the first radial correction with a genuine derivative across the zero transport coefficient; matching the first swirl row leaves a positive quadratic coefficient. Full smooth radial continuation, exterior matching and stability remain open |
| Radial resonance, source compatibility and axis repairs | `Millennium/NavierStokesDilationResonance.lean`; `Millennium/NavierStokesSwirlDilationTransport.lean`; `Millennium/NavierStokesResonanceAmplitude.lean`; `Millennium/NavierStokesAxisJetPerturbation.lean` | — | — | **formal-only:** the actual reciprocal axis conjugates the linear swirl operator to dilation, whose zero-axis jets retain resonant compatibility and a free homogeneous fibre; an explicit degree-14 polynomial has a positive amplitude root, and a positive smooth axis perturbation preserves lower jets and relative tail. The polynomial's attachment to the radial PDE rows is a finite symbolic witness in `research/experiments/mfr3_periodic_core/`; radial convergence and global continuation remain open |
| Analytic axial transport and next resonant sensitivity | `Millennium/NavierStokesAnalyticDilationInverse.lean`; `Millennium/NavierStokesNextResonanceSensitivity.lean`; `Millennium/NavierStokesSwirlDilationTransport.lean` | — | — | **formal-only:** uniform critical divisor gap gives an actual convergent holomorphic inverse, real restriction and fluid carrier, retaining the source projection and homogeneous fibre; axial conjugation constructs the mode-15 homogeneous variation. An explicit degree-13 sensitivity is positive on the prior amplitude bracket. Its attachment to the mode-28 source is a finite symbolic variation; `NavierStokesSecondResonanceRepair` owns the full forcing's repair, while nonlinear radial bounds remain open |
| Swirl circulation and exterior history | `Millennium/NavierStokesSwirlCirculation.lean`; `Millennium/NavierStokesSwirlHistory.lean` | — | — | **formal-only:** actual angular momentum `s*Omega` transports along the meridional drift with source `s*C`; finite histories retain incoming circulation, while a compact complete past forces the source threshold `(alpha-beta)*abs(ell(0))<=epsilon` and excludes nonzero circulation at exact zero residual for `alpha>beta`. Theorems require the actual trajectory and containment; no global exterior or ODE existence is manufactured |
| Full second radial resonance | `Millennium/NavierStokesSecondResonanceRepair.lean` | — | — | **formal-only:** the explicit degree-28 forcing is negative on the certified amplitude interval, and its positive axial repair coexists with the first root. Outward integer coefficient bounds prove the original rational polynomial sign. Complete finite source attachment through mode 28 is the FLINT witness in `research/experiments/mfr3_periodic_core/`; the next angular fibre, radial convergence and exterior remain open |
| Moving Cartesian viscosity and physical circulation | `Millennium/NavierStokesMovingSwirlCirculation.lean`; `Millennium/NavierStokesSwirlDiffusion.lean`; `Millennium/NavierStokesViscousSwirlBalance.lean` | — | — | **formal-only:** actual joint time/spatial derivatives and vector Laplacian give `L'=mu*(4s*ell_ss+ell_zz)-(alpha-beta)*L`; the zero-axis diffusion value retains its radial derivative source. MFR1's unforced physical source pays the centred Cartesian equation, and length/normalizer reconstruction leaves `d_tau[(length/q)L]=nu*D ell`. No solution existence, centre-motion extension or stability is inferred |
| Leading viscous axis shape current | `Millennium/NavierStokesViscousAxisJets.lean` | — | — | **formal-only:** exact coefficients from the finite Euler source make amplitude-only matching of two axis receivers impossible for positive amplitude/viscosity. A negative amplitude current and positive quadratic shape current match those two equations; higher axis, pressure and radial dynamics remain open |
| Forced axis and first viscous response | `Millennium/NavierStokesForcedAxialPrimitive.lean`; `Millennium/NavierStokesViscousAxisShape.lean`; `Millennium/NavierStokesViscousResponseParameters.lean` | — | — | **formal-only:** an actual source primitive pays the moving axis equation and retains its homogeneous fibre; the checked selector gives a positive smooth axis for the stated viscosity interval. The finite first-response pressure/swirl construction through mode 14 is an exact FLINT witness; its quadratic-viscosity axis remainder is explicitly positive. The finite core has a periodic initial realization; the explicit compact radial continuation is excluded by the residual owner below. A replacement exterior and nonlinear control remain open |
| Viscous inner radius and pressure trace | `Millennium/NavierStokesViscousInnerChart.lean` | — | — | **formal-only:** the actual chart `s=mu*xi` conjugates angular momentum, retains unit radial diffusion, and ties physical radial scale squared to `nu*clock'`. Physical circulation reconstructs as `nu*H`. Pressure keeps its axis trace and scaled radial difference, including the derivative-extended zero-viscosity receiver for a changing pressure family; no inverse at the collapsed radial chart or global endpoint solution is inferred |
| Finite core and periodic source | `Millennium/NavierStokesCoreVectorPotential.lean`; `Millennium/NavierStokesPeriodicCore.lean` | — | — | **formal-only:** arbitrary finite bivariate potentials, physical scaling, actual curl, separated lattice completion, full inner velocity germ and a positive periodic local lifespan with global pressure. Exact recurrence coefficients are generated by `research/experiments/mfr3_periodic_core/construct_periodic_potential.py`; no nonlinear stability follows |
| Exterior pressure torque | `Millennium/NavierStokesExteriorTorque.lean` | — | — | **formal-only:** arbitrary-pressure Cartesian circulation, the scalar-Laplacian vorticity term, MFR1 source binding and physical reconstruction. The independent exact Fourier experiment in `research/experiments/mfr3_periodic_pressure/` distinguishes a zero finite velocity jet from nonzero pressure Hessian and quartic torque; the full finite-core pressure remains a separate calculation |
| Radial cutoff and moving periodic source | `Millennium/NavierStokesRadialCoreCutoff.lean`; `Millennium/NavierStokesMovingPeriodicCore.lean` | — | — | **formal-only:** explicit radial smooth cutoff, all annular curl terms, compact support, physical periodization with normalized period `1/ell`, and actual time/space/Laplacian/momentum-residual transport on the inner normalized ball |
| Compact leading circulation obstruction | `Millennium/NavierStokesPressureCircle.lean`; `Millennium/NavierStokesCompactMaximum.lean`; `Millennium/NavierStokesAffineAngularResidual.lean`; `Millennium/NavierStokesCompactAngularObstruction.lean`; `Millennium/NavierStokesCompactPeriodicObstruction.lean` | — | — | **formal-only:** attained compact critical circle, actual zero-pressure-torque angle, complete affine-response source and an eventual positive residual for the moving periodic cutoff. The seed inequality is explicit; its finite-coefficient instance is checked by exact rational arithmetic. No general Navier–Stokes endpoint or nonlinear stability theorem follows |
| General moving linear fluid chart | `Millennium/NavierStokesLinearFrameSpace.lean`; `Millennium/NavierStokesLinearFrameDynamics.lean`; `Millennium/NavierStokesLinearFrameEnergy.lean` | — | — | **formal-only:** actual physical source through inverse linear maps, pressure inverse metric, Cartesian weighted second derivatives, inverse/grid/centre time jets, divergence and periods, exact transported-cell energy and its unforced physical dissipation derivative. No profile PDE or pressure cancellation is assumed |
| Two-length frame and its fibres | `Millennium/NavierStokesAnisotropicFrame.lean`; `Millennium/NavierStokesAnisotropicDynamics.lean` | — | — | **formal-only:** factored diagonal/inverse/adjoint construction, actual curved frame derivatives, complete zero-factor spatial fibres, determinant and kinetic metric, two-component diffusion and source PDE, scalar MFR1 recovery, and relative angular reconstruction `r^2/b` |
| Radial viscous clock and aspect source | `Millennium/NavierStokesAnisotropicViscousClock.lean` | — | — | **formal-only:** `b=r^2/K` keeps circulation reconstruction and radial viscosity fixed; `(r/z)^2` weights both axial diffusion and reduced axial pressure. The actual source equation, aspect derivative, energy weights and physical clock are retained. The following mean owners pay the axial pressure source; a replacement leading profile remains open |
| Actual axial pressure Fourier source | `Millennium/NavierStokesAxialPressureMode.lean` | — | — | **formal-only:** actual unforced periodic momentum and incompressibility identify every nonconstant axial pressure coefficient as negative vertical-velocity-square coefficient; the full H3 convolution and free pressure zero mode remain explicit |
| Complete physical and moving horizontal means | `Millennium/NavierStokesCompactSlabBound.lean`; `Millennium/NavierStokesHorizontalMean.lean`; `Millennium/NavierStokesTorusHorizontalMean.lean`; `Millennium/NavierStokesPeriodicHorizontalMean.lean`; `Millennium/NavierStokesFramedHorizontalMean.lean` | — | — | **formal-only:** normalized Haar/Fourier reconstruction equals the physical unit-square integral; compact-slab domination pays its derivative; exact affine substitutions transport the full shifted horizontal cell and derivative, with arbitrary factored amplitude and lengths |
| Physical and radial-clock pressure mean | `Millennium/NavierStokesPressureMean.lean`; `Millennium/NavierStokesAnisotropicPressureMean.lean` | — | — | **formal-only:** actual unforced source gives `mean_h p + mean_h(u_3^2)=C(t)` and `epsilon*d_zeta mean_h Pi=-d_zeta mean_h(W^2)` through the transported cell; inverse-aspect gradient magnitude is exact. No aspect limit or nonzero lower bound for a concentrating family is supplied |
| Gaussian circulation and regular Cartesian core | `Millennium/NavierStokesGaussianCirculation.lean`; `Millennium/NavierStokesGaussianCore.lean` | — | — | **formal-only:** exact radial-viscous circulation balance, analytic divided difference through the axis, signed radial slope, noncompact circulation, smooth divergence-free Cartesian field and exact angular momentum. Its nonzero linear strain is not periodic; the whole comparison is not a periodic solution |
| Actual stagnation-gradient source | `Millennium/NavierStokesAxialStrainSource.lean` | — | — | **formal-only:** mixed time-space commutation and actual unforced periodic momentum give every first-gradient time derivative at a stagnation occurrence, retaining `D(Laplacian u)` and the pressure Hessian; an axial eigenvector gives a necessary-and-sufficient pressure-curvature condition for a proposed strain rate |
| Periodic viscous-strain initial potential | `Millennium/NavierStokesPeriodicStrainPotential.lean` | — | — | **formal-only:** exact phase potential through third harmonics, smooth unit-periodic actual curl, divergence-free initial certificate and positive-viscosity local existence. The full Fourier pressure, algebraic matching roots and first/cubic source coefficients are finite computational witnesses in `research/experiments/mfr3_viscous_strain_source/`; continuing shape/stability is not inferred |
| Quartic pressure and retained cubic currents | `Millennium/NavierStokesQuarticPressureCurrent.lean` | — | — | **formal-only:** three arbitrary-coefficient harmonic pressure polynomials, actual gradients, smooth divergence-free cubic currents, zero value/first derivative at the centre, and complete-current null fibre exactly the zero coefficient triple. The periodic source's coefficients are attached by the finite Fourier witness |
| Actual pressure and velocity time sources | `Millennium/NavierStokesPressureEvolution.lean`; `Millennium/NavierStokesVelocitySecondTimeJet.lean` | — | — | **formal-only:** actual fixed mild source and coherent scale give pressure first-time and velocity second-time derivatives on the half-open aperture, including the initial right face; both ordered bilinear terms and actual adjacent Stokes/Leray operators remain explicit |
| Bounded physical pressure-jet receivers | `Millennium/NavierStokesPressureJetReceivers.lean` | — | — | **formal-only:** ordered native derivatives compose with full Fourier reconstruction and evaluation; the empty word is the actual physical pressure, prepend is actual spatial differentiation, and the same bounded receiver transports the actual pressure time source |
| Moving quartic force/source chart | `Millennium/NavierStokesAnisotropicQuarticCurrent.lean`; `Millennium/NavierStokesQuarticPressureModulation.lean` | — | — | **formal-only:** five-coefficient pressure split, two actual trace-source terms, regular axial force amplitude `kappa=epsilon*D`, complete harmonic null fibres, actual diagonal polynomial pullback, two factored frame weights and full source-driven force modulation with the aspect connection. Full reconstruction requires the declared quartic symmetry family; the exact finite pressure-time/second-velocity source is in `research/experiments/mfr3_pressure_evolution/` |
| Oriented entropy/action current under heat | `Millennium/HolonicEntropyActionInduction.lean`; `Millennium/HolonicTorusEntropyParametronEquivalence.lean`; `Millennium/HolonicEntropyHeatCurrent.lean` | — | — | **formal-only:** existing torus cross-current specialized to two actual heat-evolving sections, with initial alignment, positive-time reopening, zero-viscosity preservation and mixed spatial-derivative source. Full periodic Navier–Stokes shear and energy controls are recorded in `research/experiments/mfr_entropy_heat_current/`; no nonlinear stretching control or scalar thermal-entropy identification is asserted |
| Nonlinear velocity–vorticity current and cell return | `Millennium/NavierStokesCrossCurrentCalculus.lean`; `Millennium/NavierStokesLambCurrentEvolution.lean`; `Millennium/NavierStokesCellLinearReceiver.lean`; `Millennium/NavierStokesLambCurrentCell.lean` | — | — | **formal-only:** actual cross-product Laplacian, rotational momentum, nonlinear current source with pressure/stretching/forcing/mixed diffusion, open-lifespan attachment, four-term resolved/remainder reconstruction and differentiated six-face cell balance. Full-mode source and generated Leray-mode witnesses live in `research/experiments/mfr_lamb_current/`; no tail or terminal bound is assumed |
| All-time folded xi source and its retained remainder | `RH/FoldedKernel.lean`; `RH/FoldedSourceBounds.lean`; `RH/FoldedSource.lean`; `RH/FoldedSourceTail.lean`; `RH/FoldedSourceDerivative.lean`; `RH/FoldedSourceZeros.lean` | — | — | **formal-only:** actual standard `Hstd` reconstructed from absolutely integrable positive-half-line integer events at every real heat time, Gaussian cutoff remainder, uniform time/height control, differentiated event integrals, compact derivative convergence and eventual rectangle multiplicity-count agreement under a zero-free boundary; no arithmetic positivity or zero-placement conclusion |
| Finite and infinite Copson--de Bruijn boundary | `Mathematics/CopsonDeBruijnFiniteTail.lean`; `Mathematics/CopsonDeBruijnFiniteSharp.lean`; `Mathematics/CopsonDeBruijnInfiniteBoundary.lean`; `Mathematics/CopsonDeBruijnFiniteRecurrence.lean`; `Mathematics/CopsonDeBruijnAdmissibleRecurrence.lean`; `Mathematics/CopsonDeBruijnNormalizedDynamics.lean`; `Mathematics/CopsonDeBruijnOrbitConvergence.lean`; `Mathematics/CopsonDeBruijnOrbitDichotomy.lean`; `Mathematics/CopsonDeBruijnHarmonicDrift.lean`; `Mathematics/CopsonDeBruijnOrbitLimit.lean` | — | — | **formal-only:** complete suffix energies, one-based tail weights, mass/surface face and preimage, exact homogeneity, compact finite sharpness, silent-extension monotonicity, direct `ENNReal` infinite control, finite-support reflection, least-coefficient equivalence, real ambient variational calculus, strict finite minimum decrease, minimizer interiority, Euler marginals, the attained finite de Bruijn recurrence, dependent infinite recurrence/obstructions, exact finite-prefix threshold equivalence, an explicit globally admissible coefficient, boundary finiteness, critical attainment, real/`ENNReal` threshold equality, exact normalized moving-root/drift algebra, global normalized-orbit bounds, moving-root fixed points and forward-invariant basin transport, exact compact drift approximation, harmonic drift exclusion, and the derived lower-or-upper `Tendsto` dichotomy for every admissible `x>1`; threshold-dependent asymptotic branch selection and certified enclosure remain open |
| Fermionic occupation and CAR | `Computation/HolonicFermionicOccupation.lean` | — | — | **formal-only:** finite Fock occupation, signed creation/annihilation, CAR |
| Finite Fermi–Hubbard transport | `Computation/HolonicFermiHubbard.lean` | — | — | **formal-only:** Hermitian Hamiltonian and particle-number sectors |
| Coherent polarized-crystal paths | `Computation/HolonicPolarizedCrystalTransport.lean` | — | — | **formal-only:** retained path fibres, Jones transport, analyzer/intensity order |
| Simulation assurance and eigenpair residuals | `Computation/HolonicSimulationCertificate.lean` | nearest bounded owner: `exact_owner_testimony.rs` | — | **formal-only correspondence:** external producer/checker boundary remains explicit |
| Constructive differential boundary calculus | `Computation/HolonicConstructiveDifferentialBoundary.lean` | partial: `exact_linear.rs`; `running_integral.rs`; `crates/holonic-life/src/reconstruction_fiber.rs` | — | **partial:** no Rust owner for the square-zero jet and complete standard/residue receiver |

## Exterior operator applications

[established-bounded; implemented-exact] Conversation material is prepared by
`applications/conversation-data/{conversation_data,providers}.py`. Its private SQLite/JSONL
boundary preserves source records, actual user-agent comparison, distinct runtime routes and
source-addressed curation. It invokes no engine, learner or prover; see the
[data guide](CONVERSATION_DATA.md). This is an exterior data owner, not a second HNN engine.

[established-bounded; implemented-exact] `applications/conversation-data/exposure.py` now emits
separate source-qualified occurrence families, with development/evaluation/deferred boundaries,
full captured views and metadata-only source links. `holonics-hna::alpha::exposure` is its typed
cold reader and immutable-file cursor; `alpha_exposure` demonstrates cold inspection/restart.
The [data guide](CONVERSATION_DATA.md#athena-alpha-causal-exposure) states the actual artifact and
checks. These owners supply no native current or learned model; AC1 owns that attachment.


| Application relation | Exterior owner | Engine/application owners | Status and exact open fibre |
|---|---|---|---|
| Persistent morphology-variant workspace | `crates/holonics-workspace/src/{artifact,evaluation,manifest,workspace}.rs`; `applications/holonics-workbench/src/adapters/workspace.rs` | admitted dismantling return -> earlier `AthenaAlphaApplication` adapter -> bounded circulation/cultivation/snapshot/evaluation -> package export | **exact-bounded application lifecycle, not attained Athena-alpha:** explicit-root manifest and artifacts return native snapshot import, resolved experiments, persisted conduct and actual continuation, staged candidate, atomic commit/decline, current-withdrawn-restored evaluation, and exact ONNX/Safetensors round trips. The CLI resolves the visible root from `--root` or the current directory. Open fibres are raw model-directory lift, qualitative multimodal emission, and persistent configurable diffusion. [2026-09-03: the per-event construction departed under SKE4 and `lift-gemma-receipt` went with it; the workspace is founded by `import-snapshot`.] |
| Holonics diagnostic command/event protocol | `applications/holonics-workbench/src/{command,event,protocol,presentation,cli,runtime,adapters/*}.rs` | bounded Athena session mechanisms; Eros material mouth/atlas; Soulkiller exterior chart inspection; engine package/export/probe owners | **exact-bounded diagnostic surface:** versioned human/JSON/JSONL requests and returns expose low-level mechanisms beneath `diagnostic`. The rejected Ratatui body and hidden artifact root are absent. Diagnostic process-memory sessions, demos, and probes are not the persistent model-building application and do not grade qualitative capability. [2026-09-03: the per-event construction departed under SKE4 and the workbench demo went with it; `demo-open` and the scripted `diagnostic demo` flow are absent, and a session opens from a snapshot.] |

## Receiver engraving and scientific presentation

[established-bounded; source-inspected] The repository-local Typst packages
[`holonic-receiver`](../research/papers/source/packages/holonic-receiver/README.md) and
[`holonic-engraving`](../research/papers/source/packages/holonic-engraving/README.md) consume supplied
complex source/current/incidence and return vector faces. The exact exterior companion supplies
projection, depth clipping, field level traces, primary response and retained mark/source data;
Typst and SVG paint that packet. Existing `relational-geometry::{projection,receiver_atlas}`,
`holonic-engine::{dimensional_wave,display}` and the CAD rendering sources remain their distinct
native/design owners. This adds no GPU semantic renderer or live proof assistant to HNN operation.
The [receiver review](../research/records/2026-09-10_RECEIVER_ENGRAVING_RETAINS_COMPLEX_CURRENT_AND_SUPERSEDES_THE_PAINTED_ATLAS.md)
records source methods, C³/GR examples and exact checks.

[established-bounded; source-inspected] The [stress/knot return](../research/records/2026-09-10_STRESS_ENERGY_AND_SCATTERING_WAVES_RETAIN_THE_KNOT_AND_ITS_RECEIVERS.md)
adds exact annular braid geometry, triangular embedding checks and finite wave/heat propagation in
`research/experiments/receiver_engraving/{knot_geometry,knot_waves,triangle_embedding}.py`.
`verify_stress_waves.py` compares the returned packets to their actual source evolution.
`knot-scenes.json` is the exterior Typst/SVG packet; its optional dyadic entropy enclosures retain
their error radius and do not round the source current or geometry.

[established-bounded; source-inspected] The [woven ecology return](../research/records/2026-09-10_WOVEN_FIELD_ECOLOGIES_RETURN_OPTICAL_HORIZONS_AND_REMOTE_CONFORMATION.md)
composes `woven_ecology.py`, `woven_bridge.py`, `constitutive_lobes.py` and `ecology_details.py`
in that same exterior directory. These own the radial tetrahedral receiver, witnessed torus
contacts, supported shorts embedding, and finite remote conformation response.
`verify_woven.py` checks their source/receiver binding; `verify_closed_receiver.py` checks the
closed-boundary visibility option against the prior exact renderer. Native protein/constraint,
Snell, conformation and constitutive owners remain the sources of their distinct relations.

[established-bounded; source-inspected] The [sequence/kinetic return](../research/records/2026-09-10_SEQUENCE_FOLD_AND_REACTION_CURRENT_MAKE_THE_CAUSAL_THOUGHT_CHAIN_CONCRETE.md)
adds `sequence_folding.py`, `sequence_kinetics.py`, `sequence_figures.py` and `verify_sequence.py`
in the same exterior experiment directory. They construct a finite anchored FCC conformation
population, sequence-conditioned kinetic generators, geometric ligand occupancy and exact
reaction moments. The Athena blueprint uses their joint-state and marked-emission consequences;
these reference programs are not native inference or a text-to-protein routing layer.

## Maintenance law

Update a row in the same coherent change that moves, adds, or removes one of its owners. Do not
generate this file from imports, filenames, symbols, or hashes: correspondence is a mathematical and
implementation judgment. If a proposed row cannot name the common carrier and the exact open fibre,
leave it out until that relation is understood.
