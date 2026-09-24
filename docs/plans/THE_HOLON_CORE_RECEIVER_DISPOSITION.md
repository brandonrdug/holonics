# Phase 7 disposition: every receiver-named public type against the core receivers

[established-bounded; source-inspected for the rows marked so, otherwise name-and-owner inferred]
Plan phase 7 of [the Holon core plan](THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md#phase-7-disposition-receivers-as-holons-at-ports).
The workspace declares 361 public `struct`/`enum`/`trait`/`type` items whose name contains
`Receiv` outside test files (September 22, after this phase). Each is one of four things against the
core receivers of `crates/holonic-core/src/law/receiver.rs` (`holonic_core::law::receiver`,
Lean `Holon/Law.lean`):

| Disposition | Meaning | Core owner |
|---|---|---|
| **passive coholon** | a declared reading at zero flow; linear ones read `C e` (`passive_reading`), any reading draws zero power (`coholon_reading_power`) | `PassiveCoholon`, `coholon_bond`, the `Reading` trait |
| **active receiver Holon** | returns something into the Holon it reads, entering with its power term: a joined receiver body, a learned relation, an exterior drive or a pullback | `ActiveReceiver`, `ReceiverPower`, `active_receiver` |
| **receiver face (codec)** | the value a reading returns, its chart or aperture: a codec projection, not a port object | `ExactFace`, `ReceiverWidth`, `Horizon`, `Rung` |
| **different object** | a refusal, identifier, event/world chart, kind label or retention/compression algebra that happens to carry the word | — |

Counts: 19 passive coholon, 9 active receiver Holon, 158 receiver face, 175 different object. The
39 rows marked *source-inspected* were read at their owner; the rest are classified from the name
and owner module by the rules stated in each row, and a later consumer audit may move them.

## Genuine duplicates

* `holonic-engine/src/interval_potential.rs` was an orphan (declared by no `mod`), byte-identical
  after its header to `cuda_refine/interval_potential.rs`; it was removed. The compiled
  `ResidentIntervalPotentialReceiver` is unchanged.
* `receiver_release::LinearReading` and `standing::ReceiverReading` are the same object (a named
  linear reader). Neither can alias the other without breaking public API (`LinearReading` has
  public fields; `ReceiverReading` validates its extents and is `Serialize`), so both convert to
  the core `PassiveCoholon` (`passive_coholon()`), with equality tests of the reading value.
* The same-named but different objects are not aliased: three `ReceiverId(u64)` (distinct ID spaces
  in `relational-geometry::projection`, `receiver_exact_compression` and `holonic-language`), three
  `ReceiverFamily`, two `ReceiverGrain`, two `ReceiverReading` (`design_selection`'s is a reading
  value) and two `ReceiverHistoryRealizationPassage` receipts.

## The native active receivers (not receiver-named)

| Type | Owner | Power term |
|---|---|---|
| `NativeNormalizedMaterialReturn` | `field/receiver/normalized.rs` | reading (`p`, `q`, `q−p`, `J_p(q−p)` returned as covectors) |
| `NativeNormalizedSection` | `normalized/section.rs` | reading: `p = softmax(Re s)` is nonlinear, zero power |
| `NativeNormalizedSectionPullback` | `normalized/section.rs` | pullback `J_p g`, `J_p` symmetric (`softmaxJacobian_transpose`) |
| `NativePhaseParticipation` | `normalized/phase.rs` | exterior drive `y = Σ a UΨ`, delivered `⟨e_D, y⟩` enclosed by `delivered_power` |
| `NativePairParticipation` | `normalized/pair.rs` | exterior drive `y = Σ a v`, delivered `⟨e_D, y⟩` enclosed by `delivered_power` |
| `NativePhaseParticipationAdjoint`, `NativePairParticipationAdjoint` | `phase.rs`, `pair.rs` | pullback (`pullback_law`) |
| `NativeMaterialSourcePullback` | `normalized/pullback.rs` | pullback onto `10·nodes + 2·contacts` coordinates |

Each carries `receiver_element() -> ActiveReceiver`, a host-side declaration that reads only carried
extents; no kernel, launch or returned value changed (device tests
`pair_receiver_element_declares_its_drive_without_changing_the_return`,
`phase_receiver_element_declares_its_drive_without_changing_the_return`).

## Every receiver-named type

| Type | Kind | Owner | Disposition | Reason |
|---|---|---|---|---|
| `ReceiverRow` | struct | `holonic-abi/src/live_event_cuda.rs` | receiver face (codec) | a device row encoding of an event receiver (codec) (source-inspected) |
| `EventReceiver` | struct | `holonic-body/src/manifold.rs` | receiver face (codec) | an event channel/held-face declaration of the live event chart (source-inspected) |
| `ReceiverFactorization` | enum | `holonic-core/src/exact_linear/contextual.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ActiveReceiverReading` | struct | `holonic-core/src/law.rs` | active receiver Holon | the interface-conductance receiver reading (`active_receiver_law`) (source-inspected) |
| `ActiveReceiver` | struct | `holonic-core/src/law/receiver.rs` | active receiver Holon | the core active receiver element (this phase) (source-inspected) |
| `ReceiverExchange` | struct | `holonic-core/src/law/receiver.rs` | active receiver Holon | an active receiver's own balance and delivered power (this phase) (source-inspected) |
| `ReceiverPower` | enum | `holonic-core/src/law/receiver.rs` | active receiver Holon | the declared power term of an active receiver (this phase) (source-inspected) |
| `ReceiverWidth` | struct | `holonic-core/src/law/receiver.rs` | receiver face (codec) | the diameter face over a fibre; moved to the core this phase (source-inspected) |
| `JointReceiverReading` | struct | historical Rust mirror `holonic-engine/src/acoustic_receiver.rs` (retired R1) | receiver face (codec) | historical readout/face value (codec projection); the checked acoustic law remains in `Foundation/AcousticReceiver.lean` |
| `AlgebraicReceiver` | struct | `holonic-engine/src/algebraic.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `AlgebraicReceiverReceipt` | struct | `holonic-engine/src/algebraic.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ExactZetaReceiverMeasure` | struct | `holonic-engine/src/arithmetic_fiber.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `EulerReceiverId` | struct | `holonic-engine/src/arithmetic_monodromy.rs` | different object | an identifier/address (name-inferred) |
| `ExactEulerReceiverStanding` | struct | `holonic-engine/src/arithmetic_monodromy.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `PrimeAxisReceiver` | struct | `holonic-engine/src/arithmetic_phase.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `ReceiverFiber` | struct | `holonic-engine/src/atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ProposedBridge.supportingReceivers` | field | `Foundation/Bridge.lean` | receiver family supporting a proposed connection | paired receiver maps carried with the proposal; Rust mirror retired in R1 |
| `AltitudeReceiverLandmark` | struct | `holonic-engine/src/atmospheric_inverse.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `AtmosphericReceiverBody` | struct | `holonic-engine/src/atmospheric_inverse.rs` | receiver face (codec) | a receiver-named value (name-inferred) |
| `SpectralReceiverContact` | struct | `holonic-engine/src/atmospheric_inverse.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `SpectralReceiverOccurrence` | struct | `holonic-engine/src/atmospheric_inverse.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `CausalBodyReceiverStanding` | struct | `holonic-engine/src/causal_body.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `CausalProjectionReceiverReceipt` | struct | `holonic-engine/src/causal_body.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `CausalReceiverReturn` | struct | `holonic-engine/src/causal_body.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ConservingReceiverSpace` | struct | `holonics/src/receiver/causal_chord.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverWindow` | struct | `holonic-engine/src/certified_face.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `CodecIndexReceiver` | struct | `holonic-engine/src/codec_system.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `ReceiverFamily` | struct | `holonic-engine/src/cuda_realizer_search.rs` | different object | three unrelated objects (prime family, monomial family, axis bitset) (source-inspected) |
| `WheelReceiver` | struct | `holonic-engine/src/cuda_realizer_search.rs` | different object | per-prime reduction data of a realizer search (source-inspected) |
| `ResidentIntervalPotentialReceiver` | struct | `holonic-engine/src/cuda_refine/interval_potential.rs` | passive coholon | a resident interval-valued linear reader (incidence rows applied to potentials): the passive coholon's device chart; the orphan, uncompiled, byte-identical duplicate `holonic-engine/src/interval_potential.rs` was removed this phase (source-inspected) |
| `ResidentAddressedFactoredReceiverFrameReturn` | struct | `holonic-engine/src/cuda_refine/membrane_types.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ResidentFactoredMomentReceiverAddress` | struct | `holonic-engine/src/cuda_refine/membrane_types.rs` | different object | an identifier/address (name-inferred) |
| `ResidentFactoredMomentReceiverReturn` | struct | `holonic-engine/src/cuda_refine/membrane_types.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ResidentFactoredReceiverHistoryReceipt` | struct | `holonic-engine/src/cuda_refine/membrane_types.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ResidentReceiverHistoryCompressionReceipt` | struct | `holonic-engine/src/cuda_refine/membrane_types.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ResidentSituatedReceiverPairingReturn` | struct | `holonic-engine/src/cuda_refine/membrane_types.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `DeclaredReceiver` | struct | `holonic-engine/src/design_selection.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `ReceiverReading` | enum | `holonic-engine/src/design_selection.rs` | receiver face (codec) | an exact reading value or its absence (a face), not a reader (source-inspected) |
| `ReceiverWeighting` | struct | `holonic-engine/src/design_selection.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `DimensionalReceiverAtlas` | struct | `holonic-engine/src/dimensional_receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `DimensionalReceiverDeed` | enum | `holonic-engine/src/dimensional_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `DimensionalReceiverError` | enum | `holonic-engine/src/dimensional_receiver.rs` | different object | a refusal/status (name-inferred) |
| `DimensionalReceiverFounding` | struct | `holonic-engine/src/dimensional_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `DimensionalReceiverFrame` | struct | `holonic-engine/src/dimensional_receiver.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `DimensionalReceiverRadiation` | struct | `holonic-engine/src/dimensional_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `DimensionalReceiverRequest` | struct | `holonic-engine/src/dimensional_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `DimensionalReceiverTransition` | struct | `holonic-engine/src/dimensional_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ExactPremultipliedReceiverResponse` | struct | `holonic-engine/src/dimensional_wave.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ExactReceiverPhasePopulation` | struct | `holonic-engine/src/dimensional_wave.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ExactReceiverPrimaryDoctrine` | struct | `holonic-engine/src/dimensional_wave.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `DivisorReceiverId` | struct | `holonic-engine/src/divisor_reconstruction.rs` | different object | an identifier/address (name-inferred) |
| `KeptReceiverJacobian` | struct | `holonic-engine/src/edit_rigidity.rs` | receiver face (codec) | a receiver-named value (name-inferred) |
| `ReceiverResidual` | struct | `holonic-engine/src/edit_rigidity.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `FittedReceiver` | struct | `holonic-engine/src/evaluation_discipline.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `ReceiverAdmission` | struct | `holonic-engine/src/evaluation_discipline.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `SparseQuadraticPairReceiverFrame` | struct | `holonic-engine/src/factored_moment/types.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `SparseQuadraticPairReceiverTerm` | struct | `holonic-engine/src/factored_moment/types.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `FieldReceiverQuery` | struct | `holonic-engine/src/field_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `FieldReceiverReceipt` | struct | `holonic-engine/src/field_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverImageDifference` | struct | `holonic-engine/src/field_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverImageOccurrence` | struct | `holonic-engine/src/field_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverImageSection` | struct | `holonic-engine/src/field_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPhaseBasis` | struct | `holonic-engine/src/field_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPhaseProjection` | struct | `holonic-engine/src/field_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverSampleContact` | struct | `holonic-engine/src/field_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `FoundedReceiver` | struct | `holonic-engine/src/founded_receiver.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `DeedReceiver` | struct | `holonic-engine/src/front_passage.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `GraphReceiverError` | enum | `holonic-engine/src/graph_receiver.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverGraphAlgebraicEnd` | struct | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverGraphAlgebraicRegion` | struct | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverGraphAlgebraicSection` | struct | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverGraphAnalysis` | struct | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverGraphAtlas` | struct | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverGraphCell` | struct | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverGraphCellFiber` | enum | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverGraphChange` | enum | `holonic-engine/src/graph_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverGraphDeed` | enum | `holonic-engine/src/graph_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverGraphDelta` | struct | `holonic-engine/src/graph_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverGraphFrame` | struct | `holonic-engine/src/graph_receiver.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverGraphQueryWork` | struct | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverGraphRadiation` | struct | `holonic-engine/src/graph_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverGraphRequest` | struct | `holonic-engine/src/graph_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverGraphSection` | struct | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverGraphSeed` | enum | `holonic-engine/src/graph_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverGraphSourceAdvance` | struct | `holonic-engine/src/graph_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverGraphSourceWitness` | enum | `holonic-engine/src/graph_receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverGraphTransition` | struct | `holonic-engine/src/graph_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverGraphTransitionCause` | enum | `holonic-engine/src/graph_receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverGrainComplex` | struct | `holonic-engine/src/holonic_complex.rs` | different object | a complex; phase-4 disposition (a) `core_chart` (source-inspected) |
| `ReceiverGrainId` | struct | `holonic-engine/src/holonic_complex.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverHolonicComplexEvent` | struct | `holonic-engine/src/holonic_complex.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverHolonicComplexLaw` | struct | `holonic-engine/src/holonic_complex.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverHolonicComplexRadiation` | struct | `holonic-engine/src/holonic_complex.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverHolonicComplexStanding` | struct | `holonic-engine/src/holonic_complex.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `NativeReceiverResponse` | struct | `holonic-engine/src/holonic_intelligence/operative_condensation.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `NativeReceiverFace` | struct | `holonic-engine/src/holonic_intelligence/operative_intervention.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverFacet` | struct | `holonic-engine/src/holonic_intelligence/profile.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `NativeContinuationReceiver` | trait | `holonic-engine/src/holonic_intelligence/repeated_circulation.rs` | different object | a continuation decision law (like `receiver_release::DecisionLaw`), not a port object (source-inspected) |
| `UniqueActualSuccessorReceiver` | struct | `holonic-engine/src/holonic_intelligence/repeated_circulation.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `ReceiverBody` | struct | `holonic-engine/src/holonic_interaction.rs` | active receiver Holon | the participating receiver joined as a Holon at link ports (phase 3b, `joined_holon`) (source-inspected) |
| `ReceiverFamily` | struct | `holonic-engine/src/identity_atlas.rs` | different object | three unrelated objects (prime family, monomial family, axis bitset) (source-inspected) |
| `ReceiverCoupling` | struct | historical Rust prototype `holonic-engine/src/live_presentation.rs` (retired R1; no current owner) | different object | directed edge in the presentation-only receiver-coupling graph; no current standing or receiver law (source-inspected) |
| `ReceiverCouplingSet` | struct | historical Rust prototype `holonic-engine/src/live_presentation.rs` (retired R1; no current owner) | different object | transitive directed reachability over presentation-only receiver-coupling edges; no current standing or receiver law (source-inspected) |
| `ReceiverBodyState` | struct | `holonic-engine/src/local_star.rs` | receiver face (codec) | a receiver-named value (name-inferred) |
| `ReceiverBoundaryDeed` | struct | `holonic-engine/src/local_star.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverEventNerve` | struct | `holonic-engine/src/local_star.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverFounding` | struct | `holonic-engine/src/local_star.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverLocalCoupling` | struct | `holonic-engine/src/local_star.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverNerveCell` | struct | `holonic-engine/src/local_star.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPopulationChange` | enum | `holonic-engine/src/local_star.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverPopulationDeed` | enum | `holonic-engine/src/local_star.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverRotationCoupling` | struct | `holonic-engine/src/local_star.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverSharedOccurrence` | enum | `holonic-engine/src/local_star.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverTraversalChart` | struct | `holonic-engine/src/local_star.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverTraversalOccurrence` | struct | `holonic-engine/src/local_star.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverTraversalReceipt` | struct | `holonic-engine/src/local_star.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverTraversalStep` | enum | `holonic-engine/src/local_star.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverWorldlineStep` | struct | `holonic-engine/src/local_star.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverPartition` | struct | `holonic-engine/src/mordell_weil_realizers/receivers.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ResidualReceivers` | struct | `holonic-engine/src/mordell_weil_realizers/receivers.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `ResidentNativeAnatomicalPotentialReceiver` | struct | `holonic-engine/src/native_anatomical_potential.rs` | passive coholon | delegates to `ResidentIntervalPotentialReceiver`: the passive coholon's device chart (source-inspected) |
| `NativeReceivedCurrentDifference` | struct | `holonic-engine/src/native_ecology/constitutive_fibre/circulation.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `NativeFieldReceivedDifference` | struct | `holonic-engine/src/native_ecology/constitutive_fibre/field.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `NativeFieldReceiverStatus` | enum | `holonic-engine/src/native_ecology/constitutive_fibre/field.rs` | different object | a refusal/status (name-inferred) |
| `NativeCurrentHistorySourceReceiver` | struct | `holonic-engine/src/native_ecology/constitutive_fibre/field/current_history_source.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `NormalFamilyReceiverReading` | struct | `holonic-engine/src/native_ecology/constitutive_fibre/field/material_transport/normal/direct/wave/family/receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `NormalWaveFamilyReceiver` | struct | `holonic-engine/src/native_ecology/constitutive_fibre/field/material_transport/normal/direct/wave/family/receiver.rs` | active receiver Holon | a resident wave-family readout over a normal family; its power declaration is owed (source-inspected) |
| `NormalReceiverCoordinates` | struct | `holonic-engine/src/native_ecology/constitutive_fibre/field/material_transport/normal/direct/wave/family/section.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ConstitutiveImageReceiver` | enum | `holonic-engine/src/native_ecology/constitutive_fibre/resident/image.rs` | different object | a borrowed producing-relation selector for an adjoint image (the pullback's operand), not a receiver (source-inspected) |
| `WaveSourceReceiver` | enum | `holonic-engine/src/native_ecology/constitutive_fibre/resident/wave_relation.rs` | receiver face (codec) | the declared receiver chart of a wave law (direct or unit-real-sum section) (source-inspected) |
| `SeparatingReceiver` | struct | `holonic-engine/src/native_ecology/cultivation_overlay.rs` | receiver face (codec) | a separating witness value (source-inspected) |
| `NativeReceiverFibre` | struct | `holonic-engine/src/native_ecology/inference_membrane.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverReopening` | struct | `holonic-engine/src/native_ecology/recurrent.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverInsufficiency` | struct | `holonic-engine/src/native_spool/resident.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverInsufficiencyCause` | enum | `holonic-engine/src/native_spool/resident.rs` | different object | a refusal/status (name-inferred) |
| `NativeReceiverConsequence` | struct | `holonic-engine/src/native_spool/thread.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverUncertaintyWidth` | struct | `holonic-engine/src/neck.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `AdmittedReceiverPartition` | struct | `holonic-engine/src/observation_ecology.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `PredictedReceiverRelation` | struct | `holonic-engine/src/observation_ecology.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverAffineChart` | struct | `holonic-engine/src/observation_ecology.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverBatch` | struct | `holonic-engine/src/observation_ecology.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverChartId` | struct | `holonic-engine/src/observation_ecology.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverCoordinateFamily` | struct | `holonic-engine/src/observation_ecology.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverCoordinateFamilyId` | struct | `holonic-engine/src/observation_ecology.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverGradeId` | struct | `holonic-engine/src/observation_ecology.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverLineageId` | struct | `holonic-engine/src/observation_ecology.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverPredictionId` | struct | `holonic-engine/src/observation_ecology.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverRelationGrade` | struct | `holonic-engine/src/observation_ecology.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverRelationGradeCounts` | struct | `holonic-engine/src/observation_ecology.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverRelationObstruction` | struct | `holonic-engine/src/observation_ecology.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverRelationObstructionKind` | enum | `holonic-engine/src/observation_ecology.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverRelationPrediction` | struct | `holonic-engine/src/observation_ecology.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverRelationState` | enum | `holonic-engine/src/observation_ecology.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverTestimony` | struct | `holonic-engine/src/observation_ecology.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverTestimonyId` | struct | `holonic-engine/src/observation_ecology.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverTestimonyStanding` | struct | `holonic-engine/src/observation_ecology.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReturnedReceiverCell` | struct | `holonic-engine/src/observation_ecology.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReturnedReceiverPartition` | struct | `holonic-engine/src/observation_ecology.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `PhaseCurrentReceiverId` | struct | `holonic-engine/src/phase_current.rs` | different object | an identifier/address (name-inferred) |
| `PluralReceiverAssembly` | struct | `holonic-engine/src/presentation.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverApertureTrace` | struct | `holonic-engine/src/presentation.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverStandingRelation` | struct | `holonic-engine/src/presentation.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ExactReceiverMeasure` | struct | `holonic-engine/src/prime_ecology.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverOperation` | enum | `holonic-engine/src/realization.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverProgram` | struct | `holonic-engine/src/realization.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverProgramError` | enum | `holonic-engine/src/realization.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverRealization` | struct | `holonic-engine/src/realization.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverRealizationError` | enum | `holonic-engine/src/realization.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverHistoryRealizationPassage` | struct | `holonic-engine/src/realization/passage.rs` | different object | two distinct receipts (engine realization passage; holonic-life native passage) (source-inspected) |
| `CertifiedReceiverFace` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverAcceptanceCover` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverAcceptanceOrgan` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverAcceptanceSeam` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverAcceptanceSection` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverArrangement` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverDirectionalFiber` | enum | `holonic-engine/src/receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverError` | enum | `holonic-engine/src/receiver.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverFace` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverFaceExtent` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverFaceFormationCause` | enum | `holonic-engine/src/receiver.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverFaceFormationReceipt` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverFaceSpec` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverHorizonContact` | enum | `holonic-engine/src/receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverOrganSection` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPortSection` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPrimitive` | enum | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPrimitiveId` | enum | `holonic-engine/src/receiver.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverProjectiveHorizonFiber` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverSeamSection` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverSourceRebase` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverSourceSection` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverSourceSelection` | struct | `holonic-engine/src/receiver.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverAtlas` | struct | `holonic-engine/src/receiver_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ExactReceiverCurrentArrival` | struct | `holonic-engine/src/receiver_current.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ExactReceiverCurrentArrivalAtlas` | struct | `holonic-engine/src/receiver_current.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ExactReceiverCurrentDeferredArrival` | struct | `holonic-engine/src/receiver_current.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ExactReceiverCurrentError` | enum | `holonic-engine/src/receiver_current.rs` | different object | a refusal/status (name-inferred) |
| `ExactReceiverCurrentLaw` | struct | `holonic-engine/src/receiver_current.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ExactReceiverCurrentPassage` | struct | `holonic-engine/src/receiver_current.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ExactReceiverCurrentPassageReceipt` | struct | `holonic-engine/src/receiver_current.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ExactReceiverCurrentPredecessor` | struct | `holonic-engine/src/receiver_current.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ExactReceiverCurrentRadiation` | struct | `holonic-engine/src/receiver_current.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ExactReceiverCurrentSite` | struct | `holonic-engine/src/receiver_current.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ExactReceiverCurrentWitness` | struct | `holonic-engine/src/receiver_current.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverCurrentPassageId` | struct | `holonic-engine/src/receiver_current.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverCurrentSiteId` | struct | `holonic-engine/src/receiver_current.rs` | different object | an identifier/address (name-inferred) |
| `ExistingReceiverBatch` | struct | `holonic-engine/src/receiver_ecology.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverCellReturn` | struct | `holonic-engine/src/receiver_ecology.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverDirectionFiber` | struct | `holonic-engine/src/receiver_ecology.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverEcologyError` | enum | `holonic-engine/src/receiver_ecology.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverGrainQuotient` | struct | `holonic-engine/src/receiver_ecology.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverGrainQuotientId` | struct | `holonic-engine/src/receiver_ecology.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverHorizonTopology` | enum | `holonic-engine/src/receiver_ecology.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverHypervolume` | struct | `holonic-engine/src/receiver_ecology.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverMorphologyKind` | enum | `holonic-engine/src/receiver_ecology.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverMorphologySummary` | struct | `holonic-engine/src/receiver_ecology.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverPerspective` | struct | `holonic-engine/src/receiver_ecology.rs` | active receiver Holon | a participating perspective: joined as an active receiver when its body participates (source-inspected) |
| `ReceiverPerspectiveAddress` | enum | `holonic-engine/src/receiver_ecology.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverPerspectiveSpec` | struct | `holonic-engine/src/receiver_ecology.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverRelativeExtent` | struct | `holonic-engine/src/receiver_ecology.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReturnedReceiverCellAddress` | struct | `holonic-engine/src/receiver_ecology.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverExactCompression` | struct | `holonic-engine/src/receiver_exact_compression.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverId` | struct | `holonic-engine/src/receiver_exact_compression.rs` | different object | an identifier; the three `ReceiverId(u64)` name distinct ID spaces and are not aliased (source-inspected) |
| `PartialReceiverHistoryCompression` | struct | `holonic-engine/src/receiver_history_compression/compression.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverHistoryRefusal` | enum | `holonic-engine/src/receiver_history_compression/compression.rs` | different object | a refusal/status (name-inferred) |
| `AddressedFactoredIntegralReceiver` | struct | `holonic-engine/src/receiver_history_compression/factored_forms.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `AddressedFactoredIntegralReceiverComplex` | struct | `holonic-engine/src/receiver_history_compression/factored_forms.rs` | different object | a pool of receiver functionals; phase-4 disposition (c) (source-inspected) |
| `AddressedFactoredIntegralReceiverTerm` | struct | `holonic-engine/src/receiver_history_compression/factored_forms.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `AddressedPrimitiveReceiverFrame` | struct | `holonic-engine/src/receiver_history_compression/factored_forms.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `FactoredIntegralReceiverForm` | struct | `holonic-engine/src/receiver_history_compression/factored_forms.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `FactoredIntegralReceiverTerm` | struct | `holonic-engine/src/receiver_history_compression/factored_forms.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `MembraneFactoredIntegralReceiverHistory` | struct | `holonic-engine/src/receiver_history_compression/membrane.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `DecodedReceiverImage` | struct | `holonic-engine/src/receiver_history_compression/observable.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ObservableMomentReceiverDecode` | struct | `holonic-engine/src/receiver_history_compression/observable.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ObservableMomentReceiverHistoryCompression` | struct | `holonic-engine/src/receiver_history_compression/observable.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ObservableMomentReceiverSeparator` | struct | `holonic-engine/src/receiver_history_compression/observable.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverFactor` | struct | `holonic-engine/src/receiver_history_compression/observable.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverHistoryCompression` | struct | `holonic-engine/src/receiver_history_compression/observable.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverHistoryWork` | struct | `holonic-engine/src/receiver_history_compression/observable.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `FactoredIntegralReceiverHistoryFrame` | struct | `holonic-engine/src/receiver_history_compression/projective_history.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `FactoredRationalReceiverHistoryFrame` | struct | `holonic-engine/src/receiver_history_compression/projective_history.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `CultivatedReceiverHistoryRest` | struct | `holonic-engine/src/receiver_history_cultivation.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ExactReceiverPhaseJet` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverChannelSample` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverConicSpecies` | enum | `holonic-engine/src/receiver_phase_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPhaseAddress` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverPhaseAtlasError` | enum | `holonic-engine/src/receiver_phase_atlas.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverPhaseAtlasEvent` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverPhaseAtlasLaw` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverPhaseAtlasRadiation` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverPhaseAtlasStanding` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverPhaseConnection` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPhaseConnectionId` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverPhaseCycle` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPhaseCycleId` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverPhaseGerm` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPhaseGermId` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverPhaseGermSignature` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverPhaseSection` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverPhaseSectionId` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverPhaseSectionOccurrence` | struct | `holonic-engine/src/receiver_phase_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `NamedReceiver` | struct | `holonic-engine/src/relation_ladder.rs` | passive coholon | a declared (possibly nonlinear) reading of a situation: a coholon reading at zero power (source-inspected) |
| `PotentialReceiverCertificate` | struct | `holonic-engine/src/soulkiller/foreign_potential_rest.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ResidentForeignPotentialReceiver` | struct | `holonic-engine/src/soulkiller/foreign_potential_rest.rs` | passive coholon | delegates to `ResidentIntervalPotentialReceiver`: the passive coholon's device chart (source-inspected) |
| `ForeignCoefficientReceiverClass` | struct | `holonic-engine/src/soulkiller/foreign_section_descent.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ForeignCoefficientReceiverQuotient` | struct | `holonic-engine/src/soulkiller/foreign_section_descent.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ForeignReceiverConstitutiveForm` | enum | `holonic-engine/src/soulkiller/foreign_section_descent.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `AnatomyReceiverCatalog` | struct | `holonic-engine/src/soulkiller/receiver_restricted_transport.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverRestrictedFactorDescent` | struct | `holonic-engine/src/soulkiller/receiver_restricted_transport.rs` | receiver face (codec) | a receiver-named value (name-inferred) |
| `ReceiverRestrictedFactorRefusal` | enum | `holonic-engine/src/soulkiller/receiver_restricted_transport.rs` | different object | a refusal/status (name-inferred) |
| `SuccessorSupportReceiverClass` | struct | `holonic-engine/src/soulkiller/receiver_restricted_transport.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverReading` | struct | `holonic-engine/src/standing.rs` | passive coholon | the passive coholon with validated extents (`passive_coholon`, tested equal); the same object as `receiver_release::LinearReading`, kept because that type has public fields (source-inspected) |
| `ReceiverAxis` | enum | `holonic-engine/src/token_invariance.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverFamily` | struct | `holonic-engine/src/token_invariance.rs` | different object | three unrelated objects (prime family, monomial family, axis bitset) (source-inspected) |
| `ReceiverFaceCarry` | enum | `holonic-engine/src/tube.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverPresentationTransport` | struct | `holonic-engine/src/tube.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverTube` | struct | `holonic-engine/src/tube.rs` | different object | the tube's physical apparatus; the core tube is its carrier law (source-inspected) |
| `ReceiverTubeChange` | enum | `holonic-engine/src/tube.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverTubeTransition` | struct | `holonic-engine/src/tube.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `WaveReceiverId` | struct | `holonic-engine/src/wave_propagation.rs` | different object | an identifier/address (name-inferred) |
| `WaveReceiverSpec` | struct | `holonic-engine/src/wave_propagation.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `CyclicReceiver` | struct | `holonic-engine/src/winding_inertia.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `ReceiverId` | struct | `holonic-language/src/lib.rs` | different object | an identifier; the three `ReceiverId(u64)` name distinct ID spaces and are not aliased (source-inspected) |
| `ReceiverQuestion` | struct | `holonic-life/examples/m6/route.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ContinuationReceiver` | enum | `holonic-life/src/causal_language.rs` | different object | a receiver kind label (name-inferred) |
| `LaboratoryReceiverQuotientReceipt` | struct | `holonic-life/src/laboratory_language.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `RenderingReceiverReturn` | struct | `holonic-life/src/mathematical_particle.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ValueReceiverReturn` | struct | `holonic-life/src/mathematical_particle.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ConstraintReceiver` | enum | `holonic-life/src/mathematical_particle/morphology/types.rs` | different object | a receiver kind label (name-inferred) |
| `ReturnedReceiverAdjoint` | struct | `holonic-life/src/mathematical_particle/morphology/types.rs` | receiver face (codec) | a receiver-named value (name-inferred) |
| `NativeMathematicalReceiver` | enum | `holonic-life/src/mathematical_particle/production_aperture/native_consequence_types.rs` | different object | a kind label of a native consequence family (source-inspected) |
| `ReceiverHistoryFactorization` | struct | `holonic-life/src/mathematical_particle/production_aperture/native_family_types.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ProductionReceiver` | enum | `holonic-life/src/mathematical_particle/production_aperture/types.rs` | different object | a receiver kind label (name-inferred) |
| `RequestedReceiverFactor` | struct | `holonic-life/src/mathematical_particle/recurrence.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `RicherReceiverReopening` | struct | `holonic-life/src/mathematical_particle/retained_boundary/types.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverHistoryRelation` | struct | `holonic-life/src/mathematical_particle/sameness/history.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverHistoryReturn` | struct | `holonic-life/src/mathematical_particle/sameness/history.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ClassificationReceiverReturn` | struct | `holonic-life/src/mathematical_particle/sameness/receivers.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverFaceRelation` | struct | `holonic-life/src/mathematical_particle/sameness/receivers.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `SimilarityReceiverReturn` | struct | `holonic-life/src/mathematical_particle/sameness/receivers.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `OpticalReceiverSignature` | struct | `holonic-life/src/mathematical_source/optical_recovery.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `NativeReceiverConstitutiveForm` | struct | `holonic-life/src/native_intelligence/exchange_situated_product.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `GranularFactorReceiver` | struct | `holonic-life/src/native_intelligence/granular_potential/basic.rs` | receiver face (codec) | an opaque observation face (source-inspected) |
| `GranularReceiverActionCurrent` | struct | `holonic-life/src/native_intelligence/granular_potential/basic.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `MaterialReceiverChart` | struct | `holonic-life/src/native_intelligence/material_factorization/core.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `MaterialReceiverChartAxis` | struct | `holonic-life/src/native_intelligence/material_factorization/core.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `MaterialReceiverInsufficiency` | struct | `holonic-life/src/native_intelligence/material_factorization/core.rs` | different object | a refusal/status (name-inferred) |
| `NativeAcousticReceiverCurrent` | struct | `holonic-life/src/native_intelligence/membrane_acoustic.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `NativeAcousticReceiverChart` | struct | `holonic-life/src/native_intelligence/membrane_acoustic/potential_formation.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `NativeOpticalReceiverIntervention` | enum | `holonic-life/src/native_intelligence/membrane_optical.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ExteriorParticipantReceiverChart` | struct | `holonic-life/src/native_intelligence/membrane_radiation.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ExteriorRelationReceiverChart` | struct | `holonic-life/src/native_intelligence/membrane_radiation.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `FactoredReceiverHistoryGateReceipt` | struct | `holonic-life/src/native_intelligence/membrane_radiation.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverFactorActionSection` | struct | `holonic-life/src/native_intelligence/membrane_radiation.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverCapabilityManifest` | struct | `holonic-life/src/native_intelligence/morphology_package.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `SourceNeutralContinuationReceiverHistory` | struct | `holonic-life/src/native_intelligence/source_neutral_rest/wire.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ReceiverHistoryRealizationPassage` | struct | `holonic-life/src/native_intelligence/types.rs` | different object | two distinct receipts (engine realization passage; holonic-life native passage) (source-inspected) |
| `PresentationReceiver` | enum | `holonic-life/src/presentation_quotient.rs` | different object | a receiver kind label (name-inferred) |
| `ReceiverGrain` | enum | `holonic-life/src/receiver_history/types.rs` | receiver face (codec) | a grain/aperture declaration of a face (relational-geometry: pixel grain; holonic-life: a return grain enum) (source-inspected) |
| `ReceiverHistoryCongruence` | struct | `holonic-life/src/receiver_history/types.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `RelationalReceiverQuotient` | struct | `holonic-life/src/relational_language/types.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ExactSuffixReceiverHistory` | struct | `holonic-life/src/suffix_ecology.rs` | different object | retention/compression algebra or relation over receiver functionals (retained standing, not a port object) (name-inferred) |
| `ExactSuffixReceiverState` | struct | `holonic-life/src/suffix_ecology.rs` | receiver face (codec) | a receiver-named value (name-inferred) |
| `ExactSuffixReceiverTransition` | struct | `holonic-life/src/suffix_ecology.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `SynchronizedReceiverId` | struct | `holonic-life/src/synchronized_occurrence.rs` | different object | an identifier/address (name-inferred) |
| `SynchronizedReceiverSection` | struct | `holonic-life/src/synchronized_occurrence.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `TimedReceiverCell` | struct | `holonic-life/src/synchronized_occurrence.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverFiberIdentity` | struct | `holonic-membrane/src/live_constituent.rs` | different object | an identifier/address (name-inferred) |
| `ReceiverCausalPassage` | struct | `holonic-membrane/src/live_current.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverCausalPassageError` | enum | `holonic-membrane/src/live_current.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverChartIdentity` | struct | `holonic-membrane/src/live_current.rs` | different object | an identifier/address (name-inferred) |
| `NativeReceivedWire` | struct | `holonics-hna/src/native.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `GeneratorPhaseReceiverBinding` | struct | `holonics-hna/src/native/coupled_wave/body/field/incident/machine_receiving.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `IncidentTextReceiver` | struct | `holonics-hna/src/native/field_session/incident_receiver.rs` | active receiver Holon | the codec boundary with learned text/support normal materials: an active learned receiver; its power declaration is owed (hna incident owner, not touched in this phase) (source-inspected) |
| `GeneratorTextReceiver` | struct | `holonics-hna/src/native/field_session/incident_receiver/phase.rs` | active receiver Holon | wraps `IncidentTextReceiver`; the same owed declaration (source-inspected) |
| `ReceivingRowReading` | struct | `holonics-hna/src/native/field_session/measurement.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `PendingWaveReceive` | struct | `holonics-hna/src/native/wave_control.rs` | different object | a pending current wire record (source-inspected) |
| `ReceiverWire` | enum | `holonics-hna/src/native/wire.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverClosedTrace` | struct | `relational-geometry/src/decorated_path.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverCrossingMark` | struct | `relational-geometry/src/decorated_path.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverDartFace` | struct | `relational-geometry/src/decorated_path.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverIntervalFace` | struct | `relational-geometry/src/decorated_path.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverTransitionFace` | struct | `relational-geometry/src/decorated_path.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ComplexReceiverBox` | struct | `relational-geometry/src/exact_analysis/types.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `Receiver` | struct | `relational-geometry/src/projection.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `ReceiverGauge` | struct | `relational-geometry/src/projection.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverId` | struct | `relational-geometry/src/projection.rs` | different object | an identifier; the three `ReceiverId(u64)` name distinct ID spaces and are not aliased (source-inspected) |
| `ReceiverMetric` | struct | `relational-geometry/src/projection.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverOrientation` | struct | `relational-geometry/src/projection.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverOrientationError` | enum | `relational-geometry/src/projection.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverRotationAxis` | enum | `relational-geometry/src/projection.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `GrainedReceiver` | struct | `relational-geometry/src/receiver_atlas.rs` | passive coholon | a declared reading (name-inferred): a passive coholon unless it returns a current |
| `JointReceiverAtlas` | struct | `relational-geometry/src/receiver_atlas.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceivedOccurrence` | struct | `relational-geometry/src/receiver_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceivedSwing` | struct | `relational-geometry/src/receiver_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverAtlasEmanation` | struct | `relational-geometry/src/receiver_atlas.rs` | different object | an event/world/program chart of a receiver-named system (the occurrence Holon's event chart), not a port object (name-inferred) |
| `ReceiverAtlasError` | enum | `relational-geometry/src/receiver_atlas.rs` | different object | a refusal/status (name-inferred) |
| `ReceiverAtlasFace` | struct | `relational-geometry/src/receiver_atlas.rs` | receiver face (codec) | a readout/face value (codec projection) of a receiver (name-inferred) |
| `ReceiverGrain` | struct | `relational-geometry/src/receiver_atlas.rs` | receiver face (codec) | a grain/aperture declaration of a face (relational-geometry: pixel grain; holonic-life: a return grain enum) (source-inspected) |
| `ReceiverTopology` | struct | `relational-geometry/src/receiver_topology.rs` | receiver face (codec) | a receiver chart/aperture geometry (where a face is read), not a port object (name-inferred) |
| `ReceiverTopologyError` | enum | `relational-geometry/src/receiver_topology.rs` | different object | a refusal/status (name-inferred) |
