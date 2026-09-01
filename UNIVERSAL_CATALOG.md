# Universal Lean–Rust–CUDA catalog

**Status:** descriptive navigation maintained with owner changes. This catalog schedules nothing,
grades nothing by itself, and has no generator or release gate. The roadmap and construction state
remain the only scheduling authorities.

## Reading rule

Each row connects one mathematical relation to its live formal and executable presentations.

- **exact** means the named implementation owns the same stated carrier/law in the row's declared
  scope;
- **partial** means the implementation owns a receiver projection or strict subset;
- **formal-only** means no Rust/CUDA realization is admitted;
- **UAR-open** means the implementation is the intended owner but the stated R0Q fibre remains open.

Paths are stable owner addresses, not line citations. A hash, filename, count, output artifact, or
test result never upgrades a correspondence.

## Foundation and transport

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Addressed passage and both boundary maps | `soma/formal/elementary-holonics/ElementaryHolonics/Foundation/Lineage.lean`; `soma/formal/elementary-holonics/ElementaryHolonics/Foundation/AddressedBoundary.lean` | `soma/life/src/mathematical_particle/lineage.rs`; `soma/life/src/addressed_span.rs`; `crates/holonic-engine/src/realization/passage.rs`; `soma/life/src/athena_native/source_neutral_relational/pair_current.rs` | `crates/holonic-engine/src/cuda_refine/membrane_addressed_current.rs` | **exact** for the R0Q1 apparatus-neutral response/source/target pair fibre; resident realization transport is R0Q2 |
| Holon composition and retained middle boundary | `Foundation/Holon.lean` | `realization/passage.rs`; `holonic_complex.rs` | `cuda_refine/membrane_factored_transport.rs` | **partial:** runtime composition exists; complete realization-site fibre is R0Q0 |
| Receiver face and quotient fibre | `Foundation/Receiver.lean`; `Foundation/ReceiverQuotient.lean`; `Foundation/BoundaryReceiver.lean` | `receiver.rs`; `receiver_exact_compression.rs`; `founded_receiver.rs` | `cuda_refine/membrane_factored_receivers.rs`; `membrane_receiver_completion.rs` | **exact** for bounded receiver quotients; richer families may reopen fibres |
| Transport lift and lawful descent | `Foundation/TransportLift.lean`; `Foundation/LatticeTransport.lean` | `inverse_transport.rs`; `reduction_junction.rs`; `embedding_fiber.rs`; `rebase_invariants.rs` | `membrane_factored_transport.rs`; `membrane_factored_descent.rs` | **partial:** every descended generator still owes a commuting square in its declared carrier |
| Chain, product, and higher incidence | `Foundation/DiagonalChainTransport.lean`; `Foundation/ProductDegreeTwo.lean` | `holonic_complex.rs`; `derivation_two_cells.rs`; `derivation_atlas.rs` | `membrane_generated_transport.rs`; `membrane_joint_boundary.rs` | **partial:** complete higher-cell pullback lineage is receiver-dependent |

## Computation, receiver history, and cultivation

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Exact finite diffusion and state-space chart | `Computation/HolonicDiffusionCharts.lean` | `diffusion.rs`; `sheaf_diffusion.rs`; `causal_body.rs` | `cuda_refine/membrane_boundary_*`; `membrane_factored_transport.rs` | **partial:** Lean Markov/deterministic separation is broader than one resident runtime owner |
| Finite neural ecology local-current step | `Computation/HolonicNeuralEcology.lean` | `soma/life/src/dialogue_native_spool.rs`; `soma/life/src/athena_native/rest.rs`; `soma/life/src/athena_native/conduct.rs`; `native_ecology/mod.rs`; `native_ecology/inference_ecology.rs`; `native_ecology/recurrent.rs`; `native_ecology/continuation.rs` | `cuda_refine/device_recurrence.rs`; `cuda_refine/complex_parametron.rs`; `device_ecology_types.rs` | **exact** for the complete visible-exchange native spool and compact K3 batch; situated cultivation into the source-neutral rest remains R0Q5-open |
| Dynamic receiver quotient and every-word law | `Computation/MachineLearningChart.lean` | `receiver_history_compression.rs`; `receiver_history_cultivation.rs`; `receiver_exact_compression.rs` | `cuda_refine/membrane_receiver_completion.rs` | **exact** for admitted bounded quotient systems; R0Q3 adds the missing realization complex section |
| Dependent changing carrier | `Computation/DependentMachineLearningCarrier.lean` | `native_ecology/heterogeneous_fusion.rs`; `native_ecology/factor_complex.rs` | `device_ecology_types.rs`; `complex_parametron.rs` | **partial:** current UAR carrier drops response/source incidence before realization |
| Situated returned difference | `Computation/SituatedMachineLearning.lean` | `soma/life/src/athena_native/situated_difference.rs`; `exchange_situated_product.rs`; `source_neutral_relational/realization.rs` | `cuda_refine/complex_parametron.rs`; `athena_integrated_front.rs` | **UAR-open:** UAR3 must use actual emission/return occurrences and nontrivial charts |
| Eros cultivation and Athena rest | `Computation/ErosAthenaNeuralObjects.lean`; `Computation/HolonicCultivationCharts.lean` | `cultivation_derivation.rs`; `receiver_history_cultivation.rs`; `native_ecology/cultivation_overlay.rs`; `soma/life/src/athena_native/source_neutral_rest/`; `situated_cultivation/` | `athena_integrated_front.rs`; `complex_parametron.rs`; `membrane_moment_*` | **UAR-open:** direct source-neutral remount, attributable child, withdrawal, and later conduct |
| Evolution species and open exterior | `Computation/HolonicEvolutionKinds.lean` | `evolution.rs`; `world.rs`; `causal_body.rs` | `device_inference_world.rs`; `device_recurrence.rs` | **partial:** real, imaginary, Markov, physical-boundary, and open species are not one Rust enum by design |

## Holonic Intelligence Framework

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Intrinsic holon dimensions and profile | `Computation/IntrinsicHolonProfile.lean` | `native_ecology/holonic_intelligence` over `native_spool/thread.rs`, `native_spool/deposits.rs`, `native_anatomy.rs` | apparatus work remains separate under `resident_section.rs` | **exact** for bounded `NativeSpoolBundle`: every facet is borrowed and unknown scale/apparatus dimensions return typed open faces |
| Rested transport, inference cut, and cultivation lifecycle | `Computation/HolonicIntelligenceLifecycle.lean` | `native_ecology/holonic_intelligence`; partial implementations in `native_spool`, `native_ecology`, `soma/life/src/athena_native/`, and `holonic_training.rs` | `device_recurrence.rs`; `complex_parametron.rs`; `athena_integrated_front.rs` | **exact** for native bundle profile/rest/conduct/remount; concrete inference and cultivation trait implementations remain HIF3/HIF4 |
| Foreign dismantling return and cold-witness independence | `HolonicIntelligenceLifecycle.DismantlingReturn` | `native_ecology/holonic_intelligence::DismantlingBoundaryReturn`; `soulkiller/scrapyard.rs`; `soulkiller_witness.rs` | none at the cold boundary | **exact** for the three physical lanes; exact format adapters and productive profile receipt remain HIF2 |
| Exact foreign weight, residual, and preimage fibre | `Computation/ExactForeignWeight.lean` | `foreign_map.rs`; partial BF16 precedent in `athena.rs`; `embedding_fiber.rs` | format-specific resident mouths only | **formal-checked; partial:** manifestation exists; one generic exact codeword-to-native passage and ONNX/config intake remain HIF1/HIF2 |
| Current-founded versus fixed contact chart | `IntrinsicHolonProfile.ContactScheduleChart` | neutral lifecycle surface plus partial incidence owners in `native_spool`, `native_ecology`, `physical_constraint_complex`, and `soma/life/src/athena_native/source_neutral_relational.rs` | `complex_parametron.rs`; addressed junction owners | **formal-checked; partial:** fixed and current-founded controls share no concrete executable chart; HIF3 owns generation comparison |

## Active R0Q correspondence

| Formal relation | Lean theorem owner | Rust/CUDA realization | Current status |
|---|---|---|---|
| `A_p(z,z')` addressed oriented transport | `soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicOrientedSiteTransport.lean` | `soma/life/src/athena_native/source_neutral_relational/pair_current.rs`; `soma/life/src/athena_native/source_neutral_relational/realization.rs`; future resident owner under `crates/holonic-engine/src/cuda_refine/` | **R0Q0/R0Q1 exact:** ordinary off-diagonal and boundary-diagonal fibres are retained; CUDA passage is R0Q2 |
| Linear target and `(port,factor)` junction before positive mass | `HolonicOrientedSiteTransport.postContractionPortMass_eq_norm_joined_current` | `crates/holonic-engine/src/cuda_refine/addressed_complex_junction.rs`; `soma/life/src/athena_native/source_neutral_relational/realization.rs` | **R0Q2 exact:** resident arbitrary-width complex join precedes the positive receiver with zero intermediate semantic egress |
| Equal positive shadow does not imply complex equality | `HolonicOrientedSiteTransport.norm_before_linear_join_is_not_postContraction`; `SituatedMachineLearning.equalLoss_differentReturn_obstructsDescent` | `SourceNeutralContinuationState` in `soma/life/src/athena_native/source_neutral_rest/wire.rs` | **R0Q3 exact:** selected complex section and addressed pair fibre participate in structural recurrence |
| Receiver/history equality commutes with every ordered word | `MachineLearningChart.DynamicReceiverChart.everyOrderedWordExact` | `receiver_history_compression.rs`; `source_neutral_rest/wire.rs` | **partial:** bounded quotient exact; realization complex signature missing |

## Quantum and physical formalizations

| Relation | Lean owner | Rust owner | CUDA owner | Status and exact open fibre |
|---|---|---|---|---|
| Fermionic occupation and CAR | `Computation/HolonicFermionicOccupation.lean` | — | — | **formal-only:** finite Fock occupation, signed creation/annihilation, CAR |
| Finite Fermi–Hubbard transport | `Computation/HolonicFermiHubbard.lean` | — | — | **formal-only:** Hermitian Hamiltonian and particle-number sectors |
| Coherent polarized-crystal paths | `Computation/HolonicPolarizedCrystalTransport.lean` | — | — | **formal-only:** retained path fibres, Jones transport, analyzer/intensity order |
| Simulation assurance and eigenpair residuals | `Computation/HolonicSimulationCertificate.lean` | nearest bounded owner: `exact_owner_testimony.rs` | — | **formal-only correspondence:** external producer/checker boundary remains explicit |
| Constructive differential boundary calculus | `Computation/HolonicConstructiveDifferentialBoundary.lean` | partial: `exact_linear.rs`; `running_integral.rs`; `soma/life/src/reconstruction_fiber.rs` | — | **partial:** no Rust owner for the square-zero jet and complete standard/residue receiver |

## Maintenance law

Update a row in the same coherent change that moves, adds, or removes one of its owners. Do not
generate this file from imports, filenames, symbols, or hashes: correspondence is a mathematical and
implementation judgment. If a proposed row cannot name the common carrier and the exact open fibre,
leave it out until that relation is understood.
