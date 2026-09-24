# The Holon core founds the native machinery

[project-postulate] Brandon, September 22: the Holon is the foundational object of the Lean
mathematics and the foundational class of the Rust codebase; every HNN mechanism is built on it,
through a refactor and consolidation. Object: [elementary objects](../ELEMENTARY_OBJECTS.md#the-holon-as-one-object),
[refinement](../../research/records/2026-09-22_THE_HOLON_IS_AN_INTERCONNECTED_PORT_OBJECT_ON_A_COMPLEX.md).
This plan records the facet survey of the native tree and the proposed core, pending approval of the
restructuring phases.

## What already exists (source-inspected survey, September 22)

[established-bounded; source-inspected] `holonic_interaction::HolonicInteraction` already holds most
of a Holon: storage form (`Medium`, `SymmetricForm`), skew interconnection (`Medium.structure`,
`Coupling` — "the port-Hamiltonian interconnection"), resistive contacts (`ContactFace`,
`ContactDissipation`, `HelicalPairInteraction`), a source port (`SourceCurrent`) and a participating
receiver with its own storage and skew structure (`Perspective`, `ReceiverBody`). Missing everywhere:
ports carrying flow–effort pairs, an explicit Dirac type with composition, and a stepping motion on
the law (only linearization/transfer/poles exist). Duplication found: 27 `*Complex` types; five power
readings (`TellegenReceipt`, `StorageRateReading`, `ClockedEnergy`, `PowerStations`,
`DiffusionEnergyBalance`); three clocks (`Clock`, `ClockSpec`, `JointClock`); name collisions
(`GeneratorFamily` ×2, `Generator`, `SiteKind` ×2); ~351 receiver-named public types; two exact
linear-map types (`ExactRatMatrix`, `sheaf_diffusion::ExactLinearMap`). No pump schedule or LC loop
owner exists; the resident parametron is a limb-exact product body without metric phase.

| Facet | Best existing owner |
|---|---|
| Complex `K`, `∂_A` | `GradedCausalComplex` + `HodgeOperator`; connection from generator transports; device `NativeFieldDeclaredIncidence` (CSR + transpose) |
| Ports `Π` | `JointUnits` + `Quantity` for units; port-incidence role of `SourceCurrent`/`Perspective` |
| Interconnection `𝒟` | `HolonicInteraction` skew assembly; `junction_law::tellegen` |
| Element relations `𝓔` | `SymmetricForm`/`Inertia` (storage), `ContactFace`/`ContactDissipation` (resistive), `SourceCurrent` (source), resident normal material (active/learned); pump and LC loop absent |
| Generators `G` | `CompiledGeneratorSite` content: `SituatedScrew`, `RationalPhase`, `Clock`, `Odometer` |
| Receivers | `Perspective`/`ReceiverBody` (active); `receiver_release::Reading` (passive coholon) |
| Restriction `π` | `continuing_tower::{Tower, Transition, Migration}`, `continuing_tube::SquareDefect` |
| Motion | `ExactEventLaw` (event chart); `NativeCoupledBody` (resident) |

## The proposed core

[project-postulate; agent-inferred] A new crate `crates/holonic-core`, depending only on
`relational-geometry` and numeric/serde crates (builds without CUDA), exposed as `holonics::core` and
never glob-re-exported into the engine. Modules mirror the Lean foundation (`ElementaryHolonics/Holon/`):

```text
scalar       Rat reference field; DyadicBall (centre, radius, grain) — generalizes NativeFieldCurrentBall
complex      CellComplex (∂∘∂=0 validated; from GradedCausalComplex); Connection (d_A, curvature face)
port         PortUnits (flow, effort, power dimensions); Port; FlowEffort with power ⟨e,f⟩
dirac        DiracStructure { Kernel(F,E) | Incidence(B) | Skew(J) }; check (isotropic + maximal); compose (closure)
element      ElementRelation { Storage | Resistive | Source | Active{power declared} | Pump{schedule, clock} }; PowerTerm
generator    Generator { transport, initial configuration (the key), Clock, PhaseLift (Cayley phase + winding, carry) }
restriction  Restriction over Transition; Descent { Witness | Defect (retains interior/fibre) }
holon        Holon (the law); HolonState (a point); interconnect(a, b, joined ports) -> Holon
law          HolonLaw { advance, receive, interact, restrict, pullback } with EnergyBalance
             { stored_change, dissipated, port, active, deposition_work, discretization_defect, residual }
conformance  Tellegen; power balance (residual = 0 exactly); interconnection closure; restriction square;
             passive coholon = Reading; lossless winding carry; chart square (reference ∈ resident ball)
```

Reference motion: implicit midpoint for the skew-plus-quadratic part gives an exact discrete balance
(`discretization_defect = 0`); backward Euler reports its defect. The resident CUDA realization is a
chart: `ResidentHolonChart` compiled from a core `Holon` onto the existing CSR/D* layouts and
kernels, owing "exact reference value ∈ returned dyadic ball", not equality. `NativeCoupledBody`
keeps its API and delegates to the chart.

## Phases (each lands with its Lean counterpart or names the #62 obligation)

1. **Lean foundation** — `ElementaryHolonics/Holon/` (in progress).
2. **Core base** — move `ExactRatMatrix`, `SymmetricForm`, `Inertia` (and closure) into `holonic-core`
   with re-exports at old paths; replace `ExactLinearMap`.
3. **Holon from `HolonicInteraction`** — its parts become core facets; `declared` builds a core
   `Holon`; power readings become views of `EnergyBalance`.
4. **Complex consolidation** — `GradedCausalComplex`/`HodgeOperator` supply `K`; diffusion/current/
   resistive complexes become constructors; diffusion laws implement `HolonLaw`.
5. **Generators** — one `Clock` (`ClockSpec` its wire); `CompiledGeneratorSite` → core `Generator`;
   collisions renamed with aliases.
6. **Restriction** — tower/tube types move to `core::restriction`; grain/coarsening towers and
   `StandingLaw` become instances.
7. **Receivers** — `Reading` is the passive coholon; `Perspective`/`ReceiverBody` active receivers;
   normalized/pair receivers are active elements with their power term (landed; see the phase-7
   disposition below).
8. **Device chart and retention** — `ResidentHolonChart`; `NativeCoupledBody` delegates; the
   remaining history structures retire under the retention law; unconsumed body states are charted or
   retired after a consumer audit.

### Phase 4 disposition: every `*Complex` type against the core complex

[established-bounded; source-inspected] The workspace declares 27 `pub struct *Complex` types outside
`holonic-core` (three further matches are source text inside `holonic-life/driver-sources/*.json`).
Each is (a) a thin view over the core `CellComplex` (a chart method, the engine wire unchanged),
(b) a documented chart reached through another owner, or (c) a different object. Engine charts go
through `algebraic::{CoreCellChart, GraphChart, CoreChartRefusal}`
(`crates/holonic-engine/src/algebraic/core_chart.rs`): a `GradedCausalComplex` is read by the group
completion of its coefficients (`TryFrom<&GradedCausalComplex> for CellComplex`, and back through
`GradedCausalComplex::from_core` for integral boundaries); graph-shaped complexes through
`CellComplex::graph`. The core complex is `Serialize`-only, so a chart is always rebuilt from the
engine value through the core constructor, which re-certifies `∂∘∂ = 0`.

| Type | Owner | Disposition |
|---|---|---|
| `GradedCausalComplex` | `holonic-engine/src/algebraic.rs` | (a) `core_chart`, `TryFrom`, `from_core`; the engine's source presentation (caused, named cells; paired occurrence counts) |
| `SimplicialComplex` | `simplicial.rs` | (b) `core_chart` through `SimplicialIncidenceReceipt::realize` |
| `DiffusionComplex` | `diffusion.rs` | (a) `graph_chart` + `capacity_storage` (storage `C⁻¹`) + `conductance_relation` (resistive); the law's drop map is `−d₀` of the chart (duplicate incidence builder removed) |
| `DiscreteCurrentComplex` | `physical.rs` | (a) `graph_chart`; `conservation` is `∂₁ J`; a self-loop is refused (the receipt reads it once) |
| `GradedConstraintComplex` | `physical_constraint_grading.rs` | (a) `core_chart` of one family member |
| `PhysicalConstraintComplex` | `physical_constraint_complex.rs` | (b) a *family* of core complexes (one per open-contact resolution) through `graded_constraint_member`/`_family`; its vertex/edge/face tables are the material presentation |
| `CellComplex` (fold) | `fold.rs` | (a) `core_chart` through `graded`; kept as the vertex/edge/triangle presentation with its wire (the same role as the core type, not aliasable without breaking `CellComplexWire`) |
| `ContactComplex` | `contact_gluing.rs` | (a) `core_chart`; occurrences are named subcomplexes |
| `ReceiverGrainComplex` | `holonic_complex.rs` | (a) `core_chart`; cell witnesses are provenance |
| `CoPresentationComplex` | `collocation.rs` | (a) `core_chart` inside the aperture |
| `GrownComplex` | `grown_cell.rs` | (b) `complex.core_chart()` on its public field; growth censuses are provenance |
| `ExactConfigurationComplex` | `basin.rs` | (a) `graph_chart` (adjacency oriented `left → right`); measures and actions are element data |
| `SeparationComplex` | `token_invariance.rs` | (c) a longest-common-prefix order over window classes; no boundary |
| `SessionFactorComplex` | `native_ecology/factor_complex.rs` | (c) a device morphology session word, not incidence |
| `AddressedFactoredIntegralReceiverComplex` | `receiver_history_compression/factored_forms.rs` | (c) a pool of receiver functionals |
| `PortedOperationComplex` | `ported_operation.rs` | (c) an `EvolutionShape` event diagram: an event chart |
| `MoveComplex` | `move_species.rs` | (c) move records and their arrival DAG: an occurrence chart |
| `RatComplex` | `relational-geometry/src/exact_analysis/complex.rs` | (c) a complex *number* (`re`, `im`) |
| `EventComplex` | `holonic-body/src/incidence.rs` | (c) the borrowed event complex: the occurrence Holon's event chart (`Foundation/Holon.lean`) |
| `IncidenceComplex` | `holonic-life/src/incidence_production.rs` | (c) source-native material occurrence incidence with causal dependencies; an event chart |
| `ConsequenceComplex` | `holonic-life/src/holonic_training.rs` | (c) an acyclic route DAG of consequence boundaries |
| `TotalCaseComplex` | `holonic-life/examples/m6/case.rs` | (c) a case-cover receipt |
| `EditComplex` | `holonic-life/src/reconstruction_fiber/edit.rs` | (c) the minimal edit-path DAG |
| `NativeCultivatedPotentialComplex` | `holonic-life/src/native_intelligence/cultivated.rs` | (c) a direct-sum potential current receipt |
| `NativeProsePotentialComplex` | `holonic-life/src/native_intelligence/perspective_emanation.rs` | (c) a native section/contact receipt |
| `NativeAcousticPotentialComplex` | `holonic-life/src/native_intelligence/membrane_acoustic/potential_formation.rs` | (c) a native port/current receipt |
| `NativeMathematicalComplex` | `holonic-life/src/mathematical_particle/production_aperture/native_consequence_types.rs` | (c) lists of operation/constraint/geometry cells as a receipt |

The mixed incidence/constitution types that are not named `*Complex`: `HodgeOperator` is (b)
`core_chart` + `metric_storage` (the declared metric as positive storage), with its `d`, `δ` and `Δ`
equal entry for entry to `CellComplex::{coboundary, codifferential, hodge_laplacian}`;
`ResistiveNetwork` is (a) `core_chart` + `conductance_relation`, and `junction_law::tellegen` equals
`holonic_core::dirac::tellegen` on the chart; `Interface` is (c) a declared side split of flux cells
over an operator (a port partition, not a complex); `ExactCellularSheaf` exposes its base
`core_chart`, its rank-one coboundary is the core `d`, and higher stalks are a matrix-valued
incidence; `HingeTransportNetwork::core_connection` is the core `ConnectionIncidence` for scalar
dilation turns, whose curvature face equals the hinge world's cycle-return displacement, and refuses
a general `PGL(2,ℚ)` turn. Owed: a matrix-valued core connection (projective turns, affine cell
transports and higher sheaf stalks), for which the scalar determinant line is the present reading.

### Phase 6 disposition: restriction as one owner

[established-bounded; source-inspected, implemented-exact] `continuing_tower` moved whole to
`holonic_core::restriction::tower` (it depended on no engine owner). `continuing_tube`'s carrier law
(`StationedTower`, `check_commuting_square`, `SquareVerdict`, `SquareDefect`, circuit holonomy,
wormhole receipt, `ConstantTube`/`FlipTube`/`LossySwapMigration`) moved to
`holonic_core::restriction::tube`; the engine file keeps the grain and presentation tubes and the
horizon/profile/route layers, because they read a tube through `receiver_release`'s `Horizon`,
width and `ExactFace` and `relation_ladder::Rung` (phase 7 territory). Both engine paths re-export
every moved item. The two square defects are one object: the tube's per-face
`SquareDefect::route_difference` is `restriction::SquareDefect::at` at the source face
(`LinearTube`; Lean `squareDefect_mulVec_eq_zero_iff`). `restriction::Descent { Witness, Defect }`
(Lean `Holon/Restriction.lean::{Descent, descent_total}`) is built on `Transition::residual` through
`square_descent`, `tower_square_descent` and `factor_descent`; its engine instances, each tested
equal to the existing reading, are `SquareVerdict::descent` on the grain tube (with `GrainTower`'s
restriction residual), `CoarseningTower::descent` (first break = `CoarserDoesNotFactor`; a
`FactorMap` is a witness's induced reading), `standing::sufficiency_descent` (through
`StandingLaw::restriction`, a rank-tolerant `LinearRestriction`) and
`receiver_exact_compression::one_shot_descent` (breaks = collapsed pairs). The engine's only
Schur/Dirichlet-to-Neumann owner, `diffusion::compile_diffusion_transfer`, now reads `L_II⁻¹` and
`Λ_DN` off `KronReduction`; `causal_reflection.rs` is Kramers–Kronig (dispersive/absorptive
reflection), not an interior elimination, and has no Kron reading.

### Phase 7 disposition: receivers as Holons at ports

[established-bounded; source-inspected, implemented-exact] The core receivers live in
`holonic_core::law::receiver` (`crates/holonic-core/src/law/receiver.rs`; Lean `Holon/Law.lean`
§2–2b). **Passive coholon:** `PassiveCoholon` (a named linear reader `C` on the passive-coholon
Dirac structure) reads `C e` at zero power (`passive_reading`); `coholon_bond` is the bond any
reading, linear or not, stands on (`coholon_reading_power`); `HolonLaw::receive` delegates to it.
`receiver_release::{Reading, LinearReading}` and `standing::ReceiverReading` are this object:
each converts (`passive_coholon()`) with equality tests of the value, and the passive coholon is
itself a `Reading` and a tube `FaceReading` on effort-vector faces. **Active receiver:**
`ActiveReceiver` with `ReceiverPower { Reading | Learned(ActiveRelation) | ExteriorDrive |
Pullback }`; its `ReceiverExchange` closes its own balance exactly (`exterior_drive_balance`,
`learned_receiver_balance`, `pullback_law`) and the delivered power joins a Holon's
`EnergyBalance` through `EnergyBalance::joined_active`. `Perspective`/`ReceiverBody` remain the
phase-3b joined Holons. The native normalized, phase and pair receivers and their adjoints
(`field/receiver/normalized{,/section,/phase,/pair,/pullback}.rs`) declare
`receiver_element()`: the normalized face is a nonlinear reading at zero power, its covector
return a pullback through the symmetric `J_p = diag p − p pᵀ` (`softmaxJacobian_transpose`,
`softmax_pullback_power`), and the phase/pair participations exterior drives whose delivered
power `⟨e_D, y⟩` is enclosed host-side from the returned balls (`delivered_power`); no kernel,
launch or value changed. **Receiver face:** `ExactFace`, `DiameterNorm`, `ReceiverWidth`,
`WidthWitness`, `width_over_readings`, `Horizon`, `WidthRefusal` (with its claims) and the
relation ladder's `Rung`/`rung_meet` moved to the core and are re-exported at their engine paths;
wires are unchanged, and the engine's enclosure width is built through the validating
`ReceiverWidth::declared`. **Tube layers:** with those faces in the core, the two-axis horizon,
defect profile, cross-rank passage and route plan moved to
`holonic_core::restriction::tube::horizon` (re-exported by `continuing_tube`); the engine keeps
only the tubes over engine material — `GrainReadingTube` (over `grain_tower`),
`PresentationTube` (over `physical_constraint_complex`) and `GrainContactCount` — because their
sections are engine presentations, not because of a receiver dependency. The disposition of all
361 receiver-named public types is [its own table](THE_HOLON_CORE_RECEIVER_DISPOSITION.md): 19
passive coholon, 9 active receiver Holon, 158 receiver face, 175 different object; one genuine
duplicate (an orphan uncompiled copy of `ResidentIntervalPotentialReceiver`) was removed, and
the `LinearReading`/`ReceiverReading` pair is one object kept under both public names. Owed: the
power declarations of the remaining name-inferred active receivers (`IncidentTextReceiver`,
`GeneratorTextReceiver`, `NormalWaveFamilyReceiver`), and a consumer that feeds a participation's
enclosed delivered power into the resident field's balance (phase 8's chart).

### Phase 8b disposition: body states and retained history

[established-bounded; source-inspected] `NativeCoupledBody`
(`crates/holonics-hna/src/native/coupled_wave/body.rs`) has four `BodyState`s. Every one has a
live public caller, so none is retired; each is a chart of the core `Holon` whose
`HolonState.configuration` is the resident current and `HolonState.commit` the body `epoch`.

| State | Entered through | Live callers | Test-only callers | Core `Holon` chart | Retained history |
|---|---|---|---|---|---|
| `Field` (`body/field.rs::FieldModel`) | `from_field`, `from_field_with_reaction_port`; rest tag 2 | `NativeFieldSession` charts `TensorCondition`, `JointRegions`, `SharedRegions`, `GeometricRegions` (`field_session.rs::found`) and `from_native_field` (`native_source.rs`); workbench `holonics hna field-session`; examples `athena_field`, `helical_field_generator`, `athena_exposure_field` (shared regions), `athena_geometric_spec`; drivers `research/experiments/athena_field/{geometric,pattern,session}` (`shared` keeps only its recorded run), `native_performance_benchmark/quality.py` | `field_session/{native_source,geometric}/tests.rs`, `coupled_wave/tests/boundary.rs` | storage = joint field current (`K` = field nodes); skew = operative reflection `D`; active = neighborhood bilinear reaction (normal material); source ports = boundary input + condition | occurrence clock fixed at the two foundation occurrences; pending comparisons are frozen producing sections (`FieldProducingSection`: source cut, reaction enclosure, input, output) |
| `Incident` (`body/field/incident.rs::IncidentFieldModel`) | `found_incident_field` (chart `IncidentField`), `found_generator_field` (chart `GeneratorMachine`); rest tag 3 | `field_session/{incident_application,generator_application}.rs`; workbench `field-session`; examples `athena_exposure_field`, `athena_geometric_spec`, `support/generator_machine.rs`; drivers `quality.py` (`incident-field`), `athena_field/geometric/run.py` | `incident_tests.rs`, `incident/*/tests.rs`, `incident_application_tests.rs` | complex = declared site incidence (CSR + transpose); storage = joint `q/b`; skew = declared contact action `D = B_U*`; active = reaction material under `ReactionLaw` (power-neutral: `core::reaction` projections); source port = moment `m` and condition `c` through `I`; generators = compiled machine sites; receivers = the phase-7 normalized/phase active receivers | source-only field, no occurrence clock; generator comparisons are the moment quotient (`\x04`); legacy-slot comparisons are frozen words (`\x01`) |
| `Affine` (`ResidentNormalWave<NormalWaveCoupled>`) | `from_wave`; rest tag 0 | `NativeCoupledWaveSession` (`coupled_wave.rs`); workbench `holonics hna coupled-wave-session`; `HnaStream::pump_coupled_wave` | `coupled_wave/tests{,/boundary}.rs` | storage = (previous, current) wave pair; active = normal material; source ports = admitted member contacts per `WaveSourceReceiver` | pending coupled predictions keep their `relation_cut` (engine owner) |
| `Constitutive` (`ResidentCoupledConstitutive`) | only `Affine::incorporate` and rest tag 1 | the same coupled-wave session after its first incorporation | `coupled_wave/tests.rs` | the source-dependent generator continuation of the same Holon (its parameter generator is the active relation) | retained ordered generating word for prospective reads (engine owner) |

`from_incident_field` (`incident.rs`) has no caller in the workspace, examples, applications or
drivers; it is proposed for retirement with the incident owner (phase 8a's file).

[established-bounded; source-inspected, measured] **Occurrence history.**
`NativeConstitutiveField.history` grows only in `advance_with` (the constitutive `advance*`
passage). A source-only field refuses that passage ("source-only field has no legacy
constitutive advance") and its rest refuses history ("source-only field has legacy history").
Every incident and generator-machine body founds `found_incident_source_only`
(`incident.rs::found_incident_field`, `incident/machine.rs`), so **no live HNN path adds
occurrences**. The legacy constituted-field session founds exactly two occurrences
(`field_session.rs::found`: entering, then through) and, once attached, `FieldModel` exposes no
advance: generation commits reflections and the reaction material, so the count stays fixed.
The occurrence clock remains on the legacy constituted-field chart because engine drivers and
source/material readers consume its actual receivers. The exterior occurrence-placement ladder
(`FieldArchive`, `enable_history_archive`, `archive_history_before`, and
`remount_with_history_archive`) had no live non-test callers and is retired. Rest writes each
current historical carrier directly and ordinary remount restores those carriers resident. Tests:
`field/rest/tests.rs::source_only_field_refuses_occurrences_at_runtime_and_at_rest` (runtime
refusal, empty rest, remount, and grafted legacy occurrence refused) and
`body/field.rs::compatibility_tests::attached_field_occurrence_clock_is_fixed_through_generation_return_and_rest`
(the delivered `athena_field/one-pass` wire decodes with two occurrences, two generate/return
cycles and a rest/remount with one pending comparison keep two). Engine drivers
(`native_material_mode`, `native_internal_mode`, `native_conditioned_phase`) and the hna
measurement examples (`native_neighborhood`, `native_generator`) still grow the clock by their
own `advance_status` loops; the linear-emission, anchor, internal-current and context readers
consume it, so it is not removed.

[established-bounded; source-inspected] **Frozen incident cuts are not retired.** The `\x01`
pending word (`IncidentWord` with its material views, anchor, solve steps and output) is produced
only by the legacy-slot `IncidentField` chart and consumed by a public contract:
`field_session/incident_application.rs` freezes its own text/support/cohort receiver beside it
(`incident_application/rest.rs`: `frozen_text`, `frozen_support`, `frozen_cohorts`),
`inspect_incident_comparison` promises "the produced features … not a recomputation with
contemporary material", and
`incident_application_tests.rs::public_incident_session_reopens_frozen_receiver_after_intervening_update`
asserts the frozen faces survive an intervening update and a rest/reopen. Replacing the body word
alone with a contemporary reading would split that pair. The retirement is one joint packet over
the body (`incident.rs::publish`/`word`, `incident/machine_episode.rs::retained_comparison`,
`incident/rest.rs`: retain `(boundary, held, admitted, epoch)` and rebuild the word at the
contemporary field/material on return, as `contemporary_comparison_word` does for moments; write
a new tag and keep reading `\x01`) and the session receiver (read at contemporary material, with
the test's contract restated). The legacy constituted field's `FieldProducingSection` is the same
object class, consumed by the text charts' observe; it is recorded here and not retired. Owed:
that joint packet, and the `ResidentHolonChart` delegation, which remains unimplemented.

Constraints: rest/wire compatibility for `SavedCoupledBody`, `NativeIncidentModelRest`,
`CoupledConstitutiveRest`, the complex schema string and custom deserializers; interaction types stay
`Serialize`-only so no wire mints an unchecked object; no device layout change during consolidation;
public names kept; the Lean citation scan extended to `holonic-core`.

## Consolidation programme (phases 9–16)

[established-bounded; source-inspected] September 22 sweep (6,001 public types; suffix counts Receipt
268, Error 263, Reading 179, Refusal 136, Return 121, Rest/Wire 92, Fibre 74): the same growth pattern —
one wrapper per operation around a single object, each with its own Step/Reading/Rest/Refusal/Handle/
Prediction/Comparison ladder, often holding frozen producing cuts — recurs across the tree. Brandon's
standing request is consolidation onto the Holon objects with all mathematics and functionality kept.

| Phase | Cluster | Size | The one object | Retention debt |
|---|---|---|---|---|
| 9 | engine `material_transport/normal/**` and its hna consumers | 65 files, ~22k lines, ~70 types | normal-law constitution `W H = B` and its motion | producing handles, comparisons, continuations |
| 10 | core `Descent::Defect{fibre, separator}`; the ~14 reconstruction/preimage fibres and 19 separators | across life, native_ecology, spool, soulkiller | restriction descent with retained fibre | none |
| 11 | engine `constitutive_fibre/resident/**` views | 34 files, 9.5k lines | the constitutive relation (onto phase 9's object) | anchors retained in wave observation |
| 12 | HNN field session: hna `field_session*`, `coupled_wave/**`; engine `junction/operative/**`, `material_transport/{complete,contextual,moment,support}`, `archive`, `current_history_source`, `contextual_lift`, `rest` | hna 27k, junction 16k, material 5k lines | the resident field Holon; `ResidentHolonChart` lands here | heavy: frozen producing sections, pending rests, frozen receivers, occurrence kernels |
| 13 | device quadratic moment: `cuda_refine/membrane_*`, `factored_moment/`, `receiver_history_compression` staging | 25k + 2k + 6k lines | `Σ w f f*` storage on the device | occurrence-addressed staging |
| 14 | cultivated body: `native_spool`, engine `native_ecology` stages (5 files have no external consumer), life `native_intelligence/**`, `production_aperture/**` | 5k + 8.5k + 53k + 5k lines | one body with deposition (core `deposition`) | predecessor rests, deposit lists, identity histories |
| 15 | Soulkiller operator ecology (two parallel session ladders) | 19k lines, 223 types | one source-neutral operator Holon | retained previous-cycle emission |
| 16 | event-law ladder (26 `ExactEventLaw` modules; 237 ladder types) and one `HolonRest` codec | 58k lines | the event chart of motion; one rest | `history`/`pending` in 8 modules |

Kept distinct: phase-4 (c) objects; the content of each event law (only its scaffolding unifies);
within-cycle adjoint checkpoints; the traversal frontier; retention-law-conformant rests
(`condition_contact`, `preimage`); receiver-history compression frames (the quotient itself);
`holonics::membrane`/`holonic-body` register carriage until the chart exists; `DepositLedger`; legacy wire
decoders. Each phase: disposition table, equality tests, caller migration, deletion, full suites.

### Phase 9 disposition: the normal constitution stack is one Holon

[established-bounded; source-inspected, measured] Scope: `holonic-engine/src/native_ecology/
constitutive_fibre/field/material_transport/normal/**` and its consumers (`holonics-hna`
`coupled_wave/body.rs`, `normal_wave.rs`, examples `normal_wave`, `conversation_wave`,
`conversation_coupled`). Before: 90 public structs/enums + 1 alias, 23,208 lines. After: 72
public structs/enums + 9 compatibility aliases, 23,397 lines (the growth is the new equality and
conformance tests and facet documentation). Every enclosing module now re-exports the single list
`normal::api` instead of three hand-copied lists. No kernel, device layout or wire field of an
existing format changed; one new wave rest version (v11) was added.

**Facets.** *Constitution*: `NormalConstitution` (was `NativeNormalMaterialState`, `constitution.rs`)
is the element relation `W H = B` with `storage_form()` (realified `H`), `element()` (core
`ElementRelation::Storage`), `stored_energy()` and `deposition_work(successor)` (core
`element::deposition_work`); `ResidentNormalMaterial` is its one device chart (a clone is the
retained cut; `ResidentNormalMaterialView` is an alias and the duplicated view/material method
set was merged); `NormalMaterialRest` its one rest. *Motion*: `NormalWaveHolon` implements core
`HolonLaw`: the applied word `x⁺ = T x`, `T = [[0, I], [M_p − M_d, I + M_d + M_c]]`, is the
implicit-midpoint step of the medium with Cayley generator `A = 2(T − I)(T + I)⁻¹` (skew part the
interconnection, symmetric part the declared active relation); its advance equals `T x` exactly
with a zero-residual balance, and the chart square test checks the exact advance lies in the
device ball for three applied words. Every other wave motion returns the one receipt
`NormalWavePassage` (kind: actuate, develop, receive, reference, pullback, transport) with one
reading `NormalWavePassageReading`; the state is `NormalWaveState`. *Interconnection*:
`NormalWaveHolon::interact` is core interconnection; every coupled motion returns one
`NormalCoupledStep`. *Readings*: `readings.rs` holds every reading and codec face value; the
family and basis receivers declare `receiver_element()` (passive readings; the phase-7 owed
declaration for `NormalWaveFamilyReceiver`). *Refusal*: one `NormalRefusal<T> { returned, reason }`.

**Retention (one cut).** A plain-wave prediction retains only its source joint `(p, c)`; the
return (`pullback(id, v)`) reads the forward response, the fit and the updated response at the
contemporary constitution and transport. `delayed_return_is_one_cut_equal_to_an_immediate_return`
proves a delayed return equals the return at the same cut number for number and that its source
response is `P φ` of the contemporary `P = B H⁻¹` (9/10 in the witness; the retired producing cut
read 1). Pending sources rest as v11; version 5's frozen producing-cut decoder is retired.
Version 6 remains the current no-pending Applied-transport rest, while versions 7–10 remain
coupled forms. Owner-capability handles are
retired: pending returns are addressed by epoch in the plain and coupled waves.

| Former type | Disposition |
|---|---|
| `NativeNormalMaterialState` | renamed `NormalConstitution` (alias kept) |
| `ResidentNormalMaterialView` | alias of `ResidentNormalMaterial` (Clone); duplicate delegations deleted |
| `NormalRealizationRefinement` | retired: `refine_realization` returns the predecessor constitution |
| `NativeNormalMaterialObjective`, `NativeNormalMaterialReading`, `NativeNormalPrior`, `NormalMaterialRest`, `NormalSourceChart` | kept (constitution readings/rest/chart; readings moved to `readings.rs`) |
| `NormalWaveJointSource`, `NormalWaveStep` | aliases of `NormalWaveState` (the Holon state) |
| `NormalWaveSource` | retired: `read_source()` returns the lifted `ResidentNormalEnclosure` |
| `NormalWaveWord` | alias of `()` (the plain wave has no continuation state) |
| `NormalSourceActuation`, `NormalWaveDevelopment`, `NormalWaveReception`, `NormalWaveReference`, `NormalWaveComparison`, `NormalWaveTransportChange` | retired into `NormalWavePassage` |
| `NormalWaveReceptionReading`, `NormalWaveReferenceReading`, `NormalWaveComparisonReading` | retired into `NormalWavePassageReading` |
| `NormalProducingHandle`, `NormalWavePrediction` | retired: `predict() -> (id, state)`, `pullback(id, v)` (one cut) |
| `NormalWaveReading`, `NormalWaveTransport`, `NormalWaveSeedKind`, `NormalWaveCurrent`, `NormalWaveFibre`, `NormalWaveRest`, `ResidentNormalWave` | kept (word reading, operator-family scope, seed chart, occurrence, generating fibre, the one rest, the device Holon) |
| `NormalWaveSeedRefusal`, `NormalCoupledAttachRefusal`, `CoupledConstitutiveRefusal`, `ConstitutiveSourceRefusal` | aliases of `NormalRefusal<T>` |
| `NormalCoupledReception`, `NormalCoupledSourceActuation` | retired into `NormalCoupledStep` |
| `NormalCoupledProducingHandle`, `NormalCoupledPrediction` | retired: `predict_contact() -> (id, step)`, id-addressed compare/observe/release |
| `NormalWaveCoupled`, `NormalCoupledContact`, `NormalCoupledStep`, `NormalCoupledComparison`, `NormalCoupledObservation`, `NormalFamilyComparisonRow` | kept (coupled continuation state, admitted contact, the one coupled receipt, the producing-family comparison and its empirical return) |
| `NormalCoupledContinuation`, `NormalContinuationPullback`, `NormalContinuationJoin` | kept, **not retired** (see below) |
| `ResidentCoupledConstitutive`, `CoupledConstitutiveRest`, `CoupledConstitutiveFamily`, `CoupledConstitutiveAlternative`, `ConstitutiveComparisonSection`, `ConstitutiveSourceFrame`, `CompiledCoupledJoint`, `CoupledJointEvaluation`, `CoupledJointReading` | kept: the dependent (θ-parameterized) continuation and its compiled joint (see below) |
| `NormalWaveFamily`, `NormalWaveFamilyRest`, `NormalWaveFamilyReceiver`, `NormalFamilyReceiverReading`, `NormalFamilySupport`, `NormalFamilyPullback`, `NormalReceiverCoordinates`, `NormalWaveFacePacket` | kept: the anchored affine family (a restriction/descent object whose fibre is the affine relation) and its receiver faces |
| `NormalWaveBasisChart`, `NormalWaveBasisFace`, `NormalWaveBasisReading`, `NormalBasisSelection`, `NormalBasisScore`, `NormalFamilyBasisFace`, `FamilyBasisSelection`, `FamilyBasisReading`, `NormalSectionBasisFace` | kept as codec receiver faces (values in `readings.rs`; faces declare their element) |
| `ResidentNormalEnclosure{,View,Section}`, `ResidentNormalInput`, `ResidentNormalReturn`, `ResidentNormalSectionReturn`, `ResidentHeldSection{,Rest}`, `NativeAffineGeometry{,Adjoint}`, `NativeRealification{,Adjoint}`, `NativeEnclosurePropagation` | kept: the constitution's device storage and section charts (brief: device section types stay) |
| `NormalReactionProjection`, `PowerNeutralCertificate`, `BoundaryMaterialSeed`, `BoundaryMaterialMaps` | kept (phase-8a reaction law; boundary codec seed) |
| new: `NormalRefusal`, `NormalWavePassage`, `NormalPassageKind`, `NormalWavePassageReading`, `NormalWaveHolon`, `NormalWaveState` (renamed) | the consolidated facets |

**Not retired, with evidence.** The coupled continuation still retains its transport word
(`NormalWaveCoupled.transport`, rested as wave v9/v10 passages) and its pending producing
families. The dependent continuation (`ResidentCoupledConstitutive::evaluate_with_base_faces`,
`read_retained_word_pullback`) imposes a returned θ-face at the prediction's own epoch and carries it
through every intervening map to the contemporary family; a one-cut return has no such join, so
retiring the word changes what `incorporate` computes. In the live session returns are delayed as a rule:
`NativeCoupledWaveSession::emit_symbol` re-enters `(previous, current)` through `actuate_field`
immediately after every `predict_symbol` that follows an earlier emission, so a later
`incorporate_symbol` crosses at least one passage. Retirement is one joint packet over the coupled rest, the dependent continuation and the
session contract (tests `coupled_session_incorporates_observed_symbol_and_continues`,
`coupled_session_returns_original_base_prediction_after_restart`), as phase 8b recorded for the
incident `\x01` word. The θ-dependent programme re-evaluation of `ResidentCoupledConstitutive`
(its ordered `operations`) is the same debt. Owed: that packet; a device chart of reception and
actuation in `NormalWaveHolon` (the square covers the free applied word).

### Phase 10 disposition: the retained fibre and its separator

[established-bounded; source-inspected, implemented-exact] `holonic_core::restriction::fibre` owns
what a failed descent retains: `PreimageFibre<T, C, N>` (a class fibre `π⁻¹(t)`, Lean
`Foundation/Holon.lean::Holon.PreimageFibre`), `AffineFibre<N>` (`particular + span(radical)`,
checked by `check_preimage`; Lean `Holon/Restriction.lean::affineFibre_mem`), `Separation<M, W, V>`
(the Lean `Descent.defect x y merged separated`), `ShortestSeparator<M, I, R, O>` (a separation
witnessed by a shortest word and receiver, `Foundation/CausalRelevance.lean::futureHistory_quotientNe_returns_separator`)
and `FibreDefect<F, S>` (every retained fibre beside every separator; Lean
`Holon/Restriction.lean::descent_defect_refutes_factoring`). The factor descent's defect is now
`FibreDefect<PreimageFibre<T, Vec<usize>>, Separation<usize, (R, R), V>>` (`FactorBreaks`,
`FactorBreak` are aliases; the merged-pair count is `Σ C(|fibre|, 2)` over the retained fibres).
`Descent<W, D>` keeps its generic defect: square breaks retain a route difference and a fine
residual (holonomy), which is not a merged pair. A `FieldNames` marker (`fibre_field_names!`) keeps
each instance's wire — struct name, field names, unknown-field policy and `Debug` text — so an
alias serializes byte-for-byte as the struct it replaced. Before/after: 9 per-operation structs
deleted (`CollapsedPair`, observable `ReconstructionFibre`, `NativeCollapsedFibre`, `BoundaryFibre`,
`CondensedFibre`, `AffineReconstructionFibre`, `SectionSeparator`, core `FactorBreak`,
`FactorBreaks`), 5 core types added; 9 aliases; `*Fibre|*Fiber` structs/enums 78 → 75,
`*Separator` 20 → 20 (one deleted, `ShortestSeparator` added).

| Type (owner) | Disposition | Reading / reason |
|---|---|---|
| `FactorBreak`, `FactorBreaks` (core `restriction::descent`) | alias of `Separation`, `FibreDefect` | the defect now also retains every merged fibre |
| `CollapsedPair` (engine `receiver_exact_compression`) | alias `ShortestSeparator<ItemId, InputId, ReceiverId, Observation>` | same fields and serde name; wire test against the old derive |
| `ReconstructionFibre` (engine `receiver_history_compression::observable`) | alias `PreimageFibre<NativeStateId, BTreeSet<ItemId>, _>` (`native`/`sources`, unknown fields allowed) | field `.sources` → `.members` |
| `NativeCollapsedFibre` (engine `native_spool`) | alias `PreimageFibre<NativeStateId, BTreeSet<EventId>, _>` (`native`/`occurrences`, deny) | `.occurrences` → `.members` |
| `BoundaryFibre` (engine `native_ecology::recurrent`) | alias `PreimageFibre<NativeStateId, Vec<String>, _>` | `.source_sections` → `.members` |
| `CondensedFibre` (engine `native_ecology::recurrent_condensation`) | alias `PreimageFibre<u32, Vec<CondensedFibreMember>, _>` | same field names |
| `AffineReconstructionFibre` (life `situated_difference`) | alias `AffineFibre<_>` (`particular`/`kernel`) | `.kernel` → `.radical`; built by `ExactRatMatrix::affine_fibre` |
| `SectionSeparator` (life `causal_section`) | alias `ShortestSeparator<String, String, Option<String>, Option<String>>` | the collapsed pair read through the naming chart (`ShortestSeparator::map`); `interventions` → `distinguishing_word`, receiver/observations via accessors; no wire |
| `PrismaticEndpointFibre` (engine `holonic_chain::serial`) | holds an `AffineFibre` | adds joint limits and the source equation |
| `NativeExactReconstructionFibre` (engine `native_spool`) | `affine_fibre()`; `validate` delegates the fibre law to `AffineFibre::check_preimage` | wire keeps causal lineage, obstruction and support |
| `ExactLocalReconstructionFibre` (life `membrane_interior`) | `affine_fibre()`; construction checks through `check_preimage` | wire keeps the functional, partner and hidden difference |
| `NativeShortestSeparator` (engine `native_spool`) | `shortest_separator()` | wire has a flat, always-present witness |
| `CondensedSeparator`, `ReopeningSeparator`, `HistorySeparator`, `ForeignCoefficientWordSeparator`, `FactorSupportSeparator` (engine), `DerivationSeparator` (life) | `separation()` | wire records with their own field sets; `ReopeningSeparator` is tested equal to the core factor descent through its quotient |
| `ReconstructionFibre` (engine `cultivated_rest::schema`) | wire record | candidate list with an omitted-remainder digest (a rest codec, not a quotient class) |
| `ReconstructionFibre` (engine `native_ecology::continuation`) | distinct | one-entry predecessor/successor reopening receipt: `Transition::reopen`, not a preimage class |
| `BoundaryReconstructionFibre`, `NativeReceiverFibre` (engine `heterogeneous_fusion`, `inference_membrane`) | wire records | image is the tuple `(address, family, state, boundary)`; five-field wire (owed: `preimage_fibre()` reading) |
| `NativeFactorReconstructionFibre` (life `native_factor_deposit`) | distinct | kernel beside cokernel annihilator (`open_exterior`), not a preimage of a target |
| `SectionReconstructionFiber` (life `causal_section`) | kept | carries the exterior-openness flag and no image; owed: `PreimageFibre<usize, BTreeSet<String>>` once the flag moves to the reading |
| `ReconstructionFiber` (life `reconstruction_fiber`), `MoveSpeciesFiber` (engine) | kept | pass returns holding a focus, a population and the compression; their separators are `CollapsedPair`s |
| `LowPrecisionPreimageFibre` (engine `holonic_intelligence::weight`) | distinct | a quantizer transition's residual reopening (`source = value + residual`), or an open law |
| `NativeDepositFibreDelta` (engine `native_spool::deposits`) | distinct | a move-owned increment to a fibre (deliberately not `Clone`) |
| `ObservationFibre` (core `restriction::tower`) | kept | already the core preimage fibre of the restrict-to-chart receiver, with its sections |
| `NullFibre`, `ExactAffineVersionFiber`, `ExactPhaseFiber`, `OpenFieldRayFiber`, `JointBilinearFibre`, `ResidentJointBilinearFibre`, `ExactCausalKernelFiber` | distinct | kernel bases, reduced-row affine systems with lineage, implicit bilinear fibres, resident evaluators |
| `RoundingFibre`, `PathwiseFibre`, `SummedFibre` (engine `cross_chart`) | distinct | interval preimages of rounding (endpoint membership by ties-to-even) |
| `PluralFibre`, `CrossPresentationFibre`, `DesignSeparator`, `PairwiseSeparator`, `ContactSeparator` | distinct | complete member populations and complete contact comparisons (all separating contacts, never one witness) |
| `relation_ladder::Separator<F>`, `receiver_atlas::Separator<Z>`, `ObservableMomentReceiverSeparator`, `ConfigurationSeparator`, `MaterialShortestSeparator`, `ShortestHistorySeparator`, life `NativeShortestSeparator`, `ForeignShortestSeparator` | distinct | a separating witness and readings whose pair is held by the caller, a linear separating covector, or a quotient refutation without a pair |
| arithmetic, analytic, ray, receiver-direction, language, source and example fibres (`PrimeContinuationFiber`, `QuadraticPrimeFiber`, `QuinticGaloisFiber`, `ExactRefractionFiber`, `QuadricRayFiber`, `TorusRayFiber`, `FaceFiber`, `ReceiverDirectionFiber`, `ReceiverFiber`, `RelationalParseFiber`, `CoTestimonyFiber`, `RasterComponentFiber`, `StateFibre`, …) | distinct | fibre bundles, root sets, projective directions and plural parses: another meaning of "fibre" |
| `ResidentConstitutiveFibre`, `NormalWaveFibre` | distinct | resident constitutive relations (phases 9/11) |

Equality evidence: `holonic-core` `restriction::fibre` tests (named wire, positional/duplicate/
missing/unknown-field policy, `Debug`, affine preimage and its refusals), the factor-descent test
now asserting the retained fibre; engine `restriction_fibre_instances` (the four class fibres
against their old derives, including the spool fixture; the native and condensed separators),
`receiver_exact_compression` (defect fibres = one-shot blocks of two or more items; `CollapsedPair`
wire against the old derive), `cross_chart` (the reopening separator equals the core descent);
life `situated_difference` (every returned fibre is the preimage of its covector and keeps the old
wire), `causal_section` (each section separator is the collapsed pair mapped through the naming
chart), `membrane_interior`, `recurrence`.

### Phase 13 disposition: the device quadratic moment is one storage element

[established-bounded; source-inspected, measured] Scope: `holonic-engine/src/cuda_refine/
membrane_*.rs` (33 files), `cuda_refine/complex_parametron.rs` (the moment's layout validators),
`cuda_refine/tests/factored_moment.rs`, `factored_moment{,/**}`, `receiver_history_compression{,/**}`
and `kernels/refine_shell/membrane_*.cuh`. Before: 35,591 Rust lines, 162 type definitions (101
public); 7,467 kernel lines. After: 35,880 Rust lines (the growth is the storage facet, its
equality tests and facet documentation), 161 type definitions (102 public: two duplicate
wrappers deleted, one core-facing trait added); kernels byte-identical. No device layout, kernel
argument, `SLOT_WORDS` receipt or wire field of an existing format changed.

**The object.** `C = Σ_s w_s f_s f_sᵀ` on the native factor ports. Every host chart —
`FactoredMomentSection` (`Bᵀ H B`), `FactoredConstitutiveSpine` (`Eᵀ(⊕_h μ_h H_root)E`),
`SparseQuadraticMomentSection` (upper pair coefficients) — implements
`factored_moment::QuadraticMomentStorage`: it supplies `moment()` and receives from the core
`storage_form()`, `element()` (`ElementRelation::Storage`), `stored_energy(x) = ½⟨x, C x⟩`,
`is_passive()` (exact inertia) and `deposition_work(successor, x)` (core
`element::deposition_work`). `weighted_family_moment` is the defining law. Lean:
`Holon/MomentStorage.lean` (`quadraticMoment_symm`, `storageEnergy_quadraticMoment`:
`storageEnergy C x = ½ Σ w ⟨f, x⟩²`, `storageEnergy_quadraticMoment_nonneg`), over the existing
`Millennium/HolonicQuadraticMomentCondensation.lean::quadraticMoment`. The resident card is the
same element in its limb layout (the `Resident*` state below); the device suite reads its staged
target back and checks it against `weighted_family_moment` of the transported family.

**Retention.** The rooted spine accumulated one candidate-to-target boundary map per passage —
host `FactoredConstitutiveSpine.reconstruction_fibre: Vec<FactoredHistoryQuotientPassage>` and, on
the card, `ResidentFactoredConstitutiveSpine.reconstruction_fibre: Vec<…>` each holding a device
buffer — an occurrence archive that grew with every passage and that nothing read. Both are
retired: the history weights `μ_h` are the retained quotient (sufficient for every later moment
and receiver). `transport_with_quotient` returns the passage's map as a reading; on the card the
map is released at the synchronization that closes its condensation, and only its four lineage
counts cross to completion, where they are still checked. A spine wire carrying the old field
decodes (`a_spine_wire_carrying_the_retired_passage_archive_still_decodes`). Receiver-history
compression frames are the quotient itself and are kept unchanged.

| Type (owner) | Facet | Disposition / reason |
|---|---|---|
| `FactoredMomentSection`, `FactoredConstitutiveSpine`, `SparseQuadraticMomentSection` | storage element (three charts) | kept; implement `QuadraticMomentStorage`; equality test `every_moment_chart_is_one_storage_element_of_the_weighted_family` (same `C` before/after a plural passage, energy `½ Σ w⟨f,x⟩²`, cross-chart deposition work, `D C D` conditioning) |
| `FactoredConstitutiveSpine.reconstruction_fibre` | retention debt | **retired** (occurrence archive); old wire decodes |
| `FactoredHistoryQuotientPassage` | reading | kept as the per-passage reading returned by `transport_with_quotient`, never retained |
| `WeightedIntegralCurrent`, `AddressedDiagonalCurrentStep`, `SymmetricFactorPair`, `SparseQuadraticMomentAction` | source chart, generator action | kept: the source rank-one presentation, the diagonal chronology chart and the fixed generator-closed pair carrier (the pump's clocked action) |
| `FactoredMomentFoundation`, `SparseQuadraticMomentFoundation` | restriction fibre | kept: one-time founding return whose `reconstruction_fibre`/`source_to_image` is the preimage fibre of the many-to-one moment map (phase 10), not a per-occurrence archive |
| `FactoredMomentPassage` | passage reading | kept (source section, plural boundary map, target) |
| `SparseQuadraticPairReceiverTerm`, `SparseQuadraticPairReceiverFrame` | receiver face | kept |
| `FactoredMomentError` | the host refusal | kept; the one refusal of the exact charts (core storage errors map into it) |
| `ResidentFactoredMomentState`, `ResidentSparseQuadraticMomentState`, `ResidentFactoredCurrentState` | device storage chart | kept: three device charts of the same element (image `Bᵀ H B`, pair carrier, rank-one current), each with its own kernels |
| `ResidentFactoredConstitutiveSpine` | device storage chart | kept; per-passage device archive **retired** |
| `ResidentTransportedConstitutiveSpine`, `ResidentTransportedFactoredHistory` | device transport of the spine | **merged**: one owner with `effective_incidence: Option<…>` (`None` for a direct rooted continuation, whose incidence is the transport's own buffers); one `validate_weights` |
| `ResidentFactoredHistoryQuotientPassage` | lineage reading | kept as four counts; its dead device buffer released at the passage's synchronization |
| `ResidentCompletedTargetObserverWorkspace`, `MomentCompletedTargetObserverBuffers` | receiver workspace | **merged**: the allocator returns the workspace itself (octet accounting moved with it) |
| `ResidentExactRationalMatrix`, `ResidentIntegralMatrix` | device matrix charts | kept: distinct limb layouts (with/without the denominator axis) read by distinct kernels |
| `ResidentTransportedFactoredMomentIncidence`, `ResidentFactoredMomentRankAtlas`, `…CoordinateAtlas`, `…Candidate`, `…ReceiverState` | restriction/descent on the card | kept: the staged exact descent (transport → finite-chart rank → CRT coordinates → two squares → receiver), each stage owning distinct device work released at admission; not an archive (each is consumed once) |
| `ResidentSparseQuadraticConditionedCurrent`, `ResidentSparseQuadraticNativeBoundary`, `ResidentSparseQuadraticReceiverMount`, `ResidentSparseQuadraticBoundaryConditionerMount`, `SparsePairActionIngress` | pair-carrier deposition and receivers | kept (see NOT DONE: shared coefficient body) |
| `ResidentSparseRelationalCurrentAtlasMount`, `…CurrentState`, `…GeneratorTransport`, `…ConditionedCurrent`, `…BoundaryReceiver`, `ResidentFactorizedRelationalWorkspace` | the signed relational current (a separate receiver of the same field) | kept: the Complex-Parametron current is a distinct law (signed, complex, not a storage element); see NOT DONE |
| `ResidentQuadraticActionMount`, `ResidentBoundaryRestrictionAtlasMount`, `ResidentObservableIntegralFormMount`, `ResidentAddressedFactoredReceiverMount`, `ResidentFactoredReceiverHistoryMount` | invariant mounts (generator action, restriction atlas, receiver frames, the operation complex) | kept; the one mount per invariant owner |
| `ResidentReceiverHistoryCompressionMount` | the quotient | kept (receiver-history compression is the retained quotient) |
| `ResidentCompletedTargetObservationAperture` | restriction fibre of one occurrence | kept: consumed by the next receiver of that occurrence |
| `MomentFrontAdmission`, `MomentFrontPlan`, `MomentResidentContextState`, `MomentFrontWorkspace`, `MomentFrontExecution`, `MomentContractionLaunch`, `BoundaryCompletionPlan`, `BoundaryCompletionWorkspace`, `BoundaryIntervalStage`, `BoundaryReturnState`, `BoundarySupportPhaseReceipt` + six aperture aliases | one front's staged execution | kept: builder stages of one launch word (admission → plan → workspace → execution), no retained state |
| `ResidentCurrentAddress`, `ResidentFactoredMomentAddress`, `ResidentFactoredMoment{Transport,Rank,Coordinate,Descent,Receiver}Address`, `…TransportOccurrence` | occurrence addresses | kept: continuation testimony of the one live occurrence (generation-addressed, never a list) |
| `Resident*Return`, `Resident*Receipt` (22 types in `membrane_types.rs`) | readings | kept: each is one passage's reading plus apparatus testimony (launches, octets, synchronizations); several are serialized inside holonic-life rests (`source_neutral_rest/wire.rs`), so their wire stays (see NOT DONE) |
| `ResidentBoundaryChainSupport`, `ResidentQuadraticMomentRestriction{,Source}`, `ResidentBoundaryRestriction{Atlas,Front}`, `ResidentQuadraticMomentFront`, `ResidentSparseRelationalCurrentAtlas` | exterior ports and restriction incidence | kept (boundary codec of the element) |
| `CudaRefineError` | the device refusal | kept: one refusal for the whole card |
| `receiver_history_compression` (`ReceiverHistoryCompression`, `PartialReceiverHistoryCompression`, `GeneratorSquare`, `PartialGeneratorSquare`, `ReconstructionFibre`, frames `ObservableIntegralFormFrame`, `FactoredIntegralReceiverHistoryFrame`, `FactoredRationalReceiverHistoryFrame`, `MembraneFactoredIntegralReceiverHistory`, projective sections/passages, sparse forms and functionals, helical moment reuse) | the quotient and its receiver forms | kept: the compression frames are the retained quotient; `PartialReceiverHistoryCompression` is the open-exterior law (partial generator squares), not a duplicate; `ProjectiveCurrentSection.reconstruction_fibre` is replaced (not accumulated) per passage |
| duplicated `exact_bigint_gcd`/`exact_bigint_lcm` (`factored_moment/{section,passage}.rs`, `projective_history.rs`) | helpers | **merged** into `receiver_history_compression::factored_forms` |

Equality evidence: host `factored_moment::` (new storage and legacy-wire tests, the migrated
descent test asserting the returned passage map), `receiver_history_compression::`; device
`cuda_refine::tests::factored_moment::` baseline versus after at the same counts, with two added
assertions: the device-staged descent target is the storage element of the transported weighted
family (and passive), and after three resident spine passages (two compact, one rooted) the card's
history weights equal the host spine's quotient; `cuda_refine::tests::cuda_apparatus::` unchanged.

**Not done, with reasons.** (1) The signed relational current and the pair-coefficient section each
appear in two or three device wrappers (standing, generator-transported, conditioned) with the
same body (`state_present/states/…sign/limbs/bound`, resp. `state_ids/coefficients/limb bound`);
extracting one body per object is a host-only refactor, but the conditioned/completion path
(`membrane_{returned_restriction,sparse_completion,generated_condition}.rs`) is reached only from
holonic-life `source_neutral_rest` examples whose private rests are not present in this checkout,
so no device equality run covers it; owed with that fixture. (2) The apparatus testimony block
(device, context, launches, synchronizations, octet counters, `*_reuploaded`, `cpu_semantic_replay`)
repeats across the `Resident*Return` readings; one `ResidentPassageCost` flattened into each would
keep JSON but not field access, and holonic-life serializes and compares these returns
(`SourceNeutralResidentRadiationSection::same_native_receiver_consequence`), so it is owed with the
phase-14 life migration. (3) `ResidentAddressedFactoredReceiverMount.reconstruction_fibre` (the
host copy of the primitive receiver frame beside its device realization) is a mount-time receiver
declaration, not an occurrence archive; kept. (4) The situated ingress receiver
`ResidentSparseQuadraticMomentState.situated_receiver_coefficients` is carried across the
circulation as the declared dual receiver; whether it should be re-read from the contemporary
constitution is the phase-12 frozen-receiver question and is left to it.

### Phase 11 disposition: the resident constitutive views are one relation

[established-bounded; source-inspected, measured] Scope: `holonic-engine/src/native_ecology/
constitutive_fibre/resident{,.rs}/**` and its callers (engine `material_transport/normal/direct/
wave/coupled{,/comparison/constitutive,/**/tests}.rs`; hna `examples/athena_field.rs`,
`field_session{,/native_source}.rs`, `coupled_wave/tests{,/boundary}.rs` — the hna and coupled
edits are the minimal compile fixes of the refusal change). The resident relation host reading and
one contact reaction are added; duplicate views, decoders, the former consequence law and three
compatibility types are gone. No kernel, device layout or `SLOT_WORDS` receipt changed. The
source-map codec retains its current v2/v4/v5 forms; the superseded v1 and v3 readers are refused.

**The one object.** The resident constitutive fibre carries one linear relation
`R = span{(x_i, y_i)} ⊂ S × T` (`Computation/HolonicConstitutiveFibre.lean::pairedCurrentSubmodule`).
Every view returns the **fibre of R over a source**, `R_s = {t | (s,t) ∈ R}`: empty outside the
source projection, else the translate of the vertical fibre `R_0` through any member
(`vertical_fibre_iff_zero_source_difference`). `ConstitutiveRelation` (`resident/relation.rs`) is
the exact host reading of the device relation (`ResidentConstitutiveFibre::relation()`, as
`NormalConstitution` reads `ResidentNormalMaterial`); `ConstitutiveReading::fibre()` and
`ConditionPreimageReading::fibre()` return the core restriction fibre
`holonic_core::restriction::AffineFibre` (`Holon/Restriction.lean::affineFibre_mem`), and a plural
reading keeps the whole fibre. It is not the phase-9 normal law: `W H = B` is a storage element on
coefficients, while this is the exact relation of received pairs. Where the phase-9 object is the
same object — the predictive material of each neighborhood member — it is used directly
(`PredictiveMaterial.material: ResidentNormalMaterial`, its applied action read from it).

**The contact is one element law.** An actual current `h` meeting an affine family `a + V`
through the declared unit admittance returns `h' = P h + (a − P a)`, `n_in = a − P a`,
`n_ret = h − P h`, with `h' − h = n_in − n_ret` and the lossless exchange
`‖h‖² + ‖n_in‖² = ‖h'‖² + ‖n_ret‖²`; a current already in the family is unchanged. Lean:
`Holon/AffineContact.lean` (`contact_difference`, `contact_lossless`, `contact_normal`,
`contact_mem_family`, `contact_fixes_family`, `contact_idempotent`, `oblique_contact_witness`),
imported in `Framework/HolonObject.lean`. Its one resident section and decoder is
`ResidentContactReaction`; `AffineContactReading::is_lossless_exchange` reads the law, and the
wave-relation rest checks it on the retained words.

**Retention.** A wave source map retains its source operand, field row and reaction; its basis is
`source_basis(reaction)`. `read_source_passage` returns the producing prediction and arrival as
readings (`ResidentWaveSourcePassage`), and `NormalCoupledStep::predictions` carries the point-source
prediction. Current v5 writes the source map from those operands and remount checks its reaction and
basis. The former v3 wire also carried the producing prediction and whole arrival family; that
save-format reader is retired under restructure §0.2 and v3 now returns a typed rest refusal. The
chart's anchor coordinates (the family's original `z0`, carried through every map) are the phase-9
anchored affine family's restriction coordinates and a device layout; they are kept. The
observed-next snapshot is the operand the coupled remount re-reads; kept. `StandingLaw` is not
applied here: the retained data is the map's own generator and operand, not a linear quotient of a
state.

| Former type / member | Facet | Disposition |
|---|---|---|
| `ResidentConstitutiveFibre` | device chart of R | kept; `relation()` its host reading; one `admits_source` check for reads and advances |
| new: `ConstitutiveRelation`, `ConstitutiveAffineFibre` (= core `AffineFibre<ParticularDirections>`), `same_affine_fibre` | host reading of R; its fibres | new |
| `ConstitutiveReading`, `ConstitutiveFibreReturn`, `ConditionPreimageReading` | the fibre over a source | kept as codec faces; `fibre()` to the core fibre |
| `ResidentConstitutiveReturn`, `ConstitutiveReturnRest` | the fibre report and its wire | kept; one allocator (`allocate`; the method form delegates; the preimage's hand-built copy deleted) |
| `ResidentConstitutiveCurrent`, `ResidentConstitutiveSection`, `ResidentDifferenceSection`, `ResidentSourcePairs`, `ResidentBilinearFeatures` | port charts and derived source sections | kept: distinct device charts (comparison triples, source pairs, bilinear features with their adjoint) |
| `ConstitutiveDifferentialReading`, `PreparedConstitutiveFormation` | receiver reading; staged deposition | kept |
| `AffineContactReading`, former `ConditionContactReading` | the contact reading | one struct; `contact: Option<u64>` is omitted when absent, preserving both former JSON faces byte-for-byte; no alias |
| new: `ResidentContactReaction` | the contact element's one section | new; `ResidentAffineContact`, `ResidentConditionContact`, `ResidentWaveSourceContact` hold it; their three block-view copies and two decoders deleted |
| `ResidentConditionCurrent` | the retained condition (successor block of its latest reaction) | one owner; `standing()` returns a clone sharing its reaction section |
| `PreparedConditionContact`, `ConditionCurrentRest`, `ConditionContactMetric`, `ConditionContactStatus` | staged contact; rest (current only); metric; status | kept |
| `ResidentConditionPreimage`, `ConditionPreimageRest` | fibre of the derived condition relation; compact rest | kept |
| `ResidentConditionImage`, `ResidentConstitutiveImage`, `ResidentConstitutiveRefinement`, `ConditionImageReading`, `ConstitutiveImageReading`, `ConditionCoverage` | two images over one `AffineImageData` | kept: distinct kernels (bilinear condition image, linear fibre image) and public field names read by hna `mathematical` |
| `ConstitutiveImageReceiver::{WaveConditional, WaveSourceContact, WaveObservation}` | producing receiver | **merged** into `Wave`: the kind is read from the relation |
| `ResidentContextualSection`, `ContextualSectionOrigin` | source-null derived section | kept (its field-contrast reference/endpoint are operands of its absolute reading) |
| `ResidentGeneratorNeighborhood`, `GeneratorNeighborhoodStep`, `GeneratorNeighborhoodRest` | the neighborhood, its one return and one rest | kept (rest v1/v2 unchanged) |
| `GeneratorMaterial`, `PredictiveMaterial` | compatibility law beside `ResidentNormalMaterial` and its applied action | kept; phase 9's object used directly |
| `PreparedNeighborhoodAdvance` | staged consequence plus borrowed operands | **merged** into `PreparedNeighborhoodConsequence`; `publish_consequence` takes the operands; `prepare_advance`, `can_commit_advance`, `read_consequence_wave_relation` deleted |
| `receive_reaction_observation_at` (its own copy of the consequence law) | the consequence law | **merged**: one `prepare_consequence_with` at `ConsequenceCondition::{Contemporary, Producing}` |
| `ResidentNeighborhoodAlternative` | dependent-family stage | kept |
| `NeighborhoodEvidence`, `NeighborhoodEvidenceRest` | latest received condition fibre (one entry, replaced) | kept: hna `field_condition_image` reads it |
| `attach_normal_prediction` refusal `(material, error)` | refusal | now the one `NormalRefusal<ResidentNormalMaterial>` |
| `FieldReactionEnclosure{,Rest}`, `PreparedFieldReaction` | producing reaction receipt | kept, **not retired**: it retains the producing normal material, the frozen cut of hna `FieldProducingSection` (phase 12) |
| `ResidentWaveRelation`, `ResidentWavePullback`, `WaveSourceReceiver`, `ResidentWaveSourceGeometry` | derived wave map, pullback, receiver chart, geometry cache | kept |
| `ResidentWaveSourceContact` | source map | anchors retired (above); new `ResidentWaveSourcePassage` returns them |
| `NormalWaveRelationRest` | map wire | v5 source map added; current v2/v4/v5 forms read and write; superseded v1/v3 readers refuse |
| per-rest `error`/`invalid` helpers (three) | rest refusal | one `rest_refusal` |

Equality evidence: host `resident::relation` (fibre = translate of the vertical fibre; readings
as core fibres), `resident::condition_contact::reaction` (both former JSON faces byte-identical;
the lossless law on the device witness `h = (7,4)`), `wave_relation::rest`
(`v1_wave_relation_is_refused_as_a_typed_rest_error`,
`v3_anchored_source_map_is_refused_as_a_typed_rest_error`, v2/v4 codec cases);
device `resident::relation::every_resident_reading_is_the_fibre_of_the_one_relation` (every unique,
plural and outside reading of two fixtures equals the core fibre of the detached relation, number
for number for unique readings), `condition_contact::tests` (native oblique and quarter-turn contacts,
refusal preservation), and `wave_relation::rest::current_source_map_v5_round_trips_and_remounts_from_its_operands`
plus `source_rest_rejects_changed_returned_normal` (the v5 map checks its source/reaction relation
and refuses a corrupted returned normal at decode).

**Continuation verification, September 23, on `codex/consolidation-phase-11` from `de6a5300`.**
Lean built `ElementaryHolonics.Holon.AffineContact` and
`ElementaryHolonics.Framework.HolonObject`; the contact theorems report only the standard
`propext`, `Classical.choice` and `Quot.sound` axioms. Rust host test
`the_relation_fibre_is_the_translate_of_its_vertical_fibre` passed. On source commit
`a6c0c95d` (the v3 decoder and both compatibility aliases retired, before the v1 reader cut), the
full engine `material_transport::normal` suite passed 172/172 in 54.99s. The resident relation,
condition-contact and wave-rest suites passed 2/2, 10/10 and 6/6; the v5 source-map remount and
lossless-reaction refusal passed in that pre-v1 tree. Their logs are
`.local/p11-continuation-logs/engine-normal.log`, `engine-relation.log`,
`engine-condition-contact.log` and `engine-wave-rest.log`.

The full HNA library suite was started on `a6c0c95d` with 216 tests and serialized CUDA. The user
stopped it under resource pressure while `native::field_session::generator_application::deposition_probe::deposition_split_synthetic_long_control`
was active. The log contains 115 completed passing tests before that probe and no suite result;
record this as **interrupted**, not passed. Log:
`.local/p11-continuation-logs/hna-lib.log`. The active probe matched the existing
`.local/campaign-deposition/synthetic.log` result of 4,192.42s, with CPU and GPU utilization active.

On source commit `53e085eb` (v1 reader removed), the post-v1 host wave-rest filter passed 4/4
with 2 CUDA tests ignored: typed v1 and v3 refusals plus v2/v4 round trips. The run completed in
49.94s including the cached-target compilation and launched no NVCC. Log:
`.local/p11-continuation-logs/engine-wave-rest-host-postv1.log`. Post-v1 CUDA remount and HNA
consumer suites remain unverified under the resource stop.

**Not done, with reasons.** (1) The frozen producing material in `FieldReactionEnclosure` and the
coupled continuation's retained transport word are phase-12 retention debt (hna field session). (2)
`ConditionImageReading`/`ConstitutiveImageReading` could be one reading with renamed fields; their
field names are public API of hna `mathematical`, so they stay two faces of one decoder. (3)
`NormalWaveRelationRest` keeps its name (wire and public API) although the relation is not the normal
law. (4) The contact law is checked by Lean and by the resident reaction reading; a device receipt
of the balance (a sixth block) would change the reaction layout and is not added.

### Phase 15 disposition: the extracted operator is one Holon

[established-bounded; source-inspected, implemented-exact, measured] **Subject: equation
extraction.** "Soulkiller" is only a label (Brandon, September 23); the subject is reading a
foreign model's computational graph as native equations on the Holon: the operator graph's
carrier incidence is the interconnection 𝒟 (`NativeFullOperatorEcology::{carriers, operations}`,
each `NativeOperatorNode` a bond from its input to its output carriers), its coefficient
populations are the element relations 𝓔 (`NativeCoefficientPopulation`; resident as
`NativeOperatorResidence`), and the operation word is the transport law, advanced one occurrence
at a time. Owner: `holonic-engine/src/holonic_intelligence/extracted_operator.rs`.

Scope: `holonic_intelligence/{operative_*,full_operation,circulation}.rs` (20 files) and their
callers (`holonics-hna` `hna.rs`, `session.rs`, `checkpoint.rs`, `stream.rs`,
`recurrent_operator.rs`; 12 hna and 4 engine examples; `soulkiller/boundary.rs`). Before (tree
4dff57c8): 142 public types (198 with private), 14,365 lines, 11 refusal enums, two session
ladders. After: 136 public types (199), 14,975 lines (the growth is the facet documentation, the
branch's constitution chart, the legacy-rest decoder and in-file tests; the new device equality
file `extraction_equality_tests.rs`, 724 lines, is separate), 8 refusal enums, one ladder: 21
public types deleted, 15 added, 2 structs made aliases.

**Facets.** *Advance*: one occurrence `ExtractedOperatorOccurrence` (the source port: resident
row addresses for a lookup, host-entered words for an occurrence-entered product, or nothing),
one step `ExtractedOperatorStep<S>` and one word `ExtractedOperatorBranch<S>` over the trait
`ExtractedOperatorAdvance`, one emission `ExtractedOperatorEmission<O>` (the operation labelled in
its executor's chart) and one trace `ExtractedOperatorTrace<C>` (common passage testimony; the
executor's chart `GraphTraceChart`/`BranchTraceChart` flattened into the same record). Two
executors realize it: `ExtractedOperatorSession` (the graph: fused sealed segments, tiled
terminal) and `ExtractedBranchSession` (the six-node per-layer branch, one unsealed passage per
operation on host-entered carriers). *Constitution*: the branch's morphology is an instance of
the one chart (`NativeOperatorMorphology::constitution_chart`: `c0` entered carrier, `c1` entered
interaction, `c(k+2)` the output of operation `k`; `P0`/`P1` the two cross-sections, `P2` the gain).
*Rest*: one rest `ExtractedOperatorRest` for both executors; the branch rests on its constitution
chart, and its legacy JSON wire (`native-operator-session-rest.v1`) decodes through
`ResidentOperatorMorphology::read_legacy_rest`. *Refusal*: one `ExtractedOperatorRefusal` for
advance, pullback, residence and rest; constitution refusals (`NativeFullOperatorError`,
`NativeOperatorMorphologyError`, `NativeOperatorResidenceError`) enter as its sources. *Descent*:
the lens and signature quotients read onto the phase-10 core types (`separation()`,
`preimage_fibre()`). *Extraction return*: both extractors return the three-lane
`soulkiller::ExtractionReturn<native, exterior, insufficiency>` (`SoulkillerDismantlingReturn` is
its alias for existing callers).

**Retention (one cut).** The continuing return (`found_with_return`) no longer retains the
previous cycle's terminal face, reacted tiles, presented carrier or cross-layer checkpoints across
the cycle boundary. At a continuing occurrence it reads the contemporary constitution at the
retained occurrence (`previous_context`): `contemporary_terminal` re-enacts the forward and the
tiled terminal from those rows, then the return and the within-cycle checkpoint replay of the
adjoint run as before. Only a return deposits, so the constitution read is the one that emitted.
The wire keeps its layout: the three retired positions are written absent and an older wire's
material there is decoded and released (as are an older cycle boundary's checkpoints). Dissection
keeps the terminal material, because its probes read the same cycle. The measured cost is one
extra forward per continuing return (census only; every number is equal, below).

| Former type | Facet (operator / coefficients / transport / receiver face) | Disposition |
|---|---|---|
| `NativeOperatorOccurrence`, `NativeFullOperationOccurrence` | transport: the source-port occurrence | deleted → `ExtractedOperatorOccurrence` (`addressed`, `entered`, `internal`); each executor refuses the port it lacks |
| `NativeOperatorEmission`, `NativeFullOperationEmission` | receiver face of one operation | deleted → `ExtractedOperatorEmission<NativeOperatorKind>` / `<u32>`; the branch emission gains its chart carrier `c(k+2)` |
| `NativeOperatorTrace`, `NativeFullOperationTrace` | transport testimony | deleted → `ExtractedOperatorTrace<BranchTraceChart>` / `<GraphTraceChart>` (same JSON keys and values; field access `trace.chart.*`) |
| `NativeOperatorStep`, `NativeFullOperationStep` | transport: one operation | deleted → `ExtractedOperatorStep<S>` |
| `NativeOperatorBranch`, `NativeFullTerminalBranch` | transport: a run of the word | deleted → `ExtractedOperatorBranch<S>` |
| `NativeFullCycle`, `NativeFullCycleOutput` | transport: one recurrence | `ExtractedOperatorCycle { output, successor }` (no duplicated field set), `ExtractedCycleOutput` |
| `NativeFullOperatorSession`, `NativeOperatorSession` | the two executors | renamed `ExtractedOperatorSession`, `ExtractedBranchSession`; both implement `ExtractedOperatorAdvance` |
| `NativeOperatorExecutionError`, `NativeFullOperationError`, `NativeSessionRestError`, `NativeAdjointError` | refusal | deleted → `ExtractedOperatorRefusal` (variants and messages kept; the rest's `resident rest:`/`native operation:` wrappers become the shared variants, and the branch's obstruction names its operation ordinal) |
| `NativeFullSessionRest`, `NativeSessionRestHeader` | rest | renamed `ExtractedOperatorRest`, `ExtractedOperatorRestHeader`; `terminal_reacted`, `terminal_contracted`, `terminal_presented` retired (wire positions kept) |
| `NativeOperatorSessionRest` | rest | absorbed: the branch rests as `ExtractedOperatorRest`; its JSON wire decodes (private `BranchRestWire`) |
| `NativeOverlayRest` | coefficients: a deposited factor `u·v` | moved into the rest module; kept |
| `NativeTiledRest`, `NativePassageRest`, `NativeNumericalRest`, `NativeForwardReuseRest` | rest components | kept |
| `NativeFullOperatorDismantlingReturn`, `NativeOperatorDismantlingReturn` | extraction return | aliases of `ExtractionReturn<_, _, _>` (graph: insufficiency `()`) |
| `NativeFullOperatorEcology` | operator + coefficient populations: the constitution chart | kept; the branch charts onto it |
| `NativeTensorOrdinal`, `NativeCarrierOrdinal`, `NativeCarrierAxis`, `NativeCarrierChart`, `NativeCoefficientPopulation`, `NativeOperatorNode`, `NativeOperationPrimitive`, `NativeScaleConstraint`, `NativeCausalReach`, `NativeLayerTopology`, `NativeKvStanding`, `NativeCoefficientObstruction{,Kind}` | the complex, element relations and operator law of the chart | kept |
| `NativeAttentionTopology`, `NativeJoinedPassage`, `NativePassageReturn`, `NativePassageWithdrawal` | interaction: declared contact topology; additive junction of two arrivals and its local return | kept |
| `NativeOperatorMorphology`, `NativeOperatorKind`, `NativeDyadicMatrix`, `NativeDyadicCoefficient` | operator + exact dyadic coefficients of the branch | kept; `constitution_chart()` |
| `NativeOperatorResidence`, `ResidentNativeOperatorPopulation`, `NativeOperatorResidenceReceipt`, `NativeOperatorDecoderCensus`, `NativeAlignedOperatorTile`, `NativeCoefficientIntake`, `ResidentOperatorMorphology` | the resident constitution (graph; branch whole-matrix readouts) | kept (one residence for both executors owed) |
| `NativeFullOperatorColdWitness`, `NativeOperatorColdPopulation`, `NativeOperatorColdWitness`, `NativeOperatorInsufficiency` | extraction cold/insufficiency lanes | kept |
| `NativeFullOperatorError`, `NativeOperatorMorphologyError`, `NativeOperatorResidenceError` | constitution refusals | kept as sources of the one refusal |
| `NativeMorphologyTransition`, `NativeSuccessorProjection`, `NativeCycleProgress`, `NativeCycleInterruption` | trace readings; the move owner's held progress | kept |
| `NativeReturnAperture`, `NativeMorphologyDeposit` | deposition (the only change of the constitution) | kept |
| `NativeAdjointContraction`, `NativeAdjointReturnTrace`, `NativeAdjointOperationSupport`, `NativeLookupReach`, `NativeDifferentialSupport` | one-cut pullback and its testimony | kept |
| `NativeForwardReuseCensus`, `NativeNumericalOrigin` | numerical reuse | kept: memoized contemporary readings, invalidated by every constitution change (not an archive) |
| `NativeEmissionProjection`, `NativeEmissionReadout`, `NativeReceiverFace` | receiver face | kept |
| `NativeDissectionAperture`, `NativeSiteSupport{,Summary}`, `NativeExcitationTrace`, `NativeSiteSelection`, `NativeWithdrawnFace`, `NativeMagnitudeControl`, `NativeConeVerdict`, `NativeConeProbe`, `NativeConeBoundary`, `NativeConeReturn`, `NativeRoleSpan`, `NativeRole`, `NativeRoleGrain`, `NativeSiteContributions`, `NativeRoleOrder`, `NativeRoleError` | the dissection receiver (excitation, founded cones, roles) | kept; its terminal material is within one exposure |
| `NativeConeRestriction`, `NativeRestriction`, `NativeRestrictedCrossSection`, `NativeRestrictedIntake`, `NativeInputRowExtension`, `NativeInputExtendedIntake` | coefficient row restrictions | distinct: site masks and row subsets of coefficient words, not a core port map |
| `NativeCollapsedPair` | descent defect of the lens | kept wire; `separation()` = core `Separation<usize, (exposure, lens face, word), u32>` |
| `NativeClassEcology`, `NativeRetainedOccurrence` | descent: a signature class | kept; `preimage_fibre()` = core `PreimageFibre<NativeSignature, Vec<NativeRetainedOccurrence>>`, `separations()`; the retained occurrences are the class fibre (a quotient class, not a cross-cycle archive) |
| `NativeSeparation`, `NativeSignatureClass` | descent of the signature quotient | kept; `separation()`, `preimage_fibre()` |
| `NativeSignature`, `NativeSignatureQuotient`, `NativeExposure`, `NativeExposureFace`, `NativeSiteBitmask`, `NativeIdentificationError`, `NativeClassRemainder`, `NativeTerminalRemainder`, `NativeRemainderSpecies`, `NativeReceiverResponse`, `NativeConeFounding`, `NativeConeRestrictedEcology`, `NativeFoundedClassCone`, `NativeFoundedCones`, `NativeExposureTestimony`, `NativeExcitationColdWitness`, `NativeInsufficiencyCause`, `NativeFamilyInsufficiency`, `ResidentExcitationDismantling`, `NativeCondensationError` | the cone-restricted extraction and its lanes | kept |
| `NativeInferenceAddress`, `NativeInferenceRequest`, `NativeFutureFace`, `NativeEmissionSection`, `NativeEmissionAddress`, `NativeInferenceLineage`, `NativeFutureReconstruction`, `ExteriorReturnAperture`, `ExteriorReturnOccurrence`, `NativeInferenceCirculation`, `ExteriorEmissionCodec`, `Utf8InspectionCodec`, `BinaryEmissionCodec`, `NativeInferenceError` (`circulation.rs`) | receiver face of the spool circulation | distinct object (the spool transport scaffold's plural future section); kept for life, workspace and circulation-ABI callers |

**Equality evidence** (`extraction_equality_tests.rs`, device, one at a time under the GPU lock).
Each scenario reduces its emissions, traces, deposits, adjoint testimony and rests to one
canonical JSON reading whose SHA-256 was recorded on 4dff57c8 and is asserted unchanged: the plain
cycle with rest/remount (`acdaff48…`), the single-operation ladder with the terminal branch
(`12782b38…`), the joined-passage cultivation with numerical reuse and its rest (`12162e2f…`), the
dissection (read face, excitation, withdrawals; `86dae268…`), the branch chart (two branches,
rest inside and at the end of the word; `9467616b…`), and the continuing return over five cycles
with a rest (`faefec41…`, census excluded). Two recorded legacy wires are fixtures: the branch's
JSON rest decodes to the same one rest and continues to the same numbers (`079f5c14…`), and the
continuing-return rest that still carries the reacted/presented carriers and checkpoints decodes,
releases them and continues to the recorded deposits and faces (`9ba14d0c…`). Host:
`extracted_operator` (occurrence ports, flattened trace keys), `operative_rest_wire_tests` (an
older frame with the retired positions decodes; the current frame keeps the layout),
`operative_morphology` (the branch chart validates and every bond agrees in width),
`operative_condensation` and `operative_identification` (collapsed pairs, separations and classes
as core descent objects).

No new mathematical law: the return applies the retention law already formalized
(`Foundation/Standing.lean`), and the chart and the three-lane return are data; #62 is not
extended.

**Owed (not done).** One executor: the branch still runs its own per-operation unsealed passages
on host-entered carriers; the graph executor has no host-entry primitive or unsealed per-operation
mode, so running the branch through it would change the enclosures (a device-layout change this
phase does not make). One residence (`ResidentOperatorMorphology` beside `NativeOperatorResidence`).
Equation extraction still owed where the graph is carried as an opaque payload rather than as
equations: the GELU/tanh constants and series apertures are fixed in the executor rather than
extracted with the operator; the terminal receiver boundary is located positionally (the last
five operations, `operations.len() − 5`), not by a declared receiver bond; the branch's
interaction words are read from a foreign per-layer table at the host
(`AthenaTextOccurrenceApplication::occurrence_carriers`), not a declared population of the chart;
and the extracted operator has no core chart (no `HolonLaw` reference motion or `ElementRelation`
with its declared power, as phase 9 gave the normal constitution), so its passivity/power balance
is not stated.

### Phase 16 disposition: the event-law scaffolding

This phase's tables below record the September 23 phase-16 source state. The generative-transport
Rust module and its experiment were retired in R1 after the bounded law moved to
`docs/HNN_FORMULA.md` and `Transport/GenerativeTransport.lean`; the July research record retains
the full construction evidence and receiver-scope qualification.

[established-bounded; source-inspected, measured] Scope: the 26 engine `impl ExactEventLaw`
modules (27 laws; `analytic_field` has two) and `world.rs`. Each law's mathematics is unchanged;
only its scaffolding moved onto the Holon objects.

**The bridge** (`holonic-engine/src/world.rs`, `world/scaffold.rs`; core `holon.rs`). Core
`HolonState<C = Vec<Rat>>` is now generic in its configuration (`at`, `committed`); the existing
`HolonState` is the default. `CausalWorld<L>` holds a `HolonState<L::Standing>`: the standing is
the configuration and `commit` counts committed events (`next_ordinal = commit + 1`,
`CausalWorld::state`, `from_state`; `from_rest` unchanged). `EventSuccessor::port_flow` names the
radiation as the flow returned at the external ports (the event is the effort supplied there).
`EventRefusal<K>` is one refusal family per law: the four shared refusals (`RepeatedEvent(EventId)`,
`MalformedStanding`, `LawStandingMismatch`, `CarrierOverflow`) and `Law(K)` with the law's own kinds;
`RefusalKind::LAW` names the law in the shared messages; `event_refusal_from!` routes a kind's
`#[from]` sources (no blanket `From<K>`, so a shared refusal converts by identity). `EventStanding<S>`
is the repeated standing shape — schema, admitted occurrences, the law's quotient `S` (reached by
`Deref`) — with `refuse_repeated`/`check_schema` typed by `EventQuotient::Refusal`, and
`event_standing_wire!` owning each adopter's rest: a borrowed write record with the old struct name
and field order (minus archives) and an owned read record that accepts the retired archive fields.

| Module | Refusal family (`XError = EventRefusal<XRefusal>`; shared variants found) | Standing |
|---|---|---|
| `bit_causal` | `BitCausalRefusal`; all four | `EventStanding<BitCausalQuotient>` |
| `causal_state_grammar` | `CausalStateGrammarRefusal`; repeated, malformed, overflow | `EventStanding<CausalStateGrammarQuotient>` |
| `organizational_grammar` | `OrganizationalGrammarRefusal`; repeated, malformed, overflow | `EventStanding<OrganizationalGrammarQuotient>` |
| `generative_transport` | `GenerativeTransportRefusal`; all four | `EventStanding<GenerativeTransportQuotient>` |
| `inverse_transport` | `InverseTransportRefusal`; all four | `EventStanding<InverseTransportQuotient>` |
| `wave_propagation` | `WavePropagationRefusal`; repeated (was payload-free; now carries the event), malformed, overflow | `EventStanding<WavePropagationQuotient>` |
| `divisor_reconstruction` | `DivisorReconstructionRefusal`; all four | `EventStanding<DivisorReconstructionQuotient>` |
| `causal_traversal` | `CausalTraversalRefusal`; repeated, malformed, overflow | `EventStanding<ExactCausalTraversalQuotient>` (the pending frontier is a work schedule; kept) |
| `observation_ecology` | `ObservationEcologyRefusal`; repeated, malformed, overflow | `EventStanding<ObservationEcologyQuotient>` |
| `atmospheric_inverse` | `AtmosphericInverseRefusal`; repeated, malformed, overflow | `EventStanding<AtmosphericInverseQuotient>` |
| `arithmetic_fiber` | `ArithmeticFiberRefusal`; repeated, overflow | `EventStanding<ArithmeticFiberQuotient>` |
| `prime_ecology` | `PrimeEcologyRefusal`; overflow | `EventStanding<PrimeEcologyQuotient>` |
| `receiver_phase_atlas` | `ReceiverPhaseAtlasRefusal`; repeated, malformed, overflow | `EventStanding<ReceiverPhaseAtlasQuotient>` |
| `arithmetic_monodromy` | `ArithmeticMonodromyRefusal`; all four | `EventStanding<ArithmeticMonodromyQuotient>` |
| `field_atlas` | `FieldAtlasRefusal`; repeated, malformed, overflow | `EventStanding<CausalFieldQuotient>` |
| `coupled_informant` | `CoupledInformantRefusal`; repeated, malformed, overflow | `EventStanding<CoupledInformantQuotient>` |
| `causal_body` | `CausalBodyRefusal`; none (shared variants available) | `EventStanding<CausalBodyQuotient>` |
| `dimensional_wave` | `DimensionalWaveRefusal`; repeated, malformed, overflow | `EventStanding<ExactDimensionalWaveQuotient>` |
| `analytic_field` (two laws) | `AnalyticFieldRefusal`; overflow | advection: `EventStanding<ExactAnalyticAdvectionQuotient>`; field wave reuses the dimensional-wave standing |
| `arithmetic_phase` | `PrimePhaseRefusal`; overflow | kept (`value, phase, receivers, next_receiver`: no schema/occurrence set) |
| `local_star`, `physical`, `simplicial` | `LocalStarRefusal`, `PhysicalLawRefusal`, `HingeWorldRefusal`; none | kept (hinge/kinematic standings: no occurrence set) |
| `algebraic` | `CausalAlgebraicRefusal`; none | kept (`CausalAlgebraicPresentation`: no occurrence set) |
| `holonic_complex` | `HolonicComplexRefusal`; malformed, overflow | kept (nests the receiver-phase standing, which carries the occurrence set) |
| `sheaf_diffusion` | `SheafDiffusionRefusal`; none | kept (`schema, content`) |

[established-bounded; source-inspected, implemented-exact] **Retention.** Every archive below was
written by the law and read, if at all, only as a statistic; the standing now keeps the statistic.

| Archive | Read by the law's future? | Kept instead | Old rest |
|---|---|---|---|
| `bit_causal` `history: Vec<BitCausalHistoryEntry>` | certificate `testimony_events`; inspection `standing_history_events` (= admitted count); validation replay | `testimony_events: BTreeSet<EventId>`; the compatible family is the testimony's fibre; `validate` re-derives the query from the family and checks `used = testimony + widths − 1` | decodes; archive reduced to its testimony events (`BitCausalHistoryEntry` kept as the read record) |
| `causal_state_grammar` `history` | certificate `predictions_graded` (count of emitted predictions) | `emanated_predictions: u64` | decodes; archive reduced to the prediction count |
| `organizational_grammar` `history` | certificate `source_testimony_events` = every admitted observation | nothing new (= `used_events`) | decodes; dropped |
| `generative_transport` `history` | certificate `testimony_events`; `AwaitingInitialOperator` emptiness; validation replay | `used_events ∪ {event}`; the parameter family is the returned coordinates' fibre | decodes; dropped |
| `inverse_transport` `history` | certificate `testimony_events`; complete-operator count (= certificate present); validation replay | `used_events ∪ {event}`; the affine version fibre is the testimony's sufficient statistic | decodes; dropped |
| `wave_propagation` `history` | no | nothing | decodes; dropped |
| `wave_propagation` `pending: PendingWavePrediction { generation (frozen mode predictions), source }` | yes: the return grades the prediction | the producing operands `{interaction, source}`; the return regenerates the prediction through the contemporary modes (retention law: a delayed comparison is read through the contemporary constitution) | decodes (untagged read: the frozen record's interaction is kept, its predictions dropped) |
| `divisor_reconstruction` `history: Vec<DivisorContactTestimony>` | grade `explicit_contact_returns` and the explicit-section set; validation replay | the response maps (`pair_responses`, `higher_responses`) are the sufficient statistic; `validate` replays the founding answering each production query from them (the responses are an oracle) | decodes; dropped |
| `causal_traversal` `pending` frontier | yes (scheduled fronts) | kept: a work schedule, not an archive | unchanged |

Semantic change, stated: a wave prediction returned after an intervening `Condition` on the same
interaction is now graded by the contemporary modes, not the modes at generation. No existing
caller does this (unit tests, `speech_room_information_flow` and
`receiver_emission_information_flow` all return with no intervening conditioning), and
`a_retired_frozen_pending_record_decodes_to_its_operands_and_grades_unchanged` checks the graded
residuals equal the generation receipt's predictions when none intervenes. The testimony audit is
the radiation of each event (`received_testimony`, `received_exhaustive_testimony`,
`emitted_prediction`, `WaveGenerationReceipt`); the `causal_state_grammar_experiment` trace is now
written from the events and their radiation.

Retired public types (8): `OrganizationalGrammarHistoryEntry`, `GenerativeTransportHistoryEntry`,
`ParametricCompleteOperatorTestimony`, `ParametricTransportTestimony`, `CompleteOperatorRole`,
`InverseTransportHistoryEntry`, `WavePropagationHistoryEntry`, `WaveGenerationRecord`. Retired
accessors: `history()` (7 standings), `BitCausalStanding::{testimonies, exhaustive_testimonies}`
(the testimony is in the radiation). New accessors: `BitCausalStanding::testimony_events`,
`CausalStateGrammarStanding::emanated_predictions`,
`DivisorReconstructionStanding::explicit_contact_returns`, `EventStanding::{used_events, quotient}`.
Before/after over the 26 modules: 761 → 753 public structs/enums (26 error enums became their law's
refusal kinds; 19 standing structs became quotient structs), 2 → 47 aliases (26 `XError`, 19
`XStanding`), 57,977 → 61,777 lines (the explicit `XError::Law(XRefusal::…)` sites after rustfmt,
the wire records and the equality tests); plus `world/scaffold.rs` (294 lines).

Equality evidence: engine lib tests of the 26 modules, `world` (incl. scaffold) and the five
consumer modules (338 pass; the CUDA `observation_ecology` card test passes on the device); new tests
`a_retired_history_rest_decodes_to_the_quotient_and_its_future_is_unchanged` (bit),
`the_emitted_prediction_count_is_the_archive_statistic_and_old_rests_decode` (causal state),
`a_retired_history_rest_decodes_and_its_certificate_is_unchanged` (organizational),
`a_retired_testimony_archive_decodes_and_the_certificate_is_unchanged` (generative),
`a_retired_testimony_archive_decodes_and_the_future_is_unchanged` (inverse),
`a_retired_frozen_pending_record_decodes_to_its_operands_and_grades_unchanged` (wave),
`a_retired_testimony_archive_decodes_and_the_responses_replay_the_quotient` (divisor),
`the_world_is_a_core_point_whose_commit_counts_committed_events` (world); and a cross-tree dump
(`.local/p16/`): the `bit_black_box_reconstruction`, `inverse_transport_reconstruction`,
`generative_transport_prediction`, `causal_state_grammar_experiment` and
`divisor_receiver_reconstruction` drivers run on the base tree `4dff57c8` and on this change at
`5b7c89ab`: every transition receipt (1,454 across the five) and, for all but the causal-state
driver, the digest of every successor standing (archives and the two new statistics removed)
byte-equal event by event, stdout equal; the repository `causal_state_grammar_experiment` trace,
now written from each event and its radiation, is byte-equal to the base trace written from the
retired archive (1,013 rows).

Owed: `ExactEventLaw` itself still returns the law's standing type rather than a `HolonLaw`
advance (no energy balance is declared for the event laws); the kept standings without an
occurrence set (`arithmetic_phase`, `local_star`, `physical`, `simplicial`, `algebraic`,
`holonic_complex`, `sheaf_diffusion`) and the one `HolonRest` codec named in the programme table.

## Handoff, September 23: phases 11, 12a and 12b were paused mid-packet

[established-bounded; source-inspected] Landed on `main`: phases 9 (`5c4bb58a`), 10 (`4dff57c8`),
13 (`5b7c89ab`), 15 (`7e204283`) and 16 (`009e8363`). Phases 11, 12a and 12b were stopped
mid-work when the disk filled. The original WIP branches remain preserved locally; phase 11 has
since been transplanted to an isolated continuation branch:

| Phase | Branch (worktree) | Base | Last step reached | Remaining |
|---|---|---|---|---|
| 11 resident constitutive views | Original `wip/consolidation-phase-11` (`.local/p11-wt`) remains untouched; continued on `codex/consolidation-phase-11` (`.local/p11-continuation`) | `5b7c89ab` WIP transplanted onto `de6a5300`; pre-v1 source `a6c0c95d`; current source `53e085eb` | Lean AffineContact/HolonObject import built; engine normal 172/172; resident relation/contact/rest 2/10/6; post-v1 host rest 4 passed, 2 CUDA ignored; HNA full suite interrupted by user resource stop | post-v1 GPU v5 remount and focused HNA remount consumers remain unverified; retain HNA interruption receipt and close #68 only after its remaining acceptance scope is resolved |
| 12a field body and session | Original `wip/consolidation-phase-12a` untouched; current source cut on `codex/c-phase12a-current-cut` (draft #110) | Stacked on Phase 11 | Contemporary field/incident operand rest; old frozen/tape and read-only session tags retired; thirteen focused HNA tests and HNA all-targets passed | Remaining ladder/disposition/exposure work and final C acceptance are named in [the Phase 12a map](census/C_PHASE12A_INTEGRATION.md). |
| 12b coupled continuation and field internals | Original `wip/consolidation-phase-12b` untouched; source cuts are stacked on the current Rust owner line | Stacked on Phase 12a | Current engine coupled v7/v12 and published v7 rests; read-only coupled v8–v10 and dependent v1–v6 programme readers retired; unconsumed field-history exterior placement retired. Ordinary field remount keeps all current historical carriers resident. The coupled HNA session writer emits outer v3 only; its read-only v1/v2 envelope readers are retired under §0.2. See the [Phase 12b packet record](census/C_PHASE12B_INTEGRATION.md) for exact verification and remaining gates. | `current_history_source` and contextual lift stay as research operators; complete/contextual/moment material paths keep their named consumers. The `NormalWaveHolon` reception/actuation chart, remaining HNA session/behavior contract and Phase14 remain open. |

The Phase 11/12a overlap in HNA `field_session.rs` and `native_source.rs`, and the Phase 11/12b
overlap in engine `coupled.rs` and `comparison/constitutive.rs`, are resolved in the draft stack.
The original WIP branches remain untouched. Each current cut has its focused source/consumer
receipts; the remaining packets and final integration gates are listed above.

Still open after these: phase 14 (cultivated body, including the repeated apparatus fields phase 13 left);
phase 16's remainder (event laws as a core `HolonLaw` advance with energy balance, the seven unconverted
standings, the single `HolonRest` codec, the `ObservationEcologyStanding` audit); phase 15's owed extraction
(GELU/tanh constants, positional terminal boundary, host per-layer interaction table, core `HolonLaw` chart,
one executor); phase 13's unmerged relational-current and pair-coefficient wrappers.

Build hygiene: `holonic-engine` is one ~548k-line crate. Each feature set, profile and check/test/example
mode builds its own ~1.8 GB rlib and ~6 GB incremental directory. On September 23, `target/debug` held 39 engine
incremental directories (150 GB) and per-worker target directories had reached about 380 GB, which filled the
disk. Use one shared worker target directory, `CARGO_PROFILE_DEV_DEBUG=line-tables-only`, delete a phase's
build directory when it lands, and treat splitting the engine crate along the Holon facets as consolidation
work.

**Phase 17 (target refined by the [repository restructure](THE_REPOSITORY_RESTRUCTURE.md#31-rust-the-main-holonics-library-owns-the-construction)): cut the surviving `holonic-engine` by owner.** Measured September 23. The crate has
548k lines. 202 top-level single-file modules hold 302k of them. The largest directories are `native_ecology`
(79k), `cuda_refine` (38k), `resident_section` (21k), `holonic_intelligence` (20k) and the physical receivers
(`physical_occurrence`, `physicochemical_receiver`, `physical_intake`, about 20k). These are census
areas, not a proposal for six new crates:
- the event laws: the 26 `ExactEventLaw` modules and `world`, about 62k lines, CUDA-free;
- equation extraction: `holonic_intelligence`, `soulkiller`, `foreign_*`;
- the device layer: `cuda_refine`, `resident_section`, kernels, `hardware_cover`, `section_partition`;
- the constitutive field: `native_ecology`;
- the physical and chemical receivers;
- the remaining CUDA-free mathematics.

The target is a substantive main `holonics` library containing the Holon laws, geometry,
extraction, internal HNN and exact ring math in `holonics::ratio::ring`; the shared `no_std`
section ABI remains in `holonics-portable`; `holonics-cuda` owns CUDA realization and section
refusals, with `holonics-apple` later on Brandon's branch. The former host-only `holonic-words`
package is retired.
Public-path and wire handling follows the restructure's audited migration map. Run it after
phases 11, 12 and 14 land, since those phases edit the same modules.
Moving a module first requires a dependency census (`use crate::` edges) to find the acyclic cut. The
census is the first step of the phase.

## Overgrowth census and retirement programme (September 23)

[established-bounded; measured] Brandon's ruling: we are the only workers, and consolidation includes
deleting what is superseded, unconsumed or outdated. Git history is the archive. The tracked tree at
`c9012f17` (lines of `.rs/.lean/.py/.md/.cu/.cuh`):

| Owner | Lines |
|---|---|
| `holonic-engine/src` | 548,225 (196 top-level modules; 202 single-file modules hold 302k) |
| `holonic-engine/examples` | 110,723 (178 examples) |
| `holonic-life` src + examples | 161,327 + 154,732 |
| other crates (`hna` 53k, `core` 36k, `body` 24k, `mount` 17k, `membrane` 16k, `relational-geometry` 21k, …) | about 200k |
| Lean `ElementaryHolonics` | 485,811 in 1,387 files. The `Framework` closure is 188,222; the research umbrella adds 293,276 (Millennium 248,698, RH 20,703); 23 files (4,313 lines) are imported by nothing |
| `research/` | 290,470 |
| `docs/` | 39,095 |

The `model_surface` row above is only the historical `c9012f17` inventory. R1 later confirmed
no in-repo consumer beyond the module's own tests, transferred its exact readout scope to
[`TABLET_THE_REALIZER.md`](../canon/TABLET_THE_REALIZER.md#143-the-holomorphic-half-is-owned-and-it-is-aperture-complete-by-a-theorem),
and retired the Rust prototype. Its former implementation gaps are documented there; the old
line count does not describe a current owner.

Engine consumer census: a module counts as consumed if some file outside it references
`crate|super|holonic_engine::<module>`. Multi-line `use` lists and re-exports through `holonics` or
`holonics-hna` can hide a consumer, so confirm each zero with a build before deleting.
- **41 modules, 63,060 lines, have no referencing file:**
  - Event laws: `observation_ecology` 4750, `prime_ecology` 4138, `local_star` 4020, `field_atlas` 3072,
    `causal_state_grammar` 2562, `organizational_grammar` 2367, `divisor_reconstruction` 2283,
    `receiver_phase_atlas` 1933, `generative_transport` 1908, `coupled_informant` 1834,
    `wave_propagation` 1822, `atmospheric_inverse` 1730, `causal_traversal` 1660,
    `holonic_complex` 1336, `physical` 942, `arithmetic_phase` 828.
  - Receivers and dimensions: `acoustic_receiver` 3086, `graph_receiver` 2547, `dimensional_receiver` 1828,
    `arithmetic_dimensional` 1275, `receiver_ecology` 740.
  - Release, presentation and platform (historical R0 source sizes; `artifact_release` was retired in R1 #65): `artifact_release` 4328, `returned_conduct` 1882, `bridge` 1581,
    `model_surface` 887, `platform_x11` 384, `platform` 295, `live_presentation` 281, `display` 133.
  - Other: `cuda_relation` 1564, `implicit` 990, `phase_current` 850, `soulkiller_witness` 580, `conic` 527,
    `basin` 450, `atlas` 422, `mode` 334, `executor` 298, `parameter` 244, `resource` 203, `device` 166.
- **40 more modules (79,601 lines) have only one or two referencing files.** The largest:
  `physicochemical_receiver`, `design_selection`, `fold`, `evaluation_discipline`, `edit_rigidity`,
  `identity_atlas`, `iwasawa_tower`, `presentation`, `standing`, `receiver`, `curvature_bridge`,
  `derivation_curvature`, `cultivated_rest`, `returned_reading`, `causal_body`,
  `conditioned_static_response`, `sheaf_diffusion`, `bit_causal`, `derivation_codec_intake`,
  `inverse_transport`.
  Their consumers are often a single example.

[project-postulate] Phase 16 consolidated the scaffolding of event laws that nothing consumes. That was
effort spent on overgrowth. From now on, each phase begins with retirement and consolidates only what
remains. Order:

1. **Retirement census (R0).** For every engine module, life module and example, and every Lean file
   outside `Framework`, record its consumers (build-confirmed), its superseding owner if any, and one
   disposition: *keep and own* (law, owner, consumer), *fold* (its law moves into the owner that
   supersedes it), or *delete*. Lean research modules (Millennium, RH) are kept only where a
   `Framework` owner, a live campaign or a cited record consumes them. Otherwise they are deleted or
   folded into their owner.
2. **Deletion passes (R1–R3).** R1: engine modules and examples with no consumer. R2: life modules and
   examples tied to retired experiments. R3: Lean files outside every closure, then umbrella-only
   research modules. Each pass needs a workspace check, the Lean `Framework` build and the suites of
   the surviving owners. `lean_citations` and doc links are updated in the same commit.
3. **Compatibility debt (R4).** Remove the `pub type` aliases and legacy wire decoders added in
   phases 9–16 unless a saved artifact we still use needs them, and name that artifact.
4. **Consolidation phases 11, 12 and 14** continue on what remains (WIP branches above).
5. **Crate cut (phase 17)** follows the main-library graph in the repository restructure, on the
   reduced engine; the former six-way bullet list is a census, not a package proposal.
6. **Documents and records (R5).** `research/` (290k) and `docs/` get the same census. Superseded
   records are deleted or folded into their guide, and the research routes are updated.

The uncommitted `formal/.../RH`, `Millennium` and `Computation` files and the September 22–23 records
in the working tree are active work in this tree and are ours. They are committed or retired inside R0.
They are not left as "another agent's" files.
