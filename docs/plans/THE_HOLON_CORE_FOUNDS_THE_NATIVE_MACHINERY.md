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
The occurrence archive (`FieldArchive`: `enable_history_archive`, `archive_history_before`,
`remount_with_history_archive`) is enabled only by engine unit tests. Retirement landed: both
archive entries now refuse a source-only field before creating a file, and the field doc marks
`history`/`archive` as the legacy occurrence clock. Tests:
`field/rest/tests.rs::source_only_field_refuses_occurrences_at_runtime_and_at_rest` (runtime
refusal, empty rest, remount, archive refusal, grafted legacy occurrence refused) and
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
`holonic-membrane`/`holonic-body` register carriage until the chart exists; `DepositLedger`; legacy wire
decoders. Each phase: disposition table, equality tests, caller migration, deletion, full suites.

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
