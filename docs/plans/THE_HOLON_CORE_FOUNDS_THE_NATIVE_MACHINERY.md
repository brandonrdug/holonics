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

Constraints: rest/wire compatibility for `SavedCoupledBody`, `NativeIncidentModelRest`,
`CoupledConstitutiveRest`, the complex schema string and custom deserializers; interaction types stay
`Serialize`-only so no wire mints an unchecked object; no device layout change during consolidation;
public names kept; the Lean citation scan extended to `holonic-core`.
