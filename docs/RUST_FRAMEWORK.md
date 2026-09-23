# Holonics as a Rust library

[definition] `crates/holonics` is the framework entry point (`publish = false`). Its core,
structure and geometry paths are still re-exports awaiting their M1 source moves. HNN application
and wire identifiers retain `hna`; the workbench imports their implementation packages directly.

[project-postulate] This table records the **current** public paths. The
[repository restructure](plans/THE_REPOSITORY_RESTRUCTURE.md#31-rust-the-main-holonics-library-owns-the-construction)
turns this package into the substantive owner of the Holon law/geometry and the
backend-neutral HNN law and port; `holonics-cuda` receives the resident HNN and later
`holonics-apple` implements the same port. `hna` paths are replaced, not forwarded, when their
callers move; every old save-format reader goes. Target package names
are not yet importable.

[definition] The [HNN composition guide](HNN_COMPOSITION.md) describes the model's semantic
assembly, with its [governing model formula](HNN_FORMULA.md). The dependency split below improves library
access; it does not make distinct field/full-operator states interchangeable or complete the
general model architecture.

| Public path | Owner and scope |
|---|---|
| `holonics::core` | Temporary re-export of `holonic-core`; M1 will move the Holon law and exact foundation into this crate |
| `holonics::structure` | Temporary re-export of `holonic-structure`; M1 will move its surviving structural carriers into this crate |
| `holonics::geometry` | Temporary re-export of `relational-geometry`; M1 will move exact frames and receiver maps into this crate |
| `holonic-engine` | Current direct owner of engine mathematics, constitutive fields and resident execution; resident execution moves to `holonics-cuda` |
| `holonics-hna` | Current direct owner of HNN sessions and application adapters; its backend-neutral HNN law moves into `holonics`, resident execution to CUDA |

[definition] The M1 façade cut removed `holonics`’ `native` feature and its direct dependencies on
`holonics-hna`, `holonic-engine` and `life`. The workbench already declared those crates directly
and now imports them by their package crate names. `holonics` therefore builds without pulling in
the CUDA-bound engine through its own manifest.

```rust
use holonics::geometry::{ExactExpr, integer, rat};

// A declared exact chart calculation; the scalar alone is not a situated occurrence.
let two = integer(2);
let half = rat(1, 2);
assert_eq!(two * half, integer(1));
let unevaluated = ExactExpr::symbol("source_parameter");
```

[definition; M1 transition] The engine and HNN remain direct packages for current consumers; no
`holonics::engine`, `holonics::hna`, `holonics::soulkiller` or `holonics::interop` forwarding path
remains. Main still re-exports `core`, `structure` and `geometry` pending their owner moves. Advanced
mathematical modules and the resident HNN have not yet moved into their target owners.

## Productive local generator construction

[definition] The [engine blueprint](ATHENA_ENGINE_BLUEPRINT.md#actual-owners-and-the-exact-assembly-join)
links the operative field's existing forward, paired adjoint and observed-material update
to the application body. `respond_to_material_observation` is a direct field update; the
field-to-normal-predictor test is a different application and does not discharge this join.

[definition] Import `ResidentConstitutiveFibre`, `ResidentConstitutiveCurrent` and
`ConstitutiveFibreRest` through `holonic_engine::native_ecology::constitutive_fibre` until their
engine owner moves.
The existing resident relation owns observation-founded formation and later current transport.
Its rest carries learned basis, source chart and chronology, without an occurrence archive.
The [native guide](NATIVE_HNA.md) states the point/family and whole-model boundaries.

[historical] The former generic field/model wrapper and byte-field cultivation adapters were
[retired](../archive/implementations/2026-09-09-byte-field-cultivation/README.md) after the
[representation audit](../research/records/2026-09-09_THE_BYTE_CLOCK_AND_OCCURRENCE_EXPANSION_ARE_NOT_GENERATOR_CULTIVATION.md).
`NativeFieldModelSpec`, `NativeSavedField`, `with_native_field`, and the alpha text/material/session
modules are no longer exported by the SDK. Core field mathematics and older phase-session APIs
remain at their declared scopes. `hna::alpha::exposure` remains the source reader.

[definition] A mathematical client should import the relevant owner through these qualified
paths. A codec supplies an exterior realization and receiver; it does not define semantic
identity or native adjacency. The [owner map](ARCHITECTURE_MAP.md) connects further elementary,
physical and computational subjects to their formal and executable owners. Lean stays separate
verification apparatus. The [native](NATIVE_HNA.md), [Athena](ATHENA.md) and
[interoperability](INTEROPERABILITY.md) guides retain the different runtime and artifact scopes.

[definition] Exact transcendental use preserves the [constraint mode](CONSTRAINT_MODES_AND_RECEIVER_FACES.md)
and its receiver remainder. `CertifiedSeries` retains the exp/cos/sin expression species and
oriented tail; `AlgebraicRoot` retains polynomial/branch isolation; rational kernel transport
uses its implicit normalized-log relation. A display evaluator does not establish a native
state or branch. The exact phase reference composes these existing owners into actual interval
currents and receiver decisions; no live Lean invocation or floating midpoint enters the map.

[established-bounded; implemented-exact] The [analytic construction](ANALYTIC_FLUX_AND_RECEIVING_BASINS.md)
is exported through `holonics::geometry`: `ComplexJet2` exposes logarithmic current, residual
velocity, changing-source residual velocity and the relaxed release/differential.
`certify_capture` and `propagate_to_capture` consume that same enclosed source callback.
`mean_value_release` retains the whole source region through its centered differential
inclusion; failed/exhausted propagation returns the complete current region. The actual ζ
application uses the existing Euler–Maclaurin jets and independent η winding receiver.
These are CPU exact analytic owners, with source-domain and same-source certificate contracts;
they do not invoke Lean or substitute for the resident GPU field implementation.

[established-bounded; implemented-exact] `holonics::geometry::project_point_with_motion`
now composes the declared frame route and orientation with source velocity and the combined
chart rates `L̇,ḃ`; it returns the existing projected face plus its exact derivative.
`project_receiver_point_rate` covers the four existing projection laws with their singularity
domains. The caller supplies the actual trajectory rates, not a difference inferred from two
samples. The existing optical receiver example consumes this API with a proper-time receiving
world-tube and exact photon boosts. [Receiver holarchy](RECEIVER_HOLARCHY.md) connects that
spatial chart to the containing Holon's material/current state and compression family.

## Mathematical operators and model assembly

[definition] The [computational Holon contract](HOLON.md) identifies the object represented
by the library's tensor/section charts. `ResidentSection` and current views are numerical
representations; their field/relation owners supply incidence, frames, laws and joint
families. A scalar presentation plus arbitrary retained data proves no reconstruction law.
The `Face::map_scalar` documentation now states that its map can be noninvertible.

[definition] The public mathematical operation vocabulary is the
[Holonic tensor/Dirac interface](HOLON.md#high-level-holonic-interactions). It already has
concrete operator counterparts: `BilinearOperator::apply`, `BilinearRealization::then_receiver`,
`join_receivers` and `then_fixed_right`; native `bilinear_features`, `advance_bilinear_contact`
and `read_image` execute their declared resident interactions. Their documentation names
the high-level tensor action and contractions. The foundation's four-map tuple proves the
object relationships; callers should not reconstruct that tuple for every supported operation.

[established-bounded; implemented-exact] `BilinearOperator`, `BilinearProductCore` and
`BilinearRealization` now provide complete input `differential` and covector `pullback`.
The factorized realization performs them through its factors and receiver without expanding
its output interaction tensor. `precompose_ports` carries actual new-to-old linear maps and
rederives the receiver family, including new freedom under a rank drop. The name does not
assert invertibility. Callers still supply the correct physical/semantic chart relation;
matching dimensions alone never established that relation.

[established-bounded; implemented-exact] Scalar `DiffusionReceipt::energy_balance` and
`ExactSheafDiffusionLaw::energy_balance(receipt,event)` expose one shared
`DiffusionEnergyBalance`: signed source work, constitutive dissipation, implicit-step defect
and exact residual. Both laws consume the identity on enactment; the existing native
circulation adapter consumes and carries it at its public boundary. The sheaf method checks
its actual graded source certificate and uses both Hodge coboundaries. Existing receipt wire
fields remain; `energy_departed` keeps its meaning as an endpoint storage difference and is
not promoted to thermal energy. These are exact CPU mathematical/adapter operations, not a
new GPU fluid solver or a completed native Q-field implementation.

[established-bounded; source-inspected] Holonics already has reusable Rust mathematical and
learning libraries. The September 14 source inspection distinguishes their algorithms from
the model that currently consumes them. Re-exporting an owner supplies library access; it
does not join the model's data and execution. This is the concrete translation boundary for
the [formula](HNN_FORMULA.md), not a proposal for another `holonics-ml` wrapper crate.

| Mathematical contract | Existing library implementation | Actual model connection |
|---|---|---|
| Exact linear maps, preimages and factorization | `holonic_engine::exact_linear` (while the source owner remains in `holonic-core`), including `ExactRatMatrix::factor_receiver` | `NativeMathematicalSession` constructs resident linear/bilinear operators and parameter families. Its operator/product/predictor maps are application storage, not one assembled field model. |
| Normalized attention, weighted mode summaries and descended actions | `exact_linear::KernelModeReduction` and `KernelModeSummary`; formal `AttentionModeCompression`, `GeneratorModeQuotient` | The reducer's callers are its example and unit tests. It uses `ExactRatMatrix`/`Rat` on the host. Native consumption requires lowering the derived operators and current columns through existing resident owners; do not run a host semantic replay loop. |
| Normalized vector-current transport and learning differential | `exponentiated_ratio::NormalizedKernel::{apply,differential,pullback,fit_step}` | Exact log-rational kernel chart; binary sigmoid and complete value/potential returns. `connected_holonic_field` composes it into the reference field that drives the synopsis. It is exterior CPU execution. |
| Native multihead block and normalized field return | Earlier `operative_atlas` / `ExtractedOperatorSession`; active `NativeConstitutiveField::normalized_material_return` | The earlier graph has Q/K/V, phase, multihead contact, residual/gated reaction and adjoints. The active field has grouped exponential and material/current pullbacks; width two is a binary normalization. These are actual mechanisms with different consumers, not absent theory. |
| Incidence, field current and boundary/interior scattering | `native_ecology::constitutive_fibre::NativeConstitutiveField`, operative field kernels | `NativeCoupledBody::from_field` now executes this field directly with local reaction. The earlier coupled boundary test remains a separate field-to-predictor application. |
| Material differential and adjoint | `field/junction/operative/response.rs`, `propagation.rs` and their resident kernels | The field target adapter reuses the native paired adjoint on the retained producing D/current; `observe_field` publishes its contact response with the local reaction material. |
| Normal equations and condition/preimage inference | `ResidentNormalMaterial`, `ResidentConditionCurrent`, `ResidentGeneratorNeighborhood` | Normal material is attached to the neighborhood and consumed by coupled generation. Keep that actual learning law available; its fixed features do not prescribe every HNN operator. |
| Joint generation and dependent parameter families | `holonics_hna::native::NativeCoupledBody` over the field-backed, normal-wave or dependent representations | `generate_field` produces the joint field section; `observe_field` uses its original source/material; `SavedCoupledBody` persists local trained state. `NativeFieldSession` binds whole text and partial regions through the shared stream. JointRegions puts context into x and supplies activity/observation maps; `generate_received_field` holds given coordinates at the affine receiver. Target masks precede the full paired adjoint. Producing D/M, receiver/extent and failed-output delivery reopen. Content-dependent refinement and economical larger sources extend this explicit chart. |
| Spatial/temporal modal closure and boundary memory | `receiver_history_compression`, `exact_linear`, operative current factors; formal `ReflectedBoundaryMemory` | Reuse factor/recurrence algorithms for the actual model action. The dependent coupled implementation still evaluates its retained programme. A fixed-linear compiler is available but does not itself compile changing material. |

[project-postulate] Library design follows these mathematical operations. A reusable owner
provides its operands, application/composition and required differential or factorization;
the corresponding CUDA implementation realizes those operations in the declared exact/enclosed
representation. The public HNN session consumes them. Keep mathematical reference code
available independently where the dependency graph permits; a full workspace move is not
required before composing the current native model.

[definition] For the object's intrinsic recursive geometry, use the
[manifold/recurrence route](HNN_FORMULA.md#one-object-its-charts-and-its-recursive-geometry):
`SimplicialComplex`, `GradedCausalComplex`, torus phase and connection owners, then the current
and recurrence/preimage owners. Heads expose local/modal section operations within this
field. The log-rational linear reference validates its own derivative; it does not prescribe
HNN's nonlinear flow, intrinsic dimension or topology. The new analytic twelve-phase
illustration is an exterior numerical realization of the design equations, not a second
native runtime or a replacement product.

[established-bounded; source-inspected] The September 14 connected-mechanics audit found
navigation and composition failures: the formal architecture chart, normalization calculus,
old full-operator graph, active field adjoints and physical leader guide were reachable in
separate subject lists but the synopsis did not follow a current through them. The
[formula](HNN_FORMULA.md#one-connected-tensor-computation) now supplies that operation-level
route; its reference computation feeds the actual figures. This repairs discoverability
without claiming that reference code installs the composed native model.

[definition] Translation from Lean is translation of a specified construction. A formal
existence statement or `noncomputable` quotient does not choose an executable decoder. For
finite linear boundary reduction, the decoder/action is already constructive: factor
`E_next[A B]` through `[E 0]` using `ExactRatMatrix::factor_receiver`; consume the resulting
map or its actual separating vector. That is a library operation with a mathematical
contract. A new collection of theorem-named wrapper types would not improve it.

[established-bounded; source-inspected] Retention also crosses this boundary. The field's
`history: Vec<HeldField>` currently supplies occurrence counts, delayed material/current
references and rest reconstruction; operative current-factor condensation already reduces
some retained current data. The coupled dependent body evaluates its operation prefix.
These consumers explain the current representation, not a mathematical requirement to store
every event. Reconcile them around live internal modes, closed statistics and outstanding
comparison operands; keep chronology as chronology rather than making a vector of old fields
its necessary implementation. Existing evidence and rests must remain recoverable during
that migration.

[project-postulate] The next integration changes the composed model, not the public spelling
of these APIs: execute the operative scattering law and its learned/local transformations
through `NativeCoupledBody`, make the output differential reach the same material, and compile
the repeated action with its internal modes. The blueprint and roadmap own this work. Retain
the useful mathematical-session API and historical `hna` identifiers as applications and
compatibility surfaces.
