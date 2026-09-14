# Holonics as a Rust library

[definition] `crates/holonics` is the public entry point. It exposes existing implementation
owners; it supplies no second event model, numeric system or learner. The package is currently
used as a path dependency (`publish = false`). HNN application and wire names retain `hna` for
compatibility.

[definition] The [HNN composition guide](HNN_COMPOSITION.md) describes the model's semantic
assembly, with its [governing model formula](HNN_FORMULA.md). The dependency split below improves library
access; it does not make distinct field/full-operator states interchangeable or complete the
general model architecture.

| Public path | Owner and scope |
|---|---|
| `holonics::structure` | `holonic-structure`: typed relational carriers, incidence, lineage and atomic membranes; `no_std` with allocation |
| `holonics::geometry` | `relational-geometry`: exact expressions, frames, receiver maps, projection fibres and crossings |
| `holonics::engine` | `holonic-engine`: further mathematical constructions, constitutive fields, resident execution and exterior device/codec owners |
| `holonics::hna` | `holonics-hna`: separately scoped native sessions, experimental conversation apparatus and earlier inherited-operator adapters |
| `holonics::{soulkiller,interop}` | Existing dismantling and package interfaces; their individual domain and artifact contracts apply |

[definition] The default `native` feature includes the admitted application APIs and desktop runtime. Disabling it leaves `structure` and `geometry` available
without the engine, HNN, lifecycle or CUDA dependencies:

```toml
[dependencies]
holonics = { path = "/path/to/holonics/crates/holonics", default-features = false }
```

```rust
use holonics::geometry::{ExactExpr, integer, rat};

// A declared exact chart calculation; the scalar alone is not a situated occurrence.
let two = integer(2);
let half = rat(1, 2);
assert_eq!(two * half, integer(1));
let unevaluated = ExactExpr::symbol("source_parameter");
```

[established-bounded; process-audit] Both the reduced dependency configuration and default
native configuration pass `cargo check` on the desktop. This establishes the dependency split,
not execution of the default backend on a Mac. Many advanced mathematical modules still live
inside the CUDA-bound engine. Porting them or the runtime requires their actual dependency
boundaries, not a claim that all formal Holonics is already available in a portable Rust crate.

## Productive local generator construction

[definition] Import `ResidentConstitutiveFibre`, `ResidentConstitutiveCurrent` and
`ConstitutiveFibreRest` through `holonics::engine::native_ecology::constitutive_fibre`.
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

[established-bounded; source-inspected] Holonics already has reusable Rust mathematical and
learning libraries. The September 14 source inspection distinguishes their algorithms from
the model that currently consumes them. Re-exporting an owner supplies library access; it
does not join the model's data and execution. This is the concrete translation boundary for
the [formula](HNN_FORMULA.md), not a proposal for another `holonics-ml` wrapper crate.

| Mathematical contract | Existing library implementation | Actual model connection |
|---|---|---|
| Exact linear maps, preimages and factorization | `holonics::engine::exact_linear`, including `ExactRatMatrix::factor_receiver` | `NativeMathematicalSession` constructs resident linear/bilinear operators and parameter families. Its operator/product/predictor maps are application storage, not one assembled field model. |
| Normalized attention, weighted mode summaries and descended actions | `exact_linear::KernelModeReduction` and `KernelModeSummary`; formal `AttentionModeCompression`, `GeneratorModeQuotient` | The reducer's callers are its example and unit tests. It uses `ExactRatMatrix`/`Rat` on the host. Native consumption requires lowering the derived operators and current columns through existing resident owners; do not run a host semantic replay loop. |
| Incidence, field current and boundary/interior scattering | `native_ecology::constitutive_fibre::NativeConstitutiveField`, operative field kernels | The field owns actual material and internal current. The recent coupled boundary test uses field observations to fit normal prediction; this establishes that surrogate binding, not execution of the same field law by every public session. |
| Material differential and adjoint | `field/junction/operative/response.rs`, `propagation.rs` and their resident kernels | `material_contact_response`/`apply_material_contact_response` already compute and apply a declared contact response. Bind the requested output differential through these operators in the same model invocation. |
| Normal equations and condition/preimage inference | `ResidentNormalMaterial`, `ResidentConditionCurrent`, `ResidentGeneratorNeighborhood` | Normal material is attached to the neighborhood and consumed by coupled generation. Keep that actual learning law available; its fixed features do not prescribe every HNN operator. |
| Joint generation and dependent parameter families | `holonics::hna::native::NativeCoupledBody` over `ResidentNormalWave` or `ResidentCoupledConstitutive` | This is the selected application owner to extend for the composed model. The field's transport/material and modal execution must participate through one owned operation; adding a further competing session does not close that connection. |
| Spatial/temporal modal closure and boundary memory | `receiver_history_compression`, `exact_linear`, operative current factors; formal `ReflectedBoundaryMemory` | Reuse factor/recurrence algorithms for the actual model action. The dependent coupled implementation still evaluates its retained programme. A fixed-linear compiler is available but does not itself compile changing material. |

[project-postulate] Library design follows these mathematical operations. A reusable owner
provides its operands, application/composition and required differential or factorization;
the corresponding CUDA implementation realizes those operations in the declared exact/enclosed
representation. The public HNN session consumes them. Keep mathematical reference code
available independently where the dependency graph permits; a full workspace move is not
required before composing the current native model.

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
