# Holonics as a Rust library

[definition] `crates/holonics` is the public entry point. It exposes existing implementation
owners; it supplies no second event model, numeric system or learner. The package is currently
used as a path dependency (`publish = false`). HNN application and wire names retain `hna` for
compatibility.

[definition] The [HNN composition guide](HNN_COMPOSITION.md) describes the model's semantic
assembly and its actual remaining attachment. The dependency split below improves library
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
