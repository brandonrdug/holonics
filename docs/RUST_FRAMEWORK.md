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

[definition] The default `native` feature preserves all previously exposed application APIs
and includes the desktop runtime. Disabling it leaves `structure` and `geometry` available
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

## Generic field assembly

[established-bounded; implemented-exact] `holonics::hna::native::{NativeFieldModelSpec,
with_native_field}` now constructs the existing constitutive field independently of the
medium. The recipe carries seed material, numerical junction and material source/target charts;
it is not a model checkpoint. `NativeFieldModelSpec::found_on` shares a caller's resident surface.
The field's actual occurrence, source/anchor, return, rest and current-family APIs remain in use.
`NativeMaterialResponseChart` makes normalized group/series apertures explicit; generic observed
return belongs to the field rather than `TextFieldSession`. See [composition](HNN_COMPOSITION.md).

## Choosing an implementation

[definition] `hna::alpha::exposure` owns the cold conversation source/cursor;
`text_codec` owns the declared byte/part-marker chart; `text_session` borrows one constitutive
field; `checkpoint` preserves that particular session. The field owns learning and recurrence.
The current `OperativeNormal` profile fits a finite complex-linear material operator from
observed source currents. Its fixed byte chart is experimental apparatus, not a learned
general text codec or the definition of HNN. The [paused construction review](../research/records/2026-09-09_THE_BYTE_FIELD_IS_NOT_THE_COMPLETE_HNN_COMPOSITION.md)
spells out this distinction and the local return's scope.

[definition] A mathematical client should import the relevant owner through these qualified
paths. A codec supplies an exterior realization and receiver; it does not define semantic
identity or native adjacency. The [owner map](ARCHITECTURE_MAP.md) connects further elementary,
physical and computational subjects to their formal and executable owners. Lean stays separate
verification apparatus. The [native](NATIVE_HNA.md), [Athena](ATHENA.md) and
[interoperability](INTEROPERABILITY.md) guides retain the different runtime and artifact scopes.
