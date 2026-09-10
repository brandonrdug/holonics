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

[established-bounded; computational-witness] The [compiled Rust example](../crates/holonics-hna/src/native/field.rs)
accepts a caller's field recipe, incoming currents and receiver/realization, then performs serial
source-qualified reception, observed local return and native rest through those public owners.
Its serial incidence is an explicit example, not a requirement on other clients. Application
code can handle a response error inside the callback and retain the already-received successor.

[definition] `native::NativeSavedField` consumes the existing `NativeFieldRest` into one
remounted field and its actual linear/shared source slots. `read` and `publish` use the existing
native wire and no-overwrite publication; `with_field_archived` places older source carriers in
a fresh archive without depending on an old machine's archive path. This saves native model
state. A text application's cursor, delivery and pending symbol remain in its exterior session
envelope, whose remount now delegates to the same generic field owner.

[established-bounded; source-inspected] This rest still includes the field's per-occurrence
history. The generic wrapper is not a conversion into compact learned generators. The
[representation audit](../research/records/2026-09-09_THE_BYTE_CLOCK_AND_OCCURRENCE_EXPANSION_ARE_NOT_GENERATOR_CULTIVATION.md)
states the byte-driven recipe, operational history and incomplete HNN composition explicitly.

[definition] `NativeConstitutiveField::surface` exposes a borrowed resident apparatus for typed
current-section composition. It creates no source capability or second field. Use this for
existing resident wave/section ingress; a numeric section remains qualified by the receiving
field's actual chart and lineage.

## Choosing an implementation

[definition] `hna::alpha::exposure` owns the cold conversation source/cursor;
`text_codec` owns the declared byte/part-marker chart; `text_session` borrows one constitutive
field; `checkpoint` preserves that particular session. The field owns learning and recurrence.
`OperativeNormal` fits a finite complex-linear material operator; `OperativeContextual` uses
the existing joint projective source/condition feature. Neither profile name describes the
complete model anatomy. The [joint-field artifact](../research/records/2026-09-09_AC3_THE_JOINT_FIELD_CONTINUES_AND_ITS_NATIVE_ARTIFACT_IS_GENERIC.md)
retains the exposed body's scope. Its fixed byte chart is experimental apparatus, not a learned
general text codec or the definition of HNN. The [deeper construction review](../research/records/2026-09-09_ARCHITECTURE_CHARTS_REQUIRE_COMPOSED_MECHANISMS_AND_FINITE_CONSTRUCTION_RETURNS.md)
recovers the classical/tensor mechanisms and local return's scope.

[definition] A mathematical client should import the relevant owner through these qualified
paths. A codec supplies an exterior realization and receiver; it does not define semantic
identity or native adjacency. The [owner map](ARCHITECTURE_MAP.md) connects further elementary,
physical and computational subjects to their formal and executable owners. Lean stays separate
verification apparatus. The [native](NATIVE_HNA.md), [Athena](ATHENA.md) and
[interoperability](INTEROPERABILITY.md) guides retain the different runtime and artifact scopes.
