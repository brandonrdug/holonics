# Model interoperability and recompilation

[definition] Holonics supports two directions: inherited model realizations enter through
Soulkiller, and refined Athena variants leave through native persistence or a declared target
architecture. A stable framework must describe both. Container compatibility, model execution
and receiver-exact recompilation are distinct capabilities.

## What the standard formats supply

[established-bounded; source-inspected] [Safetensors](https://huggingface.co/docs/safetensors/main/index)
stores named tensor values and their shapes/dtypes. Architecture and runtime behavior require
additional configuration/code. [ONNX](https://onnx.ai/onnx/intro/concepts.html) can specify an
operator graph with parameters, inputs and outputs, but execution depends on supported operators
and domains. A custom-domain node requires its corresponding implementation.

[interpretation] [Burn's model and record separation](https://burn.dev/books/burn/saving-and-loading.html)
is a useful packaging precedent: model, backend, record, import and execution have explicit
interfaces. Holonics uses its own native recurrence and causal laws; it can offer comparable
application ergonomics without treating Burn's tensor/module vocabulary as its interior ontology.

## Present export behavior

[established-bounded; implemented-exact; source-inspected] The current
[export owner](../crates/holonic-life/src/native_intelligence/morphology_export/mod.rs) operates
on the older `NativeMorphologyArtifact` package family and returns `Exact`, `Projected` or
`Refused`. Exact round-trip preserves that package at its declared scope. It does not establish
that a standard runtime can execute the current full HNA model.

| Target | Current wire and executable meaning |
|---|---|
| Native package | Holonics reconstructs and uses its own declared package. |
| Safetensors package export | U8 `holonics.package.bytes` plus anatomy tensors. This is a standard container holding a Holonics package, not a conventional weight checkpoint. |
| ONNX package export | An IR14 graph using a custom `org.holonics` operation and a package initializer. It requires a Holonics implementation of that operation. |
| Standard Transformer/SSM/diffusion graph | An explicit operator/parameter/state lowering is still required. Existing package round-trips are not that lowering. |

## The outward compiler contract

[definition] A requested target declares architecture, operator set/domain, input/output shapes,
state and reset behavior, numeric format, codec/configuration, admitted receiver/history family,
and target runtime. The export return contains:

1. The target graph/code and coefficient tensors, with required configuration/codecs.
2. A map from native carriers, reactions and state to target operations and state.
3. Numeric conversion and all retained error/enclosure or collapsed-pair testimony.
4. A reconstruction/decoder boundary and resource costs.
5. Matched execution in the actual target runtime over the declared family, including subsequent
   stateful operations—not only a parser opening the file.
6. An exact, projected or refused disposition for that target and scope.

[conditional] A factorized native change can be represented in a compatible target linear chart
either by its base plus `U(Vx)` branch or by a realized coefficient update. That algebraic mapping
does not by itself export nonlinear reactions, quantization, chronology, receiver behavior or
the surrounding ecology. Those mappings must compose and their defects must be retained.

[definition] Target execution is an exterior validation/application action. It does not place
a foreign runtime inside Athena or turn target syntax into native topology. A projected model
can be useful and honestly graded; an exact claim requires its full declared consequence law.
If a target architecture cannot express the required relation, the compiler returns the precise
unsupported operation/state/receiver boundary rather than a mislabeled package.

## The pipeline now to be built on this interface

[open] The full native cultivated checkpoint and standard executable lowering are not yet
returned by the existing export owner. The ordered implementation is native checkpoint/remount,
a target-operation/state map for one supported family, emitted standard weights/graph and
configuration, and matched target-runtime execution. It must then expand by actual adapters to
additional Transformer, diffusion and SSM families. This is the intended route to refining models
with Eros and using them in existing machinery; no new permission or rediscovery of that intent
is needed to scope its concrete construction.

[definition] The public namespace `holonics::interop` exposes tensor/configuration/ONNX intake;
`holonics::interop::packages` exposes the existing package export/import owners. It does not present a stub portable-model compiler
as an implemented conversion. [Soulkiller](SOULKILLER.md) and [Athena](ATHENA.md) state the
corresponding inbound and native-run contracts.
