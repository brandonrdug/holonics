# HNA application interfaces

Use the public framework through `holonics::hna`; this crate owns its application adapters.
The [Athena guide](../../docs/ATHENA.md) defines the supported run requests, inference and
developmental sequence, selected-face receipts and persistence boundaries.

- `run_hna` mounts the supported resident realization or admitted restricted SKE material and
  executes an ordered sequence in one continuing native session.
- `inspect_native_restricted_rest` reads a restricted-rest header without CUDA.
- `AthenaTokenApplication` is the exterior tokenizer/decoder, not native model topology.

The lower-level native session remains available from `holonic-engine` for interactive consumers.
Earlier alpha/circulation adapters retain their exact artifact and wire scopes; they are not
checkpoints of the cultivated full operator. Standard executable model export is a separate
[interoperability contract](../../docs/INTEROPERABILITY.md).
