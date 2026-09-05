# HNA application interfaces

Use the public framework through `holonics::hna`; this crate owns its application adapters.
The [Athena guide](../../docs/ATHENA.md) defines the supported run requests, inference and
developmental sequence, selected-face receipts and persistence boundaries.

- `run_hna` mounts the supported resident realization or admitted restricted SKE material and
  executes an ordered sequence in one continuing native session.
- `inspect_native_restricted_rest` reads a restricted-rest header without CUDA.
- `AthenaTokenApplication` is the exterior tokenizer/decoder, not native model topology.
- `HnaModel::from_checkpoint` and `with_session` restore one continuing native owner;
  `HnaSession::advance`, `checkpoint`, `anatomy` and the declared family are the current public
  persistent-session seam. Checkpoints explicitly pin their separate native base.
- `HnaModel::with_stream_session` and `HnaStream::pump` retain partial JSONL input and pending
  responses with backpressure. Native-plus-transport checkpoints restore both; new connections
  replay a held event without repeating native development. The CLI is `holonics hna session`.
- `acquire_input_material` / `with_input_material` compose separately persisted, immutable
  input-row additions. `HnaSession::advance_native` admits their actually supplied input domain;
  the old inherited-family `advance` remains unchanged. See the guide for checkpoint versions
  3/4, explicit dependencies and the currently incomplete application-output boundary.
- Live `HnaSession::supply_input_material` stages new resident lookup rows without remounting.
- `HnaTextApplication` composes ordinary self-occurrences, declared codec completion and paired
  text/model rest. Its actual comparison exposes unstable additive cultivation at shift 16;
  coherent fixed-morphology output is not a replacement production learner. See the guide.

The lower-level native session remains available from `holonic-engine` for interactive consumers.
Earlier alpha/circulation adapters retain their exact artifact and wire scopes; they are not
checkpoints of the cultivated full operator. The new native checkpoint is distinct from those
older packages. See the Athena guide for versioned requests, required final checkpoints, delivery
limits and the still-bounded admitted family. Standard executable model export is a separate
[interoperability contract](../../docs/INTEROPERABILITY.md).
