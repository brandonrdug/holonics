# HNA application interfaces

[definition] Use the public framework through `holonics::hna`; this crate owns its application
adapters. The [native guide](../../docs/NATIVE_HNA.md) documents the ground-up phase body;
the [Athena guide](../../docs/ATHENA.md) retains the inherited-operator interface and artifact scopes.

[established-bounded; implemented-exact] `native::{NativeModelSpec, with_native_session,
NativeSession}` exposes one developing native phase ecology. Exact-current reception, owned
source handles, live rechart, incidence changes and open/plural receiver readings share the
same engine owner. `HnaStream::pump_native` uses the existing backpressured JSONL delivery.
`native::run_wave_control` composes an independent exterior current system with this public API;
it contains no private learner. `NativeSession::{checkpoint,checkpoint_stream}` and the consuming
`NativeSavedSession::with_session` persist/remount the whole native body and actual handles, with
shared stream delivery state. Native seed/report files remain distinct from these learned models.

## Earlier inherited-operator interface

[established-bounded; source-inspected] These interfaces retain their existing bounded scope:

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
- Text steps request `NativeEmissionReadout::LastRow` through the public readout methods. Only
  that terminal row crosses to the host; the complete resident successor and checkpoint remain
  unchanged. Existing `advance_native` and `observe_native` still return every terminal row.
- The withdrawn `from_native_rest_with_boundary_contact` draft and its inner-wire v2 are
  [archived](../../archive/experiments/2026-09-05-tied-next-arrival/README.md), not active APIs
  or native contextual foundations. The portable-fact framing and CLI promotion were withdrawn. See the
  [contextual audit](../../research/records/2026-09-05_CONTEXTUAL_TRANSPORT_PRECEDES_INHERITED_MODEL_PRODUCTION.md).

[definition] Lower-level native owners remain available from `holonic-engine`. Earlier
alpha/circulation adapters retain their exact artifact and wire scopes; they are not checkpoints
of the cultivated full operator. That inherited-operator checkpoint is also not an artifact of
the new ground-up phase body. See the Athena guide for versioned requests, required final checkpoints, delivery
limits and the still-bounded admitted family. Standard executable model export is a separate
[interoperability contract](../../docs/INTEROPERABILITY.md).
