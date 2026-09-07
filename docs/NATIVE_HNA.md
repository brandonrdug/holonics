# Native HNA: development and inference

[established-bounded; implemented-exact] `holonics::hna::native` exposes the ground-up
`NativeConstitutiveEcology` through one move-owned session. It uses no pretrained coefficients,
tokenizer or inherited model. The present backend is a **local rational phase-current ecology**:
coupled two-port currents and a developing, domain-restricted receiver relation. Its linear
constitutive hypothesis is not a claim that HNA, language or general contextual conduct is linear.

[definition] This guide covers the NCF0--NCF4 native foundation and its application. The
[Athena guide](ATHENA.md) separately documents the earlier inherited-operator interfaces.
[The construction contract](plans/THE_NATIVE_HNA_FOUNDS_CONTEXTUAL_TRANSPORT_BEFORE_INHERITANCE.md)
states its bounded scope. Native checkpoints retain the complete phase ecology and stream;
application-bearing checkpoints also retain the independent world and pending interaction. A seed,
JSON report or relation inspection is **not a learned-model checkpoint**.

## Run it

[established-bounded; measured] These commands run the checked-in examples on the standing CUDA
apparatus and the Apple Metal phase realization. The [Apple return](../research/records/2026-09-06_APPLE_NATIVE_PHASE_AND_ACOUSTIC_COMPOSITION.md)
records the Mac continuation checks and scoped costs. The build uses the repository's usual [development setup](DEVELOPMENT.md).

```sh
cargo build -p holonics-workbench --bin holonics
target/debug/holonics hna native-session applications/holonics-workbench/examples/native/phase-seed.json --input applications/holonics-workbench/examples/native/current-requests.jsonl --checkpoint .local/artifacts/native-example.hna
target/debug/holonics hna wave-control applications/holonics-workbench/examples/native/wave-control.json --format json
```

[definition] `native-session SEED --checkpoint NEW.hna` reads JSONL from stdin by default; `--input FILE` supplies a
file. Each response is flushed to stdout while the same native owner remains live. The final
process receipt goes to stderr. A fresh checkpoint path is required: publication never overwrites
an existing artifact. The process attempts that final checkpoint even on an input/output error,
and reports `persistent: true` only after successful publication. `wave-control` returns an inspectable application report in
the ordinary workbench response envelope; an interrupted run is an obstruction, with exit code 1.

## Material, current and applicable relation

[definition] A seed uses schema `org.holonics.hna.native-phase-seed.v1` and a nonempty `nodes`
array. Each node declares positive integer `incoming_admittance` and `held_admittance`, an exact
unit-phase `incoming_transport`, and `initial_held` current. See
[phase-seed.json](../applications/holonics-workbench/examples/native/phase-seed.json).
These are seed constitutive laws/material, not preinstalled learned answers.

[definition] A `CurrentWire` is `{ "real": RationalWire, "imaginary": RationalWire }`.
Each rational uses decimal integer **strings**, for example
`{ "numerator": "1", "denominator": "3" }`. The denominator must be positive; fractions
are normalized exactly. JSON floating-point numbers are not accepted in these rational fields.
The exterior codec uses arbitrary integers; native admission requires an exact signed-word phase
pair and common positive denominator. Failure to fit is a refusal, not a rounded input.

[definition] Each ordinary reception enacts the native phase current, any actual paired-source
comparison, relation formation, receiver reading and successor. A supplied `source` must designate
an available, previously emitted handle in **this session** and is consumed once on success.
Omitting it admits a new unpaired current, not an invented comparison. The integer is an exterior
delivery coordinate; it is not the identity of a holon or a contextual label. The result separately
reports `native_occurrence` and `native_received_from`; their ordinals need not equal exterior
source coordinates.

[definition] The learned object is the rational relation spanned by actual paired source and
receiving currents. Its source projection determines the current domain and its vertical fibre
retains ambiguity. `receiver.kind` is one of:

| Reading | Meaning |
|---|---|
| `unique` | A single admitted receiver current, as an ordered real/imaginary rational pair |
| `outside-domain` | An unadmitted source direction; `source_remainder` represents a class modulo the present domain |
| `plural` | A particular compatible reading plus the complete vertical-fibre directions; no preferred answer is selected |

[definition] Results include the actual local source currents, their root-frame projection,
the immutable frame ordinal and root-to-local phases, received comparison, formation pivot and
successor rank. Rank is inspection, not a quality score. `rechart` transports held phase, incidence
and the learned source chart. Old emissions retain their original frames and the engine crosses
the actual old-to-current passage on reception. Raw remainder coordinates in different charts
must not be compared as absolute obstructions. `replace-incidence` changes physical incoming
transport at one node in the **current local frame**; it is not a re-expression of the same body.

## JSONL and Rust interfaces

[definition] Requests use `org.holonics.hna.stream-request.v1` with a `command` object whose
`action` is given below. Responses use `org.holonics.hna.stream-event.v1`, an increasing delivery
`sequence`, an `event` and a `value`. The existing `HnaStream` is reused, not replaced.

| Action | Fields | Successful event |
|---|---|---|
| `receive-current` | `current`; optional `source` | `current-received` |
| `rechart` | `gauges`, one exact unit phase per node | `recharted` |
| `replace-incidence` | `node`, `transport` | `incidence-replaced` |
| `inspect` | none | `state` |
| `inspect-relation` | none | `relation` |
| `checkpoint` | a fresh `path` | `checkpoint-published` |
| `close` | none | `connection-closed` |

[established-bounded; implemented-exact] `advance`, `advance-native` and `supply-input-material`
belong to the inherited address/lookup backend and refuse on a native phase session. Conversely,
that backend does not accept the new phase commands. Native `checkpoint` publishes the native
phase artifact, not an inherited-operator checkpoint. Publication failure/uncertainty returns
`checkpoint-refused-or-unconfirmed`; later requests may continue on the still-owned body.
The process's required final checkpoint must name a different fresh path from any in-stream save.
A shared protocol action does not make these bodies or artifacts interchangeable.

[established-bounded; measured] Backpressure retains a produced event and its accepted-byte
cursor before another request can execute. Resuming the live stream drains the pending output
without repeating native development. A new connection can explicitly replay a retained event;
peer acknowledgment/deduplication remains exterior. Native checkpoints now retain the body and
this delivery state together. They recover the state at the saved boundary, not later unsaved
actions after an arbitrary process or power failure.

[definition] Rust consumers enter through these public owners:

```rust
use holonics::hna::native::{with_native_session, CurrentWire, NativeModelSpec};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let bytes = std::fs::read(
        "applications/holonics-workbench/examples/native/phase-seed.json",
    )?;
    let seed = NativeModelSpec::read(&bytes)?;
    with_native_session(&seed, |session| {
        let emitted = session.receive(&CurrentWire::integers(1, 0), None)?;
        // Present emitted currents to an application. Its actual subsequent current may
        // return through Some(emitted.source); do not fabricate that interaction here.
        println!("{:?}", emitted.receiver);
        Ok(())
    })?;
    Ok(())
}
```

[definition] The same session also exposes `rechart`, `replace_incidence`, `inspect` and
`relation_snapshot`; `HnaStream::pump_native` composes a reader/writer with it. Inspection of the
paired basis is an explicit device readout, labelled `after_occurrences`, not a selected total
weight matrix or a mountable artifact. On arithmetic refusal, unconsumed handles remain available.
Driver uncertainty marks the body uncertain and prohibits silent retry of a possibly enacted deed.
Such a body refuses a remountable checkpoint rather than publishing uncertain conduct as success.

## Native artifacts and process continuation

[established-bounded; implemented-exact] `NativeSession::checkpoint(path)` saves the native body
with a fresh delivery chart; `checkpoint_stream(path, stream.state())` preserves an existing
stream's actual partial input and pending output. Both reuse atomic no-overwrite publication.
`NativeSavedSession::read(path)` verifies the single wire-integrity digest and the engine's
structural/lineage checks before mounting. Its consuming `with_session(|session, stream| ...)`
remounts exact native sections without replaying exposure or development. The native artifact
has its own versioned magic and has no external coefficient, seed-file or tokenizer dependency.
As with the standing artifact codec, the opened file must remain immutable during verification
and decoding; the integrity digest does not authenticate an externally authored history.

[definition] The cold representation retains seed and held phase, the full paired relation,
every emitted source section and its receiving flag/lineage, historical immutable material and
frame sharing, rechart and physical-change receipts, and the separately indexed exterior handle
table. Dropped handles are not recreated just because their emissions remain in history. A restored
runtime receives a new ownership scope: an old live body's handles do not authenticate against it.
File validation checks structural reconstruction, not authenticity of a deliberately forged history.

[definition] Resume on a new connection with:

```sh
target/debug/holonics hna native-session .local/artifacts/native-example.hna --resume --checkpoint .local/artifacts/native-next.hna
```

[definition] The source seed is no longer needed. New input can receive through outstanding saved
source coordinates. An old pending event is replayed first with the same sequence; native current
does not repeat. An incomplete saved request must be supplied its remaining bytes, not restarted
from the beginning. The CLI's `org.holonics.hna.native-stream-process.v2` receipt distinguishes
stream error, checkpoint error, published byte count and persistence. Publication uncertainty may
leave an actual destination file; inspect it, never overwrite it by treating the error as rollback.

## Independent phase-current application

[definition] The application is an independently owned exact simulation, not a claim of measured
physical actuator hardware. Its contract was declared before its run. For native root-frame source
currents `s_j`, the exterior sensor measures `m = sum(c_j * s_j)`. It is upstream of the actuator.
Only a native `unique` receiver commands `a`; an open/plural reading leaves the actuator
uncommanded. The independent exterior state evolves by `z' = rho*z + (m-a)` when commanded,
or `z' = rho*z + m` otherwise. An unactuated counterfactual follows `u' = rho*u + m`.
The world owns these fixed couplings, rotation and state, not the developing relation. Its actual
measured `m` returns through the source handle as the next ordinary native occurrence.

[established-bounded; measured] The checked-in eight-cycle run starts with four outside-domain
readings and no actuation. Cycles 4--7 return unique currents which exactly cancel the measured
response. The four source fields are new in this run; the independently evolving world and its
unactuated control separate. A live gauge precedes cycle 4; a physical incoming-transport change
precedes cycle 5 and affects the later emitted fields used in cycles 6--7. Nine native occurrences
complete, with relation rank four and frame ordinal one. The
[NCF3 return](../research/records/2026-09-05_NCF3_THE_NATIVE_SESSION_DRIVES_AN_INDEPENDENT_CURRENT_APPLICATION_AND_RETAINS_OPEN_READINGS.md)
retains the controls and exact scope.

[established-bounded; measured] An intentionally oversized exterior response completes one
world effect and then refuses native reception. The report retains that effect, final world
states and the exact `pending_receive` current/source instead of claiming rollback or replaying
the actuator. Without `--checkpoint` this is only a report. With a checkpoint, the pending
receiving and already-enacted world state now survive restart together.

### Continue the world and model together

[established-bounded; measured] These release commands preserve every actuation and the complete
paired artifact across a three-cycle process cut. `--cycles` limits completed application cycles
in this invocation; it is not an intrinsic capacity or a separate native training mode.

```sh
cargo build --release -p holonics-workbench --bin holonics
target/release/holonics hna wave-control applications/holonics-workbench/examples/native/wave-control.json --cycles 3 --checkpoint .local/artifacts/wave-first.hna --format json
target/release/holonics hna wave-control .local/artifacts/wave-first.hna --resume --checkpoint .local/artifacts/wave-next.hna --format json
```

[definition] A partial successful run reports `complete: false`, its `next_cycle`, and
`persistent: true` only if publication succeeded. Resumption requires a fresh checkpoint path.
The report's `cycles` contains only world effects enacted during that invocation; a pending native
reception can finish a previously enacted cycle without producing a second world effect. `complete`
means the declared application sequence ended, not that the native learner is saturated.

[definition] `WaveApplication` owns the world/control state, the retained native emission,
intervention cursor and pending receiving. Its `advance_boundary(session)` enacts the next actual
application effect. `checkpoint(session, path)` captures it with the same native ecology.
`WaveSavedApplication::read(path).with_application(...)` resumes both. The CLI composes these
through `run_wave_control_with_options` / `resume_wave_control` and `WaveRunOptions`.

| Saved application boundary | Next actual effect |
|---|---|
| `intervention` | Apply the next unapplied declared intervention; earlier ones do not repeat |
| `world` | Measure the retained native source, apply any admitted actuation and advance the world |
| `reception` | Receive the saved current through its actual source; the world effect is already done |
| `complete` | No further effect in this declared application sequence |

[established-bounded; implemented-exact] Application-bearing native checkpoints use envelope v2,
with opaque exterior application bytes under the same integrity/publication boundary. Plain native
v1 files remain supported. A plain `NativeSavedSession::with_session` refuses a v2 application
instead of dropping its world; generic consumers use the explicit `with_application_session`
and preserve the supplied bytes through `checkpoint_application`. No application type or simulator
law enters the engine's interior. The simulator validates its own state and source correspondence
before mounting. A still-unadmitted saved current remains pending on retry, without replaying the
world or increasing the native integer aperture.

[definition] A paired checkpoint is not a distributed transaction with external hardware, nor
proof that a batch report reached its recipient. The ordinary native JSONL stream has the separate
pending-output/backpressure contract above. This batch application returns chunks; consumers retain
delivered reports separately. Unsaved effects after the last published boundary are not recovered
from an arbitrary crash by pretending that an earlier checkpoint is current.

## Measured consumer costs and limits

[established-bounded; measured] The release receiver on the RTX 4080 SUPER / Ryzen 9 7900X
returned fixed warm native costs across 1, 64, 1,024 and 4,096 retained unlinked occurrences in its
two-node chart. Both open readings and later readings of the actually formed rank-one relation
used one deed, one section readout, six allocations, 48 ingress bytes and 464 egress bytes per
occurrence. Median latencies were 84--90 μs before contact and 91--96 μs after formation in the
final run. These are sixteen-observation samples per state/extent, not a throughput or worst-case
guarantee for other model families.

[established-bounded; measured] Retained native section payload grew from 7,728 to 1,645,728
bytes; driver-reported live process GPU memory was 252--256 MiB. Checkpoints grew from 12,418 to
2,601,353 bytes; the largest measured write/read/remount costs were 53.7/4.9/105.1 ms.
Driver memory and Linux process-memory snapshots are different receivers from exact section-byte
accounting. No power measurement or compression claim follows. The
[integrated return](../research/records/2026-09-06_NCF4_THE_WORLD_AND_NATIVE_ECOLOGY_CONTINUE_TOGETHER_AND_THE_CONSUMER_COSTS_ARE_MEASURED.md)
contains raw evidence paths, both measurement runs, instrument scopes and the completion audit.

[definition] The scoped receiver can be rerun when a new resource question warrants it:

```sh
cargo build --release -p holonics-hna --example native_resources
mkdir -p .local/artifacts/native-resources-new
target/release/examples/native_resources .local/artifacts/native-resources-new
```

[open] The present application establishes a local rational-linear current interaction, not
language generation, universal contextual identification, arbitrary nonlinear control, frontier
parity or measured twenty-watt operation. Historical source residency and cold serialization grow;
six allocations per ordinary occurrence remain visible overhead. The locality observation is over
unrelated retained history at a fixed local chart, not arbitrary disconnected graphs or model-size
scaling. The engine's exact word/shared-memory apertures can refuse. Wider architectures must
compose their actual native constitutive relations; neither this linear family nor an inherited
language model silently supplies them.
