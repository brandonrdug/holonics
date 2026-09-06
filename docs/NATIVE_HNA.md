# Native HNA: development and inference

[established-bounded; implemented-exact] `holonics::hna::native` exposes the ground-up
`NativeConstitutiveEcology` through one move-owned session. It uses no pretrained coefficients,
tokenizer or inherited model. The present backend is a **local rational phase-current ecology**:
coupled two-port currents and a developing, domain-restricted receiver relation. Its linear
constitutive hypothesis is not a claim that HNA, language or general contextual conduct is linear.

[definition] This guide covers NCF3's native interface and application. The
[Athena guide](ATHENA.md) separately documents the earlier inherited-operator interfaces.
[The construction contract](plans/THE_NATIVE_HNA_FOUNDS_CONTEXTUAL_TRANSPORT_BEFORE_INHERITANCE.md)
keeps durable native artifacts and integrated resource evidence in NCF4. A seed, JSON report or
relation inspection is **not a learned-model checkpoint**.

## Run it

[established-bounded; measured] These commands run the checked-in examples on the standing CUDA
apparatus. The build uses the repository's usual [development setup](DEVELOPMENT.md).

```sh
cargo build -p holonics-workbench --bin holonics
target/debug/holonics hna native-session applications/holonics-workbench/examples/native/phase-seed.json --input applications/holonics-workbench/examples/native/current-requests.jsonl
target/debug/holonics hna wave-control applications/holonics-workbench/examples/native/wave-control.json --format json
```

[definition] `native-session SEED` reads JSONL from stdin by default; `--input FILE` supplies a
file. Each response is flushed to stdout while the same native owner remains live. The final
process receipt goes to stderr. The receipt explicitly says `persistent: false`: exiting this
version loses the developing body. `wave-control` returns an inspectable application report in
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
| `close` | none | `connection-closed` |

[established-bounded; implemented-exact] `advance`, `advance-native` and `supply-input-material`
belong to the inherited address/lookup backend and refuse on a native phase session. Conversely,
that backend does not accept the new phase commands. Native `checkpoint` currently returns
`checkpoint-refused-or-unconfirmed` and publishes nothing. A new protocol action is not permission
to treat these different bodies or artifacts as interchangeable.

[established-bounded; measured] Backpressure retains a produced event and its accepted-byte
cursor before another request can execute. Resuming the live stream drains the pending output
without repeating native development. A new connection can explicitly replay a retained event;
peer acknowledgment/deduplication remains exterior. This delivery discipline is not crash-safe
native persistence: the current CLI cannot restore this body after process exit.

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

## Independent phase-current application

[definition] The application contract was declared before its run. For native root-frame source
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
the actuator. This is an interruption report, not a resumable checkpoint.

[open] NCF4 still owes complete native session/model persistence, process-separated further
development, transport/application continuation and cold/warm resource measurements. The present
application establishes a local linear-current interaction, not language generation, universal
contextual identification, arbitrary nonlinear control, frontier parity or measured twenty-watt
operation. Wider architectures must compose their actual native constitutive relations; neither
this linear family nor an inherited language model silently supplies them.
