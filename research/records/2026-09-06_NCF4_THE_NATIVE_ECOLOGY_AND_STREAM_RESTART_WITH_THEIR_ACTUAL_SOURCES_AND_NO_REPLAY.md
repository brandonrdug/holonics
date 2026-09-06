# NCF4: native ecology and stream restart with their actual sources

**Date:** 2026-09-06. **Position:** NCF4 in progress; this returns native model/session persistence,
not the entire integrated foundation campaign.
**Contract:** [native HNA before inheritance](../../docs/plans/THE_NATIVE_HNA_FOUNDS_CONTEXTUAL_TRANSPORT_BEFORE_INHERITANCE.md).
**Recipes:** [native HNA guide](../../docs/NATIVE_HNA.md).

## Actual retained state

[established-bounded; implemented-exact] `NativeConstitutiveEcology::{rest,remount}` now captures
and consumes a complete cold representation of this native phase owner. `NativeEcologyRest`
retains the resident seed, held phase and paired basis; every historical emitted section;
incoming/predecessor/receiving lineage and returned-source flags; immutable material sharing;
frame occurrences and gauge passages; physical incidence-change receipts; and the separately
indexed slots of actually supplied linear emission handles. It is not `Clone`. Remount installs
the exact sections rather than replaying an exposure log or reconstructing a learned total map.

[definition] The wire is an exterior representation of the local rational-linear constitutive
family already founded in NCF1--NCF2. Its source slots are delivery positions, not contextual IDs.
Only actual supplied handles enter the wire. An unreturned historical emission whose handle was
dropped does not acquire a fresh handle at remount. The restored runtime has a new ownership
scope: old live-owner handles cannot authenticate against it. Immutable sharing is reconstructed
through declared local table incidences, not by merging equal-valued material or hashes.

[established-bounded; implemented-exact] The cold validator checks exact point sections,
shape/grain/aperture, positive native echelon pivots, receiver/status/rank fields, held phase,
seed/material agreement, complete claimed material allocations, frame/gauge reconstruction,
event chronology, receiving-edge uniqueness and returned flags. Bounded wire parsing rejects
truncation, trailing bytes and advertised blobs beyond their containing frame. An uncertain
native deed cannot produce a remountable rest. This structural validation does not authenticate
the developmental history of a deliberately forged artifact.

[established-bounded; measured] Six engine persistence controls returned. A matched uninterrupted
body and a byte-serialized/restored body preserve the entire cold state, held-state pullbacks,
historical frames/material and later developing successors. The controls include no-history
changes, dropped/foreign/duplicated handles, frame-0 sources returned after later gauges, malformed
states and genuinely plural receiver fibres. Remount adds no native deed launches. The physical
CUDA allocation/transfer counters describe the new apparatus realization and are not restored
as fictitious prior allocations.

## Public artifact and pipeline

[established-bounded; implemented-exact] `NativeSession::{checkpoint,checkpoint_stream}` and
the consuming `NativeSavedSession::{read,with_session}` expose this state through the public
framework. The artifact uses distinct native-phase magic/version and contains no external seed,
coefficient-base or tokenizer dependency. It embeds the complete ecology and existing
`HnaStreamState`. The existing `publish_new` remains the only atomic no-overwrite publication
owner; existing transport serialization and prefix-integrity hashing are shared with the older
checkpoint implementation without changing that format. There is one artifact-integrity digest,
not a second identity/checksum registry.

[definition] The CLI is now:

```sh
holonics hna native-session SEED.json --input REQUESTS.jsonl --checkpoint NEW.hna
holonics hna native-session NEW.hna --resume --input LATER.jsonl --checkpoint NEXT.hna
```

[established-bounded; implemented-exact] A fresh final checkpoint path is required before
mounting. The process always attempts that save after pumping, including input/output failure.
Its version-2 stderr receipt separately reports stream error, checkpoint error, published byte
count and persistence. Successful publication sets `persistent: true`; a failed or unconfirmed
publication does not. The stdout remains the actual flushed JSONL response stream. A publication
uncertainty can leave a destination file and does not authorize overwriting it.

[definition] On a new connection, a saved pending event is replayed with its original sequence;
the producing native occurrence is not repeated. An incomplete saved request needs its remaining
bytes, not a duplicate of its prefix. Peer acknowledgment/deduplication remains exterior. A
checkpoint recovers its saved boundary, not unsaved actions after an arbitrary kill or power loss.

## Actual process-separated controls

[established-bounded; measured] The split-input process control first saves after one native
occurrence and a rechart, midway through the next JSONL request. A second process consumes only
the remaining bytes, receives through the saved old-frame handle and closes. Its **entire native
plus transport artifact** is byte-identical to the uninterrupted control, not merely the emitted
face. Two further processes develop both results again through an outstanding source, reaching
three native occurrences and identical complete successor artifacts.

[established-bounded; measured] The broken-output process control receives the first event,
actually closes the child's stdout pipe, then sends the second current. That second native
occurrence executes; failed delivery leaves its produced event in the final checkpoint. A new
process replays that event, closes without another native occurrence, and produces the same
complete artifact as the uninterrupted two-occurrence control. This is a real OS pipe failure,
not only a mock writer test.

[established-bounded; measured] The public API controls additionally preserve accepted-output
byte position, partial input, complete ecology equality and further source reception. Corrupted
and truncated artifacts refuse before native mounting; the older inherited checkpoint reader
does not accept the native-phase artifact. A repeated destination is refused while the existing
file remains intact. Neither inherited model files nor pretrained tokenization are used.

[established-bounded; measured] A retained operator run additionally produced
`.local/artifacts/ncf4/current-session.hna` (3,610 bytes; two occurrences, frame one, rank one,
delivery sequence five). A second actual CLI process read only that checkpoint plus the declared
later JSONL current, and produced `continued-session.hna` (4,234 bytes; three occurrences, rank
two, sequence seven). Its census contains one native deed, not a replay of the preceding two.
Both processes returned exit zero and confirmed persistence. The `*-capture.jsonl` files beside
them preserve stdout events plus stderr process receipts; `later.jsonl` is the continuation input.
These small artifact sizes are storage observations, not a compression or general-capability claim.

## Checks and owners

[established-bounded; measured] Completed checks in this pass:

| Command / scope | Result |
|---|---|
| `cargo test -p holonic-engine --lib native_ecology::constitutive_fibre -- --ignored --test-threads=1` | 28 native controls passed in the isolated run |
| Final focused `... constitutive_fibre::circulation::rest -- --ignored --test-threads=1` | Six persistence controls passed after cold-validation refinements |
| `cargo test -p holonics-hna --lib native:: -- --ignored --test-threads=1` | Eight public-native CUDA controls passed |
| `cargo test -p holonics-workbench --test native_checkpoint_process -- --ignored --test-threads=1` | Both actual process controls passed |
| `cargo test -p holonics-hna --lib` | 37 passed; eight native CUDA tests explicitly excluded in this ordinary invocation |
| `cargo test -p holonics-workbench --lib` | Ten passed |
| `cargo check -p holonics-hna`; `cargo check -p holonics-workbench` | Passed |
| `cargo build -p holonics-workbench --bin holonics` | Passed |

[historical; measured] An earlier overlapping native/process-test run returned an allocation
calibration obstruction before the first native test mounted: the sampled free-memory extents
did not close. The other 26 tests in that invocation passed. No tolerance, kernel or admission
law was weakened. After confirming no live compute processes, the isolated 28-test invocation
passed; this does not establish that the apparatus's global-memory probe tolerates concurrent
external allocations. CUDA tests should be isolated when relying on that probe.

[definition] Exact owners are
`crates/holonic-engine/src/native_ecology/constitutive_fibre/circulation/rest.rs` and its tests;
`crates/holonics-hna/src/native/checkpoint.rs` and its tests; shared exterior helpers in
`crates/holonics-hna/src/checkpoint.rs`; and
`applications/holonics-workbench/{src/session_stream.rs,tests/native_checkpoint_process.rs}`.
The guide and public owner map connect them. The native current, formation and rechart kernels
and formal laws are unchanged; no new Lean theorem is inferred from serialization tests.

## Still required by NCF4

[open] The independent phase-current application's world/control state, exact intervention
cursor and already-enacted effect/pending reception must now compose with this persistent native
owner. The existing `wave-control` report remains nonpersistent; it is not silently promoted to
an application checkpoint. Cold/warm work, retained/support growth, residency, transfer and
latency still need their integrated consumer-apparatus receivers. No condensation, measured energy,
twenty-watt operation, general language capability or frontier parity is claimed. The corrected
goal remains unfinished and inherited-model/export work stays downstream.
