# HNP3: partial delivery survives without repeating development

**Date:** 2026-09-05 local. **Position:** HNP3 complete at the declared native-session and
process-delivery scope. HNP4 is next; no application-quality claim is made here.

## Owners and contract

[established-bounded; implemented-exact] `crates/holonics-hna/src/stream.rs` delivers versioned
JSONL requests through one `HnaSession`. It retains partial input, distinguishes an incomplete
fragment from a completed malformed record, and drains and flushes each result before reading
another request. A partial output is an already-produced result, never an instruction to repeat
its native operation. `inspect`, `checkpoint` and `close` are exterior process commands; they
do not define a native learning or completion law.

[established-bounded; implemented-exact] `checkpoint.rs` preserves native-only version 1 and
adds an explicitly distinct version 2 containing native and transport state. Pending input/output
are separate binary blobs under the same integrity footer, not enormous JSON byte arrays or a
new checksum registry. Native-only readers refuse the richer artifact instead of discarding its
transport. `session.rs::with_stream_session` restores both owners at their declared boundaries.

[established-bounded; implemented-exact] The application owner is
`applications/holonics-workbench/src/session_stream.rs`, exposed as `holonics hna session`.
Responses are flushed on stdout, not accumulated by the older batch response collector. A
required new final-checkpoint path is attempted on EOF, close and input/output failure. The
stderr process receipt separates disposition, error and saved anatomy. A failed final save names
the actual unsaved generation; there is no fictional rollback. Resume retains the saved aperture
and refuses conflicting explicit overrides. The operator recipe is in `docs/ATHENA.md`.

[definition] A writer's accepted-byte cursor is not a peer acknowledgment. Retrying that writer
continues its pending frame; a new connection replays the full pending event with the same
sequence. The peer may deduplicate it. No end-to-end exactly-once delivery across arbitrary crashes
is asserted. A checkpoint command itself saves its pending publication reply; its message asserts
publication, not peer delivery or post-publication durability. The existing publication apparatus
still distinguishes a durability-uncertain published file from failure before publication.

## Actual native controls

[established-bounded; measured] All controls used the same actual cultivated checkpoint and
explicit native SKE base as the [persistence return](2026-09-05_HNP3_THE_CULTIVATED_SESSION_RESTORES_EVERY_HELD_FIELD_AND_CONTINUES_AFTER_PROCESS_EXIT.md).
They used the admitted first occurrence with empty history, not a synthetic replacement learner.
The starting generation/factor extent was 3,825 / 5,334; one ordinary development reached
5,100 / 7,112. The complete `NativeFullSessionRest`, including all integer factors, carriers,
chronology, local returns and numerical origins, was compared to the prior uninterrupted reference.

| Control | Actual delivery return | Full native-state comparison |
|---|---|---|
| Inspect, advance, close through CLI | Events 1--3; final artifact 461,502,541 bytes | Same entire successor as `expected-after-01.hna` |
| EOF after 130 input bytes | Exit 1, incomplete frame saved; sequence 0; artifact 363,259,430 bytes | Same entire initial native state as `checkpoint-01.hna` |
| New process receives only the remaining input bytes | One advanced event, sequence 1; artifact 461,502,542 bytes | Same entire learned successor as the reference |
| Output pipe closes after its reader takes seven bytes | Exit 1; native advance completed once; 118,295,978 pending response bytes, 66,560 writer-accepted bytes; artifact 579,798,523 bytes | Same entire learned successor as the reference |
| New process, empty input, replay interrupted response | Event 1 replayed; 3,670,016 interval entries; no new native advance; artifact 461,502,542 bytes | Same entire learned successor; input/output buffers now empty |

[definition] The table is one bounded native experiment on the standing RTX 4080 SUPER apparatus.
The pipe's seven consumed bytes and 66,560 accepted bytes deliberately differ: acceptance by a
writer is not consumption by its reader. `input-exhausted` and `connection-closed` are transport
dispositions; the actual native status is still `awaiting-occurrence`.

[established-bounded; measured] Local artifacts are under `.local/artifacts/hnp3/`:
`stream-{01.jsonl,after-01.hna,events-01.jsonl,process-01.json}`;
`stream-partial-{01.hna,process-01.json,after-01.hna,after-events-01.jsonl,after-process-01.json}`;
`stream-full-output-01.jsonl`;
`stream-output-interrupted-{01.hna,process-01.json}`;
`stream-output-recovered-{01.hna,events-01.jsonl,process-01.json}`.
The large models/responses are ignored local products, not committed source. Replay requires
their pinned separate `target/ske4/rest.bin`; these are not self-contained exports.

```sh
target/debug/holonics hna session .local/artifacts/hnp3/checkpoint-01.hna --resume \
  --input .local/artifacts/hnp3/stream-01.jsonl \
  --checkpoint .local/artifacts/hnp3/stream-after-01.hna

target/debug/examples/checkpoint_hnp3 compare-stream \
  .local/artifacts/hnp3/stream-after-01.hna .local/artifacts/hnp3/expected-after-01.hna

target/debug/holonics hna session .local/artifacts/hnp3/stream-output-interrupted-01.hna \
  --resume --input /dev/null --checkpoint .local/artifacts/hnp3/stream-output-recovered-01.hna

target/debug/examples/checkpoint_hnp3 compare-stream \
  .local/artifacts/hnp3/stream-output-recovered-01.hna .local/artifacts/hnp3/expected-after-01.hna
```

[definition] Those publication paths must be new when reproducing; the existing artifacts are
never overwritten. Redirect the full-response command's stdout to a file, not an interactive
terminal. Native-only checkpoint version 1 remains the comparison reference.

## Relevant checks and remaining boundary

[established-bounded; measured] All 30 HNA library tests and nine workbench library tests passed.
Five stream controls cover fragmented reads, partial writes/backpressure, flush failure and
new-connection replay, pending checkpoint acknowledgment/close, and incomplete/malformed frame
ownership. The existing integrity, base pin, publication race/failure/panic and uncertainty tests
also passed. HNA/workbench libraries, binaries and examples type-checked; `git diff --check` passed.
No Lean statement changed; the existing native interruption and full-state rest controls stand.

[open] HNP4 owes actual text/document and genuinely different stateful/sensory applications,
lawful extension beyond the current finite inherited family, complete multi-cycle products,
ordinary later correction and founded output completion. Stream events and successful checkpoint
readback are not substitutes. HNP5--HNP7 still owe useful-task evaluation, executable standard
lowering and actual SSM/diffusion-family returns.
