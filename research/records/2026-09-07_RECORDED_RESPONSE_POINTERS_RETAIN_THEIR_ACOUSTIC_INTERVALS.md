# Recorded response pointers retain their acoustic intervals

[definition] September 7, 2026, after Apple `ba1068dd`. The preceding goal turn made concrete
progress by publishing shared condition inference and resident acoustic ingress. This return
attaches actual recording intervals and their source/response lineage. AS4–AS5 remain active.

## Current owners

[established-bounded; implemented-exact] `AcousticFieldChart::from_acoustic_range` accepts an
addressed half-open sample span. It retains the parent recording locator, byte count and digest,
full recording extent, selected PCM, exact clock offset and source sample coordinates. The whole
recording constructor uses this same path. Cell support remains in parent sample coordinates;
padding is explicitly outside the source span. The caller's aperture still does not define a
native acoustic holon.

[established-bounded; implemented-exact] `holonics_hna::native::recorded` exposes the existing
speech application's new cold annotation reader, owned by `native/speech/recorded.rs`. Each
record retains its complete JSON value, original pointer roles and endpoint metadata. Resolution
requires explicit source/target pointers to the actual relative annotation paths and dialogue-act
IDs. Different directories, malformed or repeated pointers, missing endpoints, invalid clocks
and original refusals do not silently select a source. Structured clock-refusal objects survive.
No speaker, transcript, type label or temporal adjacency authors a native condition.

[established-bounded; implemented-exact] `RecordedInterval::covering_frames` uses exact rational
decimal times, floors the beginning and ceils the end. It retains the original annotation support
beside that PCM cover, including sub-sample overhang. `RecordedResponseSections::bind` in
`recorded/sections.rs` joins a resolved annotation to the explicitly declared recording occurrence
and constructs both addressed acoustic charts. Both faces use the same mono receiver; speaker
metadata does not create microphone channels. Their sample cells can enter the shared resident
rational-current port. The binding neither mutates an ecology nor resolves an unknown condition.

## Actual corpus return

[established-bounded; measured] The public `recorded_acoustic_sections` example read all four
local ES2002 WAVs through `ExactAcousticOccurrence`, checked their actual bytes/frame counts/rates
against the acquisition receipt, and processed every response-link record. All 899 records remain:
844 resolved source/target pairs and 55 explicit refusals, comprising 54 incomplete-pointer records
and one invalid source clock. Resolved counts by meeting are 97, 185, 197 and 365. The
[receipt](2026-09-07_recorded_acoustic_sections/return.json) retains every emitted interval and
signed gap/overlap in original record order. Total preparation time was 54.480446458 s; this is a
cold source/codec run, not native learning or streaming-audio throughput.

[established-bounded; computational-witness] An independent Python `Fraction` comparison checked
every emitted endpoint ID, original decimal bound, floor/ceil PCM range, signed gap/overlap and
refusal against the source index. All 899 records agreed. The
[comparison receipt](2026-09-07_recorded_acoustic_sections/source-comparison.json) retains that scope.

[established-bounded; measured] The first actual pair,
`ES2002a.adjacency-pairs.dharshi.1`, retains source frames `[1190720,1236640)` and target frames
`[1239040,1293920)`, with the actual `3/20`-second gap. The complete 45,920-source-sample and
54,880-target-sample intervals reconstruct exactly and enter 1,435 and 1,715 resident cells at
the declared extent 32. Their complete mount uses 3,276,000 bytes of ingress and live resident
carriers, with zero numerical readouts and zero native deeds; two subsequent cold boundary
receivers inspect the first source and last target sections. These counts establish source
attachment only, not learning, recognition, synthesis or native acoustic grain.

## Verification and next construction

[established-bounded; measured] Fourteen focused tests passed: seven annotation/interval-binding
controls and seven acoustic-field controls, including the existing Metal current/source-return
checks. New controls cover exact nonaligned edges, nonzero recording origins, parent coordinates,
empty/reversed/outside bounds, false pointer suffixes, malformed roles, structured refusal
retention, source binding and PCM overhang. The public example built and ran successfully.

```sh
cargo test -p holonics-hna --lib native::speech::recorded::tests:: -- --test-threads=1
cargo test -p holonics-hna --lib native::acoustic_field::tests:: -- --include-ignored --test-threads=1
cargo build -p holonics-hna --example recorded_acoustic_sections --locked
target/debug/examples/recorded_acoustic_sections .local/datasets/ami-conversation-es2002 32 research/records/2026-09-07_recorded_acoustic_sections/return.json
```

[established-bounded; process-audit] `git diff --check` passed. Existing unused-code and dependency
warnings remain unrelated. Only intended files were formatted. No Lean build, corpus mutation,
microphone acquisition, native cultivation or model-quality measurement occurred.

[open] The source/response interval attachment is now present. The next substantive gap is
the admitted temporal/material action joining these complete source and receiving sections to
native condition standing, its full Preimage Fibre and subsequent emission. Equal cell ordinals
in unequal utterances do not supply that passage. Do not replace it with a sample-step schedule,
speaker/type selector, one unrestricted linear chart over the corpus, or a fixed sonification.
Compose the existing generator and temporal transport owners at their actual scopes, retain
unsupported domain and separating histories, and establish useful sound conduct before claiming
recorded English/conversational capability. Whole-family forward conduct remains shared work;
its availability must be checked in current source rather than presumed from this data attachment.
