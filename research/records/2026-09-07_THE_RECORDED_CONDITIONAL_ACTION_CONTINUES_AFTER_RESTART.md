# The recorded conditional action continues after restart

[definition] September 7, 2026; `codex/apple-silicon`, following `4a9209ce`.
This return supplies the missing conditional-state persistence boundary in the
[Apple construction](../../docs/plans/HOLONICS_ON_APPLE_SILICON.md), using the existing local
relation/current and complete field owners. AS4–AS5 remain active.

## Exact state and ownership

[established-bounded; implemented-exact] `ResidentConstitutiveFibreRest` in
`crates/holonic-engine/src/native_ecology/constitutive_fibre/rest.rs` retains the declared linear
or bilinear source chart, source/receiver dimensions, completed occurrence count and complete
positive-pivot echelon basis. In particular, serialization retains the vertical fibre and
outside-domain behavior. Validation checks the native carrier, source-law dimensions and rank
against the occurrence count. Remount consumes this cold chart and mounts its section directly;
it does not fit coefficients or replay observations.

[established-bounded; implemented-exact] `ResidentConditionCurrentRest` in
`resident/condition_contact/rest.rs` retains the bound bilinear chart, explicit metric, contact
count and complete five-row contact section: predecessor, successor, incoming normal, returned
normal and difference, with their common positive denominator and disposition. Cold exact
validation checks the contact equations, unit-admittance quadratic balance, untouched initial
current and outside-family preservation. Remount creates one continuing move owner. An earlier
immutable contact receipt can survive dropping that owner; neither owner is cloned.

[established-bounded; implemented-exact] `holonics-hna::native::NativeSavedConditionalField` and
`save_conditional_checkpoint`, in `native/conditional_checkpoint.rs`, compose these two rests
with the existing `NativeFieldRest`, delivery state and application bytes. The field retains its
own complete history, producing frames, actual resident inputs, current and explicitly supplied
emission/anchor capabilities. The envelope checks matching conditional charts and the relation's
receiver width against twice the field node count. Condition and receiver dimensions may differ.
It uses existing checksummed, no-overwrite publication and bounded native rest streams.

[definition] The local relation/current have no source-capability archive to invent. Their rests
do not replace `NativeFieldRest` or authenticate an externally authored developmental history.
This envelope preserves the supplied three owners and delivery/application chart; standalone
in-flight conditional prediction, joint-family and contact receipts are not implicitly saved.
The example checkpoints after its conditional contacts and field operations have completed.
An application with pending work must retain that work's actual carriers before claiming a
complete application restart. No new learning engine, kernel or physical acoustic law was added.

## Recorded process continuation

[established-bounded; measured] The existing `recorded_temporal_action` example now optionally
publishes a conditional checkpoint. Its `--continue` mode consumes that checkpoint in another
process, mounts a later recording at the same declared sample clock, conducts the retained
condition through the full temporal action, enters a small declared comparison current into the
continuing field, publishes timed PCM/exact output and saves the successor. The latter process
receives no calibration controls or observed target and does not select a new condition.

[definition] The complete waveform action uses every source coefficient. The separate local
relation/field comparison uses the first complete four-coefficient aperture; this is an explicit
receiver comparison, not native acoustic grain or a PCM sample recurrence. Its target remains
five complex coordinates, its condition two, and its field five nodes. The action is still the
controlled digital two-tap family from the preceding record. Reuse across recordings is not
additional acoustic cultivation, recognition or an utterance-response law.

[established-bounded; measured] Three separate processes returned on M1 Pro using LibriSpeech
`2277-149897-0007`, `0008` and `0009`, in that declared order. The first process retained the
earlier study's learned action and changed condition; the next two consumed only their preceding
checkpoint and new WAV. Checkpoints contain 49,126, 53,199 and 57,269 bytes. Relation occurrence
counts are 38, 39 and 40; contact count stays two; the field continues through two, three and
four occurrences. These ordinals describe chronology, not semantic identities.

[established-bounded; measured] Debug apparatus costs for the two subsequent processes:

| Receiver/work | Second recording | Third recording |
|---|---:|---:|
| Source frames at 16 kHz | 46,080 | 59,600 |
| Source duration | 2.880 s | 3.725 s |
| Native rest remount, excluding file decoding | 0.000405 s | 0.000615 s |
| Local relation plus field, wall/GPU | 0.2062 / 0.2036 s | 0.2046 / 0.2017 s |
| Complete temporal action, wall/GPU | 0.1080 / 0.1066 s | 0.1554 / 0.1537 s |
| Cold exact-section/PCM publication | 2.3128 s | 3.1103 s |
| Cold checkpoint publication | 0.0120 s | 0.0131 s |
| Entire process | 2.7318 s | 3.5899 s |
| Native peak residency | 6,714,084 bytes | 8,668,580 bytes |

[established-bounded; measured] Each full temporal action uses one deed, one command buffer,
six allocations, zero ingress and zero numerical readout, with 64 receipt bytes. Each remount
uses zero deeds and numerical readouts; its counted ingress is 68,384/76,000 bytes. The terminal
receiver reads 1,474,608/1,907,248 bytes and the checkpoint reads 75,760/83,376 bytes. This is
whole-file debug batch work, not a streaming latency or power measurement. Native residency
excludes CPU rational objects, process RSS and disk; cold reconstruction still dominates time.

## Verification and remaining construction

[established-bounded; measured] Seventeen focused Rust controls pass: four relation-rest,
eleven condition-contact/rest and two public checkpoint controls. They cover exact roundtrip,
plural/outside continuation, later development/contact, immutable prior receipts, malformed
charts/equations/denominators/dispositions, unequal condition/receiver dimensions, resident
generated-current ingress, restored emission/anchor capabilities, foreign-handle refusal,
truncation/corruption/trailing bytes and no-overwrite publication. The initial new relation test
incorrectly expected a pre-operation occurrence count; its expectation was corrected to the
existing completed-operation convention. The final example builds. No native kernel, CUDA,
Lean or workspace-wide changes required a broader build.

[established-bounded; measured] The original exact PCM/fibre/field comparison passes for the
first process. `compare_temporal_continuation.py` independently decodes both later checkpoints,
verifies the entire retained field history carrier prefix, source/occurrence chronology, unchanged
conditional basis/current and actual added Hermitian contact moment. It verifies the small
prediction against the saved condition and actual per-node field input, then checks every
whole-waveform coordinate, clock, causal tail, PCM projection and quantization residual. Five
negative controls reject changed clock, undeclared native readout, altered historical carrier,
altered exact tail and altered PCM; changed files carry updated checksums where applicable.
Two application controls refuse a changed sample clock and an existing output before publication.

[established-bounded; source-inspected] Initial observer drafts wrongly required an unchanged
field moment and treated saved incoming phase triples as one common-denominator vector. The
field's existing `junction.rs` and `resident_input.rs` define the actual evolving moment and
per-node normalized input chart. The corrected observer checks those laws; the final complete
comparisons above pass. No native operation was changed to satisfy either mistaken expectation.

[definition] Raw reports and comparisons are under
`research/records/2026-09-07_native_temporal_restart/`; checkpoint, WAV and exact-section
artifacts remain outside Git under `.local/experiments/native-temporal-restart/`. Negative
observer artifacts are retained in its `observer-controls/` directory. The read-only observer
uses original PCM and serialized state; it never supplies native learning or emitted current.

[open] Actual acoustic constitutive/material binding remains the next construction. A resolved
AMI response pointer supplies source-qualified interaction evidence, but does not establish that
an arbitrary second utterance is produced by the calibrated temporal family. Neither matching
cell widths nor passing those currents to condition-preimage inference repairs that missing law.
Native temporal organization, useful sound perception/production, recorded English/conversational
conduct and the full streaming application are still unfinished. Desktop private cultivation
remains independent. This persistence return is a necessary reusable boundary, not AS4–AS5 completion.
