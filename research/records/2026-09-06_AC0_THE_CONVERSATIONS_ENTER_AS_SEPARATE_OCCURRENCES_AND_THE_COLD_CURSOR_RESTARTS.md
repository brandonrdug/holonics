# AC0: conversations enter as separate occurrences and the cold cursor restarts

**Authority:** Brandon's September 6 instruction to design, deposit and immediately construct the
[Athena-alpha blueprint](../../docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md).
**Plan commit:** `b16e6bc0`. **Disposition:** AC0 complete at its cold data/application scope;
the whole Athena-alpha construction goal remains active.

## Returned source boundary

[established-bounded; implemented-exact] `applications/conversation-data/exposure.py` extends the
existing preparation owner. The CLI command is `export-exposure`. It reads the refined package
without modifying or recapturing it, holds one coherent read transaction and atomically publishes
a new `0600` JSONL file. Narrow family metadata is sorted before message material is read one
family at a time. Source comparison references are indexed once in memory; neither incoming-link
scans nor all-body buffering are required.

[definition] `holonics.conversation-exposure.v1` begins with private source/capture metadata and
then emits separate occurrence families. Every visible human and agent event participates, with
all captured presentations sharing its provider-declared ID retained; missing IDs retain separate
capture addresses. An unpaired message is still ordinary material. Grouping captured views does
not infer native identity from either text or names. Different views can remain incompatible.

[definition] The earlier request never contains the future agent response. Actual agent responses
carry source-qualified request references; later human occurrences carry their actual earlier
references. Tool, reasoning, client and branch material keep their distinct part/reference roles.
Only actual outgoing edges are emitted. Target metadata contains no target material. No loss,
reward, gold-answer designation, curation-derived input or automatic response-interval prompt is
introduced. This source chart does not compute a semantic comparison or select a native route.

[definition] The temporal study cut is `2026-09-04T00:00:00Z`, chosen before model outputs. Known
coherent earlier families enter development; later families enter evaluation. Unknown or conflicting
clock/role/material presentations and contradictory request/response order are retained as deferred.
Equivalent normalized times remain equivalent exterior clock presentations. A branch label alone
is not a reason to exclude material. These partitions define the study, not native meaning or rank.

[definition] Reference availability is a cold chronological reading, not a proof of contextual
contact. The parent/comparison/tool kinds and evidence remain attached. A consuming native
application still owes the actual material attachment, source handles and applicable chart;
missing route material must stay open. The exposure does not reconstruct hidden reasoning or the
provider's complete effective prompt from log order.

## Actual private artifact and verification

[established-bounded; measured] The returned artifact is
`.local/datasets/athena-alpha-exposure-source-context-2026-09-06.jsonl`:

| Receiver | Return |
|---|---:|
| File bytes | 184,572,827 |
| Declared occurrence families | 36,920 |
| Captured views | 49,928 |
| Development families | 34,046 |
| Evaluation families | 1,121 |
| Deferred families | 1,753 |
| Original visible human/agent source events retained | 49,142 |
| Additional captured branch-input views | 786 |
| Development visible octets under the common-view projection | 47,082,418 |

[established-bounded; source-audit] A complete read-only comparison against the refined package
matched every retained event's source/record/byte range, provider, role, timestamp, phase and other
metadata; every visible part and nonvisible part reference; and every actual source link plus
comparison-request reference. All 39,731 reference targets retained their exact source coordinates.
Every visible source event was present, each declared family occurred once, and frame sequence
was contiguous. The final provider-metadata addition matched all 49,928 original dictionaries,
including API generation/request IDs, parent-session and agent-path testimony, while every
previously verified field remained exactly unchanged. The public Rust reader independently
consumed the entire artifact and returned the same family/view/partition counts. No model was initialized or executed.

[established-bounded; measured] The final source-context export took 10.91 seconds with a Linux
child-process maximum RSS of 73,988 KiB, measured by Python's monotonic clock and `resource.getrusage`. The source-fidelity
comparison took 11.05 seconds; the final context-dictionary and unchanged-field comparison
took 1.43 seconds. These are cold data/application observations, not native training
throughput, GPU residence or energy. Receipts are in `.local/artifacts/athena-alpha/ac0/` as
`source-context-export{,-process}.json`, `source-fidelity.json`,
`source-context-fidelity.json` and `source-context-full-inspection.json`.

[historical; measured] The earlier local export
`.local/datasets/athena-alpha-exposure-2026-09-06.jsonl` selected comparison/later-observation
endpoints only (24,768 families). It remains retained but is superseded for this campaign by the
all-visible artifact above: absence of a comparison is not absence of ordinary material. The
intermediate `athena-alpha-exposure-all-visible-2026-09-06.jsonl` retained all visible material
but omitted provider API-generation/parent-origin metadata; it is also preserved and superseded
by the final source-context artifact. A first measurement command could not run because `/usr/bin/time` was absent; its failed command output
remains separate. The successful measurement used Python's standard library. No raw source or
failed evidence was deleted to conceal these changes.

## Cold Rust interface and actual process continuation

[established-bounded; implemented-exact] `holonics-hna::alpha::exposure` supplies a typed manifest,
occurrence/view/part/reference wire, partition and conflict types, and `ExposureReader`. It validates
source extents, the complete actual capture coordinate, family membership, visible-role separation,
normalized UTC development cut and link availability. Targets can contain source metadata only.
`development_parts` rejects evaluation/deferred or incompatible material rather than selecting an
arbitrary captured presentation. The original full view population remains alongside the projection.

[definition] The normalized UTC field is the partition chart; the raw timestamp remains provider
testimony. These structural checks do not authenticate a maliciously fabricated history or
independently reconstruct the original provider's clock/parser. The actual source comparison above
establishes the generated artifact's correspondence to the retained package.

[established-bounded; implemented-exact] The reader uses the existing `HnaFileDependency` wire pin.
`peek` retains one pending frame; `acknowledge` advances the cold cursor only for that frame.
An error leaves the prior cursor intact and stops that reader instead of skipping malformed
material. A resumed reader verifies the immutable exposure file and its line/sequence boundary.
The cursor is exterior delivery state, not proof of native development or a model checkpoint.

[established-bounded; process-audit] The `alpha_exposure` example read 1,024 actual frames, saved
its private cursor through the existing no-overwrite publication owner, exited, then a new process
read the remaining 35,896 frames. Its complete final cursor equalled the uninterrupted cursor;
frame/view/role/partition/visible-byte counts composed exactly. The example reports
`native_model_executed: false` and prints no message content. The complete process receipt is
`.local/artifacts/athena-alpha/ac0/source-context-continuation-receipt.json`. Native-plus-exposure atomic
persistence remains AC3; this cold test does not discharge it.

## Source repairs and focused checks

[counterexample; source-inspected] An initial draft merely repackaged a request together with its
response and repeated requests across response families. It did not meet the exposure boundary.
A second draft reversed incoming parent edges and omitted their direction, which could make a
descendant look like its ancestor's parent. These drafts were corrected before the accepted return.
The final source emits one occurrence family at a time and preserves outgoing relation direction.

[established-bounded; implemented-exact] Additional corrections preserve a real joint
source/record/event coordinate rather than three unrelated minima, compare normalized times
rather than timestamp spelling, compare exact visible material rather than text hashes, retain
unpaired material and provider generation/parent-origin metadata, and check target source/provider/availability in the Rust reader. Python and
Rust tests include the cases that exposed these defects.

[established-bounded; process-audit] Checks returned:

- `python3 -m unittest discover -s applications/conversation-data -p 'test_*.py'`: 32 passed.
- `cargo test -p holonics-hna --lib alpha::exposure`: nine passed, with the final native-source and
  future-reference tamper controls included.
- `cargo build -p holonics-hna --example alpha_exposure`: passed; the actual all-visible artifact
  then passed full inspection and process-separated cold continuation.
- Owned diff/source review passed. Two pre-existing engine dead-code warnings remain. No native
  kernel or Lean source/import changed; no native quality, training or formal-build result is claimed.

## Next native construction

[open] AC1 must turn actual available material and source incidence into native current, contextual
formation and the complete successor. A reversible exterior bit/octet chart may excite admitted
ports; it cannot supply a byte-difference semantic vector. The dimensional-wave law and NCF
scattering/formation provide existing constitutive owners. Their full branch currents, historical
source frames, actual handles and any higher contacts must share a resident successor. Running
the wave law on the host and feeding a collapsed current into a second learner would not satisfy
that requirement. Learned text-codec production, broad cultivation, usefulness and the actual
Athena-alpha artifact remain AC2–AC5. The full goal is not complete.
