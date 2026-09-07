# Corrected AS4–AS5: corpus continuity and resident packets

[definition] Brandon's September 6 request, “Can you proceed then into the corrected AS4-AS5?”,
continues the [correction](2026-09-06_AUDIO_APPLICATION_PROBES_DO_NOT_COMPLETE_CONVERSATIONAL_AUDIO.md).
Recorded sound and English conversations are required development material; a microphone is not
a prerequisite. This return starts from `aef12e47` on `codex/apple-silicon`.

[open] AS4 and AS5 remain incomplete. This return implements source acquisition, continuation
and device operations; it does not produce a corpus-cultivated acoustic model, useful recognition,
intelligible synthesis or conversational responses. A continuing signal state is not evidence of
learned acoustic/language correspondence. The unlinked packet operation does not deposit a
constitutive relation row. The older fixed sonification and WAV-then-byte probe keep their
previously corrected scopes.

## Source and communication material

[established-bounded; measured] The official AMI distribution supplied four complete recordings,
ES2002a–d, with 275,208,026 original WAV bytes and 8,600.2453125 seconds of mono PCM16 at 16 kHz.
The original manual annotation ZIP, selected XML and CC BY 4.0 license remain local. The
acquisition recipe is `research/experiments/apple_silicon/prepare_ami_conversation_subset.py`;
the local corpus is `.local/datasets/ami-conversation-es2002`. The source metadata designates
these meetings as training material. This is one scenario group with four speaker agents,
not an evaluation result or a claim of broad speaker coverage. Sources: the
[AMI corpus](https://groups.inf.ed.ac.uk/ami/corpus/) and
[official download distribution](https://groups.inf.ed.ac.uk/ami/download/).

[established-bounded; measured] The source index retains 2,109 timed segments and 3,874 dialogue
acts. All 899 original adjacency-pair records remain: 844 links resolve their direct source and
target pointers; 54 have incomplete source pointers and one additional link has a reversed source
word interval. Four reversed word intervals remain explicit source clock refusals. No timestamps
were repaired or links inferred from neighboring turns. Word/segment attributes, speaker/channel
and role metadata, original pointer roles, XML paths, exact decimal clocks and original bytes
remain source-qualified. Annotation types are cold testimony, not native routes or currents.
The [source receipt](2026-09-06_as4_as5_continuation/ami_source_receipt.json) records provenance.

[established-bounded; source-inspected] Primary review corrected lexical ordering of decimal
timestamps, silent reversed word-span selection, cross-file word references, duplicate role
selection and incomplete download/WAV-payload acceptance in the first acquisition drafts.
Earlier indices remain local alongside their original XML. The final recipe checks source
intervals, preserves explicit refusals and compares actual WAV payload length to frame counts.

## Continuing application and device operation

[established-bounded; implemented-exact] `AcousticApplication::append_recording` and
`append_acoustic` attach another complete source recording to the same `NativeSession`. The
application retains earlier WAV bytes, PCM charts, returns and absolute native chronology.
Append refuses an incomplete current recording or malformed source before mutation. Its first
sample is new exterior ingress. The optional digital return law operates only within that
recording; adjacency never fabricates a receiving edge. Version-one saved applications remain
readable, and appended applications use the extended version-two chart.

[established-bounded; implemented-exact] `NativeSession::receive_unlinked_batch` and
`NativeConstitutiveEcology::advance_unlinked_batch` submit known exterior inputs through the
existing circulation kernel in a serial resident passage. Each kernel depends on its predecessor's
success. Arithmetic refusal commits only the exact successful prefix and reports the refused
suffix with complete obstruction lineage. Every successful output remains a source section.
Uncertain launch/readback retains staged sections in the unusable owner and prevents replay or
checkpoint. No input is downsampled, no CPU semantic operation substitutes for GPU conduct,
and no temporal parallel-independence claim is made. The relation is unchanged for unlinked
ingress, so reading its complete receiver basis after the packet preserves each receiver fibre.

[established-bounded; implemented-exact] The acoustic run path uses packets of at most 256 samples
for unlinked input. Explicit digital feedback keeps its dependent scalar path. `holonics-acoustic
append SOURCE --wav WAV --occurrence ID --checkpoint OUTPUT` exposes continuation with an explicit
new output path. CLI frame/hop defaults are now 4096, with complete PCM retained and the folded
section unused. This removes redundant per-sample cold frame descriptions without deleting any
source samples or treating delivery boundaries as semantic boundaries.

[established-bounded; implemented-exact, measured] `ResidentComplexIncidence::mount_metal` and
`accelerators/metal/complex_incidence.metal` implement the existing bounded signed-integer complex
incidence contraction on Metal. Both quadratures and rational common denominators are preserved;
the inherited row-mass bound refuses possible signed accumulation overflow before launch. This
retains that bounded apparatus domain, including its conservative refusals. The immutable incidence
stays resident and independent contexts rebind correctly. Errors retain the actual Metal boundary
message. The cultivated morphology mount selects this operation on macOS.

[open] The broader cultivated ecology is not thereby runnable end to end on Apple. Its predecessor
conduct still mounts resident words/thread currents through CUDA; situated cultivation and
receiver-history quotient construction also have CUDA dependencies. The existing
`ReceiverHistoryCongruence::found_on_device` consumes a laboratory `ContinuationAperture` with
particular surface-counterexample and overlapping proposal-role requirements. AMI's annotated
audio/response graph cannot be admitted by relabeling its speakers as user/assistant or inventing
those witnesses. Native source/material interaction, contextual formation and productive acoustic
and English receivers remain the required composition, alongside the desktop's AC1 work.

## Returned checks and costs

[established-bounded; measured] On this M1 Pro, 24 ignored public native tests passed, including
the new scalar/batch complete-return and byte-identical checkpoint comparison after formation and
rechart, old-source return after the batch, exact arithmetic refusal prefix/suffix behavior,
cross-recording restart and refusal before invalid append. Six acoustic tests include both
unlinked packets and coupled continuation. The existing 28 engine phase tests also passed with
Metal API validation enabled. Two new Metal complex-incidence tests passed against exact rational
contraction, including negative coefficients, multiple fronts, interleaved contexts and reuse
after overflow refusal. No Linux GPU execution or Lean build is claimed.

[established-bounded; measured] The public `native_audio_packets` example processed two complete
recordings in one owner, using the existing two-junction seed, unlinked PCM ingress and packets
of 256. Native occurrence count continued from 0 through 220,500 to 325,940. Source decoding and
final checkpoint publication are outside these timed intervals. The debug run overlapped CPU
compilation, so these are observed execution costs, not isolated performance bounds. Full returns
are in the [packet receipt](2026-09-06_as4_as5_continuation/recorded_packets.jsonl).

| Complete input | Source duration | Processing | Median packet | p95 packet | Synchronizations | Resident allocation calls |
|---|---:|---:|---:|---:|---:|---:|
| ESC-50 `1-100032-A-0.wav` | 5 s | 63.251 s | 69.767 ms | 108.068 ms | 862 | 883,724 |
| LibriSpeech `2277-149896-0000.wav` | 6.59 s | 46.584 s | 115.105 ms | 122.681 ms | 412 | 422,584 |

[open] These runs are 12.65 and 7.07 times slower than their source clocks. Reducing synchronization
count has not achieved real time: per-sample allocations, command encoding, retained source
sections and cold history remain substantial. A resident arena with exclusive subregions and
ordered device iteration is a concrete next execution change; it must preserve every source,
failure prefix and complete successor. It cannot be replaced by dropping samples or history.

[established-bounded; process-audit] Raw build/test/acquisition/measurement logs remain under
`.local/setup/apple-silicon/as4-*`. During integration, an agent's accidental workspace-wide
formatting was restored outside the changed owners; the patch was retained locally. No corpus,
user file or historical evidence was removed. The unrelated `.DS_Store` files remain unstaged.
