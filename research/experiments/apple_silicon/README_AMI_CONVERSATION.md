# AMI conversation subset

[established-bounded; implemented-exact] `prepare_ami_conversation_subset.py` acquires the original AMI Meeting Corpus headset-mix WAV
files for `ES2002a` through `ES2002d` from the official Edinburgh AMI distribution and extracts
the corresponding manual NXT annotations from `ami_public_manual_1.6.2`. It keeps the source ZIP,
the selected XML files, the complete meeting WAV for each session, a JSONL index of the original
time-aligned segments and words, and a separate source graph of the corpus' explicit dialogue-act
adjacency-pair pointers.

The local corpus is at:

```text
.local/datasets/ami-conversation-es2002/
├── audio/                         # four complete 16 kHz mono Mix-Headset WAVs
├── annotations/                   # selected original NXT XML, dialogue acts, and LICENCE.txt
├── source/ami_public_manual_1.6.2.zip
├── turns.exact.jsonl              # 2,109 source-linked segments, exact source clock strings
├── response-links.exact.jsonl     # 899 original adjacency-pair records
├── turns.v1.float.jsonl           # preserved earlier convenience index
└── provenance.json
```

[established-bounded; measured] The four WAVs total 275,208,026 bytes and retain the original 16 kHz, mono, signed PCM16 files.
Their exact frame durations are 1272.64, 2279.7546875, 2423.68, and 2624.170625 seconds for
ES2002a-d respectively. The revised index has 2,109 segments across four meetings and four
speaker agents. It retains empty
transcript segments when the source segment contains a vocal-sound annotation, so the index does
not silently turn the source into text-only examples. Each row carries source session, speaker
agent/channel/global name/role, start/end seconds, source segment ID/file, and the original word
IDs and times. Clock fields remain the original decimal strings; segment and word references are
refused if unresolved, and every annotation bound is checked against its source WAV duration.
[established-bounded; measured] The response-link graph contains 3,874 dialogue-act records and 899 original
adjacency-pair records: 844 resolve direct source/target pointers with valid word intervals, while
55 remain explicit refusals (54 incomplete pointer records and one invalid source clock). The
graph never infers a link from temporal or turn adjacency. Resolved endpoints retain source
dialogue-act IDs/files, direct word-span hrefs, exact times, speaker metadata, all source
attributes, and the original annotation type pointers. These labels and links remain cold corpus
provenance; they do not supply native current or contact.

[established-bounded; source-inspected] The official [AMI site](https://groups.inf.ed.ac.uk/ami/corpus/) describes the corpus as about 100 hours of English meeting recordings with
orthographic transcription and other annotations. Its download page states that signals and
transcription are released under CC BY 4.0; the copied `annotations/LICENCE.txt` is the governing
license text for this acquisition. The selected ES2002a-d scenario meetings have
`seen_type="training"` in the copied official `corpusResources/meetings.xml`; the provenance
receipt records that source partition metadata without asserting an external evaluation split.
This is corpus material, not evidence of a trained model or speech competence.

Reproduce or choose another admitted ES2002 a-d subset with the installed Apple Silicon Python:

```sh
.local/venvs/apple-silicon/bin/python \
  research/experiments/apple_silicon/prepare_ami_conversation_subset.py
```

[established-bounded; implemented-exact] The script publishes downloads atomically through `.partial` files and refuses an existing partial
download. It does not use repository code, gated-access workarounds, generated audio, synthetic
labels, pretrained models, or a native learner. Re-running with `--rebuild-existing` preserves the
earlier float index and provenance receipt before writing the exact-clock revision.

[established-bounded; measured] Primary validation retains four reversed source word intervals as explicit clock refusals. The 899 original adjacency-pair records yield 844 resolved links and 55 refused links (54 incomplete pointers and one affected by an invalid word clock). Endpoint extrema use exact decimal ordering. Complete WAV payload lengths were checked against their declared frame counts. Original XML and earlier convenience indices remain retained.
