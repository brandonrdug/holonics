# EROS AUDIO CTC PATH FIBER 01 — RESULTS

**Date:** 2026-07-23

**Grade:** COMPLETE WAV2VEC2 FRAME--ALPHABET FIELD / EXACT DYADIC CTC FORWARD RELATION / TWO
NONIDENTICAL PRONUNCIATIONS COHERED / PHASED EXPRESSION SUCCESSOR / HELD VOICE RECRUITED /
CONTEXT CROSS-FACES SELECTED / COMPLETE RESIDUALS RETAINED / EXACT REST-REMOUNT / HOST-MEASURED /
NO CAUSAL DIGEST / SOMA RECEIVING LAW UNCHANGED

## Fixed question

Can acoustically nonidentical pronunciations found and later recruit one expression through the
complete CTC label-path fiber supplied by an inherited speech model, without making a filename,
waveform hash, transcript, speaker, or exact recording identity causal?

The qualitative read was:

```text
recording
  -> complete frame x alphabet field
  -> exact 35-expression fiber order
  -> genuinely later expression return during cultivation
  -> phased expression successor
  -> held-pronunciation expression and context recruitment
```

This was not a transcription-accuracy benchmark. The inherited model was a lawful world
transducer. Soma received exact event geometry, direct expression/context interfaces, complete
occurrence interiors, and their later consequences.

## Fixed material and exact numerical law

The source was Google Speech Commands v0.02 and the locally complete
`facebook/wav2vec2-base-960h` snapshot. Recording selection was lexicographic and occurred before
model inference:

| Occurrence | Partition | Speaker | Frames | Raw field words | Complete-fiber result | Greedy testimony |
|---:|---|---|---:|---:|---|---|
| 1 | training `right` | `00b01445` | 44 | 1,408 | `right` | `RIT` |
| 2 | training `right` | `012187a4` | 49 | 1,568 | `right` | `RIGHT` |
| 3 | testing `right` | `03401e93` | 49 | 1,568 | `right` | `RIGHT` |
| 4 | testing `left` | `022cd682` | 49 | 1,568 | `left` | `LECD` |

All four WAVs are distinct mono signed PCM16 worldlines at 16 kHz. All four speakers are distinct.
No recording was selected by model score, waveform distance, or Eros result.

Wav2Vec2 supplied every output frame and all 32 vocabulary symbols. Each binary32 probability
codeword was decoded as an exact nonnegative dyadic. The Rust world independently recomputed all
140 CTC forward relations using only integer addition, multiplication, normalization, and
comparison:

```text
M_x(y) = sum of every CTC path through x whose blank/repetition collapse is y
```

No best alignment, top-k tensor cut, averaged score, decimal probability, epsilon, or tolerance
entered. The full exact order remained available. Its leading five expressions were:

| Occurrence | Exact leading fibers |
|---:|---|
| 1 | `right, eight, yes, on, one` |
| 2 | `right, eight, go, tree, nine` |
| 3 | `right, eight, go, two, nine` |
| 4 | `left, learn, cat, bed, up` |

The complete fiber succeeds where greedy transcript collapse does not: occurrences 1 and 4 have
observer strings `RIT` and `LECD`, yet the sum over all lawful label paths selects `right` and
`left`.

The source generator used PyTorch `2.10.0+cu128`, Transformers `5.8.1`, CUDA `12.8`, and the RTX
4080 SUPER. The 377,607,901-byte model weight file had SHA-256
`8aa76ab2243c81747a1f832954586bc566090c83a0ac167df6f31f0fa917d74a`.
Peak allocated GPU memory was 416,601,600 bytes. Source generation took 954,383 microseconds.

Hashes in this paragraph and the source report are provenance only.

## What crossed Soma

Each occurrence carried one ordered direct-data section containing:

- its extent and PCM bounds;
- every unpadded 320-sample block sum;
- every raw frame--alphabet codeword;
- every exact frame sum;
- all 35 exact fiber numerators, denominator exponents, and forward-state extents; and
- the complete 35-expression order.

The resulting exact occurrence interiors contained 4,197, 4,728, 4,835, and 4,865 direct words.
Their interfaces used only occurrence ordinal, data address, and exact word. SHA-256, relative
path, speaker, observer label, and transcript text never entered a causal interface.

Expression interfaces used direct Wav2Vec2 symbol IDs, symbol position, and causal phase. Context
interfaces used direct context atoms. Their intersection was the direct pair
`(context id, expression id)`. No string or digest was converted into a capability.

## Cultivation and the necessary phase successor

Each cultivation recording first entered alone and stood entirely OPEN. Its source label then
returned as a genuinely later event through only that occurrence's direct link.

The first return emitted expression phase one for `RIGHT` and the `TURN/right -> DIRECTION`
cross-face. The second return:

1. closed its own acoustic occurrence;
2. met phase one through the same ordered `RIGHT` symbol path;
3. integrated the two nonidentical acoustic interiors;
4. emitted expression phase two; and
5. added `ANSWER/right -> CORRECTNESS`.

Phase is native causal chronology, not an audio or phrase identity. Without this successor, the
second return correctly consumed the recurrent expression seam, leaving no outward aperture for a
third pronunciation. Keeping that spent seam active would have falsified lineage completion.
Phase two is the compressed higher construction becoming later terrain.

The cultivated result is one body:

| Property | Exact result |
|---|---:|
| cells | 35,869 |
| incidences | 44,811 |
| pins | 43,734 |
| complete paths | 8,969 |
| exposed pins | 8,945 |
| support sections | 9 |
| occurrence 1 words retained | 4,197 |
| occurrence 2 words retained | 4,728 |
| live lineages | 0 |

Its 14,791,600-byte rest image remounted exactly.

## Held pronunciation and situated context

The held third-speaker recording received neither source label nor decoded transcript. Its complete
field independently selected `right`.

All probes branched from the same exact rest:

| Held event | Standing result | Cultivation interiors carried | Selected face |
|---|---|---|---|
| phase-two `right` only | one joined body | both, complete | expression: 1 RIDE |
| `TURN/right` | one joined body | both, complete | turn cross-face: 1 RIDE |
| `ANSWER/right` | one joined body | both, complete | answer cross-face: 1 RIDE |
| `COPY/right` only | separate OPEN body | neither | copy cross-face: OPEN |
| phase-two `right` plus `COPY/right` | one joined body | both, complete | expression RIDEs; copy remains OPEN |
| `TURN/left` | separate OPEN body | neither | left cross-face: OPEN |
| `ANSWER/left` | separate OPEN body | neither | left cross-face: OPEN |
| `TURN/right` against empty Standing | one new OPEN body | neither | no inherited face |

This separates three things which a scalar result would conflate:

```text
expression recurrence
!= context-cross-face conduct
!= carriage of the integrated ecology
```

`COPY` does not block an independently afforded expression, but it cannot manufacture a contextual
consequence. A familiar context alone also cannot recruit the wrong expression: both `left` probes
remained separate despite receiving trained context atoms.

Speaker and timing differences did not disappear. The held `right` branch retained its own 4,835
word interior beside both cultivated interiors, with 13,799 OPEN boundaries and 11 RIDE
boundaries. The held `left` branches retained 4,865 own words, 4,868 OPEN boundaries, zero RIDEs,
and none of the cultivation ecology.

## Physical aperture and bounded execution

The first physical attempt overflowed the default scoped-worker stack before any report or commit.
The regional cell was not reduced. `ParallelHostLiveCurrentExecutor` now accepts an explicit
worker-stack aperture; the accepted run used:

```text
host workers:       8
worker stack:       33,554,432 bytes
available CPUs:     24
event wall limit:   30 seconds
whole-run limit:    180 seconds
slowest event:      927,357 microseconds
aggregate events:   8,379,325 microseconds
```

The stack aperture changes physical worker storage only. It does not enter the event, interface,
successor, report identity, or rest image.

## Narrow verification

```text
cargo check --manifest-path src/soma/Cargo.toml \
  -p life --example eros_audio_ctc_path_fiber

cargo test --manifest-path src/soma/Cargo.toml \
  -p soma-membrane \
  joint_regional_closure_is_exact_across_one_and_many_host_cores

src/.venv/bin/python -m py_compile \
  src/soma/life/examples/audio_ctc_path_fiber/wav2vec2_source.py
```

The executor regression passed `1 / 1`; the example and source generator checked cleanly. No broad
suite, CUDA run, corpus pass, recording search, or parameter sweep ran.

## Exact commands and artifacts

```text
src/.venv/bin/python \
  src/soma/life/examples/audio_ctc_path_fiber/wav2vec2_source.py \
  --model /home/b/.cache/huggingface/hub/models--facebook--wav2vec2-base-960h/snapshots/22aad52d435eb6dbaf354bdad9b0da84ce7d6156 \
  --speech-commands /home/b/Workspaces/laboratory/runs/speech-commands-cache/raw \
  --output src/soma/observations/eros-audio-ctc-path-fiber-01/generated/source-run-01

cargo run --manifest-path src/soma/Cargo.toml -p life --release \
  --example eros_audio_ctc_path_fiber -- \
  src/soma/observations/eros-audio-ctc-path-fiber-01/generated/source-run-01/SOURCE.json \
  src/soma/observations/eros-audio-ctc-path-fiber-01/generated/source-run-01/REPORT.recorded.json
```

The create-once local measurement artifacts remain ignored. Their final SHA-256 values are:

```text
SOURCE.json
1a99f2e76efd9981eb8fc3d0fa5ffcd6ac16af1bf62d864a5a1c8168cd0e2af9

REPORT.recorded.json
d1bc6199a6f2ebe79a482afb4b36ce96b178dc5bbc34485936a1f55e0fabf013
```

The source generator, receiving world, research contract, and this result are tracked.

## Boundary

Closed here:

1. complete inherited acoustic fields become exact finite path-fiber populations;
2. two nonidentical pronunciations cohere through one returned expression without merging their
   interiors;
3. recurrence emits a new causal expression phase instead of retaining a spent event;
4. an unseen speaker recruits the cultivated expression without a source label or transcript;
5. context/expression cross-faces select situated consequences;
6. unfamiliar context and wrong expression remain OPEN;
7. all direct fields and fiber residuals remain available; and
8. the one cultivated ecology rests and remounts exactly.

Not established here: learning the CTC law inside Soma, continuous speech segmentation, an
unbounded expression vocabulary, autonomous source-label discovery, or corpus scale. Those are not
needed to interpret this result: the experiment closes the missing relative-pronunciation carrier
by lawful inheritance from an existing model ecology.
