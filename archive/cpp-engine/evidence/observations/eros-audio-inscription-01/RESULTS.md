# EROS AUDIO--INSCRIPTION 01 — RESULTS

**Date:** 2026-07-21

**Grade:** EXACT INTEGER PCM CARRIER / REVERSIBLE FORWARD+REVERSE BUTTERFLY / ONE FIXED HOST
RECURRENCE RUN / REST-REMOUNT EXACT / EXACT AUDIO-ONLY REPLAY IMPORTED THE PAIRED CONSTITUENT /
NONIDENTICAL SAME-SPEAKER RECORDING DID NOT CONTACT / STOPPED AT RECURRENCE BOUNDARY / NO FLOAT /
NO LOSS / NO THRESHOLD / NO CUDA / NO SOMA INTERIOR CHANGE

## Fixed question

Can an exact paired PCM--inscription event leave one regional constituent which participates in a
later audio-only recording, and does that participation extend beyond literal replay to another
recording of the same speaker saying the same word?

This cell did not ask a classifier to choose among digit labels. No inscription candidates were
present during either probe. The read was whether the later sound imported the earlier regional
factor through the current live Standing law.

## Source and fixed acoustic cut

The source was the original AudioMNIST corpus. The paired event was speaker `01`, digit `0`,
recording `0`, with the supplied UTF-8 inscription `zero`. The exact replay used the same WAV. The
nonidentical probe was speaker `01`, digit `0`, recording `1`.

Every WAV was required to be mono, signed 16-bit integer PCM at 48,000 samples/second. No
resampling, normalization, padding, window threshold, trigonometric basis, or floating-point
quantity entered. Adjacent samples were carried by the reversible integer butterfly

```text
s = a + b                 a = (s-d)/2
d = b - a                 b = (s+d)/2.
```

Both file directions were admitted at ranks 6, 7, and 8. The forward and reverse atlases
reconstructed every original sample exactly. Forward rank-8 sum was the persistent receiving
current, so the inscription could be absent from a later event without changing the receiver
species. Twelve acoustic currents continued across rest; paired exposure supplied one additional
inscription current.

An initial carrier-only preflight preceded this receiver correction and made no behavioral claim.
Before the fixed recurrence run, the receiver was placed on the persistent acoustic sheet because
an absent probe inscription cannot lawfully receive its own event. The behavioral cut was then run
once and was not widened or retuned.

## Exact command and report

```text
cargo run -p life --example eros_audio_inscription -- recurrence \
  /tmp/eros-audio-recurrence.mroG3F/RECURRENCE.json
```

The create-once report has SHA-256:

```text
f1730c2e807330d0a6fb33b5959c897cf147ad4d8388bfe815f8e2cd6003cdc9
```

The raw report is temporary generated testimony. This file is the authored result.

## Result

The exact replay closed; the nonidentical recurrence did not.

| Event | Samples | Currents | Source arcs | Touched prior factors | Grain | Axes | Cells | Paths | Exposed pins |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| paired `0_01_0` seed | 35,877 | 13 | 1,956 | 0 | 3 | 1 | 7,832 | 1,956 | 1,956 |
| audio-only exact replay | 35,877 | 12 | 1,954 | 1 | 4 | 940 | 15,662 | 5,864 | 941 |
| audio-only `0_01_1` | 31,356 | 12 | 1,704 | 0 | 3 | 1 | 6,829 | 1,704 | 1,704 |

The paired seed stood as one constituent with 1,956 open boundaries. Rest/remount preserved the
machine and all thirteen organ capabilities exactly.

The exact audio-only replay touched predecessor ordinal `0` and imported it whole. Its 1,954
acoustic arms made exactly 1,954 cross-event seams: 1,015 RIDEs and 939 FOUNDs. Those FOUNDs raised
the local axis population from 1 to 940. The 1,956 seed arms and 1,954 arriving arms remained as
3,910 open residual boundaries, while the seam population became the additional 1,954 completed
boundaries. Thus the returned total was exactly:

```text
1,956 prior boundaries + 1,954 arriving boundaries + 1,954 seams = 5,864 paths.
```

The two seed boundaries joining sound to `zero` were therefore not looked up afterward or copied
from a label table. They returned because the entire paired constituent participated in the later
audio-only closure.

The second recording supplied 1,704 acoustic arms but formed no compatible cross-event seam. It
left a new grain-3 constituent beside the seed rather than replacing or extending it. The body
ended with two Standing factors. This is the declared recurrence stop, so the held-speaker probe,
English-versus-rotated convention contrast, and unpaired sibling were not run.

## What the boundary means

The direct machine can carry exact acoustic material, rest it, and use a later sound event to
return a prior cross-medium constituent. It is not inventing vocabulary and it is not limited by
the PCM carrier.

The current source atlas nevertheless supplies only within-recording sample relations. A second
utterance changes duration, local phase, speaking rate, amplitude, and the placement of acoustic
events. None of the present butterfly sheets declares a lawful transport across those changes.
Standing consequently sees a distinct exact geometry. Repeating the same event many times would
strengthen literal replay while leaving that missing relation untouched.

The next question is therefore not a larger training corpus or a looser scalar match. It is the
source-world construction of exact relative acoustic charts: carried correspondences among
multiscale pressure events under translation, duration re-base, and amplitude re-base, with the
unmatched residual retained. Only after a nonidentical recording can RIDE such a chart is the
English/rotated/unpaired convention contrast physically meaningful.

## Verification

The example compiles cleanly and the host library suite passed after the run:

```text
385 passed; 0 failed; 7 ignored
```

No production receiving law, cellular Standing law, CUDA path, historical apparatus, observer,
or semantic mechanism changed. The only new source dependency is the integer WAV reader `hound`.
