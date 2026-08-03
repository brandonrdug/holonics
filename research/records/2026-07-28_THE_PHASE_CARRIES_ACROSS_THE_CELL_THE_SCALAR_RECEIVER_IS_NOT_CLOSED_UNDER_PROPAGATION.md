# THE PHASE CARRIES ACROSS THE CELL; THE SCALAR RECEIVER IS NOT CLOSED UNDER PROPAGATION

**Date:** 2026-07-28  
**Status:** PRODUCTION WAVE CONDITIONING BUILT / OFFICIAL SPEECH AND ROOM
RESPONSE DATA ACQUIRED / FULL REAL-CORPUS DISTRIBUTIONS EXECUTED / STRICT
RETURN FALSIFIED SCALAR-CELL CLOSURE / EXACT CARRIED-PHASE CURRENT BUILT

**Continuation:** The phase/current construction is composed with an exact
receiver-relative emission spectrum and a real binaural return in
`2026-07-29_THE_DIFFERENCE_EMITS_THE_PATH_CARRIES_THE_SPECTRUM_IS_THE_RECEIVER_PHASE_FACE.md`.
That continuation adds a spectral receiver face; it does not replace this
record's complete propagated chronology or conditioning law.

## Present question

Brandon's correction was that the geometry is not principally what should be
rendered. The observable should be the current or wave distribution
propagating through receiver phases and superstates. He then ratified
recording a plan and constructing both the machinery and relevant datasets.

The concrete question was:

> Can the production engine condition a growing receiver-local response
> ecology from real information-flow testimony, emit plural propagated
> distributions before a held-out return exists, grade the complete return as
> topology rather than a scalar score, and use the result to determine which
> phase structure a finite receiver quotient must retain?

This is not a speech classifier and not another image fixture. It is a real
system-identification experiment. Speech PCM is the caused source current,
measured room impulse responses are inherited environmental responses, and
transcripts remain separate receiver testimony. The application does not
calculate a requested learned successor and pass it into production.

## 1. Ratified construction plan and disposition

The plan was:

1. give the production engine receiver-local exact current sections;
2. condition causal response fibers from returned source/target pairs;
3. retain incompatible returns as plural modes rather than average them;
4. generate through every contemporary mode before the selected environment
   returns;
5. grade the return as connected residual support before any later
   conditioning;
6. acquire a real speech corpus and real room-response corpus with verifiable
   provenance;
7. inspect the complete acquired distributions, not one named waveform;
8. test whether a finite integrated-current receiver is actually closed under
   the raw propagation law; and
9. if it is not closed, derive and construct the missing exact phase carrier.

All nine items were performed. The last item was determined by the negative
return, not inserted as a decorative phase feature in advance.

## 2. Production wave conditioning

`crates/holonic-engine/src/wave_propagation.rs` now owns one reusable exact
event law.

A `WavePropagationSpec` declares receiver-local coordinate counts and the
source/target receivers which may actually interact. One
`ExactWaveSection` carries:

\[
(\text{receiver},\text{lineage},\text{origin},\text{step},
  [x_0,\ldots,x_{n-1}]).
\]

Origin and step belong to that receiver chart. They are not an absolute
clock.

For a declared source/target interaction, a returned pair restricts the exact
finite causal response fiber

\[
y_t^o
=
\sum_{d=0}^{s-1}\sum_i
H_{d,i}^{o}x_{t-d}^{i}.
\]

The engine infers the finite causal support \(s\) from the complete returned
extent. Coefficients remain an exact affine version fiber until testimony
fixes them. A contradictory pair does not rewrite or average an established
response. It leaves an obstruction and founds another local mode. A support
change is likewise retained as an obstruction and a new mode.

Generation traverses every contemporary mode before the target return
exists. An unresolved coefficient fiber emits an open affine prediction. A
resolved fiber emits exact values. The later return is graded into contiguous
residual components carrying every exact receiver coordinate. The grade is
fixed before optional conditioning.

The law has:

- atomic event succession;
- source and target lineage;
- open and determined prediction;
- plural response modes;
- exact causal horizons;
- structured return obstruction;
- exact rest/remount;
- canonical serial and multicore standing equality; and
- physical executor testimony only in radiation, never in logical standing.

Resolved coordinate predictions were initially retaining a zero affine
residual vector as large as the kernel for every emitted coordinate. That was
not causal information. `WaveCoordinatePrediction` now stores one exact value
when determined and retains a full affine residual only while genuinely open.
On this experiment the complete artifact fell from approximately 221 MiB to
36 MiB before the new phase receipt was added. The transition-receipt artifact
fell from 51,762,845 bytes to 1,159,657 bytes without changing one logical
result.

## 3. Acquired testimony and provenance

The acquired speech material is the official LibriSpeech `dev-clean`
distribution:

- archive: `dev-clean.tar.gz`;
- bytes: `337926286`;
- declared and observed MD5:
  `42e2234ba48799c1f50f24a7926300a1`;
- observed SHA-256:
  `76f87d090650617fca0cac8f88b9416e0ebf80350acb97b343a85fa903728ab3`;
- 2,703 FLAC utterances and 2,703 aligned transcript entries;
- 310,337,932 native samples, or 19,396.12075 seconds
  (approximately 5.388 hours), at 16 kHz; and
- 54,402 word occurrences over 8,333 distinct written word forms.

The acquired environmental material is the official OpenSLR Room Impulse
Response and Noise Database:

- archive: `rirs_noises.zip`;
- bytes: `1311166223`;
- declared and observed MD5:
  `e6f48e257286e05de56413b4779d8ffb`;
- observed SHA-256:
  `3b50cfde915b3984738169b4beb341e9f6b8062ae4c2076146c5db71c2c05dc7`;
- 61,260 extracted WAV files in the complete database;
- 417 WAV files in the real-response/isotropic-noise collection;
- 325 real RIR files, containing 3,810 response channels;
- 16 kHz, 16-bit native sensor carriage; and
- 92 associated real-database noise files, containing 780 channels.

Both archive member lists were checked for absolute and parent-traversing
paths before extraction. Both official MD5 declarations were reproduced.
Complete local provenance is in
`runs/information-flow-datasets/PROVENANCE.md`.

Sources:

- [LibriSpeech corpus, OpenSLR 12](https://www.openslr.org/resources/12)
- [Room Impulse Response and Noise Database, OpenSLR 28](https://openslr.org/28/)

## 4. Complete distribution inspection

`speech_room_information_flow.rs` decoded every LibriSpeech utterance and all
4,590 channels in the acquired real-response/noise directory. Three nested
dyadic receiver grains were derived from the complete selected response
horizon rather than named as image-like patch sizes:

\[
g\in\{1024,2048,4096\}\quad\text{native samples}.
\]

For speech, the exact signed-current distributions were:

| grain | cells | positive | negative | zero | sign changes |
|---:|---:|---:|---:|---:|---:|
| 1024 | 304,396 | 147,281 | 156,607 | 508 | 180,684 |
| 2048 | 152,872 | 72,137 | 80,502 | 233 | 89,549 |
| 4096 | 77,089 | 34,708 | 42,292 | 89 | 42,526 |

Across the 3,810 real response channels:

| grain | cells | positive | negative | zero | sign changes |
|---:|---:|---:|---:|---:|---:|
| 1024 | 66,854 | 32,769 | 33,926 | 159 | 25,896 |
| 2048 | 34,020 | 16,549 | 17,407 | 64 | 11,506 |
| 4096 | 18,212 | 8,823 | 9,361 | 28 | 4,423 |

These counts are corpus checks and resource testimony. They are not the
learned topology. The per-occurrence and per-channel distributions remain in
the emitted TSV files.

## 5. Conditioning and held-out passage

The response population was sorted by complete native horizon. Three duration
quantiles supplied distinct environmental modes:

1. RWCP circle response, 1,667 raw samples;
2. RWCP circular-line response, 15,000 raw samples; and
3. AIR Aula Carolina binaural response, channel 1, 159,792 raw samples.

Every response was retained completely inside one common 159,792-sample
observation horizon. Shorter responses were followed only by structural zero
support. Nothing was cropped or thresholded.

At every dyadic grain, the measured impulse response entered as returned
testimony to an impulse source. This is exact system identification: the
application supplies the caused response occurrence, while the production
fiber forms and retains its response mode. Nine exact modes were founded:
three environmental modes at each of three scales, with supports 157, 79, and
40 cells. Every response fiber resolved exactly.

The held-out source was selected by median native duration over the entire
LibriSpeech development corpus:

`3081-166546-0059`, 94,720 samples.

Its transcript was retained in a separate receiver:

> I SUPPOSE SHE HAS BEEN CAREFULLY QUESTIONED VERY I SHOULD SAY

The transcript did not fit the acoustic response. At each scale the acoustic
source generated three complete mode continuations. Generation used three CPU
workers because three modes were the complete causal antichain. The requested
24-worker limit did not manufacture nonexistent parallel causal members.
Serial and multicore execution produced identical exact standing on the real
corpus. All predictions then rested and remounted exactly before either
return was formed.

## 6. The control succeeds and the strict return falsifies scalar closure

The first return was a control in the same scalar receiver doctrine used for
conditioning. It was formed only after generation by applying the median
response mode. At all three grains, the corresponding mode was exact and the
other two modes left connected residual supports:

| grain | exact mode | other residual spans |
|---:|---:|---|
| 1024 | 2 | `0..106`, `0..248` |
| 2048 | 5 | `0..53`, `0..124` |
| 4096 | 8 | `0..26`, `0..62` |

This establishes that mode conditioning, plural generation, causal horizon,
grading, and residual topology work as specified.

The strict return then used the shortest measured RIR at native sample
resolution. Production emitted every scalar-mode prediction first. Only then
was the complete exact sample-level propagation formed and restricted back
into the same three scalar receiver charts.

No mode was exact at any scale. Even the response mode belonging to that same
RIR left one connected residual:

| grain | response mode | strict residual span |
|---:|---:|---|
| 1024 | 1 | `0..94` |
| 2048 | 4 | `0..47` |
| 4096 | 7 | `0..23` |

This is not stochastic error and not a failure to choose the right room.
Scalar integrated-current cells are not closed under causal convolution.

## 7. Exact reason for the failure

Let the scalar receiver quotient at grain \(g\) be

\[
Q_g(x)_j=\sum_{a=0}^{g-1}x_{jg+a}.
\]

The control assumed

\[
Q_g(x*h)=Q_g(x)*Q_g(h).
\]

That is false in general. In the product of two local cells, source phase
\(a\) and response phase \(b\) produce exponent

\[
a+b=qg+r,\qquad 0\le r<g.
\]

The quotient \(q\) transports the product into a later coarse cell and the
remainder \(r\) places it in that cell's local phase. Multiplying the two
scalar sums forgets both facts. It assigns every pair to one cell and then
cannot reconstruct the carry.

The missing receiver object is therefore the local phase polynomial

\[
X_j(z)=\sum_{a=0}^{g-1}x_{jg+a}z^a,
\]

with multiplication in the graded chronology, not the quotient
\(z^g=1\). Terms of degree at least \(g\) must be carried to the next cell.
This is the elementary curvature the scalar chronology erased: a local
product changes both phase and causal cell.

## 8. Production carried-phase current

`crates/holonic-engine/src/phase_current.rs` now implements that object.
`ExactPhaseCurrentSection` carries:

- receiver and source lineage;
- exact origin and sample step;
- a finite phase polynomial in every cell;
- exact raw extent; and
- structural final-cell zero support.

`convolve_phase_current` performs the complete graded causal product and
returns:

- the exact phase-resolved output;
- products remaining in the same coarse cell;
- products carried across a cell boundary;
- the exact integer carrier selected by preflight; and
- canonical physical execution testimony.

The carrier is selected from a proven magnitude bound. This corpus used the
exact `i128` path. Values outside that bound use arbitrary-precision integers;
they do not fall into floats.

For the real held-out source and shortest real RIR at phase extent 1024:

- 87,552,764 nonzero products remained local;
- 66,361,616 nonzero products crossed a cell boundary;
- 96,386 exact output samples were formed;
- 24 CPU workers realized the canonical output; and
- the resulting scalar restrictions reproduced the strict-return topology
  above.

The carried population is not a small correction which a scalar average
could safely ignore. It is a second causal branch of the local product.

## 9. Established boundary

This construction establishes:

- deterministic training as exact response-fiber restriction;
- growth by incompatible environmental modes;
- complete generation before return;
- structured loss as residual support;
- exact receiver-relative multiscale current distributions;
- a real-data counterexample to scalar quotient closure;
- the exact phase-and-carry law which repairs that elementary loss; and
- multicore execution without making worker scheduling part of standing.

It does not establish a linguistic deed, speech recognition, raw audio
generation, nonlinear room acoustics, or a universal wave equation. The
native-sample return is the exact linear convolution induced by a measured
RIR, not a separately recorded reverberant utterance.

The full phase-current product is correct but is not yet the conditioned
response species inside `ExactWavePropagationLaw`; that learner still
conditions scalar or finite-channel causal kernels. The precise unresolved
question is now narrower and testable: which exact recursive factorization of
the local phase polynomials preserves the carry relation while allowing
response modes to be conditioned and reused without retaining every native
phase coefficient? A quotient which drops the carry is ruled out by this
experiment. A full coefficient fiber is correct but uncompressed. The
current phase receipt supplies the grading authority for any proposed
recursive factorization.

## Artifacts

- production learned propagation:
  `crates/holonic-engine/src/wave_propagation.rs`
- production carried-phase current:
  `crates/holonic-engine/src/phase_current.rs`
- real-corpus instrument:
  `crates/holonic-engine/examples/speech_room_information_flow.rs`
- dataset provenance:
  `runs/information-flow-datasets/PROVENANCE.md`
- corpus occurrence table:
  `runs/information-flow-distributions/speech-room-real/utterances.tsv`
- speech current distributions:
  `runs/information-flow-distributions/speech-room-real/utterance_current_distributions.tsv`
- room current distributions:
  `runs/information-flow-distributions/speech-room-real/room_current_distributions.tsv`
- exact grades:
  `runs/information-flow-distributions/speech-room-real/heldout_return_grades.tsv`
- exact phase-current receipt:
  `runs/information-flow-distributions/speech-room-real/phase_current_receipt.ron`
- pending and final exact standing:
  `runs/information-flow-distributions/speech-room-real/pending_standing.ron`,
  `runs/information-flow-distributions/speech-room-real/final_standing.ron`
