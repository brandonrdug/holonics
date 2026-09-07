# Acoustic experiments through native HNA

[definition] This application attaches ordered PCM material to the existing native phase
recurrence. It retains the WAV bytes, complete `ExactAcousticOccurrence`, sample clock, every
native return, pending input and one native checkpoint. Labels and transcripts do not enter the
sound-current interface. The [Apple plan](plans/HOLONICS_ON_APPLE_SILICON.md) governs scope.

## Digital contact and return

[definition] At sample ordinal `n` and exact time `n / sample_rate`, PCM codeword `s[n]` enters
as the exact complex current `(s[n] / pcm_divisor, 0)`. This is an explicitly declared digital
amplitude chart. It is not a calibrated pressure/velocity law, analytic-signal reconstruction,
frame classifier or spectral summary. The complete PCM fibre remains recoverable; zero samples
and their duration remain ordinary occurrences. Caller packet sizes only choose process cuts.

[definition] An optional one-sample digital return declares one exact complex gain per native
port. The exterior world returns `s[n]/divisor + sum(gain[p] * emitted[n-1,p])` through the
previous actual source handle. This is an explicit digital interaction, distinct from microphone
reception through a room. With no return law, the sample enters unpaired. The GPU owns current,
relation formation, receiver fibre and successor; the exterior application does not choose a
preferred answer from a plural fibre.

[definition] The example material uses two equal-admittance junctions, one with real unit
transport and one with imaginary unit transport. Equal admittance exchanges the incoming and
held phases. This retains an exact signed-word sampled domain for extended controls without
rounding a growing rational denominator. It is a declared constitutive specimen, not learned
sound-category competence. Other admitted material may reach its carrier aperture and refuse;
the pending sample and last confirmed state must remain available.

## Run, stop and resume

```sh
cargo build -p holonics-workbench --bin holonics-acoustic
mkdir -p .local/artifacts/acoustic

target/debug/holonics-acoustic run \
  --seed applications/holonics-workbench/examples/native/acoustic-seed.json \
  --wav .local/datasets/esc50/audio/1-100032-A-0.wav \
  --occurrence esc50-first-contact \
  --return-couplings applications/holonics-workbench/examples/native/acoustic-digital-return.json \
  --samples 4096 --checkpoint .local/artifacts/acoustic/prefix.hna

target/debug/holonics-acoustic resume .local/artifacts/acoustic/prefix.hna \
  --checkpoint .local/artifacts/acoustic/continued.hna
```

[definition] `--samples` is an exterior process cut, including zero; omission runs the retained
occurrence to completion or an explicit refusal. Checkpoint publication uses new paths and never
overwrites an existing artifact. A failed receive retains its exact pending current and source;
resume retries that pending occurrence without replaying earlier development.

## Hear actual native emission

[definition] The production factor receives only actual root-frame native emitted currents in
causal/node order. It preserves both quadratures and every silent port. Noncontiguous emission
orders refuse; absence is not filled with invented silence. It does not fabricate an old
open-world-tube receipt or substitute the older granular ecology.

[definition] Calibrate a cold acoustic receiver once, then reuse its JSON unchanged across
comparisons. Order stride/support determine playback chronology; frequency support and logarithmic
amplitude calibration are receiver declarations. They are not native learning coefficients.
`render` retains exact production and potential/current reconstruction beside the lossy WAV.

```sh
target/debug/holonics-acoustic receiver .local/artifacts/acoustic/continued.hna \
  --output .local/artifacts/acoustic/receiver.json \
  --sample-rate 44100 --stride 1 --support 64 --low-hz 80 --high-hz 8000

target/debug/holonics-acoustic render .local/artifacts/acoustic/continued.hna \
  --receiver .local/artifacts/acoustic/receiver.json \
  --output .local/artifacts/acoustic/rendered
```

[definition] This spectral receiver makes native current audible; it does not claim waveform
reconstruction or intelligible speech. Compare the complete native return as well as the rendered
surface, since different currents can collapse under the PCM projection.

## Curated material and live apparatus

[established-bounded; measured] The local ESC-50 acquisition contains 2,000 five-second mono
PCM16 WAV files at 44.1 kHz. The [upstream dataset](https://github.com/karolpiczak/ESC-50)
provides categories, folds and per-clip attribution. Its full collection is CC BY-NC 3.0; ESC-10
is the CC BY subset. Acquisition preserves original files and metadata under ignored
`.local/datasets/esc50`; `fetch_esc50.py` records the immutable Hugging Face mirror revision.

[established-bounded; measured] The speech companion retains 100 deterministic LibriSpeech
`dev-clean` clips, original FLAC, exact PCM16 WAV conversion, speaker/chapter identity and transcript.
This subset has two speakers and four chapters; it is not the full development split.
[OpenSLR](https://www.openslr.org/12) supplies the CC BY 4.0 source. The acquisition recipe and
limitations are in [the speech apparatus note](../research/experiments/apple_silicon/README_LIBRISPEECH.md).

[definition] Brandon's later instruction substitutes curated datasets for the proposed microphone
experiment. The Swift [audio application](../applications/holonics-audio/README.md) supplies finite
capture/playback with explicit format, clock, interruption and gap receipts. Building it and
running codec checks do not establish live acoustic contact. Speech/text exposure must preserve
actual shared interactions; a stored transcript or a WAV renderer alone does not implement it.

## Speech and text exposure

[definition] `SpeechExposureApplication` composes the acoustic application and a separate byte
occurrence in one native session. All sound samples arrive before any transcript byte. A byte
enters as `(byte / transcript_divisor, 0)` under a declared digital codeword chart. With the
same explicit return circuit, the arrival also contains the gain-weighted actual prior root
emission and consumes its actual source handle. Without a circuit, it remains unlinked. This
is serial exposure to curated sound and text, with no word alignment or semantic equality
inferred from a transcript. The native receiver retains its complete plural/open consequences.

[definition] The complete application checkpoint preserves both sources, both cursors, pending
sound or text, native history and the actual successor. The public CLI can cut before sound,
at the modality boundary, in the transcript or after completion. Native sound production can
read all actual acoustic and text-reaction emissions; it cannot read a stored WAV as output.

```sh
cargo build -p holonics-workbench --bins
# transcript.txt contains the original transcript from the locally retained dataset manifest.
target/debug/holonics-speech run \
  --seed applications/holonics-workbench/examples/native/acoustic-seed.json \
  --wav .local/datasets/librispeech-dev-clean-subset/wav/2277-149896-0000.wav \
  --occurrence librispeech:2277-149896-0000 \
  --transcript .local/artifacts/speech/transcript.txt \
  --return-couplings applications/holonics-workbench/examples/native/acoustic-digital-return.json \
  --occurrences 105440 --checkpoint .local/artifacts/speech/audio-complete.hna

target/debug/holonics-speech resume .local/artifacts/speech/audio-complete.hna \
  --checkpoint .local/artifacts/speech/complete.hna

target/debug/holonics-speech inspect .local/artifacts/speech/complete.hna

target/debug/holonics-speech render .local/artifacts/speech/complete.hna \
  --receiver .local/artifacts/acoustic/receiver.json \
  --output .local/artifacts/speech/rendered
```

[definition] The sonification clock is the fixed receiver's order stride and sample rate. The
source clock remains separately retained (16 kHz for this LibriSpeech utterance). Rendering
under the 44.1 kHz receiver compresses those arrival intervals in playback; it is an explicit
receiver change, not preservation of the speech waveform or speech synthesis. Speech
recognition, intelligible native speech, acoustic meaning and general cross-modal competence
are not established by this exposure apparatus.

[established-bounded; measured] Three resident speech tests verify linked and unlinked conduct,
byte-identical full checkpoints after cuts at zero, the sound/text boundary, mid-text and end,
and refusal of premature or altered pending text before any native deed. The
[Apple implementation record](../research/records/2026-09-06_APPLE_NATIVE_PHASE_AND_ACOUSTIC_COMPOSITION.md)
retains the actual execution and receiver scope.
