# AS4 ESC-50 acoustic controls

`prepare_esc50_acoustic_controls.py` prepares a small, reproducible control family from the
already procured original ESC-50 WAVs under `.local/datasets/esc50`. It selects one 1 s base window
per source by maximum RMS energy using only a declared amplitude observer, then takes a centered
0.25 s control window from that base and writes four exact PCM16 controls:

- the complete 1 s maximum-energy base window;
- original sample order;
- reversed sample chronology;
- exact polarity inversion, refused if the signed-16 domain cannot represent the inversion.

The original WAV bytes and metadata remain untouched. The listening manifest retains source file,
fold, source hash, exact base/control sample ranges, observer settings, sample rate, and PCM metrics for every
variant. The selection receipt records the source range, observer basis, RMS, threshold, and
whether a candidate was refused for exact polarity inversion; replacement candidates are chosen
by the same deterministic fold order. ESC-50 semantic target/category labels are deliberately
omitted from the control manifest. `native_current_metrics` in this preparation manifest remains null; native returns belong to
the separate run/observer report. Preparation invokes no learner, GPU operation, classifier, or playback.

```sh
VENV=.local/venvs/apple-silicon/bin/python
"$VENV" research/experiments/apple_silicon/prepare_esc50_acoustic_controls.py \
  --count 10 --base-window-seconds 1.0 --window-seconds 0.25 --amplitude-threshold 0.01
```

The generated WAVs are directly inspectable by the existing `holonics-audio playback` CLI for playback inspection. An all-zero prefix in an ESC-50 source is a valid
silence fixture, but is not used as sound-perception evidence; maximum-energy selection avoids
using that prefix as the initial control. This preparation step makes no claim about native
perception or generated sound.

Run the first three prepared sources and their quarter-second controls through the public HNA
application, then inspect the actual emitted current and generated PCM:

```sh
"$VENV" research/experiments/apple_silicon/run_acoustic_controls.py --output NEW_RUN_DIRECTORY
"$VENV" research/experiments/apple_silicon/observe_acoustic_controls.py \
  --runs NEW_RUN_DIRECTORY/runs.json --receiver FIXED_RECEIVER.json --output NEW_OBSERVER_DIRECTORY
```

The observer compares every rational phase coordinate including its denominator, checks it
against the complete retained quadrature fibre, and reads native successor rank and receiver
fibres from public `inspect`. Generated PCM is read from each render's `sound.wav`; the figure
separately labels source PCM, one actual oriented current coordinate and generated PCM.
Use `--render-root EXISTING_RENDER_DIRECTORY` to recompute an observer without rendering or
replaying native development. The declared fixed receiver and source scope are checked against
the reused artifacts. The [admitted result](../../records/2026-09-06_APPLE_NATIVE_PHASE_AND_ACOUSTIC_COMPOSITION.md)
contains the completed three-source comparison.
