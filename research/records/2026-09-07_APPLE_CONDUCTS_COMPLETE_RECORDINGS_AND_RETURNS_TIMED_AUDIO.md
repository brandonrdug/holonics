# Apple conducts complete recordings and returns timed audio

[definition] September 7, 2026; `codex/apple-silicon`, continuing the active AS4–AS5 goal from
`a551eecb`. This return composes the existing resident causal action, retained condition contact
and an exterior timed receiver. The controlled digital two-tap experiment does not supply a
physical room law, an utterance-response law or a completed sound/English model.

## Complete resident operation

[established-bounded; implemented-exact] `phase_current::resident::convolve_resident` now
retains complete outputs beyond threadgroup storage. Small outputs keep their existing shared
placement. Larger outputs allocate resident wide workspace and record four dependent commands
inside one passage: complete input validation, products, whole-result normalization and final
word publication. Both operand carriers remain borrowed until the operation returns; no
intermediate numerical current is read by the host. The full `N + K - 1` causal support returns.

[established-bounded; source-inspected] Each parallel product reads immutable operands and the
validated common denominator, and writes only its own real/imaginary workspace coordinates.
Its source summation retains the original ascending order. Complete point/padding/disposition
validation precedes parallel arithmetic, whose possible refusal is the shared carrier flag.
The subsequent gcd joins the complete result before disjoint output packing. All output is
private until the whole passage succeeds; an obstruction discards it without altering inputs.
Thus the complete accepted result and refusal kind do not depend on product-worker ordering.
This is a placement argument for this operation, not a general parallel HNA theorem.

[established-bounded; implemented-exact] Apple execution lives in
`accelerators/metal/phase_convolution.metal`; the small kernel moved there from `native_phase.metal`.
Both placements now reuse the paired/enclosed field's checked product/add helpers, matching the
CUDA operation's accumulator admission. In particular, checked addition refuses magnitudes
at or above `2^126` before normalization, even when an abstract final quotient could be small.
The existing standalone wide-arithmetic probe keeps its own declared helper scope.

[established-bounded; implemented-exact] `holonic-mount/src/metal.rs` now records actual flat
dispatch geometry for the explicitly independent product and pack kernels. It checks positive
dimensions, flat shape, the pipeline threadgroup limit and u32 thread addressing. Existing
complete serial kernels retain one thread. Captured command replay keeps these dimensions and
the same ordered encoder dependencies. The CUDA source receives the corresponding four
kernels through its existing include; no new executor or learning law is introduced.

## Timed receiver and reconstruction

[established-bounded; implemented-exact] `AcousticFieldChart::mount_complete` returns an
`AcousticFieldSection` containing every actual recording/range coefficient at its exact clock.
It excludes structural final-cell padding and preserves the source range, parent recording,
receiver and lineage. Mounting neither advances the chart cursor nor creates one native
occurrence per PCM sample. The phase partition remains an exterior chart declaration.

[established-bounded; implemented-exact] The public
`life::native_intelligence::NativeAcousticTemporalPcm16Projection` is a cold receiver: one complex
coefficient becomes one stereo PCM frame, real on channel zero and imaginary on channel one.
A positive rational digital gain and exact `sample_step = 1 / sample_rate` are required.
Toward-zero integer quantization precedes signed-16 clipping. The original carrier, both PCM
coordinates, exact residuals and clipping flags are retained and validated. The carrier is
reconstructed by `(PCM + residual) / gain`; this channel packing makes no binaural or SPL claim.

[established-bounded; implemented-exact] The optional third argument of `recorded_temporal_action`
enables v5 full-recording outputs. Two complete native operations reuse the immutable earlier
condition and its actual successor, respectively. Both happen after the hidden observation;
the earlier four-coefficient prediction retains its original chronology. No terminal numerical
inspection selects a condition or calculates a developmental target. The experiment's fixed
digital gain is 8192 PCM units per current unit, without input-peak normalization or tone synthesis.

[definition] Each WAV is accompanied by the complete canonical `ResidentSectionRest` plus its
clock/gain/receiver metadata in the report. Together these retain the entire exact projection
fibre with an executable decoder. SHA-256 values protect these local wires only. Files in
`.local/experiments/` are local output artifacts, not committed corpus material. These section
files persist output currents; they are not a checkpoint of the learned relation or condition owner.

## Verification and measured return

[established-bounded; measured] Thirteen resident temporal controls pass, including complete
16,000-sample convolution against the independent cold owner, complex currents on both sides
of the shared/workspace boundary, wide-denominator normalization, the checked-add limit,
malformed-before-arithmetic refusal and preservation of original inputs. Eleven mount-library
controls pass, including captured multi-group geometry and invalid launch refusal. Five cold
PCM controls pass for both quadratures, clock/frame shape, silence, clipping reconstruction and
corrupted receipt refusal. The complete concatenated Metal source compiles and links with Xcode.

[established-bounded; measured] The first workspace test run returned ten passes and three
failures: the old Metal mount dispatched one thread and left the final denominator unwritten.
The explicit grid binding above repaired the cause; all thirteen tests then passed. The failing
controls were retained and strengthened. No CUDA execution or compilation is claimed on this Mac.

[established-bounded; measured] The example builds and nine acoustic-field controls pass,
including complete range/clock mounting and the existing source/contact/carry controls. This
required repairing a stale test consumer left by the desktop field-input enum change: it now
explicitly reads the exterior-input variant. These are 38 passing scoped Rust controls in total,
not a workspace-wide or CUDA test result.

[established-bounded; measured] The [ESC-50 return](2026-09-07_native_temporal_action/esc50-whole-waveform.json)
and [LibriSpeech return](2026-09-07_native_temporal_action/librispeech-whole-waveform.json) both
finish without whole-recording refusal. The [independent comparison](2026-09-07_native_temporal_action/whole-waveform-comparison.json)
checks every exact output coordinate, both PCM channels, full tail, clock, frame count, clipping
population and reconstructible residual against original PCM and the actual retained condition.
It also retains the earlier complete field/current/fibre comparisons. All four WAVs have zero
clipped samples. These are separate controlled studies, each with its own continuing local
relation; they do not constitute one cultivated model spanning the two recordings.

[established-bounded; measured] The [cold observer controls](2026-09-07_native_temporal_action/whole-waveform-observer-controls.json)
reject a changed clock, missing terminal readout, altered exact tail and altered PCM (including
updated wire hashes for the latter two). Both earlier v4 recorded reports remain accepted.

[established-bounded; measured] These M1 Pro debug-build costs include the declared stages:

| Receiver/work | ESC-50 | LibriSpeech |
|---|---:|---:|
| Source duration / rate | 5 s / 44,100 Hz | 7.855 s / 16,000 Hz |
| Output frames per condition | 220,501 | 125,681 |
| Full source mount, wall seconds | 0.025730 | 0.018154 |
| Earlier-condition action, wall / GPU seconds | 0.303172 / 0.301661 | 0.209275 / 0.208124 |
| Successor-condition action, wall / GPU seconds | 0.301989 / 0.301462 | 0.321747 / 0.321226 |
| Both cold exact audio exports, wall seconds | 4.179861 | 9.564269 |
| Complete experiment, wall seconds | 6.619638 | 11.351104 |
| Peak counted resident bytes | 39,000,260 | 22,314,212 |
| Complete section bytes per output | 7,056,088 | 4,021,848 |
| WAV bytes per output | 882,048 | 502,768 |

[established-bounded; measured] Every whole-recording action uses one deed and one completed
Metal command buffer, six allocations, zero ingress, zero numerical readouts and 64 receipt
bytes. The declared source mount accounts for 7,056,016 / 4,021,776 ingress bytes. Only the cold
audio stage detaches the two exact outputs, accounting for 14,112,096 / 8,043,616 numerical
egress bytes. GPU timestamps are available for these actions. Counted resident memory excludes
CPU receiver objects and filesystem storage; no process-memory peak, power or real-time stream
claim follows. Cold exact projection/export now dominates the complete study cost.

[established-bounded; measured] A cold waveform inspection retains the recorded temporal
envelope. ESC-50's uninformative fixed cuts leave its actual condition unchanged, and the two
complete outputs are exactly equal. LibriSpeech's nonzero evidence changes the retained
condition and the full output has both quadratures. The local
`.local/experiments/native-temporal-audio/waveforms.png` and the four WAVs permit direct product
inspection. No listening-based speech intelligibility or generative usefulness claim is made.

[definition] Reproduce the bounded return with new output paths:

```sh
cargo test -p mount --lib -- --test-threads=1
cargo test -p holonic-engine --lib phase_current::resident::tests:: -- --include-ignored --test-threads=1
cargo test -p life --lib native_intelligence::membrane_acoustic::temporal_receiver::tests:: -- --test-threads=1
cargo test -p holonics-hna --lib native::acoustic_field::tests:: -- --include-ignored --test-threads=1
cargo build -p holonics-hna --example recorded_temporal_action
target/debug/examples/recorded_temporal_action SOURCE.wav NEW_REPORT.json .local/experiments/NEW_AUDIO_DIR
python3 research/experiments/apple_silicon/compare_recorded_temporal_action.py NEW_REPORT.json --output NEW_COMPARISON.json
```

## Continuing construction

[open] AS4–AS5 remain active. This change removes a full-recording placement obstruction and
supplies timed exterior reception of the resident action. The next construction must bind
actual acoustic material and receiving circumstances to retained generative standing, develop
it across distinct recordings and persist the same ecology. The present two-tap controls and
the unchanged condition under uninformative sound evidence do not establish that capability.
Useful English/conversational recognition and generation, public continuing streaming and
consumer-cost completion remain required by the unchanged blueprint.
