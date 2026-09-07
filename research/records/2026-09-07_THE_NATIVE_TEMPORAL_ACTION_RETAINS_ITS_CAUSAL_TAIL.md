# The native temporal action retains its causal tail

**Date:** September 7, 2026. **Branch:** `codex/apple-silicon`.
**Source parent:** `65b4c5b2`. **Scope:** resident causal polynomial action and its composition
with the existing conditional relation, acoustic chart and condition Preimage Fibre.

[project-postulate] Brandon resumed AS4–AS5 after the shared generator/linguistic handoff and
blueprint update. Useful recorded sound, then recorded English/conversation, persistence and
consumer cost remain the goal. A device primitive or a declared digital action does not complete it.

## Existing owner and exact composition

[established-bounded; source-inspected] `holonic-engine/src/phase_current.rs` already owns
`convolve_phase_current`: complete temporal polynomial coefficients, the carried product, exact
clock and both source lineages. Its CPU implementation is an independent cold observer/reference.
The absent port was the execution of this action on `ResidentConstitutiveCurrent` operands,
without copying numerical currents back to that reference owner.

[established-bounded; implemented-exact] `phase_current::resident` now provides that port.
`ResidentPhaseCurrentView` borrows a rational complex current with validated raw extent, phase
extent, exact origin and positive sample step. `convolve_resident` produces all `N + K - 1`
complex coefficients of the two input polynomials. Their clocks must share sample step and phase
extent; output origins add. Coordinates beyond a declared raw extent must be exactly zero.
The resulting `ResidentPhaseConvolution` borrows both complete particular operands, so summation
does not discard those source histories. It does not claim to enumerate all possible factorizations
of a given output. `view()` carries the result directly into another resident temporal operation.

[established-bounded; implemented-exact] Metal `section_phase_convolution` uses existing checked
wide multiplication, addition, normalization and rational-current validation. Every output word
is checked before publication. Negative/zero/nonpoint denominators, nonpoint coordinates,
nonzero padding and nonunique current dispositions refuse. Host launch admission checks surface,
shape and actual device scratch aperture before allocating output. Scratch contains
`2 * (N + K - 1)` wide carriers; on Metal each has twenty bytes, with launch allocation rounded
to sixteen-byte alignment. Inputs are never mutated. Arithmetic can still refuse at the declared
wide or final signed-word carrier boundary.

[established-bounded; source-inspected] The matching CUDA entry is in
`kernels/phase_current_convolution.cuh`, included by `exact_resident_section.cu` and watched by
`build.rs`. Its ABI and use of the corresponding checked wide helpers were reviewed. This Mac
has no `nvcc`; this return supplies neither CUDA compilation nor measured cross-device parity
for the new convolution kernel.

[established-bounded; implemented-exact] `AcousticFieldCell::temporal_view()` binds the resident
operation to the existing exact PCM chart. It retains the actual recording support/origin,
receiver, lineage, sample step and structural padding without advancing the chart cursor.
The response origin belongs to its declared local delay chart. A recorded reply interval is
not thereby an impulse response, and equal cell ordinals in two utterances do not establish contact.

## Verification

[established-bounded; measured] Thirteen engine temporal controls passed on Apple Metal: five
existing cold phase-current controls and eight new resident controls. The first command returned
twelve passes; the additional plural-fibre control was compiled and run separately after addition.

```sh
cargo test -p holonic-engine --lib phase_current:: -- --include-ignored --test-threads=1
cargo test -p holonic-engine --lib phase_current::resident::tests::temporal_point_consumer_preserves_a_plural_fibre -- --include-ignored --test-threads=1
```

[established-bounded; measured] These controls cover complete causal carry against the existing
cold owner, nonzero origins and exact clocks, rational complex serial continuation without ingress
or numerical readout, wide-product normalization before word conversion, late overflow and
malformed-source preservation, chart/surface refusal before allocation, the last admitted scratch
coordinate and next-extent refusal, and preservation of a plural current when the point consumer
refuses it.

[established-bounded; measured] The native learning control uses the existing
`ResidentConstitutiveFibre::found_bilinear_contact(2,2,3)`. Twenty-five independent source/response
impulse combinations are applied to the native temporal apparatus; only its resident returns
enter the learner. A later source and observation infer the unprovided response
`[(2-i)/3, (5+3i)/3]`. That inferred condition predicts another source's complete three-coefficient
return exactly. Development, preimage derivation and prediction use no numerical host readout.
This is a declared finite polynomial-action control, not corpus-cultivated acoustic competence.

[established-bounded; measured] Eight acoustic-field controls passed, including the new actual
source-clock attachment and two-tap causal-tail control, plus the previous source/padding,
recording-range, rational ingress and refused-source continuation checks:

```sh
cargo test -p holonics-hna --lib native::acoustic_field::tests -- --include-ignored --test-threads=1
```

## Recorded coefficient experiment

[established-bounded; measured] The public `recorded_temporal_action` example ran on an original
ESC-50 WAV and a LibriSpeech WAV. Each run founds one conditional owner with four source complex
coordinates, two response coordinates and five output coordinates. Six fixed interior clock cuts
provide thirty recorded observations under five declared digital response controls. Five native
zero-source calibration observations expose the direct condition axes. Two further fixed clock
cuts are held out. Neither amplitude, rank nor an expected answer selects a cut. All native
development, preimage and prediction stages have zero numerical host readouts; inspection happens
after the native operations. The learner never receives the hidden response control directly.

[established-bounded; measured] The [LibriSpeech receipt](2026-09-07_native_temporal_action/librispeech.json)
returns the unique condition `[(2-i)/3, (5+3i)/3]` and exactly predicts the complete later temporal
current. The source contains 125,680 mono samples at 16 kHz; this experiment learns from six
four-sample cells, not from the full recording. Thirty recorded observations take 0.067211667 s;
condition inference takes 0.002308208 s and prediction 0.004068084 s. Whole cold execution takes
0.198372 s. These small-aperture measurements do not establish sound throughput or speech quality.

[counterexample; measured] The [ESC-50 receipt](2026-09-07_native_temporal_action/esc50.json)
has zero hidden and later source cells at the declared cuts. The compatible condition retains
four free directions and its point consumer refuses without choosing a condition or advancing
the relation. The run retains 35 observations rather than the successful run's 36th predictive
occurrence. Source and output silence are retained; this is not a sound recognition result.

[established-bounded; measured] The independent
[Fraction/PCM comparison](2026-09-07_native_temporal_action/comparison.json) checks the original
WAV hashes and source sample supports, all complex rational convolution coordinates including
the final carry, inferred conditions and the native-stage readout census. For the silent case,
every basis direction in the returned condition fibre has zero later image under the declared
polynomial action. Thus that entire image is fixed even though the condition remains plural;
the point-condition consumer alone cannot expose that supported consequence. Desktop subsequently
pushed `82fef476`, supplying the shared condition-image/receive owners for the next integration.
Their whole-family evidence is not a universal certainty gate on generation.

```sh
cargo build -p holonics-hna --example recorded_temporal_action
target/debug/examples/recorded_temporal_action .local/datasets/esc50/audio/1-100032-A-0.wav research/records/2026-09-07_native_temporal_action/esc50.json
target/debug/examples/recorded_temporal_action .local/datasets/librispeech-dev-clean-subset/wav/2277-149897-0007.wav research/records/2026-09-07_native_temporal_action/librispeech.json
python3 research/experiments/apple_silicon/compare_recorded_temporal_action.py research/records/2026-09-07_native_temporal_action/esc50.json research/records/2026-09-07_native_temporal_action/librispeech.json --output research/records/2026-09-07_native_temporal_action/comparison.json
```

## Remaining product work

[open] General situated material/condition binding, useful sound perception and production,
recorded English/conversation, persistence of the resulting acoustic ecology and measured
streaming consumer cost remain unfinished. A convolution family supplies one temporal action;
it is not a universal sound law or a learned utterance-to-reply mechanism. Actual generated sound
must come from productive native standing and its declared timed receiver, with complete causal
composition across source sections. Fixed sonification and a sequence of independent short cells
do not close that boundary.
