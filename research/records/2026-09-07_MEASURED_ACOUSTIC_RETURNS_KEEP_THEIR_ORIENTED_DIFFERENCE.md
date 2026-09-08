# Measured acoustic returns keep their oriented difference

[definition] September 7, 2026, on `codex/apple-silicon`, after `7dcb9f1d`. This return
continues AS4–AS5 under the [Apple blueprint](../../docs/plans/HOLONICS_ON_APPLE_SILICON.md).
The preceding checkpoint study retained a controlled digital action. This construction attaches
actual synchronized excitation/receiver recordings and returns their complete temporal defect.
It does not install a learned room response or complete useful sound/English development.

## Source and declared acoustic relation

[established-bounded; source-inspected] [SoundCam](https://masonlwang.com/soundcam/) publishes
recorded music, microphone arrays and electrical loopback channels. Its
[paper](https://arxiv.org/abs/2311.03517) describes synchronized playback/recording at 48 kHz,
ten seconds of excitation and four subsequent seconds for decay. We use the raw recorded
electrical loopback as an excitation witness, with its simultaneous microphone recording.
The digital float64 music source, deconvolved impulse responses and delay-adjusted recordings
are separate products and are not substituted for either measured channel.

[established-bounded; measured] `research/experiments/apple_silicon/fetch_soundcam.py` acquired
only `Human1/music_audio.npy` and `Human1/music_directlines.npy` from the
[Stanford small-set archive](https://downloads.cs.stanford.edu/viscam/SoundCam/TreatedRoomSmallSet.zip).
One acquisition receipt records five ZIP ranges transferring 31,340,408 bytes from the
659,806,886-byte archive. Its ETag is
`"6700980d-2753daa6"`; the selected member CRCs are `74320442` and `52bf1d9c` respectively.
The original little-endian PCM16 arrays have shapes `(3,10,672000)` and `(3,672000)`.
The 33 exported mono WAVs preserve every original coefficient. Source arrays, WAVs and
acquisition receipt occupy 88,752,401 bytes outside Git under `.local/datasets/soundcam`.
The receipt retains archive/range/member identities, exact array selectors, output hashes,
the source clock and project licensing references. These are exterior provenance, not semantic
identities. Room/person labels never supply conditions or choose a native current.

[definition] The first application uses an explicit unit digital response as its initial
prediction. Electrical loopback and microphone ADC values are normalized PCM coordinates;
unit gain does not assert calibrated acoustic pressure, equal instrument gain or a physical
room law. Their common raw recording clock is retained without onset fitting, resampling or
delay correction. A later temporal constitutive family must carry propagation, gain and the
remaining observed difference at its declared scope.

## Native owners and exact operation

[established-bounded; implemented-exact] `phase_current::resident::compare_resident` borrows
both complete current views and returns `ResidentPhaseDifference`. It requires the same receiver,
sample step and phase chart. Origins may differ by an integral clock step. The support receipt
identifies the exact common interval and both excluded populations; a predicted tail outside the
recording remains unobserved. No padding or lack of observation supplies a zero target.

[proved-derived] If the overlap coordinates are `p/a` and `o/b`, let `d=lcm(a,b)>0`.
The returned current has numerator `o(d/b)-p(d/a)` and denominator `d`. Reducing the complete
vector and denominator by their common divisor preserves every coordinate of `o/b-p/a`.
This is the oriented receiver difference, including both quadratures; it is not a condition
estimate or an assertion that the observations belong to a particular generator family.

[established-bounded; implemented-exact] The resident binding
`resident_section/surface_phase_difference.rs` records validation, independent coordinate
products, normalization and publication in one passage. CUDA
`kernels/phase_current_difference.cuh` and Metal `accelerators/metal/phase_difference.metal`
use the existing checked wide arithmetic and convolution normalization/publication. Validation
checks the full input views, dispositions, denominators and structural padding before product
lanes run. Private candidate output is published only after the complete receipt succeeds.
Both operand carriers survive; no numerical intermediate is read to the CPU.

[proved-derived] The existing convolution already uses the common denominator `a*b` for
every product. Normalizing each complex product and then multiplying it back by the removed
factor restores precisely its original numerator. Both device implementations now accumulate
that original checked complex numerator directly, then perform the existing complete-vector
normalization. Product/sum bounds, final i64 publication, causal order and tail remain unchanged.
This removes redundant rational work; no speedup ratio is claimed without a matched measurement.

## Verification and recorded return

[established-bounded; measured] Nineteen focused native controls pass with:

```sh
cargo test -p holonic-engine --lib phase_current::resident:: -- --include-ignored --test-threads=1
```

[established-bounded; measured] Five new controls cover full oriented rational differences,
clock/receiver refusals before launch, shifted overlapping support, retained excluded populations,
malformed points/padding, late overflow, wide normalization, all coordinates of a 4,099-frame
parallel section and zero hot numerical readouts. Fourteen convolution controls include the
shared conditional-relation composition, both storage placements and unequal denominators.
The new unequal-denominator test initially omitted the final `(2,-1)` causal coefficient in its
expected vector; direct multiplication supplied the correction. Native execution was unchanged.

[established-bounded; measured] `cargo build -p holonics-hna --example recorded_acoustic_return`
passes. The application then returns all three complete 672,000-frame loopback/microphone-0 pairs,
each in its own process with the explicit initial unit response. The
[raw reports and acquisition receipt](2026-09-07_measured_acoustic_return/) retain source files,
hashes, selected channels, full clock/support and stage costs. Native exact sections and cold WAVs
remain outside Git at `.local/experiments/soundcam-native-return/row_{000,001,002}/`.
The thirty acquired microphone recordings are available material; these executions use three.

[established-bounded; measured] `compare_recorded_acoustic_return.py` verifies the selected
source NPY arrays against every WAV sample, every coordinate of the native prediction and
oriented difference, clocks, common support, terminal PCM and its exact projection residual.
All three reports pass, including 1,344,000 real/imaginary coordinates in each returned section.
Four negative observer controls reject a changed clock, a declared hot numerical readout, an
altered final exact coefficient with its hash updated, and altered PCM with its hash updated.
The acquisition's local malformed dtype and bounded-deflate controls also pass. Original arrays
and acquired WAVs remain untouched; no source, cache or evidence was removed.

[established-bounded; measured] M1 Pro debug-build wall times in seconds are:

| SoundCam row / microphone | Native prediction | Native oriented return | Cold exact prediction | Cold difference + audio | Whole process study |
|---|---:|---:|---:|---:|---:|
| 0 / 0 | 1.078520 | 1.342001 | 0.167540 | 14.405782 | 18.764140 |
| 1 / 0 | 1.098458 | 1.355091 | 0.167959 | 14.450938 | 17.921433 |
| 2 / 0 | 1.098214 | 1.364538 | 0.174234 | 14.719390 | 18.204402 |

[established-bounded; measured] Each prediction and difference has one deed, zero numerical
readouts/ingress and 64 receipt bytes. Peak tracked native residency is 139,776,340 bytes;
86,016,112 remain while the complete operands and outputs are borrowed. Each cold section read
returns 21,504,016 bytes. No PCM sample clips in these three returns. CPU codec objects, process
RSS and durable bytes are separate from the native residency census. GPU timestamps are present;
the raw reports distinguish them from wall time. This is batch execution with an expensive cold
codec, not a completed real-time streaming application or a measured power claim.

[established-bounded; measured] The unit-response defect has respectively about 3.68, 4.38 and
3.12 times the recorded microphone's squared PCM amplitude sum. The exact ratios and complete
oriented currents survive in the reports/artifacts. This exposes the starting model's discrepancy;
it does not attribute that discrepancy to one physical cause or establish acoustic learning.
The CUDA counterpart was inspected, but CUDA compilation/execution was unavailable on this Mac.
No Lean source or import changed.

## Remaining developmental attachment

[open] The measured difference is now available as a resident rational current, with its actual
source/receiver support. A declared acoustic action and its condition/contact law must use that
evidence to develop persistent generative standing. An exact condition fibre may be empty when
a restricted action cannot represent an observation; noise and unmodelled transport must remain
explicit instead of manufacturing a compatible target. A residual receiver alone does not
perform that development. Useful sound perception/production, English/conversation capability
and the complete continuing streaming application remain open under the active AS4–AS5 goal.
