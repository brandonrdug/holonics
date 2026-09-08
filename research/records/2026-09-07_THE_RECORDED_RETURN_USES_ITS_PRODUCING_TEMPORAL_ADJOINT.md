# The recorded return uses its producing temporal adjoint

[definition] This continues AS4–AS5 after the [shared internal-mode port](2026-09-07_APPLE_RETURNS_THE_INTERNAL_CURRENT_AND_SHARED_DRIVE_MODE.md).
The [earlier measured return](2026-09-07_MEASURED_ACOUSTIC_RETURNS_KEEP_THEIR_ORIENTED_DIFFERENCE.md)
already retained complete SoundCam electrical-loopback/microphone differences. The new port
returns that oriented evidence into the original temporal response chart. It does not yet contact
a compatible-condition fibre or commit developed acoustic standing.

## Declared return and ownership

[definition] For the retained causal action `p = X_x h`, a comparison on actual sampled support
`S` returns `e = y_S - R_S p`. In the declared unit-admittance complex chart, the response adjoint is

```text
g[k] = sum over j with j+k in S of conjugate(x[j]) e[j+k]
     = (R_S X_x)* e.
```

[definition] This is the adjoint of the restricted receiver. It contributes no covector outside
observed support; it does not assert that missing measurements equal zero. Both excluded support
populations remain in the comparison, and every original response coordinate remains in `g`,
including directions on which this receiver returns zero. The sample clock and phase chart are
exterior declarations, not semantic grains or measured physical admittances.

[established-bounded; implemented-exact] `phase_current::resident::return_response_resident`
borrows the actual `ResidentPhaseConvolution` and `ResidentPhaseDifference`. It checks that the
comparison retains this exact prediction section and view, including offset, denominator,
disposition, clock, support and lineage. Equal values or labels from another operation fail before
a launch. The returned receipt retains both prior owners and presents the current in the original
response chart. Later operations cannot substitute their current morphology for that forward cut.

[established-bounded; implemented-exact] `phase_current_response_adjoint.cuh`,
`phase_response_adjoint.metal` and `surface_phase_response_adjoint.rs` realize one resident passage:
validate both full point views and padding; accumulate independent response coordinates; normalize
the whole result; publish exact words. Each coordinate visits its admitted source indices in
ascending order. Both quadratures use checked products and sums, sharing the existing convolution
normalizer and packer. Intermediate workspace uses the actual target wide representation and
never crosses to a host numerical receiver. Failure publishes no response current and leaves the
forward and difference carriers intact.

## Controls

[established-bounded; measured] All 23 resident temporal controls pass on the M1 Pro, including
four new controls. The complex partial-support case returns `[19/21, -5/21, -13/21, -22/21]`
and independently verifies the realified duality pairing. A different equal-valued prediction
refuses before launch. A response wider than threadgroup storage preserves all inactive
directions. An overflowing exact return refuses while earlier prediction and observation remain
unchanged. The nineteen existing convolution/difference/conditional controls also pass.

```sh
cargo test -p holonic-engine --lib phase_current::resident:: -- --include-ignored --test-threads=1
```

## Actual recorded return

[established-bounded; measured] The v2 `recorded_acoustic_return` example builds and runs in
three separate processes on the same three 672,000-frame, 48 kHz SoundCam row/microphone-zero
pairs. Prediction precedes observation mounting; difference and response adjoint precede every
cold numerical readout. The explicitly declared initial response still has one unit coefficient.
No condition is updated, and each report states `generator_developed: false`.

[established-bounded; measured] The [source-qualified comparison](2026-09-07_recorded_acoustic_response_return/comparison.json)
verifies every original NPY/WAV sample, prediction, oriented difference and PCM projection,
and independently computes `sum x_pcm * (y_pcm - x_pcm) / 32768^2` using Python integers.
It checks both exact adjoint coordinates, original response receiver/clock/lineage and native
transfer receipts. All three v2 records pass; the earlier v1 row-zero record also passes the
updated observer. The three returned currents, with imaginary component zero, are:

| Source row | Exact real response current | Portable exact section |
|---|---|---|
| 000 | `-1812071716551 / 1073741824` | [88-byte return](2026-09-07_recorded_acoustic_response_return/row_000_response_return.section) |
| 001 | `-245483819625 / 134217728` | [88-byte return](2026-09-07_recorded_acoustic_response_return/row_001_response_return.section) |
| 002 | `-2318513610903 / 1073741824` | [88-byte return](2026-09-07_recorded_acoustic_response_return/row_002_response_return.section) |

[established-bounded; measured] Four [observer controls](2026-09-07_recorded_acoustic_response_return/observer-controls.json)
refuse a changed real coordinate, changed imaginary coordinate, claimed hot readout and changed
response clock. The coordinate mutations update their hashes, so refusal comes from the exact
pairing rather than a checksum mismatch. Source/waveform evidence and malformed controls remain
under `.local/experiments/soundcam-native-response-return`; only the small response sections and
qualified receipts are retained here. No recorded source was newly acquired or removed.

[established-bounded; measured] The actual M1 Pro costs are:

| Row | Response adjoint, s | Its GPU time, s | Three native stages, s | Cold audio export, s | Whole process, s |
|---|---:|---:|---:|---:|---:|
| [000](2026-09-07_recorded_acoustic_response_return/row_000.json) | 2.525432334 | 2.524221875 | 4.498711417 | 14.198790833 | 20.721956625 |
| [001](2026-09-07_recorded_acoustic_response_return/row_001.json) | 2.572221792 | 2.571502250 | 4.572976792 | 14.315708125 | 19.926262750 |
| [002](2026-09-07_recorded_acoustic_response_return/row_002.json) | 3.325763417 | 3.324773625 | 5.792473959 | 14.446995292 | 21.263021292 |

[established-bounded; measured] Each adjoint is one deed, six allocations and 64 receipt bytes,
with zero numerical egress, numerical readouts or ingress. Peak native residency is 139,776,340
bytes; 86,016,160 bytes remain held during cold publication. Cold response publication reads
48 numerical bytes and writes an 88-byte serialized section. CPU codec/RSS and disk are separate
from those residency counters. These are batch measurements, not a matched speedup, real-time
stream or measured power claim. CUDA is source-inspected here, not compiled or executed.
No Lean proofs or imports changed.

```sh
cargo build -p holonics-hna --example recorded_acoustic_return
target/debug/examples/recorded_acoustic_return .local/datasets/soundcam/wav/row_000/loopback.wav .local/datasets/soundcam/wav/row_000/microphone_00.wav NEW_REPORT.json .local/experiments/NEW_RETURN
python3 research/experiments/apple_silicon/compare_recorded_acoustic_return.py .local/datasets/soundcam/acquisition.json NEW_REPORT.json --output NEW_COMPARISON.json
```

## Remaining construction

[open; source-inspected] The adjoint supplies a concrete missing response port. The full temporal
family `F_y = {(h,e): R_S X_x h + e = y_S}`, its existing unit-admittance contact and persistent
successor remain to be implemented. An exact acoustic point port also cannot consume a numerical
enclosure centre as a selected current. The structured fibre and certified enclosure consumer
must preserve shared amplitude constraints, unmodelled return, actual normal currents and the
producing/current operator cuts. The [Apple blueprint](../../docs/plans/HOLONICS_ON_APPLE_SILICON.md)
retains that sequence. Useful acoustic/English development and AS4–AS5 completion remain open.
