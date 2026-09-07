# Apple acoustic fields and holonic profiling

[definition] September 6, 2026, `codex/apple-silicon`. This implements the next shared field
construction under Brandon's instruction to proceed with the acoustic correction and profile for
real-time work. Desktop `673b8d42` was integrated as `20b3e9a3`; its native field law and its
[contextual obstruction](2026-09-06_AC1_THE_COMPLETE_MATERIAL_FIELD_RETAINS_ITS_CONTEXTUAL_OBSTRUCTION.md)
remain the base. This is not an AS4–AS5 completion or a new acoustic learning law.
The implemented source and measurement consumer are committed at `8122f777`.

## Native construction

[established-bounded; implemented-exact] The two desktop field kernels now run on Metal:
`section_constitutive_field` and `section_constitutive_field_rechart` in
`accelerators/metal/native_phase.metal`. The existing limb/rational helpers conduct independently
addressed input ports, both complex outgoing and held branches, the complete joint relation,
one-use source reception, and historical frame transport. The sole continuing memory/basis commit
follows successful arithmetic/conversion; rechart writes fresh staging. The CUDA source is unchanged.

[established-bounded; implemented-exact] `ResidentSurface::constitutive_field_scratch` accounts
for the target carrier: Metal's 20-byte `W`, aligned to 16 bytes, versus CUDA's 16-byte wide value.
Both founding and recording use that same calculation. Field rechart uses the existing target-aware
rechart scratch helper. The boundary regression conducts and recharts at the largest admitted
field, reaches the final receiver coordinate and refuses the next extent before native construction.

[established-bounded; implemented-exact] The public
`holonics_hna::native::acoustic_field::AcousticFieldChart` reuses `ExactPhaseCurrentSection` to
retain complete coefficients, source lineage, exact origin/step, cell support and structural padding.
One section cell enters the shared `NativeConstitutiveField` as a joint addressed field, with a
`4N` real source chart (outgoing plus held quadratures), `2N` receiving chart and their full relation.
The application no longer needs one scalar recurrence per coefficient to use this path. It advances
its source cursor only after success and restores the same receiving handle on refusal.

[definition] The coefficient aperture is still caller-declared. Grouping coefficients does not
establish learned holonic grain, and this adapter does not claim to do so. The substantive native
construction is the complete joint source/receiver relation and actual continuing field. The cold
WAV/PCM chart supplies neither topology nor a new current law; scattering against actual standing
produces current on the GPU. Exact source coefficients stay recoverable beside any receiver face.
Chronology alone supplies no receiving handle. No transcript/classifier/annotation authors contact.

## Structural and execution receivers

[established-bounded; implemented-exact] `NativeConstitutiveField::intrinsic_profile()` in
`field/profile.rs` borrows material, actual source lineages, predecessor positions, current and
historical frames, rechart and incidence changes, and pending state. Its explicit extents are chart
extents. Dimensions not exposed by this profile have a typed open face rather than a port/history
count masquerading as rank or generator population. The reconstruction extent counts retained
source sections; it is not a scalar replacement for their contents. Profile construction issues
no source handles, clones no ecology and performs no device readback.

[established-bounded; implemented-exact] The `acoustic_field_profile` consumer measures complete
recordings through one move-owned field. `TransferCensus` separates ingress, terminal section and
receipt egress, allocations, graph launches and retained device bytes. The printed first and last
field returns retain outgoing/held currents and source timing. The current public field API reads
its terminal result after **every** operation (`16N + 9` interval words), including in status mode;
only the paired relation basis avoids that readback. Full intermediate native source sections also
remain with the owner. Zero extra readouts from the borrowed profile therefore does not mean a
readout-free loop. Loop timing includes chart delivery, native conduct, terminal
readout and boundary observation; mount and WAV decoding/chart construction are reported separately.

[established-bounded; source-inspected] The installed Apple SDK's `MTLCommandBuffer.h` defines
`GPUStartTime` and `GPUEndTime` as host seconds at GPU execution boundaries, with zero denoting
unavailable timestamps. The Metal mount now accumulates these after normal command completion;
the getter neither waits nor reads native state. Floating-point seconds are an exterior apparatus
receiver only. These spans include the complete command buffer, including the terminal census;
they do not individually attribute rational arithmetic, memory traffic and command overhead.

## Recorded execution

[definition] Both measured layouts use declared matched unit-admittance material with unit incoming
phase and zero initial held state. Each starts one field, processes the complete ESC-50 dog WAV
`1-100032-A-0.wav` (220,500 samples, 44.1 kHz), then the complete LibriSpeech English WAV
`2277-149896-0000.wav` (105,440 samples, 16 kHz), retaining its successor between recordings.
No handles are inferred from audio adjacency; these are unlinked field-conduct measurements,
not corpus cultivation or useful acoustic production. Dataset provenance and licenses remain in
the [acoustic guide](../../docs/ACOUSTIC_EXPERIMENTS.md) and original local acquisition receipts.

[established-bounded; measured] The first release sweep, with no simultaneous compilation,
returned the following loop times. These layouts have different declared field relations; they
are not identical models with only a scheduler changed. The old scalar/debug measurements do
not supply a matched speedup baseline.

| Declared ports | 5 s sound: wall seconds | 6.59 s English: wall seconds | Retained native bytes after both |
|---|---:|---:|---:|
| 16 | 17.456696 | 11.305524 | 86,527,552 |
| 32 | 14.731893 | 10.217732 | 85,505,952 |

[established-bounded; measured] Both layouts completed every source coefficient, including zeros.
The borrowed profile added zero section readouts. Doubling the aperture halved the operation
population but did not halve elapsed time. This observation does not isolate the device cost;
the subsequent timestamped run supplies that receiver separately.

[established-bounded; measured] The matched timestamped runs at 32 ports returned:

| Input | Before: wall / GPU seconds | After exact fast paths: wall / GPU seconds | After: wall / source duration |
|---|---:|---:|---:|
| 5 s sound | 15.073592 / 13.186661 | 12.350281 / 10.571535 | 2.4701 |
| 6.59 s English | 10.258986 / 9.335093 | 7.792539 / 6.692136 | 1.1825 |

[established-bounded; measured] Wall throughput improved by 1.22× and 1.32× respectively in
these two individual runs. GPU spans account for about 86% of the optimized wall times. Both
recordings completed; source coefficients, first/last outgoing and held currents, lineage,
receiver classifications, rank faces, chart/profile faces and complete reported transfer censuses
matched the baseline exactly. This comparison does not claim to inspect every intermediate
history section. The independent native regressions cover their stated complete-return cases.
Raw receipts, seeds, a baseline-reproduction patch and the comparison are retained
[beside this record](2026-09-06_acoustic_field_profile/README.md).

[established-bounded; measured] Sound field latency was 1.758 ms median, 2.151 ms p95 and
7.743 ms maximum, against 0.726 ms of source time per 32 coefficients. English was 2.195 ms
median, 3.509 ms p95 and 43.944 ms maximum, against 2 ms of source time per field. The English
p95 did not improve over the baseline's 3.242 ms. Single-run throughput improvement therefore
does not establish a tail-latency improvement or a streaming deadline guarantee. Mount and
decode/chart work are outside these loop times and retained separately in the receipts.

[established-bounded; measured] The continuing owner retained 85,505,952 native bytes after
the two recordings, with 10,186 terminal section reads and the same number of synchronizations.
The arithmetic change did not reduce those populations or storage. These are execution probes
over declared fixed material, not recognition, synthesis, conversational accuracy or corpus learning.

[established-bounded; source-inspected] The field and rechart kernels currently admit only thread
zero to their arithmetic. Independently addressed ports thus still execute serially inside the
one joint field operation. The measured GPU dominance makes device arithmetic/layout and lawful
staged parallel execution pertinent next investigations. Host packet batching alone cannot remove
the dominant measured span. Retained source history and terminal delivery also need explicit
placement/receiver constructions before this path can support a sustained stream.

## Verification and remaining composition

[established-bounded; measured] All 42 constitutive engine tests passed with
`MTL_DEBUG_LAYER=1`, including the 28 scalar-family regressions, 11 existing field controls,
the new full-aperture field/rechart test, the no-readback/source-handle profile test and the typed
profile test. All three acoustic chart tests passed with Metal validation enabled. Six Metal
mount tests passed after adding command timing, including unchanged output/order and absence of
double-counting at a second synchronization. The timestamp test initially forgot the separate
allocation-fill command; its assertion now compares against the actual prior counter.

[established-bounded; implemented-exact, measured] The carrier now specializes complete single-limb
magnitudes for exact multiplication/division, retaining the existing wider fallback and overflow
refusal. Rational normalization stops once the GCD is one and avoids divisions by one. This changes
neither the declared field nor its arithmetic. The Metal arithmetic probe passed 248 deterministic
Python-integer oracle cases, retaining the original 100 wide cases and adding small-magnitude and
32-/64-bit boundary cases. The 42 engine and three acoustic tests above passed again after these
changes. No Lean source, CUDA kernel law or native floating-point law changed.

[open] The shared field is not yet a contextual acoustic morphology. Source-qualified temporal
sections must participate in the same contextual/formation construction as the linguistic work;
the desktop's equal-field/different-history obstruction remains relevant. Productive acoustic
emissions need their actual temporal support and receiver passage, rather than a fixed sonification
being declared learned sound. The field has no rest/remount product in this return. Sustained
streaming also needs lawful placement/condensation of retained source history and measured latency
under the resulting operation. No microphone input is required for any of these constructions.

## Desktop composition boundary

[established-bounded; source-inspected] Both devices now share `NativeConstitutiveField`,
`NativeFieldOccurrence` and its one-use `NativeFieldEmission`, including full source/receiver
relations and historical frames. The acoustic adapter returns `AcousticFieldSupport` beside that
same native return. `NativeFieldOccurrence` currently accepts coefficients and an actual receiving
handle; it does not accept the acoustic clock/support as an operative temporal generator. The
clock stays in `ExactPhaseCurrentSection` and the exterior support return. This is the concrete
remaining temporal attachment boundary, not a missing PCM codec or microphone sample.

[open] The next acoustic/linguistic composition must retain those source-qualified temporal
sections while constructing the shared contextual receiver/formation relation. Recorded response
annotations may declare their actual interaction scope; equal time, equal field values or an
annotation label cannot supply native contextual identity. Productive emission must return an
actual temporal passage. The separate fixed sound renderer and a transcript fed after a WAV do
not discharge either construction.

[definition] No recorded source, cache or user file was removed. Changes belong to the Apple branch;
the desktop private conversation material and `main` were not modified or messaged.
