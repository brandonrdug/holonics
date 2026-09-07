# Hardware and modality boundaries

[definition] This guide records the execution boundary, implemented Apple phase/field owners and acoustic attachments. It
describes source ownership; it does not schedule construction. The roadmap and `CONSTRUCTION_STATE.md` remain the construction authorities.

[definition] Brandon's subsequent MacBook request is now specified in
[Holonics on Apple silicon](plans/HOLONICS_ON_APPLE_SILICON.md). Its order is native Apple
execution and sound perception/generation, then speech, on the separate `codex/apple-silicon`
branch. The [Mac setup record](../research/records/2026-09-06_APPLE_SILICON_SPECIFICATION_AND_MAC_SETUP.md)
adds actual local build and MLX apparatus evidence to the source comparison below.

[established-bounded; source-inspected] Local sources were inspected at `6f547c4a` on September 6,
2026. Source descriptions below are not fresh execution measurements.

## Current common mechanism

[established-bounded; source-inspected] The public framework enters through
[`holonics::hna`](../crates/holonics/src/lib.rs). Its native session is exposed by
[`with_native_session`](NATIVE_HNA.md), while the earlier inherited operator retains a
separate adapter and artifact scope. Neither public adapter founds a second engine.

[definition] One native operation has the shape `occurrence -> local current -> reaction ->
emission + successor ecology -> next occurrence`. The successor returned by a successful deed is
the standing used by the next deed; a readout, application response, or codec output is an
ordinary next occurrence.

[established-bounded; source-inspected] The native transport scaffold retains addressed sections,
incidence, ordered generator words, and reconstruction fibres through
[`NativeTransportScaffold`](../crates/holonic-engine/src/native_spool/scaffold.rs). Its
non-owning `NativeAddressedSection` borrows those carriers from one scaffold rather than making a
second topology.

[established-bounded; source-inspected] The resident native owners are
[`ResidentNativeWord`](../crates/holonic-engine/src/cuda_refine/complex_parametron.rs) and
[`ResidentComplexIncidence`](../crates/holonic-engine/src/cuda_refine/complex_parametron.rs).
Their `mount` methods receive exact integer incidence or generator material; their `conduct`
methods receive an addressed population and return exact terminal sections plus apparatus census.

[established-bounded; source-inspected] The resident section owner binds the complete passage as
a CUDA graph, keeps intermediate sections on the card, carries refusal along declared lineage,
and reads one terminal census/face. Its contract and owner are
[`resident_section`](../crates/holonic-engine/src/resident_section.rs) and
[`ResidentSurface`](../crates/holonic-engine/src/resident_section.rs).

[definition] A portable execution seam must preserve the native carriers and successor contract
while replacing only the apparatus that mounts memory, schedules dependent operations, conducts
the hot law, synchronizes its declared boundary, and returns a typed receipt. A public interface
around one backend does not create portability.

## What is hardware-neutral

[definition] The following objects belong to the mathematical/native owner and survive a device
change: situated occurrence and caused incidence; local receiver charts; oriented current and
relative phase; complete preimage/reconstruction fibres; lineage and obstruction; move ownership;
atomic successor formation; and checkpoint chronology.

[definition] Counts, launch time, energy, transfer bytes, occupancy, memory pressure, and device
name are receiver/apparatus measurements. They can qualify a hardware realization, but they do
not identify a holon, choose a route, establish context, or replace the returned difference.

[established-bounded; source-inspected] The current resident complex path keeps the two current
coordinates together through contraction and states that the host neither selects phase nor
replays the product ([`ResidentComplexIncidence::conduct`](../crates/holonic-engine/src/cuda_refine/complex_parametron.rs)).

[established-bounded; source-inspected] The current device layer derives launch extents from the
mounted CUDA device and function attributes in [`CudaRefineExecutor::new`](../crates/holonic-engine/src/cuda_refine/cuda_executor.rs)
and [`mount::Device::launch_census`](../crates/holonic-mount/src/cuda.rs). A future backend must
report its own capability census rather than reuse CUDA warp or block constants.

## Native device boundary

[historical; process-audit] At `b16e6bc0`, the Mac HNA check failed at four unconditional generated
PTX includes and six target-gated launch/cover imports. The pre-port source comparison correctly
located a native dependency-closure obstruction, rather than an absent Rust installation.

[established-bounded; implemented-exact] The Apple phase port gates CUDA linkage, PTX consumers
and CUDA-only realizer search under Linux. `device_launch.rs` owns the common integer launch
admissions; `mount::metal` realizes resident allocation, serial command capture/replay and terminal
completion. `ResidentReadout` owns a Metal context for `ResidentSurface`; foreign embedding and
refine entry points refuse explicitly. No CPU current law or empty PTX substitutes for execution.

[established-bounded; measured] The public HNA library compiles on the M1 Pro. The existing 28
native phase and 15 public session tests pass against `accelerators/metal/native_phase.metal`.
These cover the current local rational-linear phase domain, not all native owners.

[established-bounded; implemented-exact] The subsequent
[complete field return](../research/records/2026-09-06_APPLE_ACOUSTIC_FIELDS_AND_HOLONIC_PROFILING.md)
adds Metal conduct/rechart for the desktop's `NativeConstitutiveField`, a public acoustic temporal
chart and borrowed structural profile. GPU command-buffer timestamps are apparatus observations.
This field retains its joint relation and historical source sections; each operation still reads
its terminal result. Learned acoustic grain, field rest/remount and sustained real-time conduct
are not established by this implementation.

[established-bounded; source-inspected] `DeviceBackend` and `ExactDeviceExecutor` in
[`device.rs`](../crates/holonic-engine/src/device.rs) provide a small exact parity vocabulary,
but only `CpuExactDevice` implements it. The native resident lifecycle does not currently use
this trait; `NativeTransportScaffold` constructs `CudaRefineExecutor` directly at
[`scaffold.rs`](../crates/holonic-engine/src/native_spool/scaffold.rs).

[open; source-inspected] Implementing `ExactDeviceExecutor` for another device would not by itself
port native HNA. The native mount, resident carrier, operation scheduling, multiword arithmetic,
and successor commit require their actual lifecycle owner; the phase path now uses the Metal mount.

## MLX as an architectural comparison

[established-bounded; source-inspected] MLX HEAD `ce916dbbcaa88e433b6fd1e60a17f766d49c27fe`, read
2026-09-06, documents an Apple-silicon array framework with unified CPU/GPU memory, dynamic lazy
graphs, and CPU/GPU operations selected by streams. See the [official README](https://github.com/ml-explore/mlx/blob/ce916dbbcaa88e433b6fd1e60a17f766d49c27fe/README.md),
[unified memory](https://github.com/ml-explore/mlx/blob/ce916dbbcaa88e433b6fd1e60a17f766d49c27fe/docs/src/usage/unified_memory.rst),
[lazy evaluation](https://github.com/ml-explore/mlx/blob/ce916dbbcaa88e433b6fd1e60a17f766d49c27fe/docs/src/usage/lazy_evaluation.rst),
and [streams](https://ml-explore.github.io/mlx/build/html/usage/using_streams.html). The README
also documents Linux CPU/CUDA packages; its array interface is separate from those device
implementations.

[established-bounded; source-inspected] MLX's documented unified-memory model lets CPU and GPU
operations address shared arrays without an explicit device move, while its scheduler inserts
dependencies between streams. Shared storage does not establish HNA identity, lineage, or a
semantic successor, and the absence of an explicit copy does not establish zero synchronization
or energy cost.

[interpretation] The first correspondence is `MLX array storage -> resident carrier`, `MLX stream
-> backend operation queue`, `MLX dependency edge -> declared predecessor relation`, and `mx.eval
-> apparatus completion/readout`. The preserved diagram is the native recurrence above. The first
derivation target is one exact native word conducted on two queues with the same successor. A
different successor, changed fibre, or missing dependency falsifies the correspondence.

[definition] An Apple backend may defer an operation graph as an apparatus schedule, but semantic
commit occurs only after the complete native operation has produced and validated its successor.
Implicit evaluation, array printing, or a host scalar branch cannot become a second learning law.

[established-bounded; source-inspected] MLX documents custom Metal kernels and backend-specific
`eval_cpu`/`eval_gpu` implementations in [custom extensions](https://ml-explore.github.io/mlx/build/html/dev/extensions.html).
That is a valid device implementation seam. Kernel signatures, shapes, and dtypes remain an
exterior apparatus contract; they do not author contextual topology.

[established-bounded; source-inspected] MLX documents integer, floating, and `complex64` dtypes,
with `float64` restricted to CPU operations, in its [data-type reference](https://ml-explore.github.io/mlx/build/html/python/data_types.html).
The documentation does not provide an arbitrary-precision rational or native `i128` carrier.

[established-bounded; implemented-exact] The phase port now uses checked sign/magnitude u32
limbs, exact rational contraction and reconstruction at the existing receiver boundary. Its
[measured return](../research/records/2026-09-06_APPLE_NATIVE_PHASE_AND_ACOUSTIC_COMPOSITION.md)
records the admitted signed-word mouth and bounded wide intermediates. Wider native families
still require their own representation and growth law. A float-array port may be a declared projection or export; it cannot silently become
the native current, topology, coefficient, or branch.

## Required backend mapping

[definition] Every future backend must map the following six boundaries without changing their
meaning:

| Native boundary | Current CUDA realization | Apple phase realization |
|---|---|---|
| Mount | device/context/module and resident buffers | Owned Metal context and shared buffers with checked ranges. |
| Exact carrier | signed words, wide intermediate, rational reconstruction | Checked four-u32 magnitude, sign and exact rational reconstruction. |
| Ownership | non-`Clone` resident organs and one move owner | Existing unique ecology; staged device deltas and immutable pipeline sharing. |
| Dependency | CUDA stream/events/graph edges | Ordered command queue and context-qualified captured dependencies. |
| Commit | device conduct, terminal synchronization, typed return | Terminal command completion and native status check before successor publication. |
| Apparatus receipt | launch, sync, transfer, residency, refusal census | Existing transfer census, actual Metal capabilities, working-set budget and process RSS. |

[definition] Intermediate native sections remain resident for the duration of one operation. Input
ingress, terminal readout, checkpoint I/O, and codec conversion may cross to the host or shared
memory at declared boundaries; host replay may not determine the committed native result.

[definition] Resource pressure changes lawful representation, factorization, placement, or returns
an obstruction. It does not justify deleting current, widening a magic aperture, or replacing a
failed exact operation with a float result.

## Audio and acoustics boundary

[established-bounded; source-inspected] The exterior source owner
[`ExactAcousticOccurrence`](../crates/holonic-life/src/mathematical_source/acoustic.rs) admits
mono signed 16-bit PCM WAV at a positive sample rate, retains every sample, and derives exact
frame/sample chronology. It performs no transcription and keeps the full PCM population beside
its folded section.

[established-bounded; source-inspected] The native acoustic owner
[`NativeAcousticProductionMorphology`](../crates/holonic-life/src/native_intelligence/membrane_acoustic.rs)
is founded from returned native outward-port currents. It retains ordered port incidence and two
quadrature coordinates; it does not retain a source waveform or template.

[definition] [`NativeAcousticReceiverChart`](../crates/holonic-life/src/native_intelligence/membrane_acoustic/potential_formation.rs)
declares `sample_rate`, order support/stride in receiver samples, and a bounded frequency chart in
Hz. Its logarithmic current center/width are one cold calibration of the declared receiver; they
are not Athena state, a universal loudness law, or an intrinsic physical measurement.

[established-bounded; source-inspected] `NativeAcousticPotentialComplex::found` places exact
quadrature currents into receiver-local time/frequency incidences and retains the complete
production fibre ([`potential_formation.rs`](../crates/holonic-life/src/native_intelligence/membrane_acoustic/potential_formation.rs)).

[established-bounded; source-inspected] `render_pcm16` is an explicit cold projection. It uses
`f64` trigonometric evaluation and signed-16 quantization, retains the native potential identity,
rejects clipping, and marks the result `cold_renderer_only`
([`render_pcm16`](../crates/holonic-life/src/native_intelligence/membrane_acoustic/potential_formation.rs)).

[definition] The first audio composition boundary is
`NativeAcousticRadiationInput::from_open_world_tube -> AcousticProductRest::radiate ->
NativeAcousticPotentialComplex::found -> render_pcm16`. Native current formation remains the hot
owner; PCM/WAV is a receiver and codec surface after the exact native return.

[open; source-inspected] `AcousticProductRest` embeds the earlier
`RecurrentGranularReturnedAffineEcologyRest`. It is not a wrapper for the current
`NativeConstitutiveEcology`; nor does the current phase session return a
`NativeOpenWorldTubeReceipt`. The Apple/acoustic specification therefore requires the actual
exterior-acoustic-to-native-material and native-outward-current attachments before claiming this composition
over the current ecology. Existing acoustic results retain their original body/receiver scope.

[project-postulate] Brandon's subsequent September 6 acoustic correction requires native holons,
not PCM sample ordinals, to organize acoustic material. WAV decoding and playback are exterior
charts; their coordinates do not prescribe native topology or operation frequency. The
[grain correction](../research/records/2026-09-06_ACOUSTIC_HOLONS_ARE_NOT_PCM_SAMPLE_STEPS.md)
locates phase, clock, occurrence and reconstruction owners without treating their older execution
bodies as an already integrated Apple acoustic learner.

[open] No current audio owner establishes calibrated microphone pressure, speaker pressure, power,
or room acoustics. Those claims require a physical chart with typed units, constitutive and
boundary laws, chronology, and calibrated receivers.

[definition] The comparison keeps hardware placement separate from the application's material
chart: an acoustic occurrence does not require a distinct learner, and an Apple device does not
change the meaning of a native occurrence or successor. Actual Apple/audio construction follows
the subsequent authorized work, using these existing owners.
