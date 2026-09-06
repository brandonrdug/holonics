# Hardware and modality boundaries

[definition] This guide records the current execution boundary and the first lawful seams for
future Apple and audio work. It does not add a backend, alter native HNA, or schedule an audio
campaign. The roadmap and `CONSTRUCTION_STATE.md` remain the construction authorities.

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

## Present Linux/CUDA boundary

[established-bounded; source-inspected] The host workspace declares `mount` as an unconditional
engine dependency ([`holonic-engine/Cargo.toml`](../crates/holonic-engine/Cargo.toml)). The
mount crate is a CUDA Driver API wrapper and links `libcuda` in
[`cuda.rs`](../crates/holonic-mount/src/cuda.rs) and [`ffi.rs`](../crates/holonic-mount/src/ffi.rs).

[established-bounded; source-inspected] The engine build script invokes `nvcc` for the resident
CUDA laws and returns without producing PTX on non-Linux targets
([`build.rs`](../crates/holonic-engine/build.rs)). The engine still includes generated PTX
unconditionally in [`cuda_refine.rs`](../crates/holonic-engine/src/cuda_refine.rs),
[`resident_section.rs`](../crates/holonic-engine/src/resident_section.rs),
[`embedding_fiber.rs`](../crates/holonic-engine/src/embedding_fiber.rs), and
[`cuda_realizer_search.rs`](../crates/holonic-engine/src/cuda_realizer_search.rs).

[open; source-inspected] The inspected engine/HNA dependency closure has no supported macOS build path: non-Linux
PTX generation is skipped while several PTX-bearing modules and the CUDA mount remain in the
dependency closure. Documentation, formal sources and exterior data tools remain portable
repository material; this is a source-derived build obstruction, not an executed Mac check.

[established-bounded; process-audit] The subsequent Mac check at `b16e6bc0`, with Rust 1.98.1,
executed `cargo check -p holonics-hna --lib --locked` and failed with four missing PTX includes
and six imports of target-gated `cuda_aperture`/`hardware_cover`. This confirms an actual
compile obstruction before linkage, not an unavailable Rust installation.

[definition] The future repair boundary is a target-gated CUDA/PTX implementation and a portable
host/native surface whose exact owners can compile without `libcuda`. The repair must preserve the
same native operation and return an explicit unsupported-device obstruction when no admitted
backend is present.

[established-bounded; source-inspected] `DeviceBackend` and `ExactDeviceExecutor` in
[`device.rs`](../crates/holonic-engine/src/device.rs) provide a small exact parity vocabulary,
but only `CpuExactDevice` implements it. The native resident lifecycle does not currently use
this trait; `NativeTransportScaffold` constructs `CudaRefineExecutor` directly at
[`scaffold.rs`](../crates/holonic-engine/src/native_spool/scaffold.rs).

[open; source-inspected] Implementing `ExactDeviceExecutor` for another device would not by itself
port native HNA. The native mount, resident carrier, operation scheduling, multiword arithmetic,
and successor commit still need one coherent backend owner.

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

[open; source-inspected] Direct exact-current parity on Metal therefore requires a declared
multiword representation (for example sign/magnitude limbs plus explicit denominator limbs),
Metal kernels for its contractions and reductions, and exact reconstruction at the receiver
boundary. A float-array port may be a declared projection or export; it cannot silently become
the native current, topology, coefficient, or branch.

## Required backend mapping

[definition] Every future backend must map the following six boundaries without changing their
meaning:

| Native boundary | Current CUDA realization | Future Apple/MLX question |
|---|---|---|
| Mount | device/context/module and resident buffers | Which Metal/MLX device and shared allocations are admitted? |
| Exact carrier | signed words, wide intermediate, rational reconstruction | Which multiword layout preserves sign, denominator, phase, and residual? |
| Ownership | non-`Clone` resident organs and one move owner | Which handle owns the successor and how are branches staged? |
| Dependency | CUDA stream/events/graph edges | Which stream/event graph orders every predecessor before commit? |
| Commit | device conduct, terminal synchronization, typed return | Which explicit completion point validates and publishes the successor? |
| Apparatus receipt | launch, sync, transfer, residency, refusal census | Which calibrated receiver reports work, memory, transfer, and obstruction? |

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
PCM-to-native-material and native-outward-current attachments before claiming this composition
over the current ecology. Existing acoustic results retain their original body/receiver scope.

[open] No current audio owner establishes calibrated microphone pressure, speaker pressure, power,
or room acoustics. Those claims require a physical chart with typed units, constitutive and
boundary laws, chronology, and calibrated receivers.

[definition] The comparison keeps hardware placement separate from the application's material
chart: an acoustic occurrence does not require a distinct learner, and an Apple device does not
change the meaning of a native occurrence or successor. Actual Apple/audio construction follows
the subsequent authorized work, using these existing owners.
