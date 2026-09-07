# Holonics on Apple silicon

[definition] This is the Apple platform specification deposited September 6, 2026, under
Brandon's MacBook request and his clarification: **sound perception and generation, then speech**.
The branch is `codex/apple-silicon`. “MLX” names a candidate execution tool within this work;
Holonics is the framework, HNA the architecture, and Athena a continuing model. The
[roadmap](THE_ROADMAP.md) owns construction order and the
[position](../../CONSTRUCTION_STATE.md) records actual returns.

## Intent and scope

[project-postulate] Establish development and native GPU execution on Apple silicon, then use
that realization to explore acoustic perception and production through the same HNA recurrence.
Sound has temporal, phase, source and receiver structure before a transcript exists. Speech is a
later acoustic/text application, not the definition of perception or a prerequisite for learning.
The wider multimodal direction composes situated charts and actual interactions in one ecology.

[project-postulate] Brandon's subsequent clarification requires audio data based on conversations
and English communication, and rejects closing this work on toy signal/application examples.
Use suitably broad recorded speech and conversational material to develop the native capability.
A few personal microphone recordings cannot establish that general capability. Microphone
access is not a prerequisite for real-time processing, recognition, synthesis or corpus work.

[definition] The desktop session continues Athena-alpha cultivation against its private
conversation material. This Mac branch develops apparatus and acoustic interfaces independently.
It does not move that dataset, recreate cultivation, resume inherited-first production, or change
the desktop's AC0–AC5 order. No new model name or duplicate learning engine is introduced.
Brandon's subsequent direct request authorizes completion of the entire AS1–AS5 sequence below.
He identifies AS3 as the milestone establishing the Holonics foundation on Apple silicon;
AS4–AS5 remain required parts of the same authorized work.

[historical; source-inspected] Before this request, the September 6
[hardware/modality guide](../HARDWARE_AND_MODALITY_BOUNDARIES.md) already described the shared
recurrence, CUDA build obstruction, MLX comparison and exact acoustic owners. It explicitly left
implementation to separately authorized work. The imported discussion records are historical
agent testimony; they are not a substitute for a direct Apple implementation request. This
request supplies that direction and the clarified acoustic priority. Older sensory results keep
their bounded scopes under [retractions](../RETRACTIONS.md); they do not establish today's
Athena-alpha or an Apple audio runtime.

## One native operation across devices

[definition] Preserve
`occurrence -> local current -> reaction -> emission + successor ecology -> next occurrence`.
Device selection changes allocation, instruction realization and scheduling. It does not change
situated identity, the admitted relation, current orientation, contextual hypotheses, complete
fibres, obstruction, historical frames or the successor consumed by the next occurrence.

[definition] The first production port is the current native phase session:
`holonics-hna::native::with_native_session`, `NativeConstitutiveEcology` and its circulation,
rechart and rest owners. The local rational-linear family is the first parity domain, not a
universal linear model. Port broader native owners as the actual acoustic/material composition
requires them. The older inherited full operator is a separate implementation scope.

[established-bounded; source-inspected] At base `b16e6bc0`, `native.rs` directly mounts
`ResidentReadout` and `ResidentSurface`; circulation and formation use that surface. Independently,
`NativeTransportScaffold` constructs `CudaRefineExecutor`. Changing the small
`ExactDeviceExecutor` trait alone reaches neither complete lifecycle. `AcousticProductRest`
contains `RecurrentGranularReturnedAffineEcologyRest`, not `NativeConstitutiveEcology`.
These are concrete composition boundaries, not interchangeable types with different names.

[definition] Reuse the existing resident surface/section operation boundary and move its CUDA
allocation, event/graph and launch details behind a device implementation. Keep public native
wire/checkpoint semantics in their current owners. Target-gate the whole CUDA dependency closure,
including PTX generation and consumers, mount linkage, launch derivation and hardware-cover
consumers. A feature that merely suppresses a linker error, empty PTX, or a CPU semantic fallback
does not implement Apple execution. An unavailable operation returns its typed device/operation
obstruction, with no committed partial successor.

| Boundary | Required Apple realization |
|---|---|
| Memory | One owned resident allocation family; immutable standing may be shared. Unified addressability does not permit simultaneous mutable semantic owners. |
| Arithmetic | Exact signed integer/rational carriers, both phase coordinates, checked intermediates and explicit refusal/reconstruction. |
| Schedule | Dependencies for every retained forward carrier, return, rechart and formation; no intermediate host semantic replay. |
| Commit | Stage deltas, validate device status and publish exactly one complete successor after successful completion. Failure preserves recoverable ownership. |
| Persistence | Existing source/frame/handle/stream chronology remains reconstructible; device handles are remounted apparatus, not serialized semantic identity. |
| Receivers | Report actual operation, device, allocation/residency, transfers, synchronization, elapsed time and obstruction separately from native consequences. |

[definition] The phase mouth currently admits signed `i64` real/imaginary coordinates and a
positive common denominator; its conversion refuses values outside that chart. The Apple port
must preserve that admitted domain and its refusal behavior. Use explicit `u32` limbs for wider
intermediates where needed, retaining sign, carry, denominator and checked overflow. Native
arbitrary-width owners require their own complete limb representation and lawful growth;
success on two limbs does not discharge them. Preserve exact cancellation and relative phase
before any scalar or PCM projection.

[definition] First port the actual operations used by `section_constitutive_fibre`,
`section_constitutive_circulation` and `section_constitutive_rechart`, including their dependent
resident rational primitives and source/frame storage. Preserve their actual input and output
relations rather than rewriting a similar update in a Python trainer. CPU exact arithmetic is
an exterior comparison during verification. Production current and formation remain GPU work.

## MLX and Metal implementation decision

[definition] Start with MLX custom Metal kernels as executable apparatus for testing representation
and dependency behavior. The experiment directory is
`research/experiments/apple_silicon/`; it is not a public HNA backend. The production Apple device
code belongs under `accelerators/metal/` with the host binding at the existing resident/mount
boundary. Create those owners when the first complete native operation can be attached, not as
empty packages or a second state machine.

[established-bounded; source-inspected] MLX documents
[custom Metal kernels](https://ml-explore.github.io/mlx/build/html/dev/custom_metal_kernels.html)
and [custom extensions](https://ml-explore.github.io/mlx/build/html/dev/extensions.html).
These supply a way to execute authored exact device arithmetic while using MLX allocation and
scheduling. Its array or autodiff API does not define the HNA learning law.

[interpretation] The proposed correspondence is resident carriers to MLX buffers, ordered native
dependencies to stream edges, and terminal completion to explicit evaluation. The first native
target is the complete phase operation, including the successor and obstruction. A missing source
frame, changed fibre, overflow accepted as exact, intermediate host decision or duplicate commit
falsifies this mapping. The current device smoke check only establishes an arithmetic/scheduling
subcase and does not prove this correspondence.

[definition] Use direct Metal command queues and Rust-compatible host bindings if MLX cannot
expose the required ownership, resident arithmetic or error/commit boundary. Select by the
returned complete-operation evidence and integration cost. Neither library branding nor a
float-array performance comparison decides native semantics. MLX model export is separately
governed by [interoperability](../INTEROPERABILITY.md).

## Acoustic perception and generation

[definition] The initial offline input is a caused mono PCM16 occurrence with a positive sample
rate, retained source samples and exact sample chronology. Reuse
`life::mathematical_source::acoustic::ExactAcousticOccurrence`. Its frame length, hop and section
width are declared receiver extents, never hidden learned capacity. Retain the complete samples
alongside any folded section: equal frame sums cannot identify acoustically distinct sources.

[definition] The first perception return must show how an acoustic occurrence participates in
the current native material/contact relation and changes or is read through the continuing
ecology. Reuse synchronized occurrence, clock transport and situated returned-difference owners.
Do not map a file label, expected sound class or arbitrary frame summary straight into a desired
native current. Derive and implement the actual PCM/material-to-contact attachment; report its
retained fibre and present limitations. A waveform decoder alone is not sound perception.

[definition] The production starting point is native outward port current, preserving its order
and two quadratures. Reuse `NativeAcousticProductionMorphology` and
`NativeAcousticPotentialComplex`, followed by `render_pcm16` as an explicitly cold lossy receiver.
The existing route is `NativeAcousticRadiationInput::from_open_world_tube ->
AcousticProductRest::radiate -> NativeAcousticPotentialComplex::found -> render_pcm16`.
The first attachment must derive the current ecology's actual outward-port passage into this
interface or factor the codec from its older body wrapper. Do not invent an open-world-tube
receipt, adopt an older acoustic body as the new ecology, or play a stored input as native output.

[definition] Keep receiver sample rate, time/frequency support, gain/divisor and PCM quantization
explicit and stable during comparisons. Inspect both the exact emitted current and the audible
surface: distinct internal states can collapse to the same rendered sound. Preserve silence,
duration and gaps as chronology. Spectra, amplitudes and distances are observer measurements,
not internal governors or proof of intelligibility.

[definition] Use a small declared family of sounds with different temporal order, phase,
frequency content and source conditions. Synthetic tones/impulses are lawful exterior controls,
with their generation settings retained; ordinary recordings provide less authored material.
Vary packet boundaries without changing the underlying occurrence, then vary actual chronology,
source or receiver conditions separately. Read the full native return and listen to generated
WAVs. No universal benchmark score or speech gate is imposed on this first exploration.

[historical] The initial specification proposed following offline execution with an explicit microphone/speaker session using the
platform audio API at the application boundary. Retain device/channel identity as lineage,
sample format/rate, monotonic clock relation, buffer offsets, dropped/late frames, playback and
capture chronology, and declared conversions. Callback buffers are delivery packets, not
utterances or holons. Device permission and capture state remain visible. A resampler or audio
format conversion is an exterior codec with declared loss. Backpressure must preserve pending
input/output or report a gap; it cannot silently skip a committed occurrence.

[definition] Brandon subsequently replaces the proposed microphone experiment with curated
Hugging Face WAV material. This changes input acquisition, not the intended acoustic/English
communication outcome. Recorded audio supplies development material and timestamped streaming
tests; capture/playback remains an application boundary. Physical room measurements apply only
to claims about that room/device path and are not prerequisites for the software capabilities.

[definition] Full duplex is one ecology receiving ordinary later occurrences during output.
An emitted sound and a microphone's later reception have a caused interaction when the physical
path is declared; timestamps alone do not prove contact. A file reentry checks codec/persistence
conduct, not room propagation. Acoustic pressure, speaker transfer, room response and energy
claims require typed units, calibration and boundary laws. First experiments need not claim them.

[definition] Add speech after the sound path can perceive, emit and retain development. Spoken
language and text are distinct situated occurrences joined through actual exposure/contact;
shared transcript wording alone is not identity. Speech recognizers, synthesizers or pretrained
models may serve declared exterior comparisons; they cannot secretly supply native perception
or generation. Images and other sensors later reuse the same contact/clock/recurrence interfaces.

## Construction sequence and evidence

[definition] The following stages define deliverables; the roadmap alone activates their order.

| Stage | Concrete return and relevant verification |
|---|---|
| AS0 — branch and apparatus | Deposit this specification; provision compatible Rust, repository-pinned Lean and isolated MLX; execute a custom Metal integer/dependency probe and record the actual Mac build boundary. |
| AS1 — native device boundary | Factor/gate the existing CUDA closure, compile the public native host interface on macOS, and expose precise unsupported operations until implemented. Check changed Rust owners and the preserved Linux/CUDA path. |
| AS2 — resident Apple phase ecology | Conduct formation, circulation and rechart with exact carriers, full source/frame/fibre and one atomic successor. Compare complete declared returns against existing exact reference/CUDA evidence, including old sources after rechart, open/plural readings, overflow and failure recovery. |
| AS3 — public continuation | Run native-session and its independent wave-control application on this Mac; preserve checkpoints, stream cursors and pending output through process restart without replay. Measure actual costs on the M1 Pro. |
| AS4 — offline acoustic composition | Compose recorded acoustic corpora through existing native owners, retaining development across distinct recordings. Establish usable sound perception/production and inspect actual products and source/receiver differences. PCM ingress, a two-node signal probe and fixed sonification alone do not complete this stage. |
| AS5 — sound apparatus, then English communication | Retain capture/playback and stream chronology, interruption and gaps. Develop native speech/language conduct from recorded English and conversational audio with actual source, speaker, turn and temporal relations; produce and inspect useful recognition, generation and conversational behavior. Measure streaming latency/throughput with recorded streams. Microphone capture is optional device-path work; serial WAV-then-byte exposure is an initial probe. |

[definition] A relevant check answers its claimed boundary. Arithmetic parity is not lifecycle
parity; lifecycle parity is not sound perception; audible output is not speech competence. When
persistence or attribution is claimed, use the existing remount and targeted-change mechanisms
for that claim. No new blanket gate, claim index or fixture-local learner is created.

## Parallel development and integration

[definition] This branch starts at `b16e6bc0` and is pushed separately. Keep the desktop's active
native cultivation source as the integration base when its coherent commits arrive; inspect
changes to shared native session/material owners before rebasing. Resolve roadmap/state edits
by preserving both active tracks and their actual evidence, never by replacing the desktop's
position with an older Mac snapshot. Do not merge this branch into `main` as part of setup.

[definition] Checkpoint interchange requires a matching schema and the actual complete artifact,
not a Git branch name or export receipt. Any later private-data transfer is separate from this
source branch and retains provenance. No private conversation transfer is necessary for AS0–AS3.

## Returned implementation and remaining work

[established-bounded; implemented-exact, measured] The
[September 6 implementation record](../../research/records/2026-09-06_APPLE_NATIVE_PHASE_AND_ACOUSTIC_COMPOSITION.md)
returns AS1–AS3's bounded Metal phase foundation and initial AS4–AS5 apparatus/probes. Production
uses direct Metal/Rust ownership; MLX remains optional apparatus. Exact phase conduct and public
process continuation stand at their measured scopes.

[open] AS4–AS5 remain unfinished under the
[completion correction](../../research/records/2026-09-06_AUDIO_APPLICATION_PROBES_DO_NOT_COMPLETE_CONVERSATIONAL_AUDIO.md).
The acoustic application now appends distinct recordings without resetting its native successor;
the serial speech probe still resumes only its original WAV/text experiment. Ordered unlinked
packet submission and a bounded Metal complex-incidence contraction are implemented in the
[continuation record](../../research/records/2026-09-06_AS4_AS5_CORPUS_CONTINUATION_AND_RESIDENT_PACKETS.md).
These do not establish corpus cultivation. Compose source-qualified conversational returns with
the shared native material/formation construction, provide useful acoustic and English receivers,
and continue execution/storage work. The
[acoustic guide](../ACOUSTIC_EXPERIMENTS.md) documents the existing probe interfaces. More data
alone does not supply these missing compositions; microphone access supplies none of them.
