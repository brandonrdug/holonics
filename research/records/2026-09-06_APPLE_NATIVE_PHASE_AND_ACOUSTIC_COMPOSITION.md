# Apple native phase and acoustic composition

[definition] This record follows Brandon's September 6 request to complete AS1–AS5 in
`docs/plans/HOLONICS_ON_APPLE_SILICON.md`, with AS3 the Apple foundation milestone. His later
direct instruction substitutes curated Hugging Face WAV material for the proposed microphone
recording. The branch is `codex/apple-silicon`, following setup commit `2329a539`; the implementation
revision is the commit containing this record. The desktop Athena-alpha position is independent.

[historical] Completion status corrected after Brandon's follow-up: AS1–AS3's bounded phase
foundation stands; AS4–AS5 are partial apparatus/application probes and do not complete the
intended conversational audio work. See the
[correction](2026-09-06_AUDIO_APPLICATION_PROBES_DO_NOT_COMPLETE_CONVERSATIONAL_AUDIO.md).
The source and measurements below retain their actual scopes. Microphone access is not a
prerequisite for the remaining corpus, streaming, recognition or synthesis work.

## Device and exact native operation

[established-bounded; implemented-exact] The current public phase session runs on the M1 Pro GPU
through direct Metal. `holonic-mount::metal` owns shared resident allocations, ordered command
buffers, captured dependencies and completion. The existing `ResidentSurface` dispatches
`accelerators/metal/native_phase.metal` for fibre formation, circulation, rechart, carry and census.
The existing native ecology and public session still own source/frame history, obstruction and
the successor. MLX remains installed experiment apparatus; no second MLX learning loop was added.

[definition] The admitted native mouth is unchanged: signed i64 coordinates and a positive
common denominator. Device intermediates use checked signed magnitudes in four u32 limbs, with
magnitude at most 2^127−1. Every phase coordinate and complete staged successor remains present.
Out-of-chart arithmetic refuses before commit. One scalar Metal thread executes the dependent
operation; serial command order is a dependency realization, not an independence claim.

[established-bounded; measured] On macOS 26.5 / Xcode 26.6, Rust 1.98.1, Apple M1 Pro (8 CPU,
14 GPU cores, 16 GiB unified memory), all 28 existing engine phase tests passed after the final
limb multiplication/division optimization, with Metal API validation enabled (4.08 s test time).
These include exact reference comparisons, open/plural fibres, source-qualified formation,
earlier-source recharting, full rest/remount and atomic arithmetic refusal. An independent Python
integer oracle and freshly compiled Metal probe also agreed on 100 bounded wide arithmetic
cases and signed-minimum/overflow boundaries. These are finite comparisons in the stated domain.

[established-bounded; measured] Six mount tests exercised ordered copy/fill capture, aborted
capture recovery, cross-context and overlapping-copy refusals, unsupported typed operations and
repeated allocation/command release with Metal API validation. The allocation receiver returned
to within 4 KiB of its baseline. Command submission and compiler temporary objects use explicit
autorelease pools; immutable pipelines are cached, while each continuing ecology stays uniquely
owned. Reported Metal memory is a working-set recommendation and tracked allocation use, not
physical free VRAM or a measured energy budget.

[established-bounded; source-inspected] CUDA linkage, generated PTX consumers and CUDA-only
realizer search are gated under Linux. Shared integer launch admission moved to `device_launch.rs`,
with its old public CUDA re-export preserved. The Mac `ResidentReadout` owns the Metal context;
unported foreign embedding/refinement operations return an explicit unsupported-device result.
No CPU native semantic fallback or empty PTX implementation was installed.

[open] Linux/CUDA execution has not been rerun on this Mac. Source preservation and successful
macOS compilation do not supply a new Linux runtime receipt. Broader inherited operator kernels,
CUDA virtual-memory facilities and arbitrary-width native families remain outside this phase port.

## Public continuation and cost receiver

[established-bounded; measured] The existing 15 public native-session tests and four separate
process continuation tests passed on Metal. These cover complete stream/model persistence,
pending stdout delivery, input cuts, an independent wave world with actuation, and refused pending
wave input. Remount uses the saved successor; completed native effects are not replayed.

[definition] Actual Apple cost measurements use the existing `native_resources` example in the
debug profile, with retained source counts 1, 64, 1,024 and 4,096 and 16 warm operations per case.
macOS process RSS comes from `ps`; unavailable GPU-isolated and high-water measurements remain
null. This receiver does not establish power, general scaling, or release-profile parity with the
desktop's previously measured CUDA times.

[established-bounded; measured] The cost run completed in 5.89 s wall time. Every warm open
operation reported one native deed, one terminal section readout, 48 ingress bytes, 400 section
and 64 receipt egress bytes, six allocations and one synchronization. Retained intermediate
carriers stayed resident. All four remounts reported zero replayed native deeds and retained
source zero, whose later actual contact formed a unique receiver.

| Earlier unlinked sources | Warm open median | Warm formed median | Checkpoint bytes | Remount entry | Mounted process RSS |
|---|---:|---:|---:|---:|---:|
| 1 | 0.503 ms | 0.537 ms | 12,418 | 1.204 ms | 19,680 KiB |
| 64 | 0.458 ms | 0.527 ms | 51,919 | 1.607 ms | 20,352 KiB |
| 1,024 | 0.553 ms | 1.996 ms | 656,777 | 9.963 ms | 22,800 KiB |
| 4,096 | 0.588 ms | 1.020 ms | 2,601,353 | 40.423 ms | 31,792 KiB |

[definition] These are one run's medians, not throughput guarantees. Formed timings varied;
only the measured operation census was invariant across these retained extents. The complete
receiver JSON is retained with this record; local native checkpoints remain outside Git.

## Acoustic attachment and curated source

[established-bounded; implemented-exact] `holonics-hna::native::AcousticApplication` retains the
original WAV, complete exact PCM occurrence, source clock, next sample, pending return and native
checkpoint. Its declared digital chart maps sample s to (s / divisor, 0). An optional declared
one-sample digital world return uses the actual preceding root emissions and actual source
handle. The GPU performs the resulting native reaction and relation formation. No category,
transcript, frame sum or desired answer supplies the native result.

[established-bounded; measured] Four acoustic GPU tests passed with Metal API validation: split
versus whole execution, malformed chart refusal before effects, a zero-sample checkpoint followed
by byte-identical complete continuation, and first-sample arithmetic refusal preserved identically
through remount and retry. Silence remains an occurrence. The first 4,096-sample ESC-50 prefix
was entirely zero-valued source material and remained silent; calibrating a receiver from that
all-zero emission correctly refused. This prefix is persistence/silence evidence, not evidence
of discrimination between audible sounds.

[established-bounded; implemented-exact] `NativeAcousticProductionMorphology::found_phase_session`
factors the existing acoustic production codec from its older ecology wrapper. It receives only
actual ordered root-port emissions, retains both quadratures and silent ports, and refuses gaps
or incomplete port populations. It does not fabricate an open-world-tube receipt. The existing
potential complex and PCM renderer remain a declared cold sonification receiver.

[established-bounded; measured] Hugging Face tooling is installed in the isolated Apple Python
environment. Acquisition retained all 2,000 ESC-50 WAVs, verified mono PCM16 / 44.1 kHz / five
seconds, from mirror revision `8171bc2eca65db806e5da50d01683e867e38ccad`. A deterministic 100-clip
LibriSpeech dev-clean subset retains original FLAC, exactly decoded PCM16 WAVs, speaker/chapter
provenance and transcripts from revision `71cacbfb7e2354c4226d01e70d77d5fca3d04ba1`. Data,
checkpoints and generated audio stay under ignored `.local/`; reproducible recipes are tracked.

[definition] The full ESC-50 collection is CC BY-NC 3.0 (its ESC-10 subset is CC BY), with per-clip
attribution retained. LibriSpeech is CC BY 4.0. See the source links and acquisition instructions
in `docs/ACOUSTIC_EXPERIMENTS.md` and `research/experiments/apple_silicon/README_LIBRISPEECH.md`.

## Sound products, continuation and speech exposure

[established-bounded; measured] The full ESC-50 `1-100032-A-0.wav` completed all 220,500
arrivals by continuing its earlier silent prefix. There was no refusal or pending sample.
The complete application/native checkpoint is 465,125,473 bytes. This debug continuation and
cold publication took 299.47 s while other build/observer work was active; it is not a real-time
sound-performance result. The final actual source handle is 220,499, its returned source is
220,498, and the successor has rank two with a retained plural receiver direction. Both final
root-port quadratures remain recorded in [the dataset return](2026-09-06_apple_native_phase/dataset-returns.json).

[established-bounded; measured] One fixed receiver calibrated from the completed native emission
rendered 220,563 PCM16 samples at 44.1 kHz: five source seconds plus the declared 63-sample
support tail. The input has 15,134 nonzero samples; the output has 121,529. Native feedback
continues after source impulses, so this output is not the original recording. Output peak was
4,716 PCM codewords and RMS about 214.70, versus source peak 32,730 and RMS about 1,360.68.
These are digital receiver measurements, not acoustic pressure, intelligibility or energy.

[established-bounded; measured] Nine controls completed, using the first three sources in the
prepared family and 11,025 original-rate samples per control. The source preparation retained
fixed sample ranges selected by an exterior maximum-RMS observer; no native outcome or class
selected those ranges. Reversing chronology changes 11,023 emitted current cells in each source.
Polarity inversion exactly negates every rational emitted coordinate and every generated PCM
sample in each of these three comparisons. The full rational phase cells were checked against
the independently retained port/quadrature fibre, including their common denominators.
All final native successors have rank two and plural receiver fibres, read from the actual
session inspection rather than inferred from nonzero coordinates. No generated control clipped.

| Source | Changed generated samples after reversal | Changed generated samples after polarity inversion |
|---|---:|---:|
| `1-100032-A-0.wav` | 11,068 | 5,823 |
| `3-100018-A-18.wav` | 9,478 | 11,067 |
| `4-102844-A-49.wav` | 11,048 | 11,044 |

[definition] The [complete comparison](2026-09-06_apple_native_phase/acoustic-comparisons.json)
retains exact oriented differences and receiver fibres before scalar/PCM summaries. The
[figure](2026-09-06_apple_native_phase/acoustic-comparisons.png) separately labels source PCM,
one actual oriented native coordinate and generated PCM. Earlier local observer drafts confused
input/output plotting, coordinate counts/rank and integer/rational units; those drafts were
corrected before admission. Their local files remain recoverable and supply no evidence here.
The corrected observer reused existing render artifacts, without rerunning native development.

[established-bounded; measured] `SpeechExposureApplication` completed LibriSpeech utterance
`2277-149896-0000`: 105,440 samples at 16 kHz, a process checkpoint at the exact acoustic/text
boundary, then 113 original transcript bytes in a new process. The first transcript arrival
uses actual source 105,439 under the same declared digital return circuit. The complete artifact
is 235,886,724 bytes with no pending input. The linked experiment ends with rank two and a
plural receiver; an independently founded unlinked control using the same sound/text ends at
rank zero and outside-domain. This comparison changes the entire declared circuit, not just
its modality boundary, and establishes only that scoped causal attribution. It is not an
ablation isolating a learned audio/text semantic association.

[established-bounded; measured] Speech sound/text emissions rendered to 105,616 samples under
the same fixed 44.1 kHz sonification receiver. Source sample time and receiver playback time
remain separately declared. Generated speech-exposure audio also completed actual speaker playback (105,616 frames;
peak 2,303 PCM codewords). Three speech GPU tests verify malformed source refusal, premature
or altered pending text refusal, linked/unlinked conduct, and byte-identical complete artifacts
after cuts at zero, the modality transition, mid-text and completion. Native recognition,
intelligible speech generation and semantic cross-modal competence are not established by this
bounded exposure experiment.

[established-bounded; measured] The Swift audio apparatus built and passed the exact PCM16 WAV
round-trip and preexisting-output refusal checks. Actual generated audio completed playback on
MacBook Pro Speakers, with AVAudioFile's mono 44.1 kHz source and the device's float32 stereo
48 kHz output format recorded. The explicit `dataPlayedBack` callback prevents premature
completion at buffer consumption. A SIGINT interruption preserved an incomplete receipt with
unknown played frames. Final receipts include host-tick conversion (125/3 ns per tick), sample
scheduling and observed process intervals. They do not assert DAC calibration. Capture, route
change and gap handling are implemented; actual microphone capture was replaced by curated data
under Brandon's instruction and was not performed.

[historical] The original conclusion promoted these AS4–AS5 application probes into completion
of the requested sequence. That promotion is withdrawn. AS1–AS3 return the bounded Apple phase
foundation; the offline sound attachment, sonification, speaker lifecycle and serial sound/text
exposure are partial AS4–AS5 work. Corpus-based acoustic and English conversational capability
and measured real-time processing remain within the authorized objective. They do not depend
on personal microphone recordings. Physical room coupling has its own optional measurement scope.

## Verification apparatus

[definition] Local raw logs live in `.local/setup/apple-silicon/`. Relevant commands are:

```sh
cargo check -p mount --lib
cargo check -p holonics-hna --lib --locked
MTL_DEBUG_LAYER=1 cargo test -p holonic-engine --lib native_ecology::constitutive_fibre -- --ignored --test-threads=1
cargo test -p holonics-hna --lib native:: -- --ignored --test-threads=1
cargo test -p holonics-workbench --test native_checkpoint_process -- --ignored --test-threads=1
MTL_DEBUG_LAYER=1 cargo test -p mount --lib metal::tests -- --test-threads=1
MTL_DEBUG_LAYER=1 cargo test -p holonics-hna --lib native::acoustic::tests -- --ignored --test-threads=1
cargo build -p holonics-workbench --bins
cargo build -p holonics-hna --example native_resources
cargo test -p life --lib phase_session_factor -- --test-threads=1
```

[definition] The Metal README owns fresh arithmetic probe compilation. The acoustic guide owns
public run/resume/receiver/render commands. Lean proofs and imports were unchanged, so no Lean
build is claimed for this implementation. No microphone capture or physical room-path measurement
was performed under the curated-data substitution.

[established-bounded; process-audit] The final public-native test selection returned 20 passes
(acoustic, speech, checkpoint, session and wave application); the separate-process suite returned
four passes. Two source-neutral acoustic production factor tests and three shared launch-admission tests passed. A diagnostic run with
`MTL_DEBUG_LAYER=1` injected Apple's validation banner into stderr and broke two process tests
that require exactly one JSON receipt there. The normal protocol run then passed all four without
weakening that assertion; Metal validation remains enabled in the engine/mount and targeted
acoustic/speech checks. The diagnostic failure log remains local alongside the passing logs.
