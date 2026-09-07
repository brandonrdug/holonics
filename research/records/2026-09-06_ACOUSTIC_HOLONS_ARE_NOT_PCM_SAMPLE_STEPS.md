# Acoustic holons are not PCM sample steps

[definition] September 6, 2026. Source inspection at `be9211857c330fda4594f218a2a997699e434aa8`
on `codex/apple-silicon`. This record corrects the acoustic specification and interpretation of the
[packet measurements](2026-09-06_AS4_AS5_CORPUS_CONTINUATION_AND_RESIDENT_PACKETS.md);
it does not report a new native implementation or performance run.

## Direct correction

[project-postulate] Brandon's direct message in the MacBook Apple/acoustics task, following the
explanation of slower-than-real-time processing: “I would rather not use PCM when we they are
better put as Holons, we have extensive research and ontology about this.” The requested native
representation is holonic. His preceding request places acoustic/linguistic unification with the
desktop work; neither a microphone sample nor a new file format resolves that composition.

[established-bounded; source-inspected] `AcousticApplication::current_for` in
`crates/holonics-hna/src/native/acoustic.rs` supplies `(sample / pcm_divisor, 0)`, optionally adding
the declared digital return. Scalar and packet execution both perform a native step for every
sample. Packet submission preserves this chosen sequence. This was an authored experimental
mapping, not a consequence of the ontology or a requirement imposed by WAV decoding.

## Existing constructions and their boundaries

[established-bounded; source-inspected] The following are existing sources, not newly verified
theorems or a claim that their complete composition already runs on Apple:

| Owner | Relevant construction and limitation |
|---|---|
| `docs/canon/TABLET_THE_OPERATIONS.md`; `TABLET_THE_RESONANCE.md` | Construction composes holons with causal residue; participation and relations precede a receiver's face. Sample count, spectral magnitude and file labels do not found native identity. |
| `formal/elementary-holonics/ElementaryHolonics/Foundation/CausalNaturalHolon.lean` | `CausalNaturalHolon` carries occurrence/source/target/receiver families and actual parameter passages. `mapPreimageFibre` transports the population behind a face; arbitrary causal transport does not fabricate an inverse. This is formal apparatus, not a runtime to embed. |
| `formal/elementary-holonics/ElementaryHolonics/Computation/IntrinsicHolonProfile.lean` | Profiles distinguish caused relations and role-indexed dimensions; codec labels do not classify native topology. |
| `crates/holonic-engine/src/phase_current.rs` | `ExactPhaseCurrentSection` retains receiver, lineage, local clock, full phase coefficients and raw extent; causal convolution carries phase into later cells. The caller's `phase_extent` is a chart choice, not learned grain. Existing CPU execution is not an authorized substitute for the GPU hot operation. |
| `crates/holonic-life/src/synchronized_occurrence.rs` | `ExactClockTransport` and `SynchronizedReceiverSection` retain distinct local clocks and overlapping cells. Co-presence does not supply association. This owner uses the older live-current mouth, not the current phase-session API. |
| `crates/holonic-engine/src/native_ecology/recurrent_condensation.rs` | `CondensedRecurrentRest` retains compact standing, executable decoder and fibres with separators for its bounded recurrent family. This is an existing construction to reuse at its actual domain, not an arbitrary WAV compressor. |
| `crates/holonic-life/src/native_intelligence/membrane_acoustic.rs` and `membrane_acoustic/potential_formation.rs` | Native production carries actual ordered outward currents and both quadratures into an acoustic receiver. Cold PCM rendering follows it. The existing phase attachment/fixed sonification does not yet supply learned acoustic production. |

[definition] `docs/canon/TABLET_THE_COMPRESSION.md` governs a codec pivot: its decoder and
receiver-relative remainder belong to the construction. Continuing condensation also retains the
generator transport relation and separating histories required by its domain. This does not impose
universal losslessness, permanent hot residency of raw audio, or a universal compression gate.
Source recordings remain recoverable evidence; they are not a source-bearing quotation emitter.

## Corrected AS4–AS5 composition

[definition] Import recorded sound through its exterior chart, then compose situated material with
addressed source/receiver relations, local temporal support, actual transport and oriented current.
Retain the complete reconstruction fibre for any admitted projection. Native organization must
come from that interaction and its returned consequences. Fixed PCM steps, arbitrary frame cuts,
frequency bins or authored phoneme labels cannot silently determine native morphology.

[definition] Acoustic and linguistic exposure meet through the same native material/current/formation
construction and one continuing successor. AMI speaker, clock, transcript and response annotations
remain source-qualified exterior testimony; their metadata alone cannot author learned contact.
The active phase session and older acoustic/clock bodies have concrete type/execution boundaries
to compose. Do not create another learner or fabricate older receipts to hide those boundaries.

[definition] Production proceeds from the developed native emission into an explicit acoustic
receiver, with PCM only where the file/device boundary needs that presentation. Retaining a
waveform for provenance does not license playing it as native generation. Useful sound perception,
production and English communication remain the requested products.

[established-bounded; measured] The prior packet run took 63.251 s for 5 s of sound and 46.584 s
for 6.59 s of English under its recorded debug/concurrent-build conditions. Those are measurements
of the per-sample probe; no native holonic acoustic representation was compared in that run.

[open] The realized native acoustic carrier, its attachment to shared formation and its end-to-end
cost remain unfinished. Establish the composition before presenting sample-loop optimization as
the product path. Fewer operations or smaller storage may follow from lawful composition and
reuse, but no speedup or real-time capability is established by this correction.

[established-bounded; process-audit] This return updates the Apple specification, live position,
roadmap, acoustic/hardware guides, retraction history and probe module documentation. Runtime
behavior and schemas are unchanged. The diff was reviewed and `git diff --check` passed;
no Cargo, Lean or audio benchmark was rerun for documentation-only changes.
