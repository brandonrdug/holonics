# Holonics — Codex operating guide

Brandon's latest direct request governs. Holonics is a mathematical, physical and computational
framework; **HNN** is its neural machinery, **Athena** its first intended product, and **Eros** the
collective formative organization and composition within it. Codex uses this guide; Claude uses
its self-contained [CLAUDE.md](CLAUDE.md). Both use the shared mathematical sources below.

Read [THE_MACHINE](docs/THE_MACHINE.md) first. Then read the active brief in
[CONSTRUCTION_STATE](CONSTRUCTION_STATE.md) and the complete [roadmap](docs/plans/THE_ROADMAP.md),
retaining already-read context at the same revision. The state names the consuming operation;
the roadmap orders it. The machine, source guides and research supply the construction.

## The mathematical object you are implementing

[definition] One Holon `|H⟩_F` carries situated incidence K, constitutive/learned material Θ,
joint currents and internal modes, a frame F, and participating receivers. Circulating modes,
interlinked toroidal domains, helical passages, contacts and recursive/preimage geometry belong
to the same continuing field. A vector or a saved file is a chart of that construction. The
geometry supplies transport, comparison, variation and reuse; it is part of the learning law.

| Operation | Working equation / obligation |
|---|---|
| Transport and receive | `\|H'⟩_(F')=Ĝ_(F'←F)\|H⟩_F`, `y=⟨r\|b_H(H')⟩`; retain the frame, source, incidence and receiver |
| Coupled participation | `T_F[Ψ]=Σ_G a_FG[Ψ] U_(F←G)[Ψ] Ψ_G` over admitted contacts |
| Its complete variation | `δT=Σ a δ(UΨ)+Σ δa UΨ`; softmax has `J=diag(a)−aa*` |
| Native local reaction | `Φ(s,c)=s⊕c⊕(c⊗s)`, `incoming=s+MΦ(s,c)`, `out=S_D(incoming,b)` |
| Normal/factor inference | `W H=B` for the declared source/target statistics, prior and weights; preserve an unresolved null fibre |
| Generation | Refine the joint field under source and receiving conditions, then emit its boundary face; the refinement coordinate is distinct from an output-token index |
| Contact variation | `Q=⟨Δ\|Δ⟩`, with both sources' motion; the second variation includes geometric/prestress terms as well as a Gram term |
| Continuing compression | `D E=ρ`, `E_next T_g=U_g E`; retain the separating direction or interior defect when the source does not descend |

[project-postulate] The framework's ambition is frontier-level usefulness on consumer hardware.
Start from its accumulated mathematical and executable capabilities. Solver inference, generator
formation and Holonic Encoding are learning/intelligence at their stated scope. State the supplied
data, inferred unknown, returned relation and consequence. The [Holon](docs/HOLON.md),
[formula](docs/HNN_FORMULA.md) and [composition](docs/HNN_COMPOSITION.md) hold the detailed laws.

[definition] Use [Holonic notation](docs/HOLONIC_NOTATION.md): kets are constructions, bras
receivers, brackets faces, and `Ĝ_(F'←F)` a transport. Upper/lower tensor indices join through
the declared pairing; raising/lowering uses its metric. A diagram retains oriented lines,
interaction vertices and loops. `−1=e^{iπ}` and `i=e^{iπ/2}` name passages with windings;
state split and hand separately. Neighbouring passages use arrows `A_↗`, `A_↘`. An abstract
expression is unoriented until framed. Exact phase representation does not itself imply periodicity.

[definition] Context is the situated causal boundary: actual incidence, current, material/storage,
local clocks and the interior return needed by continuation. A token window is one exterior
source aperture. The programme treats difference as primary: values are its situated faces. Difference retains its comparands, orientation, source and receiving scope.
A zero face establishes agreement at that receiver; a richer receiver may distinguish the sources.
Preimage Fibres may be implicit and plural. Retain what admitted future operations need rather
than assuming a perfect inverse or a complete event archive.

## Code map: start at the consuming call

Paths in this table are relative to `crates/` unless stated otherwise. These are existing owners;
[ARCHITECTURE_MAP](docs/ARCHITECTURE_MAP.md) and the linked source guides give their formal peers.

| Work | Owning call / source to inspect |
|---|---|
| Public HNN model | `holonics-hna/src/native.rs`; `native/coupled_wave/body/field.rs` and `field/section.rs`; `NativeCoupledBody` is the move owner |
| Field session and source rows | `holonics-hna/src/native/field_session.rs`, `field_session/{shared,geometric}.rs`; `field_geometry.rs` compiles analytic incidence; `body/field/geometric.rs` composes phase participation, held refinement and its complete return |
| Exposure, source/response relations and resume | `holonics-hna/src/alpha/exposure.rs`; `examples/athena_exposure_field.rs`; [conversation data](docs/CONVERSATION_DATA.md) |
| Constitutive field, source and paired return | `holonic-engine/src/native_ecology/constitutive_fibre/field/`; source/reflection/target, material transport, internal modes and receiver |
| Normalized sections and pullback | `field/receiver/normalized{,.rs}` and `normalized/phase.rs` below that field; `holonic-engine/kernels/field_normalized_receiver.cuh`; exact reference `exponentiated_ratio::transport::NormalizedKernel` |
| Bilinear source/condition and normal law | `resident/section/bilinear_features.rs`, `field/material_transport/normal/direct/section.rs`; `section_bilinear_adjoint.cuh`, `normal_applied_condition.cuh` |
| Resident packets, kernels and launch | `holonic-engine/src/resident_section{,.rs}`; `kernels/exact_resident_section.cu`, `exact_packet_linear.cuh`; `holonic-mount/src/{cuda,launch_law,section_layout}.rs` |
| Exact algebra / generator reduction | `holonic-engine/src/exact_linear{,.rs}`, `prime_image_algebra.rs`, `receiver_history_compression/`, `winding_inertia.rs`; host/reference and resident APIs have distinct scopes |
| Helical and geometric source | `relational-geometry/src/{exact,model,screw,exact_analysis}.rs`; `holonic-engine/src/{identity_atlas,exact_contact,holonic_interaction,holonic_chain}.rs`; `receiver_history_compression/observable.rs::HelicalMomentReuse` binds finite pair actions to the existing moment decoder |
| Framework facade | `holonics/src/lib.rs`: `geometry` and `structure` work without the default native feature; HNN implementation is `holonics-hna` |
| Formal entry | `formal/elementary-holonics/ElementaryHolonics/Framework.lean`: Core, Geometry, Dynamics, Information, Physics, Computation; [formal guide](docs/FORMAL_FRAMEWORK.md) |
| Application interfaces | `applications/holonics-workbench`; `applications/conversation-data`; [repository layout](docs/REPOSITORY.md) |

[definition] **Native enclosure ABI:** a sealed section can store definite words for a centre
and a separate nonnegative radius. Equality of its lower/upper **carrier words** validates that
packet; it does not assert that the represented radius is zero. Read the row layout, grain,
denominator and radius position before interpreting a check. `ResidentNormalEnclosureSection`,
`normal_applied_condition.cuh` and `field_normalized_receiver.cuh` exhibit this distinction.
An enclosing ball and independent coordinate intervals also have different retained information.

[definition] `upstream_refused` consumes a complete `SLOT_WORDS` receipt (16 u32 words),
including lineage fields. Independent rows own complete receipts through launch; the final
barrier joins their statuses. Host allocation, kernel stride and logical placement share
`resident_section::SLOT_WORDS` as the Rust layout owner.

[definition] A ready native upload includes device completion. Pageable host-to-device copies
can return after host staging; the synchronous `holonic-mount` slice/range methods complete
their legacy-stream transfer before a nonblocking passage consumes the destination. Explicit
asynchronous copies retain their caller-owned event/stream dependency.

[definition] The native hot operation uses exact integer/rational packets and dyadic enclosures
with checked carriers. CPU code owns codecs, I/O and declared reference/certificate work; native
field execution keeps its current and intermediate sections resident. Device capacity comes from
the mounted hardware. Read/write footprints, joined outcomes and resource effects license a
parallel decomposition; `hardware_cover`, `section_partition`, `SectionLayout` and `launch_law`
enact it. Co-presence alone is not that proof. The [hardware guide](docs/HARDWARE_AND_MODALITY_BOUNDARIES.md)
and [device contract](docs/plans/THE_EXACT_DEVICE_LAW_IS_CONSTRUCTED.md) give the actual seams.

## Research that should already be in the construction

Use the maintained [research reading routes](research/records/README.md). Each route links the
founding/recent records, the governing mathematical guide, and the formal/native consumers.

| Subject / familiar spelling | Existing source family |
|---|---|
| Landmarks, periods, moduli, π/e, golden mode | `LandmarksAndModuli`, `Farey`, `Polarity`, `PiIterationConstraint`, `MachinPhaseConstraint`, `winding_inertia`, exact analytic owners |
| Generator inference, normalization, softmax/sigmoid, coding | `GeneratorInference`, `HolonicAdjointNormalization`, `NormalizedExponential`, `AttentionModeCompression`, `ReceiverCodeCost`, native normal and normalized receivers |
| Holonic Compression, modes, retained interior | `ReceiverHistoryCompression`, `GeneratorModeQuotient`, `JointReceiverDescent`, `HolonicQuadraticMomentCondensation`, native factor/moment/word owners |
| Helical/toroidal geometry, phase, contact and friction | [helical guide](docs/HELICAL_GEOMETRY.md), [constraint modes/active faces](docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md), [intrinsic field](research/experiments/intrinsic_holonic_flow/README.md), screw/connection/contact owners |
| Hodge, spectral placement, Euler/NS, time and levels | [mathematics/native synthesis](docs/MATHEMATICS_AND_NATIVE_CONDUCT.md), [fluid construction](docs/HOLONIC_FLUID_CONSTRUCTION.md), RH source families and Iwasawa/tube owners |
| Text, optics, acoustics and Holonic Encoding | [source preparation](docs/CONVERSATION_DATA.md), [receiver holarchy](docs/RECEIVER_HOLARCHY.md), generator recovery and phase-transport records |
| Earlier architecture/capability decisions | [retractions](docs/RETRACTIONS.md), [portable evidence](research/records/2026-09-06_REPOSITORY_SYNTHESIS_AND_PORTABLE_EVIDENCE.md), frozen `~/Workspaces/laboratory` source at its recorded revisions |

[project-postulate] These mathematical subjects develop reusable machinery, including their
physical consequences. Their named conjecture endpoints do not determine their relevance or
become prerequisites for every application. Native HNN foundations precede further inherited-model
production; Soulkiller's admitted source-neutral/resident material remains available at its
recorded scope. Use [Soulkiller](docs/SOULKILLER.md), [Athena](docs/ATHENA.md),
[architecture](docs/ARCHITECTURE.md) and [interoperability](docs/INTEROPERABILITY.md) for those interfaces.
Preserve existing `hna` API/wire identifiers and historical names.

[established-bounded; source-inspected] `GeometricRegions` currently uses alphabet-derived
channels, unit-current inputs/targets and per-slot basis decoding. It is a numerical application
control; `HelicalMomentReuse` is a separate caller. The next encoder/decoder work follows the
[existing Holonic Encoding construction](research/records/2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md)
and the [campaign correction](research/records/2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md#correction-the-nibble-control-is-not-holonic-encoding).

## Construct, connect, verify

1. Identify the requested object, mathematical unknown, source/receiver and actual consuming call
   from the active brief. Read the relevant research route and source, including its hypotheses.
2. Search the subject **and** its operations before proposing a new mechanism or absence:
   `.agents/bin/prior-art 'subject|LeanName|rust_name|classical spelling'`. Follow matching record
   titles and callers. Cite the existing owner and the concrete unconnected port or missing term.
3. Implement the relation in its owner and update its consumer. Use a realization equation such
   as `decode(T_native(encode(x)))=T(x)`, the complete directional residual, or the appropriate
   variation/descent law. Shared immutable standing and owned differences preserve one continuing
   ecology; stage changes and publish only after the return succeeds.
4. Resolve routine choices from that mathematics, mark inferred choices with their reason, and
   proceed. Develop interpretations into a derivation, counterexample or concrete residual.
   Ask Brandon only for a material choice that the available direction cannot determine.
5. Check the changed relation and inspect its emitted/consumed result. Preserve units, branch,
   uncertainty, source identity and cost. Measure the same input when comparing implementations;
   synthetic data and measured material retain their distinct scopes.
6. Update the owning guide, research links, issue body and current position together. A new
   document is useful when it supplies a needed explanation or source route; create or reorganize
   it as the task requires. Keep order in the roadmap and current progress in the state.

[definition] Tests, proofs and experiments support their stated scopes. Use one truth-status
from [epistemic grades](docs/canon/EPISTEMIC_GRADES.md) plus applicable evidence tags;
`agent-inferred` is a decision annotation, not a proof grade. Lean verifies research outside
cultivation/inference. A generated face is already output; later comparison/update and durable
continuation are separate operation contracts when requested. Benchmark counts do not replace
inspection of the actual requested result.

## Commands and shared-workspace practice

Commands below use Bash. With a fish shell, invoke a Bash command explicitly. CUDA compilation
may require `PATH=/opt/cuda/bin:$PATH`. Keep model/data artifacts in `.local/`, build output in
`target/`. The [development guide](docs/DEVELOPMENT.md) owns detailed build and measurement practice.

```bash
git status --short
rg --files crates formal docs research
cargo check -p holonics --no-default-features
cargo test -p holonic-engine --lib <module>::
cargo test -p holonic-engine -p holonics-hna -p relational-geometry --lib
flock .local/gpu.lock cargo test -p <crate> --lib <module>:: -- --include-ignored --test-threads=1
bash tools/lean_check.sh ElementaryHolonics.Framework.Geometry
rustfmt --edition 2024 --config skip_children=true <explicit-changed-files.rs>
gh issue view <number> --repo brandonrdug/holonics
git diff --check
```

[project-postulate] Check the device's current use before GPU tests; the lock coordinates only
processes that take it. Run checks appropriate to changed paths and retain their command/tree/
result in [VERIFICATION_RECEIPTS](docs/VERIFICATION_RECEIPTS.tsv). Reuse unchanged receipts.
One combined check closes interacting edits; a later isolated correction needs its changed
scope, not automatic replay of every suite. A timeout is incomplete evidence.

[project-postulate] Codex delegates to **Luna only**, for bounded independent work with explicit
owned paths, mathematical operands, source records and consuming calls. Workers read their
harness guide and the named machine/source material once; the primary provides the concrete
brief and integrates their returns. [WORKER_BRIEF](docs/WORKER_BRIEF.md) supplies the template.
Worker measurements are receipts; judgements are inspected against source. Use fewer workers
when the work does not split. Honour a request to work without agents.

[project-postulate] This is a shared checkout. Preserve other work, stage explicit owned paths,
and format explicit files. Never use a broad restore/reset/stash/clean to remove changes you did
not make. Constructors and remounts validate carrying values; checked dimensions precede their
allocation/work. Rebase, factor or change an exact representation when it outgrows its carrier,
retaining its decoder and residual. Commit and push coherent verified changes on the task's
branch, preserving requested branch names.

[definition] The repository is public; `.local/` and raw conversation/data captures are private.
Publish source, scoped results and necessary design provenance without raw private text or
machine-specific source paths. [AGENT_PROTOCOL](docs/AGENT_PROTOCOL.md) locates Codex/Claude logs
and their message codecs; direct messages govern, generated summaries and tool outputs do not.
The [document law](docs/canon/THE_DOCUMENT_LAW.md) owns documentation placement and continuity.
