# Holonics — Claude operating guide

Holonics is Brandon's mathematical, physical and computational framework. **HNN** is the machinery,
**Athena** its first intended product, and **Eros** the collective formative organization and the
composition within it. Brandon's latest direct request governs. This is Claude's self-contained
project guide; Codex uses [AGENTS.md](AGENTS.md). Both use the mathematical definitions and source
maps in [THE_MACHINE](docs/THE_MACHINE.md), [HOLON](docs/HOLON.md) and [HNN_FORMULA](docs/HNN_FORMULA.md).

Read the machine, [CONSTRUCTION_STATE](CONSTRUCTION_STATE.md) and the complete
[roadmap](docs/plans/THE_ROADMAP.md) once for the current task, retaining already-read context.
Worker prompts name this guide and the specific machine/source material to read. Make that context
explicit rather than relying on an assumption about which files a particular harness loaded.

## 1. The object and its equations

[project-postulate] HNN is one continuing geometric field: circulating phase modes, interlinked
toroidal domains, helical passages, active contacts and participating receivers. A Holon `|H⟩_F`
carries incidence K, material Θ, joint currents/modes and interior storage in frame F; it is a whole
and a part simultaneously. The geometry is how information is carried, compared, transformed and
learned. Every value is a situated comparison; its source, orientation and receiving scope remain.
The full theory-of-everything ambition and consumer-hardware usefulness guide the construction.

[definition] Independent commuting phases admit a toroidal chart. Linked/overlapping domains have
actual common cells and an interaction law; overlap alone does not supply friction. A helical object
has a generator **and an initial configuration**, with its own clock/parameter. A receiver is a
participating Holon whose reading can also have a simpler fixed-frame specialization.

```text
Object           (K, Θ, Ψ, interior) in frame F; its displayed vector/file is a chart
Transport        |H'⟩_(F') = Ĝ_(F'←F)|H⟩_F         Output   y = ρ_F b_H(H')
Interaction      |source⟩ → [standing H_int, dynamic H_pert, contact/material law] → ⟨perspective|
Helical source   ξ=(ω,v), V_ξ(x)=ω×x+v; two objects retain both generators and initial configurations
Pair receiver    Δ=x_a(s)−x_b(t), Q=⟨Δ|Δ⟩; DQ and D²Q include both motions and geometric Δ·a terms
Participation    T_F[Ψ]=Σ_G a_FG[Ψ] U_(F←G)[Ψ] Ψ_G over admitted contacts
Phase chart      s_ij=β cos(2π(q_i−q_j−φ_ij)), a=softmax(s); this unit-phase restriction has a connection φ
Variation        δT=Σ a δ(UΨ)+Σ δa UΨ, δa=(diag(a)−aa*)δs
Local reaction   Φ(s,c)=s⊕c⊕(c⊗s), incoming=s+MΦ(s,c), out=S_D(incoming,b)
Normal law       H=H₀+Σw f f*, B=B₀+Σw t f*, W H=B, with declared prior/weights/receiver
Generation       ∂_τ x=F_(K,Θ)(x,h,τ); refine the joint field and receive its boundary
Compression      D E=ρ, E_next T_g=U_g E; otherwise retain the separator, interior and defect
Recursion        A₀=A, A_(n+1)=Φ⁻¹(A_n)∖A: receiver-first-arrival populations of the actual recurrence
```

[definition] Learning uses the covector of a declared comparison. With prediction p and target q,
`p−q` is the cross-entropy logit gradient; `q−p` is its descent/update covector. Squared-probability
error also passes through the softmax Jacobian. Physical dissipation `⟨Jv,DJv⟩`, stored-energy
change and a learning loss are distinct quantities until a constitutive/receiver law connects them.
The paired adjoint uses the operands that produced the forward carriers.

[definition] Exact representation keeps constraints, branch, units, winding and remainder.
Periodic closure additionally needs a period/commensurability relation; an exact rational or
algebraic phase can have nonperiodic transport. The [helical guide](docs/HELICAL_GEOMETRY.md) and
[constraint-mode guide](docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md) supply the actual cases.

[project-postulate] Hodge's realization/cycle laws, RH's source-qualified spectral-placement laws,
Euler/Navier–Stokes transport, Iwasawa levels and the geometric/physical/information constructions
are implementation material at their stated hypotheses. Their conjecture endpoints are separate
claims. Recover the applicable relation and compose it; an isolated example does not reset the
framework's accumulated capability. **Compression is intelligence is navigation** names the same
construction: infer and retain generating relations, then execute/reuse them from the situated source and receiver. Solvers,
generator inference and Holonic Encoding already realize parts of it; the
[circulating cartographer](docs/canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md) carries this source.

[definition] Use [Holonic notation](docs/HOLONIC_NOTATION.md): typed kets, bras, faces and frame
transports; upper/lower tensor ports and an explicit metric for raising/lowering; oriented lines,
vertices and loops. Binary states are polarized side readings in a declared frame. `PhaseCarrier`
relates its two sheets to sign faces; multiplication by `−1=e^{iπ}` and `i=e^{iπ/2}` enacts half- and
quarter-turns. State, passage and winding have separate roles; split/hand remain explicit.
Neighbouring block passages use `A_↗`, `A_↘`. Abstract expressions are unoriented until framed.
Context means actual incidence, current, material/storage, local clocks and the interior return
needed by continuation. Limited observations may retain a plural Preimage Fibre without a perfect
inverse or an event archive.

[established-bounded; source-inspected] `GeometricRegions` currently uses alphabet-derived
channels, unit-current inputs/targets and per-slot basis decoding. It is a numerical application
control; `HelicalMomentReuse` is a separate caller. The next encoder/decoder work follows the
[existing Holonic Encoding construction](research/records/2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md)
and the [campaign correction](research/records/2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md#correction-the-nibble-control-is-not-holonic-encoding).

[definition] The [executable field campaign](docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#executable-field-campaign)
fixes the next composition: standing q/incident Delta feed the reaction, participation supplies
drive y, and one global D/b acts on their sum. Source/text/support maps are boundary material
with stated priors and the same normal update. The contract contains the complete adjoint,
publication, rest and source-episode packets; workers implement those choices rather than
reopening the source/condition chart question.

## 2. Where the implementation lives

| Operation | Source owner |
|---|---|
| Public model and move owner | `crates/holonics-hna/src/native.rs`; `native/coupled_wave/body/field.rs`, `field/section.rs`; `NativeCoupledBody` |
| Session, region preparation and observed return | `crates/holonics-hna/src/native/field_session.rs`, `field_session/{incidence,native_source}.rs` attaches an actual field and derives pre-target source/incident contrasts; `{shared,geometric}.rs` retains the text/control callers; `body/field/{formation,geometric}.rs` owns formation/family transport and geometric refinement |
| Real source and its comparison/cursor | `crates/holonics-hna/src/alpha/exposure.rs`, `examples/athena_exposure_field.rs`; [conversation data](docs/CONVERSATION_DATA.md) |
| Constitutive field and paired source/current | `crates/holonic-engine/src/native_ecology/constitutive_fibre/field/`: source/reflection/target, material transport, receivers and internal modes |
| Normalization and adjoints | `field/receiver/normalized{,.rs}`, `normalized/phase.rs`, `field/material_transport/normal/direct/section{,/composition}.rs`, `resident/section/bilinear_features.rs`; exact reference `exponentiated_ratio::transport::NormalizedKernel` |
| Kernels and their Rust binders | `crates/holonic-engine/kernels/{exact_resident_section.cu,field_normalized_receiver.cuh,normal_applied_condition.cuh,section_bilinear_adjoint.cuh}`; `src/resident_section/` |
| Hardware law | `hardware_cover`, `section_partition`; `crates/holonic-mount/src/{cuda,launch_law,section_layout}.rs` |
| Exact geometry and helical pair | `crates/relational-geometry/src/{exact,model,screw,exact_analysis}.rs`; `holonic-engine/src/{identity_atlas,exact_contact,holonic_interaction,holonic_chain}.rs`; `receiver_history_compression/observable.rs::HelicalMomentReuse` binds finite pair actions to the existing moment decoder |
| Algebra and economical continuation | `exact_linear`, `prime_image_algebra`, `receiver_history_compression`, `winding_inertia`; resident bilinear/normal/word/mode owners at their separate call boundaries |
| Public framework | `crates/holonics/src/lib.rs`: `geometry` and `structure` without default native features; `holonics-hna` for HNN |
| Lean | `formal/elementary-holonics/ElementaryHolonics/Framework.lean` and its Core/Geometry/Dynamics/Information/Physics/Computation entry points |
| Applications and evidence | `applications/holonics-workbench`, `applications/conversation-data`; `research/{records,experiments,papers,notebook}`; [layout](docs/REPOSITORY.md) |

[definition] **Enclosure ABI:** sealed low/high carrier words can encode a definite centre and
an independently nonzero radius. Equality of those words is not a zero-radius test. Read the row
layout, grain, denominator and radius slot before judging propagation or refusal. The native
normal and normalized-receiver section tests exercise nonzero source/condition/covector radii.

[definition] A kernel using `upstream_refused` supplies a complete `SLOT_WORDS` receipt
(16 u32 words), including lineage fields. Independent rows own those complete receipts until
their deterministic barrier joins the statuses. Host allocations, kernel stride and logical
placement use that same layout; `resident_section::SLOT_WORDS` is the Rust owner.

[definition] A ready native upload includes device completion. Pageable host-to-device copies
can return after host staging; synchronous `holonic-mount` slice/range methods complete the
legacy-stream transfer before a nonblocking passage reads it. Explicit asynchronous copies
retain their caller-owned event/stream dependency.
A joint ball, a family with shared parameters and independent coordinate intervals have different
information; use the representation the consuming equation needs.

[definition] **Hardware:** co-present regions execute together when complete read/write, lineage,
obstruction and resource effects commute. Shared immutable input and disjoint staged output are
one sufficient pattern; mutable overlap needs its actual interchange/reduction law. Certify the
partition, read device capacity, derive layout/launch and retain the current on the card. One
block per row with one active thread, one thread looping all rows, and useful parallel work within
a row are different realizations. Report the actual one, not only the word “resident”.

## 3. Recover the research before choosing an implementation

The maintained [research routes](research/records/README.md) link useful records directly to
formal/native owners. Begin with the task's subject, not only a recently proposed algorithm.

- **Landmarks/phase/constants:** `LandmarksAndModuli`, `Farey`, `Polarity`, `PiIterationConstraint`,
  `MachinPhaseConstraint`, `winding_inertia`, exact analytic owners; qualify the distinct Copson
  and Newman source families.
- **Inference/normalization/compression:** `GeneratorInference`, `HolonicAdjointNormalization`,
  `AttentionModeCompression`, `GeneratorModeQuotient`, `ReceiverHistoryCompression`,
  `ReceiverCodeCost`, quadratic moments and their native factor/receiver/mode consumers.
- **Geometry/physics:** [helical geometry](docs/HELICAL_GEOMETRY.md),
  [fluid construction](docs/HOLONIC_FLUID_CONSTRUCTION.md),
  [active faces](docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md),
  [intrinsic field](research/experiments/intrinsic_holonic_flow/README.md),
  [mathematics/native synthesis](docs/MATHEMATICS_AND_NATIVE_CONDUCT.md).
- **Data and prior decisions:** [conversation data](docs/CONVERSATION_DATA.md),
  [retractions](docs/RETRACTIONS.md), [evidence/log protocol](docs/AGENT_PROTOCOL.md), and the frozen
  `~/Workspaces/laboratory` at the relevant source revision.

```bash
.agents/bin/prior-art 'subject|LeanName|rust_name|classical spelling'
rg -n '<term>' docs/ARCHITECTURE_MAP.md
rg --files research/records | rg -i '<subject|alternate spelling>'
gh issue view <number> --repo brandonrdug/holonics
```

Read the matched record and its actual source/caller. The task identifies the known operands,
inferred unknown, generating law, receiver and returned residual. Native HNN foundations remain
prior to further inherited-model production; Soulkiller's admitted material retains its recorded
scope. [Architecture](docs/ARCHITECTURE.md), [Soulkiller](docs/SOULKILLER.md), [Athena](docs/ATHENA.md)
and [interoperability](docs/INTEROPERABILITY.md) define those interfaces. Keep existing API/wire names.

## 4. Work, verify and document the return

[project-postulate] Resolve routine choices from the mathematics, annotate inferred choices with
their reason, and proceed. Implement the relation and its actual consumer together. Stage changes
under one move owner; use the producing material for its adjoint and publish the successor when
its return succeeds. Inspect the generated result and measured cost at the declared receiver.
A scalar loss or benchmark has its source, units and population; it is not intrinsic identity.

[project-postulate] Create and reorganize documentation when it makes the mathematics or source
usable. Put reusable definitions in their guide, implementation beside its owner, substantial
research in dated records, current order in the roadmap and current position in the state.
Connect the record to its subject route, code and issue body. [Epistemic grades](docs/canon/EPISTEMIC_GRADES.md)
separate truth status from evidence; `agent-inferred` annotates a decision rather than proving it.
[The document law](docs/canon/THE_DOCUMENT_LAW.md) gives the shared placement convention.

Commands below use Bash; invoke Bash explicitly if the active shell is fish. CUDA may need
`PATH=/opt/cuda/bin:$PATH`. [DEVELOPMENT](docs/DEVELOPMENT.md) owns the detailed procedure.

```bash
cargo check -p holonic-engine --lib
cargo test -p <crate> --lib <module>::
cargo test -p holonic-engine -p holonics-hna -p relational-geometry --lib
flock .local/gpu.lock cargo test -p <crate> --lib <module>:: -- --include-ignored --test-threads=1
bash tools/lean_check.sh ElementaryHolonics.Framework.Geometry
bash tools/lean_check.sh ElementaryHolonics  # complete research umbrella when that scope changed
rustfmt --edition 2024 --config skip_children=true <explicit-changed-files.rs>
git diff --check
```

Check current device use before GPU tests; the file lock coordinates only processes taking it.
Record command, tree, scope and result in [VERIFICATION_RECEIPTS](docs/VERIFICATION_RECEIPTS.tsv).
Reuse unchanged receipts. The primary verifies the combined changed scope; a later isolated fix
needs its own scope rather than a replay of every suite. Lean verifies mathematics outside native
cultivation/inference. The normal Lake default is `ElementaryHolonics.Framework`, not the complete
research umbrella. Timeouts remain incomplete evidence.

[project-postulate] Claude delegates to at most **three Opus 5 workers** on disjoint owner paths,
then **one Sonnet 5 reviewer that spawns nothing**; use fewer workers when the work does not split,
and a sequential join when it consumes multiple returns. Every prompt supplies this guide, the
machine/source material, exact paths, existing owners, equations, consumer and relevant receipts.
[WORKER_BRIEF](docs/WORKER_BRIEF.md) has the concrete template. The primary inspects source and
integrates returned changes; worker measurements are reusable receipts.

[project-postulate] This is a shared checkout. Stage and format explicit owned paths; preserve
other agents' and the user's work. A broad restore/reset/stash/clean is not a way to tidy another
owner's diff. Constructors and remounts validate carrying values, checked extents precede work,
and exact growth is handled by rebase/factor/representation change with its decoder and residual.
Commit and push coherent verified work on the task's branch. If adding a co-author credit, use
actual attribution rather than a hardcoded model name.

[definition] The repository is public; `.local/` contains private datasets, captures, models and
run artifacts. Publish source and scoped evidence without raw private conversation or source
paths. Dataset roles and provenance are exterior codec information, not native semantic IDs.
The current application position and next action live only in CONSTRUCTION_STATE and the roadmap.
