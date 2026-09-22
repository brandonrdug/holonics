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

[project-postulate] Begin generation work with the
[situated generator/action relation](docs/HOLON.md#situated-generator-inference-dormant-modes-and-action):
known source family, admitted controls/conditions, participating receiver and requested consequence.
Text, image, acoustic and motor releases are applications of that relation. Robotics is an intended
HNN capability; the [simulator boundary](docs/HARDWARE_AND_MODALITY_BOUNDARIES.md#robotics-and-simulation-boundary)
constrains the shared design now without scheduling a simulator run. A mode's availability is
retained standing, not continuous activation.

[definition] **Retention is a quotient sufficient for the admitted future**
(`Foundation/Standing.lean`, `standing.rs`); it is never an event archive, tape, journal,
ledger or frozen producing cut kept for replay. "A current changes the standing a later current
meets" is a consequence of that law, not the definition of learning: do not derive a per-occurrence
state chain, its adjoint tape, frozen cuts or a fold over an update list from it. The source
passage enters as phase-carried moments `m_g=Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)` whose adjoint needs
no tape; a comparison observed after an update is read through the contemporary standing and
returns its residual. The [retention audit](research/records/2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md)
names the objects this replaces. Read `Foundation/Standing.lean`, the
[prediction/release record](research/records/2026-09-12_PREDICTION_IS_PREPARED_TRANSPORT_AND_RELEASE_IS_BOUNDARY_CURRENT.md)
and the [source audit](research/records/2026-09-21_SITUATED_GENERATORS_RETAIN_MODES_AND_RELEASE_ACTION.md)
when working on recall, relevance, homeostasis or action inference.

[definition] **The computational object is the helical pair interaction**
([definition](docs/HOLON.md#the-helical-pair-interaction-unit),
[geometry](docs/HELICAL_GEOMETRY.md#the-pair-is-a-holonic-interaction-contact),
[audit and packets](research/records/2026-09-21_THE_HELICAL_PAIR_INTERACTION_IS_THE_HNN_SITE_AND_PHASE_CARRIES_CONTEXT.md)):
a `HolonicInteraction` over a `ScrewPair` whose contact slip map is the pair's relative velocity.
HNN sites are generators with initial configurations, admitted pairs are arcs and the machine's
phases carry context. A source passage enters as phase-carried helical moments, a response
position is a receiving phase, and generator count is independent of source length. Ingestion,
exact bit growth and retained source defects have their own costs. The
rotor machine (material carried by a phase shift, reflected return through the producing
operands), the Bombe (configuration inference by pairwise loop closure) and an articulated body
(an ordered chain of `SituatedScrew`s) are instances. State a design in these operands before
implementing it; a text, image, acoustic or motor chart is a boundary of this object.

[project-postulate] **One picture, kept attached during work**
([winding guide](docs/WINDING_CARRY_AND_PLACEMENT.md),
[record](research/records/2026-09-21_WINDING_CARRY_FACES_AND_PLACEMENT_GENERALIZE_THE_HELICAL_PAIR.md)).
The pair unit continues into six general objects, and a design or worker brief states which it
touches and keeps the rest attached: (1) **helix = circle + carry** — retain the cocycle and
lift; phase-only material descent needs closure/commutation; (2) **pair = torus with a modular
address** — a no-slip direction has a Farey address in the positive rational chart; material
null slip, signs and stationary cases retain their own domains; (3) **generator faces and
placement** — frame carriage conserves determinant, trace sequence and transfer determinant;
rotation–dilation and signature placement require their stated metric/spectral hypotheses;
(4) **face = holonomy around a cell** — class functions are gauge-free, a proper rigid holonomy
has a screw reading, a flat affine holonomy has a Burgers translation, and harmonic standing
is relative to node/cell receivers; (5) **tube = transfer between cross-section charts** — map
and pairing readings use a declared duality, with reflection eliminating the interior where
its law applies; (6) **continuing = a compatible thread through a tower** — unique lifting
requires its lifting condition. Compression keeps future-distinguishing classes and the gluing
between levels. Primes, `ζ`, `Λ_DN`, elliptic curves, Hodge classes, Einstein's tensors, rotor
machines and articulated bodies are instances with graded scope, using these shared objects.

[definition] The [finalized machine contract](docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#situated-generator-and-receiving-composition)
keeps configuration, rate, storage and resident-current charts distinct. `RationalPhase` is a
Cayley half-angle chart, not a rational turn rate; finite odometer levels require closure.
Moment and trace equality preserve their declared faces; functionality also needs `D E=ρ`
and `E_next T=U E`, including source order and changed receivers. `PairQuadranceJet::pullback`
is only the scalar-Q parameter return; the full feature/material/clock adjoint remains owed
where consumed. Harmonic standing is a concrete receiver-relative instance of general standing.

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
| Pair contact | `J=[v_a\|−v_b]`, `DQ=2J*Δ`, `D²Q=2J*J+2diag(Δ·a_a,−Δ·a_b)`; `M_contact=Σw J*DJ`; zero power ⇔ `D_f J u=0`; definite response on attainable slips gives `ṡv_a=ṫv_b`; a bilinear score is the polarized pair quadrance, so the unit-phase chart is the pair at zero advance and unit radii |
| Phase carriage | `R_d=S⁻ᵈPSᵈ`; return `A⁻¹FA`; n uniform steps through fixed P compose to `(PS⁻¹)ⁿSⁿ`; a menu loop closes ⇔ the stage word fixes the boundary image; the helix is the winding-retaining lift of a torus chart |
| Carry | `x=phase+n·winding`; `winding(x+y)=winding x+winding y+carry`; the carry is a cocycle and is content (`ℤ/4≄ℤ/2×ℤ/2`); `Sⁿ=C ⇒ S^(d+nk)=S^d·C^k`; the odometer's upper level advances by the lower winding |
| Lock and address | `q·v_a=p·v_b` ⇔ no-slip (zero power under definite response); neighbours ⇔ `p'q−pq'=1`; the mediant is the cheapest lock between; an address is a word in ⟨step, inversion⟩ |
| Trace faces and placement | `(S⁻ᵈPSᵈ)ᵏ=S⁻ᵈPᵏSᵈ`; `det`, `tr(Mᵏ)`, `det(1−T·M)` conserved; block-diagonal machine `∏(1−a_gT+q_gT²)`, `Σ tr(M_gᵏ)`; `SiteKind::Rotation` ⇔ `a²<4q`; placement under its signature hypotheses |
| Cell holonomy and dormant class | `H=g₀₁g₁₂g₂₀ ↦ k₀⁻¹Hk₀`; `d₁(A+d₀φ)=d₁A`; a harmonic mode is silent at node/cell receivers; a harmonic potential is zero; retain its class |
| Source and receiving phases | `m_g=Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)`, pair relation `M_gh(δ)` at relative offset δ, `y_j=ρ_R(Ĝ(j)q)`; each generator advances by its own rate and the codec unit is not a native clock |
| Continuing compression | `D E=ρ`, `E_next T_g=U_g E`; retain the separating direction or interior defect when the source does not descend |

[project-postulate] The framework's ambition is frontier-level usefulness on consumer hardware.
Start from its accumulated mathematical and executable capabilities. **Compression is intelligence
is navigation:** infer and retain generating relations, then execute/reuse them from the situated source and receiver. Solver inference, generator
formation and Holonic Encoding are actual forms of this work. The
[circulating cartographer](docs/canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md) and
[solver clarification](research/records/2026-09-12_SOLVER_INFERENCE_AND_GENERATOR_COMPRESSION_ARE_INTELLIGENCE.md)
carry the existing construction. State the supplied
data, inferred unknown, returned relation and consequence. The [Holon](docs/HOLON.md),
[formula](docs/HNN_FORMULA.md) and [composition](docs/HNN_COMPOSITION.md) hold the detailed laws.

[definition] Use [Holonic notation](docs/HOLONIC_NOTATION.md): kets are constructions, bras
receivers, brackets faces, and `Ĝ_(F'←F)` a transport. Upper/lower tensor indices join through
the declared pairing; raising/lowering uses its metric. A diagram retains oriented lines,
interaction vertices and loops. A binary state is a polarized side reading in a declared frame;
the existing `PhaseCarrier` relates its two sheets to sign faces. Multiplication by `−1=e^{iπ}` or `i=e^{iπ/2}` acts as a
half- or quarter-turn. State, passage and winding retain their separate roles; state split
and hand separately. Neighbouring passages use arrows `A_↗`, `A_↘`. An abstract
expression is unoriented until framed. Exact phase representation does not itself imply periodicity.

[definition] Context is the situated causal boundary: actual incidence, current, material/storage,
local clocks and the interior return needed by continuation. A token window is one exterior
source aperture. The programme treats difference as primary: values are its situated faces. Difference retains its comparands, orientation, source and receiving scope.
A zero face establishes agreement at that receiver; a richer receiver may distinguish the sources.
Preimage Fibres may be implicit and plural. Retain what admitted future operations need rather
than assuming a perfect inverse or a complete event archive.

[established-bounded; source-inspected] Public generator `observe` now develops positive
pair amplitudes through `operative/source/action/contact_amplitude.rs`, reconstructing D/D*
from a fixed template and current parameters. The rank-0 source-only CSR path stores no
completed update journal; the `returns` journal remains on other paths. Pending comparisons
still retain a per-occurrence nonlinear tape (`incident/machine_episode.rs`); its removal in
favour of the moment accumulation is the next return, per the
[retention audit](research/records/2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md).
`enclosure_propagation` selects joint-ball bounds for new generator declarations; absent
fields replay the legacy numerical law. The
[material return](research/records/2026-09-22_PAIR_MATERIAL_LEARNS_WITHOUT_A_COMPLETED_UPDATE_ARCHIVE.md)
names the native/formal evidence and remaining geometry/closure/economy scope;
`Transport/ContactAmplitudeState.lean` is a fold tautology, not the standing binding owed in #17.

[definition] The [executable field campaign](docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#executable-field-campaign)
fixes the implemented composition: standing q/incident Delta feed the reaction, participation supplies
drive y, and one global D/b acts on their sum. Source/text/support maps are boundary material
with stated priors and the same normal update. The contract contains the complete adjoint,
publication, rest and source-episode packets. These are implemented constituents of the shared
operation; the text/support chart is one application. Its Athena geometry
(`examples/support/linked_torus_field.rs`) assigns one ring junction per source cell with a
one-hot encoder and per-slot faces. That legacy caller does not consume the new pair-derived
machine; its layout is a control the generator machine
replaces. Continue from those returns through the roadmap's packets: pair contact and serial
chain, the generator-machine geometry, closure inference with standing/release, then economy
and episodes, preserving the original target port and source fibre.

[established-bounded; source-inspected] The [first campaign return](research/records/2026-09-21_PAIR_CONTACT_SERIAL_KINEMATICS_AND_THE_RESIDENT_QUADRANCE_RETURN.md)
implements the exact pair-contact adapter and Cayley/prismatic serial chain with their formal
laws. `NativePairParticipation` executes the quadrance score with separate geometry/value
covectors on the device; `IncidentParticipationChart::QuadranceCurrent` binds the explicit
same-current specialization into the existing HNN word and rest. Legacy bilinear mode remains
the default. These are dependencies of the fixed generator/source/phase machine, whose actual
configuration/current maps and phase reception now have a body consumer; ordered source/session
binding has returned through the public generator session.

[definition] `IncidentFieldOptions::response_port_start` fixes the receiving slots independently
of input length; fresh sessions reserve the final receiving aperture. Generation, comparison
and rest use the same binding. Native potential ordering supplies text/support selection, with
each text row's own radius. The [source guide](docs/CONVERSATION_DATA.md#incident-field-source-boundary)
and current campaign record distinguish that receiving face from a broad normalized enclosure.

## Code map: start at the consuming call

Paths in this table are relative to `crates/` unless stated otherwise. These are existing owners;
[ARCHITECTURE_MAP](docs/ARCHITECTURE_MAP.md) and the linked source guides give their formal peers.

| Work | Owning call / source to inspect |
|---|---|
| Public HNN model | `holonics-hna/src/native.rs`; `native/coupled_wave/body/field.rs` and `field/section.rs`; `NativeCoupledBody` is the move owner |
| Field session and source rows | `holonics-hna/src/native/field_session.rs`, `field_session/{incidence,native_source}.rs` attaches an actual field and derives pre-target source/incident contrasts; `field_session/mathematical_port.rs` is the scoped same-surface typed global-complex workshop port; `{shared,geometric}.rs` retains the text/control callers; `body/field/{formation,geometric,incident}.rs` owns formation, family transport, incident `Phi(q,Delta)` and geometric refinement |
| Exposure, source/response relations and resume | `holonics-hna/src/alpha/exposure.rs`; `examples/athena_exposure_field.rs`; [conversation data](docs/CONVERSATION_DATA.md) |
| Constitutive field, source and paired return | `holonic-engine/src/native_ecology/constitutive_fibre/field/`; `field/junction/operative/source/{action,map_action,reflection,reflection_commit,reflection_target}.rs` owns the source-qualified dense/reference and CSR+low-rank global action, full joint covector and staged material return; source/reflection/target, material transport, internal modes and receiver |
| Normalized sections and pullback | `field/receiver/normalized{,.rs}` and `normalized/phase.rs` below that field; `holonic-engine/kernels/field_normalized_receiver.cuh`; exact reference `exponentiated_ratio::transport::NormalizedKernel` |
| Bilinear source/condition and normal law | `resident/section/bilinear_features.rs`, `field/material_transport/normal/direct/section.rs`; `section_bilinear_adjoint.cuh`, `normal_applied_condition.cuh` |
| Resident packets, kernels and launch | `holonic-engine/src/resident_section{,.rs}`; `kernels/exact_resident_section.cu`, `exact_packet_linear.cuh`; `holonic-mount/src/{cuda,launch_law,section_layout}.rs` |
| Exact algebra / generator reduction | `holonic-engine/src/exact_linear{,.rs}`, `prime_image_algebra.rs`, `receiver_history_compression/`, `winding_inertia.rs`; host/reference and resident APIs have distinct scopes |
| Retained availability and predictive release | `holonic-engine/src/{standing,receiver_release}.rs`, `exact_linear/{contextual,kernel_modes}.rs`; `field/internal_mode.rs` retains the equal-drive specialization and explicitly refuses incompatible operative currents; `Foundation/{Standing,CausalRelevance,ReceiverHistoryCompression}.lean` supplies future sufficiency |
| Helical and geometric source | `relational-geometry/src/{exact,model,screw,exact_analysis}.rs`; `holonic-engine/src/{identity_atlas,exact_contact,holonic_interaction,holonic_chain}.rs`; `receiver_history_compression/observable.rs::HelicalMomentReuse` binds finite pair actions to the existing moment decoder. `holonic_interaction/helical.rs` now joins `ScrewPair` to the checked `HolonicInteraction` with an explicit rate port; `holonic_chain/serial.rs` supplies exact Cayley/prismatic chains, contact rows and constrained target fibres. `Transport/{HelicalPairInteraction,SerialScrewChain}.lean` owns their checked algebra; the full HNN generator-machine binding remains #17 |
| Winding, carry, address, trace faces and cell holonomy | Lean `Geometry/{PhaseCarry,PairResonance}`, `Transport/{GeneratorTraceFaces,CellHolonomy}` over `Millennium/{Farey,LocalFactor,TraceSequence,HodgeIndex,PlaceLedger,WindingLedger}`, `RH/{FosterTanks,HeatFlowStackedSeam}`, `Foundation/{HodgeReceiver,IwasawaTower,FractalPacking}`; Rust `relational-geometry/src/winding.rs` (`Odometer`, `LockAddress`, `SiteFactor`, `Machine`, `triangle_holonomy`); [guide](docs/WINDING_CARRY_AND_PLACEMENT.md) §8 lists the operands a design states |
| Framework facade | `holonics/src/lib.rs`: `geometry` and `structure` work without the default native feature; HNN implementation is `holonics-hna` |
| Formal entry | `formal/elementary-holonics/ElementaryHolonics/Framework.lean`: Core, Geometry, Dynamics, Information, Physics, Computation; [formal guide](docs/FORMAL_FRAMEWORK.md). Core imports `Foundation/{Standing,ReceiverRelease}`; Dynamics imports `Transport/{HolonicInteraction,HolonicChain,ContinuingTube,HelicalPairInteraction}`. A native packet that adds or changes a mathematical law lands with its Lean counterpart or names the obligation it leaves in #62 |
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
| Winding, carry, staircases of remainders, locks and addresses, conserved faces, cell holonomy, dormant classes, placement, tubes, continuation | [winding guide](docs/WINDING_CARRY_AND_PLACEMENT.md) first; `PhaseCarry`, `PairResonance`, `GeneratorTraceFaces`, `CellHolonomy`; `Farey`, `LocalFactor`, `TraceSequence`, `HodgeIndex`, `HodgeDivisorExponentialPassage`, `PlaceLedger`, `WindingLedger`, `Crossings`, `FosterTanks`, `HeatFlowStackedSeam`, `HodgeReceiver`, `IwasawaTower`, `FractalPacking`; Rust `relational_geometry::winding` |
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

[definition] `NativeCoupledBody::found_generator_field` now consumes the fixed machine:
`field_geometry/{machine,machine_factor}.rs` owns its validated declaration and exact contact
factor, `incident/{machine,machine_transport,machine_receiving}.rs` owns its resident affine
word and tagged phase boundary. Original complex-3 currents are encoded as six real-coded
native complex channels; the explicit projection and its transpose preserve that image.
Declared pair material remains fixed while reaction material develops. Ordered source/session
binding now consumes that body; the [current-chart record](research/records/2026-09-21_THE_FIXED_GENERATOR_MACHINE_CONSUMES_ITS_AFFINE_CURRENT_CHART.md)
states its law and remaining scope. Legacy slot/response semantics remain distinct.

[definition] `field_session/generator_application.rs` now owns the public `GeneratorMachine`
source/receiving session. `incident/{machine_source,machine_source_contacts,machine_episode}.rs`
advances the fixed machine, injects original complex source currents and appends directed
kind-specific contrasts to the incident condition. `machine_source.rs` (advance + inject) is
the per-step form of the moment law and is kept. `machine_episode.rs` interposes the full
nonlinear word between occurrences and retains every occurrence's word as a reverse tape,
which rest serializes; that recurrence is the contamination named in the
[retention audit](research/records/2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md)
and is replaced by moment accumulation with one word on the joint field. Old slot/session
wires remain readable. [Return and scope](research/records/2026-09-21_ORDERED_SOURCE_AND_PHASE_RECEIVING_ENTER_THE_PUBLIC_GENERATOR_SESSION.md).
