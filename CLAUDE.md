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

## Repository restructure in progress

[project-postulate] Brandon's September 23 intervention follows
[THE_REPOSITORY_RESTRUCTURE](docs/plans/THE_REPOSITORY_RESTRUCTURE.md). The owner paths below
describe today's tree until a verified move lands. The substantive main `holonics` library
will own the Holon, exact geometry, elementary operations and the backend-neutral `hnn` law
and execution port. `holonics-cuda` receives the device-resident HNN as it is and implements the
port; `holonics-apple` (later, on Brandon's branch) implements it for Apple silicon. `holonic-words`
stays a separate `no_std` crate only while a Rust device kernel consumes it; otherwise its rings fold
into `holonics::ratio`. Main builds without CUDA; its HNN host reference is construction campaign
K2, not a precondition of the move. Lean becomes one Lake package with `Holonics` and dependent
`HolonicsResearch`. Moving its paths and changing the current `Soma.Holonics` declaration
namespace are separate checked phases.
The proposed internal operator order is ratio/remainder/inversion, geometric transport,
the Holon law and its pair/tube operations, receiver-relative Holarchy, then HNN;
the complex parametron is an HNN physical chart, not a prerequisite of every Holon.
The main library's fluid, wave, Einstein/stress-energy and thermal instances retain their
constitutive equations, clocks, heat/entropy balances and participating receiver. Cross-entropy
acts physically only through a stated material/port return; its scalar face is not that law.

[definition] Each moved operator retains its typed source and receiver, forward law, complete
variation, material/clock/frame hypotheses and consuming call. Account for the uncommitted
research and paused worktrees in R0 before retirement. **Lean holds the mathematics; Rust holds
what runs:** unconsumed Rust is deleted after any law it alone states moves to Lean or a guide;
checked Lean theorems stay unless duplicate or wrappers. A move updates its in-repo callers in
the same commit, with no forwarding modules or aliases; every old save-format reader goes
(an old save is a superseded prototype). The restructure moves existing behavior; new objects (Holarchy,
active receive, physics instances, HNN host reference) are separate construction campaigns
(plan §0, §4). Do not present target names as existing code. The restructure is tracked in
GitHub #63 (steps #64–#71, construction #72–#76). Every campaign cites its issue in its plan
and commits (`Refs #n`/`Closes #n`), and closes it with the commit, verification receipt and
remaining scope.

## The elementary objects — the only design vocabulary

[project-postulate] Brandon, September 22: design, worker briefs, formal work and code state
their operations **only** in the [elementary objects](docs/ELEMENTARY_OBJECTS.md), which own the
definitions, the [operator contract](docs/ELEMENTARY_OBJECTS.md#operator-contract) (operations, current and target owners); `ElementaryHolonics.Framework.Objects` imports them
and the proved joins in `Objects/{Pairing,Deposition,Ratio,Parametron,RelativeCompleteness}`. A text, image, acoustic, motor or arithmetic
application is a boundary chart of them. A noun that is not one of them, or a composition of
them, is a design defect. The picture: a continuing field of chains of **complex parametrons**
(annular rings that store, oscillate and lock) joined by **helical pair contacts** (which slip,
dissipate and address); rings rotate and align, contacts converge and diverge action.

[definition] **The Holon as one object** ([guide](docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object)): the
law and its ports, not its state — `H=(K,∂_A; Π; 𝒟; 𝓔; G; π)`: complex with connection-valued
incidence, ports carrying flow/effort pairs whose pairing is power, a power-neutral interconnection
(Dirac) structure, element relations (the constitution: storage, resistive contacts, sources,
active/learned relations with their power, pumps), generators with keys/clocks/phase lifts, and
scale restrictions. Receivers are Holons joined at ports; interconnected Holons form a Holon.
Passivity is proved, never assumed. The table below lists its facets. The Lean foundation and the
Rust core implement this object, and every native owner implements or charts it.

| Object | Dual / law |
|---|---|
| Complex | oriented cells, `∂²=0` |
| Holon `\|H⟩`: a continuing current/motion, already present as potential, never produced by a computation | coholon `⟨Ȟ\|`, `d=∂ᵀ`; face `⟨Ȟ\|H⟩`; Stokes `⟨dȞ,H⟩=⟨Ȟ,∂H⟩`; orientation exists only in the pairing |
| Constitution `Θ`: the material law relating a coholon to the motion it excites (capacitive `C=BᵀM_C B`, inverse-inductive `K=BᵀM_L B`, dissipation `D⪰0`) | modes `Kv=ω²Cv`, the two energies exchanging; motion = exact ⊕ coexact (induced) ⊕ harmonic (dormant) |
| Generator `Ĝ` with initial configuration and clock; helix = circle + carry; fractal family = words, restrictions, scale square, first arrival; a source word is its address | adjoint `Ĝ*` carries the learning covector; release at tolerance |
| Pair contact: slip `J`, `Q=⟨Δ\|Δ⟩`, `DQ=2J*Δ`, Farey lock address | contact material `ΣwJ*DJ` |
| Parametron: incidence, `C`, `L`, pump, half-turn sheets, Ising lock; a perceptron is its locked-sheet receiver face | storage↔flow exchange at `ω=1/√(LC)`; a section crossing is a clock tick |
| Tube (longitudinal clocked span) and tower (transverse restriction; gluing unique/plural/obstructed); world tube; `Λ_DN` eliminates an interior | holonomy only on declared circuits |
| Relatively complete region (globe): a boundary that bounds the interior, interior coupled to the exterior (conserved charges count) but not determined by it, with persistent interior motion | completeness is only relative to a receiver family; the full theorem is owed (#62) |
| Deposition: the only law changing a constitution, from covectors that actually reached that locus | retention is the future-sufficient quotient of the constitution (the constitution suffices but is not minimal), never a record of fluxes |
| Ratio: "one per two", a typed comparison of two Holons/coholons/transports carried as an undivided pair, with division-with-remainder, residue/modulo, inversion with its nonunit fibre, lift/carry and jets | `ℓ=log R` with winding branch; `R⁻¹dR`; its jet (velocity, acceleration, jerk, …); loss is `log Ĝ_(T←H)` |
| Receiver and receipt: a receiver is a role of a participating Holon; reception `I_C(\|H_S⟩,\|H_R⟩)=(\|H'_S⟩,\|H'_R⟩,f_R)` changes both and returns a receipt, a field of readings over a partition, each region in its own frame and clock | no global scalar or global gradient; per-region variability over its own ticks, joined to interface flux |
| Holarchy: what `interconnect` returns; the joined whole with its retained constituents, incidence, gluing and restrictions (or a typed gluing defect) | quantities belong to the receiver: `view(receiver, grain, clock)`; `count` only under a certified finite partition; one continuing whole, many receiver-relative counts |

[definition] Retire these phrasings: "terrain" and bare "standing" for the constitution; "a
current changes a later current's standing" as a definition of learning; a constitution
"turning" a coholon "into" a Holon; a single scalar of progress; and any tape, journal or
frozen cut as retention.

[project-postulate] **Keys and navigation.** Every action is a key: an action expression and its
antecedents induce a consequence as flux only when they fit a constitution (the lock). The
Enigma/Bombe reading is literal: rotors are parametron rings whose stepping is winding with
carry, fixed material and reflector return through the producing operands, the key is the
generators' initial configuration, and the Bombe infers it by pairwise loop closure over the
menu of contacts. Dormant modes wait for a fitting antecedent. **Learning is locating keys** —
inferring configuration and gauge of relevant generators from loop-closure constraints, which is
compression (pruning) and navigation (the route). Resonating drives an existing mode at its
eigenfrequency (RIDE); emanating founds or drives off-resonance (FOUND). The inference is
general; no cryptanalytic application is pursued.

## 1. The object and its equations

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
no tape; a comparison observed after an update is read through the contemporary constitution
and returns its residual. The [retention audit](research/records/2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md)
names the objects this replaces. Read `Foundation/Standing.lean`, the
[prediction/release record](research/records/2026-09-12_PREDICTION_IS_PREPARED_TRANSPORT_AND_RELEASE_IS_BOUNDARY_CURRENT.md)
and the [source audit](research/records/2026-09-21_SITUATED_GENERATORS_RETAIN_MODES_AND_RELEASE_ACTION.md)
when working on recall, relevance, homeostasis or action inference.

[project-postulate] HNN is one continuing geometric field: circulating phase modes, interlinked
toroidal domains, helical passages, active contacts and participating receivers. A Holon `|H⟩_F`
carries incidence K, material Θ, joint currents/modes and interior storage in frame F; it is a whole
and a part simultaneously. The geometry is how information is carried, compared, transformed and
learned. Every value is a situated comparison; its source, orientation and receiving scope remain.
The full theory-of-everything ambition and consumer-hardware usefulness guide the construction.

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
Pair contact     J=[v_a|−v_b], DQ=2J*Δ, D²Q=2J*J+2diag(Δ·a_a,−Δ·a_b); M_contact=Σw J*DJ; PSD: P=0 ⇔ D J u=0; definite on slip image: ⇔ ṡv_a=ṫv_b
Phase carriage   R_d=S⁻ᵈPSᵈ; return A⁻¹FA; n uniform steps through fixed P compose to (PS⁻¹)ⁿSⁿ; menu loop closes ⇔ stage word fixes S a
Source/receiver  m_g=Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k), M_gh(δ) pair relation at offset δ; y_j=ρ_R(Ĝ(j)q); helix = winding-retaining lift
Carry            x=phase+n·winding; winding(x+y)=winding x+winding y+carry; carry is a cocycle; Sⁿ=C ⇒ S^(d+nk)=S^d·C^k
Lock and address q·v_a=p·v_b ⇔ no-slip (zero power under definite response); neighbours ⇔ p'q−pq'=1; mediant is the cheapest lock between; word in ⟨step, inversion⟩
Trace faces      (S⁻ᵈPSᵈ)ᵏ=S⁻ᵈPᵏSᵈ; det, tr(Mᵏ), det(1−T·M) conserved; block-diagonal machine: ∏(1−a_gT+q_gT²), Σ tr(M_gᵏ); SiteKind::Rotation ⇔ a²<4q
Cell holonomy    H=g₀₁g₁₂g₂₀ ↦ k₀⁻¹Hk₀; d₁(A+d₀φ)=d₁A; harmonic ⇒ silent at node/cell receivers; harmonic potential = 0; retained by its class
Participation    T_F[Ψ]=Σ_G a_FG[Ψ] U_(F←G)[Ψ] Ψ_G over admitted contacts
Phase chart      s_ij=β cos(2π(q_i−q_j−φ_ij)), a=softmax(s); the pair receiver at zero advance and unit radii, connection φ
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

[definition] **Loss is the logarithm of a ratio of Holons.** The comparison is between two
Holons in one frame: the produced `|H⟩` and the target `|T⟩`, encoded through the same `E` and
phase transport as the source. Their ratio is the relative transport `R=Ĝ_(T←H)`: an amplitude
ratio `ψ_T/ψ_H` on a receiving face, `A_H⁻¹A_T` on a material block, `g_H⁻¹g_T` on a pair. The loss
is `ℓ=log R` in the additive chart (softmax/exp is that chart transition, `exponentiated_ratio`),
with the winding kept as the branch of the log: `log(ψ_T/ψ_H)=½log(q/p)+i(φ_T−φ_H+2πn)`. Its
calculus is the logarithmic derivative `R⁻¹dR`, which is the learning covector; `p−q` is only
its real, codec-chart part. Scalars such as `E_p[ℓ]` (lifted cross-entropy, i.e. KL bits plus
phase excess), `tr log R=log det R`, a pair twist in rad/m or `dℓ/dn` in bits per observation are
limit readings of the ratio with units. They are valid measurements. They are not the operand the
adjoint pulls back, and they are not the retained state. Classical cross-entropy alone is
insufficient. [Contract](docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#holonic-loss-is-the-logarithm-of-a-holon-ratio).

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
channels, unit-current inputs/targets and per-slot basis decoding. The incident Athena geometry
(`examples/support/linked_torus_field.rs`) assigns one ring junction per source cell, with a
one-hot encoder and per-slot faces. `holonics-hna` now imports the screw/pair-interaction owners
(`field_geometry/machine.rs`); chain, standing, release, `exponentiated_ratio`,
`receiver_history_compression`, `kernel_modes` and `HelicalMomentReuse` are still unconsumed. Both are numerical application controls that
the generator machine replaces; `HelicalMomentReuse` is a separate caller. The next
encoder/decoder work follows the
[existing Holonic Encoding construction](research/records/2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md)
and the [campaign correction](research/records/2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md#correction-the-nibble-control-is-not-holonic-encoding).

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
records the implemented composition: standing q/incident Delta feed the reaction, participation supplies
drive y, and one global D/b acts on their sum. Source/text/support maps are boundary material
with stated priors and the same normal update. The contract contains the complete adjoint,
publication, rest and source-episode packets. These are implemented constituents of the shared
operation; the text/support chart is one application. Continue from those returns through the
roadmap's packets: pair contact and serial chain, the generator-machine geometry, closure
inference with standing/release, then economy and episodes, preserving the original target
port and source fibre.

## 2. Where the implementation lives

| Operation | Source owner |
|---|---|
| Public model and move owner | `crates/holonics-hna/src/native.rs`; `native/coupled_wave/body/field.rs`, `field/section.rs`; `NativeCoupledBody` |
| Session, region preparation and observed return | `crates/holonics-hna/src/native/field_session.rs`, `field_session/{incidence,native_source}.rs` attaches an actual field and derives pre-target source/incident contrasts; `{shared,geometric}.rs` retains the text/control callers; `body/field/{formation,geometric,incident}.rs` owns formation, geometric refinement and the complete incident q/Delta word; `field_session/mathematical_port.rs` joins scoped workshop products to the same field |
| Real source and its comparison/cursor | `crates/holonics-hna/src/alpha/exposure.rs`, `examples/athena_exposure_field.rs`; [conversation data](docs/CONVERSATION_DATA.md) |
| Constitutive field and paired source/current | `crates/holonic-engine/src/native_ecology/constitutive_fibre/field/`: operative/source/{action,map_action,reflection_commit}.rs and operative/factor_return.rs own sparse D/D*, the full joint return and current publication; normal/direct owns E/R/support priors and material statistics |
| Normalization and adjoints | `field/receiver/normalized{,.rs}`, `normalized/phase.rs`, `field/material_transport/normal/direct/section{,/composition}.rs`, `resident/section/bilinear_features.rs`; exact reference `exponentiated_ratio::transport::NormalizedKernel` |
| Kernels and their Rust binders | `crates/holonic-engine/kernels/{exact_resident_section.cu,field_normalized_receiver.cuh,normal_applied_condition.cuh,section_bilinear_adjoint.cuh}`; `src/resident_section/` |
| Hardware law | `hardware_cover`, `section_partition`; `crates/holonics-cuda/src/{cuda,launch_law,section_layout}.rs` |
| Exact geometry and helical pair | `crates/relational-geometry/src/{exact,model,screw,exact_analysis}.rs`; `holonic-engine/src/{identity_atlas,exact_contact,holonic_interaction,holonic_chain}.rs`; `receiver_history_compression/observable.rs::HelicalMomentReuse` binds finite pair actions to the existing moment decoder. `holonic_interaction/helical.rs` now joins `ScrewPair` to the checked `HolonicInteraction` with an explicit rate port; `holonic_chain/serial.rs` supplies exact Cayley/prismatic chains, contact rows and constrained target fibres. `Transport/{HelicalPairInteraction,SerialScrewChain}.lean` owns their checked algebra; the full HNN generator-machine binding remains #17 |
| Winding, carry, address, trace faces and cell holonomy | Lean `Geometry/{PhaseCarry,PairResonance}`, `Transport/{GeneratorTraceFaces,CellHolonomy}` over the existing `Millennium/{Farey,LocalFactor,TraceSequence,HodgeIndex,PlaceLedger,WindingLedger}`, `RH/{FosterTanks,HeatFlowStackedSeam}`, `Foundation/{HodgeReceiver,IwasawaTower,FractalPacking}`; Rust `crates/relational-geometry/src/winding.rs` (`Odometer`, `LockAddress`, `SiteFactor`, `Machine`, `triangle_holonomy`) |
| Algebra and economical continuation | `exact_linear`, `prime_image_algebra`, `receiver_history_compression`, `winding_inertia`; resident bilinear/normal/word/mode owners at their separate call boundaries |
| Retained availability and predictive release | `holonic-engine/src/{standing,receiver_release}.rs`, `exact_linear/{contextual,kernel_modes}.rs`; `field/internal_mode.rs` retains the equal-drive specialization and explicitly refuses incompatible operative currents; `Foundation/{Standing,CausalRelevance,ReceiverHistoryCompression}.lean` supplies future sufficiency |
| Public framework | `crates/holonics/src/lib.rs`: `geometry` and `structure` without default native features; `holonics-hna` for HNN |
| Lean | `formal/elementary-holonics/ElementaryHolonics/Framework.lean` and its Core/Geometry/Dynamics/Information/Physics/Computation entry points. Core imports `Foundation/{Standing,ReceiverRelease}`; Dynamics imports `Transport/{HolonicInteraction,HolonicChain,ContinuingTube,HelicalPairInteraction}`. #62 lists the formal counterparts owed by the current design |
| Applications and evidence | `applications/holonics-workbench`, `applications/conversation-data`; `research/{records,experiments,papers,notebook}`; [layout](docs/REPOSITORY.md) |

[definition] The implemented incident mode uses standing q and transported differences Delta
for Phi, with participation as the separate drive. Its global state contains one q and one b.
Nonzero normal priors initialize both the applied W0 and H0/B0/C0; observed energy is Q_data.
A delayed comparison owns its producing operands (moment, phases, covector, material cut id),
not a replayable frozen cut of earlier material; the implemented frozen-cut replay is retired
with the tape. The [incident-field implementation return](research/records/2026-09-21_THE_INCIDENT_FIELD_JOINS_ITS_GENERATOR_RECEIVER_AND_FROZEN_RETURN.md)
connects these calls and their measured scope; the live state tracks the full application.

[definition] The incident text interface fixes `response_port_start` independently of request
length, using the same receiving slots in generation, comparison and rest. Fresh sessions
reserve the final receiving aperture. Native real-potential order determines nominal text and
support selections, retaining each text row's own radius; normalized faces serve the paired
comparison. Earlier saved source-relative layouts retain their recorded binding.

[definition] **Enclosure ABI:** sealed low/high carrier words can encode a definite centre and
an independently nonzero radius. Equality of those words is not a zero-radius test. Read the row
layout, grain, denominator and radius slot before judging propagation or refusal. The native
normal and normalized-receiver section tests exercise nonzero source/condition/covector radii.

[definition] A kernel using `upstream_refused` supplies a complete `SLOT_WORDS` receipt
(16 u32 words), including lineage fields. Independent rows own those complete receipts until
their deterministic barrier joins the statuses. Host allocations, kernel stride and logical
placement use that same layout; `resident_section::SLOT_WORDS` is the Rust owner.

[definition] A ready native upload includes device completion. Pageable host-to-device copies
can return after host staging; synchronous `holonics-cuda` slice/range methods complete the
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

- **Winding/carry/placement:** the [winding guide](docs/WINDING_CARRY_AND_PLACEMENT.md) first;
  then `PhaseCarry`, `PairResonance`, `GeneratorTraceFaces`, `CellHolonomy` and the
  `Millennium/`/`RH/` owners it names. Use its §8 operand list when stating a design.
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
and [interoperability](docs/INTEROPERABILITY.md) define those interfaces. Rename or retire API/wire names under the ownership rule below.

[definition] "Soulkiller" is a name only (borrowed from a game); it determines no mathematics.
Its subject is **equation extraction**: reading a foreign realization's operators and coefficients
as element relations, interconnection and generators of a Holon, so the extracted equations are
native objects. Name types and designs after the extracted-equation facet they carry.

## 4. Work, verify and document the return

[project-postulate] Resolve routine choices from the mathematics, annotate inferred choices with
their reason, and proceed. Implement the relation and its actual consumer together. Stage changes
under one move owner; use the producing material for its adjoint and publish the successor when
its return succeeds. Inspect the generated result and measured cost at the declared receiver.
A scalar reading is a limit face of a ratio with its source, units and population; it is a valid measurement, not the adjoint's operand or intrinsic identity.

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
cultivation/inference. A native packet that adds or changes a mathematical law lands with its
Lean counterpart under the matching `Framework` entry point, or names the obligation it leaves
in #62; formal work is part of the packet, not a later pass. The normal Lake default is `ElementaryHolonics.Framework`, not the complete
research umbrella. Timeouts remain incomplete evidence.

[project-postulate] Claude delegates to at most **three Opus 5.5 workers** on disjoint owner paths,
then **one Opus 5.5 reviewer that spawns nothing**; use fewer workers when the work does not split,
and a sequential join when it consumes multiple returns. Every prompt supplies this guide, the
machine/source material, exact paths, existing owners, equations, consumer and relevant receipts.
[WORKER_BRIEF](docs/WORKER_BRIEF.md) has the concrete template. The primary inspects source and
integrates returned changes; worker measurements are reusable receipts.

[project-postulate] **Ownership and retirement** (Brandon, September 23). This repository is Brandon's
personal research programme; Brandon, Claude and Codex are its only workers, and every file in the
tree, committed or not, is ours to account for. Consolidation includes deletion: code, examples,
Lean and documents that are superseded, unconsumed or outdated are removed, and git history is the
archive. Old names, compatibility aliases and legacy save-format decoders go: an old save is a
superseded prototype (Brandon, September 23). "Keep all mathematics"
means keep each law once, in its owner, with its consumer, not every representation of it.

[project-postulate] Stage and format explicit paths; preserve
in-progress work until it is accounted for. Retire by explicit deletion, never by a broad
restore/reset/stash/clean. Constructors and remounts validate carrying values, checked extents precede work,
and exact growth is handled by rebase/factor/representation change with its decoder and residual.
Commit and push coherent verified work on the task's branch. If adding a co-author credit, use
actual attribution rather than a hardcoded model name.

[definition] The repository is public; `.local/` contains private datasets, captures, models and
run artifacts. Publish source and scoped evidence without raw private conversation or source
paths. Dataset roles and provenance are exterior codec information, not native semantic IDs.
The current application position and next action live only in CONSTRUCTION_STATE and the roadmap.

[established-bounded; source-inspected] The [first campaign return](research/records/2026-09-21_PAIR_CONTACT_SERIAL_KINEMATICS_AND_THE_RESIDENT_QUADRANCE_RETURN.md)
implements the exact pair-contact adapter and Cayley/prismatic serial chain with their formal
laws. `NativePairParticipation` executes the quadrance score with separate geometry/value
covectors on the device; `IncidentParticipationChart::QuadranceCurrent` binds the explicit
same-current specialization into the existing HNN word and rest. Legacy bilinear mode remains
the default. These are dependencies of the fixed generator/source/phase machine, whose actual
configuration/current maps and phase reception now have a body consumer; ordered source/session
binding has returned through the public generator session.

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
