# Holonics — Codex operating guide

Holonics is Brandon's mathematical, physical and computational framework. **HNN** is the machinery,
**Athena** its first intended product, and **Eros** the collective formative organization and the
composition within it. Brandon's latest direct request governs. This is Codex's guide; Claude uses [CLAUDE.md](CLAUDE.md), which states the same rules.

## The repository after the reset (September 24)

[project-postulate] The repository was reset on September 24 to what functions. Everything else is
in git history: the retired engine, the prototype HNN machine and its sessions, the applications,
campaign experiments, census documents and superseded guides. The last pre-reset tree is
[`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734). Port from it deliberately,
one law or kernel at a time, when a rebuild step needs it. Never restore wholesale.
[THE_REBUILD](docs/plans/THE_REBUILD.md) gives the order.

| Path | Role |
|---|---|
| `crates/holonics/` | The main library: the Holon law and its facets, ratio/ring arithmetic, geometry (frames, screws, winding), receivers, standing and release. It is reorganized into the operator layout in rebuild step 1. |
| `crates/holonics-cuda/` | The CUDA driver. The HNN's resident realization is rebuilt here after its law exists in `holonics`. |
| `lean/` | The Lean mathematics: the `ElementaryHolonics.Framework` foundation and the research umbrella. The declaration namespace and library split come in later steps. |
| `docs/` | The object and mathematics guides: [elementary objects](docs/ELEMENTARY_OBJECTS.md), [Holon](docs/HOLON.md), [notation](docs/HOLONIC_NOTATION.md), [the machine's formula](docs/HNN_FORMULA.md), winding, helical and fluid geometry, [formal framework](docs/FORMAL_FRAMEWORK.md), and the canon. |
| `research/` | Dated records (derivations, measurements, lessons), papers, design, notebook. |

## The line: compression is intelligence is navigation

[project-postulate] Brandon's slogan names the line the repository builds
([THE_REBUILD](docs/plans/THE_REBUILD.md#the-line-the-rebuild-serves)):
- Holonic Compression couples a fractal navigator's resonating modes with terrain (stuff in
  general).
- Landmark discovery locates the faces where navigator paths converge.
- The HNN executes both at scale.

RH, Hodge, complex Euler/Navier–Stokes and BSD are targets advanced enough to apply Holonics to.
They are never a separate "Millennium" category: work on them is landmark discovery and
compression in the same objects. Their Lean (`lean/ElementaryHolonics/{Millennium,RH,Mathematics,Computation}`)
stays attached to every rebuild step. A campaign names the navigators, terrain, kernel, cokernel
and landmarks it touches.

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
active/learned relations with their power, pumps), navigators with keys/clocks/phase lifts, and
scale restrictions. Receivers are Holons joined at ports; interconnected Holons form a Holon.
Passivity is proved, never assumed. The table below lists its facets. The Lean foundation and the
Rust core implement this object, and every native owner implements or charts it.

| Object | Dual / law |
|---|---|
| Complex | oriented cells, `∂²=0` |
| Holon `\|H⟩`: a continuing current/motion, already present as potential, never produced by a computation | coholon `⟨Ȟ\|`, `d=∂ᵀ`; face `⟨Ȟ\|H⟩`; Stokes `⟨dȞ,H⟩=⟨Ȟ,∂H⟩`; orientation exists only in the pairing |
| Constitution `Θ`: the material law relating a coholon to the motion it excites (capacitive `C=BᵀM_C B`, inverse-inductive `K=BᵀM_L B`, dissipation `D⪰0`) | modes `Kv=ω²Cv`, the two energies exchanging; motion = exact ⊕ coexact (induced) ⊕ harmonic (dormant) |
| Navigator `Ĝ` (fractal navigator; formerly "generator") with initial configuration and clock; helix = circle + carry; fractal family = words, restrictions, scale square, first arrival; a source word is its address | adjoint `Ĝ*` carries the learning covector; release at tolerance |
| Pair contact: slip `J`, `Q=⟨Δ\|Δ⟩`, `DQ=2J*Δ`, Farey lock address | contact material `ΣwJ*DJ` |
| Parametron: incidence, `C`, `L`, pump, half-turn sheets, Ising lock; a perceptron is its locked-sheet receiver face | storage↔flow exchange at `ω=1/√(LC)`; a section crossing is a clock tick |
| Tube (longitudinal clocked span) and tower (transverse restriction; gluing unique/plural/obstructed); world tube; `Λ_DN` eliminates an interior | holonomy only on declared circuits |
| Relatively complete region (globe): a boundary that bounds the interior, interior coupled to the exterior (conserved charges count) but not determined by it, with persistent interior motion | completeness is only relative to a receiver family; the full theorem is owed (#62) |
| Deposition: the only law changing a constitution, from covectors that actually reached that locus | retention is the future-sufficient quotient of the constitution (the constitution suffices but is not minimal), never a record of fluxes |
| Ratio: "one per two", a typed comparison of two Holons/coholons/transports carried as an undivided pair, with division-with-remainder, residue/modulo, inversion with its nonunit fibre, lift/carry and jets | `ℓ=log R` with winding branch; `R⁻¹dR`; its jet (velocity, acceleration, jerk, …); loss is `log Ĝ_(T←H)` |
| Receiver and receipt: a receiver is a role of a participating Holon; reception `I_C(\|H_S⟩,\|H_R⟩)=(\|H'_S⟩,\|H'_R⟩,f_R)` changes both and returns a receipt, a field of readings over a partition, each region in its own frame and clock | no global scalar or global gradient; per-region variability over its own ticks, joined to interface flux |
| Holarchy: what `interconnect` returns; the joined whole with its retained constituents, incidence, gluing and restrictions (or a typed gluing defect) | quantities belong to the receiver: `view(receiver, grain, clock)`; `count` only under a certified finite partition; one continuing whole, many receiver-relative counts |
| Holonic Compression: a fractal navigator's resonating modes coupled with terrain; a codec pivot carrying its decoder | kernel: differences no admitted future receiver distinguishes, whose quotient is retention; cokernel: the residual emanated or retained; landmarks: faces where navigator paths converge |
| Aeon (a container of causality in time, part of a Holarchy's parametric orientation), epoch (a division of an aeon at a receiver's section), cycle (a closed loop; completeness, not duration) | elapsed time is the pairing `⟨ω_R\|γ⟩ = windings + phase`; no privileged clock; epochs count flux through the receiver's section; cycles read conserved whole windings |

[definition] Retire these phrasings: bare "standing" for the constitution, and "terrain" as a
synonym for it (terrain is stuff in general: whatever a navigator meets); "generator" for the
object, which is a navigator (the algebraic senses remain); "a
current changes a later current's standing" as a definition of learning; a constitution
"turning" a coholon "into" a Holon; a single scalar of progress; and any tape, journal or
frozen cut as retention. For time, use aeon, epoch and cycle
([record](research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md));
retire "session" and "episode", and do not use `epoch`, `cycle` or `generations` for a
program-chosen counter or iteration count.

[project-postulate] **Keys and navigation.** Every action is a key: an action expression and its
antecedents induce a consequence as flux only when they fit a constitution (the lock). The
Enigma/Bombe reading is literal: rotors are parametron rings whose stepping is winding with
carry, fixed material and reflector return through the producing operands, the key is the
navigators' initial configuration, and the Bombe infers it by pairwise loop closure over the
menu of contacts. Dormant modes wait for a fitting antecedent. **Learning is locating keys** —
inferring configuration and gauge of relevant navigators from loop-closure constraints, which is
compression (pruning) and navigation (the route). Resonating drives an existing mode at its
eigenfrequency (RIDE); emanating founds or drives off-resonance (FOUND). The inference is
general; no cryptanalytic application is pursued.

## The object's governing laws

[definition] **Retention is a quotient sufficient for the admitted future**
(`Foundation/Standing.lean`, `holonics::receiver::standing`); it is never an event archive, tape, journal,
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

[definition] "Soulkiller" is a name only (borrowed from a game); it determines no mathematics.
Its subject is **equation extraction**: reading a foreign realization's operators and coefficients
as element relations, interconnection and navigators of a Holon, so the extracted equations are
native objects. Name types and designs after the extracted-equation facet they carry.

## Work practice

[project-postulate] **Ownership and retirement** (Brandon, September 23). This repository is Brandon's
personal research programme; Brandon, Claude and Codex are its only workers, and every file in the
tree, committed or not, is ours to account for. Consolidation includes deletion: code, examples,
Lean and documents that are superseded, unconsumed or outdated are removed, and git history is the
archive. Old names, compatibility aliases and legacy save-format decoders go: an old save is a
superseded prototype (Brandon, September 23). "Keep all mathematics"
means keep each law once, in its owner, with its consumer, not every representation of it.

[definition] The repository is public; `.local/` contains private datasets, captures, models and
run artifacts. Publish source and scoped evidence without raw private conversation or source
paths. Dataset roles and provenance are exterior codec information, not native semantic IDs.
The current application position and next action live only in CONSTRUCTION_STATE and the roadmap.

[project-postulate] Claude delegates to at most **three Opus 5.5 workers** on disjoint owner paths,
then **one Opus 5.5 reviewer that spawns nothing**; use fewer workers when the work does not split,
and a sequential join when it consumes multiple returns. Every prompt supplies this guide, the
machine/source material, exact paths, existing owners, equations, consumer and relevant receipts.
The primary inspects source and
integrates returned changes; worker measurements are reusable receipts.

[project-postulate] Each campaign has a GitHub issue (restructure parent #63; construction
#72–#76; formal obligations #62) and cites it in its plan and commits (`Refs #n` / `Closes #n`).
Close it with the commit, the verification and the remaining scope.

Commands below use Bash; invoke Bash explicitly if the active shell is fish. CUDA may need
`PATH=/opt/cuda/bin:$PATH`. The gates, lowest first:

1. any code change: `cargo check --workspace --all-targets`;
2. once per step or PR: the host suite of each changed crate, `cargo test -p <crate>`;
3. at the end of a step that changes HNN behaviour or a kernel: the GPU suite, alone on an idle
   card, `flock .local/gpu.lock cargo test -p <crate> -- --include-ignored --test-threads=1`;
4. when Lean changes: the library build, `bash tools/lean_check.sh`.

Record one verification receipt per step, in its PR or issue, not one per check. A timeout is incomplete evidence. A native packet that adds or changes a mathematical
law lands with its Lean counterpart under the matching `Framework` entry point, or names the
obligation it leaves in #62.
