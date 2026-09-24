# Holonics — Codex operating guide

This is Codex's guide. Claude uses [CLAUDE.md](CLAUDE.md), which states the same laws and practice with its own delegation rule.

Holonics is Brandon's mathematical, physical and computational framework. **HNN** is the
machinery, **Athena** its first intended product, and **Eros** the collective formative
organization and the composition within it. These names, like Hephaestus, carry no machinery.
The full theory-of-everything ambition, and usefulness on consumer hardware (the 20 W ideal,
frontier-level usefulness), guide the construction. Brandon's latest direct request governs.

Read [THE_MACHINE](docs/THE_MACHINE.md), the [elementary objects](docs/ELEMENTARY_OBJECTS.md),
[CONSTRUCTION_STATE](CONSTRUCTION_STATE.md) and [THE_REBUILD](docs/plans/THE_REBUILD.md) once per
task, and keep what you have already read. Worker prompts name this guide and the exact material
to read.

## The repository after the reset (September 24)

[project-postulate] The repository was reset on September 24 to what functions. Everything else is
in git history: the retired engine, the prototype HNN machine and its sessions, the applications,
campaign experiments, census documents and superseded guides.
- The last pre-reset tree is [`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734).
- Worktree and branch leftovers are on `archive/leftovers-2026-09-24`.
- Brandon's Metal port is on `codex/apple-silicon`.

Port from history deliberately, one law or kernel at a time, when a rebuild step needs it. Never
restore wholesale. [THE_REBUILD](docs/plans/THE_REBUILD.md) gives the order.

| Path | Role |
|---|---|
| `crates/holonics/` | The main library: the Holon law and its facets, ratio/ring arithmetic, geometry (frames, screws, winding), navigators, receivers, standing and release. Rebuild step 1 reorganizes it into the operator layout. |
| `crates/holonics-cuda/` | The CUDA driver. The HNN's resident realization is rebuilt here after its law exists in `holonics`. |
| `lean/` | The Lean package `holonics`: library `Holonics` (the `Framework` closure, the default target) and `HolonicsResearch` (the rest), namespace `Holonics`. |
| `docs/` | The object and mathematics guides and the canon. The canon is historical doctrine; the elementary objects govern its wording. |
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
compression in the same objects. Their Lean (`Millennium`, `RH`, `Mathematics`, `Computation` under `lean/Holonics/` and `lean/HolonicsResearch/`)
stays attached to every rebuild step. A campaign names the navigators, terrain, kernel, cokernel
and landmarks it touches.

## The elementary objects — the only design vocabulary

[project-postulate] Brandon, September 22: design, worker briefs, formal work and code state
their operations **only** in the [elementary objects](docs/ELEMENTARY_OBJECTS.md), which own the
definitions, the [operator contract](docs/ELEMENTARY_OBJECTS.md#operator-contract) (operations, current and target owners); `Holonics.Framework.Objects` imports them
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
| Swing: the primitive act of situated relating and transport; its frozen-board chart is the point reflection about an anchor, `S_a x=2a−x` (a half-turn, `e^{iπ}` about `a`); the clocked pantographic Swing keeps the fibre of inner Swings and their ticks | two Swings compose to a translation, `S_b S_a x=x+2(b−a)`; a tick is an oriented crossing of a section; Lean `Geometry/{AffineSwing,SwingPotential}`, `HolonicClockedPantographicSwing` |
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

[definition] **Exact arithmetic; no floats inside the machinery.** This is a law of the
mathematics, not a style.
- Values are exact: ratios with their remainder, and integers carried with their factorization
  (`13122 = 2·3⁸`, `729 = 3⁶`), never as bare magnitudes.
- Algebraic and transcendental quantities are their constraint identities. π and `e` are
  navigators; a float is a face of one, and error enters only in how a face is attained.
- Estimation is replaced by partition.
- A float appears only at an exterior boundary: matching external data, or reading a measurement
  for a person. Nothing inside a law, an owner or the HNN consumes one.
- A percentage is a rate, which is motion; state the motion.
- No unjustified literal or magic number enters a law.

[definition] **Retention is a quotient sufficient for the admitted future**
(`Foundation/Standing.lean`, `holonics::receiver::standing`). It is never an event archive, tape,
journal, ledger, or frozen producing cut kept for replay. "A current changes the standing a later
current meets" is a consequence of that law, not the definition of learning. Do not derive from it
a per-occurrence state chain, its adjoint tape, frozen cuts, or a fold over an update list. The
source passage enters as phase-carried moments `m_g=Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)`, whose adjoint needs
no tape. A comparison observed after an update is read through the contemporary constitution and
returns its residual. The [retention audit](research/records/2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md)
names the objects this replaces.

[definition] **Learning uses the covector of a declared comparison.** With prediction `p` and
target `q`, `p−q` is the cross-entropy logit gradient and `q−p` its descent covector. The paired
adjoint uses the operands that produced the forward carriers.

[definition] **Loss is the logarithm of a ratio of Holons** ([ratio](docs/ELEMENTARY_OBJECTS.md#9-ratio)).
- The comparison is between the produced `|H⟩` and the target `|T⟩`, encoded through the same `E`
  and phase transport as the source.
- Their ratio is the relative transport `R=Ĝ_(T←H)`. It is an amplitude ratio `ψ_T/ψ_H` on a
  receiving face, `A_H⁻¹A_T` on a material block, and `g_H⁻¹g_T` on a pair.
- The loss is `ℓ=log R` in the additive chart. Its winding is the branch of the log:
  `log(ψ_T/ψ_H)=½log(q/p)+i(φ_T−φ_H+2πn)`.
- Its calculus is the logarithmic derivative `R⁻¹dR`, which is the learning covector. `p−q` is only
  its real, codec-chart part.
- Scalars (lifted cross-entropy, `log det R`, a twist in rad/m, bits per observation) are limit
  readings of the ratio, with units. They are valid measurements, but they are neither the operand
  the adjoint pulls back nor the retained state. Classical cross-entropy alone is insufficient.

[definition] **Cross-entropy is physical.** It is flux across crossing sections and axes of time,
not a statistic.
- Along a passage `γ`, entropy production is `σ = D(P_γ‖P_{Rγ})` (aeon A6).
- The free energy of `p` over the equilibrium `q` is `F(p)−F(q)=k_BT·D(p‖q)`.
- Along a clock `λ`, both participants move:
  `d/dλ H(p,q) = −Σ ṗ log q − Σ p q̇/q`.
- A single cross-entropy number is a face of that flux.
- The fluid, wave, Einstein/stress-energy and thermal instances keep their constitutive equations,
  clocks, heat/entropy balances and participating receiver.

[definition] **Exact representation** keeps constraints, branch, units, winding and remainder.
Periodic closure also needs a period/commensurability relation: an exact rational or algebraic
phase can have nonperiodic transport. When a value outgrows its carrier, it is rebased, factored or
re-represented with its decoder and residual. The [helical guide](docs/HELICAL_GEOMETRY.md) and the
[constraint-mode guide](docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md) supply the cases.

[definition] **Notation and context** ([Holonic notation](docs/HOLONIC_NOTATION.md)).
- Notation uses typed kets, bras, faces and frame transports, with upper and lower tensor ports and
  an explicit metric.
- A binary state is a polarized side reading in a declared frame. `−1=e^{iπ}` and `i=e^{iπ/2}`
  enact half- and quarter-turns, and neighbouring passages are `A_↗`, `A_↘`.
- An abstract expression is unoriented until it is framed.
- Context is actual incidence, current, material and storage, local clocks, and the interior
  return that continuation needs.
- A limited observation may keep a plural Preimage Fibre, without a perfect inverse or an event
  archive.

[definition] **Generation and action.** Generation starts from the situated navigator/action
relation: the known source family, the admitted controls, the participating receiver, and the
requested consequence. It refines a joint field and releases its boundary, not a sequence of
tokens. Text, image, acoustic and motor releases are applications of that relation. Robotics is an
intended HNN capability, and its motor chart is serial screw words.

[definition] **Languages are applications.** Lean, and every programming or natural language, is
data to the HNN. No Lean parser, kernel call, theorem emitter, template or verdict enters the HNN.
Lean verifies mathematics outside it.

[definition] **"Soulkiller" is a name only** (borrowed from a game). Its subject is **equation
extraction**: reading a foreign realization's operators and coefficients as the element relations,
interconnection and navigators of a Holon, so that the extracted equations are native objects.

[definition] **Hardware law.** Co-present regions execute together when their complete read/write,
lineage, obstruction and resource effects commute.
- Shared immutable input with disjoint staged output is one sufficient pattern. Mutable overlap
  needs its actual interchange or reduction law.
- Certify the partition, read the device capacity, derive layout and launch, and keep the current
  on the card.
- One block per row with one active thread, one thread looping over all rows, and parallel work
  within a row are different realizations. Report the actual one.

## Work practice

[project-postulate] **Recover before implementing.** Before proposing a mechanism, or saying that
something is absent, search for the subject **and** its operations in:
- the [expression atlas](docs/atlas/README.md) first: about 2,200 derived expressions, identities,
  bounds and barring counterexamples, stated on the objects with their owners
  (`rg -i '<object|operation|classical name>' docs/atlas/`);
- `docs/` and `research/records/` (its [README](research/records/README.md) routes subjects);
- `lean/` and `crates/`;
- history, with `git grep -i '<term>' 13f8c734`.

Read the matched record and its actual owner or caller. A search hit is not a join. Name the
existing owner and the concrete missing term. A change that adds, moves or retires an owner updates
its atlas rows in the same commit.

[project-postulate] **Decide from the mathematics.** Resolve routine choices from the mathematics,
mark an inferred choice with its reason (`agent-inferred`), and proceed. Never hand Brandon a
decision that the framework settles, and never hedge finished work with a queue of "next" items.
Implement a relation together with its consumer, stated as an equation at the consumer: for
example `decode(T_native(encode x))=T(x)`, `E_next T=U E`, `D E=ρ`, or the complete residual.

[project-postulate] **Lean holds the mathematics; Rust holds what runs.** Unconsumed Rust is deleted
once any law that only it states has moved to Lean or a guide. A target name in the operator
contract is not existing code until its owner is built.

[project-postulate] **Ownership and retirement** (Brandon, September 23). This repository is
Brandon's personal research programme; Brandon, Claude and Codex are its only workers, and every
file in the tree, committed or not, is ours to account for.
- Consolidation includes deletion. Superseded, unconsumed or outdated code, Lean and documents are
  removed, and git history is the archive.
- Old names, compatibility aliases and legacy save-format decoders go: an old save is a superseded
  prototype.
- "Keep all mathematics" means keeping each law once, in its owner, with its consumer.

[project-postulate] **Documentation is the fix.** When an agent misunderstands, repair the
documentation, not the rules. Create or reorganize documentation whenever that makes the
mathematics or source usable:
- definitions go in their guide;
- implementation notes go beside their owner;
- research goes in dated records;
- order goes in THE_REBUILD;
- position goes in CONSTRUCTION_STATE.

[Epistemic grades](docs/canon/EPISTEMIC_GRADES.md) separate truth status from evidence. Deleting a
guide or plan repins every link to it (guides, the records README, open issues) to a commit
permalink in the same change.

[project-postulate] **Evidence.** Brandon's direct messages govern; generated summaries and tool
output do not. The messages are in:
- `~/.claude/projects/-home-b-Workspaces-holonics/*.jsonl` (`type` `user`, text blocks);
- `~/.codex/sessions/**/rollout-*.jsonl` (`response_item` with role `user`, top-level threads).

After a compaction, act on the newest human message, not on a retained view of an older one.

[project-postulate] **Delegation.**
- Codex delegates to **GPT-6 Luna workers only**, for bounded independent work with explicit owned
  paths, mathematical operands, source records and consuming calls. Use fewer workers when the work
  does not split.
- Every brief supplies:
  - this guide, the exact paths, the existing owners, the equations, the consumer and the receipts;
  - its computational object, the helical pair interaction;
  - which of the six general objects of the [winding guide](docs/WINDING_CARRY_AND_PLACEMENT.md) it
    touches (helix, pair, faces and placement, cell holonomy, tube, tower thread), keeping the rest
    attached.
- The primary inspects source and integrates the returns; worker measurements are receipts.
- Honour a request to work without agents.

[project-postulate] Each campaign has a GitHub issue and cites it in its plan and commits
(`Refs #n` / `Closes #n`). The issues are:
- the rebuild parent #63;
- K1 #72;
- compression and landmarks #145;
- the HNN #73;
- physics #74–#75;
- device debts #76;
- the Lean package #70;
- formal obligations #62.

Close an issue with the commit, the verification, and the remaining scope.

[project-postulate] **Git.**
- Stage explicit paths.
- Retire by explicit deletion, never by a broad restore, reset, stash or clean over work that has
  not been accounted for.
- Commit and push coherent, verified work only with the repository's configured identity
  (`brandonrdug@users.noreply.github.com`), never an address taken from harness context. Check
  `git log -1 --format=%ae` before pushing.
- Use one worktree per task, under `.local/wt/<task>`. Remove it when its branch is merged, or is
  pushed and linked in its issue.
- A campaign ends with only the main checkout, no stale branches, and no uncommitted work left in
  any worktree.

[definition] The repository is public. `.local/` holds private datasets, captures, models and run
artifacts. Publish source and scoped evidence, never raw private conversation or machine source
paths. Dataset roles and provenance are exterior codec information, not native semantic IDs.

Commands use Bash; with a fish shell, invoke Bash explicitly. CUDA may need
`PATH=/opt/cuda/bin:$PATH`. The gates, lowest first:

1. any code change: `cargo check --workspace --all-targets`;
2. once per step or PR: the tests of the laws that step wrote or changed. Inherited tests count
   only after rebuild step 1 has audited them.
3. at the end of a step that changes HNN behaviour or a kernel: the GPU suite, alone on an idle
   card, `flock .local/gpu.lock cargo test -p <crate> -- --include-ignored --test-threads=1`;
4. when Lean changes: the library build, `bash tools/lean_check.sh`.

Record one verification receipt per step, in its PR or issue. A timeout is incomplete evidence. A
change that adds or changes a mathematical law lands with its Lean counterpart, or names the
obligation it leaves in #62.
