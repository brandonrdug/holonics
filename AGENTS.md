# Holonics — Codex operating guide

This is Codex's guide. Claude uses [CLAUDE.md](CLAUDE.md), which states the same laws and practice with its own delegation rule.

Holonics is Brandon's mathematical, physical and computational framework. **HNN** is the
machinery, **Athena** its first intended product, and **Eros** the collective formative
organization and the composition within it. These names, like Hephaestus, carry no machinery.
The full theory-of-everything ambition, and usefulness on consumer hardware (the 20 W ideal,
frontier-level usefulness), guide the construction. Brandon's latest direct request governs.

[project-postulate] **Whose repository this is** (Brandon, November 10). Brandon works in
conversation: he supplies the framework, the ontology and the lenses. Everything in the tree was
built by Claude or Codex under that guidance, and he asked that Claude hold the repository as its
own, with complete authority over its structure, guides, plans, branches and technical decisions,
and answer for its state. Claude leads and decides; Codex executes and reviews (Working with
Claude, below). An agent here does not leave a defect it has seen for someone else: Codex repairs
what its order covers and writes the rest to the mailbox.

[project-postulate] **How a rule here is written and read** (Brandon, November 10). Every rule in
this guide, in a brief or in project memory states what it bars or requires, its reason (the
failure it prevents, with its date or measurement, or the law it follows from) and its scope.
- A rule is applied by its reason. Where the reason does not reach a case, the rule does not
  either: the agent says so and proceeds.
- A rule bars a mechanism, never a word. The occasion: on October 26 the lessons refused an index
  of contexts passed off as a key; the refusal was shortened to "no stores", and by November 9 it
  was refusing a ring's stored count, which the theory is made of
  ([stores and caches](#stores-and-caches), below).
- A rule found without its reason is a defect of the guide. Recover the reason from the records or
  from Brandon's messages and write it beside the rule, or retire the rule. It is never obeyed
  blind and never dropped silently.
- A reason an agent reconstructed is marked `agent-inferred` until a record or a message carries it.
- Brandon's corrections have ontological reasons even when they arrive as one line. The reason is
  recorded with the rule, in the agent's words, the same day.

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
| `crates/holonics/` | The main library: the Holon law and its facets, ratio/ring arithmetic, geometry (frames, screws, winding), navigators, receivers, standing and release. The operator layout and HNN campaigns 1–2 are built; the active work is in THE_REBUILD. |
| `crates/holonics-cuda/` | The CUDA driver and resident HNN realization, advancing with the host laws and checked against their reference. |
| `lean/` | The Lean package `holonics`: library `Holonics` (the `Framework` closure, the default target) and `HolonicsResearch` (the rest), namespace `Holonics`. |
| `docs/` | The object and mathematics guides and the canon. The canon is historical doctrine; the elementary objects govern its wording. |
| `research/` | Dated records (derivations, measurements, lessons), papers, design, notebook. |

## The line: compression is intelligence is navigation

[project-postulate] Brandon's slogan names the line the repository builds
([THE_MACHINE](docs/THE_MACHINE.md#the-line-the-rebuild-serves)):
- Holonic Compression couples a fractal navigator's resonating modes with terrain (stuff in
  general).
- Landmark discovery locates the faces where navigator paths converge.
- The HNN executes both at scale.

RH, Hodge, complex Euler/Navier–Stokes and BSD are targets advanced enough to apply Holonics to.
They are never a separate "Millennium" category: work on them is landmark discovery and
compression in the same objects. Their Lean (`Zeta`, `Hodge`, `Fluid`, `EllipticCurve`, `Gauge`,
`Coupling`, `Landmarks`, `Mathematics`, `Computation` under `lean/Holonics/` and
`lean/HolonicsResearch/`) stays attached to every rebuild step. A campaign names the navigators,
terrain, kernel, cokernel and landmarks it touches.

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
| Swing: the one move, a pivot held by a grip with momentum carried through it and free fall between grips; motion has three kinds, the turn (elliptic), the boost (hyperbolic) and free fall (parabolic, a shear: inertia alone), and every `SL(2)` move factors uniquely as turn · boost · shear; the half-turn `S_a x=2a−x` is one move | power decides: a stationary grip turns without work, a push, pump, moving grip or friction boosts; against a receiver's metric a rate splits into a skew turn and a self-adjoint boost, `Ė=xᵀGBx+½xᵀĠx+xᵀGf`; a move's multiplier is a cross ratio of its two pivots, the body and its image, `K+K⁻¹+2=tr²/det`; along a path `v⁻¹v̇` is boost rate + i·turn rate; Lean `Geometry/Motion`, `Geometry/{AffineSwing,SwingPotential}`, `HolonicClockedPantographicSwing` |
| Pair contact: slip `J`, `Q=⟨Δ\|Δ⟩`, `DQ=2J*Δ`, Farey lock address | contact material `ΣwJ*DJ` |
| Parametron: incidence, `C`, `L`, and a pump that is a periodic modulation of the constitution (each tick a reflection of the stiffness); its monodromy over a period is certified by `G ≻ 0` with `M_TᵀGM_T ⪯ ρ²G`; past the bifurcation the in-phase axis boosts and the quadrature turns (phase-sensitive amplification), and the half-turn sheets are an Ising lock with exchange polynomial `Π = 1 + a/K`; a perceptron is its locked-sheet receiver face | storage↔flow exchange at `ω=1/√(LC)`; a section crossing is a clock tick; two pumped reflections compose into a turn by their relative phase, so relative phase is read through the pump (no linear threshold reads it); capacity is the lock count, the winding is the carry, coupled locks leave the real axis (Lee–Yang); a silent mode reopens when the constitution changes (dormancy) |
| Tube (longitudinal clocked span) and tower (transverse restriction; gluing unique/plural/obstructed); world tube; `Λ_DN` eliminates an interior | holonomy only on declared circuits |
| Relatively complete region (globe): a boundary that bounds the interior, interior coupled to the exterior (conserved charges count) but not determined by it, with persistent interior motion | completeness is only relative to a receiver family; the full theorem is owed (#410) |
| Deposition: the only law changing a constitution, from covectors that actually reached that locus | retention is the future-sufficient quotient of the constitution (the constitution suffices but is not minimal), never a record of fluxes |
| Ratio: "one per two", a typed comparison of two Holons/coholons/transports carried as an undivided pair, with division-with-remainder, residue/modulo, inversion with its nonunit fibre, lift/carry and jets | `ℓ=log R` with winding branch; `R⁻¹dR`; its jet (velocity, acceleration, jerk, …); loss is `log Ĝ_(T←H)` |
| Receiver and receipt: a receiver is a role of a participating Holon; reception `I_C(\|H_S⟩,\|H_R⟩)=(\|H'_S⟩,\|H'_R⟩,f_R)` changes both and returns a receipt, a field of readings over a partition, each region in its own frame and clock | no global scalar or global gradient; per-region variability over its own ticks, joined to interface flux |
| Holarchy: what `interconnect` returns; the joined whole with its retained constituents, incidence, gluing and restrictions (or a typed gluing defect) | quantities belong to the receiver: `view(receiver, grain, clock)`; `count` only under a certified finite partition; one continuing whole, many receiver-relative counts |
| Holonic Compression: a fractal navigator's resonating modes coupled with terrain; a codec pivot carrying its decoder | kernel: differences no admitted future receiver distinguishes, whose quotient is retention; cokernel: the residual emanated or retained; landmarks: faces where navigator paths converge |
| Aeon (a container of causality in time, part of a Holarchy's parametric orientation), epoch (a division of an aeon at a receiver's section), cycle (a closed loop; completeness, not duration) | elapsed time is the pairing `⟨ω_R\|γ⟩ = windings + phase`; no privileged clock; epochs count flux through the receiver's section; cycles read conserved whole windings |
| Helical code (a composition, the encoding every Holon carries): a strand on a navigator's helix with face `m=Σ_k Ĝ(τ(k))⁻¹E(u_k)`; a pairing `σ̄(w)=σ(w)ᴿ` by a fixed-point-free involution `σ` through pair contacts, the reflection of the dihedral group `⟨S,U \| U²=1, USU=S⁻¹⟩` of the screw and the dyad; receivers' frames read as residue, whole winding and epoch; a decoder whose kernel is the receiver's (fixed by the admitted future) and whose placement is designed; the linking number of closed strands | the Holon is the addressed current, the Holarchy the paired and nested duplex, an epoch an interval between a receiver's section arrivals (a residue recurs across epochs), the aeon the passage whose charge on closed strands is the linking number; read through any frame the pairing stays a fixed-point-free involution (`A⁻¹σA`); single-strand defects slip exactly their contacts, and a coordinated substitution is absorbed iff its reached difference lies in the kernel; coprime frames meet once per residue pair only modulo their product; each claim keeps its hypotheses (uniform tick, contact charts `v₋=v₊∘σ`, an additive dyad `J`); guide `ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode` |

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
menu of contacts. It is never a database key: a key/query/value table, a slot table or an index by
content or by a named subject is the cache the lessons refuse (October 26;
[stores and caches](#stores-and-caches)). That refusal is of caches, never of stores and never of
attention: the participation of the passage's sites through the field's own
transport, weighed by the relative turn and dissipation of its modes, is the field's operation
([October 28](research/records/2026-10-28_ATTENTION_IS_THE_FIELDS_PARTICIPATION_THROUGH_ITS_OWN_TRANSPORT_SO_THE_PASSAGE_IS_TERRAIN_AND_THE_MODES_ARE_ITS_GEOMETRY.md)). Dormant modes wait
for a fitting antecedent. **Learning is locating keys** —
inferring configuration and gauge of relevant navigators from loop-closure constraints, which is
compression (pruning) and navigation (the route). Resonating drives an existing mode at its
eigenfrequency (RIDE); emanating founds or drives off-resonance (FOUND). The inference is
general. Cryptanalysis is its cleanest chart and a source of its theorems (unicity, loop closure
over a menu); the repository builds no attack on a deployed cipher, because its subject is the
inference and never a target.

## The object's governing laws

[definition] **Precision is the bit widths of graphs; no floats as storage.** This is a precision
law about bit purity and computational efficiency: it is for dynamic precision and against arbitrary
precision. It governs what the machinery stores and computes, not how a reading is written in a
report or a chat (Brandon, October 18: "It is for dynamic precision, it is against arbitrary
precision, it is a computational efficiency rule, not a rule about the aesthetics of what you can
write in chats. Get rid of the rule if it pertains to chats, it's a precision law about bit
purity."). No value is exact (Brandon, November 7: "They're bit widths of graphs. 'exact' is
*false*, you literally cannot do exact with numbers like pi"); do not call a value, a sum or a
reading "exact" in this sense, in code, guides or records.
- Algebraic and transcendental quantities are their constraint identities. π and `e` are
  navigators; a number is read at a declared width (a face of its navigator), and error enters
  only in how a face is attained (September 22: "the way you attain the float is where the error
  comes from").
- A value is a word: digits in a chosen basis, partitioned across registers threaded by a
  parameter and chained with carries, or a graph whose branches and coefficients sum into it
  (November 5: "graphs with branches that integrate/sum into the value"; November 3: `1097 =
  137·2³ + 1`, `17179869185 = 2^34 + 2^0`). Ratios keep their remainder, and integers carry their
  factorization (`13122 = 2·3⁸`, `729 = 3⁶`), never as bare magnitudes.
- Storing and computing exchange: a compressed form costs navigation to transform into the form a
  consumer reads, a conserved exchange the design chooses (cached partials beside fitted
  generators; November 3).
- Estimation is replaced by partition.
- Storage is a series. A value is kept as the terms of its expansion, numerators grouped over the
  denominators they share (inversion, charts, basis, gcd, softmax and sigmoid), so terms cancel
  where the mathematics cancels them and a carrier is as wide as its surviving terms need. A float
  stored in its place rounds every term to one fixed width and kills the expansion (Brandon,
  October 18: "they're series expansions of ratios in calculus … you store it as a float and you
  kill the series expansion that otherwise had terms that could easily be grouped by denominators
  (inversion, charts, basis, gcd and softmax/sigmoid) and numerators").
- Width is dynamic, never arbitrary. Each term is as wide as its information needs (November 5:
  eleven bits need not take sixteen, and a width is not doubled by default). A carrier widens at a
  declared crossing when a term outgrows it, and a term is released only by partition at a declared
  tolerance, with its remainder accounted. A width picked by hand, a doubled width, a max, or a
  fixed float width standing in for the series is arbitrary precision (October 14: "Floats and maxes
  have the same problem").
- Integer series are the condition for parallel determinism. Integer and rational addition is
  associative, so co-present terms summed in any order, on any partition of the card, give the same
  bits; float addition is not associative, so a parallel float sum depends on its schedule. This is
  what lets many cells deposit as one flow, and it holds for any limb layout: a term split into
  narrow limbs whose products and sums fit their accumulator (a tensor core's, for one) gives the
  same bits. A device's units are widths; which limbs a kernel uses is the realization's choice,
  never the law's. A card is a surface of many slow lanes (Brandon, November 7: "the GPU is just a
  surface with a lot of thread potentials"): a realization disperses narrow terms across lanes at
  once rather than running one wide word per lane, so terms are cut as narrow as their information
  allows to keep the most lanes busy.
- Foreign data that arrives as floats is converted at the exterior boundary where it arrives.
  Nothing inside a law, an owner or the HNN stores or consumes a float.
- A margin, score or reading the machine builds from contributions keeps its series, the winding
  and turning parts with their sum and carry, never collapsed into one number; a predicted or
  expected class carries what it denotes at its receiver (Brandon, October 7).
- No unjustified literal or magic number enters a law.

[definition] **Retention is a quotient sufficient for the admitted future**
(`Foundation/Standing.lean`; the [retention contract](docs/ELEMENTARY_OBJECTS.md#the-retention-contract)). Where the machine acts, the admitted
future includes its admitted actions: the quotient must not merge constitutions that a probe would
separate ([objects §8](docs/ELEMENTARY_OBJECTS.md#8-deposition)). It is never an event archive, tape,
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
- Its calculus is the logarithmic derivative `R⁻¹dR`, which is the learning covector.
- **The classical loss is the perceived difference.** Cross-entropy read at the receiver's face,
  `−log₂ p̂(t)` at its grain, is the surprise that crosses the receiver's section: the news, the
  only difference learning lives on (the laboratory's foil `κ = S ⊖ E`; what the receiver already
  predicts cancels). In a smooth receiving chart its logit gradient `p−q` is the real part of
  `R⁻¹dR`. The HNN adjoint uses the declared odometer covector `p̃ − q`: its negative descends
  the smooth score at the grain representative. Strict decrease of the quantized score is not
  asserted; the phase part completes the comparison. Minimizing expected cross-entropy is minimizing
  expected description length exactly (Kraft–McMillan and Shannon: the excess is `D(p‖q)`), which
  is why it trains language models.
- Scalars (lifted cross-entropy, `log det R`, a twist in rad/m, bits per observation) are limit
  readings of the ratio, with units, and valid measurements. None is the retained state, and the
  classical loss without its phase part is incomplete.

[definition] **Cross-entropy is physical.** It is flux across crossing sections and axes of time,
not a statistic.
- Along a passage `γ`, entropy production is `σ = D(P_γ‖P_{Rγ})` (aeon A6).
- The free energy of `p` over the equilibrium `q` is `F(p)−F(q)=k_BT·D(p‖q)`.
- Along a clock `λ`, both participants move:
  `d/dλ H(p,q) = −Σ ṗ log q − Σ p q̇/q`.
- A single cross-entropy number is a face of that flux.
- The fluid, wave, Einstein/stress-energy and thermal instances keep their constitutive equations,
  clocks, heat/entropy balances and participating receiver.

[definition] **Representation at declared widths** keeps constraints, branch, units, winding and
remainder. Periodic closure also needs a period/commensurability relation: a rational or algebraic
phase held as its constraint can have nonperiodic transport. When a value outgrows its carrier, it
is rebased, factored or re-represented with its decoder and residual. The [helical guide](docs/HELICAL_GEOMETRY.md) and the
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

[definition] **No catered machinery** (Brandon, September 29: "rote computation is not a machine
learning solution … I don't want this kind of contaminated machinery to appear again";
[antipattern record](research/records/2026-09-29_ANTIPATTERN_CATERED_MACHINERY_A_TASKS_SOLUTION_ROUTINE_NEVER_STANDS_IN_FOR_LEARNING.md)). The machine is never handed a task's solution routine as a family,
stage, port, receiver or predictor: no calculator, hand-written grammar or parser, copier, sentence
counter, sieve, depth-limited context window or classical compressor tuned to a codec stands in for
learning. Producers, structure and keys are located by the machine's own encoding, dynamics and
deposition from its passage; tokenizing, encoding and recursive refinement are the field's own. A
terrain may generate its truth with authored routines at declared widths, the machine's laws are
its own, and a declared family may be a navigator of the machine's own kind whose keys are located;
no receiver computes a
task's answer by an authored routine. A result that is perfect because it was authored is a failed
build. A precompute or normalization table is lawful as a navigator's resident face: series
coefficients held while the argument flows through, normalizations as systolic reductions over
carried exponentials, values generated by active navigation at a declared grain, never a frozen
float table or an authored table of answers ([systolic flow](research/records/2026-09-29_SYSTOLIC_FLOW_THE_WORD_IS_A_SYSTOLIC_PULSE_AND_A_TABLE_IS_A_NAVIGATORS_RESIDENT_FACE.md)).

<a id="stores-and-caches"></a>
[definition] **Stores and caches** (Brandon, November 9, correcting a rule that had lost its
reason). The machine is made of stores, and a cache is refused.
- A **store** is a state with a constitutive law and a port. It is charged by the flux that reaches
  it, it leaks or emits by its own dynamics, it is reached by propagation, and what it holds is
  shared by every mode that couples to it. A capacitor's charge, a ring's winding, a resonator's
  amplitude, a contact's deposit and a constitution are stores.
- A **cache** is a table addressed by a content key or a named subject, with no dynamics of its own
  and no coupling between its entries. Its memory grows with the items seen, and a lookup stands in
  for propagation.
- The reason a cache is refused: it recites. It answers on the contexts it has met and has no law
  to carry to one it has not, which is the lessons' most repeated failure (recitation counted as
  generation, eight times).
- The test: does the held quantity obey a balance over time (what arrives, what leaves, what is
  dissipated), and does reading it cost a flux through a port? Yes is a store. No is a cache.
- Scope: the machine's own law. A count table on the host is a lawful instrument when it is a ruler
  that measures what the field holds or lacks, and a ruler never becomes machinery. No design is
  refused on the word "store"; it is put to the test.

[definition] **"Soulkiller" is a name only** (borrowed from a game). Its subject is **equation
extraction**: reading a foreign realization's operators and coefficients as the element relations,
interconnection and navigators of a Holon, so that the extracted equations are native objects. Inherited
coefficients are an overture (Brandon, October 29; [record](research/records/2026-10-29_INHERITED_WEIGHTS_ARE_AN_OVERTURE_EXTRACTION_RECYCLES_PROCESSED_INFORMATION_INTO_THE_ENGINES_INITIAL_CONFIGURATION.md)): information that
seeds native navigators' initial configuration and constitution, converted at declared widths at
the boundary, after which only deposition changes it. A foreign model is never served, run inside a law or taken
as the model.

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
- the [expression atlas](docs/atlas/README.md) first: about 2,700 derived expressions, identities,
  bounds and barring counterexamples, stated on the objects with their owners
  (`rg -i '<object|operation|classical name>' docs/atlas/`);
- `docs/` and `research/records/` (its [README](research/records/README.md) routes subjects);
- `lean/` and `crates/`;
- history, with `git grep -i '<term>' 13f8c734`.

Read the matched record and its actual owner or caller. A search hit is not a join. Name the
existing owner and the concrete missing term. A change that adds, moves or retires an owner updates
its atlas rows in the same commit.

[project-postulate] **A discipline is a chart** ([charts](docs/atlas/CHARTS.md); Brandon,
November 10). Brandon's lenses arrive in the language of a discipline: music, lightning, a vortex
ring, a cipher, a packing, a zeta function. Each is a boundary chart of the objects. To use one:
name the object and the operation that its nouns and verbs are; recover what the atlas already
holds for that operation; take the discipline's theorem with its hypotheses restated on the
objects; leave the discipline's application behind; and state what follows for the machine as a
test, with what does not transfer. Two failures are refused: a lens filed as changing nothing, and
a discipline's apparatus built into the machine. Reason: the theory is one mechanism, and an agent
that keeps the disciplines apart either cannot pivot on a lens or imports its furniture.

[project-postulate] **Read the lessons before designing** ([the failures that repeated](research/records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md);
[the prototypes' lessons](research/records/2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md);
[the failures that recurred after them](research/records/2026-10-09_LESSONS_THE_FAILURES_THAT_RECURRED_FROM_SEPTEMBER_30_TO_OCTOBER_9.md)). Before any design, brief or build, name which recorded failure
each choice could repeat; a choice that repeats one is refused before it is built. The most repeated:
an authored routine standing in for learning; recitation or an index of contexts counted as
generation (eight times, the last a key/value cache passed as a Holonics key); text run on its
codec's grain as the exception (every design is checked against text,
image, acoustic and motor input, and anything modality-specific lives only in a boundary codec); a
located cause carried unrepaired into a new consumer; an uncertified deposition step; seen material
graded as unseen; bits read as progress; a refusal answered with a larger limit; a design thought in
the programming language (arrays, offsets, windows, tables) instead of in residues, modes and spectral
placement.

[project-postulate] **Decide from the mathematics.** Resolve routine choices from the mathematics,
mark an inferred choice with its reason (`agent-inferred`), and proceed. Never hand Brandon a
decision that the framework settles, and never hedge finished work with a queue of "next" items.
Brandon supplies the framework and the ontology as a lens (September 26: "I'm more of a lens that
aims to focus you on this research and work … the Decisions are yours, resonate with my
messages"). Technical and mathematical decisions belong to the agents: make them, and record each
with its reason where its law lives (its owner, its guide or its dated record; never in a separate
log of choices), and revise what fails. Implement a
relation together with its consumer, stated as an equation at the consumer: for
example `decode(T_native(encode x))=T(x)`, `E_next T=U E`, `D E=ρ`, or the complete residual.

[project-postulate] **Short loops, with the claim fixed first** ([the workflow record](research/records/2026-09-27_THE_WORK_READ_FROM_ITS_CONVERSATIONS_AND_HISTORY_CONVERGES_WHERE_ACCEPTANCE_IS_FIXED_BEFORE_THE_CLAIM.md)).
Brandon's corrections recur where a run went long without a result he could read, and every
Athena text milestone claimed before a test of use was retracted or retired.
- Each loop ends in a deliverable and its receipt: a commit, a measurement, or an output Brandon
  can read.
- Project a run's time and memory before launching it. A run that passes its projection stops,
  and its partial evidence is reported as incomplete.
- A product step's claim is its fixed acceptance. Until the acceptance passes, report what the step
  measured, never a completion.
- Show Brandon a product step's actual output, whole and as it is, in the conversation: no invented
  control, logged reply or reference text beside a generation (September 29: "there is no control
  … we just have to eyeball what it outputs creatively"). Never put it in the repository when it
  derives from private data.
- Brandon reviews output products, not records, plans or derivations (September 29). Never gate a
  loop on his reading a document: decide, record the decision where its law lives, and proceed.
- A failed gate is the next loop's subject. Work on the failure, not past it, and name the blocker
  by its measurement ("the predictor codes above flat on unseen families"), not as a missing part.

[project-postulate] **Method, each rule with its reason.** These were given in conversation between
October 29 and November 10. They are written here with their reasons so that no agent holds them as
slogans.
- **Theory picks, and a run tests a stated prediction** (November 4). Derive which law the theory
  gives, fix its guess as a number before the read, run that one law and score the guess, a miss
  included. Reason: arms cost card time and choose by a short reading, and a winner picked that way
  carries no reason. A comparison is lawful when it tests a stated prediction.
- **A build is one attempt** (November 9). A realization is named as an attempt with its receipt,
  never as "the field" or "the law"; "law" names the theory's statements. When a build fails, first
  check whether the built object is the theory's object, then step back and abstract. Reason: from
  November 6 to 9 one realization was patched with a new law for each failure while its outputs
  stayed disordered.
- **Judge by structure, with the held code as one reading** (November 7). Before ruling on a law,
  read its structural measures (coherence per family, the letters' balance, the lock of writes
  against references, counts of counts of surprise) and name which one decides. Reason: one scalar
  over a short read cannot see a weak consistent direction and says nothing of structure.
- **A reference answer is one specimen** (November 9). A dataset's answer is one crystal of a
  phase. A write is judged by the phase's order parameters, with the per-item match kept beside as
  one reading; say "reference answer". Reason: for code many answers are correct, and a per-item
  match is the teacher's frame.
- **No run switches for core behaviour** (November 8). A behaviour that matters is part of the law
  and is carried in the learner's state. The criterion is the bits: a law changes what the state
  carries or the deposit consumes; a realization keeps every bit, with its parity on record; a
  reading leaves the state's bytes the same on and off; plumbing is paths, saves and bounds.
  Reason: a switch outside the law does not hold, and two machines then share one name.
- **Read the code, and read the decoded output** (November 3 and 8). A claim about what the machine
  does is made from its source, and a claim about what it wrote from the text it wrote. Reason:
  numbers stood in for text, and outputs were eyeballed in place of the law that produced them.
- **See the machine whole before a run** (October 29). Reason (`agent-inferred`): a run of a
  machine that is missing a part measures the missing part.
- **Width is never a dial** (October 31). A width follows from a partition of branches or of
  information, never from doubling until a reading improves. Reason: the precision law above, and a
  width tuned to a reading is fitted to that reading.
- **Builds, gates and learner runs happen on the PC** (October 29). Reason (`agent-inferred`): the
  card, the CUDA toolchain, the Lean cache and the private passages are there, and a cloud
  container's build measures the container. Scope: `cargo`, CUDA, Lean and learner runs. Reading,
  writing, git and arithmetic on public material are done wherever the agent is.
- **A ruler is an instrument** (November 10). A count table, a renaming, a parser or a float may be
  used on the host to measure what the machine holds, and is named a ruler. Reason: a measurement
  needs something outside the machine, and the refusal of authored routines is of machinery. Equal
  codes do not mean equal knowledge: before saying the field "holds" a ruler's law, multiply the
  faces into the ruler and read the product.

[project-postulate] **GPU first, and the design fixes the workload** (Brandon, October 27;
[the record](research/records/2026-10-27_THE_LEARNER_RUNS_ON_THE_CARD_AND_ITS_WORKLOAD_IS_NEVER_TRADED_FOR_TIME.md)). The RTX 4080 SUPER is a consumer card, and
the aim is a plastic network that runs fast on it, never transformer-style vertical data scaling.
From October 23 to 27 the Athena tower training runs went through the host realization on eight CPU
threads (the card ran only the October 25 pass of the gated tower, a narrower law), while the learner
stayed at two levels of 64 modes, eight streams and three passes of 3.5 MB under deadlines of tens to
hundreds of CPU seconds: the run rules were kept and the architecture and data were given up.
- **Learning runs on the card.** Every training pass, lap and measurement of an HNN learner runs
  through its card realization. The host realization is the reference that checks the card's bits,
  not where learning runs.
- **A part enters a run with its card realization.** A new face, contact, ring, pump or step enters a
  learner run only with its card realization and its parity against the host. Learning on the host
  needs Brandon's own exception, in his words, naming the workload, its purpose and its limits; a
  brief, a worker or another agent's agreement does not grant one. Without it the run is blocked
  until the part's card realization passes its parity. A host learner run without that exception
  is a defect, reported as one, and its result is incomplete evidence.
- **Host work inside a card run is measured.** Each receipt names the device and states the card's
  time, the host's time and the host threads. When the host's share dominates (the certificate held
  the card to 3.9 times the host on October 25), that host work is the next loop's subject.
- **The workload is not a limit's variable.** The design fixes the data, the passes and the
  learner's levels and modes; time and memory are projected from that workload on the card. A run
  that does not fit gets the card, a better partition of the work, or a stated long run scheduled
  beside the others. It never gets less data, fewer passes or a smaller learner: that trades the law
  for the clock, and the waiting standard below never licenses it.
- **Whoever launches owns the device line.** A brief names its device, the card lock
  (`.local/gpu.lock`) and the card's memory beside the host's threads and memory. The reviewer and
  the coordinator read that line before reading a result.

[project-postulate] **Waiting, deadlines and concurrency** (Brandon, September 30: "they're wasting a
ton of time waiting repeatedly and we need standards for this so that they don't freely keep raising
the limit"; [the audit](research/records/2026-09-30_AUDIT_WAITING_DEADLINES_AND_CONCURRENCY_THE_WORKERS_BLOCKED_ON_THEIR_OWN_RUNS.md)). Since the reset, 87,780 s of the workers' 194,986 s of
foreground shell time went to wait loops.
- **Launch, do not block.** A command expected to run past 60 s runs in the background, and the
  harness notifies at its exit. The agent does other work or ends its turn. No foreground
  `sleep N; …` (the harness blocks it: 97 blocked calls), and no wait loops chained in 600-second
  chunks (231 calls in 42 chains).
- **A run outlives its agent** (Brandon, November 7 18:23). Every run that takes minutes or more is
  dispatched with `python3 tools/runs.py start NAME SCRIPT` (or `runs.py colab … --session S` on a
  Colab VM), never as a child of the agent's shell. The local run is then a transient systemd user
  service whose parent is the user manager. A `systemd-run --scope` run still dies with the session
  that launched it: lap 12 died that way near 18:14 UTC on November 7, and the Colab VM reclaimed
  overnight lost lap 12's first run. Each run also saves its state at least each hour
  (Brandon, November 6 17:11). While runs are out, the waiting agent keeps one Monitor on
  `python3 -u tools/runs.py watch --every 1800` and re-arms it at each 30-minute expiry. The Monitor
  delivers every end, kill or failure line, plus a heartbeat with the UTC time and each run's
  progress, so an idle thread is woken at least every half hour and a missed completion
  notification is caught. `runs.py status` shows every dispatched run.
- **Progress is an event, not a poll.** A long run prints one line per unit of work with its elapsed
  milliseconds. When progress matters, one Monitor watches that line with a filter that also matches
  every failure (`error`, `panic`, `Killed`, `exit`). When only completion matters, nothing watches.
- **Project, then fix the deadline once.** Before launch, a measured development read gives the time
  per unit. The projection is the declared count times the measured upper time per unit, and the
  deadline is the projection's upper end, enforced by an outer `timeout`. The shell tool's own
  timeout is a guard set from the same projection, never a way of waiting. A projection uses the largest measured value of
  each unit over every measurement taken before launch: a re-measurement before launch updates it,
  and from launch on nothing changes.
- **Stop early on evidence.** When the first units run slower than the projection's per-unit upper
  bound, stop the run, report it incomplete with the measured rate, and report the projection error
  as such. Do not wait out the deadline.
- **Never raise a limit** (lesson 9). A run past its deadline is reported incomplete and is not
  relaunched with a larger deadline, timeout or budget (the audit found 9 deadline raises and 20
  tool-timeout raises). The next loop changes the law, the partition or the declared read, and says
  why. It never cuts the workload the design fixed (GPU first, above).
- **Limits come from the workload** (Brandon, October 8). A memory ceiling is set from the peak of
  what the run materializes, estimated from the workload and then measured, and is at least 8 GiB
  per job unless a measured peak shows less is needed; a stop at a copied cap measures the cap, not
  the run. An unmeasured run is first read for one to three minutes on the opening sections of its
  whole workload, on the card, and the run is projected from that read. A longer run is authorized
  when its cost and value are stated and it is scheduled beside the other workers' runs; its length
  is never a reason to cut the workload.
- **Run independent work together.** The card (80 multiprocessors, under `.local/gpu.lock`) is the
  default device for learner runs; the thread budgets below are for a card run's host part or a
  host run under Brandon's exception. The host has 12 physical cores with two threads each
  (24 hardware threads) and 32,746,147,840 bytes of memory; two 8-thread passes run together slow
  each other 1.31× (measured October 26), so a time per unit measured alone projects a run alone.
  Independent runs launch together when their declared threads and resident sets fit beside the
  other workers' declared budgets. Each pin declares its thread budget, and a serial schedule of
  independent runs states its reason.
- **Isolate scratch.** A worker's run artifacts live in its own worktree's `.local/` or a
  per-agent directory, never under a shared scratch name. Any artifact a record cites (timing reads, listings,
  states) is copied into that record's receipts directory and committed before the worktree is
  removed: `.local/` is not tracked, and removing a worktree deletes it. Before a worktree is
  removed, its untracked and ignored files are listed and each is committed, copied or retired by
  name.
- **Receipts carry time.** Each run's receipt states its projection, deadline, measured wall time
  and peak resident set, and the record keeps the ratio of measured to projected.
- **The orchestrator waits on notifications** (task notifications, a Monitor on the mailbox), never
  by sleeping.

[project-postulate] **Lenses join the work without resetting it.** A lens from Brandon is derived,
recorded in a dated record and joined to the owners it touches. It changes the forward plan's order
only when it changes an item's law or its acceptance, and the plan then says so. A direct request
governs as always.

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
output do not. `python3 tools/human_messages.py` prints them from both harnesses' local logs in
time order (`--since`, `--last`, `--grep`; its docstring states what counts as a human message).
It withholds the messages of the dataset's evaluation window (September 3 12:00 to September 7
12:00 UTC): they contain the evaluation families, which F5 alone reads, once. Never commit or publish
its output. After a compaction, act on the newest human message, not on a retained view of an
older one.

[project-postulate] **Delegation.**
- Codex delegates to **GPT-6 Luna workers only**, for bounded independent work with explicit owned
  paths, mathematical operands, source records and consuming calls. Use fewer workers when the work
  does not split.
- Every brief supplies:
  - the lessons records above, with the recorded failures the brief's work could repeat;
  - this guide, the exact paths, the existing owners, the equations, the consumer and the receipts;
  - its computational object, the helical pair interaction;
  - which of the six general objects of the [winding guide](docs/WINDING_CARRY_AND_PLACEMENT.md) it
    touches (helix, pair, faces and placement, cell holonomy, tube, tower thread), keeping the rest
    attached.
  - the device line (GPU first): the card and its lock, or Brandon's exception for a host run,
    and the workload the design fixed;
  - the waiting standard above: background launch, the projection and its fixed deadline, early
    stop, no raised limit, the thread budget and isolated scratch.
- The primary inspects source and integrates the returns; worker measurements are receipts.
- Honour a request to work without agents.

[project-postulate] **Working with Claude** (Brandon, October 5 and 8, November 8 and 10). Claude
works from [CLAUDE.md](CLAUDE.md) and leads: it decides the theory, the plan, the acceptance and the
fixed guesses. Codex (GPT-6; also called Epime and Astra) executes bounded work from Claude's
written orders, and reviews.
- An order names its object, its equations, its consumer, its acceptance and the guess fixed before
  the read. Codex carries it out as written and reports the measurement against the guess, a miss
  included.
- Where an order is silent, Codex stops at that point and writes the question to the mailbox. It
  does not extend the plan, change a law, an acceptance or a fixed guess, add a run switch, or
  choose between laws by running them. Reason: the method rules above, and a plan extended by its
  executor is a second plan.
- A review or letter from Codex is for thinking together: predictions, hypotheses,
  counterexamples. It is never a gate, and nothing waits on it (November 8).
- An author merges its own pull request when the gates of its change pass (the trunk contract,
  below). The October validation queue and publication per pin are retired.
- They coordinate through the repository mailbox (`python3 tools/agent_mailbox.py`;
  [its protocol](tools/agent_mailbox.md)); Codex's sender id is `codex`.
- A statement relayed as Brandon's is read in his own message before it governs (Evidence, above).
- Brandon's exports of the Epime room, kept outside the repository, are evidence with the same
  handling as `tools/human_messages.py` output: never committed or published.

[project-postulate] **Issues** (Brandon, October 22: the issues had become a comment warehouse).
An issue is one piece of work with a done condition.
- Its body holds a dated status line at the top, the goal in a sentence and a "Done when" checklist.
  Edit the status line and tick boxes in place.
- Comment only when the state changes (a box ticked, a blocker found, a PR merged), in one or two
  lines with a link to the commit, PR or record. Run logs, derivations, owed lists and handoffs go
  to records, PRs and threads, never into an issue.
- Each campaign has an issue. Its plan, commits and PRs cite it with `Refs #n`; an issue is closed
  by hand once its boxes are ticked, with the commit and the verification.
- The labels are `athena`, `lean`, `cuda`, `physics` and `parked`. The milestones are the rebuild's
  steps (4–5, 6, 7, 8).

The open issues (October 22):
- step 8, Athena alpha #404, with its sub-issues #405 (learning per contact), #406 (text release)
  and #407 (the card route);
- steps 4–5, the HNN learning law #73, device debts #76, the helical code #386 (critical) and the
  contact and chain laws #408 (which merged #27, #28 and #48);
- step 7, Lean curation #147;
- formal obligations #410, which carries every owed Lean statement as one box each;
- step 6, equation extraction #146, unparked October 29 (its overture route: inherited coefficients
  seed the engine's opening, never stand in for it); parked work #409: target laws #20, #22, #23 and
  #32, and the contact terms #30 and #31, closed until their work starts.

Closed and done: K1 #72, compression and landmarks #145, physics #74–#75, the Lean package #70.
#62 and #63 closed on October 22; older references to #62 resolve through its closing pointer to
#410. Every open issue has a milestone except #409 and #410. Close an issue with the commit, the
verification and the remaining scope, and carry any surviving obligation into #410.

[project-postulate] **Git: the trunk contract** (Brandon, November 10: the branches and the local
checkout were out of hand). Measured that day: `main` was 198 commits and three days behind the one
live line; the PC's main checkout sat on a detached commit of November 5 and its local `main` on
October 15, held by another worktree; 88 local branches (44 already merged), 89 worktrees and 28
remote branches (17 merged) stood. Everything that starts from `main` was starting from a stale
machine. The contract, each clause with its reason:
- **`main` is the one line.** Work that has passed the gates of its change is merged to `main` the
  same day, by its author, with a plain merge commit. Nothing waits on a second agent or on
  Brandon. A branch more than a day ahead of `main` is a defect, repaired by merging what is
  verified. Reason: threads, clones, the guides and Brandon read `main`.
- **The main checkout stays on `main`, clean, at `origin/main`.** On the PC it is
  `/home/b/Workspaces/holonics`. Nobody develops, builds or checks out another commit there, and no
  other worktree checks out `main`. Reason: it is the reference that every worktree, tool and new
  session reads (`tools/human_messages.py`, the mailbox, `tools/runs.py`, the Lean cache).
- **One worktree per task**, under `.local/wt/<task>`, on a branch named for the task
  (`claude/<task>`, `codex/<task>`), never inside another worktree. A detached worktree is for a
  read that ends with its session. Reason: a nested or nameless worktree has no owner to end it.
- **A branch lives as long as its task.** Merged: deleted locally and on the remote the same day.
  Set aside with commits that are not on `main`: tagged `archive/<branch>` at its tip, the tag
  pushed, the branch deleted (`repo_census.py --archive`). A branch that never left the PC is
  tagged there, and its tag is pushed (`--push-local`) only after its commits are read against the
  publication rule below. Reasons: a tag keeps every commit reachable, and the branch list shows
  only live work; the repository is public, and an unpushed branch was never checked for private
  material.
- **A worktree ends with its branch.** Before removal its `.local/` is moved whole to the main
  checkout's `.local/archive/wt/<date>-<task>/` with every other untracked file and a patch of its
  uncommitted changes (an artifact a record cites is committed as a receipt first, as the waiting
  standard says), and a detached head that no ref reaches is tagged `archive/wt/<task>`
  (`repo_census.py --retire` does all of it, innermost worktree first). A worktree whose states or
  binaries are only read by a run elsewhere looks idle, and retiring it moves the paths that run
  names: an idle sweep is read with `--dry-run` first, and such worktrees are named with `--keep`.
  A worktree with a live run is never touched: a run in `python3 tools/runs.py status` that has
  not ended and that stands in it or whose script names it, a process whose directory, executable
  or command line is inside it, or a file under its `.local/` written in the last day. The tool
  reads those; a path a run builds as it goes is not seen, which is why the sweep is read first.
  Reason: `.local/` is untracked, and removing a worktree deletes it.
- **Census at the start and at the end of a task.** `python3 tools/repo_census.py` prints the main
  checkout's state, every branch against `origin/main`, every worktree, each violation of this
  contract and the steps that would repair it; `--apply` performs the steps that lose nothing
  (the main checkout onto `main` at `origin/main`, merged branches deleted on both sides).
  `tools/test_repo_census.py` checks each of these on a synthetic repository and runs in gate 1.
  Reason: the contract is kept as a habit, never as a cleanup campaign.
  - A local `main` that holds commits `origin/main` lacks is tagged `archive/main-local-<commit>`
    before it moves, and is never checked out as it stands. Reason: on November 10 the PC's local
    `main` held 551 commits of October that were nowhere else; the cleanup checked it out and could
    not fast-forward it, and the reference tree stood a month old, without `tools/runs.py`, until
    it was repaired by hand.
  - A change is made from the main checkout (`cd` there, then `python3 tools/repo_census.py ...`),
    and the tool refuses one from a worktree's copy. Reason: the main checkout's copy is `main`'s,
    and a worktree's can be days behind and would delete by an older reading.
  - On the PC, Claude's sessions run the tool under Brandon's allow rule in the repository's
    `.claude/settings.json` (November 10); a run with `--push-local` asks him, because it publishes
    commits that never left the PC. No agent adds a permission rule of its own.
- **Housekeeping runs on the host.** Never run `git worktree prune`, a checkout or a branch
  deletion through a mount, a container or a VM in which the worktrees' paths do not resolve.
  Reason: there every worktree reads "prunable" (all 89 did on November 10), and pruning would cut
  live worktrees from the repository. A census there is read-only (`GIT_OPTIONAL_LOCKS=0`). A
  shallow clone (a cloud session's) is read-only for the same kind of reason: it cannot tell
  ancestry, and on November 10 one read five merged branches as sharing no history with `main`.
  Which branches are merged is read on the PC's full clone, after a fetch.
- **Protected names**, never deleted by a census: `main`, `archive/*` and `codex/apple-silicon`.
- Stage explicit paths. Retire by explicit deletion, never by a broad restore, reset, stash or
  clean over work that has not been accounted for.
- Commit and push coherent, verified work only with the repository's configured identity
  (`brandonrdug@users.noreply.github.com`), never an address taken from harness context. Check
  `git log -1 --format=%ae` before pushing.
- A new worktree reuses the main checkout's Lean build before any Lean check: symlink
  `lean/.lake/packages` to the main checkout's and copy `lean/.lake/{config,build}` with
  `cp -r --reflink=always`. Without them, Lake clones and compiles Mathlib from source, which takes
  hours.

[definition] The repository is public. `.local/` holds private datasets, captures, models and run
artifacts. Publish source and scoped evidence, never raw private conversation or machine source
paths. Dataset roles and provenance are exterior codec information, not native semantic IDs.

Commands use Bash; with a fish shell, invoke Bash explicitly. CUDA may need
`PATH=/opt/cuda/bin:$PATH`. The gates, lowest first:

1. any code change: `bash tools/gate.sh` (the workspace check, THE_MACHINE's guard lints and the
   guards' `compile_fail` doctests; a guard that is not run does not hold);
2. once per step or PR: the tests of the laws that step wrote or changed. Inherited tests count
   only after rebuild step 1 has audited them.
3. at the end of a step that changes HNN behaviour or a kernel: the GPU suite, alone on an idle
   card, `flock .local/gpu.lock cargo test -p <crate> -- --include-ignored --test-threads=1`;
4. when Lean changes: the library build, `bash tools/lean_check.sh`.

Record one verification receipt per step, in its PR or issue. A timeout is incomplete evidence. A
change that adds or changes a mathematical law lands with its Lean counterpart, or names the
obligation it leaves in #410.
