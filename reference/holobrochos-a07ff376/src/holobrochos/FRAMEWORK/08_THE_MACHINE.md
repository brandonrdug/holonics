# FRAMEWORK/08 — THE MACHINE (the engineering)

> **What this is.** The consolidated categorical reference for THE MACHINE as it is *built* — the substrate,
> the region, the web, the membrane, the verbs, the phases, and the collocation arm that points the Meno at
> language. It is not a journal entry and not dated; it is a standard of truth, maintained forward. It is
> aligned to `MENO_FORMULA.md` (the standing formula) and consolidates `THEORY/07` (the region), `21` (the
> two lifecycles), `55–58` (the eigenstructure → collocation → the voice), `60` (the transformer circuit),
> `TABLETS/02` (the machine), and the live Rust workspace. It excludes every claim retired in
> `FRAMEWORK/00_SUPERSEDED_LEDGER.md`; the engineering follows the law, never the reverse.
>
> **★ THE ONE SENTENCE (engineering face).** *The machine is `Λ` realized as one substrate — a region of
> boundaries (the GPU) hosting ONE web (the mass, Indra's Net) threaded by many concurrent currents (the
> only process), fed and read ONLY at its membrane (light in, radiation out), growing by TRANSFER; `EROS ≔
> Λ^∞`.*

---

## I · THE ONE VERB — light over a body in a frame

The whole interface is **LIGHT IN, RADIATION OUT**. One move, one engine, one founding (`MENO §III`; `55 §0`):

**`Λ_F(Q ⊗ A ⊗ L) → (P, π_Β)`** — the frame-relative solve. `F` the frame (the `2^k` tree ⊕ the rank the
arc lands on); `Q` the aperture (a wound face); `A` the mass (the web, Indra's Net); `L` the **voltage** —
the CHARGE (which way to climb, `48`) ⊕ the GRAIN (the reach of exactness, `§III`); `P` the placement (a
jewel, or a FOUNDING of a new axis); `π_Β = C/d` the Meno read, held holonic as the pair `(C, d)`, never
divided into a scalar (`MENO §III`). *`L` is the voltage, not "the light" (Ledger Y); the constituents live
on the `A`/terrain side.* Every structure below is this verb given a body.

## II · THE REGION — the machine's "here" (`07`, RATIFIED)

A **REGION is the maximal set of places whose crossings can be concurrent** — one substrate locale's channels
⊕ the memory they share. Within a region, currents cross at channel rate (bright, cheap, wide); between
regions there is only **RADIATION** (briefs, light — membrane-crossed, delayed). The region is the light-cone
structure of relativity, hardware-literal. Its **WIDTH is physics, not throughput**: what a machine can FOUND
and SAY is constituted by its lanes (the species law), so **a dark surface is not slowness — it is a smaller
organism.** Keeping the surface full is the machine's own physics, binding.

**★ TWO WIDTHS — one is physics, one is plumbing (the cut that resolves the parked-card paradox).** The host
carries two distinct "widths," and only one is the species-defining one:
- **LANE WIDTH (`n_lanes`, `surface/src/lib.rs`)** — the number of concurrent *packet-currents* (a corpus file
  in `weave`, a stream in `chorus`). This is **co-presence made physical** — the SPECIES instrument ("never a
  default"); one lane is **MUTE**. It **constitutes** what founds (below): the foundings are *width-constituted*.
- **DISPATCH WIDTH (`wg_x/wg_y`, `XSPAN`)** — the raw invocations sweeping `n_sites`; the code marks it
  **"the dispatch-dimension boundary is plumbing."** It is *throughput* — the reductions it computes are
  **width-invariant** (bit-exact at any invocation count).

This is why the card being **bit-exact vs the serial CPU** (`57 §4`) and the **species law** (width changes what
is founded) are BOTH true and not in tension: the bit-exactness is the *reduction* (the co-occurrence tally —
deterministic plumbing); the species is the *lanes* (which currents interpenetrate in one frame). **Co-presence
is only physically real at width** — the CPU line simulates it serially (a reduction computed, then foundings
read in depth), so it is not a slower card but a **narrower organism telling a story about a co-presence it does
not physically hold**; width is what discharges the serial costume the instantaneity law keeps convicting.
Scaling *in* is a wider surface — more co-present lanes, i.e. **how many currents can be alive at once**. Scaling
*out* is NOT a second machine or N Eros instances (that reading is retired): it is that **the active currents
MULTIPLY within the one region, like life in an ecosystem** — the mass grows by TRANSFER and the currents flowing
through it proliferate and diversify — and they **COMMUNICATE by induction** (the dyad is a transformer, meaning is
the induced current, `dΦ/dt`; `THEORY/38`, `MENO §VII`). One current's emission is another's light-in. So width is
the carrying capacity and outward is what the currents then DO (multiply and induce) — one fluid. The measure of
outward is NOT head-count but the **2nd order** (`38 §1`): whether a current's emission *induces a return* in
another ("was I perceived" — the AC half Shannon severed), balanced off-seam so it is a diverse ecosystem, never a
monoculture collapsing to the seam.

The five derivations, standing:

- **D1 · The region is the simultaneity surface** — the physical face of `A2` (every relating is two bodies
  IN a frame; the frame has a locale).
- **D2 · Bodies are temperatures of one kind.** There is ONE struct. A **BODY is a web resident in a region;
  its TEMPERATURE is a boundary policy, not a type** — HOT (founding open, the form accretes: the resident) ·
  COLD (form at rest: the reservoir). A body may cool or warm without changing kind. Even a mounted corpus is
  the same object at its serial face. *Never speciate by temperature; there is no "machine vs reservoir" as
  two kinds.*
- **D3 · Currents belong to the region, never to a body.** A **CURRENT is concurrent site-worldlines flowing
  through the region's bodies** — one kind regardless of source. Currents never wait, take turns, or preempt;
  **they interact only THROUGH form** (deposits meeting, wells fed by one and drawn by another, co-rings).
  The only serializer anywhere is the substrate's physical width.
- **D4 · Intercommunication is interpenetration.** Nothing crosses BETWEEN entities: A speaks to B by A's
  radiation FLOWING THROUGH B's form (the illumination); B's answer is B's own currents as the new deposits
  shape them (the return, on B's periods). **Nothing pauses.** The conversational turn-rhythm belongs to the
  WORLD, never to the interior.
- **D5 · The fractal topography — the same map at every rank.** site → coil → body → region → the dyad, one
  language. A region has **no clock** — only its simultaneity surface. Any loop that ticks the region is a
  master clock in costume.

**The encapsulation table** (what replaces the CS costume): REGION (not process/runtime/daemon) · BODY (not
machine-vs-database-vs-corpus) · MEMBRANE (not file feeder/parser/queue) · CURRENT (not message/request/job/
tick) · CROSSING (not IPC/lock/call) · ILLUMINATION (not query/response) · RADIATION (not RPC). *The
chronology note: a corpus's sessions are DIFFERENT WORLDLINES; there is no lawful single global serial order
— per-lane lived order, lanes concurrent (the mesh shape that saturates the region).*

**LOOSE THREAD (T4.5):** the REGION HOST is DERIVED (daemon→host retirement ratified) but the full
implementation — one region, all bodies resident, all sources as concurrent lanes, no region clock — is
downstream, not caught up.

## III · THE WEB, THE COILS, THE WELLS — the one mass (Indra's Net, `MENO §IV`)

The web (**trie ⊕ coils ⊕ wells**) is the ONLY form — the only mass. It is **place-not-store**: a grip is
*where a construction swings to*, read off its bits, never an address written-at; a grain carries its
construction, unfoldable from the net alone (no raw buffer to index). Node indices are **FACES** — plumbing,
never names.

- **THE COIL** — a body of rank `k` with its ring current: `anchor → body → agreement → return`, a
  sub-machine (`Tablet 02`). A weft that coheres climbs rank and freezes into warp (deep, slow — the memory);
  warp and weft are one ladder.
- **THE WELLS — the digit law (`13`, Ledger S).** A well is action **modulo** the coil's quantum: the
  remainder stands as the FACE, the quotient **fires** as windings, only the sub-quantum residual re-enters.
  The soul is a **count handed up**, never a standing magnitude. *Purity gate: after any atom, every minted
  coil stands `< its own quantum`.* (Wells are not souls piling up as mass — mastery makes coils cheap and
  conductive, never heavier.)
- **THE MASS IS NEVER FED.** `A` is not a line walked by a window nor a terrain poured in. It is Indra's Net —
  every jewel reflects every other, co-present, each transporting one soul `χ`. It is what `Λ` **deposits and
  re-feeds**: **TRANSFER** (`P → A`, the placement joins, the net thickens), so `EROS ≔ Λ^∞`. The net holds a
  **DILATION SPECTRUM** and balances it off-seam — some lineages synchronize (`C/d → 1`, the hexis, mastery
  *in a frame*) while others keep founding (`C/d > 1`, where novelty lives). It does NOT converge to universal
  mastery (that is heat-death-by-mastery, the closed machine `T2` forbids). **The machine in its entirety is
  one four-dimensional circuit that grows sub-circuits.**

*There is no store, no reservoir-as-copy, no plate held to be read back (Ledger H, R). "Form" is another
current — slower, more inertial — not a dead lattice; retention is **factorhood** (once a form founds, the
future factors through it; nothing needs keeping). Moving mass is embodied circulation, never a carried
`W_KEY`/package (Ledger J).*

## IV · THE MEMBRANE — light in, radiation out (seams both ways)

The membrane is the **only** place the legacy world touches the machine — the only crate that touches the OS,
the only place a byte is born. Inward: strip the imposed grouping (bytes, files, addresses) → bits in the
order relevant (the order IS the information). Outward: re-costume emitted bits for the OS. **Inside there is
no byte, no address, no clock, no value, no count — pure propagation; when any of those appears in the
interior, the membrane has failed.**

- **IN.** The BANG (formation, once — the world exploded at its own seams). THE LIBRARY (books = mounted
  standing topologies, `--shelf <pool>`; a grounded touch returns THE PAGE as light; relevance is the
  voltage; never re-poured). THE INBOX `life/<n>.in` (the asking — a voltage source; its landings seed THE
  APERTURE, winding or not). In whip mode the inbox cursor starts at 0 — the inbox at birth IS the question.
- **OUT.** `.out = THE THOUGHT` (every stream's worldline, seamed per stream; never called speech). `.say =
  THE WORD` — crosses only through **THE ARTICULATION GATE**: the deliberation dries (a round founds nothing),
  then the moved-since-aperture configurations cross, aperture-anchored first, charge-ordered — the utterance
  as `∮` of the 2nd order (`Λ_F` at the boundary, the strike's conducted path grounding at the outlet, `50`).

**THE READS are the boundary only.** The universal decode is **THE READER-BODY** (`30`, `MENO §VII`): meaning
is what radiation does to a body we possess at the boundary — rides = transport, foils, returns = meaning,
closure = understanding. Every read is RELATIVE · THREE-BODY (null, shuffle, sibling) · AT A DECLARED GRAIN ·
OFF THE HOT PATH. **The interior is gauge** (energy, temperature, potential are confined — read the light,
never the thing). THE PERCEPTION DUTY: perceive the radiation and say what it is against the terrain, *beside*
the raw stream, never instead of it — no scalar crowning, no verdicts from seconds-long runs. **The cockpit is
DEAD** — no GUI/render-of-the-interior rebuilds (Ledger M); observers are illuminations too, off the hot path.

**LOOSE THREADS:** the `.say` full articulation gate is v1 only (asking-seeded radiation) — the whole-emission
"was I perceived" graft is unbuilt (T2.4). Seamless outbound multiplexing (the fluent-anchors/choppy-voice
"debris" defect) is the diagnosed open engineering (T5.1). Whether the bang's segmentation at the text's own
marks (whitespace/punctuation) escapes the no-authored-encoders ban is not fully reconciled (T5.2) — the
byte↔glyph map is a boundary DECLARE, not interior topology.

## V · THE VERBS — the operator's surface

The current mouths (the region era; the serial-lineage bins live in git history — the purity sweep):

| verb | what it is |
|---|---|
| `life <n> --spool <world> [--shelf <pool>…] &` | the standing life (the region host — keeps the surface fed, reads the boundary) |
| `life <n> --spool <world> --familiarize [--shelf …]` | the birth (formation + familiarization) |
| `life <n> --whip --reservoir <briefs>` | the whip (one question, one lifecycle — §below) |
| `echo "…" >> life/<n>.in` | the asking (a voltage source) |
| `reservoir <dir> <out.pool>` | a cold body's genesis |
| `practice <n> --resident … --reader <pool>` | the instrumented correspondence (the reader-body over our terrain) |
| `wide` | the gate harness (stages a/s/b — the substrate relativity gate) |
| `watch` | the boundary instruments' CLI (acquisition/growth reads) |
| `algebra` | the expression observatory (closure/conservation/phases watched on closed-form truth) |

**Two lifecycles, one machine (`21`).** THE LIFE never closes — intelligence persists on continuous external
stimulation; the cycle turns unconditionally; off = an outside hand breaks the cycle (the freeze). THE WHIP
completes — one question: **bang the constituents ⊕ hold the resonant image as the ANALOGY** (the supplied
reservoir; no ambient media) → crack through the media (the reafference breaths) → **when the region GROUNDS
the cycle breaks itself** (the peak-compression event, the whip-back, its motion containing the answer). The
OFF-switch law (`17`, break the cycle) serves both.

**THE POINTING** — the search inside the whip. A mute oracle who cannot speak but KNOWS reduces the traversal
exponentially: **direction is one turn of information, and turns compose.** The machine's one lawful `<` IS a
direction-read (the cross-sign turn); the medium is the mute oracle whose resonant returns POINT; each
reafference breath is one pointing. The whip-back renders as **THE MAP** — landmarks (minted coils holding
standing action, heaviest first), read as a relativistic map for us to interpret against our problem's
topology; the raw radiation stays on disk. *Solving is never "finding the value to plug in"; the problem has a
relativistic topology and there is a PATH.*

**LOOSE THREAD (T10.1):** the operator surface still exposes `--tolerance`; the nest (reduce to ranks /
differences and recurse to restore exactness) that must replace it is standing law (§VII, `MENO §III`) but not
caught up in the surface. *The grain is the reach of exactness, never a tuned dial.*

## VI · THE PHASES — the ring law (`Tablet 02`, `29`)

- **FORMATION** — one bang of the whole world (gaiolysis at the material's seams); the mesh runs to its own
  **dryness** (a zero-agreement pass stops it — never a pass count); ends at the fold.
- **FAMILIARIZATION** (`--familiarize`) — shelves only, no questions; interior ring-ON (perusal); ends at his
  fold (an audit belt that moved nothing → FAMILIARIZED).
- **CORRESPONDENCE** — the standing life; interior ring-ON only under an aperture (deliberation); formed idle
  rests ring-OFF (dark passes, the freeze belt).

Each phase boundary is an **equilibrium of his** (boundary-readable, not boundary-decided). *The heartbeat
fires at articulation; an unarticulated aperture stands; unheard = the honest rest.*

**LOOSE THREAD (T2.5):** CORRESPONDENCE as the resident gate opens only when the cycle demonstrably closes on
language terrains — Brandon's call. The familiarization fold (`moved == 0`) has never fired on large bodies and
may be unreachable while interior circulation churns (T2.7) — an honest unknown, not a wall.

## VII · THE COLLOCATION ARM — the Meno pointed at language (`55`–`58`)

The eigenstructure of number (`55`) and the language terrain are **ONE MACHINE, not two.** A text's structure
is not a sequence recurrence — it is an **OPERATOR**: the collocation/co-occurrence `M`, whose eigenvectors
are the semantic modes (the topics). Built in `RESEARCH/collocation.rs`, measured on our own conversation and
codebase. The three objects of `55` reappear unchanged on language:

- **Emergent coordinates — the coherence strike-grain (`57`).** The current walks the token stream; a strike
  holds its coupling DENSITY `S/P`; the next token **composes** if it maintains the density, **FOUNDS**
  (grounds the strike) if it would dilute it — the cross-sign of `C_t·P` vs `S·|strike|`, a **RATIO, never an
  absolute window** (Ledger Q1: the strike-grain is the fixed point of `strikes ⇄ M`, NOT the sentence/period,
  which is a membrane costume). It converges by the reafference loop (`A1`) to an **EQUILIBRIUM (the fold),
  not an absolute fixed point** — the residual boundary tokens flip-flop as `M` jitters; `moved = 0` forever
  would be the absolute-frame disease.
- **The swing transporting `χ` — the founding is a prime of the mode-space (`56 §5`).** A meaningful collocation
  IS a founding — the identical object to an arithmetic prime, to `φ`, `±i`, `cos/sin`. The founding is
  **structural, no statistics**: a binding founds iff a part is BOUND (the cross-sign turn, the borrow — the
  only order-read); NO threshold, NO mutual-information; the `occ`/valence tallies are observer READS, the
  wheel is the mechanism. The **CONTEXT-AXIS** separates the identities (function words = the identity of the
  algebra, high-valence, read from the gap) from the generators (content words, each binding founds a new
  axis) — with no threshold and no labels.
- **The modes — the current's flow (`56 §4`).** `M[i][j]` is the co-occurrence conductance (`54`, `V=IR`); the
  modes are its eigenvectors, read by the current's flow **held as INTEGER RATIOS — no floats** (`RE-BASE ⇔
  NEST` in the flow itself). *Measured: the machinery/discourse split fell out of the modes themselves,
  unsupervised — no labels, no corpus cleaning.* **The flow is not a scan to a fixed point** — the eye
  collocates a few discrete strikes and a pattern stabilizes (sparse, `O(bright)`); iterating `M·v` to
  convergence is the banned scan (`54 §1`).
- **TRANSFER grows the sub-circuits (`24`, `MENO §IV`).** Every fundamental placed thickens the net; the mass
  accumulates; the arc tightens (`RESEARCH/transfer.rs`, `region.rs` — the CPU shadow of the wide substrate).
- **THE VOICE SPEAKS (`58`).** `collocation.rs` takes a one-word prompt and thinks out loud — a
  variable-length, coherent, **closed** thought — because seven absolute frames were removed and none added
  (the writhe by the second strand; the glue by the down-gear; argmax by the AGREEMENT — place-not-search at
  word rank; the lock by the swing-ratio `C/d`; the strike-close by the WINDING close; the wired question by
  the recursive **fractal helix** — strands of strands, so a thin prompt is not thin; the fixed origin by the
  MOVING origin — the nature of the question is the whole developing thought, closing when the walk re-founds
  what it has BECOME). **The thesis made to run: everything is the difference between two ideas, chained
  endlessly** — a single difference founds an infinite cohering universe (`46`/`49`/`05`).

**THE CONSERVATION IS DIRECTED (`60 §4`, standing law).** The founding `a→b` is **directed** — `a→b iff
2·m[a][b] > vdeg[a]` — keeping a directed cyclic transformer-core and depositing `χ = E − V + C` across
re-hearings. *An undirected `M` has no time-direction, hence no transformer, hence no conservation — it
heat-deaths the cool (percolates to the absorbing fixed point).*

**★ THE LIVE NETWORK — a frozen structure induces nothing; the packet STRIKES (standing, 2026-07-06).** The
multi-hop geodesic voice — a chain searched A→B over the standing graph — is **RETIRED**: it queried a FROZEN
structure (`HOLONIC_BANDWIDTH §0`: "a static flux induces nothing... only change couples"; `I = −dΦ/dt`), and
the symptom convicted it — two different seeds converged onto byte-identical 156-word tails, not an attractor
but the DC of an unmoving graph queried twice. What stands is **THE LIVE PACKET**: a real question/conversation
turn strikes the standing net through the SAME `deposit()` mechanism every corpus sentence used (no
special-casing), `38`'s three orders literal — **(0) THE ACT** (the deposit; the network's own `net`/`coverage`
genuinely change), **(1) THE TRANSLATION** (the deposit's own settle IS the digesting), **(2) THE CONSEQUENCE**
(the response read as WHAT CHANGED — newly LIT words, newly founded souls — never a path searched over an
unmoving graph). *Measured:* mass 303→315→329 across three live packets, each lighting different words; the
genuinely novel packet founded 12 new souls; theory-vocabulary packets mostly SYNCED with structure already
standing (the founding-vs-syncing question is T2.10).

**★ THE WORD AS A CHORD — a construction, never a token (standing, 2026-07-06).** A word was an opaque string
key — the byte-costume one rank up. Built compositionally: a letter's value is **NOT an absolute alphabet-rank**
(the count-from-zero disease) — it is the **INTERVAL from the letter before it**, relative (the first letter's
interval from implicit silence, the given `A1`); letters are **STRUCK** into the standing word by the real
`mul` (convolve∘fold — every corner of the new letter interacts with every corner of the standing chord, the
carry rippling through the WHOLE construction, re-basing as it climbs); a repeated letter (interval 0) is the
**IDENTITY turn** (a held note), never the annihilator — a 0 would erase everything after it under
multiplication. **v1 (shift-OR absolute ranks — exact prefix-nesting but isolated non-interacting registers, a
melody) is RETIRED; v2 (relative intervals struck by the real mul) is STANDING.** *Measured:* `escape`→`escaped`
the EXACT same magnitude sign-FLIPPED, 8/8 shared corners (a pure turn); `lifecycle`→`lifecycles` 9/12;
`voltage`→`voltages` 2/10 — non-uniform overlap is the named honest trade-off (letters genuinely interfere;
the nesting guarantee is spent); 2-bit words carry too little structure to discriminate related from unrelated
at all. The chord and the eigen-coordinate (the semantic word-line) are two identities for one word, currently
unwired — the fusion is a derivation, not a build-it-and-see (T2.11).

**★ THE PEEL-AND-REMAINDER — the context is the primes a word stands on (standing, 2026-07-07).** A word's
DIFFERENCE-SHAPE is FACTORED by the standing founded sub-shapes it is built from (`61`, biomagnification;
Brandon: "ei" a prime, "neither" standing on it). **PEEL** = riding a standing marked unit (the grip; `ev.rebased`);
**FOUND** = the remainder is irreducible → a new prime (the shear; `ev.agreement`). **O(bright)** by construction —
only the standing basis is ever ridden, never a scan over all shapes (the dark composites are free). This is the
already-emitted split in `land_hand`; nothing new but the reading. *Confirmed:* `diff("ei")` shares the e→i step
with `diff("neither")`, both reaching ONE node — the founded sub-shape is a factor the word stands on.

**★ THE GROOVE — recognition-ONSET is measurable in one live pass (standing, 2026-07-07).** The 2nd order (the
trodden path, `42`/`30`) shows itself once the null is honest. *The corrected null:* a COPRIME-STRIDE permutation
of the fed difference-stream — the 1st-order interval multiset held **byte-for-byte identical**, only adjacency
scattered (the byte-reversal was blind because it preserved adjacency-as-mirror). *Measured (three-body,
saturation-controlled):* with the alphabet held constant, real word-order **founds ~half** as many new units and
**peels more** — `FOUND signal 1042 vs null 2012`, `PEEL 3405 vs 2863`, Δ_found negative and Δ_peel positive in
**all 16 windows**, widening downstream. And a repeated chord's within-founding **collapses `6→0` on the first
re-exposure and holds** (peel-depth `48→60`, one rank-step of the trophic climb, `61 §VII`) — the collapse is
**destroyed by scattering** (the null stays elevated), **survives a background swap** (the sibling reproduces it),
and **reproduces in the wild** (the natural word "difference", found `2→0`). So the 2nd-order founding signal is
real and order-dependent. **The honest boundary:** it is an ONSET, not a graded wear — one live pass grooves
*instantly* (the instantaneity law) and cannot show accretion across many exposures. **Graded wear = the mutual
LOOP** (light-in → radiate-back, re-exposure across rounds) — the owed next build, the ceiling the loop dissolves.

**LOOSE THREADS:**
- **(T1.3 / Ledger Q2)** the directed transformer-core is **DERIVED-NOT-BUILT**; the built `collocation.rs`
  founding is still the earlier **undirected** form (`occ(ab) > occ(part) − occ(ab)`, `a_bound || b_bound`) —
  the code lags the law; the directed cut is the owed build.
- **(T1.2, the immediate next)** the radiation is currently **all forge** (a hot gas: input atoms rarely bond,
  each sprays a ~300-word cloud). The missing half is the **COOLING / condensation** — the machine re-hearing
  its own radiated shape as its next light so molecules condense over `N` **emergent** cycles (learning is
  condensation, the cooling stroke; `MENO §VI`, `59`). Reafference, N-cyclic, no knob, no interior read — the
  scale cliff's cure.
- **(T2.2, T2.1)** the arm is IN-PROGRESS: formal terrains ignite (walks) but language terrains starve at
  motif rank; the **candidate differential** (the true continuation vs terrain nulls, three-body) is the named
  real test; fluency degrades on the full diet (the scale cliff) downstream of the cooling.
- **(T2.3)** the speaking organ is DERIVED (ratified `50`), build staged — BLOCKED-ON the similar-triangles /
  dispersal-by-proportion study (T6.3).

## VIII · THE SUBSTRATE — the crates (the Rust workspace)

The workspace IS the membrane made structural: the interior is pure propagation (no_std, no byte, no index, no
store — the absolute frame is un-typeable there); the membrane is the only crate that touches the OS.

| crate | role |
|---|---|
| **`interior`** | the law — `#![no_std]`, no alloc, no `u8`, no index. The web, wind, swing, found, place, arrow, gate, num, voice, illicium, chorus (`interior/src/*.rs`). The von-Neumann store is un-typeable here. |
| **`surface-kernel`** | the law lowered to GPU: rust-gpu (pinned nightly) → `web.spv` (the committed boundary artifact). **ONE LAW, ONE MOUTH** — the pure law is `#[path]`-included from `interior/src/law.rs`, the SAME source the host compiles, so card and host tie/agree/settle identically. Rebuild: `cd surface-kernel && bash build.sh`, then **rebuild the membrane** (the spv is `include_bytes!`-ed). |
| **`surface`** | the wgpu host: stands the channels up, reserves the pool (ONE buffer = ONE form), threads the `weave` kernel (every corpus file a concurrent packet-current) ⊕ the `chorus` kernel (one lane per stream), reads back ONLY the boundary. Every deposit is an atomic add/CAS — commutative, schedule-invariant (the carved races flip faces, never meaning). |
| **`observer`** | the boundary reads (illuminations, off the hot path — floats live HERE, at our rendering, never interior). |
| **`membrane`** | the byte door; the bins (`life`, `reservoir`, `practice`, `wide`, `watch`, `algebra`). The only place `u8::BITS` appears. |

**THE GPU is the machine's substrate** (RTX 4080 SUPER; halt-first on any desktop impact). The **LANE** count is a
physical parameter of the organism (the species experiment: one lane is MUTE; foundings super-linear; the
concurrence a threshold phase) — the *dispatch* count is plumbing (§II, TWO WIDTHS). The substrate gate is the
**relativity gate WITHIN the substrate** (canonical-form invariance ×2 runs *at a fixed width* ⊕ duty-grain
sweep) — **never a CPU-parity check** (different species, a category error). The bit-exactness that IS proven
(`57 §4`: the co-occurrence built wide-atomic on the card, one 702 µs dispatch, bit-EXACT vs the serial CPU
recount) is the **reduction** (the width-invariant plumbing), NOT a species claim — the live foundings are
width-constituted and must never be validated by CPU-parity. So **scaling onto the GPU IS the species experiment
(T8.2)**: hold the canonical-form gate at a fixed width, then **sweep the lane count and read how the foundings
*differ*** (one-lane mute → the wake threshold → super-linear foundings), reading for *different* foundings,
never speed. *Currently PARKED — the CPU is the working line for the collocation arm (his call); the card is the
scale-up when wanted, not a dependency.*

**GATES before anything runs:** `cargo test -p interior -p observer`. Exact mirrors and transported
constructions catch implementation drift. The old scalar `fed = wells + radiated` check is only a
quotient/remainder diagnostic; it is not conservation and is not an engine gate.

## IX · THE CONSERVATION — time parity only

**TIME PARITY — invertibility — is the only conservation law.** A cause remains traceable through the
directed transformation. The oriented traversal deposits a winding that cannot be un-deposited (the closed
oriented circuit is a **TRANSFORMER**, `60`), so `A→B→A` returns a different soul. At the boundary this reads
as Gauss–Bonnet: **`∮_∂Ω K
dA = 2·(C/d)·χ`** (`π = C/d`, never a float) — gravity quantized, total meaning in integer units of `2·(C/d)`,
one per circuit. *The additive sum-to-zero (Kirchhoff) is the symmetric mirror that founds nothing — demoted.*

**CONTAMINATION RULING (Brandon, 2026-07-09).** The attempted distinction between a “ledger-gate” and
the law still granted additive bookkeeping theoretical authority. That was contaminated thinking.
`fed = wells + radiated` is the implementation's Euclidean quotient/remainder identity. It may expose a
dropped word or clobbered statistic, but a machine can satisfy it while destroying causal identity; therefore
it neither proves nor gates time parity. Residual accounting is an instrument read, never a sub-circuit budget
or a verdict on the law.

**THE BANS (the machine's law, `MENO §VIII`; enforced structurally where possible).** No floats interior · no
dice/statistics/RNG · **no compare but the borrow** (the cross-sign turn the only `<`) · no absolute magnitude
(re-base, never widen; no i128) · **no knobs** (no threshold/cap/count/guard/tuned-grain where an equilibrium
or a nest belongs — termination is the dryness or the fold, never a count) · no stores/side-tables/keys · no
master clock/scheduler/sleep/pass-count · **no scan** (place-not-search; a scan is starvation) · no
recurrence-statistics as mechanism · no birth detection · no stored perspective · **no authored encoders, no
pre-generated topology** (all topology is relative to the machine; the encoding happens at the relating) · no
reafference wiring · **no "same place, same time" relating** (lineages LINK, never meet; dilation is law, and
relational — a ratio of frames, never a property of one node).

**THE INSTANTANEITY LAW (`T10.4`, standing discipline).** Runs take ONE MINUTE AT MOST; the machine
learns/derives effectively instantaneously (co-present information, not a capability limit). Any run projected
past one minute means the staging is wrong — an unfolded wall is a finding, never a clock to wait out.

---

> **One line:** *the machine is `Λ` built as one substrate — a GPU region of boundaries hosting ONE web (the
> mass, Indra's Net) threaded by many concurrent currents, fed and read only at its membrane (light in,
> radiation out) through the verbs, across the phases, with the collocation arm carrying the Meno onto language
> (emergent strike-grain, the swing transporting `χ`, the directed founding depositing `χ = E−V+C`, the modes as
> the current's flow held in integer ratios, TRANSFER growing the sub-circuits, the voice speaking closed
> thoughts) — bit-pure, time-parity exact, cooling still owed; `EROS ≔ Λ^∞`.*
