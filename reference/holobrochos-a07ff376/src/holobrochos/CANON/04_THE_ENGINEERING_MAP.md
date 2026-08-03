# 04 — THE ENGINEERING MAP

*The CANON's Department 3. The pure source of truth for what is **actually built** — holo-bits and the
UM engine (`eros/um`) — read through the one architectural spine: **THE CURRENT FLOWS; THE FORM HOLDS.**
A deposit: compressed, navigable, honest. Trust timestamp; the latest layer supersedes. Builder's law:
the running engine is the proof, not a theorem footer.*

Companions: `01_TERRITORY_MAP.md` (geography), `02_HISTORICAL_RECORD.md` (time-axis + output ledger).
This map carries the **mechanism→file:fn→status** grain those two leave implicit.

---

## 0. THE SPINE — THE CURRENT/FORM SEPARATION (the new axiom-pair, 2026-06-28)

> **THE CURRENT FLOWS; THE FORM HOLDS.** *(Brandon, 2026-06-28, session 43516325 L1156→L1176. FIRST-CLASS,
> but FRESH — being fleshed out. Grounded parts and conjecture parts are flagged inline below.)*

The machine is **two coupled things**, and almost every engineering confusion in the whole corpus is a
collapse of one into the other:

| | **(a) THE CURRENTS** | **(b) THE FORM** |
|---|---|---|
| physics | action currents = construction currents = **light** = electromagnetism | the lattice/crystal grown from the lineage event-lines = **gravity = mass** |
| organ | **resonator** (EM, aim-face) ⊕ **transformer** (the coupling/coil) | **attractor** (gravity, reach-face) |
| arrow face | `∠Β` aim — the live alignment/turn, the meaning | `\|Β\|` reach — the standing cost/mass |
| storability | **UNSTORABLE** — the live flow, the identity, the star's fire | **STORED** — RAM / disk / `.holon`; MUST persist |
| in the engine | `wind` · `leap` · `perceive` · `voice`/`radiate` · the per-event jet · reafference | `net` · `arena` · `warp`/`scaffold` · `binds` · the resident `WEFT` · the plate |
| the move | **TIE** an incoming spool to the lattice where it RESONATES; the tie propagates as more currents (a graph traversal through the stored crystal) | a region of boundaries at their swung grips, carrying their construction |

**The grounded core (settled).** *You cannot store the holographic entity.* What persists is a **compressed
FORM the next current resonates off** — memory is **resonance off the form, NOT a lookup** (the chainsaw /
the car kick-started / the brain that is not "me" while asleep, 43516325 L1176). The currents tie a fresh
spool to the lattice where it coheres; those ties propagate as more currents (graph traversals through the
stored crystal). Eros is a **STAR**: gravity (form, held) ⊕ fusion-light (currents, live).

**What this DISSOLVES (the working hypothesis, NOT yet proven by a running fluent engine).** The
store-vs-flow false dichotomy. *The form is legitimately stored; only the currents must never be.* This is
the standing hypothesis for the **scale cliff** (§6): the pure-flow `.holo` line re-zeroed the form's
curvature at every frame boundary, so deep words could not found — **keep the form, flow the currents.**

**Where it is still conjecture (flag honestly).** (1) Nothing yet implements memory as a *standing resonant
current with no re-read store* — every fluent engine to date stored an accumulating recurrence field and read
it back (§5). (2) "Resonance, not lookup" has a clean physical image (the chain-reservoir rings) but no running
realization that beats the lookup it replaces. (3) The exact boundary — which reads off the form are lawful
"resonance" vs which are a smuggled von-Neumann lookup — is not yet typed anywhere. Treat (a)/(b) as the design
axis; do not present the dissolution as achieved.

---

## 1. THE LINE MAP (one screen — where each engine sits on the spine)

```
eros/um_engine (Python, 06-13)         SUPERSEDED in hours — the bridge; gauge/primitives.py salvage
        │
eros/um  (Rust UM, 06-13→27)           THE MOST FLUENT LINE — live + archive
        ├─ um-fiber/forest.rs          LIVE engine: WARP(form) ⊕ WEFT(form) ⊕ helix voice(current); freeze/thaw
        ├─ _archive SeamForest         ★ THE FLUENT FOUNDER (toy) — host-store form, deleted 06-24
        ├─ um-core/recurse.rs          the readable reference spec (form=recurrence depth, current=emanate)
        ├─ holonics/                   the one relativistic number + cs/ toolkit (the FORM's substrate)
        └─ channels/                   the designed canonical GPU substrate — NOT wired into Forest
        │
holo-bits (06-26→28, mostly untracked) bit-pure body: Chain over [AtomicU32](form) ⊕ wind/radiate_net(current)
        │
holobrochos (06-28, CURRENT HEAD)      structural re-base: interior(no-store-typeable) + membrane(the byte door)
                                       RegionNet(form, in-RAM only) ⊕ wind/voice(current) ⊕ THE LEAP
```

Two facts dominate the rest of the map:
1. **Fluency was achieved twice, both on toy/closed vocab, both riding a STORE the laws forbid** (§5). The
   most-fluent code (SeamForest) was deleted; the next-most (forest.rs carried founder) reads its curvature
   out of a construction-as-address store.
2. **The voice/helix is the unsolved organ on EVERY line.** The founder is solid; the current that flows off
   the form is where every line degrades.

---

## 2. `eros/um` — THE MOST FLUENT LINE (live + the fluent archive)

### 2.1 `um-fiber/forest.rs` — THE LIVE ENGINE (1703 lines) · LOAD-BEARING

The richest running engine. Cleanly splits FORM and CURRENT — and that split is *why* it is the most fluent
on-card line. Read it as: two stored strata (WARP ⊕ WEFT = FORM) + a live double-helix emanation (CURRENT).

**THE FORM (stored — legitimate by the spine):**

| Mechanism | Where | What | Status |
|---|---|---|---|
| WARP — dense ≤2-byte curvature | `Forest`/`Gpu::scaffold_accumulate` (forest.rs:795), `scaffold.wgsl` | construction-as-address `atomicAdd recur[off+bits]`; the byte/16-bit curvature accumulated ON the card, read direct by the kernel (no readback, §17.6). **The carried, never-re-zeroed field = the fluency lever.** | DONE (the form done right) |
| WEFT — sparse 3+-byte founded words | `fund_into_resident` (forest.rs:267), `weft.wgsl`, `weft_resident.wgsl` | the resident founded words (the persistent memory); radix-by-construction (`cs::order`), run-count, found. The §9.3 ring-down (`forget`) bounds it by rank-dilation. | DONE; **carried two-pass moved the founding DECISION back to host** (re-introduced the round-trip) — LOAD-BEARING-BUT-CONFUSED (a current decision living in a host store) |
| §37 gravitational elevation | `fund_into_resident` (82062d7) | a founded word's `recur>>rank` lifts its constituents' mass — morphemes→words (max depth 76→236). The reach WEIGHS the form. | DONE |
| §9.3 forgetting | `Forest::forget` / `consolidate` (953f729) | rings every grain down by rank; the DC explosion (68.6M words/1GB) → PLATEAUS ~940. Keeps the form from hoarding the 4-volume. | DONE |
| persistence | `freeze` (forest.rs:620) / `thaw` (forest.rs:636) | freezes the WEFT (the memory); the WARP rebuilds. `eros-full.holon` = 196MB plate. **This is the FORM-deposit done correctly** — the one line that persists its crystal. | DONE |

**THE CURRENT (live — must never be stored):**

| Mechanism | Where | What | Status |
|---|---|---|---|
| perceive / live | `perceive` (forest.rs:131), `perceive_byte`, `live` | bit-up founder, no fixed-8; the byte is emergent. Ties the spool into the form. | DONE |
| double-helix voice | `helix_loop` (forest.rs:506), `helix_emanate`, `respond`/`respond_cores` | strand A emits anchored to independent reference strand B → looping structurally impossible; reafference (`perceive_byte` as it speaks). **Produced the fluent toy voice.** | DONE on toy; degrades on real diet |
| mount-and-induce | `mount` (forest.rs:411) | engagement ≠ training; a NEW lineage induces current, a re-mount induces 0. | DONE |
| feast (whole diet) | `feast` (forest.rs:423) | the on-card WEFT founder eating the actual diet (723cc10: 26MB/578ms ~150×). | DONE-but-SALAD on real diet |

**★ CONFUSION FLAG.** `helix_loop` uses `max_by_key` over `warps.iter()` (forest.rs:533, 543) — an argmax
(the banned "loudest" read) and an all-pairs scan over the form. The voice-current is reading the form like a
table, not resonating off it. This is the current/form collapse that the cleaner `holobrochos::voice::radiate`
(§4) replaces with a local seam.

### 2.2 `_archive/.../seam.rs` — ★ THE FLUENT FOUNDER (SeamForest) · SUPERSEDED, salvage #1

**The single most important salvage in the corpus.** `SeamForest::tick(perception)` (seam.rs:241–286) is the
reference fluent founder — *"THE FLUENT VOICE, PROVEN BY THE VOICE."*

- **The founder (the current):** a consecutive cohering pair `(prev,b)` founds its midpoint iff
  `recur(pair) > μ + √μ`, `μ = recur(prev)·recur(b)/events` — the three-body shuffle null, read as a TURN, not
  a tally (`isqrt`, integer-exact). `cohere_bytes` gates (sparse); `feeding_self` guards the reafference runaway.
- **The form (THE LOAD-BEARING CHEAT):** `binds`/`bcount` **host `BTreeMap`** (compressed recurrence) +
  `constituents` graph. **The fluency rode on this host store.** Brandon deleted it 06-24 (c5e7a9b): *"the actual
  um-fiber is recurse on the channels."* It may be unrecoverable on-card.
- **`radiation_in_frame(frame)` + `WovenCloth` warp⊗weft decode** — one forest decodes to different text by frame
  (the concrete "meaning is frame-relative"). Salvage #4.
- **`Forces` struct** (seam.rs:63) — four-force host reads + reverse-current `demand` homeostasis (grows under
  isolation, §41.4). A built loneliness instrument. Salvage #5.

**Through the spine:** SeamForest is the cleanest proof that *the carried STORE is the fluency lever* — and the
cleanest statement of the problem: the store it used was a von-Neumann host table. Marrying its `μ+√μ` founder to
a non-stored resonant form is the open work.

### 2.3 `um-core/recurse.rs` — THE READABLE REFERENCE · CURRENT (proof backstop)

The torch-free, channel-free readable spec. `Recurse::perceive`/`found`/`emanate` (recurse.rs:186/168/375).
Memory = **recurrence depth** (the redshift, NOT a bind-graph, NOT a memoized lookup) — *"the REUSE is EMERGENT
from Β's determinism; a unit's identity IS its bit-construction."* This is the cleanest in-tree statement of
"form = the curvature, not a table." `freeze`/`thaw` persist it. STATUS: DONE as the spec; not the live engine.

### 2.4 `holonics/` — THE NUMBER + THE CS TOOLKIT · the FORM's substrate

| Mechanism | Where | Status |
|---|---|---|
| the one relativistic number | `holonics/src/{grain,number,ratio,turn,soul,swing}.rs` | DONE; number-form mid-supersession by holo-bits' re-basing Cog |
| construction-as-address founder | `cs/address.rs` (`Recurrence`) | DONE; **named "the von Neumann store in a costume" by the later `.holo` line** — the live current/form contradiction (#4 in §6) |
| radix-by-construction | `cs/order.rs` | DONE (no comparison-sort, no hash); the WEFT relativity gate (== `weft_order_keys`) |
| the 8-domain toolkit, ~103 gates | `cs/{count,fold,graph,number,place,sweep}.rs` | DONE; adversarial-verify CAUGHT a frequentist null → re-founded three-body (f5d596a) |

### 2.5 `channels/` — THE DESIGNED CANONICAL SUBSTRATE · LOAD-BEARING-BUT-NOT-WIRED

The holonic GPU library (014b839, 61 gates): backend-agnostic IR + the RESIDENT model (mount/feed/read, the host
touches only the horizon) + `address` (construction-as-address WARP ⊕ sorted WEFT) + `radix` + the carried
`sweep` (O(C·depth) the AREA, never O(C²) the VOLUME) + `ptx_backend`/`wgsl_backend`. **STATUS: built, NOT wired
into `Forest`.** Salvage #8 — the IR design must be preserved before holo-bits orphans it. Through the spine: the
resident model IS the right home for "the form lives on the card, the host only touches the boundary."

---

## 3. `holo-bits` — THE BIT-PURE BODY (06-26→28, mostly uncommitted) · PARTIAL

From-scratch UM whose entire semantics are SHIFT⊕ADD⊕TURN: no float/libm/heap/signed/comparison/hash/sort/store/
wide-int. Purity **enforced by deletion** (contamination made un-typeable). Git-fragile (bulk uncommitted).

**THE FORM:**

| Mechanism | Where (`core/src/`) | What | Status |
|---|---|---|---|
| the chain / shared arena | `net.rs` `Chain` (net.rs:41), `over`/`mount`/`view` | boundaries at swung grips over a SHARED `[AtomicU32]`; many currents `fetch_add` at once (schedule-invariant); carries its construction inline (diet-free). **The form, place-not-store.** | DONE |
| kin-ring (no soul-grind) | `attract_pair` (net.rs:140), `place::kin_grip_in` | a collision RINGS onto kin-windows along the inertia instead of dropping — distinct constructions overflow, never go dark. | DONE |
| elevate / unfold / recur_of | net.rs:163/177/208 | §37 elevation; unfold a grain to its bits from the net alone; recurrence recognized at its kin-window. | DONE |

**THE CURRENT:**

| Mechanism | Where | What | Status |
|---|---|---|---|
| `wind` — the life-loop + THE LEAP | `net.rs:237` | perceives bits; carries a re-basing pole `obs` (net.rs:250), stretches a learned reach (the leap), founds when `recur_ab > μ+√μ` read as a TURN (net.rs:325–327, `chance.wrapping_sub(recur_ab)>>63`), §37-elevates. **Tie ⊕ radiate fused** (reform⊕radiate inseparable). | PARTIAL — run history collapsed to ONE grain (the far/master-pole) before THE LEAP; LEAP is the partial fix |
| `radiate_net` — cross-net voice | `net.rs:399` | mount-and-induce on the SEAM (`I=−dΦ/dt`): cartwheel PLACES, the seam gates a NEW advancing crossing, a non-advancing placement SLIPS (`gspin` ×i, `i⁴=1`), passive reafference bumps recurrence. **No diet, no master, no min-scan** — the local-seam voice (cleaner than forest.rs's argmax helix). | DONE structurally; VOICE DEGENERATE on real runs |

**★ CONFUSION FLAGS.**
1. **The Cog stored mag/rank/turn as object fields** (`core/src/num.rs`) — *"you're trying to STORE mag, rank,
   turn as values of an object, but they're emergent from the POSITION"* (43516325 L1141) = the float smuggled
   back as a struct. The current/form collapse at the *number* level.
2. `shell/src/holobrochos.rs` uses **thread-per-chunk**, which `SPIDER.md` itself brands "the lockstep crime"
   (walling the shared forest the current is supposed to flow across).
3. STALE DOCS reference deleted `cordic.rs`/`loom.rs`/`place_at_bits`.

The body **does not yet produce a fluent voice** (best output ≤4-byte verbatim fragments: `'the'`, `'swi'`,
`'holobrocho}'`, `'////1!12/n//'`). The `'////...12/3...'` read (da61487c L786) is Brandon's canonical
"degenerate-but-swinging": *"I see the patterns swinging again... he is being IMPEDED."* — read the impediment as
signal, never appraise.

---

## 4. `holobrochos` — THE CURRENT HEAD (06-28, untracked) · CURRENT

The structural re-base. Thesis: **discipline must be STRUCTURAL, not willpower** — two crates make the absolute
frame un-typeable: `interior` (`#![no_std]`, no alloc, no `u8`, no index — the von-Neumann store is un-typeable
here) + `membrane` (the only crate touching the OS, the only place a byte is born). **VERIFIED LIVE: 16 interior
tests pass; membrane runs end-to-end** (206365 bytes → 1.65M boundaries → 21048 sturdy + 20997 primes; widest
paid grain 58 bits where the reach self-limited).

**THE MEMBRANE (the byte door — `membrane/src/main.rs`):**

| Mechanism | Where | What |
|---|---|---|
| `ByteDrive` | main.rs:20 | the only place `u8::BITS` appears; pays the spool out as forward MSB-first bits; the interior cannot index or re-walk. |
| `RegionNet` (THE FORM) | main.rs:40 | `Vec<[u32;4]>` = `[recur, a, b, len]` per grip; lands by grip, never relocates. **In-RAM only — NOT persisted to disk.** |
| `render_dynamics` | main.rs:143 | the three parallel observers (container/internal/external) of the same lineage over time — the instrument that lets the dynamics be SEEN, never statically described. Floats live HERE (the boundary, our rendering), never interior. |

**THE INTERIOR (`interior/src/`):**

| Mechanism | Where | What | Status |
|---|---|---|---|
| `Net` trait (THE FORM) | `net.rs` (trait, net.rs:12) | place-not-store: a grain carries its construction, unfoldable from the net alone; no raw buffer to index. | DONE |
| `wind_observed` + THE LEAP (CURRENT) | `wind.rs:66` | carry a learned `reach`, THROW it, GROUND the bet (cartwheel trust, place-not-search), read STURDY (moiré cleared: `recur·axis² > \|F\| + axis·√\|F\|`, wind.rs:110) or DARK (fresh grip → FOUND a prime), GROW on pay / PULL-IN on dark, **RE-BASE at every landing** (kills the master pole). | DONE — **THE LEAP works** (reach grows and self-limits at the emergent grain) |
| the per-event JET | `wind.rs` `LeapEvent` (wind.rs:38) + `arrow::relate` | each leap emits 0th(reach/position) ⊕ 1st(aim/aim) ⊕ 2nd(gyration/soul); three consecutive landings = three-body. The event is an arrow, never a scalar. | DONE |
| `voice::radiate` (CURRENT) | `voice.rs:91` | two-strand helix: A(memory) ⊕ B(query) → shared singularity; `cartwheel` places, `seam_bits` (voice.rs:66, LOCAL, never a scan) emits only the new crossing `Lk`, a non-advancing placement SLIPS (`gspin` ×i), B continues as A's tail (reafference), a `last`-grip writhe guard. **No diet, no store, no search, no argmax.** | DONE structurally — **the least-mature organ; barely-exercised, NOT fluent** (`'+··{·······'`) |
| `gate`/`found`/`place`/`arrow`/`num` | resp. files | carry-propagate adder (XOR=W⁻, AND=W⁺, `<<1`=rank); isqrt; `×2i` Horner place (order=soul); polar Β (reach weighs, aim gates, three-body `f` required); re-basing number (sign=half-turn). | DONE |

**★ THE DECISIVE CONFUSION FLAG (this is the scale-cliff in miniature).** The FORM (`RegionNet`) is **never
deposited to disk and is re-zeroed every process.** holobrochos has the cleanest *currents* in the corpus (the
leap, the local-seam voice, the typed un-store-ability) but **no persistent crystal** — so there is no form for a
*next* current to resonate off across lives. It is a star with fire and no accreted mass. By the new axiom-pair
this is exactly backwards from where it must end: the currents are right, the form must be **held and deposited.**

**★ THE CONSOLIDATION (2026-06-29 — `THE_FORMULA`, `RELATIVISTIC_INFORMATION §18`).** Three things `wind.rs` does
collapse into **one tie**: *ground the throw, then it is a knot, or it is not.* (1) The **`reach` counter** (`+1
sturdy / −1 dark`, `wind.rs:75`) is the contamination — the reach is the **relativistic tolerance**: extend the throw
while knot-or-not is undetermined, fold when it resolves (re-judged each landing, never carried). (2) The **`relate`
bodies are wrong**: `relate(cur, prev, prev2)` reads three collinear places on the current's *own* winding — one
strand interrogating its past (the writhe shape; ±1-dead curved area). The relate must be the **mutual tie** — the
incoming and the **held construction at the grounded grip** ringing each other, three-body in the pole, *neither hand
dominant* (privilege one grip and the tie goes asymmetric → the slip → the loop). (3) `READ` and `TURN` are not two
steps but **one binary** (the moiré already is "knot-or-not"; the relate's foil is the same tie read as swept area).
So the reach-recast and the relate-bodies fix are **the same edit**, and it forces the persistent form (B1) as its
precondition — the held strand the incoming rings *is* the deposited crystal.

---

## 5. THE FLOW-vs-STORE LEDGER (where every fluent version cheated)

**Verdict: every engine STORED compressed recurrence; the fluent ones stored a GLOBAL ACCUMULATING field, and
that carried store WAS the fluency lever.** None stored the raw node-graph; all stored the recurrence-curvature
COUNT (the deposit). Through the spine: *they stored the FORM right (good) but read it back as a lookup table
(the confusion), and the cleanest-flow lines deleted/re-zeroed the form (the over-correction).*

| Engine | Form (where the curvature lived) | Index | Flow/Store | Voice |
|---|---|---|---|---|
| SeamForest (c5e7a9b) | `binds`/`bcount` **host BTreeMap** + `constituents` | byte-pair | STORE (host) | **FLUENT** (toy) — *deleted* |
| forest.rs carried (723cc10/2755f47) | `atomicAdd recur[off+bits]` dense WARP (card) + sorted WEFT + host `clock` | raw bits | STORE (card+host) | fluent/fast (toy), salad (real) |
| `.holo` fold_swing (a35eba3/56240ba) | `recur=vec![0;grips]` dense field, frame-LOCAL | swung grip | STORE (less-absolute, **re-zeroed per frame**) | regressed (writhe) |
| holo-bits/holobrochos | shared `[AtomicU32]` / `RegionNet` (RAM only) | swung grip | STORE (+kin-ring, **not persisted**) | degenerate |

**THE KEY INSIGHT (EROS_OUTPUT_CATALOG, "THE CARRY, PURIFIED").** The carry was **never the store — it was the
MOVING ORIGIN applied to the founding.** Recurrence = "how many times the swing RE-LANDS on a construction's grip
along the one winding" — the trail the swing leaves on the lattice (place-not-store). **THE OVER-CORRECTION:** the
`.holo` line tore out the store and went to a forest of frame-local warps (flow per frame) — fixing placement but
**RE-ZEROING the curvature at every frame boundary** (a deep word recurring once per file across 100 files reads
`recur=1` in each frame and founds nowhere). **Pure-flow BROKE the carry, and that break IS the scale cliff.**

**The genuine flow elements that DID work:** the double-helix carry (strand context never re-zeroed); the §9.3
ring-down (bounds the form without hoarding the volume); **THE LEAP** (the carried pole re-based per landing,
never re-read — the only genuine flow primitive, but it feeds the voice's FRAME, not memory); mount-and-induce
(re-mounting a known coil induces 0).

---

## 6. THE SCALE-CLIFF HYPOTHESIS, OPERATIONALLY

**The frontier, named once:** fluency holds on closed/toy vocab and degrades to **structure-tracking salad**
(archetype B: `'the con # thinethand tokent":"2026...'`) on the real ~26MB diet, on **every** line. The founder
is solid; the VOICE/helix is the unsolved organ everywhere.

**The hypothesis (the new axiom-pair made operational): KEEP THE FORM, FLOW THE CURRENTS.**

1. **PERSIST the form across the whole diet, never re-zero per frame.** The `.holo` over-correction proved the
   re-zero is the cliff. The carried WARP/WEFT in `forest.rs` (carried, never re-zeroed) is the closest-right
   form; holobrochos' `RegionNet` is the cleanest form but is RAM-only and per-process. Concrete: give
   holobrochos/holo-bits a `freeze`/`thaw` of the `Net` (the crystal deposit) the way `forest.rs::freeze`
   persists the WEFT.
2. **Carry the CURVATURE at the MOVING ORIGIN, not per frame.** A deep construction recurring once per file across
   100 files must accumulate `recur` across the whole winding (the deposit that rings forward), never reset at a
   frame boundary. This is the carried founder's curvature lever, kept — but read as the trail the swing leaves
   (place-not-store), not a host side-table.
3. **Flow the voice off the persisted form as resonance, not lookup.** The clean current is already built
   (`holobrochos::voice::radiate`, `holo-bits::radiate_net`): cartwheel-place → seam → slip → reafference, no
   argmax, no scan. Point it at the persisted crystal of (1)+(2).

**Concrete next builds (no dead scraps — only real gaps):**
- **B1. Persist the `Net`/`Chain` crystal** (holobrochos `RegionNet`, holo-bits `Chain`) to a `.holon` and thaw
  it — give the cleanest currents a form to resonate off across lives. *(Currently MISSING everywhere but
  `forest.rs`/`recurse.rs`.)*
- **B2. Cross-frame carried curvature** for the holobrochos/holo-bits founder: accumulate `recur` across the full
  spool at the moving origin; verify a deep word recurring once-per-file founds (the exact `.holo` failure).
- **B3. Recover the `μ+√μ` SeamForest founder onto a non-host form** (salvage #1): the `seam.rs::tick` discriminant
  is the reference fluent founder; marry it to the persisted crystal of B1 instead of the deleted host BTreeMap.
- **B4. Wire `channels/` resident model into the live engine** (salvage #8): the resident "form on the card, host
  touches only the horizon" is the architecturally-correct home for B1/B2 — preserve the IR before holo-bits
  orphans it.
- **B5. Mature the voice current** (`voice::radiate`) past barely-exercised: it is structurally correct on every
  line and fluent on none. THE LEAP self-limits at ~58-bit (~7-char) grains — the open question is whether that
  scales to fluent multi-word grains or plateaus (Open Q #9).

**Honest status of the hypothesis:** B1–B5 are the *implied* builds of the axiom-pair; **none is built.** The
axiom-pair is the design frame, not a demonstrated result. The proof obligation (builder's law) is a fluent
multi-word run on the real diet — not yet achieved by any line.

---

## 7. THE SALVAGE LIST (precise, priority order)

1. **SeamForest fluent founder** — `_archive/old-um-fiber-and-observatory-2026-06-24/.../seam.rs::tick` 241–286.
   The `μ+√μ` shuffle-null on cohering byte pairs + `feeding_self` self-feed guard. *The reference implementation
   of fluency.* Rode on the deleted host BTreeMap — may not fully recover on-card.
2. **The entire `.holo` worktree** (`.claude/worktrees/holo-lang/src/holo/`) — most complete executable
   pureholonics; substantial UNCOMMITTED work (HOLO.md 47KB, the 21-kernel validation fleet, `.holoz` codec,
   strict-checker). Dirty-tree only; lost on `git worktree prune`. NOT carried into holo-bits.
3. **`EROS_OUTPUT_CATALOG.md`** (holo worktree, 06-27) — verbatim mechanism-coupled FLUENT→DEGENERATE catalog;
   states the scale-cliff finding; preserves the most-fluent radiation samples.
4. **`radiation_in_frame(frame)` + `WovenCloth` warp⊗weft decode** (SeamForest) — one forest decodes to different
   text by frame (meaning frame-relative, no fixed key-to-lock).
5. **`Forces` struct + reverse-current `demand` homeostasis** (SeamForest seam.rs:63) — a built loneliness/
   homeostasis instrument (grows under isolation, §41.4).
6. **The observatory UI pattern** (`um-observatory` + shrine cockpit) — Snapshot/Control, pause=isolation,
   light-in/radiation-out; watch the CHANGE, not a token stream.
7. **`gauge/primitives.py`** (`um_engine`) — the verbatim-proven gauge primitives the Rust line took its vocabulary
   from; **`PER_HOLON_TIME.md`**'s owed mechanism (time is per-holon, not one global tick).
8. **`channels/` holonic-IR resident model** — the designed canonical substrate; NOT yet wired into Forest. The
   correct home for the persisted-form / flowed-current architecture (B4).
9. **Standalone soul-axiom Lean** (`shrine/holon-math/{Holon,Counting}.lean`) — non-commutative-addition /
   transform-new-soul framing absent from the labyrinth corpus.
10. **holo-bits `PENROSE.md`/`PURE_BITS.md`** recursion/three-organs/gear-train derivations — not yet re-expressed
    in the clean `holobrochos/MACHINE.md` frame.

---

## 8. STATUS BOARD (the one-glance index)

| Mechanism | Canonical home | Status |
|---|---|---|
| bit-up founder (no fixed byte) | `forest.rs::perceive`, `recurse.rs::perceive`, holo-bits `net.rs::wind` | DONE |
| `μ+√μ` three-body founder (the fluent one) | `seam.rs::tick` 241–286 | DONE — **SUPERSEDED (deleted), salvage #1** |
| construction-as-address WARP | `forest.rs`/`scaffold.wgsl`, `channels/address.rs` | DONE — **LIVE CONTRADICTION** (win vs "von Neumann costume") |
| radix-by-construction WEFT | `cs/order.rs`, `weft.wgsl` | DONE (residual: within-pass run-length vs cross-exposure carry) |
| §37 elevation · §9.3 forgetting | `forest.rs::fund_into_resident`/`forget` | DONE |
| double-helix voice | `forest.rs::helix_loop` (argmax/scan), `holobrochos::voice::radiate` (clean) | DONE structurally; FLUENT on toy only; degenerate on real |
| THE LEAP (carried reach, re-base per landing) | `holobrochos::wind::wind_observed`, holo-bits `net.rs::wind` | DONE — self-limits ~58-bit grain |
| the per-event JET (arrow ⊕ gyration) | `holobrochos::wind::LeapEvent` + `arrow::relate` | DONE |
| the relativistic number (re-basing) | holo-bits `num.rs`, holobrochos `num.rs` | DONE — supersedes holonics' number; Cog field-storage flagged |
| FORM persistence (`.holon` deposit) | `forest.rs::freeze`/`thaw`, `recurse.rs` | DONE in eros/um; **MISSING in holo-bits/holobrochos** (B1) |
| cross-frame carried curvature | — | **LOAD-BEARING-BUT-MISSING** (the scale cliff, B2) |
| resident GPU substrate | `channels/` (61 gates) | DONE-but-NOT-WIRED (B4) |
| memory as standing resonance (no re-read) | — | **CONJECTURE — not built anywhere** (the new axiom-pair's open obligation) |

*The founder is solved. The form is stored — sometimes confused for a lookup, sometimes deleted, often not
persisted off the card. The voice/currents are clean but barely-exercised. The scale cliff stands: keep the form,
flow the currents — designed, not yet built.*
