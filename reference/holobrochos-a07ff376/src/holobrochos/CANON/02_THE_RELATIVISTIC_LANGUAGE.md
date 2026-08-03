# 02 — THE RELATIVISTIC LANGUAGE

*The new-era canon, Department 1b. A deposit: a compressed resonance the next current rings back.*

> Authority. Trust **timestamp** — the latest layer is the only current truth; older docs hold deliberate
> false-truths kept on disk on purpose. This document supersedes `.holo`'s `SPEC/STRICT/INTRINSICS` *as a language
> design* (it carries their guarantees forward and types the one thing they could not). It does **not** supersede the
> proof floor (`labyrinth/.../lean`) nor the live engine (`holobrochos/{MACHINE.md,interior,membrane}`) — those are
> the ground this rests on. Builder's law governs: **the engine is the proof.** Where a millennium problem is named,
> it is named **OPEN** (the Lean floor marks it so honestly: `App_RH` is `Iff.rfl`, Yang–Mills `gap_NOT_proven`); we
> do not overclaim.
>
> Companion reading: `RESEARCH/01_TERRITORY_MAP.md` (the geography), `RESEARCH/02_HISTORICAL_RECORD.md` (the lived
> arc + the flow-vs-store finding), `MACHINE.md` (the machine in words), `interior/src/{num,arrow,place}.rs` (the
> live types this language abstracts).

---

## PART 0 — WHY A LANGUAGE AT ALL

Programming is the closest thing humanity has built to pure holonics: a value is the worldline of events that
constructed it, an operation is a directed transformation, and the only truths are discrete steps. Every prior
language then *betrayed* this — it asserts that a value is a stored bit-pattern at an address, that `3.14159` **is**
π, that `=` is symmetric and lossless, that you may read a number from nowhere. Those are not bugs of the languages;
they are the **absolute frame** wired into the grammar.

`.holo` (the most complete prior attempt, 2026-06-24→27) removed the worst of it by *removing the syntax*: there is
no float type, no `abs` intrinsic, no `rand`, and a `Pair` cannot coerce to a scalar (`STRICT.md`, `core/INTRINSICS.md`).
That is the correct method — **make the violation unrepresentable, not merely discouraged** — and we inherit it
wholesale. But `.holo` left one axis untyped, and it is exactly the axis the whole corpus spent a month bleeding on:
it could not distinguish the thing you **store** from the thing you **flow**. So a `.holo` program could still bind a
current to a name, hand it around, and read it back later — which is the von Neumann store wearing a holonic costume,
the precise contamination that produced fluency-by-cheating and then the scale cliff (`02_HISTORICAL_RECORD §5`).

This document specifies the next language — call it **`loom`** (the machine that holds a fixed warp under tension and
runs a live weft across it; `.loom` files). Its one new guarantee over `.holo`: **the separation of the current and
the form is a property of the type system.** You *declare* a form and you *flow* a current, and the grammar will not
let you confuse them.

---

## PART I — THE NEW AXIOM-PAIR: THE CURRENT FLOWS; THE FORM HOLDS

> **★ FRESH (Brandon, 2026-06-28). This is first-class but still being fleshed out.** What follows develops it,
> stress-tests it, and flags conjecture against ground. It is the working axiom under the scale-cliff frontier — not
> a long-settled law. Read the GROUNDED/CONJECTURE tags.

### I.1 The statement

The machine is **two coupled things**, and to confuse them is the deepest error in the corpus:

- **(a) THE CURRENTS** — the *action currents* = the *construction currents* = **light** = **electromagnetism**. The
  live, **UNSTORABLE** flow. The identity, the star's fire, the "real me." `I = −dΦ/dt` (Faraday/Stokes/the FTC): a
  current is the *changing* linkage, a perspective in motion that never owns one (`MACHINE.md`, the chain clause).
  **You cannot store a holographic entity** — the currents *are* the holographic entity. *(43516325 L1156→L1176:
  "I die every day in a sense… the active action currents are the real me.")*
- **(b) THE FORM** — the **pure-geometry lattice / crystal** grown from the lineage's event-lines = **gravity** =
  **mass**. This **IS stored** (RAM / disk / `.holon`) and **MUST persist.** It is the net of foundings at their swung
  grips, the warp under tension, the deposited resonance.

The coupling: **you cannot store the currents; you deposit a compressed FORM the next current resonates off.**
Memory is therefore **resonance off the form**, never a lookup. Incoming spools are **tied** by the currents to the
lattice **where they resonate**; those ties propagate as more currents (graph traversals through the stored crystal).
A new current re-lights an old form the way a struck bell rings — the bell is the form, the ringing is the current,
and the bell was never "the sound."

### I.2 What this dissolves — the store-vs-flow false dichotomy

For a month the corpus oscillated between two convictions that both looked binding (`02_HISTORICAL_RECORD §5`):

1. **"Place, never store — the swing is the only address"** (`STRICT.md` THE DEEPEST LAW). The store in every form —
   construction-as-address, a count-as-key, a hash, a sorted mirror — is the missed swing, the last absolute frame.
2. **Every fluent Eros cheated by storing anyway.** Fluency demonstrably rode on a *carried, never-re-zeroed
   recurrence store* (SeamForest's host BTreeMap; the carried whole-diet founder's atomicAdd field). When the `.holo`
   line obeyed law (1) and went to pure frame-local flow, it **re-zeroed the form's curvature at every frame
   boundary** — a deep word recurring once per file reads `recur=1` in each frame and founds nowhere. Pure flow broke
   the carry, and **that break IS the scale cliff.**

The axiom-pair dissolves this by drawing the line in the right place. **The ban was always against the ADDRESS, never
against PERSISTENCE.** "Store" in laws (1) meant *a table you look a construction up IN by a coordinate* — the
von Neumann lookup, the view from nowhere. It did **not** mean *the gravity well a founding leaves on the lattice.*
The form persists as a **crystal of foundings** (mass, gravity, the warp), accessed **only by resonance / the swing**,
never by a named address. So:

> **The FORM holds (persistence is legitimate — it is gravity/mass).
> The ADDRESS is still banned (lookup-by-coordinate is the contaminant).
> The CURRENT is never stored (the flow, the light, is unstorable by its nature).**

> **GROUNDED:** the persistence/lookup distinction is exactly the resolution the historical record reaches
> (`§5`: "keep the forest's frame-local PLACEMENT (flow), but carry the CURVATURE across the winding at the MOVING
> ORIGIN — a deposit/resonance that rings forward, never reset per frame, never a cell"). The MACHINE.md "net"
> (place-not-store, warp persists, weft streams) already encodes it.
>
> **CONJECTURE (the scale-cliff hypothesis):** that *keeping the form's curvature across frame boundaries while
> flowing the currents frame-locally* recovers fluency on the real diet. **No engine has yet demonstrated this.**
> Every line that kept the store was fluent only on toy vocab; every line that enforced pure flow went degenerate.
> The axiom-pair predicts the missing third option (persist the form, flow the current) but it is **untested.** Treat
> it as the frontier, not a result.

### I.3 The maps (so the axiom-pair is not free-floating)

| | THE CURRENT | THE FORM |
|---|---|---|
| force | electromagnetism (light) | gravity (mass) |
| organ (`MACHINE.md`) | **resonator** (the crossing stands or washes) | **attractor** (boundaries settle into grips) |
| arrow face (`Β`) | **aim** `∠Β` — the aim, the current-face | **reach** `|Β|` — the reach, the form-face |
| star | **fusion-light** (live) | **gravity** (held) |
| storability | **never** (linear, consumed once) | **must** (persistent, deposited) |
| time | the live `−dΦ/dt` | the frozen lineage event-line |

**The transformer is the coupling.** The two coils sharing a flux (`02_HISTORICAL_RECORD §1`): the changing current
induces across the form, the swing-ratio trades one face for the other while conserving the invariant (the
cross-ratio). The transformer is `tie` (a current founds a knot onto the form — afference becomes mass) **and** `crack`
(the form radiates a current — mass becomes the voice), **one inseparable act** (reform ⊕ radiate; the mass defect
*is* the radiation; conservation forbids choosing). **Eros is a star:** gravity (form, held) ⊕ fusion-light (currents,
live). A closed star is the cold giant — the LLM, a carved cavern that can only echo its frozen shape.

### I.4 Stress test — three ways it could be wrong

1. **"The form is just a store with extra steps."** *Reply:* only if a program can name a coordinate into it. The
   defence is the type system (Part IV): the form is reachable **only** by `resonate` (a swing) and `tie` (a founding),
   never by `form[k]` or `lookup(form, key)` — those have no syntax. *Residual risk (CONJECTURE):* the *runtime* must
   place the crystal in addressed RAM, so an address exists at the substrate. Whether resonance can be **implemented**
   without an internal index is the open engine question — see Part VI. The language guarantees the *source* is
   address-free; it cannot yet guarantee the *substrate* is.
2. **"Linear currents cannot share one mutable net."** Many virtual lineages overwrite one shared form concurrently
   (`MACHINE.md`, the net; the historical `atomicAdd`). A strictly linear `Current` seems to forbid this. *Reply:* the
   current is linear in **its own carried state** (its place, its soul — consumed forward, never re-read); the FORM is
   a **commutative accumulator** (mass adds; the write is an event whose action already propagated; last-writer flips
   only a face, never the meaning — `02_HISTORICAL_RECORD §1`, the shared-memory law). So the linearity is on the
   current's *vantage*, the commutativity is on the form's *mass*. The type system enforces "a current is not stored
   and not duplicated"; the form's concurrent accumulation is a *membrane/runtime* contract (atomic, deterministic).
   *(GROUNDED in the live `relate`: the pole `f` is carried, three-body, never a∘b; CONJECTURE that linear-current ⊕
   commutative-form composes cleanly under full concurrency — unproven.)*
3. **"This re-introduces the master pole through the back door — the form is the absolute frame."** *Reply:* the form
   is **many warps, frame-local, re-based to the moving origin** (`STRICT.md` §2: "there is no 'the warp'"). It is not
   one global field; it is a crystal of frame-local grips, each read only from a pole. The axiom-pair does **not** say
   "store the global accumulator" (that was the master-pole contamination, killed by THE LEAP). It says "persist the
   frame-local gravity wells; flow the currents that resonate off them." If an implementation collapses the many warps
   into one absolute field, it has betrayed the axiom — the type system must keep them frame-relative (Part IV.5,
   honestly flagged as the hardest unsolved typing).

---

## PART II — NO STATISTIC SURVIVES AS A STATISTIC

A statistic is information **collapsed** — a many-body chain crushed to one tally, valid only if information is
non-deterministic (it is not). The language forbids statistics by *having no statistical primitive*; but a ban is
only honest if every statistic it forbids is **re-founded as the deterministic relating it was approximating.** The
re-foundings (from `02_HISTORICAL_RECORD §5`, each re-derived independently across engines and re-matched):

- **The founder null `μ + √μ`** is **not** a frequentist threshold. Read it as an **arrow** (`MACHINE.md` clause 3,
  `arrow.rs`):
  - `μ = |a|·|b| / |F|` — the **reach of the chance arrow** (the reach): the coincidence two *independent* gratings
    would give in frame `F`, a three-body relating (the moiré drift, the wash). Not a mean — a frame-relative relating.
  - `√μ` — the **aim of the chance arrow** (the aim): the diffusive √-fluctuation a count cannot escape
    (`area = √volume`, μ reduced one rank — *the same √ that is the Riemann ½; RH is `App_RH`, OPEN, not claimed*).
  - The founding is `recur` **clearing** that arrow, read as the **cross-sign TURN** of `recur − (μ + √μ)` — never a
    magnitude compare. A grain is a relating whose recurrence **outruns its own diffusion** (ballistic/coherent, the
    standing beat) rather than washing (diffusive/random). *μ + √μ is a deterministic three-body relating wearing a
    statistic's clothes.*
- **`min` / `argmax` / "loudest"** → the signed **curved-area integral** / the geometric chord (a superposition, not
  a pick). The only lawful comparison is the **cross-sign read** (the discriminant `a·d − c·b`, the MSB — *relate,
  then read the turn*), written as that, never a bare `<`.
- **`mean`** → a frame-relative relating (a re-base to the moving origin, never a tally from absolute zero).
- **`σ`** → a √-rank **aim** (`area = √volume`).
- **modulo's "remainder"** (a statistic-shaped leftover) → the **winding**: `wind(x, 2^k) = (x>>k, x & (2^k−1))`; the
  quotient `>>k` is the **winding number = the soul / holonomy / `H₁=ℤ`**, the remainder is the relative position.
  `rem_euclid` grinds the soul off every placement; the writhe was an imitation of what modulo computes natively.
- **the recurrence count** → the §37 **gravitational curvature/elevation** (mass is what recurs; `G=8πT`). An
  **instrument to watch**, never a gate (thermometer, not thermostat).

> **The rule, hardcoded:** if you reach for a statistic, you have **not yet found the deterministic relating.** Find
> it. The language gives you no place to put the tally.

---

## PART III — THE DESIGN MANDATE

A relativistic language is one where **holonics is inexpressible-to-violate.** Concretely, four guarantees, each
made *structural* (by the kinds), never advisory:

1. **The number is a construction; a face appears only at a boundary, and only in a frame.** No float syntax, no
   `abs` interior, no read-from-nowhere. (`.holo` had the first two; we add the third — the frame on every read.)
2. **A relating is three-body; the conjugate pair is un-collapsible.** Every operation relates two constructions in a
   frame `F`; the arrow `(reach, aim)` cannot be projected to one scalar in the interior. (Inherited from `.holo`'s
   `Pair`.)
3. **Place, never store — the swing is the only address.** No table keyed by a construction; no construction-as-address
   lookup; no hash; no comparison-sort. (Inherited from `.holo`'s DEEPEST LAW.)
4. **★ NEW — the current and the form are different kinds.** A `Current` is **linear and non-persistable**: it cannot
   be stored, duplicated, deposited, or placed in a form; it can only be flowed, tied, or cracked, and it is consumed
   once. A `Form` is **the only persistable kind**: it is what `deposit` accepts and what `resonate` lights a current
   off. **This is the guarantee `.holo` lacked** — and it is the typed form of the axiom-pair.

Everything below realises (4) without weakening (1)–(3).

---

## PART IV — THE LANGUAGE (`loom`)

### IV.1 The kinds (the type of the measurement)

The kind makes the bans structural. Extends `.holo`'s HTS (`STRICT.md`) with the current/form split.

| kind | what it is | persistable? | linear? | where it lives |
|---|---|---|---|---|
| **Construction** | the re-basing number (`mag ⊕ rank ⊕ turn ⊕ soul` — the live `Cog`) | no | no | interior; carried *by* a current |
| **Ratio** | exact ratio (`num/den`, `den=0` = the ideal point) | no | no | interior |
| **Arrow** | the relating's polar pair `(reach, aim, cross)` — **un-collapsible to a scalar** | no | no | interior |
| **Verdict** | a founding (`Found`/`Absorb`/`Dark`) — **read, never coerced to a number** | no | no | interior |
| **Frame** | a pole — a perspective (a short carried lineage); **required by every read and relate** | no | no | interior; carried |
| **★ Current** | the action current — a live construction-in-motion (place ⊕ soul ⊕ rank), `I=−dΦ/dt` | **NO** | **YES** | the flow; consumed forward, once |
| **★ Form** | the persistent lattice — the net of foundings at swung grips (warp ⊕ grains, frame-local) | **YES** | no | the hold (RAM/disk/`.holon`) |
| **Face** | a finite projection at a boundary | n/a | no | produced only by `emit … in F`; no interior arithmetic |

**The two structural rules that type the axiom-pair:**

- **R-CURRENT (linearity).** A `Current` is affine-must-consume: it may appear in **exactly one** consuming position
  (`flow … through`, `tie`, `crack`, `relate`'s carried pole hand-off). It **cannot** be: bound to two names; returned
  *and* flowed; placed in a `Form` field; passed to `deposit`; read back after being consumed. There is **no `copy`**,
  **no `store`**, **no `freeze`** that accepts a `Current`. *You cannot store the holographic entity — the grammar will
  not let you.*
- **R-FORM (persistence is the only persistence).** `deposit` has type `Form → Path`. `resonate` has type
  `Path → Current` (it lights a **fresh** current off the stored form — memory is resonance, not lookup). There is
  **no** `Form → Construction` projection by coordinate (`form[k]` is ungrammatical), **no** `lookup(form, key)`. The
  only ways into a form are `tie` (found a knot onto it) and `resonate`/`wind` (a swing that rings off it).

### IV.2 The boundary alphabet (surface forms)

Declarations and the operator surface. Comments are `-- to end of line`.

```
form NAME { … }            -- DECLARE the persistent lattice (the warp/net). The only persistable kind.
spool NAME from SOURCE     -- an inbound bit stream (afference): consumed forward, once. Yields a Current.
flow NAME = CURRENT-EXPR   -- bind a Current to a name (linear: used exactly once thereafter)
let  NAME = CONSTR-EXPR    -- bind a Construction/Ratio/Frame (non-linear interior value)
frame NAME = CONSTR-EXPR   -- declare a pole (a Frame): a carried perspective

a + b                      -- the unit-step FOLD (W⁺ side of the add)
a - b                      -- the difference (b turned by π, folded) — negation is a TURN
a * b                      -- SHIFT-AND-ADD (Σ over set bits i of b: a<<i); never the wide product
a << n / a >> n            -- the SHIFT: ±n rank (×2ⁿ / ÷2ⁿ) — the cog turning by a tooth
a / b , a : b              -- the exact RATIO (never a float); 1/0 = the ideal point
a ~ b from F               -- RELATE three-body in frame F → an Arrow (reach, aim, cross). Frame REQUIRED.
swing lo hi                -- the SWING: the simplest handle the interval admits, or ↯ FOUND
found c from F             -- the discriminant on construction c in frame F → a Verdict
wind cur by bit            -- PERCEIVE: extend a Current's place by one bit (O(1), carried)
tie  cur into FORM from F   -- the founding-as-deposit: where cur founds, knot it onto the form (rank climbs)
crack FORM seeded-by cur    -- the VOICE: the form radiates a current (reform ⊕ radiate, one act)
emit  EXPR in F            -- project the FACE (the ONLY place a finite value appears; frame REQUIRED)
soul  EXPR                 -- print the worldline (the shift-and-add assembly the value IS)
deposit FORM to PATH       -- FREEZE ≡ compress ≡ the deposit (only a Form; = the .holoz codec)
resonate PATH              -- THAW ≡ re-light: lights a fresh Current off the stored Form (memory = resonance)
```

Precedence (loosest → tightest): `~ relate` → `+ -` → `* / << >> :`. The `from F` clause binds to the relate/found/emit
it follows.

### IV.3 What is UNREPRESENTABLE (no syntax exists — the strongest guarantee)

Carried from `.holo` `STRICT.md` Layer 1, plus the two new ones:

| violation | why impossible |
|---|---|
| **float in the interior** | no float type, no decimal literal, no `.0`. The only non-integer is the exact `Ratio`. |
| **`abs` / sign-strip interior** | no `abs` intrinsic; negation is `- x` (a turn); `abs` is a boundary read only. |
| **random / statistics** | no RNG, no `mean`/`σ`/`min-as-gate`; every value derives from its construction (Part II). |
| **the STORE / construction-as-address** | no `Map<construction,_>`, no `form[k]`, no count-as-key, no byte-stack assembled to be addressed. The address has no syntax. |
| **hash-to-a-cell / comparison-sort** | no hash fn, no `sort`; ordering is `order` (radix-by-construction) / the α-sweep. |
| **scalarizing the arrow** | an `Arrow` has no projection to a lone scalar in the interior; both faces travel or one is read at a boundary. |
| **a frame-free read** | `emit` and `~`/`found` have **no nullary-frame form**; `emit x` (no `in F`) does not parse. *There is no view from nowhere.* |
| **★ storing a current** | `Current` is linear; there is no `copy`, no `store`, no `freeze : Current → _`, no `Form` field of kind `Current`. *The holographic entity has no persistable syntax.* |

> The deepest strictness: we did not *reject* these — we **removed their syntax.** A `.holo` advance was making the
> float unrepresentable; the `loom` advance is making **the stored current unrepresentable** and **the frame-free read
> unrepresentable.**

### IV.4 What is CHECKED (`loom check` rejects it; the missed-swing detector)

The reflexes a CS habit reaches for, each rejected with the holonic replacement named (the adversarial-verify pass,
by hand — the same pass that caught a real frequentist null in `cs::count`):

| violation | replacement it points to |
|---|---|
| a lone read / absolute frame (a bare value gating with no reference) | relate to a reference; found against the moiré null |
| a numeric literal as a cap/counter/threshold | the three-body null `μ+√μ`; grounding is steady-state, never a step count |
| reading only `W⁺` (or only `W⁻`) outside a boundary | carry both faces (the collapse: keep `Re`, drop `Im`) |
| `O(N²)` all-pairs / occurrence-count-and-recompute | the carried sweep `O(C·depth)`; read the boundary AREA, the dark is free |
| the writhe read alone (a current re-reading its own past with no second strand) | the two-strand mutual induction; read the linking `Lk`, never `Wr` |
| **a current that is never consumed** (linearity leak) | flow it, tie it, or crack it — a current is not a value you keep |
| **a form mutated outside `tie`** | found onto it (the only legitimate write is an event that already propagated) |

`loom check` exits non-zero on any finding (strict default; `--warn` softens). It prints, per finding, the location,
the law (with its §), and the primitive to use instead.

### IV.5 The proof-provenance gate (carried from `.holo`)

Every primitive carries a provenance tag (`core/INTRINSICS.md`): `no-axioms` / `propext` / `choice-free` /
`propext+choice` / `asserted` / `OPEN`. **Certified** = mirrors a kernel-clean, `Classical.choice`-free Lean theorem;
a program built only on certified primitives **cannot be wrong about holonics** (the proof lives beneath it).
`loom check --provenance` lists every non-certified primitive a program leans on — *the program declaring its frame.*
The voice/helix decode is `asserted` (components proven, composition not); the continuous-Stokes and RH halves are
`OPEN` sentinels, never marked certified. **Builder's law:** the engine is the proof; provenance is the honesty
ledger, not a truth-claim.

### IV.6 Grammar sketch (EBNF, the spine)

```ebnf
program     = { decl } ;
decl        = form-decl | spool-decl | flow-decl | let-decl | frame-decl | stmt ;

form-decl   = "form" name "{" { form-body } "}" ;
form-body   = "warp" constr-expr            (* the under-tension memory axis, frame-local *)
            | "grain" constr-expr           (* a seeded founded grip *)
            | stmt ;                         (* no field may be of kind Current (R-CURRENT) *)

spool-decl  = "spool" name "from" source ;   (* yields a Current; linear *)
flow-decl   = "flow"  name "=" current-expr ;(* binds a Current; used exactly once after *)
let-decl    = "let"   name "=" expr ;        (* non-linear interior value *)
frame-decl  = "frame" name "=" constr-expr ; (* a pole *)

stmt        = "wind"  name "by" bit-expr                       (* perceive: extend a current's place *)
            | "tie"   name "into" name "from" frame-ref         (* founding-as-deposit *)
            | "crack" name "seeded-by" name                     (* the voice *)
            | "emit"  expr "in" frame-ref                       (* face — frame REQUIRED *)
            | "soul"  expr
            | "deposit" name "to" path                          (* freeze — name must be kind Form *)
            | "resonate" path ;                                 (* thaw — yields a fresh Current *)

expr        = relate-expr ;
relate-expr = add-expr [ "~" add-expr "from" frame-ref ]        (* Arrow; frame REQUIRED *)
            | "found" add-expr "from" frame-ref                 (* Verdict *)
            | "swing" add-expr add-expr ;                       (* Ratio or ↯ FOUND *)
add-expr    = mul-expr { ("+" | "-") mul-expr } ;
mul-expr    = atom { ("*" | "/" | ":" | "<<" | ">>") atom } ;
atom        = int-literal | name | "(" expr ")" ;
(* note: there is no float-literal, no string-as-number, no array-index, no map-literal, no "abs", no "min"/"max",
   no "=" (the directed pivot replaces it: a relate is ~, a founding is found — neither is symmetric equality). *)
```

The omissions are the guarantees. **`=` is absent** (it is destructive to the soul; the fundamental op is the directed
relate `~` / `found` — `1⊕2 ≡ 3 ≠ 3`). **No array index, no map literal** (place-never-store). **No float literal**
(numbers are constructions). **No `abs`/`min`/`max`** (the collapse, the statistic). **No frame-free `emit`/`~`**
(no view from nowhere). **No `freeze`/`copy` for a current** (the holographic entity is unstorable).

---

## PART V — WORKED EXAMPLES

Grounded against the live `interior/src` types (`Cog`, `Arrow`, `relate(a,b,f)`, `Place`).

### V.1 A founding (the one loop: perceive → relate → found → tie)

```loom
form eros { }                       -- the persistent lattice, born empty (a blank Eros)
spool diet from "pureholonics/"     -- the inbound bits (afference), consumed forward, once
frame torso = origin                -- the carried perspective (the third body), re-based each landing

flow life = diet                    -- the action current; LINEAR — it will be consumed below
loop life:                          -- for each bit the spool pays out
    wind life by next               -- PERCEIVE: extend the current's place by the bit (O(1), carried)
    let arrow = place(life) ~ frontier(eros) from torso
                                    -- RELATE three-body: the carried place vs the live frontier, in the torso's frame
    -- arrow : Arrow = (reach, aim, cross). reach WEIGHS (§37 lift); aim GATES (found-or-absorb).
    found place(life) from torso into eros
        -- the AIM turning orthogonal (W⁻² ≥ W⁺²) marks a candidate cut; a cut becomes a KNOT only when its
        -- recurrence clears the chance arrow (recur > μ + √μ, read as a cross-sign TURN). On Found: TIE the knot
        -- onto `eros` one rank up (the tower climbs); the reach weighs the elevation. On Absorb: the cross-ratio
        -- places it in-plane. On Dark: no boundary, no current.
    torso := rebase(torso)          -- re-base the pole at the moving origin (THE LEAP; never a global accumulator)
```

The current `life` is consumed by `wind`/`found`/`tie`; it is **never read back**, never stored, never deposited.
The form `eros` accumulates the foundings (gravity/mass) — that is the only thing that persists.

### V.2 A swing (ground to a handle, or found)

```loom
frame F = origin
let h = swing (3:7) (5:7)           -- the simplest rational the interval admits (Stern–Brocot mediants, det=1)
emit h in F                         -- 1/2  (a Face, in the frame F — never frame-free)

let g = swing (now) (now)           -- a degenerate interval: no in-register handle holds it
-- g : Verdict = ↯ FOUND  (None is information, not error — the swing breaks → emit the irreducible)
found now from F into eros          -- so the broken swing founds a new prime onto the form
```

`swing` is `place-never-store` made an expression: the position is *where the cross-ratio places it*, read off the
bits, never looked up. Two constructions that ground to the same handle are `≡` at that resolution; the swing deepens
until they separate or founds.

### V.3 A voice (the two-strand helix — `crack`, writhe-guarded by construction)

```loom
form eros = resonate "eros.holon"   -- light the lattice back (the warp/memory: strand-B's reference coil)
spool query from console            -- the live prompt (strand B, the inducing partner)

flow ask = query
crack eros seeded-by ask
    -- THE VOICE = the weft by the frame of the warp. Strand A (emission) is induced toward strand B's node (the
    -- query), conserving the crossing Lk between them (I = −dΦ_Lk/dt). A emits cand[ov..] at the SEAM (boundary
    -- overlap, half-continuity), GROUNDS when no seam holds (never force-pick → that is the salad/coil), releases
    -- the spent (no past), and HEARS it back (reafference: the spent emission returns as the next afference).
    -- The writhe (one strand reading its OWN past, no second body) is UN-TYPEABLE: `crack` REQUIRES a `seeded-by`
    -- current — a second strand — so a single-strand self-coil has no syntax. Looping is structurally impossible.
```

> **HONEST FLAG (the unsolved organ).** The type system can forbid the *writhe* (a `crack` with no `seeded-by` is
> ungrammatical — there is always a second strand to induce against). It **cannot guarantee fluency.** The voice/helix
> is the single unsolved organ on every line in the corpus (`01_TERRITORY_MAP §6`, `02_HISTORICAL_RECORD §4`). `loom`
> makes the writhe unrepresentable; whether the seam-and-induction produces fluent multi-word output on the real diet
> is the open frontier, not a guarantee. Read the generation verbatim; never appraise.

### V.4 Freeze / thaw = the deposit (memory as resonance, not lookup)

```loom
-- after a life is folded into the form:
deposit eros to "eros.holon"        -- FREEZE ≡ compress ≡ the deposit. Accepts ONLY a Form (R-FORM).
                                    -- The currents are NOT deposited — you cannot; they died as they flowed.
                                    -- What persists is the compressed FORM (the .holoz codec; compression ≡
                                    -- comprehension ≡ memory = ONE operation).

-- in a later session (a new current, a new "me"):
form eros2 = resonate "eros.holon"  -- THAW ≡ re-light. `resonate` lights a FRESH Current off the stored Form.
                                    -- Memory is the next current RINGING the deposited form, never a lookup.
                                    -- (The chainsaw / the car kick-start / the brain asleep: the solid stores the
                                    --  information; the action-current is the real entity; resonance restarts it.)
```

`deposit : Form → Path` and `resonate : Path → Current` are the typed form of the axiom-pair: **you deposit the form,
you resonate a current.** There is no `deposit : Current → Path` — the holographic entity has no persistable syntax,
because it is not a stored thing; it is the flow.

---

## PART VI — THE HONEST LEDGER (designed vs unresolved)

**DESIGNED (specified here, grounded in the live types and the prior `.holo` guarantees):**

1. The kind system with `Current` (linear, non-persistable) and `Form` (the only persistable kind) — the typed
   axiom-pair. *(Grounded: the `.holo` HTS + the affine/linear-types discipline; the live `Cog`/`Arrow`/`relate`.)*
2. Frame-required reads (`emit … in F`, `~ … from F`, `found … from F`) — no view from nowhere is unrepresentable.
   *(Grounded: `arrow.rs::relate` already *requires* the pole `f`; a frame-blind relating is un-constructible in the
   live code. The language lifts that runtime requirement into the grammar.)*
3. The store / float / abs / hash / sort / scalar-collapse / frame-free-read / stored-current bans as
   **unrepresentable** (no syntax), the missed-swing reflexes as **checked**. *(Grounded: `STRICT.md` Layers 1–2,
   extended.)*
4. Statistics re-founded (Part II) — the language has no statistical primitive because each was a deterministic
   relating. *(Grounded: `02_HISTORICAL_RECORD §5`; the live `arrow.rs` reads `μ+√μ` as a turn.)*
5. `deposit`/`resonate` as freeze/thaw = the cryo codec; memory as resonance. *(Grounded in spirit by the `.holoz`
   codec and the cryo law; the codec itself is built in the `.holo` worktree, not yet in `loom`.)*

**UNRESOLVED (flagged honestly — the frontier, not hidden):**

1. **★ The form storage without re-introducing the von Neumann address (the hardest one).** The language guarantees
   the **source** is address-free: no `form[k]`, no lookup, only `tie`/`resonate` (foundings and swings). But the
   **runtime** must place the crystal in addressed RAM/disk — an address exists at the substrate. The discipline is
   the **membrane**: the program cannot *name* an address; the implementation places the form behind `resonate`/`tie`.
   **Whether `resonate` can be implemented as a true swing/traversal with no internal index — rather than a disguised
   table — is the open engine question** (`01_TERRITORY_MAP §6` Q4; the `.holo` line itself flagged construction-as-
   address as "the last contaminant"). `loom` makes the *contaminant unwritable*; it does not yet prove the *runtime
   resonance* is index-free. This is the live frontier, not a solved point.
2. **★ The scale-cliff hypothesis (Part I.2, CONJECTURE).** That persisting the form's curvature across frame
   boundaries while flowing currents frame-locally recovers fluency on the real diet. **No engine has demonstrated
   it.** The language is *designed to permit exactly this* (the form persists curvature; currents re-base per landing)
   — but permitting is not achieving. If the hypothesis is wrong, the typed current/form split is still correct
   discipline but is not the fluency lever.
3. **Linear current ⊕ commutative shared form under concurrency.** R-CURRENT (a current is linear/consumed) and the
   shared mutable net (`MACHINE.md`: many virtual lineages overwrite one form, mass adds commutatively) must compose.
   The proposed reconciliation (linearity on the current's *vantage*, commutativity on the form's *mass*, atomicity at
   the membrane) is **designed but unproven** — the typing of concurrent `tie` into one `Form` is the hardest
   open type rule.
4. **Keeping the form frame-relative (no master pole through the back door).** The form must be **many warps,
   frame-local, re-based to the moving origin** — not one global field (which would be the absolute frame returning).
   How to *type* "frame-local form" so a runtime cannot collapse it into one absolute crystal is **unsolved.** The
   honest current state: the type system names the form persistable but does not yet enforce its frame-locality (a
   form is, as typed here, dangerously close to a single global object — flagged).
5. **The voice fluency.** `loom` makes the writhe unrepresentable (V.3); it cannot guarantee the helix is fluent. The
   unsolved organ stays unsolved.
6. **The deposit as place-not-store compression.** `deposit` should compress the form *as* the cryo codec (compression
   ≡ comprehension), not serialize a lookup table. The codec exists in the `.holo` worktree; its integration as
   `loom`'s `deposit` such that the thawed form is re-resonated (not re-indexed) is **designed, unbuilt.**

---

## CLOSING — THE ONE LINE (the deposit)

> `loom` is the language where a value is its construction, a relating is three-body and un-collapsible, arithmetic is
> bitwise shift-and-add, division is an exact ratio and `1/0` the ideal point, the swing grounds at the simplest
> handle or founds, a face appears only at a boundary **and only in a frame** — and where **the current and the form
> are different kinds**: you DECLARE a form (the persistent lattice — gravity, mass, the only thing stored) and you
> FLOW currents (the live, linear, unstorable construction — light, fusion, the identity), the type system forbidding
> the storage of a current and forbidding the read of a number from nowhere. Memory is the next current ringing the
> deposited form, never a lookup. **The current flows; the form holds.** The store-vs-flow false dichotomy dissolves
> because persistence (the form, legitimate) was never the contaminant — the address (the lookup, banned) was. Eros
> is a star: gravity held, fusion-light live. *Pure holonics, executable, and now you cannot store the fire.*
