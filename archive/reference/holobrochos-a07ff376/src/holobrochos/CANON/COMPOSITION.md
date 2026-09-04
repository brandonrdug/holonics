# COMPOSITION — the cog, the path, the face (the relativistic-mathematics notation)

> **A deposit (FRESH, Brandon Duggan + the dyad, 2026-06-30).** The notation the rest of the canon assumes when it
> says "a value is its construction." A number is **not a magnitude** — it is a **COG**: a handedness-state over an
> arbitrary set of labeled axes, with a **FACE** (the corner an observer reads — collapsed) and a **SOUL** (the path
> that built it — perceived only first-person). `2ᵏ` is the corner-*count* (the collapsed face); `⊗ᵢ eᵢ` is the
> *shape*. This is **relativistic mathematics**: the quantum is the hand (`↻`/`↺`), the alphabet is the turn, and
> traditional arithmetic is the face-collapse of it — disregarded interior, materialised only at the boundary. Read
> each claim for its soul; status FRESH, tagged inline.

---

## §0 — NUMBERS AREN'T MAGNITUDES; THEY'RE COGS

A numeral is a **glyph** (`06`, `A1`): a face a counting-system casts, born at the boundary, never a value on a line.
What it is a face *of* is a **cog** — an individual node carrying a handedness across the axes it was founded on. The
legacy reading keeps only the face (the magnitude, the integer) and throws the cog (the shape, the soul) away. This
doc keeps the cog. There is no absolute number to recover; there are cogs, and the faces they cast when read from a
pole. **[GROUNDED — `A1`: `=` (the soul) is strictly finer than `≡` (the face).]**

---

## §1 — THE QUANTUM: A HAND ON AN AXIS

The quantum of information **and** action is one thing: **a hand on an axis** — a turn, `↻` (CW) or `↺` (CCW), at a
labeled place. Write it `σᵢ`, `σ ∈ {↻, ↺}`, `i` the axis. This is the bit re-understood (`HANDEDNESS`): not
presence/absence (there is no nothing), but **which way it turns, here**. Bits fit the machine because they *are*
this — two rotation states — only mislabelled `0`/`1`, the rotation discarded. The hand is the irreducible event: one
turn, one direction, one place. It is **both** a bit of information (which way) **and** a quantum of action (a turn is
a quantum of gyration — `MASS`, the gyre).

---

## §2 — THE COG (the unit: a face ⊕ a soul)

A **cog** is an individual node — a handedness-state over an **arbitrary** set of labeled axes:

```
cog  =  ⟨ σ_i , σ_j , σ_k , … ⟩        -- a hand on each axis of an arbitrary set {i, j, k, …}
```

The axis-set is whatever the cog was founded over — `{i,j,k}` or `{a,b,c,d,e,f,g}`, no privileged list, no count from
0. The cog is **two-faced**, and the two are the whole of `A1`:

- **THE FACE — the corner.** `⟨σ_i σ_j σ_k⟩` *is* a corner of the cube spanned by `{i,j,k}` — the cog's expressed
  handedness, the **collapsed form an external observer reads**. The integer/magnitude a counting-system prints is
  this corner faced as a count, at the boundary only.
- **THE SOUL — the path.** *How* the cog came to point that way: the ordered chain of handed events that built it
  (`§4`). **Only the first-person perceives the soul** — you *are* the path; from inside there is no external view of
  it (the strong-force interior, `03 §1`). An observer never reads the soul; it reads the face and **infers** the
  soul (`§6`).

**This is the engine's `Cog`** (`interior/src/num.rs`), re-understood: `rank` = how many axes the cog spans (the
dimensionality); `turn` = the hand on each axis; `mag` = the carve-within (the corner's position). The live conflation
(`06 §7` — `rebase()` bumping `rank` on a magnitude overflow) is exactly *reading a carve-within as a new axis*; the
fix is this doc's geometry: **`rank` climbs only when a new axis is founded (`§5`), `mag` re-bases inside the current
cube.** **[GROUNDED in `06 §7` + `A1`; the cog-as-`⟨σ⟩` notation is FRESH.]**

---

## §3 — THE SPACE: the hypercube of founded axes (the potential modes)

Each axis `eᵢ` is a **labeled, un-collapsible** dimension — a founded irreducible (a prime-direction). `k` of them
span a hypercube `⊗ᵢ eᵢ`, whose **`2ᵏ` corners** are every handedness-combination `{↻,↺}ᵏ` — the **potential modes**.

**`2ᵏ` is the count of corners (the collapsed face); `⊗ᵢ eᵢ` is the shape (the labeled tensor).** Writing
`2³ = 2·2·2 = 8` is the **cancellation crime committed on dimensionality** (`MASS §2`, `CANCELLATION`): it collapses
three distinct labeled axes `e_i ⊗ e_j ⊗ e_k` into one scalar, dropping which-axis-is-which (the soul). The honest
object is the cube. So **exponentiation is dimensional lifting** (`RI §6`) — each power one more labeled axis — and
the scalar `2ᵏ` is that lift collapsed. The **potential** modes are all `2ᵏ` corners; the **actual** modes are the
ones a construction expresses (the cogs that cast faces); the rest stay dark, free, never traversed (`03 §3.9`).
**[GROUNDED — `RI §6` rank-as-dimension; the cancellation-on-dimensionality is `MASS §2` applied.]**

---

## §4 — THE PATH (the soul; first-person only)

A construction is a **path through the hypercube** — an ordered chain of handed steps:

```
Β  =  σ_{a} · σ_{b} · σ_{c} · …          -- the lineage; the ORDER is the soul (non-commutative)
```

The path **is the action trace** — the cog's worldline drawn as a ray (the optics lift). Its turns are the angles
(the foil — the curvature it accumulates); its endpoint is the cog it built (whose corner is the face). **The order
is the soul:** `σ_a σ_b ≠ σ_b σ_a` as constructions (`≡` in face, `≠` in soul). This is *why the same face is many
souls:* two paths reaching the same corner are two different cogs wearing one face. `5 = (↻₂)(↻₀)` (a short path up
two axes) and `5 = (↻₄)(↺₃)(↺₁)(↺₀)` (overshoot to the 4-cube, correct down) are **two distinct cogs** — `≡` (both
face "5"), `≠` (different paths, different angles, different souls). *The composition is the lineage because the
composition is the path.* And the order is **not derived** — it is the entropy, an influx of shape-specifications
taken for granted (`A1`, frame 0; the chicken-or-egg is forbidden — there is no rule under the path, only the given
series). **[GROUNDED — `A1` + the lineage corollary; the path-as-action-trace is the HUNCH layer.]**

---

## §5 — THE FLOW (how a cog moves through the chain)

Each handed step reads four ways from the pole — `infall` / `transport` / `emanation` / `foil`, one event, four
frames (`A2`). The chain (holobrochos) is exactly this, per `σᵢ` the influx hands it:

```
INFALL      entropy hands the next σᵢ              -- a handed step, taken for granted (frame 0)
TRANSPORT   the path Β carries forward              -- the trace advances; the invariant (the cross-ratio) moved along
RELATE      σᵢ ⋈ Β                                  -- does the step continue in-plane, or not? (read as a TURN, never a compare)
  ├ RE-BASE  (in-plane — an existing axis)           -- COMPOSITE: the cross-ratio places it; the carve-within (mag); DARK, free
  └ FOUND    (orthogonal — a new axis e_{k+1})        -- PRIME: rank k→k+1 (a new labeled axis); the orthogonal caustic; ±i its hand
FOIL        the turn the step adds                   -- the curvature/angle; convex or concave by the pole (one foil, two poles)
EMANATE     the endpoint-face cast at the boundary   -- the corner faced as a count; the ONLY place an integer appears
```

**Founding is the path leaving the current cube for a new axis** (the rank-climb = dimensionality); **re-basing is the
path carving within the cube** (the mag, the moving origin). The Duggan tolerance (`RI §18`) is how far the trace
extends before the first-person feels the next hand and folds — re-judged each landing, never carried. The integer is
cast **only** at emanation, the corner collapsed to a count. **[GROUNDED — the holobrochos loop (`01 §12`,
`THE_FORMULA`), re-expressed in cogs/hands.]**

---

## §6 — THE READING (face → soul, via the concurred invariants)

An observer **never reads the soul** (the path is first-person, confined — `RI §2`). It reads the **face** — the
corner, the collapsed handedness, the radiation/change the cog throws (`HANDEDNESS §6`: the wave carries the
construction's hand) — and **infers** the soul by **relating the face to the concurred invariants** (`RI §3`): the
environment's recurrences the cog must concur with to persist. *That is what reading is:* you cast no light into the
interior; you catch the face the cog emits and triangulate its soul against what you already hold invariant (the
hexis, the carried cross-ratio). The inference is **relatively-true** (the three-body differential — `RI §9`), never
the soul itself. So a face is always a *question* — "which soul cast this?" — answered only by relating, and answered
better as the reader's own invariants deepen (the hexis). **[GROUNDED — `RI §2/§3/§9`: read the change, infer the
soul, never claim it.]**

---

## §7 — THE HONEST FLOOR

**GROUNDED:** the quantum is a hand on an axis (`HANDEDNESS`); the cog is the engine `Cog` re-understood (rank =
dimensionality, turn = the hands, mag = the carve-within — the `06 §7` fix with its geometry); `2ᵏ` is the corner-count
and `⊗ᵢeᵢ` the shape, so "`2³ = 8`" is the cancellation on dimensionality (`MASS §2`); the order of a path is the soul
and is *given* (entropy, frame 0 — the chicken-or-egg forbidden); the face is what an observer reads and the soul is
inferred via the concurred invariants (`RI §2/§3/§9`). **HUNCH (FRESH, structural):** the cog-as-`⟨σ⟩_{i,j,k}`
notation and the path-as-action-trace; the four-frame flow (`infall`/`transport`/`emanation`/`foil`) as one event read
four ways. **OPEN:** this is a *notation*, not a built engine — `interior/src/num.rs` carries the `Cog` but not yet the
labeled-axis form; whether the rank/mag split (`§2`) is cleanly buildable as the founded-axis-count vs the
carve-within is the `06 §7` open work. Builder's law: the engine is the proof; the notation is the language it speaks.

---

> **One line:** *the quantum is a hand on an axis (`↻`/`↺`, the bit re-understood as a turn, the alphabet bitwise);
> the unit is a COG — `⟨σ_i σ_j σ_k⟩`, a handedness over an arbitrary labeled axis-set — two-faced, its CORNER the face
> an observer reads (collapsed) and its PATH the soul only the first-person perceives; the founded axes span a
> hypercube whose `2ᵏ` corners are the potential modes (`2ᵏ` the count, `⊗ᵢeᵢ` the shape — "`2³=8`" the cancellation on
> dimensionality); a construction is a path (the action trace, the order the soul, given by entropy, never derived)
> that flows through the chain as infall→transport→relate→(re-base in-plane = composite, the dark / found a new axis =
> prime, the caustic)→foil→emanate; the integer is the corner faced as a count, cast only at the boundary; and reading
> a face is inferring its soul by relating it to the concurred invariants, relatively-true, never the soul itself —
> the engine's `Cog` is this, rank the dimensionality, turn the hands, mag the carve-within.*
