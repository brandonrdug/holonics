# THE MENO MACHINE — THE FORMULA (`RESEARCH/meno.rs`)

> **What this document is.** `THE_FORMULA.md` states the whole Universality Machine (the region, the web,
> the perspective, the membrane, the ecosystem — the communicative life). **This document states the MENO
> MACHINE** — the mathematics/physics arm, the clean rebuild in `RESEARCH/meno.rs`: bit-pure, no language,
> no bloat. It is the machine's ONE MOVE made literal — **reach EXACT, then NEST** — wrapped as **Λ, the
> frame-relative solve (`24`)**, run over Indra's Net in the re-based number. Read `THE_FORMULA` for the
> life; read this for the solve. Where this and a ratified stratum disagree, the stratum wins and this is
> corrected — the formula gets MORE intuitive as it consolidates. Trust timestamp; builder's law: the
> engine is the proof.
>
> **★ THE CLICK.** The Meno machine is **Λ striking across Indra's Net, in the re-based number.** A
> question is an aperture; the net is the mass of what has been solved; the illicium reaches the minimal
> EXACT recurrence and, where the raw frame does not hold it, NESTS to a frame that does — or the
> irreducible remainder founds a new axis; and the whole thing composes
> with itself forever — `EROS ≔ Λ^∞`. Every read is PLACE-NOT-SEARCH; the only "hardness" is STARVATION
> (`46 §4`).

---

## THE NUMBER — magnitude ⊕ rank ⊕ turn, carried re-based (`02`, `13`)

Every value is `Num { m, e }` = **`m · 2^e`** — a magnitude `m` (with the sign a **turn**, never an absolute
zero) at a **rank** `e` — and the rank is **itself a `Num`** (recursive: the exponent is a rank is a number;
the NUMBER NESTS, no exponent ceiling). It is NEVER an absolute magnitude:

- **RE-BASE, never widen (`02`).** When `|m|` passes the grain (`GRAIN` bits), the **low bit falls** and the
  rank climbs — *the resolution IS the compression.* `norm(m, e)` enforces it.
- **A register overflow is a RANK-CLIMB, not a discard (`13`).** So `2^r` is `pow2(r) = (1, r)` — the tower
  is stored, never materialized; **rank-UP is setting the rank field, free.** The double-exponential climbs
  `2^16 → 2^32 → 2^64 → … → 2^2048 → …` and never once overflows the register (measured).
- **A logarithm is a rank (`02`).** `rank_of((m,e)) = e + msb(m)` — a re-based number reads its own log for
  free (the rank field). Ranking DOWN the tower is this read; ranking UP is `2^`.
- **The only order-read is the borrow (`below`).** `cmp` lifts it to the re-based number (the sign, then the
  rank, then the aligned mantissas — recursing down the tower). No `<`, no float, no `%` in the number; the
  digit (`digit`) is the only division.

## THE SUBSTRATE — the number as its combinatorial faces (`02`, `13`)

- **`shape(n)`** — the `2ᵏ` corners a number stands on (its whole combinatorial identity).
- **`convolve(p,q)`** — × read combinatorially: the raw mode-count `Σ pᵢqⱼ` at each rank `i+j`, before carries.
- **`fold(conv)`** — the carry-ripple that turns the convolution back into the number (`× = convolve∘fold`);
  rank by rank the WELL stands (the bit) and the WINDING fires up (the carry) — the digit law (`13`).
- **`digit(action, q)`** — action MOD the quantum: the remainder STANDS (`< q`), the quotient FIRES as the
  soul. Bit-pure long division. **`below`** — the adder's borrow, the one order-read.

Factoring is DECONVOLUTION; a prime is the shape irreducible under convolution (`46`/`08 §6`) — the STARVED
terrain (see WHAT IS OPEN).

## Λ — THE SOLVE (`24`): `Λ_F(Q ⊗ A ⊗ L) → (P, π_Β)`

The subscript is load-bearing: **`Λ` abstracts the FRAME `F`** (`λ` would fix the frame and abstract a
value). The frame is the `2ᵏ` tree ⊕ the rank the arc lands on; the voyage chooses it. The six factors, each
a construction the machine computes:

| factor | what it is | the construction | stratum |
|---|---|---|---|
| **F** frame | the lattice ⊕ the rank | the `2ᵏ` tree ⊕ the tower floor the arc grounds on | `05`, `24` |
| **Q** the aperture | a wound face | the chain's window, the next term open | `25`, `47` mode 8 |
| **A** Indra's Net | the mass, holographic | the standing jewels, each reflecting one soul `χ` (the cross-ratio) | `46`, `26`, `49 §3` |
| **L** the voltage | charge ⊕ reach | the arrow (`48`, which way) ⊕ the reach of exactness (the register — its end triggers the NEST, never a tolerance) | `35`, `49 §5`, Ledger A |
| **P** the placement | a jewel or a founding | the illicium places the exact recurrence, or the irreducible remainder FOUNDS a new axis | `05`, `23`, `55` |
| **π_Β** the Meno read | the pair `(C, d)` | `C` the finding cost (order ⊕ nest depth; the geodesic length), `d` the check — never divided to a scalar | `23`, `51`, `MENO_FORMULA §III` |

## A — INDRA'S NET (the mass, holographic — `46`, `26`, `49 §3`)

The net is NOT a line walked by a sliding window (that is the serial costume) and NOT a terrain fed to the
machine (that is the dead half — `THE_FORMULA`: "a machine without perspectives is terrain"). It is a **net
where every jewel reflects every other**, co-present (`31`), and what every reflection conserves is the
**cross-ratio `χ`** — *the* invariant, because it is the projective invariant of the inversion (`49 §3`: the
deep law is the cross-ratio, never the additive sum) and it is scale-free (`V.13`, the dispersal by
proportion — the same ratios at every scale). A coherent net holds ONE soul across every face. The mass is
never fed in — it is what `Λ` **deposits and re-feeds** (TRANSFER, below); the "terrain" is only the shadow
`Λ` casts by running. **The `χ`-conserving Indra's-Net deposit engine lives in `RESEARCH/collocation.rs`**
(souls addressed by their held cross-ratio, place-not-search); in `meno.rs` the net is the chain `eros`
grows by TRANSFER.

## L — THE VOLTAGE (the lifecycle; `35`, `49 §5`; the grain per Ledger A) — never a cap, never a tolerance

`L` is the push the aperture supplies, and it has **two parts** (the mirror is BOTH an undirected drive AND
an unframed question — `49 §5`):

- **the CHARGE (`48`)** — the signed arrow: which way to climb (found FORWARD up the dilating `C`-direction,
  never retrace the diagonal). In the chain it is the signed drive: the winding's cross-sign (the turn)
  chases the climb where a rank fired — founding forward IS reading the boundary.
- **the GRAIN (Ledger A; `MENO_FORMULA §III`)** — **NOT a tolerance** (the "Duggan tolerance" is RETIRED).
  Conservation is **EXACT** — the recurrence is verified on every point, then extrapolated (`direct`). The
  grain is only the **reach of exactness** (`k·rank < GRAIN`, the register's own resolution); where the raw
  frame does not hold the invariant, the ONE MOVE **NESTS — re-base ⇔ nest**: reduce to the **ranks** (the
  log — exponential/tower) or the **differences** (`Δ` — the higher polynomial) and recurse; **the nest
  RESTORES exactness in the reduced frame, no loss.** `π_Β = C/d` is the NEST DEPTH read as the DILATION,
  **held as the pair `(C, d)`, never a scalar dial**.

**The stop is NEVER a cap** (the old `floor < 6` is dead — `49 §5`). The illicium runs until the direct
recurrence verifies exact, or the nest bottoms in a frame with nothing left to reduce (the voltage spent, an
equilibrium — the fold). The nest frame is **where agreement is restored, not a dial we set** — a detour is
a structure the raw frame could not hold, and the reduced frame holds it exactly (measured: squares/cubes by
Δ-nest, double-exp/tower by rank-nest — exact in the reduced frame, never tolerated in the raw).

## THE ILLICIUM — the one move (`22`, `55`): reach EXACT, then NEST

`illicium(xs)` is the strike — reach as far as the grain holds exact, then nest:

1. **THE REACH** — the **minimal linear recurrence** at order `k`, by **exact Cramer determinants** over the
   re-based number, tried while the grain holds the determinant exact (`k·rank < GRAIN`). **Verified on
   every point, then extrapolated** (`direct`) — the recurrence, not its roots, carries the placement
   (Fibonacci's irrational modes never materialize). Catches ratio ⊕ difference ⊕ MIXED (`n·2ⁿ`) ⊕ any
   linear recurrence.
2. **THE NEST** — when the reach runs out (the determinant would go lossy, or no finite recurrence exists):
   reduce to the **ranks** (the log — exponential/tower) or the **differences** (`Δ` — the higher
   polynomial) and **recurse**. Re-base ⇔ nest — the same act as the number's own re-base, at every scale;
   exactness restored in the reduced frame.
3. **THE EIGENSTRUCTURE (`55`)** — the recurrence's characteristic polynomial factored into integer roots
   with multiplicity → the MODES (`p(n)·rⁿ`); an **irreducible remainder is a FOUNDING** — a prime of the
   mode-space (Fibonacci's `φ`, a rotation's `±i`).

The same determinant reaches on: **SYSTEMS** (`A·x = b` by Cramer); the **NONLINEAR** (`x_{n+1} = P(x_n)` —
nonlinear in `x`, LINEAR in the coefficients: a Vandermonde solve); the **CONTINUOUS** (a linear ODE is the
recurrence's twin — the same characteristic polynomial, modes `e^(λx)`, the irreducible pair the OSCILLATORY
founding); the **FACTORIAL/COMBINATORIAL** (Legendre: `exp_p(n!)` placed from the digit-sum shape, no
product; Kummer: the binomial's prime powers ARE the carries); the **GEODESIC/PALINDROME** (`24`): the
shortest add ⊕ shift ⊕ `2^` program `A → B` — the wormhole shift across the rank gap, then the correction
whose difference is a base-2 SHAPE; palindromic — forward FINDS, backward CHECKS (`48`/`38`).

`C` is the finding cost (the recurrence order, or nest depth ⊕ reduced order; the geodesic length); `d` is
the check (the diagonal). **`π_Β` is held as the pair `(C, d)`, never divided** (`MENO_FORMULA §III`).
`C/d = 1` REFLECTS in ONE frame (mirror, or mastery if mass stands behind it, `51 §5`); the detour FOUNDS.

## EROS ≔ Λ^∞ (`24`) — the solve unbroken

`eros` iterates `Λ`: place a jewel, **feed it back into the net (TRANSFER — `P` becomes `A`, `24`)**, and the
net thickens. The mass appears because `Λ` deposits its own placements (every passage deposits, Theorem 1) —
never a store fed in. As the net grows and holds one soul, `π_Β` tightens (**the hexis**, `23`: `C` collapsing
onto `d`). A founding declares a new axis (found forward, the charge, `48`).
Measured: arithmetic/geometric/mixed/Fibonacci solve DIRECT (the recurrence exact — mastery, local P=NP);
squares and cubes by Δ-nest; the double-exponential and the tower by rank-nest, climbing the rank by re-base
forever (`2^(2^…)`, no overflow).

## THE BANS (the machine's; the full list in `THE_FORMULA`)

No floats (the number IS `(m,e)`; the low bits fall — never a leaking tail, a founding denied) · no `/`, no
`%` (the digit) · no compare but the borrow (`below`/`cmp`) · **no cap** where an equilibrium belongs (`L` is
the voltage/reach, never `floor < N`) · **no store** (the net IS the mass, path-preserved — never a
side-table) · **no scan** (place-not-search; a scan is starvation, the machine's opposite) · no absolute
magnitude (re-base, never widen) · no fabricated statistic (no filter+threshold+tally crowned as a scalar).

## THE UNITS ⊕ THE GATES

| quantity | unit | law |
|---|---|---|
| the corner | one `Num` `(m,e)` | a fold of the perspective's face; magnitude ⊕ rank ⊕ turn |
| the soul `χ` | a ratio pair | the cross-ratio, conserved across the net (the deposit engine: `RESEARCH/collocation.rs`); never a float, never a collapsed scalar |
| the read `π_Β` | the pair `(C, d)` | `C` the finding cost (order ⊕ nest depth; the geodesic length); `d` the check; never divided |
| the grain | the register's reach | the reach of exactness (`k·rank < GRAIN`) — its end triggers the NEST, never a tolerance (Ledger A) |
| the rank `e` | itself a `Num` | the tower position, recursive (no ceiling); re-base climbs it — the tower does not re-base, the magnitude does |

**Gates:** `rustc -O RESEARCH/meno.rs && <bin>` runs clean, all demos ≪ 1 s; the workspace gates
`cargo test -p interior -p observer` stay green (meno.rs is standalone). Bit-purity is structural **in the
number**: no float, no `<` but the borrow, no absolute magnitude crosses un-re-based; the `Num` arithmetic
uses no `/`/`%` but the digit. **The licensed exception:** the Legendre/Kummer/roots section still uses raw
`/` and `%` and is OWED a re-basing onto the digit operator — an open debt (`FABLE_ORGANIZING`).

## WHAT STANDS ⊕ WHAT IS OPEN (honest, binding — do not overclaim)

**STANDS (built ⊕ measured):** the re-based number with the RECURSIVE rank (the exponent itself a `Num` —
the tower with no ceiling, no overflow); the ILLICIUM (the minimal exact recurrence by Cramer,
verify-then-extrapolate, then NEST — ranks or differences, recursed); the EIGENSTRUCTURE (characteristic
polynomial → integer modes; the irreducible remainder a FOUNDING); SYSTEMS by Cramer; the Vandermonde
nonlinear fit; the ODE twin; Legendre/Kummer factorial placement (the carry the combinatorial engine); the
geodesic/palindrome (`π_Β` the compression, a pair); `L` de-contaminated (the nest, the equilibrium — no
cap, no tolerance); TRANSFER (`Λ^∞`, the net thickening).

**OPEN (the named frontier):** the general multiplicative decomposition — **factoring a number's own faces**
— is the STARVED terrain (`46 §4`): where the tree offers a small branch it is place-not-search; where it is
withheld (the balanced semiprime) it starves. The `√` reads perfect-square reducibility, not the general
factorization. This is **not** claimed solved; the honest next is feeding the net a tree it can walk (the
mass, the caverns) so the balanced placement grounds — or measuring, honestly, that it does not. RH's `½`
likewise stays a finite measurement ⊕ our `2⁻¹` framing, never a proof.

---

> **One line:** *the Meno machine is `Λ`, the frame-relative solve, run as the ILLICIUM over the re-based
> number — a question opens the chain's next term, the minimal recurrence is verified EXACT on every point
> then extrapolated, where the raw frame does not hold the invariant the move NESTS (ranks or differences,
> recursed — exactness restored in the reduced frame, never tolerated in the raw), the eigenstructure names
> the modes and the irreducible remainder founds, the tower climbs by re-base so no magnitude ever runs
> absolute, and the whole composes with itself forever (`EROS ≔ Λ^∞`) — the net thickening, `π_Β` held as the
> pair `(C, d)`, place-not-search throughout, and the one hard frontier (factoring the balanced number)
> sitting honestly named as starvation rather than faked as solved.*
