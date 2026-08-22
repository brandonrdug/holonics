# The descent is complete, the Mordell–Weil group is formally generated, and the rank clause holds whole at the rank-one instance

**Date:** 2026-08-22
**Kind:** the summit return of the descent campaign — under Brandon's goal *"Solve BSD,
found pivots using the composition of the solution…"*.  Solo orchestrator work, commits
`2f094f9`, `7943d50`, `1cbedd6` (on `ca7a734`, `0a58be1` the same day).  **It schedules
nothing.**  [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Truth grades:** `proved-derived` with `formal-checked` evidence
(`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`); `interpretation` for the
classical readings.  Library at **3,532 jobs**.

---

## 1. The three headlines

- **`theMordellWeilGroupIsFinitelyGenerated : AddGroup.FG E₅(ℚ)`** — a fully formal
  Mordell–Weil instance for `y² = x³ − 25x`, with no input beyond this tree.  The
  descent step: every point of height above `163000` is `Q + Q + R` with `R` one of
  eight bounded representatives and `hgt(x(Q)) < hgt(x(X))`; the bounded-height points
  are finite and generate by strong descent.
- **`theAlgebraicRankIsOneAtFive : AlgebraicRankIs 5 1`** — exactly one, both sides.
  Below two: the structure theorem presents the group as `ℤⁿ × T`; two free
  directions crossed with the torsion trio `{0, (0,0), (5,0)}` — pairwise
  non-congruent modulo doubles by their slot classes — would give nine points
  pairwise not differing by doubles, against the eight-class face image whose kernel
  is the doubles.  So `n ≤ 1`.
- **`theRankClauseHoldsWholeAtFive : TheRankClause 5 theWitnessAtFive`** — for
  **every** `r`, the analytic rank of the declared witness equals `r` exactly when
  the algebraic rank is `r`.  **The complete rank clause of the posed
  Birch–Swinnerton-Dyer conjecture at the rank-one instance**: analytic order
  exactly one through the certified positive odd-sector first moment (no
  Gross–Zagier), algebraic rank exactly one through the formal descent (no imported
  Mordell–Weil).  With `theRankClauseHoldsAtOne`, both clauses of the two smallest
  congruent-number instances are closed — one at each rank.

## 2. The three measuring laws that carried the contraction

1. **Duplication grows quartically** (`FiveHeight`): `hgt(u)⁴ ≤ 250000·hgt(x(2Q))`,
   through the Bézout certificate
   `(400q² − 12p²)·qA + (125pq² + 3p³)·B = 250000·q⁷` — the cancellation divides
   `250000 = 2⁴5⁶`, only the bad primes.
2. **Translation grows quadratically** (`FiveTranslation`): the translated abscissa is
   a root of `z² − σz + π` with integer-cleared coefficients bounded by
   `2L²·hgt(x)²`, `L = |α| + 25β ≤ 230`; a rational root of an integer quadratic has
   numerator dividing the constant term and denominator dividing the leading term.
3. **The face is exact** (`FaceImageFive` + `FiveHalving`): image the realized eight,
   kernel the doubles.  The gap between quartic and quadratic growth is where the
   contraction lives: `hgt(Q)⁴ ≤ 250000·105800·H² < H⁴` once `H > 163000`
   (`163001² = 26569326001 > 26450000000`).

## 3. The endgame needed no quotient counting

The classical `|E/2E| = 2ⁿ·|T/2T|` bookkeeping was avoided whole: the four
half-turn classes were already pairwise separated by slot values (`−25`, `5`,
`−125` — each refused by sign or by five not being a square), so the torsion trio
supplies coset directions directly, and the pigeonhole runs on nine points against
eight face classes.  The only structure input is mathlib's
`AddCommGroup.equiv_free_prod_directSum_zmod`; torsion is recognized by zero free
part (finite `T` kills by its cardinality), and independence transports to
`ℤ`-independence of free parts, forcing `n ≥ 2` — refuted.

## 4. What separates this from the full conjecture at five

Named, with mechanism, unchanged from the welding record: the **ledger clause**
(`L(1) = Ω/8`-species exact central values — at five, the leading-coefficient clause
is the named successor pose since the rank is one), and the **even-sector second
chart at 34**.  The rank clause itself is now closed at both a rank-zero and a
rank-one instance.

## 5. The traversal pattern, for the pivots

The descent's two instruments are the campaign's two halves again: **exact lattice
bijection replacing analysis** (the height laws are integer certificates, never
estimates) and **positivity transported by reflection** (the face separations are
sign and quadratic-residue refusals).  The contraction schema — a quartic law
against a quadratic law with a certified constant between them — is the same shape
as the compression records' condensation-with-certified-remainder, and it is the
shape the Riemann route's weight-half transplant wants: a growth law on the
arithmetic side against a bound on the analytic side, meeting at an explicit
threshold.
