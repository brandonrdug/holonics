# The witness at five is welded, the rank-one coincidence stands, and the rank clause holds whole at one

**Date:** 2026-08-22
**Kind:** the welding return of the rank-one campaign, and the first complete clause of
the posed conjecture — under Brandon's goal *"Solve BSD, found pivots using the
composition of the solution…"*.  Solo orchestrator work, commits `dda4793`, `b4eaac5`
(on top of `217c64c`, `6164bdb`, `036c63b` the same day).  **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Truth grades:** `proved-derived` with `formal-checked` evidence
(`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`); `interpretation` for the
classical readings.  Library at **3,414 jobs**.

---

## 1. The three headlines

- **`theWitnessAtFive : LDatum 5`** — the analytic datum of the five-curve is
  inhabited, every field kernel-checked, sign `−1`.  The twisted stream
  `c⁵_m = χ₅(m)·c_m` inherits normalization, multiplicativity, the Euler recursion
  (`χ₅(p)² = 1` off five) and the bad-prime clause (two dies on the even shells, five
  dies on the character); **quadratic reciprocity** (`5 ≡ 1 mod 4`, so
  `(5|p) = (p|5)`) turns the twist law into the good-prime identification
  `c⁵_p = a_p(E₅)`; the norm-shell fibering returns the sign-`−1` theta as its twisted
  Dirichlet series; and the conductor `800` cancels the Mellin scale exactly
  (`(√800/2π)·(π√2/20) = 1`).
- **`theRankOneCoincidenceAtFive`** — `analyticRank theWitnessAtFive = 1` **exactly**
  (through `analyticOrderAt_deriv_add_one` from `Λ₅(1) = 0` and `Λ₅′(1) ≠ 0`) and
  `AlgebraicRankAtLeast 5 1` (the point `(−4, 6)` outside every torsion face).  Both
  sides of the rank-one coincidence formal, no Gross–Zagier input anywhere.
- **`theRankClauseHoldsAtOne : TheRankClause 1 theWitness`** — for **every** `r`,
  `analyticRank = r ↔ AlgebraicRankIs 1 r`.  Both sides are decided at one (analytic
  rank zero by the positive theta integral, algebraic rank zero by the completed
  descent), so the equivalence closes at every `r` at once.  **The first complete
  clause of the posed Birch–Swinnerton-Dyer conjecture proven whole at an instance.**

## 2. What separates this from the full conjecture at these instances

Named, with their mechanism:

1. **The descent upper bound at five** (`¬AlgebraicRankAtLeast 5 2`, closing
   `AlgebraicRankIs 5 1` and hence `TheRankClause 5`).  Two pieces: the **halving
   converse** — a point whose three slot values are squares is a double (explicit
   half-point construction through the group law; the easy inclusion
   `theDoublesLandInTheKernelOnTheFiveCurve` is already in the tree) — and the
   **height descent** that converts kernel-membership into a finite generation
   argument (`HeightLattice.lean` is the staged material).  This is a fully formal
   Mordell–Weil instance: a pivot prize in its own right.
2. **The ledger clause at one** — the exact value `L(1) = Ω/8` (lemniscatic period,
   arithmetic–geometric mean; the certified-interval species of `exact_value.rs`
   carried into Lean).
3. **The even-sector second chart at 34** — the ternary count, per the
   sign-hand record.

## 3. The traversal pattern this day establishes

Five commits moved one instance of the conjecture from *posed* to *rank clause whole*:
theta by lattice folds → reflection with a hand → positivity through the reflection →
fold at the fixed point → certified compact remainder → reciprocity weld.  Every step
is parametrized by the modulus, not special to five; the same traversal reaches every
odd-sign twist.  The two instruments that carried all of it — **exact lattice
bijection replacing analysis** and **positivity transported by a reflection** — are
the two halves of integration by reflection, and they are the pivot payload for the
Riemann route (weight one-half, the same construction) and for the Weil-positivity
chart of the one missing organ.
