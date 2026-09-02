# A height between the zeros

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: owner cone within Mathlib; root module green, 9731 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, selecting the height of the explicit-formula rectangle: every unit interval contains a height at distance at least 1/(2(N+1)) from N given imaginary parts. Assistant derivation for the proofs.
**Band:** N + 2 CANDIDATES SPACED 1/(N+1) APART / EACH POINT BLOCKS AT MOST ONE CANDIDATE / A FREE CANDIDATE EXISTS BY COUNTING / DISTANCE ≥ 1/(2(N+1)) FROM EVERY POINT / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `cand_eq_of_close`: two candidates `a + j/(N+1)`, `a + k/(N+1)` both within
`1/(2(N+1))` of the same real number coincide, since their difference `|j − k|/(N+1)` is then
below `1/(N+1)`.

[proved-derived] `exists_gap`: for a finite set `S` of reals with `N = |S|` and any `a`, there is
`T ∈ [a, a+1]` with `1/(2(N+1)) ≤ |T − p|` for every `p ∈ S`. Each `p` blocks at most one of the
`N + 2` candidates `a + k/(N+1)`, `k ≤ N + 1`, so a free candidate exists by counting.

## Constants

[definition] The gap `1/(2(N+1)) = 1 / (2 · (N + 1))`: half the candidate spacing `1/(N+1)`,
the spacing being one unit divided among `N + 1` steps so that `N + 2` candidates fit in a unit
interval. No other constant appears.

## Holonic reading

[definition] The horizontal edges of the explicit-formula rectangle must keep their distance
from the zero comb; this owner returns that distance as a function of the local count alone,
which the Jensen owner bounds. Together with Landau for `ξ`, this gives the polynomial bound on
`ξ′/ξ` along the selected height.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/ZeroGap.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.ExplicitFormulaFiniteHeight`.
- Axiom audit for `exists_gap`: `[propext, Classical.choice, Quot.sound]`.
