# Landau at height with an explicit budget

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8715 jobs for the owner cone; root module green, 9733 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, making Landau's lemma for ξ explicit at the base points 2 + iτ: the growth bound above and the lower bound below give a budget and a Jensen count that are both polynomial in the height. Assistant derivation for the proofs.
**Band:** heightBudget C r τ = max 1 (C(5+|τ|+r) log(5+|τ|+r) + |τ| + 2) / heightCount = (heightBudget + |τ| + 2)/log(3/2) / xiBudget ≤ heightBudget / JENSEN COUNT ≤ heightCount / FLUX REMAINDER ≤ 16(heightBudget + heightCount·log 2)/r ON THE EIGHTH DISC / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `heightBudget C r τ = max 1 (C (2 + |τ| + r + 3) log(2 + |τ| + r + 3) + (|τ| + 2))`
and `heightCount C r τ = (heightBudget C r τ + |τ| + 2) / log(3/2)`.

[proved-derived] `riemannXi_two_add_ne_zero`: `ξ(2 + iτ) ≠ 0`. `xiBudget_le`: the Landau budget
`xiBudget C (2 + iτ) r` is at most `heightBudget C r τ`, by `‖2 + iτ‖ ≤ 2 + |τ|`, the
monotonicity of `u log u`, and `−log |ξ(2 + iτ)| ≤ |τ| + 2`. `log_jensen_le`: the Jensen
logarithm `log(jensenCeiling / |ξ(2 + iτ)|)` is at most `heightBudget + |τ| + 2`, in both
branches of the ceiling's `max`.

[proved-derived] `exists_zeroFactorization_at_height` (**Landau at height**): for the growth
constant `C` of `ξ`, `|τ| ≥ 2`, and `r > 0`, there is a zero factorization of `ξ` on the disc of
radius `r` about `2 + iτ` whose count is at most `heightCount C r τ` and whose flux remainder
satisfies `‖ξ′/ξ(z) − Σ m_ρ/(z − ρ)‖ ≤ 16 (heightBudget + heightCount · log 2) / r` on the
closed eighth disc, wherever `ξ(z) ≠ 0`.

## Constants

[definition] `5 = 2 + 3`: the `2` is the real part of the base point, the `3` the offset of the
growth bound `log |ξ(z)| ≤ C (‖z‖ + 3) log(‖z‖ + 3)`. `log(3/2)` is the Jensen ratio of the
radii `3r/4` and `r/2`. `16 = 2 · 8` is the Landau constant on the eighth disc, and `log 2` the
cost per zero of the maximum principle on the three-quarter disc. All inherited.

## Holonic reading

[definition] The horizontal edges of the explicit-formula rectangle are read from base points
on the line `Re s = 2`; this owner returns the whole Landau apparatus there with a budget that
is explicit in the height. What remains for the edge bound is the flux itself, which the
height selection keeps at distance `1/(2(N+1))` from every zero.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/LandauAtHeight.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.XiLowerBoundOnLineTwo`.
- Axiom audit for `exists_zeroFactorization_at_height`: `[propext, Classical.choice, Quot.sound]`.
