# The explicit formula in the limit

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9737 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, assembling the explicit formula in the limit: along selected heights T_n ∈ [n+2, n+3], the weighted divisor sum of ξ over the rectangle differs from the prime side by a quantity tending to zero, for every entire weight of decay (1 + |t|)⁻⁵ on the strip. Assistant derivation for the proofs.
**Band:** zeroSide = Σᶠ divisor(ξ, OPEN RECTANGLE)·h / primeSide = i·(∫ h·arch − Σ_n ∫ h Λ(n) s^{−n}) + i·(SAME WITH h(1−s)) ON Re s = 1+δ / NO ZERO OF ξ ON THE BOUNDARY AT THE SELECTED HEIGHT / ‖2πi·zeroSide − primeSide‖ ≤ 2K·edgeConst·(1+2δ)/(1+T₀) / Tendsto → 0 ALONG T_n ∈ [n+2, n+3] / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `riemannXi_ne_zero_of_one_lt_re`, `riemannXi_ne_zero_of_re_lt_zero`: `ξ` does
not vanish right of `Re s = 1` or left of `Re s = 0`. `riemannXi_eq_zero_of_mem`: the zeros of a
factorization of `ξ` are zeros of `ξ`. `boundaryRect_cases`: a boundary point of the rectangle
lies on one of its four edges.

[definition] `zeroSide δ h T = Σᶠ_u divisor(ξ, (−δ, 1+δ) × (−T, T))(u) · h(u)` and
`primeSide δ h T` is the prime side at height `T` on the line `Re s = 1 + δ`: the archimedean
integral minus the von Mangoldt sum, for the weights `h(s)` and `h(1 − s)`, each multiplied by
`i`.

[proved-derived] `explicit_formula_at_height`: for the growth constant `C`, `δ > 0`, an entire
weight with `‖h(x + it)‖ ≤ K/(1 + |t|)⁵` on the strip, and `T₀ ≥ 2`, there is
`T ∈ [T₀, T₀ + 1]` with `‖2πi · zeroSide δ h T − primeSide δ h T‖ ≤ 2K · edgeConst · (1 + 2δ)/(1 + T₀)`.
The selected height keeps the horizontal edges free of zeros; the vertical edges are free by
the nonvanishing lemmas; so the finite-height formula applies to the factorization of `ξ` about
`0`, the interior sum is the divisor sum by the multiplicity owner, and the remainder is the two
horizontal edges bounded by the previous owner.

[proved-derived] `explicit_formula_limit` (**the explicit formula in the limit**): under the
same decay hypothesis there are heights `T_n ∈ [n + 2, n + 3]` with
`2πi · zeroSide δ h (T_n) − primeSide δ h (T_n) → 0`.

## Constants

[definition] `2 = 1 + 1`: the two horizontal edges. Everything else is inherited.

## Holonic reading

[definition] The zero comb of `ξ`, read as the divisor on a growing rectangle and weighted by
the test, is asymptotically the prime comb read twice from the line `Re s = 1 + δ`, once with
`h(s)` and once with `h(1 − s)`, together with the archimedean integrals. This is the explicit
formula as the corpus wanted it: one rectangle integral read two ways, with the height sent to
infinity along the heights where the horizontal edges keep their distance from the zeros. On the
zero side there is only the divisor of `ξ`; no factorization, no circle, no free boundary scalar.

[established-bounded] Not closed here: the convergence of `primeSide` itself as `T → ∞` (the
improper integrals along the line and the exchange with the von Mangoldt sum), and the decay of
the spectral kernel of a compactly supported smooth arithmetic kernel on vertical strips, which
supplies the hypothesis for the corpus's Weil test functions. Both are classical; neither is
needed for the asymptotic identity above.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/ExplicitFormulaLimit.lean` compiles
  under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.EdgeIntegralVanishes`.
- Axiom audit for `explicit_formula_limit`, `explicit_formula_at_height`:
  `[propext, Classical.choice, Quot.sound]`.
