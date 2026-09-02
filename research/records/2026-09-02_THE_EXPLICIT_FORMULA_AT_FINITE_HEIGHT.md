# The explicit formula at finite height

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8713 jobs for the owner cone; root module green, 9730 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, assembling the explicit formula on the rectangle [−δ, 1 + δ] × [−T, T]: the weighted zero comb inside equals the two horizontal edges plus the two prime-comb edges, each the archimedean integral minus the von Mangoldt sum. Assistant derivation for the proofs.
**Band:** ξ FACTORIZES ON EVERY DISC ABOUT 0 SINCE ξ(0) = ½ / RECTANGLE [−δ, 1+δ] × [−T, T] INSIDE THE HALF DISC / 2πi Σ_{ρ inside} m_ρ h(ρ) = HORIZONTAL EDGES + i·(∫ h·arch − Σ_n ∫ h Λ(n) n^{−s}) + i·(∫ h(1−s)·arch − Σ_n ∫ h(1−s) Λ(n) n^{−s}) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `exists_zeroFactorization_riemannXi_zero`: `ξ` has a `ZeroFactorization` on
every disc about `0`, because `ξ(0) = 1/2 ≠ 0`. `closedRect_subset_ball`: the closed rectangle
`[−δ, 1 + δ] × [−T, T]` lies in the open disc of radius `2 + δ + T` about `0`.

[proved-derived] `explicit_formula_finite_height` (**the explicit formula at finite height**):
for an entire weight `h`, `δ, T > 0`, the rectangle with corners `−δ − iT` and `1 + δ + iT`, and
a factorization `Z` of `ξ` on the disc of radius `2(2 + δ + T)` about `0` none of whose zeros lies
on the rectangle's boundary,

`2πi · Σ_{ρ ∈ Z.zeros} [ρ inside] · m_ρ · h(ρ)`
`= ∫_{−δ}^{1+δ} h(x − iT) ξ′/ξ(x − iT) dx − ∫_{−δ}^{1+δ} h(x + iT) ξ′/ξ(x + iT) dx`
`+ i · (∫_{−T}^{T} h(s) archimedean(s) dt − Σ_n ∫_{−T}^{T} h(s) Λ(n) s^{−n} dt)`
`+ i · (∫_{−T}^{T} h(1 − s) archimedean(s) dt − Σ_n ∫_{−T}^{T} h(1 − s) Λ(n) s^{−n} dt)`,

with `s = 1 + δ + it`. The proof is the rectangle argument principle for `Z`, the fold of the
vertical edges, and the prime comb on the right edge applied to the weights `h(s)` and
`h(1 − s)`; the sums are `tsum`s of the convergent von Mangoldt series.

## Constants

[definition] The disc radius `2(2 + δ + T) = 2 · (2 + δ + T)` is twice the half-disc radius
`2 + δ + T`, which exceeds `1 + δ + T ≥ |Re| + |Im|` on the rectangle by one; the factor `2` is
the factorization's convention that its zeros lie in the half disc. `2πi` and `½` are inherited.

## Holonic reading

[definition] This is the explicit formula as one rectangle integral read two ways, at finite
height: the interior returns the zero comb, the vertical edges return the prime comb twice (once
from each side of the critical line), and the horizontal edges are the only remainder. The
remainder is where the height enters: it is bounded by Landau for `ξ` (`JensenCountsTheComb`)
along heights at which the horizontal edges keep their distance from the zeros.

[established-bounded] Remaining for the explicit formula in the limit: the horizontal-edge
bound `|ξ′/ξ| ≪ (log T)²` along a good sequence of heights (Landau's flux with the Jensen count
of zeros within distance one, and the choice of `T` in each unit interval at distance `≫ 1/log T`
from every zero), the decay of the weight in the vertical direction, and the limit of the
interior sum over all zeros.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/ExplicitFormulaFiniteHeight.lean`
  compiles under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains
  green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.XiEdgeDecomposition`.
- Axiom audit for `explicit_formula_finite_height`, `exists_zeroFactorization_riemannXi_zero`:
  `[propext, Classical.choice, Quot.sound]`.
