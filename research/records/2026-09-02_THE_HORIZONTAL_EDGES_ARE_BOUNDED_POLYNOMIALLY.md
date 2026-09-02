# The horizontal edges are bounded polynomially in the height

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8727 jobs for the owner cone; root module green, 9734 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, bounding ξ′/ξ on the two horizontal edges of the explicit-formula rectangle at a selected height: Landau's remainder plus the flux of at most heightCount zeros, each at distance at least the gap. Assistant derivation for the proofs.
**Band:** HEIGHT T ∈ [T₀, T₀+1] AT GAP 1/(2(N+1)) FROM THE IMAGINARY PARTS OF THE ZEROS IN THE TWO HALF DISCS ABOUT 2 ± iT₀ / N ≤ 2·heightCount / ξ ≠ 0 ON BOTH EDGES / |ξ′/ξ| ≤ edgeBound = 16(heightBudget + heightCount·log 2)/r + 2·heightCount(2·heightCount + 1), r = 8(3+δ) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `card_zeros_le_count`: a factorization has at most `count` distinct zeros.
`edge_bound_of_gap`: at a point `z` of the closed eighth disc whose imaginary part is at
distance at least `ε` from the imaginary part of every zero of the factorization, `ξ(z) ≠ 0`
and `‖ξ′/ξ(z)‖ ≤ R + count/ε`, where `R` bounds the Landau remainder; the flux is bounded term
by term through `‖z − ρ‖ ≥ |Im z − Im ρ| ≥ ε`.

[definition] `edgeBound C δ T₀ = 16 (heightBudget + heightCount · log 2) / (8(3 + δ)) + 2 · heightCount · (2 · heightCount + 1)`,
with `heightBudget` and `heightCount` taken at radius `8(3 + δ)` and height `T₀`.

[proved-derived] `norm_edge_sub_le`: a point `x + iT` with `−δ ≤ x ≤ 1 + δ` and `|T − τ| ≤ 1`
lies within `3 + δ` of `2 + iτ`. `exists_good_height` (**the horizontal-edge bound**): for the
growth constant `C` of `ξ`, `δ > 0`, and `T₀ ≥ 2`, there is `T ∈ [T₀, T₀ + 1]` such that on both
edges `x ± iT`, `−δ ≤ x ≤ 1 + δ`, `ξ` does not vanish and `‖ξ′/ξ‖ ≤ edgeBound C δ T₀`. The two
Landau factorizations about `2 ± iT₀` at radius `8(3 + δ)` place both edges in their eighth
discs; the height is selected by `exists_gap` against the union of the imaginary parts of one
comb and the negated imaginary parts of the other, a set of at most `2 · heightCount` reals.

## Constants

[definition] `r = 8 (3 + δ) = 8 · (3 + δ)`: the eighth disc must reach `2 + δ` horizontally
(from `Re = 2` to `Re = −δ`) and one unit vertically (the selection window), so its radius is
`3 + δ` and the Landau radius is eight times that. `2 · heightCount` counts both combs; the
gap is `1/(2(N + 1))` with `N ≤ 2 · heightCount`, so `count/ε ≤ heightCount · 2(2 · heightCount + 1)`.

## Holonic reading

[definition] The horizontal edges are where the height enters the explicit formula, and this
owner returns their cost as a polynomial in the height: the remainder is `O(T₀ log T₀)` and the
flux is `O((T₀ log T₀)²)`. A weight that decays faster than any power along horizontal lines
therefore kills both edges in the limit; that decay is the last analytic ingredient.

[established-bounded] Remaining: the multiplicity of the factorization equals the analytic
order (so the interior comb is the divisor of `ξ`), and the limit along the selected heights
with a decaying weight.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/HorizontalEdgeBound.lean` compiles
  under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.LandauAtHeight`.
- Axiom audit for `exists_good_height`, `edge_bound_of_gap`:
  `[propext, Classical.choice, Quot.sound]`.
