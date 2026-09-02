# The horizontal-edge integrals vanish under polynomial decay

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8729 jobs for the owner cone; root module green, 9736 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, closing the horizontal edges of the explicit-formula rectangle: the edge bound is at most a constant times (T₀ + 1)⁴, and a weight decaying like (1 + |t|)⁻⁵ on the strip makes both edge integrals O(1/T₀) at the selected height. Assistant derivation for the proofs.
**Band:** heightBudget ≤ budgetConst·(|τ|+1)² / heightCount ≤ countConst·(|τ|+1)² / edgeBound ≤ edgeConst·(T₀+1)⁴ / ‖∫ EDGE‖ ≤ K·B·(1+2δ) / DECAY K/(1+|t|)⁵ ⇒ BOTH EDGE INTEGRALS ≤ K·edgeConst·(1+2δ)/(1+T₀) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `budgetConst C r = C (5 + r)² + 3`, `countConst C r = (budgetConst + 2)/log(3/2)`,
and `edgeConst C δ` is the edge bound's shape with `budgetConst`, `countConst` in place of
`heightBudget`, `heightCount`, at radius `8(3 + δ)`.

[proved-derived] `heightBudget_le`, `heightCount_le`: for `|τ| ≥ 2`,
`heightBudget ≤ budgetConst · (|τ| + 1)²` and `heightCount ≤ countConst · (|τ| + 1)²`, using
`log u ≤ u` and `5 + |τ| + r ≤ (5 + r)(|τ| + 1)`. `edgeBound_le`: for `T₀ ≥ 2`,
`edgeBound C δ T₀ ≤ edgeConst C δ · (T₀ + 1)⁴`.

[proved-derived] `norm_edge_integral_le`: a weight bounded by `K` and a log derivative bounded
by `B` along an edge of length `1 + 2δ` give an edge integral of norm at most `K B (1 + 2δ)`.

[proved-derived] `exists_height_edges_small` (**the horizontal edges vanish**): for the growth
constant `C`, `δ > 0`, a weight with `‖h(x + it)‖ ≤ K/(1 + |t|)⁵` on the strip
`−δ ≤ x ≤ 1 + δ`, and `T₀ ≥ 2`, there is `T ∈ [T₀, T₀ + 1]` on whose two horizontal edges `ξ`
does not vanish and both edge integrals of `h · ξ′/ξ` are at most
`K · edgeConst C δ · (1 + 2δ)/(1 + T₀)`.

## Constants

[definition] `5 = 4 + 1` is the decay order needed: four for `(T₀ + 1)⁴` and one to spare for
the limit `1/(1 + T₀) → 0`. `(5 + r)²` and `+3` in `budgetConst` come from `log u ≤ u` and from
`|τ| + 2 ≤ 3(|τ| + 1)²`; `+2` in `countConst` from `|τ| + 2 ≤ 2(|τ| + 1)²`. All inherited from
the explicit bounds.

## Holonic reading

[definition] With this owner the explicit formula at finite height has a vanishing remainder:
along the selected heights the interior divisor sum differs from the prime-comb side by a
quantity that is `O(1/T₀)` for every weight of polynomial decay. The limit statement is now a
matter of assembling the pieces; the analysis is done.

[established-bounded] Remaining: the assembled limit statement, and the decay of the spectral
kernel of a compactly supported smooth arithmetic kernel on vertical strips (which supplies the
decay hypothesis for the corpus's Weil test functions).

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/EdgeIntegralVanishes.lean` compiles
  under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.FactorizationMultiplicity`.
- Axiom audit for `exists_height_edges_small`, `edgeBound_le`:
  `[propext, Classical.choice, Quot.sound]`.
