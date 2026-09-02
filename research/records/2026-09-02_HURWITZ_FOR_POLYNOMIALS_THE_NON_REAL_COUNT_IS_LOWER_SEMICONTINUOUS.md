# Hurwitz for polynomials: the non-real count is lower semicontinuous

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8730 jobs for the owner cone; root module green, 9752 jobs)
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02, returning the limit step for forward preservation: a polynomial is its own zero factorization, the rectangle argument principle counts its roots, the counts converge under coefficientwise convergence by dominated convergence on the four edges, integers eventually agree, and every non-real root of the limit is the limit of as many non-real roots of the approximants. Assistant derivation for the proofs.
**Band:** polyFactorization / rootCount p U = Σ_{ρ ∈ U} mult / ∮ p′/p = 2πi·rootCount / COEFFICIENT CONVERGENCE ⇒ UNIFORM ON BOUNDED SETS / EDGE INTEGRALS CONVERGE BY DOMINATED CONVERGENCE / INTEGER COUNTS EVENTUALLY EQUAL / SQUARES ABOUT THE NON-REAL ROOTS, DISJOINT, OFF THE AXIS / nonreal p ≤ nonreal (q N) EVENTUALLY / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `polyFactorization`: a nonzero polynomial as a `ZeroFactorization` of its own
evaluation (zeros the distinct roots, multiplicities the root multiplicities, unit the leading
coefficient). `rootCount p U = Σ_{ρ ∈ roots, ρ ∈ U} mult_ρ`, equal to the cardinality of the
filtered root multiset.

[proved-derived] `rectIntegral_logDeriv_poly` (**the rectangle counts the roots**): for a
rectangle whose boundary carries no root, `∮ p′/p = 2πi · rootCount p (openRect)`.

[proved-derived] `eventually_norm_eval_sub_lt`: coefficientwise convergence with a degree bound
gives uniform convergence on every bounded set. `tendsto_edge_integral`: along an edge on which
`p ≠ 0`, eventually `q N ≠ 0` and `∫ q N′/q N → ∫ p′/p` (dominated convergence with the constant
bound `(D + 1)/(δ/2)`). `tendsto_rectIntegral_logDeriv`: the four edges together; eventually no
root of `q N` lies on the boundary. `nat_eq_of_norm_sub_lt`, `eventually_rootCount_eq`
(**Hurwitz on a rectangle**): the integer counts are eventually equal.

[proved-derived] `rootCount_mono`, `sum_rootCount_disjoint`, `exists_square_radius`,
`norm_sub_le_of_mem_closedRect_square`, `mem_openRect_square`: squares of half-side `η` about
each non-real root, pairwise disjoint, off the real axis, containing no other root.
`nonreal_le_of_tendsto` (**the non-real count is lower semicontinuous**): under coefficientwise
convergence `q N → p` of real polynomials of bounded degree with `p ≠ 0`, eventually
`nonreal p ≤ nonreal (q N)`.

## Constants

[definition] `4η < ‖ρ − z‖` and `2η ≤ |Im z|`: the square of half-side `η` has diameter at most
`2η` in the `ℓ¹` sense, so two squares are disjoint when their centres are more than `2(η + η′)`
apart, and a square is off the axis when its height is below the centre's. `1/2` is the
integer gap. `(D + 1)/(δ/2)` is the dominated-convergence bound. All lineage in the proofs.

## Holonic reading

[definition] The rectangle receiver that returns the zero comb of `ξ` returns, for polynomials,
a count that cannot jump down in the limit: non-real roots of the limit are limits of non-real
roots. With the Hermite–Poulain step this is what carries "no pair is born" from the Euler
steps to the flow itself.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/HurwitzPolynomial.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.PolyaStep`.
- Axiom audit for `nonreal_le_of_tendsto`, `eventually_rootCount_eq`,
  `rectIntegral_logDeriv_poly`: `[propext, Classical.choice, Quot.sound]`.
