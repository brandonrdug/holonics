# The rectangle winds once

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8706 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, returning Cauchy's integral formula on a rectangle, which Mathlib lacks in residue form, so that the explicit formula can be posed on the contour whose right edge carries the prime comb. Assistant derivation for the proofs.
**Band:** RECTANGLE BOUNDARY INTEGRAL IN MATHLIB'S SHAPE / EDGE INTEGRABILITY, ADDITIVITY, SCALARS, FINITE SUMS, BOUNDARY CONGRUENCE / FOUR LOGARITHMIC PRIMITIVES / ∮ (ζ − ρ)⁻¹ = 2πi FOR INTERIOR ρ / ∮ g/(ζ − ρ) = 2πi g(ρ) / ZERO WHEN ρ IS OUTSIDE / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `rectIntegral f z w` is the positively oriented boundary integral of `f` around the
rectangle with corners `z` and `w`, written in the exact four-term shape of Mathlib's
`integral_boundary_rect_*` conclusions; `closedRect`, `openRect`, and `boundaryRect` are the
closed rectangle, the open rectangle, and their difference. `EdgeIntegrable f z w` is interval
integrability of `f` along the four edges.

[proved-derived] `bottom_mem`, `top_mem`, `right_mem`, `left_mem`: every edge point lies on
`boundaryRect`. `EdgeIntegrable.of_continuousOn`: continuity on the boundary gives edge
integrability. `rectIntegral_add`, `rectIntegral_const_mul`, `rectIntegral_congr`,
`rectIntegral_finset_sum`: the rectangle integral is additive, scalar-linear, depends only on the
boundary values, and commutes with finite sums of boundary-continuous integrands.
`rectIntegral_eq_zero_of_differentiableOn`, `rectIntegral_div_sub_of_notMem`: Cauchy--Goursat in
this shape, and its corollary that `g(ζ)/(ζ − ρ)` integrates to zero when `ρ` is outside the
closed rectangle.

[proved-derived] `integral_inv_horizontal`, `integral_inv_vertical_right`,
`integral_inv_vertical_left`: along each edge the primitive of `(ζ − ρ)⁻¹` is a principal
logarithm, with the left edge taken through `log(−(ζ − ρ))` so that no edge crosses the slit.
`log_neg_of_im_neg`, `log_neg_of_im_pos`: `log(−x) = log x ± πi` on the two half-planes.

[proved-derived] `rectIntegral_inv_sub`: for `z.re < w.re`, `z.im < w.im`, and `ρ` in the open
rectangle, `∮ (ζ − ρ)⁻¹ dζ = 2πi`. The eight logarithms at the four corners cancel in modulus;
the two sign changes on the left edge each contribute a half-turn.

[proved-derived] `rectIntegral_div_sub` (**Cauchy's formula on a rectangle**): for `g` continuous
on the closed rectangle and differentiable on the open one, `∮ g(ζ)/(ζ − ρ) dζ = 2πi · g(ρ)`. The
integrand is `dslope g ρ + g(ρ)(ζ − ρ)⁻¹` on the boundary; the difference quotient is continuous
on the closed rectangle and differentiable off `ρ`, so Mathlib's off-countable Cauchy--Goursat
kills it, and the residue term is the previous theorem.

## Constants

[definition] `2πi = 2 · π · i`: the product of the two half-turns, one from each of the two
identities `log(−x) = log x ± πi` met on the left edge, with `i` the orientation of the vertical
edges. No other constant appears.

## Holonic reading

[definition] The rectangle is the receiver on which both combs can be read at once: the right
edge lies where the Euler product converges and carries the prime comb (previous owner); the
interior returns the zero comb through this owner's residue. A circle cannot do this because it
has no edge inside the region of absolute convergence.

[established-bounded] Next: the rectangle argument principle for a `ZeroFactorization` (the log
derivative on the boundary is the Landau flux plus the log derivative of the unit; the unit's
term integrates to zero, each flux term returns `2πi · m_ρ · ĥ(ρ)` for interior `ρ` and zero for
exterior `ρ`), then the reflection of the left edge and the horizontal-edge bounds.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/RectangleCauchy.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green
  (9727 jobs).
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.PrimeSideVertical`.
- Axiom audit for `rectIntegral_inv_sub`, `rectIntegral_div_sub`, `rectIntegral_finset_sum`:
  `[propext, Classical.choice, Quot.sound]`.
