# The derivative-series heat flow is entire and extends the polynomial flow

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/HeatFlowEntire.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow and to carry the passage to Ξ through: heatE t f z = Σ_k (−t)^k/k! f^{(2k)}(z) agrees with the polynomial flow on polynomials, and for an entire f of order below two the terms are bounded on every ball by a point-independent summable majorant, so heatE t f is entire by Mathlib's locally uniform limit theorem. Assistant derivation for the proofs.
**Band:** heatE t f z = Σ'_k heatTerm t f z k / iteratedDeriv n (eval p) = eval (D^n p) / heatE t (eval p) = eval (heat t p) / majorant C δ k = (C k^{−δ})^k SUMMABLE / ‖heatTerm t f z k‖ ≤ A exp(B 2^ρ r^ρ) · majorant k FOR ‖z‖ ≤ r / heatE t f ENTIRE FOR 0 < ρ < 2 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.HeatFlowEntire` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/HeatFlowEntire.lean`, importing
`RH.EntireDerivativeGrowth` and `RH.HeatFlowOfPolynomials`. Receiver: the function
`heatE t f : ℂ → ℂ`, the derivative-series heat flow of an entire `f`.

## Theorems

[definition] `heatE t f z = Σ'_k heatTerm t f z k`.

[proved-derived] `iteratedDeriv_eval`: the `n`-th derivative of a polynomial function is the
evaluation of the `n`-th formal derivative.

[proved-derived] `heatTerm_poly`, `heatTerm_poly_eq_zero`, `heatE_poly`: on `fun w => p.eval w`
the series is finite and equals `(heat t p).eval z`, the polynomial flow of the corpus. The
derivative series therefore extends `heat` and, through `heat_map`, `heatR`.

[definition] `majorant C δ k = (C k^{−δ})^k` for `k ≥ 1`, `1` at `k = 0`.

[proved-derived] `summable_majorant` for `C ≥ 0`, `δ > 0`.

[proved-derived] `norm_heatTerm_le_majorant`: for `‖z‖ ≤ r`,
`‖heatTerm t f z k‖ ≤ A exp(B 2^ρ r^ρ) · majorant C δ k` with `δ = 2/ρ − 1`. The bound is
independent of the point on the ball.

[proved-derived] `differentiable_heatTerm`, `differentiable_heatE`: each term is entire, and by
`differentiableOn_tsum_of_summable_norm` on every ball, `heatE t f` is entire for `0 < ρ < 2`.

## Position on the route

[established-bounded] The de Bruijn–Newman flow on entire functions of order below two is now an
entire function for each `t`, agreeing with the exact polynomial flow on polynomials. The pair
population of `heatE t f` is a well-formed object. What is not yet transported is the count
inequality: on polynomials `nonreal (heatR t p) ≤ nonreal p` is a theorem; on entire functions
the corresponding statement needs polynomial approximants whose non-real count is controlled by
that of `f`, which is the Hadamard product, not the Taylor polynomial, and is the open passage.

[established-bounded] Nothing here touches the face `t = 0` of `Ξ`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: the backward heat equation for `heatE`, and the growth bound
`HasGrowth` for `Ξ`.
