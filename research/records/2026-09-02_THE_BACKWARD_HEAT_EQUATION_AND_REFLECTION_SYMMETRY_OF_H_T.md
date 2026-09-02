# The backward heat equation and reflection symmetry of H_t

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/HeatEquationEntire.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to carry the de Bruijn–Newman passage to Ξ: the growth bound passes to derivatives by Cauchy's estimate at radius one, ∂_z of the series is the series of f′ by Mathlib's termwise differentiation on a ball, the t-derivative of each term is minus the previous term of f″, termwise differentiation in t on a bounded interval with the point-independent majorant, and the reflection symmetry of Ξ passes through even derivatives. Assistant derivation for the proofs.
**Band:** HasGrowth f′ (A e^{B2^ρ}) (B2^ρ) ρ / ∂_z heatTerm = heatTerm OF f′ / ∂_z heatE t f = heatE t f′ / ∂_t heatTerm_{k+1} = −heatTerm_k OF f″ / ∂_t heatE t f = −heatE t f″ / ∂_t H_t = −∂_z² H_t / iteratedDeriv n (f(1−·)) = (−1)^n f^{(n)}(1−·) / H_t(1−s) = H_t(s) FOR Ξ / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.HeatEquationEntire` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/HeatEquationEntire.lean`, importing
`RH.XiGrowth`, `RH.ZeroComb`, and Mathlib's smooth series. Receiver: the partial derivatives of
`heatE t f z` in `z` and in `t`, and the value of `heatE t f` at `1 − s`.

## Theorems

[proved-derived] `hasGrowth_deriv`: `f′` has growth `(A e^{B 2^ρ}, B 2^ρ, ρ)`, from Cauchy's
estimate at radius one and `(‖z‖+1)^ρ ≤ 2^ρ(‖z‖^ρ + 1)`.

[proved-derived] `deriv_heatTerm`, `deriv_heatE`: `∂_z heatE t f = heatE t f′`, by
`hasSum_deriv_of_summable_norm` on the ball of radius `‖z‖+1` with the point-independent majorant.

[proved-derived] `hasDerivAt_heatTerm_succ`, `hasDerivAt_heatTerm_zero`: the `t`-derivative of the
`(k+1)`-st term of `f` is minus the `k`-th term of `f″`; the zeroth term is constant.

[proved-derived] `majorant_mono`, `hasDerivAt_heatE_t`: on `|t| < |t₀| + 1` the shifted derivative
sequence is bounded by a summable majorant, so `∂_t heatE t f = −heatE t f″` by
`hasDerivAt_tsum_of_isPreconnected`.

[proved-derived] `heat_equation`: `∂_t H_t(z) = −∂_z² H_t(z)` for `H_t = heatE t f`, every entire
`f` of order below two.

[proved-derived] `iteratedDeriv_comp_one_sub`, `heatE_one_sub`: reflection symmetry passes through
the flow.

[proved-derived] `heatE_riemannXi_one_sub`, `heat_equation_riemannXi`: `H_t(1 − s) = H_t(s)` and
the backward heat equation for `H_t = e^{−tD²} Ξ`.

## Position on the route

[established-bounded] `H_t = e^{−tD²} Ξ` is now an entire function, reflection-symmetric, and
satisfies the backward heat equation, exactly the equation from which `zero_curve_flux` derives the
comb flux of simple zeros at the polynomial face. The corpus's earlier `RodgersTaoZeroDynamics`
postulate names this equation; the equation is now a theorem for `Ξ`'s flow.

[established-bounded] Open on this route: the count inequality at the entire face, and the face
`t = 0`. Axioms: `[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: zero dynamics for `H_t` along a `C¹` curve of simple zeros
(the entire-function form of `zero_curve_flux`), and the conjugation symmetry `H_t(conj s) =
conj H_t(s)` so that the pair population of `H_t` is conjugation-closed.
