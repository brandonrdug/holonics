# The heat series converges for entire functions of order below two

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/EntireDerivativeGrowth.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to take the pair population under the de Bruijn–Newman flow, opening the passage from the polynomial face to entire functions: Cauchy's estimate under a growth bound of order ρ, the choice R = k^{1/ρ} for the 2k-th derivative, the factorial bounds (2k)! ≤ (2k)^{2k} and k^k/k! ≤ e^k, and the resulting term bound M (C k^{−(2/ρ−1)})^k, eventually below M/2^k when ρ < 2. Assistant derivation for the proofs.
**Band:** ‖f w‖ ≤ A exp(B‖w‖^ρ) / ‖f^{(n)}(z)‖ ≤ n! A exp(B(‖z‖+R)^ρ)/R^n / (a+b)^ρ ≤ 2^ρ(a^ρ+b^ρ) / R = k^{1/ρ}, R^ρ = k, R^{2k} = k^{2k/ρ} / (2k)! ≤ 4^k k^{2k}, 1/k! ≤ e^k/k^k / ‖(−t)^k/k! f^{(2k)}(z)‖ ≤ M (C k^{−(2/ρ−1)})^k / Σ_k ‖heatTerm t f z k‖ < ∞ FOR 0 < ρ < 2 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.EntireDerivativeGrowth` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/EntireDerivativeGrowth.lean`, importing
Mathlib's Cauchy estimate (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`) and the
real-power asymptotics. Receiver: the terms `heatTerm t f z k = (−t)^k/k! · f^{(2k)}(z)` of the
derivative-series heat flow on an entire function.

## Theorems

[definition] `HasGrowth f A B ρ`: `∀ w, ‖f w‖ ≤ A exp (B ‖w‖^ρ)`.

[proved-derived] `norm_le_of_mem_sphere`, `norm_iteratedDeriv_le`: on the circle of radius `R`
about `z` the growth bound reads `A exp (B (‖z‖+R)^ρ)`, and Cauchy's estimate gives
`‖f^{(n)}(z)‖ ≤ n! A exp (B (‖z‖+R)^ρ) / R^n` for every `R > 0`.

[proved-derived] `add_rpow_le`: `(a+b)^ρ ≤ 2^ρ (a^ρ + b^ρ)` for `a, b, ρ ≥ 0`, through the
larger of the two.

[proved-derived] `inv_factorial_le`: `1/k! ≤ e^k/k^k`, from Mathlib's `x^n/n! ≤ exp x`.

[proved-derived] `norm_heatTerm_le`: with `R = k^{1/ρ}`,
`‖heatTerm t f z k‖ ≤ A exp(B 2^ρ ‖z‖^ρ) · (4 e |t| exp(B 2^ρ) · k^{−(2/ρ−1)})^k` for `k ≥ 1`.

[proved-derived] `summable_heatTerm`: for `0 < ρ < 2` the heat series converges absolutely at every
`z` for every real `t`, since `k^{−(2/ρ−1)} → 0` puts the term below `M/2^k` eventually.

## Position on the route

[established-bounded] `Ξ` has order one and so satisfies `HasGrowth` with any `ρ ∈ (1, 2)`; the
derivative-series flow `H_t(z) = Σ_k (−t)^k/k! Ξ^{(2k)}(z)` is therefore defined pointwise as an
absolutely convergent series. Its holomorphy in `z`, its agreement with `heatR` on polynomials,
the backward heat equation, and the transport of the pair-count monotonicity from the polynomial
face are the remaining passage; the growth bound for `Ξ` itself is a separate owner.

[established-bounded] Nothing here touches the face `t = 0`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: the flow `heatE t f z = Σ_k heatTerm t f z k` as an entire function of
`z`, locally uniform convergence from the term bound, and agreement with `heatR` on polynomials.
