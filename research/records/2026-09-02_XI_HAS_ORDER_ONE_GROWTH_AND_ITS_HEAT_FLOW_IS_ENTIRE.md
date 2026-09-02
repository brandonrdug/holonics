# Ξ has order-one growth and its heat flow is entire

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/XiGrowth.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to carry the de Bruijn–Newman passage to Ξ: the Mellin representation of completedRiemannZeta₀ through Mathlib's theta functional-equation pair, the fold of the (0,1) piece onto (1,∞) by the kernel's functional equation, the explicit Jacobi theta bound ‖θ(ix) − 1‖ ≤ 2e^{−πx}/(1 − e^{−π}) for x ≥ 1, the Gamma envelope on each Mellin piece, and the assembly ‖Ξ(s)‖ ≤ (Cθ e^{74} + 1) exp(10‖s‖^{3/2}). Hence H_t = e^{−tD²}Ξ is entire for every real t. Assistant derivation for the proofs.
**Band:** h = 1_{(1,∞)}(θ − 1), ‖h t‖ ≤ Cθ e^{−πt} / f_modif t = h t + t^{−1/2} h(1/t) ON (0,∞) / MellinConvergent h s FOR ALL s / ‖mellin h s‖ ≤ Cθ G(Re s) / Λ₀(s) = mellin h s + mellin h (1/2 − s) / ‖completedRiemannZeta₀ s‖ ≤ Cθ exp(8‖s‖^{3/2} + 72) / ‖Ξ s‖ ≤ (Cθ e^{74} + 1) exp(10‖s‖^{3/2}) / HasGrowth riemannXi A 10 (3/2) / heatE t riemannXi ENTIRE FOR EVERY REAL t / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.XiGrowth` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/XiGrowth.lean`, importing `RH.GammaGrowth`,
`RH.HeatFlowEntire`, `RH.RiemannXi`, and Mathlib's Riemann zeta and one-variable Jacobi theta.
Receiver: the norm of `Ξ` on the whole plane, and the derivative-series heat flow of `Ξ`.

## Theorems

[definition] `h t = 1_{(1,∞)}(t) (θ(it) − 1)` with `θ` the theta kernel of Mathlib's functional
equation pair; `Cθ = 2/(1 − e^{−π})`.

[proved-derived] `evenKernel_eq_jacobiTheta`, `norm_evenKernel_sub_one_le`: for `x ≥ 1`,
`‖θ(ix) − 1‖ ≤ Cθ e^{−πx}`, from Mathlib's explicit one-variable theta bound.

[proved-derived] `norm_term_le`, `aestronglyMeasurable_term`, `mellinConvergent_h`,
`norm_mellin_h_le`: the Mellin transform of `h` converges at every `s` and
`‖mellin h s‖ ≤ Cθ · G(Re s)` with the incomplete Gamma envelope `G`.

[proved-derived] `f_modif_eq`: on `(0, ∞)` Mathlib's modified kernel is
`h t + t^{−1/2} h(1/t)`, by the kernel's functional equation `θ(t) = t^{−1/2} θ(1/t)`.

[proved-derived] `mellinConvergent_second`, `mellin_second`, `norm_Λ₀_le`:
`Λ₀(s) = mellin h s + mellin h (1/2 − s)`, hence `‖Λ₀(s)‖ ≤ Cθ (G(Re s) + G(1/2 − Re s))`.

[proved-derived] `norm_completedRiemannZeta₀_le`, `G_le_of_abs_le`,
`norm_completedRiemannZeta₀_le'`: `‖completedRiemannZeta₀ s‖ ≤ Cθ exp(8‖s‖^{3/2} + 72)`.

[proved-derived] `norm_riemannXi_le`, `hasGrowth_riemannXi`:
`‖Ξ s‖ ≤ (Cθ e^{74} + 1) exp(10 ‖s‖^{3/2})`, that is `HasGrowth riemannXi A 10 (3/2)`.

[proved-derived] `summable_heatTerm_riemannXi`, `differentiable_heatE_riemannXi`: the heat series
of `Ξ` converges absolutely everywhere and `H_t = heatE t riemannXi` is entire for every real `t`.

## Position on the route

[established-bounded] The de Bruijn–Newman family `H_t` now exists in the corpus as an entire
function for every real `t`, defined by the derivative series `Σ_k (−t)^k/k! Ξ^{(2k)}` and
agreeing with the exact polynomial flow on polynomials. The pair population of `H_t` is a
well-formed object at every `t`. The constants are crude by design: the exponent `3/2` is what the
polynomial-to-entire passage needs, not a sharp order.

[established-bounded] What remains open on this route: the count inequality
`nonreal (H_t) ≤ nonreal (H_0)` at the entire-function face (the Hadamard-product approximation,
not the Taylor one), and the face `t = 0` itself, which is the Riemann hypothesis. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: the backward heat equation `∂_t H_t = −∂_z² H_t` for `heatE`, and
the reflection symmetry `H_t(1 − s) = H_t(s)` inherited from `Ξ`.
