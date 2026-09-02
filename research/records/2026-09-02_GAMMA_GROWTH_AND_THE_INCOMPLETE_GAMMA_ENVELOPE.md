# Gamma growth and the incomplete Gamma envelope

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `soma/formal/elementary-holonics/ElementaryHolonics/RH/GammaGrowth.lean`
**Provenance:** Assistant, under Brandon's direct instruction of 2026-09-02 to carry the de Bruijn–Newman passage to Ξ: the archimedean growth needed to bound Ξ to order one, Γ(b) ≤ exp(2(b+1)^{3/2}) for b ≥ 1 through Γ(b) ≤ Γ(⌈b⌉) = (⌈b⌉−1)! ≤ (b+1)^{b+1} and log y ≤ 2√y, and the incomplete integral ∫_1^∞ t^{a−1}e^{−πt} dt ≤ Γ(max a 1) ≤ exp(2(|a|+2)^{3/2}). Assistant derivation for the proofs.
**Band:** Γ(b) ≤ 2 FOR 1 ≤ b ≤ 2 / Γ(b) ≤ (b+1)^{b+1} FOR b ≥ 2 / (b+1)^{b+1} ≤ exp(2(b+1)^{3/2}) / Γ(b) ≤ exp(2(b+1)^{3/2}) FOR b ≥ 1 / t^{a−1}e^{−πt} ≤ e^{−t}t^{max(a,1)−1} ON t > 1 / ∫_1^∞ t^{a−1}e^{−πt} ≤ Γ(max a 1) ≤ G a = exp(2(|a|+2)^{3/2}) / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Owner

[definition] `Soma.Holonics.RH.GammaGrowth` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/GammaGrowth.lean`, importing Mathlib's
Bohr–Mollerup monotonicity and the Gamma integral. Receiver: the real Gamma function on `[1, ∞)`
and the incomplete integral `∫_1^∞ t^{a−1} e^{−πt} dt`.

## Theorems

[proved-derived] `Gamma_le_two_of_mem`: `Γ(b) ≤ 2` on `[1, 2]`, from `Γ(b+1) = bΓ(b) ≤ Γ(3) = 2`.

[proved-derived] `Gamma_le_rpow`: `Γ(b) ≤ (b+1)^{b+1}` for `b ≥ 2`, via monotonicity on `[2, ∞)`,
`Γ(⌈b⌉) = (⌈b⌉−1)!`, `n! ≤ n^n`, and `⌈b⌉ < b+1`.

[proved-derived] `rpow_self_le_exp`: `(b+1)^{b+1} ≤ exp(2(b+1)^{3/2})`, from `log y ≤ 2 y^{1/2}`.

[proved-derived] `Gamma_le_exp`: `Γ(b) ≤ exp(2(b+1)^{3/2})` for all `b ≥ 1`.

[proved-derived] `rpow_mul_exp_le`, `integrableOn_rpow_mul_exp`, `integral_rpow_mul_exp_le_Gamma`:
for every real `a`, `∫_1^∞ t^{a−1} e^{−πt} dt ≤ Γ(max a 1)`, by pointwise domination on `t > 1`
and enlargement of the domain to `(0, ∞)`.

[definition] `G a = exp(2(|a|+2)^{3/2})`.

[proved-derived] `Gamma_max_le_G`, `integral_rpow_mul_exp_le_G`: `∫_1^∞ t^{a−1} e^{−πt} dt ≤ G a`.

## Position on the route

[established-bounded] The Mellin transform of a kernel bounded by `C e^{−πt}` on `(1, ∞)` is now
bounded at `s` by `C · G(Re s)`, an envelope of order `3/2` in `Re s`. Together with the
functional-equation fold of the `(0, 1)` piece this bounds `completedRiemannZeta₀` and hence `Ξ`
by `A exp(B |s|^{3/2})`, which is `HasGrowth riemannXi A B (3/2)` with `3/2 < 2`, the hypothesis
of `differentiable_heatE`. That assembly is the next owner.

[established-bounded] Nothing here touches the face `t = 0`. Axioms:
`[propext, Classical.choice, Quot.sound]`; no `sorry`.

[established-bounded] Next: `XiGrowth`, the growth bound for `Ξ` from the Mellin representation
of `completedRiemannZeta₀` and the explicit Jacobi theta bound.
