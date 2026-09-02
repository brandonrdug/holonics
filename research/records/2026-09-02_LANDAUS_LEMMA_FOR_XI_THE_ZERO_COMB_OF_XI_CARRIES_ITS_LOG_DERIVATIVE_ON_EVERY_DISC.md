# Landau's lemma for ξ: the zero comb of ξ carries its log-derivative on every disc

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8720 jobs for the owner cone; root module green)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, applying Landau's lemma to ξ with the corpus's pointwise abscissa growth, closing the analytic input of the explicit-formula population side. Assistant derivation for the proofs.
**Band:** xiBudget C z₀ r = max 1 (C (‖z₀‖ + r + 3) log(‖z₀‖ + r + 3) − log‖ξ(z₀)‖) / ‖ξ‖ ≤ ‖ξ(z₀)‖ e^{BUDGET} ON THE DISC BY x log x MONOTONICITY / ZERO FACTORIZATION OF ξ CONSTRUCTED / ‖ξ′/ξ − Σ m_ρ/(z − ρ)‖ ≤ 16 (BUDGET + N log 2)/r ON THE r/8 DISC / 16 = 2⁴, 3 = 3 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[definition] `xiBudget C z₀ r = max 1 (C (‖z₀‖ + r + 3) log(‖z₀‖ + r + 3) − log ‖ξ z₀‖)`, the
growth budget of `ξ` on the disc `ball z₀ r` with the pointwise abscissa constant `C`.

[proved-derived] `norm_riemannXi_le_of_growth`: on the disc, `‖ξ z‖ ≤ ‖ξ z₀‖ e^{budget}`, since
`‖z‖ ≤ ‖z₀‖ + r` and `x log x` is monotone past one, so the pointwise bound at `z` is dominated
by the bound at the disc's outer radius.

[proved-derived] `exists_zeroFactorization_riemannXi`: for every `z₀` with `ξ z₀ ≠ 0` and every
`r > 0` there are the growth constant `C > 0` of `pointwiseAbscissaGrowthOfRiemannXiHolds` and
a constructed zero factorization `Z` of `ξ` on the disc such that on the closed `r/8` disc, off
the zeros, `‖ξ′/ξ(z) − Σ_{ρ ∈ Z.zeros} m_ρ/(z − ρ)‖ ≤ 16 (xiBudget C z₀ r + N log 2)/r`.

## Holonic reading

[definition] The log-derivative of `ξ` is now, on every disc of the plane, the Coulomb flux of
the zeros of the half disc plus a background paid for by the abscissa growth: the same pairwise
law `1/(z − ρ)` as the de Bruijn--Newman zero dynamics, read statically. The zero comb of `ξ`
carries its own log-derivative. Every contour integral of `ĥ · ξ′/ξ`, the arithmetic side of the
explicit formula, can now be cut into comb terms and a remainder controlled by `M/r`; this is the
analytic input the residual-identity port needs, and the horizontal-segment bounds of the
rectangular explicit formula are its immediate consequence once `N` is counted.

[established-bounded] `N` is still carried explicitly; Jensen's count (`AnalyticOnNhd.sum_divisor_le`)
bounds it by the same budget over `log 2`, which is the next owner. The residual identity itself
then needs the rectangle contour rather than the corpus's circle.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/LandauXi.lean` compiles under
  `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.ZeroFactorizationExists`.
