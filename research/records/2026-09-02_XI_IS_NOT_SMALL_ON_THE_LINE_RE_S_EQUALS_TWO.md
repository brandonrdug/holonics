# ξ is not small on the line Re s = 2

**Date:** 2026-09-02
**Truth status:** `proved-derived`
**Evidence:** `formal-checked` (Lean `v4.33.0`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`); `measured` (`lake` job count: 8712 jobs for the owner cone; root module green, 9732 jobs)
**Provenance:** Assistant, under Brandon's standing loop of 2026-09-02, bounding ξ from below on the line Re s = 2, where Landau's lemma for the horizontal edges takes its base point: the Möbius series inverts ζ, the reflection formula gives |Γ(1 + iy)|² = πy/sinh(πy), and |s(s − 1)| ≥ 2. Assistant derivation for the proofs.
**Band:** |L(μ, s)| ≤ ζ(2) = π²/6 FOR Re s ≥ 2 / |ζ(s)| ≥ ½ / |Γ(1 + iy)|² = πy / sinh(πy) / |Γ(1 + iy)| ≥ e^{−π|y|/2} FOR |y| ≥ 1 / |Γℝ(2 + iT)| = |Γ(1 + iT/2)|/π / log |ξ(2 + iT)| ≥ −(|T| + 2) FOR |T| ≥ 2 / NO CONJECTURE CLOSED / RUST SOURCE UNCHANGED / CONSTRUCTION STATE UNCHANGED / COMMITTED ON MAIN

---

## Statement

[proved-derived] `norm_LSeries_moebius_le`: for `Re s ≥ 2`, `|L(μ, s)| ≤ Σ 1/n² = π²/6`, term by
term from `|μ(n)| ≤ 1` and `n^{Re s} ≥ n²`. `norm_riemannZeta_ge`: `|ζ(s)| ≥ 1/2` there, from
Mathlib's `ζ(s) · L(μ, s) = 1` and `π²/6 ≤ 2`.

[proved-derived] `Gamma_one_add_mul_Gamma_one_sub`: for `y > 0`,
`Γ(1 + iy) Γ(1 − iy) = πy / sinh(πy)`, from `Γ(z) Γ(1 − z) = π / sin(πz)`, the recurrence
`Γ(1 − iy) = (−iy) Γ(−iy)`, and `sin(π + iπy) = −i sinh(πy)`. `normSq_Gamma_one_add`: hence
`|Γ(1 + iy)|² = πy / sinh(πy)` by conjugation. `norm_Gamma_one_add_ge`,
`norm_Gamma_one_add_ge_abs`: `|Γ(1 + iy)| ≥ e^{−π|y|/2}` for `|y| ≥ 1`, since
`sinh(πy) ≤ e^{πy}/2` and `πy ≥ 1/2`.

[proved-derived] `norm_Gammaℝ_two_add`, `norm_Gammaℝ_two_add_ge`:
`|Γ_ℝ(2 + iT)| = |Γ(1 + iT/2)|/π ≥ e^{−π|T|/4}/π` for `|T| ≥ 2`.

[proved-derived] `log_norm_riemannXi_two_add_ge` (**`ξ` is not small on `Re s = 2`**): for
`|T| ≥ 2`, `log |ξ(2 + iT)| ≥ −(|T| + 2)`, from the product `ξ = ½ s(s − 1) Γ_ℝ ζ`, the bounds
`|s| ≥ 2`, `|s − 1| ≥ 1`, and `log(2π) ≤ 2 ≤ ... `; the final constant uses `π/4 ≤ 1` and
`e² > 2π`.

## Constants

[definition] `π²/6 = ζ(2)` is the Basel value from Mathlib; `1/2 ≤ 6/π²` uses `π < 3.15`.
`e^{−π|y|/2}` is the square root of `2πy · e^{−πy} ≥ e^{−πy}`, the lower half of
`πy / sinh(πy)` after `sinh(πy) ≤ e^{πy}/2`. The final slope `1 = 4 · (π/4)/π ≥ π/4` and offset
`2 ≥ log(2π)` (from `e > 2.718`, so `e² > 7.38 > 2π`) are the elementary product expansions of
the linear bound `−(|T| + 2)`.

## Holonic reading

[definition] Landau's lemma is a ratio bound: it controls `f′/f` on a disc by the growth of
`|f|/|f(z₀)|`. The corpus already had the numerator (the growth bound on `ξ`); this owner
returns the denominator on the line where the base points of the horizontal-edge bound sit.
With both, the budget `xiBudget C (2 + iT₀) r` is `O(T₀ log T₀)`, and the horizontal-edge bound
is polynomial in the height.

## Evidence

- `soma/formal/elementary-holonics/ElementaryHolonics/RH/XiLowerBoundOnLineTwo.lean` compiles
  under `lake env lean` and `lake build`; the root module `ElementaryHolonics` remains green.
- Registered in `ElementaryHolonics.lean` after `ElementaryHolonics.RH.ZeroGap`.
- Axiom audit for `log_norm_riemannXi_two_add_ge`, `normSq_Gamma_one_add`,
  `norm_riemannZeta_ge`: `[propext, Classical.choice, Quot.sound]`.
