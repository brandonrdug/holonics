# FT1: the centre is positive, the count is `R log R`, and the inverse squares converge

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** FT1 under
[`THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md`](../../blueprint/THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md).  
**Owners:** `RH/XiCentre.lean`, `RH/FosterCount.lean`, and the unconditional restatements appended to
`RH/FosterTanks.lean`, all under `soma/formal/elementary-holonics/ElementaryHolonics/` and
registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## (i) The centre value

[proved-derived; formal-checked] `XiCentre.riemannXi_one_half_ne_zero`, from
`riemannXi_one_half_pos : ∃ v > 0, ξ(½) = v`. The route: Mathlib's `completedRiemannZeta₀ (½)` is
`Λ₀(¼)/2` for the even Hurwitz FE-pair at `a = 0`, and `Λ₀ = mellin f_modif`. At the symmetric
point `¼` the Mellin integrand is real and nonnegative. `theta_sub_one_nonneg` and
`theta_sub_one_le` bound the theta tail, `0 ≤ θ(t) − 1 ≤ 4 e^{−πt}` for `t ≥ 1`, by comparing the
sum over the nonzero integers with a geometric majorant split into its positive and negative
halves (`hasSum_tailMajorant`). `kernel_nonneg` and `weighted_kernel_le` read the modified kernel
on `(1, ∞)` directly and on `(0, 1)` through the theta functional equation, and bound the weighted
integrand by `4 e^{−x}` on `(0, ∞)`; the elementary inequality `x^{−5/4} e^{−π/x} ≤ e^{−π}` on
`(0, 1)` does the inner work. `integral_exp_neg_Ioi_zero` closes: `0 ≤ Λ₀(¼) ≤ 4`, so
`0 ≤ completedRiemannZeta₀(½) ≤ 2`, so `ξ(½) = ½ − Λ₀(½)/8 ≥ ¼`. The true value is `≈ 0.4971`;
the bound is crude on purpose and mentions no zero.

[proved-derived; formal-checked] `FosterTanks.exists_symmetricZeroFactorization_count'` and
`exists_paired_foster_form'` restate FT0 without the carried hypothesis. The hypothesis of the same
name in `OffLineJensen` is discharged by the same theorem.

## (ii) The count

[definition] `FosterCount.mult u := (meromorphicOrderAt ξ u).untop₀`, the global multiplicity;
`mult_eq_divisor` identifies it with the divisor on every closed disc containing `u`;
`mult_nonneg`; `mult_half : mult ½ = 0` from (i). `Zero := {u // mult u ≠ 0}`, and
`Zero.dist_pos`: no zero is the centre. `N R := ∑ᶠ u, if u ∈ closedBall ½ R then mult u else 0`,
and `N_eq_inner` identifies it with the tree's `innerRiemannXiZeroCount ½ R`.

[definition] `growthC` is the order-one envelope's constant, chosen once from
`abscissaGrowthOfRiemannXiHolds`; `L₀ := max 0 (−log ‖ξ(½)‖)`; `K := (6 growthC + L₀) / log 2`.

[proved-derived; formal-checked] `count_le`: for `R ≥ 3`, `N R ≤ K · (R · log R)`. The chain:
`logTwo_mul_N_le` composes the tree's inner-count-by-outer-Jensen passage with the weighted Jensen
count at the fixed constant (`weightedCount_le`), then `a log a ≤ 6 R log R` for `a = 2R + 5/2` by
`mulLog_mono_on_one` and `log 3 ≤ log R`, and `R log R ≥ 1` absorbs the centre's debt. The constant
is exhibited from the envelope's, not existential per radius.

## (iii) The exponent of convergence

[proved-derived; formal-checked] `summable_inverse_square : Summable term` with
`term u := mult u · (‖u − ½‖²)⁻¹` over `Zero`. Dyadic shells: `shell u := (Int.log 2 ‖u − ½‖).toNat`;
`lt_two_pow_shell_succ` places every zero of shell `k` inside the closed disc of radius `2^{k+1}`,
and `two_pow_shell_le` gives `2^k ≤ ‖u − ½‖` for `k ≥ 1`, so `invSq_le_of_shell` bounds the weight
by `4^{−k}`. `sum_le_weighted_finsum` dominates any finite family of zeros in a disc by the
weighted finsum over the disc. Hence `fibre_sum_le`: the partial sums over shell `k ≥ 1` are at
most `4^{−k} N(2^{k+1}) ≤ 2 K log 2 · (k+1) 2^{−k}`, and `fibre_zero_sum_le` bounds the inner shell
by the finite weighted count `M₀`. `summable_sigma_of_nonneg` over `Equiv.sigmaFiberEquiv shell`
and `summable_pow_mul_geometric_of_norm_lt_one` close the sum.

`#print axioms` on `riemannXi_one_half_ne_zero`, `exists_paired_foster_form'`, `mult_half`,
`count_le`, `fibre_tsum_le`, and `summable_inverse_square` returns `propext`, `Classical.choice`,
`Quot.sound`. The owners build alone and inside the root umbrella.

## Pass FT1

All three theorems are formal-checked; the constant `K` is exhibited from the envelope's constant
and the centre value; the FT0 existence theorems are restated without the carried hypothesis.
**FT1 passes.** Falsifier unchanged: a radius at which the divisor mass the tree already computes
beats `K R log R`.

## Boundaries

- No claim of movement on the Riemann Hypothesis. Nothing here places a zero.
- `growthC` is fixed by choice from an existence theorem; its numerical value is not computed.
- The convergence exponent is two; the finer `Σ |ρ′|^{−1−ε}` is not needed by FT2 and is not
  claimed.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.XiCentre ElementaryHolonics.RH.FosterCount ElementaryHolonics.RH.FosterTanks
timeout 180s lake build ElementaryHolonics
```
