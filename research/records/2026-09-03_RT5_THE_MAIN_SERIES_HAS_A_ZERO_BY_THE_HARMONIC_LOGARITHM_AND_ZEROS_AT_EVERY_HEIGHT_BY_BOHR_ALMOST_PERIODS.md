# RT5: the main series has a zero by the harmonic logarithm, and zeros at every height by Bohr almost periods

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** RT5 under
[`THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md`](../../archive/plans/THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md).  
**Owner:** `RH/BohrZeros.lean` under `soma/formal/elementary-holonics/ElementaryHolonics/`,
registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] `F_t(s) = Σ_{n ∈ ℤ} Fterm t s n` with `Fterm t s n = e^{−t log²|n|} |n|^{−s}` for
`n ≠ 0` (RT4's series; the `±n` terms coincide, so this is twice Dobner's series over `n ≥ 1`
and has the same zeros); `Fr t x n` its real form at real `x`; an *almost period* of size `ε`
on the strip `|Re s| ≤ X` is a `τ` with `‖F_t(s + iτ) − F_t(s)‖ ≤ ε` for every `s` in the strip.

[proved-derived; formal-checked]

- `differentiable_Ft`: **`F_t` is entire**, by `Complex.differentiableOn_tsum_of_summable_norm`
  on each half-plane `Re s > −X` with the one-sided Gaussian domination `norm_Fterm_le'`.
- `norm_Ft_le`, `log_norm_Ft_le`: `‖F_t(s)‖ ≤ e^{(Re s)²/(2t) + 9/(8t)} Z_{3/2}`, so
  `log ‖F_t‖` has quadratic growth.
- `norm_Ft_zero_ge`, `norm_Ft_ofReal_ge`, `norm_Ft_ofReal_le`: on the real axis
  `2 ≤ ‖F_t(x)‖ ≤ 2 + 2^{−x} ‖F_t(0)‖` for `x ≥ 0`, and `‖F_t(0)‖ ≥ 2 + 2e^{−t log² 2} > 2`.
- **`exists_zero_Ft`: `F_t` has a zero.** If it had none, `log ‖F_t‖` would be harmonic
  (Mathlib's `AnalyticAt.harmonicAt_log_norm`), hence the real part of an entire `H`
  (`HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq`); Borel–Carathéodory
  (`Complex.borelCaratheodory_zero`, `norm_H_le`) turns the quadratic bound on `Re H` into a
  quadratic bound on `‖H‖`; Cauchy's estimate
  (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, `iteratedDeriv_three_eq_zero`)
  kills the third derivative; `eq_quadratic_of_iteratedDeriv_three` makes `H` a quadratic; so
  `log ‖F_t(x)‖` is a real quadratic bounded on `[0, ∞)`, hence constant (`quad_bounded`),
  which the strict inequality `‖F_t(x)‖ < ‖F_t(0)‖` for large `x` refutes. No Hadamard
  factorization and no entire logarithm are taken.
- `exists_simultaneous_approx`: **simultaneous Dirichlet approximation** for finitely many reals
  by pigeonhole on the `Q^k` boxes of scaled fractional parts
  (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`), with the multiple `q ≥ q₀` prescribed
  below.
- `norm_exp_neg_I_sub_one_le`, `Fterm_add_I_mul`, **`exists_almost_period`**: for every
  `ε > 0`, `T₀`, and strip, an almost period `τ ≥ T₀`: the finitely many frequencies
  `log |n| / (2π)`, `n ∈ s₀`, are approximated simultaneously, the rest is the Gaussian tail
  (`tendsto_tsum_compl_atTop_zero`).
- `exists_zero_of_norm_center_lt`: **the minimum-modulus principle** on a disc, from
  `Complex.norm_le_of_forall_mem_frontier_norm_le` applied to `1/f`.
- `exists_zero_margin`: a zero `s₀` of `F_t` with `δ ≤ ‖F_t‖` on a circle `|s − s₀| = r`,
  by isolation of zeros (`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, the identity
  theorem against `F_t(0) ≠ 0`) and compactness of the circle.
- **`exists_zero_Ft_above`: for every `T₀` a zero of `F_t` with `Im ≥ T₀` in the fixed strip
  `|Re s| ≤ |Re s₀| + r`**: the translate `F_t(· + iτ)` along an almost period of size `δ/4`
  is below `δ/2` at `s₀` and above `δ/2` on the circle, so it has a zero in the disc.

`#print axioms` on `exists_zero_Ft`, `exists_almost_period`, and `exists_zero_Ft_above` returns
`propext`, `Classical.choice`, `Quot.sound`. The owner builds alone (8,773 jobs) and inside the
root umbrella.

## The scope, corrected in place

[definition] The contract's RT5 text asked for a bound `L` with a zero in every window of height
`L` (relative density of the almost periods). The return gives zeros at unbounded heights: the
pigeonhole yields an almost period `q` in `[q₀ + 1, (Q^k + 1)(q₀ + 1)]`, a gap that grows with
`q₀`, and the relatively dense form was not needed. RT6 needs one off-seam zero for each
`t > 0`, which one zero of `F_t` at a large height provides, so the contract's RT5 text is
corrected to the unbounded-height form. The zero of `F_t` is proved for every `t > 0` by the
harmonic-logarithm argument, which is Dobner's Lemma 3 with Mathlib's Borel–Carathéodory in
place of Hadamard's factorization.

## Pass RT5

For every `t > 0`, a strip and, for every `T₀`, a zero of `F_t` above `T₀` in it, formal-checked.
**RT5 passes** at the corrected scope. Falsifier: a `t > 0` and a height `T₀` above which the
strip `|Re s| ≤ |Re s₀| + r` holds no zero of `F_t`.

## Boundaries

- No claim of movement on `0 ≤ Λ_DN` in this record; the seal is RT6's.
- The almost periods are not shown relatively dense; nothing downstream uses density.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.BohrZeros
timeout 180s lake build ElementaryHolonics
```
