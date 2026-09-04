# RT1: the descent comb converges absolutely at every point, and each event carries a Gaussian weight in `n`

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** RT1 under
[`THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md`](../../blueprint/THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md).  
**Owner:** `RH/DescentComb.lean` under `soma/formal/elementary-holonics/ElementaryHolonics/`,
registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] For repository `t > 0` (standard `τ < 0`, the descent side) and every `z`, the flowed
integer events of FT5, `flowedTerm t z n u = e^{−t u²} · lapTerm (−1) z n u`, with
`lapTerm (−1) z n u = e^{(z − ½)u} |n|^{−1/2} φ(u + log |n|)` and the profile
`φ(v) = e^{v/2}(2π² e^{4v} − 3π e^{2v}) e^{−π e^{2v}}`. `Mφ := 2π² + 3π`; `a := Re z − ½`;
`L := log |n|`.

[proved-derived; formal-checked]

- `abs_φ_le`: `|φ(v)| ≤ Mφ e^{−|v|}` for every `v`, and `abs_φ_le_of_nonneg`:
  `|φ(v)| ≤ Mφ e^{−v} e^{−e^{2v}/2}` for `v ≥ 0` (from `x³ e^{−cx} ≤ 6/c³`, `cube_mul_exp_le'`).
- `norm_flowedTerm_le`: for `t > 0`, `n ≠ 0`,
  `‖flowedTerm t z n u‖ ≤ Mφ e^{(|a|+1)²/(2t)} |n|^{−3/2} e^{−(t/2)u²}`: the flow's Gaussian
  absorbs `e^{au} e^{|u|}` by `c|u| ≤ (t/2)u² + c²/(2t)` (`lin_le_sq`), and the event's translation
  gives `e^{−|u+L|} ≤ |n|^{−1} e^{|u|}`.
- `integrable_flowedTerm`: every flowed event is integrable for `t > 0`.
- `integral_norm_flowedTerm_le`: `∫ ‖flowedTerm t z n u‖ du ≤ K(t, z) |n|^{−3/2}` with
  `K(t, z) = Mφ e^{(|a|+1)²/(2t)} √(2π/t)` exhibited.
- **`norm_flowedTerm_le_split` and `integral_norm_flowedTerm_le_gaussian`: the Gaussian weight
  in `n`.** On `u ≤ −L/2` the flow's Gaussian is at most `e^{−tL²/8} e^{−(t/4)u²}` and the profile
  is bounded; on `u ≥ −L/2` the profile is doubly exponentially small,
  `|φ(u + L)| ≤ Mφ e^{−(u+L)} e^{−|n|/2}`. Hence
  `∫ ‖flowedTerm t z n u‖ du ≤ K₂(t, z) e^{−(min(t,1)/8) (log |n|)²}` with `K₂` exhibited, using
  `log² x ≤ 4x` (`log_sq_le_four_mul`) to fold `e^{−|n|/2}` into the Gaussian weight.
- `summable_norm_integral_flowedTerm`: `Σ_n ‖∫ flowedTerm t z n‖ < ∞` at every `z`, by the
  `|n|^{−3/2}` bound against Mathlib's `summable_abs_int_rpow`.
- **`hasSum_flowedTerm_of_pos`: for every `t > 0` and every `z`,
  `Σ_{n ∈ ℤ} ∫ flowedTerm t z n = heatE t ξ (z)`**, by the exchange `integral_tsum` under the
  finite `lintegral` sum, the kernel identity `heatE_riemannXi`, and `hasSum_lapTerm`;
  `heatE_eq_tsum_flowedTerm` restates it as a `tsum`.

`#print axioms` on `hasSum_flowedTerm_of_pos`, `summable_norm_integral_flowedTerm`,
`integral_norm_flowedTerm_le`, `norm_integral_flowedTerm_le_gaussian`, and `abs_φ_le` returns
`propext`, `Classical.choice`, `Quot.sound`. The owner builds alone in 4 s and inside the root
umbrella (9,813 jobs).

## The scope, corrected in place

[definition] The contract's RT1 text named the weight as `e^{−t (log |n|)²/4}`-type; the returned
exponent is `min(t, 1)/8`. The `1/8` comes from the crude split at `u = −L/2` and the fold of
`e^{−|n|/2}` through `log² |n| ≤ 4|n|`; nothing downstream needs the sharper constant, since RT3
computes each event's main term exactly and RT4 uses this bound only for the tail ranges. The
contract is corrected to the returned exponent.

## Pass RT1

`HasSum` at every `z` for every `t > 0`, formal-checked, with absolute convergence and the Gaussian
weight in `n`. **RT1 passes.** Falsifier: one `t > 0`, one `z`, and a divergent comb.

## Boundaries

- No claim of movement on `0 ≤ Λ_DN`; the port `RodgersTaoNonneg` stands until RT6.
- The identity is the kernel's own on the descent side; no continuation argument was needed, and
  none is claimed.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.DescentComb
timeout 180s lake build ElementaryHolonics
```
