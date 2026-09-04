# RT4: the flowed ξ after the shift is γ_t' times the main series plus a remainder that vanishes uniformly on every strip

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** RT4 under
[`THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md`](../../archive/plans/THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md).  
**Owner:** `RH/DescentApproximation.lean` under `soma/formal/elementary-holonics/ElementaryHolonics/`,
registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] `Fterm t s n = e^{−t log²|n|} e^{−s log|n|}` for `n ≠ 0` and `0` at `n = 0`;
`F_t(s) = Σ_{n ∈ ℤ} Fterm t s n` (twice Dobner's series over `n ≥ 1`, since `±n` contribute
equally); `R_t(s) = heatE t ξ (J_t s)/γ_t'(s) − F_t(s)`; `dterm t s n` the difference between
the flowed event and `γ_t'(s) · Fterm t s n`; `c = min(t,1)/8`; `Z_{3/2} = Σ_{n ∈ ℤ} |n|^{−3/2}`;
`tterm t X n = e^{X log|n| − (3c/8) log²|n|}`;
`ρ(w) = e^{X²/(2t) + 9/(8t)} Z_{3/2} · Bmaj t X w⁴ + 13 e^{−(c/8) w⁸} · e^{4X²/(3c) + 3/c} Z_{3/2}`.

[proved-derived; formal-checked]

- `exp_neg_mul_log_sq_le`: `e^{b L − a L²} ≤ e^{b²/(2a) + 9/(8a)} |n|^{−3/2}` for `L = log|n|`,
  `a > 0`, `b ≥ 0`: the Gaussian in `log|n|` is dominated by a convergent power with the
  constant exhibited (two completed squares).
- `norm_Fterm_le`, `summable_Fterm`, `tsum_norm_Fterm_le`: **`F_t` converges absolutely at every
  `s`**, with `Σ ‖Fterm‖ ≤ e^{X²/(2t) + 9/(8t)} Z_{3/2}` on `|Re s| ≤ X`.
- `heatE_J_eq`: `heatE t ξ (J_t s) = γ_t'(s) (F_t(s) + R_t(s))` whenever `γ_t'(s) ≠ 0`;
  `γt'_ne_zero_of`: `γ_t'(s) ≠ 0` for `‖s‖ ≥ 2`, `|Re s| ≤ X`, from RT3's lower bound.
- `hasSum_dterm`, `Rt_eq_tsum`, `norm_Rt_le_tsum`: `R_t(s) = Σ_n dterm t s n / γ_t'(s)` by RT1's
  absolutely convergent comb at `z = J_t s`, and `‖R_t(s)‖ ≤ Σ_n ‖dterm t s n‖ / ‖γ_t'(s)‖`.
- **`norm_dterm_le`: eventually in `w`, at `s = x + i w¹²` with `|x| ≤ X`, for every `n`,**
  `‖dterm t s n‖ ≤ ‖γ_t'(s)‖ (‖Fterm t s n‖ · Bmaj t X w⁴ + 13 e^{−(c/8)w⁸} tterm t X n)`:
  on the main range `L ≤ w⁴` the difference is `γ_t' · Fterm · r` with RT3's `‖r‖ ≤ Bmaj`; on
  the tail `L > w⁴` both the event (RT3's medium and large bounds) and the main term are at most
  `e^{−xL} e^{−(c/2)L²}` times `‖γ_t'‖`, and `e^{−(c/8)L²} ≤ e^{−(c/8)w⁸}` there.
- `tendsto_ρ`: **`ρ(w) → 0`**, by RT3's `tendsto_Bmaj` composed with `w ↦ w⁴` and the Gaussian
  tail.
- **`descent_approximation`: eventually in `w`, for every `s = x + i w¹²` with `|x| ≤ X`:
  `γ_t'(s) ≠ 0`, `heatE t ξ (J_t s) = γ_t'(s) (F_t(s) + R_t(s))`, and `‖R_t(s)‖ ≤ ρ(w)`.**

`#print axioms` on `descent_approximation` and `tendsto_ρ` returns `propext`,
`Classical.choice`, `Quot.sound`. The owner builds alone (8,772 jobs) and inside the root
umbrella (9,832 jobs).

## The scope, corrected in place

[definition] The contract's RT4 text asked for
`‖R_t(s)‖ ≤ C y^{−1/5} e^{(10/t) min(x, −2)²}` uniformly for `|x| ≤ C y^{1/4}`. The return
gives `‖R_t(s)‖ ≤ ρ(w)` with `ρ → 0` at the rate of `Bmaj t X w⁴`, which is `O(y^{−1/3})`,
uniformly on `|x| ≤ X` for each fixed `X ≥ 0`. The strip is fixed, not widening; the rate is
sharper. Since `s ↦ (Im s)^{1/12}` is onto `[0, ∞)`, "eventually in `w`" is "for all `s` with
`Im s ≥ y₀(t, X)`". RT5 places the zeros of `F_t` in a fixed strip and RT6 transfers on bounded
discs about them, so the fixed strip is what the seal uses; the contract's RT4 text is corrected
to this form.

## Pass RT4

The uniform bound formal-checked. **RT4 passes** at the corrected scope. Falsifier: `t > 0`,
`X ≥ 0`, and heights `w` beyond every threshold at which some `s = x + iw¹²`, `|x| ≤ X`, has
`‖R_t(s)‖ > ρ(w)`.

## Boundaries

- No claim of movement on `0 ≤ Λ_DN`; the port `RodgersTaoNonneg` stands until RT6.
- `F_t` has not yet been shown to have zeros; that is RT5's. `γ_t'(s) ≠ 0` on the strip is
  established here, so the zeros of `heatE t ξ ∘ J_t` at large height are exactly the zeros of
  `F_t + R_t`.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.DescentApproximation
timeout 180s lake build ElementaryHolonics
```
