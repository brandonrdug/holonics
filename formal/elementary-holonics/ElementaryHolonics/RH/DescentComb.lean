import Mathlib
import ElementaryHolonics.RH.FlowedExplicitFormula

/-!
# RT1: the descent comb everywhere

For repository time `t > 0` (standard `τ = −t < 0`, the descent side, Dobner's regime) the flowed
integer events of FT5 converge absolutely at **every** `z`, and their sum is `heatE t ξ (z)`.
FT5 returned this for `Re z > 1` by the Dirichlet-series domination of the unflowed events; here
the flow's Gaussian `e^{−t u²}` does the domination on its own, and the profile
`φ(v) = e^{v/2}(2π² e^{4v} − 3π e^{2v}) e^{−π e^{2v}}` is bounded by `(2π² + 3π) e^{−|v|}`.

**Returned.** `abs_φ_le`; the pointwise bound `norm_flowedTerm_le`
(`‖flowedTerm t z n u‖ ≤ M e^{(|a|+1)²/(2t)} |n|^{−3/2} e^{−t u²/2}`, `a = Re z − ½`); every flowed
event is integrable for `t > 0`; `integral_norm_flowedTerm_le` (the event's norm integral is at
most `K(t, z) |n|^{−3/2}`); `summable_norm_integral_flowedTerm` (absolute convergence of the comb
at every `z`); and **`hasSum_flowedTerm_of_pos`**: `Σ_n ∫ flowedTerm t z n = heatE t ξ (z)` for
every `t > 0` and every `z`. Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.DescentComb

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.FlowedExplicitFormula

/-! ## The profile is exponentially small on both sides -/

/-- The profile constant `2π² + 3π`. -/
def Mφ : ℝ := 2 * π ^ 2 + 3 * π

theorem Mφ_pos : 0 < Mφ := by
  unfold Mφ
  positivity

/-- `x³ e^{−cx} ≤ 6/c³` for `x ≥ 0`, `c > 0`, from `(cx)³/3! ≤ e^{cx}`. -/
theorem cube_mul_exp_le' {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    x ^ 3 * Real.exp (-c * x) ≤ 6 / c ^ 3 := by
  have h := Real.pow_div_factorial_le_exp (c * x) (by positivity) 3
  have hE : 0 < Real.exp (c * x) := Real.exp_pos _
  have hc3 : 0 < c ^ 3 := by positivity
  have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3] at h
  rw [neg_mul, Real.exp_neg, mul_inv_le_iff₀ hE, div_mul_eq_mul_div, le_div_iff₀ hc3]
  nlinarith [mul_pow c x 3]

theorem cube_mul_exp_le {x : ℝ} (hx : 0 ≤ x) : x ^ 3 * Real.exp (-π * x) ≤ 6 / π ^ 3 :=
  cube_mul_exp_le' Real.pi_pos hx

/-- **The profile bound**: `|φ(v)| ≤ (2π² + 3π) e^{−|v|}` for every `v`. -/
theorem abs_φ_le (v : ℝ) : |φ v| ≤ Mφ * Real.exp (-|v|) := by
  have hM : 0 ≤ Mφ := Mφ_pos.le
  unfold φ
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have hpoly : |2 * π ^ 2 * Real.exp (4 * v) - 3 * π * Real.exp (2 * v)| ≤
      2 * π ^ 2 * Real.exp (4 * v) + 3 * π * Real.exp (2 * v) := by
    calc |2 * π ^ 2 * Real.exp (4 * v) - 3 * π * Real.exp (2 * v)|
        ≤ |2 * π ^ 2 * Real.exp (4 * v)| + |3 * π * Real.exp (2 * v)| := abs_sub _ _
      _ = 2 * π ^ 2 * Real.exp (4 * v) + 3 * π * Real.exp (2 * v) := by
          rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rcases le_or_gt v 0 with hv | hv
  · rw [abs_of_nonpos hv, neg_neg]
    have hE : Real.exp (-π * Real.exp (2 * v)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [Real.exp_pos (2 * v), Real.pi_pos]
    have h4 : Real.exp (4 * v) ≤ Real.exp (2 * v) := Real.exp_le_exp.mpr (by linarith)
    have h52 : Real.exp (v / 2) * Real.exp (2 * v) ≤ Real.exp v := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    calc Real.exp (v / 2) * |2 * π ^ 2 * Real.exp (4 * v) - 3 * π * Real.exp (2 * v)| *
          Real.exp (-π * Real.exp (2 * v))
        ≤ Real.exp (v / 2) * (2 * π ^ 2 * Real.exp (4 * v) + 3 * π * Real.exp (2 * v)) * 1 := by
          gcongr
      _ ≤ Real.exp (v / 2) * (2 * π ^ 2 * Real.exp (2 * v) + 3 * π * Real.exp (2 * v)) * 1 := by
          gcongr
      _ = Mφ * (Real.exp (v / 2) * Real.exp (2 * v)) := by
          unfold Mφ
          ring
      _ ≤ Mφ * Real.exp v := by gcongr
  · rw [abs_of_pos hv]
    set x := Real.exp (2 * v) with hx
    have hx1 : 1 ≤ x := by
      rw [hx, Real.one_le_exp_iff]
      linarith
    have hx0 : 0 < x := by linarith
    have h4 : Real.exp (4 * v) = x ^ 2 := by
      rw [hx, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hhalf : Real.exp (v / 2) * Real.exp v ≤ x := by
      rw [← Real.exp_add, hx]
      exact Real.exp_le_exp.mpr (by linarith)
    have hcube := cube_mul_exp_le hx0.le
    have h6 : 6 / π ^ 3 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    rw [h4]
    have key : Real.exp (v / 2) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) * Real.exp (-π * x) *
        Real.exp v ≤ Mφ := by
      calc Real.exp (v / 2) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) * Real.exp (-π * x) * Real.exp v
          = (Real.exp (v / 2) * Real.exp v) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) *
              Real.exp (-π * x) := by ring
        _ ≤ x * (2 * π ^ 2 * x ^ 2 + 3 * π * x ^ 2) * Real.exp (-π * x) := by
            gcongr
            nlinarith [Real.pi_pos]
        _ = Mφ * (x ^ 3 * Real.exp (-π * x)) := by
            unfold Mφ
            ring
        _ ≤ Mφ * (6 / π ^ 3) := by gcongr
        _ ≤ Mφ * 1 := by gcongr
        _ = Mφ := mul_one _
    have hA : Real.exp (v / 2) * |2 * π ^ 2 * x ^ 2 - 3 * π * x| * Real.exp (-π * x) ≤
        Real.exp (v / 2) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) * Real.exp (-π * x) := by
      rw [h4] at hpoly
      gcongr
    calc Real.exp (v / 2) * |2 * π ^ 2 * x ^ 2 - 3 * π * x| * Real.exp (-π * x)
        = (Real.exp (v / 2) * |2 * π ^ 2 * x ^ 2 - 3 * π * x| * Real.exp (-π * x) * Real.exp v) *
            Real.exp (-v) := by
          rw [mul_assoc _ (Real.exp v), ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ Mφ * Real.exp (-v) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact (mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le).trans key


/-- On `v ≥ 0` the profile is doubly exponentially small: `|φ(v)| ≤ Mφ e^{−v} e^{−e^{2v}/2}`. -/
theorem abs_φ_le_of_nonneg {v : ℝ} (hv : 0 ≤ v) :
    |φ v| ≤ Mφ * Real.exp (-v) * Real.exp (-(Real.exp (2 * v) / 2)) := by
  have hM : 0 ≤ Mφ := Mφ_pos.le
  unfold φ
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  set x := Real.exp (2 * v) with hx
  have hx1 : 1 ≤ x := by
    rw [hx, Real.one_le_exp_iff]
    linarith
  have hx0 : 0 < x := by linarith
  have h4 : Real.exp (4 * v) = x ^ 2 := by
    rw [hx, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpoly : |2 * π ^ 2 * x ^ 2 - 3 * π * x| ≤ 2 * π ^ 2 * x ^ 2 + 3 * π * x := by
    calc |2 * π ^ 2 * x ^ 2 - 3 * π * x| ≤ |2 * π ^ 2 * x ^ 2| + |3 * π * x| := abs_sub _ _
      _ = 2 * π ^ 2 * x ^ 2 + 3 * π * x := by
          rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hhalf : Real.exp (v / 2) * Real.exp v ≤ x := by
    rw [← Real.exp_add, hx]
    exact Real.exp_le_exp.mpr (by linarith)
  have hc : 0 < π - 1 / 2 := by linarith [Real.pi_gt_three]
  have hcube := cube_mul_exp_le' hc hx0.le
  have h6 : 6 / (π - 1 / 2) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hsplit : Real.exp (-π * x) = Real.exp (-(π - 1 / 2) * x) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h4, hsplit]
  have key : Real.exp (v / 2) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) * Real.exp (-(π - 1 / 2) * x) *
      Real.exp v ≤ Mφ := by
    calc Real.exp (v / 2) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) * Real.exp (-(π - 1 / 2) * x) *
          Real.exp v
        = (Real.exp (v / 2) * Real.exp v) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) *
            Real.exp (-(π - 1 / 2) * x) := by ring
      _ ≤ x * (2 * π ^ 2 * x ^ 2 + 3 * π * x ^ 2) * Real.exp (-(π - 1 / 2) * x) := by
          gcongr
          nlinarith [Real.pi_pos]
      _ = Mφ * (x ^ 3 * Real.exp (-(π - 1 / 2) * x)) := by
          unfold Mφ
          ring
      _ ≤ Mφ * (6 / (π - 1 / 2) ^ 3) := by gcongr
      _ ≤ Mφ * 1 := by gcongr
      _ = Mφ := mul_one _
  have hA : Real.exp (v / 2) * |2 * π ^ 2 * x ^ 2 - 3 * π * x| *
      (Real.exp (-(π - 1 / 2) * x) * Real.exp (-(x / 2))) ≤
      (Real.exp (v / 2) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) * Real.exp (-(π - 1 / 2) * x)) *
        Real.exp (-(x / 2)) := by
    rw [← mul_assoc]
    gcongr
  calc Real.exp (v / 2) * |2 * π ^ 2 * x ^ 2 - 3 * π * x| *
        (Real.exp (-(π - 1 / 2) * x) * Real.exp (-(x / 2)))
      ≤ (Real.exp (v / 2) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) * Real.exp (-(π - 1 / 2) * x)) *
          Real.exp (-(x / 2)) := hA
    _ = ((Real.exp (v / 2) * (2 * π ^ 2 * x ^ 2 + 3 * π * x) * Real.exp (-(π - 1 / 2) * x) *
          Real.exp v) * Real.exp (-v)) * Real.exp (-(x / 2)) := by
        rw [mul_assoc _ (Real.exp v), ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ (Mφ * Real.exp (-v)) * Real.exp (-(x / 2)) := by gcongr

/-- `log² x ≤ 4x` for `x ≥ 1`. -/
theorem log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have hx0 : 0 ≤ x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have h1 := Real.log_le_sub_one_of_pos hsx
  rw [Real.log_sqrt hx0] at h1
  have h2 : Real.log x ≤ 2 * Real.sqrt x := by linarith
  have h3 := Real.sq_sqrt hx0
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have := mul_le_mul h2 h2 hl (by positivity)
  nlinarith

/-! ## The flow's Gaussian dominates every event -/

/-- `c |u| ≤ (t/2) u² + c²/(2t)` for `t > 0`, `c ≥ 0`. -/
theorem lin_le_sq {t c : ℝ} (ht : 0 < t) (_hc : 0 ≤ c) (u : ℝ) :
    c * |u| ≤ t / 2 * u ^ 2 + c ^ 2 / (2 * t) := by
  have h := sq_nonneg (t * |u| - c)
  have hu := sq_abs u
  have h2t : 0 < 2 * t := by positivity
  rw [← sub_nonneg]
  have : t / 2 * u ^ 2 + c ^ 2 / (2 * t) - c * |u| = (t * |u| - c) ^ 2 / (2 * t) := by
    field_simp
    nlinarith [hu]
  rw [this]
  positivity

/-- The event constant `K(t, z) = (2π² + 3π) e^{(|Re z − ½| + 1)²/(2t)} √(2π/t)`. -/
def K (t : ℝ) (z : ℂ) : ℝ :=
  Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) * √(π / (t / 2))

theorem K_nonneg (t : ℝ) (z : ℂ) : 0 ≤ K t z := by
  unfold K
  have := Mφ_pos
  positivity

/-- **The pointwise bound**: for `t > 0` and `n ≠ 0`,
`‖flowedTerm t z n u‖ ≤ M e^{(|a|+1)²/(2t)} |n|^{−3/2} e^{−(t/2) u²}` with `a = Re z − ½`. -/
theorem norm_flowedTerm_le {t : ℝ} (ht : 0 < t) (z : ℂ) {n : ℤ} (hn : n ≠ 0) (u : ℝ) :
    ‖flowedTerm t z n u‖ ≤
      Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) *
        Real.exp (-(t / 2) * u ^ 2) := by
  have hM : 0 ≤ Mφ := Mφ_pos.le
  have hna : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  set L : ℝ := Real.log |(n : ℝ)| with hL
  set a : ℝ := z.re - 1 / 2 with ha
  rw [norm_flowedTerm, norm_lapTerm_eq]
  have hev : Real.exp (u / 2) * |Ψterm' (-1) n (Real.exp (2 * u))| =
      |(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |φ (u + L)| := by
    rw [← abs_of_pos (Real.exp_pos (u / 2)), ← abs_mul, event_eq hn, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  rw [hev]
  -- `e^{−|u+L|} ≤ e^{−L} e^{|u|}` and `e^{−L} = |n|⁻¹`
  have hLpos : 0 ≤ L := by
    rw [hL]
    exact Real.log_nonneg (by exact_mod_cast Int.one_le_abs hn)
  have htri : L ≤ |u + L| + |u| := by
    have := abs_sub (u + L) u
    rw [add_sub_cancel_left, abs_of_nonneg hLpos] at this
    exact this
  have hφ : |φ (u + L)| ≤ Mφ * (|(n : ℝ)|⁻¹ * Real.exp |u|) := by
    calc |φ (u + L)| ≤ Mφ * Real.exp (-|u + L|) := abs_φ_le _
      _ ≤ Mφ * (Real.exp (-L) * Real.exp |u|) := by
          rw [← Real.exp_add]
          gcongr
          linarith
      _ = Mφ * (|(n : ℝ)|⁻¹ * Real.exp |u|) := by
          rw [hL, Real.exp_neg, Real.exp_log hna]
  have hpow : |(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |(n : ℝ)|⁻¹ = |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hna]
    norm_num
  -- the exponent: `−t u² + a u + |u| ≤ (|a|+1)²/(2t) − (t/2) u²`
  have hexp : Real.exp (-t * u ^ 2) * Real.exp (a * u) * Real.exp |u| ≤
      Real.exp ((|a| + 1) ^ 2 / (2 * t)) * Real.exp (-(t / 2) * u ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : a * u ≤ |a| * |u| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 := lin_le_sq ht (by positivity : (0 : ℝ) ≤ |a| + 1) u
    nlinarith
  calc Real.exp (-t * u ^ 2) * (Real.exp (a * u) * (|(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |φ (u + L)|))
      ≤ Real.exp (-t * u ^ 2) * (Real.exp (a * u) *
          (|(n : ℝ)| ^ (-(1 / 2 : ℝ)) * (Mφ * (|(n : ℝ)|⁻¹ * Real.exp |u|)))) := by gcongr
    _ = Mφ * (|(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |(n : ℝ)|⁻¹) *
          (Real.exp (-t * u ^ 2) * Real.exp (a * u) * Real.exp |u|) := by ring
    _ ≤ Mφ * (|(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |(n : ℝ)|⁻¹) *
          (Real.exp ((|a| + 1) ^ 2 / (2 * t)) * Real.exp (-(t / 2) * u ^ 2)) := by
        gcongr
    _ = Mφ * Real.exp ((|a| + 1) ^ 2 / (2 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(t / 2) * u ^ 2) := by
        rw [hpow]
        ring

/-- Every flowed event is integrable on the descent side. -/
theorem integrable_flowedTerm {t : ℝ} (ht : 0 < t) (z : ℂ) (n : ℤ) :
    Integrable (flowedTerm t z n) := by
  by_cases hn : n = 0
  · subst hn
    have : flowedTerm t z 0 = fun _ => 0 := by
      funext u
      unfold flowedTerm
      rw [lapTerm_zero, mul_zero]
    rw [this]
    exact integrable_zero _ _ _
  · have hg := (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < t / 2)).const_mul
      (Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)))
    exact hg.mono' (continuous_flowedTerm t z n).aestronglyMeasurable
      (Eventually.of_forall fun u => norm_flowedTerm_le ht z hn u)

/-- **The event's norm integral is `O(|n|^{−3/2})`.** -/
theorem integral_norm_flowedTerm_le {t : ℝ} (ht : 0 < t) (z : ℂ) {n : ℤ} (hn : n ≠ 0) :
    ∫ u : ℝ, ‖flowedTerm t z n u‖ ≤ K t z * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  set c : ℝ := Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ))
    with hc
  calc ∫ u : ℝ, ‖flowedTerm t z n u‖ ≤ ∫ u : ℝ, c * Real.exp (-(t / 2) * u ^ 2) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
          ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < t / 2)).const_mul c)
        exact Eventually.of_forall fun u => norm_flowedTerm_le ht z hn u
    _ = c * ∫ u : ℝ, Real.exp (-(t / 2) * u ^ 2) := integral_const_mul c _
    _ = c * √(π / (t / 2)) := by rw [integral_gaussian]
    _ = K t z * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
        rw [hc]
        unfold K
        ring

/-- **The split bound**: on `u ≤ −L/2` the flow's Gaussian is at most `e^{−tL²/8}` and the profile
is bounded; on `u ≥ −L/2` the profile is at most `e^{−|n|/2}` times the earlier bound
(`L = log |n|`). -/
theorem norm_flowedTerm_le_split {t : ℝ} (ht : 0 < t) (z : ℂ) {n : ℤ} (hn : n ≠ 0) (u : ℝ) :
    ‖flowedTerm t z n u‖ ≤
      Mφ * Real.exp (|z.re - 1 / 2| ^ 2 / t) * Real.exp (-(t / 8) * Real.log |(n : ℝ)| ^ 2) *
          Real.exp (-(t / 4) * u ^ 2) +
        Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) *
          (|(n : ℝ)| ^ (-(3 / 2 : ℝ)) * Real.exp (-(|(n : ℝ)| / 2))) *
          Real.exp (-(t / 2) * u ^ 2) := by
  have hM : 0 ≤ Mφ := Mφ_pos.le
  have hna : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hn1 : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  set L : ℝ := Real.log |(n : ℝ)| with hL
  set a : ℝ := z.re - 1 / 2 with ha
  have hLpos : 0 ≤ L := Real.log_nonneg hn1
  rw [norm_flowedTerm, norm_lapTerm_eq]
  have hev : Real.exp (u / 2) * |Ψterm' (-1) n (Real.exp (2 * u))| =
      |(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |φ (u + L)| := by
    rw [← abs_of_pos (Real.exp_pos (u / 2)), ← abs_mul, event_eq hn, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  rw [hev]
  have hT1 : 0 ≤ Mφ * Real.exp (|a| ^ 2 / t) * Real.exp (-(t / 8) * L ^ 2) *
      Real.exp (-(t / 4) * u ^ 2) := by positivity
  have hT2 : 0 ≤ Mφ * Real.exp ((|a| + 1) ^ 2 / (2 * t)) *
      (|(n : ℝ)| ^ (-(3 / 2 : ℝ)) * Real.exp (-(|(n : ℝ)| / 2))) *
      Real.exp (-(t / 2) * u ^ 2) := by positivity
  rcases le_or_gt u (-(L / 2)) with hu | hu
  · refine le_trans ?_ (le_add_of_nonneg_right hT2)
    have hφ : |φ (u + L)| ≤ Mφ := by
      calc |φ (u + L)| ≤ Mφ * Real.exp (-|u + L|) := abs_φ_le _
        _ ≤ Mφ * 1 := by
            gcongr
            rw [Real.exp_le_one_iff]
            linarith [abs_nonneg (u + L)]
        _ = Mφ := mul_one _
    have hpow : |(n : ℝ)| ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
    have hu2 : L ^ 2 / 4 ≤ u ^ 2 := by nlinarith
    have hexp : Real.exp (-t * u ^ 2) * Real.exp (a * u) ≤
        Real.exp (|a| ^ 2 / t) * Real.exp (-(t / 8) * L ^ 2) * Real.exp (-(t / 4) * u ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : a * u ≤ |a| * |u| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h2 := lin_le_sq (by positivity : (0 : ℝ) < t / 2) (abs_nonneg a) u
      have h3 : t / 2 / 2 * u ^ 2 + |a| ^ 2 / (2 * (t / 2)) = t / 4 * u ^ 2 + |a| ^ 2 / t := by
        field_simp
        ring
      rw [h3] at h2
      nlinarith
    calc Real.exp (-t * u ^ 2) * (Real.exp (a * u) * (|(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |φ (u + L)|))
        ≤ Real.exp (-t * u ^ 2) * (Real.exp (a * u) * (1 * Mφ)) := by gcongr
      _ = Mφ * (Real.exp (-t * u ^ 2) * Real.exp (a * u)) := by ring
      _ ≤ Mφ * (Real.exp (|a| ^ 2 / t) * Real.exp (-(t / 8) * L ^ 2) *
            Real.exp (-(t / 4) * u ^ 2)) := by gcongr
      _ = Mφ * Real.exp (|a| ^ 2 / t) * Real.exp (-(t / 8) * L ^ 2) *
            Real.exp (-(t / 4) * u ^ 2) := by ring
  · refine le_trans ?_ (le_add_of_nonneg_left hT1)
    have hv : 0 ≤ u + L := by linarith
    have h1 : Real.exp (-(u + L)) ≤ Real.exp (-L) * Real.exp |u| := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [neg_abs_le u]
    have h2 : Real.exp (-(Real.exp (2 * (u + L)) / 2)) ≤ Real.exp (-(|(n : ℝ)| / 2)) := by
      apply Real.exp_le_exp.mpr
      have : |(n : ℝ)| ≤ Real.exp (2 * (u + L)) := by
        calc |(n : ℝ)| = Real.exp L := by rw [hL, Real.exp_log hna]
          _ ≤ Real.exp (2 * (u + L)) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hφ : |φ (u + L)| ≤ Mφ * (|(n : ℝ)|⁻¹ * Real.exp |u|) * Real.exp (-(|(n : ℝ)| / 2)) := by
      calc |φ (u + L)| ≤ Mφ * Real.exp (-(u + L)) * Real.exp (-(Real.exp (2 * (u + L)) / 2)) :=
            abs_φ_le_of_nonneg hv
        _ ≤ Mφ * (Real.exp (-L) * Real.exp |u|) * Real.exp (-(|(n : ℝ)| / 2)) := by gcongr
        _ = Mφ * (|(n : ℝ)|⁻¹ * Real.exp |u|) * Real.exp (-(|(n : ℝ)| / 2)) := by
            rw [hL, Real.exp_neg, Real.exp_log hna]
    have hpow : |(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |(n : ℝ)|⁻¹ = |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hna]
      norm_num
    have hexp : Real.exp (-t * u ^ 2) * Real.exp (a * u) * Real.exp |u| ≤
        Real.exp ((|a| + 1) ^ 2 / (2 * t)) * Real.exp (-(t / 2) * u ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : a * u ≤ |a| * |u| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h2 := lin_le_sq ht (by positivity : (0 : ℝ) ≤ |a| + 1) u
      nlinarith
    calc Real.exp (-t * u ^ 2) * (Real.exp (a * u) * (|(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |φ (u + L)|))
        ≤ Real.exp (-t * u ^ 2) * (Real.exp (a * u) * (|(n : ℝ)| ^ (-(1 / 2 : ℝ)) *
            (Mφ * (|(n : ℝ)|⁻¹ * Real.exp |u|) * Real.exp (-(|(n : ℝ)| / 2))))) := by gcongr
      _ = Mφ * (|(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |(n : ℝ)|⁻¹) * Real.exp (-(|(n : ℝ)| / 2)) *
            (Real.exp (-t * u ^ 2) * Real.exp (a * u) * Real.exp |u|) := by ring
      _ ≤ Mφ * (|(n : ℝ)| ^ (-(1 / 2 : ℝ)) * |(n : ℝ)|⁻¹) * Real.exp (-(|(n : ℝ)| / 2)) *
            (Real.exp ((|a| + 1) ^ 2 / (2 * t)) * Real.exp (-(t / 2) * u ^ 2)) := by gcongr
      _ = Mφ * Real.exp ((|a| + 1) ^ 2 / (2 * t)) *
            (|(n : ℝ)| ^ (-(3 / 2 : ℝ)) * Real.exp (-(|(n : ℝ)| / 2))) *
            Real.exp (-(t / 2) * u ^ 2) := by
          rw [hpow]
          ring

/-- The Gaussian-weight constant `K₂(t, z)`. -/
def K₂ (t : ℝ) (z : ℂ) : ℝ :=
  Mφ * Real.exp (|z.re - 1 / 2| ^ 2 / t) * √(π / (t / 4)) +
    Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) * √(π / (t / 2))

/-- **The Gaussian weight in `n`**: the event's norm integral is at most
`K₂(t, z) e^{−(min t 1 / 8) (log |n|)²}`. -/
theorem integral_norm_flowedTerm_le_gaussian {t : ℝ} (ht : 0 < t) (z : ℂ) {n : ℤ} (hn : n ≠ 0) :
    ∫ u : ℝ, ‖flowedTerm t z n u‖ ≤
      K₂ t z * Real.exp (-(min t 1 / 8) * Real.log |(n : ℝ)| ^ 2) := by
  have hM : 0 ≤ Mφ := Mφ_pos.le
  have hn1 : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  set L : ℝ := Real.log |(n : ℝ)| with hL
  set A : ℝ := Mφ * Real.exp (|z.re - 1 / 2| ^ 2 / t) * Real.exp (-(t / 8) * L ^ 2) with hA
  set B : ℝ := Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) *
    (|(n : ℝ)| ^ (-(3 / 2 : ℝ)) * Real.exp (-(|(n : ℝ)| / 2))) with hB
  have hiA := (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < t / 4)).const_mul A
  have hiB := (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < t / 2)).const_mul B
  have hint : ∫ u : ℝ, ‖flowedTerm t z n u‖ ≤ A * √(π / (t / 4)) + B * √(π / (t / 2)) := by
    calc ∫ u : ℝ, ‖flowedTerm t z n u‖
        ≤ ∫ u : ℝ, (A * Real.exp (-(t / 4) * u ^ 2) + B * Real.exp (-(t / 2) * u ^ 2)) := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) (hiA.add hiB)
          exact Eventually.of_forall fun u => norm_flowedTerm_le_split ht z hn u
      _ = A * (∫ u : ℝ, Real.exp (-(t / 4) * u ^ 2)) + B * (∫ u : ℝ, Real.exp (-(t / 2) * u ^ 2)) := by
          rw [integral_add hiA hiB, integral_const_mul, integral_const_mul]
      _ = A * √(π / (t / 4)) + B * √(π / (t / 2)) := by rw [integral_gaussian, integral_gaussian]
  have hL2 : L ^ 2 ≤ 4 * |(n : ℝ)| := log_sq_le_four_mul hn1
  have hm : min t 1 ≤ t := min_le_left _ _
  have hm1 : min t 1 ≤ 1 := min_le_right _ _
  have hA' : Real.exp (-(t / 8) * L ^ 2) ≤ Real.exp (-(min t 1 / 8) * L ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg L)])
  have hB' : |(n : ℝ)| ^ (-(3 / 2 : ℝ)) * Real.exp (-(|(n : ℝ)| / 2)) ≤
      Real.exp (-(min t 1 / 8) * L ^ 2) := by
    calc |(n : ℝ)| ^ (-(3 / 2 : ℝ)) * Real.exp (-(|(n : ℝ)| / 2))
        ≤ 1 * Real.exp (-(|(n : ℝ)| / 2)) := by
          gcongr
          exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
      _ = Real.exp (-(|(n : ℝ)| / 2)) := one_mul _
      _ ≤ Real.exp (-(min t 1 / 8) * L ^ 2) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (sq_nonneg L)])
  calc ∫ u : ℝ, ‖flowedTerm t z n u‖ ≤ A * √(π / (t / 4)) + B * √(π / (t / 2)) := hint
    _ ≤ (Mφ * Real.exp (|z.re - 1 / 2| ^ 2 / t) * Real.exp (-(min t 1 / 8) * L ^ 2)) *
          √(π / (t / 4)) +
        (Mφ * Real.exp ((|z.re - 1 / 2| + 1) ^ 2 / (2 * t)) *
          Real.exp (-(min t 1 / 8) * L ^ 2)) * √(π / (t / 2)) := by
        rw [hA, hB]
        gcongr
    _ = K₂ t z * Real.exp (-(min t 1 / 8) * L ^ 2) := by
        unfold K₂
        ring

/-- The comb's `n`-th term carries the Gaussian weight. -/
theorem norm_integral_flowedTerm_le_gaussian {t : ℝ} (ht : 0 < t) (z : ℂ) {n : ℤ} (hn : n ≠ 0) :
    ‖∫ u : ℝ, flowedTerm t z n u‖ ≤
      K₂ t z * Real.exp (-(min t 1 / 8) * Real.log |(n : ℝ)| ^ 2) :=
  (norm_integral_le_integral_norm _).trans (integral_norm_flowedTerm_le_gaussian ht z hn)

/-- **Absolute convergence of the descent comb at every `z`.** -/
theorem summable_norm_integral_flowedTerm {t : ℝ} (ht : 0 < t) (z : ℂ) :
    Summable (fun n : ℤ => ‖∫ u : ℝ, flowedTerm t z n u‖) := by
  refine ((summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2)).mul_left (K t z)).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp [flowedTerm, lapTerm_zero]
  · exact (norm_integral_le_integral_norm _).trans (integral_norm_flowedTerm_le ht z hn)

/-- **RT1, the descent comb everywhere**: for every `t > 0` and every `z`, the flowed integer
events sum to `heatE t ξ (z)`. -/
theorem hasSum_flowedTerm_of_pos {t : ℝ} (ht : 0 < t) (z : ℂ) :
    HasSum (fun n : ℤ => ∫ u : ℝ, flowedTerm t z n u) (heatE t riemannXi z) := by
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (flowedTerm t z n) volume :=
    fun n => (continuous_flowedTerm t z n).aestronglyMeasurable
  have hbound : ∀ n : ℤ, ∫ u : ℝ, ‖flowedTerm t z n u‖ ≤ K t z * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [flowedTerm, lapTerm_zero]
    · exact integral_norm_flowedTerm_le ht z hn
  have hfin : ∑' n : ℤ, ∫⁻ u : ℝ, ‖flowedTerm t z n u‖ₑ ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (b := ∑' n : ℤ, ENNReal.ofReal (K t z * |(n : ℝ)| ^ (-(3 / 2 : ℝ))))
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => ?_)
        ((summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2)).mul_left (K t z))]
      · exact ENNReal.ofReal_ne_top
      · exact mul_nonneg (K_nonneg t z) (Real.rpow_nonneg (abs_nonneg _) _)
    · apply ENNReal.tsum_le_tsum
      intro n
      rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_flowedTerm ht z n)]
      exact ENNReal.ofReal_le_ofReal (hbound n)
  have hsum : Summable (fun n : ℤ => ∫ u : ℝ, flowedTerm t z n u) :=
    (summable_norm_integral_flowedTerm ht z).of_norm
  have h := integral_tsum hmeas hfin
  have hkernel : heatE t riemannXi z = ∫ u : ℝ, ∑' n : ℤ, flowedTerm t z n u := by
    rw [heatE_riemannXi]
    apply integral_congr_ae
    refine Eventually.of_forall fun u => ?_
    show flowLap t z u = ∑' n : ℤ, flowedTerm t z n u
    unfold flowLap flowedTerm
    rw [tsum_mul_left, (hasSum_lapTerm z u).tsum_eq]
  rw [hkernel, h]
  exact hsum.hasSum

/-- The comb as a sum. -/
theorem heatE_eq_tsum_flowedTerm {t : ℝ} (ht : 0 < t) (z : ℂ) :
    heatE t riemannXi z = ∑' n : ℤ, ∫ u : ℝ, flowedTerm t z n u :=
  (hasSum_flowedTerm_of_pos ht z).tsum_eq.symm

end Soma.Holonics.RH.DescentComb
