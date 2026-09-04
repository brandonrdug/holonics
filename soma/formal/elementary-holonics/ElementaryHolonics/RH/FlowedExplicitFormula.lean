import Mathlib
import ElementaryHolonics.RH.HeatKernelPhi
import ElementaryHolonics.RH.HeatFlowBinding
import ElementaryHolonics.RH.FosterClassHeatFlow

/-!
# FT5: the flowed integer events, the seam where the Euler side meets the flow

The kernel is `Φ(u) = Σ_{n ∈ ℤ} |n|^{−1/2} φ(u + log |n|)` with one Gamma-type profile
`φ(v) = e^{v/2} (2π² e^{4v} − 3π e^{2v}) e^{−π e^{2v}}` translated to the integer event `log n`, and
the flow multiplies it by `e^{−t u²}`. In the event's own coordinate `v = u + log n`,
`e^{−t(v − log n)²} = e^{−t v²} · n^{2tv} · flowWeight (−t) n` (`HeatFlowBinding`): the flow
weight is the non-multiplicative factor, with its binding defect on composites.

**Returned.** For repository time `t ≥ 0` (standard `τ = −t ≤ 0`) and `Re z > 1`, the flowed
integer events sum to `heatE t ξ (z)`: the integer side of the flowed explicit formula, exact,
and the zero side is the Foster form of `heatE t ξ` (`FosterClassHadamard`, through the class
instance). **The exact obstruction**: for `t < 0` (standard `τ > 0`, the side on which pairs
descend), every flowed integer event with `n ≠ 0` has infinite norm integral — the integer side
does not exist termwise, only the kernel integral does. Every theorem is discharged with no
`sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FlowedExplicitFormula

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatKernelPhi
open Soma.Holonics.RH.HeatFlowBinding

/-! ## The event profile -/

/-- The one Gamma-type profile of the integer events. -/
def φ (v : ℝ) : ℝ := Real.exp (v / 2) * (2 * π ^ 2 * Real.exp (4 * v) - 3 * π * Real.exp (2 * v)) *
  Real.exp (-π * Real.exp (2 * v))

/-- **The `n`-th event is the profile translated to `log |n|` at half density.** -/
theorem event_eq {n : ℤ} (hn : n ≠ 0) (u : ℝ) :
    Real.exp (u / 2) * Ψterm' (-1) n (Real.exp (2 * u)) =
      (|(n : ℝ)|) ^ (-(1 / 2 : ℝ)) * φ (u + Real.log |(n : ℝ)|) := by
  have ha : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  set a : ℝ := |(n : ℝ)| with hadef
  have hn2 : (n : ℝ) ^ 2 = a ^ 2 := (sq_abs _).symm
  have hn4 : (n : ℝ) ^ 4 = a ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hn2, ← pow_mul]
  have hL : Real.exp (Real.log a) = a := Real.exp_log ha
  have h2 : Real.exp (2 * (u + Real.log a)) = Real.exp (2 * u) * a ^ 2 := by
    rw [mul_add, Real.exp_add, show (2 : ℝ) * Real.log a = (2 : ℕ) * Real.log a by norm_num,
      Real.exp_nat_mul, hL]
  have h4 : Real.exp (4 * (u + Real.log a)) = Real.exp (4 * u) * a ^ 4 := by
    rw [mul_add, Real.exp_add, show (4 : ℝ) * Real.log a = (4 : ℕ) * Real.log a by norm_num,
      Real.exp_nat_mul, hL]
  have hhalf : Real.exp ((u + Real.log a) / 2) = Real.exp (u / 2) * a ^ (1 / 2 : ℝ) := by
    rw [add_div, Real.exp_add, Real.rpow_def_of_pos ha]
    congr 2
    ring
  have hpow : a ^ (-(1 / 2 : ℝ)) * a ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add ha]
    norm_num
  unfold Ψterm' φ
  rw [h2, h4, hhalf, hn2, hn4]
  have e4 : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e4]
  have hE : Real.exp (-π * (Real.exp (2 * u) * a ^ 2)) = Real.exp (-π * a ^ 2 * Real.exp (2 * u)) := by
    congr 1
    ring
  rw [hE]
  linear_combination (-(Real.exp (u / 2) * (2 * π ^ 2 * (Real.exp (2 * u) ^ 2 * a ^ 4) -
    3 * π * (Real.exp (2 * u) * a ^ 2)) * Real.exp (-π * a ^ 2 * Real.exp (2 * u)))) * hpow

/-- **The flow weight in the event's own coordinate**: `e^{−t(v − log n)²}` is the free Gaussian
times the running power `n^{2tv}` times the flow weight `flowWeight (−t) n`. -/
theorem flow_weight_split (t v : ℝ) {n : ℝ} (hn : 0 < n) :
    Real.exp (-t * (v - Real.log n) ^ 2) =
      Real.exp (-t * v ^ 2) * n ^ (-(2 * (-t) * v)) * flowWeight (-t) n :=
  flow_factor_split (-t) v hn

/-! ## The flowed events sum to the flow on the convergent side -/

/-- The `n`-th flowed event integrand. -/
def flowedTerm (t : ℝ) (z : ℂ) (n : ℤ) (u : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ) * (u : ℂ) ^ 2) * lapTerm (-1) z n u

theorem norm_flowedTerm (t : ℝ) (z : ℂ) (n : ℤ) (u : ℝ) :
    ‖flowedTerm t z n u‖ = Real.exp (-t * u ^ 2) * ‖lapTerm (-1) z n u‖ := by
  unfold flowedTerm
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, ← Complex.ofReal_pow]

theorem continuous_flowedTerm (t : ℝ) (z : ℂ) (n : ℤ) : Continuous (flowedTerm t z n) :=
  (Complex.continuous_exp.comp (by fun_prop)).mul (continuous_lapTerm (-1) z n)

/-- **FT5, the integer side**: for `t ≥ 0` and `Re z > 1`, the flowed integer events sum to the
flow of `ξ`. -/
theorem hasSum_flowedTerm {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 1 < z.re) :
    HasSum (fun n : ℤ => ∫ u : ℝ, flowedTerm t z n u) (heatE t riemannXi z) := by
  have hmeas : ∀ n : ℤ, AEStronglyMeasurable (flowedTerm t z n) volume :=
    fun n => (continuous_flowedTerm t z n).aestronglyMeasurable
  have hle : ∀ n u, ‖flowedTerm t z n u‖ₑ ≤ ‖lapTerm (-1) z n u‖ₑ := by
    intro n u
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_flowedTerm]
    apply ENNReal.ofReal_le_ofReal
    have h1 : Real.exp (-t * u ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg u]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hfin : ∑' n : ℤ, ∫⁻ u : ℝ, ‖flowedTerm t z n u‖ₑ ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ∑' n : ℤ, ENNReal.ofReal ((termValue 1 (z.re : ℂ) n).re))
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => ?_) (summable_termValue_one_re hz)]
      · exact ENNReal.ofReal_ne_top
      · by_cases hn : n = 0
        · subst hn
          unfold termValue
          simp
        · rw [termValue_one_re_eq hz hn]
          exact mul_nonneg (Cmaj_nonneg hz) (Real.rpow_nonneg (abs_nonneg _) _)
    · apply ENNReal.tsum_le_tsum
      intro n
      exact (lintegral_mono (hle n)).trans (lintegral_lapTerm_le hz n)
  have hsum : Summable (fun n : ℤ => ∫ u : ℝ, flowedTerm t z n u) := by
    refine (summable_termValue_one_re hz).of_norm_bounded fun n => ?_
    calc ‖∫ u : ℝ, flowedTerm t z n u‖ ≤ ∫ u : ℝ, ‖flowedTerm t z n u‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ u : ℝ, (lapTerm 1 (z.re : ℂ) n u).re := by
          have hs' : 1 < ((z.re : ℝ) : ℂ).re := by simpa using hz
          apply integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
            (integrable_lapTerm 1 hs' n).re
          refine Eventually.of_forall fun u => ?_
          show ‖flowedTerm t z n u‖ ≤ (lapTerm 1 (z.re : ℂ) n u).re
          rw [norm_flowedTerm]
          have h1 : Real.exp (-t * u ^ 2) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            nlinarith [sq_nonneg u]
          exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans (norm_lapTerm_le z n u)
      _ ≤ (termValue 1 (z.re : ℂ) n).re := by
          have hs' : 1 < ((z.re : ℝ) : ℂ).re := by simpa using hz
          have hint := integrable_lapTerm 1 hs' n
          by_cases hn : n = 0
          · subst hn
            simp only [lapTerm_zero, Complex.zero_re, integral_zero]
            unfold termValue
            simp
          · have := Complex.reCLM.integral_comp_comm hint
            simp only [Complex.reCLM_apply] at this
            rw [this, integral_lapTerm 1 hs' hn]
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

/-! ## The zero side -/

/-- **FT5, the zero side**: the Foster form of `heatE t ξ` at every time, off its zeros. -/
theorem foster_form_heatE (t : ℝ) {z : ℂ} (hz : heatE t riemannXi z ≠ 0) :
    logDeriv (heatE t riemannXi) z =
      ∑' u : Soma.Holonics.RH.FosterClassCount.Zero (heatE t riemannXi),
        ((Soma.Holonics.RH.FosterClassCount.mult (heatE t riemannXi) (u : ℂ)).toNat : ℂ) *
          ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - ((u : ℂ) - 1 / 2) ^ 2)) :=
  Soma.Holonics.RH.FosterClassHadamard.foster_form (f := heatE t riemannXi) hz

/-! ## The exact obstruction: the events diverge on the descent side -/

theorem norm_lapTerm_eq (z : ℂ) (n : ℤ) (u : ℝ) :
    ‖lapTerm (-1) z n u‖ = Real.exp ((z.re - 1 / 2) * u) * (Real.exp (u / 2) * |Ψterm' (-1) n (Real.exp (2 * u))|) := by
  unfold lapTerm
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  congr 2
  simp [Complex.mul_re]

/-- Near `u → −∞` the `n`-th event is at least `(3π n²/4) e^{2u}` in absolute value. -/
theorem abs_Ψterm_ge {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ 3 / (4 * π * (n : ℝ) ^ 2)) (hx2 : x ≤ Real.log 2 / (π * (n : ℝ) ^ 2)) :
    3 * π * (n : ℝ) ^ 2 / 4 * x ≤ |Ψterm' (-1) n x| := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
  unfold Ψterm'
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hE : 1 / 2 ≤ Real.exp (-π * (n : ℝ) ^ 2 * x) := by
    rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ π * (n : ℝ) ^ 2)
    rw [mul_div_cancel₀ _ (by positivity)] at this
    linarith
  have hpoly : 3 * π * (n : ℝ) ^ 2 / 2 * x ≤ |2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 + -1 * (3 * π * (n : ℝ) ^ 2 * x)| := by
    have h1 : 2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 ≤ 3 * π * (n : ℝ) ^ 2 / 2 * x := by
      have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ 2 * π ^ 2 * (n : ℝ) ^ 4 * x)
      rw [show 2 * π ^ 2 * (n : ℝ) ^ 4 * x * (3 / (4 * π * (n : ℝ) ^ 2)) = 3 * π * (n : ℝ) ^ 2 / 2 * x by
        field_simp; ring] at this
      nlinarith
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  calc 3 * π * (n : ℝ) ^ 2 / 4 * x = (3 * π * (n : ℝ) ^ 2 / 2 * x) * (1 / 2) := by ring
    _ ≤ |2 * π ^ 2 * (n : ℝ) ^ 4 * x ^ 2 + -1 * (3 * π * (n : ℝ) ^ 2 * x)| *
          Real.exp (-π * (n : ℝ) ^ 2 * x) := by
        apply mul_le_mul hpoly hE (by norm_num) (abs_nonneg _)

/-- **FT5, the obstruction**: for `t < 0` (standard `τ > 0`), the `n`-th flowed event is not
integrable — its norm integral is infinite. -/
theorem not_integrable_flowedTerm {t : ℝ} (ht : t < 0) (z : ℂ) {n : ℤ} (hn : n ≠ 0) :
    ¬ Integrable (flowedTerm t z n) := by
  intro hint
  have hfin := hint.hasFiniteIntegral
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
  set c : ℝ := 3 * π * (n : ℝ) ^ 2 / 4 with hc
  have hc0 : 0 < c := by positivity
  set x₀ : ℝ := min (3 / (4 * π * (n : ℝ) ^ 2)) (Real.log 2 / (π * (n : ℝ) ^ 2)) with hx₀
  have hx₀0 : 0 < x₀ := lt_min (by positivity) (by positivity)
  set σ : ℝ := z.re with hσ
  set M : ℝ := max (max 1 (-(Real.log x₀) / 2)) ((|σ + 2| + |Real.log c| + 1) / (-t)) with hM
  -- for `u ≤ −M`, `1 ≤ ‖flowedTerm t z n u‖`
  have hlow : ∀ u, u ≤ -M → 1 ≤ ‖flowedTerm t z n u‖ := by
    intro u hu
    have hM1 : 1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
    have hMx : -(Real.log x₀) / 2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
    have hMt : (|σ + 2| + |Real.log c| + 1) / (-t) ≤ M := le_max_right _ _
    have h2u : 2 * u ≤ Real.log x₀ := by linarith
    have hxu : Real.exp (2 * u) ≤ x₀ :=
      calc Real.exp (2 * u) ≤ Real.exp (Real.log x₀) := Real.exp_le_exp.mpr h2u
        _ = x₀ := Real.exp_log hx₀0
    have hΨ := abs_Ψterm_ge hn (Real.exp_pos (2 * u)) (hxu.trans (min_le_left _ _))
      (hxu.trans (min_le_right _ _))
    rw [norm_flowedTerm, norm_lapTerm_eq]
    -- ‖·‖ ≥ e^{−t u²} e^{(σ−½)u} e^{u/2} c e^{2u} = c e^{−t u² + (σ+2) u}
    have h1 : Real.exp (-t * u ^ 2) * (Real.exp ((σ - 1 / 2) * u) *
        (Real.exp (u / 2) * (c * Real.exp (2 * u)))) ≤
        Real.exp (-t * u ^ 2) * (Real.exp ((σ - 1 / 2) * u) *
        (Real.exp (u / 2) * |Ψterm' (-1) n (Real.exp (2 * u))|)) := by
      gcongr
    refine le_trans ?_ h1
    have e1 : Real.exp ((σ - 1 / 2) * u) * (Real.exp (u / 2) * (c * Real.exp (2 * u))) =
        c * Real.exp ((σ + 2) * u) := by
      rw [show (σ + 2) * u = (σ - 1 / 2) * u + u / 2 + 2 * u by ring, Real.exp_add, Real.exp_add]
      ring
    rw [e1]
    have hexp : Real.exp (-t * u ^ 2) * (c * Real.exp ((σ + 2) * u)) =
        Real.exp (-t * u ^ 2 + (σ + 2) * u + Real.log c) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hc0]
      ring
    rw [hexp, Real.one_le_exp_iff]
    -- with `w = −u ≥ M`: `(−t) w² − |σ+2| w − |log c| ≥ 0`
    set w : ℝ := -u with hw
    have hwM : M ≤ w := by linarith
    have hw1 : 1 ≤ w := le_trans hM1 hwM
    have hnt : 0 < -t := by linarith
    have hkey : |σ + 2| + |Real.log c| + 1 ≤ (-t) * w := by
      have := (div_le_iff₀ hnt).mp hMt
      nlinarith
    have hu' : u = -w := by rw [hw, neg_neg]
    rw [hu']
    have h2 : (σ + 2) * (-w) ≥ -(|σ + 2| * w) := by
      rw [mul_neg]
      have := mul_le_mul_of_nonneg_right (le_abs_self (σ + 2)) (by linarith : (0 : ℝ) ≤ w)
      linarith
    have h3 : Real.log c ≥ -|Real.log c| := neg_abs_le _
    have h4 : (-t) * w * w ≥ (|σ + 2| + |Real.log c| + 1) * w :=
      mul_le_mul_of_nonneg_right hkey (by linarith)
    nlinarith [abs_nonneg (σ + 2), abs_nonneg (Real.log c)]
  -- the norm integral is infinite
  have hle : ∀ u, (Iic (-M)).indicator (1 : ℝ → ENNReal) u ≤ ‖flowedTerm t z n u‖ₑ := by
    intro u
    by_cases hu : u ∈ Iic (-M)
    · rw [indicator_of_mem hu, Pi.one_apply, ← ofReal_norm_eq_enorm]
      exact ENNReal.one_le_ofReal.mpr (hlow u hu)
    · rw [indicator_of_notMem hu]
      exact bot_le
  have hbig : (⊤ : ENNReal) ≤ ∫⁻ u, ‖flowedTerm t z n u‖ₑ := by
    calc (⊤ : ENNReal) = volume (Iic (-M)) := Real.volume_Iic.symm
      _ = ∫⁻ u, (Iic (-M)).indicator (1 : ℝ → ENNReal) u :=
          (lintegral_indicator_one measurableSet_Iic).symm
      _ ≤ ∫⁻ u, ‖flowedTerm t z n u‖ₑ := lintegral_mono hle
  unfold MeasureTheory.HasFiniteIntegral at hfin
  exact absurd hfin (not_lt.mpr hbig)

end Soma.Holonics.RH.FlowedExplicitFormula
