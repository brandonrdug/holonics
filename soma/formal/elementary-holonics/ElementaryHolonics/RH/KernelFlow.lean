import Mathlib
import ElementaryHolonics.RH.HeatKernelPhi

/-!
# FT4 (iii): admissible kernels, and the flow is a semigroup at the entire face

An *admissible kernel* is a continuous `K : ℝ → ℝ` dominated, after any Gaussian and exponential
weight, by a Gaussian: `e^{a u² + b|u|} |K(u)| ≤ C e^{−u²}`. Its two-sided Laplace transform
`T_K(z) = ∫ e^{(z − ½)u} K(u) du` is entire, its derivatives are the moment transforms, and the flow
acts on it by the weight: `heatE t (T_K) = T_{e^{−t u²} K}`. The kernel `Φ` of `HeatKernelPhi` is
admissible and `ξ = T_Φ`, so `heatE t ξ = T_{e^{−t u²} Φ}`, the flow is a semigroup on `ξ`, and every
`heatE t ξ` is the transform of the even positive kernel `e^{−t u²} Φ`. Every theorem is
discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.KernelFlow

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatKernelPhi

/-- **An admissible kernel.** -/
structure Kernel where
  K : ℝ → ℝ
  cont : Continuous K
  dom : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ∃ C : ℝ, 0 ≤ C ∧
    ∀ u, Real.exp (a * u ^ 2 + b * |u|) * |K u| ≤ C * Real.exp (-u ^ 2)

namespace Kernel

variable (κ : Kernel)

/-- The Laplace integrand `e^{(s−½)u} K(u)`. -/
def lap (s : ℂ) (u : ℝ) : ℂ := Complex.exp ((s - 1 / 2) * u) * (κ.K u : ℂ)

/-- The `m`-th moment integrand. -/
def lapM (m : ℕ) (s : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ m * κ.lap s u

/-- The transform. -/
def T (s : ℂ) : ℂ := ∫ u : ℝ, κ.lap s u

/-- The `m`-th moment transform. -/
def TM (m : ℕ) (s : ℂ) : ℂ := ∫ u : ℝ, κ.lapM m s u

theorem continuous_lap (s : ℂ) : Continuous (κ.lap s) :=
  (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
    (Complex.continuous_ofReal.comp κ.cont)

theorem continuous_lapM (m : ℕ) (s : ℂ) : Continuous (κ.lapM m s) :=
  (Complex.continuous_ofReal.pow m).mul (κ.continuous_lap s)

theorem norm_lapM (m : ℕ) (s : ℂ) (u : ℝ) :
    ‖κ.lapM m s u‖ = |u| ^ m * (Real.exp ((s.re - 1 / 2) * u) * |κ.K u|) := by
  unfold lapM lap
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs]
  congr 3
  simp [Complex.mul_re]

theorem hasDerivAt_lapM (m : ℕ) (u : ℝ) (s : ℂ) :
    HasDerivAt (fun z => κ.lapM m z u) (κ.lapM (m + 1) s u) s := by
  unfold lapM lap
  have h : HasDerivAt (fun z : ℂ => (z - 1 / 2) * (u : ℂ)) ((u : ℂ)) s := by
    have := ((hasDerivAt_id' s).sub_const (1 / 2 : ℂ)).mul_const (u : ℂ)
    simpa using this
  have := ((h.cexp).mul_const ((κ.K u : ℝ) : ℂ)).const_mul ((u : ℂ) ^ m)
  refine this.congr_deriv ?_
  ring

theorem norm_lapM_le {m : ℕ} {s₀ s : ℂ} (hs : s ∈ Metric.ball s₀ 1) (u : ℝ) :
    ‖κ.lapM m s u‖ ≤ Real.exp (0 * u ^ 2 + (|s₀.re| + 3 / 2 + m) * |u|) * |κ.K u| := by
  rw [κ.norm_lapM]
  have h1 : |u| ^ m ≤ Real.exp (m * |u|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (abs_nonneg u) (by linarith [Real.add_one_le_exp |u|, abs_nonneg u]) m
  have hre : |s.re - s₀.re| < 1 := by
    have h := Complex.abs_re_le_norm (s - s₀)
    rw [Metric.mem_ball, dist_eq_norm] at hs
    rw [Complex.sub_re] at h
    linarith
  have h2 : |s.re - 1 / 2| ≤ |s₀.re| + 3 / 2 := by
    have := abs_sub (s.re) (1 / 2 : ℝ)
    have habs : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    linarith [abs_sub_abs_le_abs_sub s.re s₀.re]
  have h3 : (s.re - 1 / 2) * u ≤ (|s₀.re| + 3 / 2) * |u| := by
    calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
      _ = |s.re - 1 / 2| * |u| := abs_mul _ _
      _ ≤ (|s₀.re| + 3 / 2) * |u| := mul_le_mul_of_nonneg_right h2 (abs_nonneg u)
  have hK := abs_nonneg (κ.K u)
  calc |u| ^ m * (Real.exp ((s.re - 1 / 2) * u) * |κ.K u|)
      ≤ Real.exp (m * |u|) * (Real.exp ((|s₀.re| + 3 / 2) * |u|) * |κ.K u|) := by
        apply mul_le_mul h1 _ (by positivity) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h3) hK
    _ = Real.exp (0 * u ^ 2 + (|s₀.re| + 3 / 2 + m) * |u|) * |κ.K u| := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem integrable_gauss (C : ℝ) : Integrable (fun u : ℝ => C * Real.exp (-u ^ 2)) :=
  (integrable_exp_neg_mul_sq one_pos).const_mul C |>.congr (by
    refine Filter.Eventually.of_forall fun u => ?_
    simp)

theorem integrable_lapM (m : ℕ) (s : ℂ) : Integrable (κ.lapM m s) := by
  obtain ⟨C, hC0, hC⟩ := κ.dom 0 (|s.re| + 3 / 2 + m) le_rfl (by positivity)
  refine (integrable_gauss C).mono' (κ.continuous_lapM m s).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  exact (κ.norm_lapM_le (Metric.mem_ball_self one_pos) u).trans (hC u)

theorem integrable_lap (s : ℂ) : Integrable (κ.lap s) := by
  have h := κ.integrable_lapM 0 s
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  unfold lapM
  simp

/-- **The moment transforms form a derivative ladder.** -/
theorem hasDerivAt_TM (m : ℕ) (s₀ : ℂ) : HasDerivAt (κ.TM m) (κ.TM (m + 1) s₀) s₀ := by
  obtain ⟨C, hC0, hC⟩ := κ.dom 0 (|s₀.re| + 3 / 2 + (m + 1 : ℕ)) le_rfl (by positivity)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z u => κ.lapM m z u) (F' := fun z u => κ.lapM (m + 1) z u) (x₀ := s₀)
    (bound := fun u => C * Real.exp (-u ^ 2)) (s := Metric.ball s₀ 1)
    (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun z => (κ.continuous_lapM m z).aestronglyMeasurable)
    (κ.integrable_lapM m s₀) (κ.continuous_lapM (m + 1) s₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u z hz => (κ.norm_lapM_le hz u).trans (hC u))
    (integrable_gauss C) (Filter.Eventually.of_forall fun u z _ => κ.hasDerivAt_lapM m u z)
  exact h.2

theorem TM_zero : κ.TM 0 = κ.T := by
  funext s
  unfold TM T lapM
  simp

/-- **`T^{(m)} = TM m`.** -/
theorem iteratedDeriv_T (m : ℕ) : iteratedDeriv m κ.T = κ.TM m := by
  induction m with
  | zero => simp [TM_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    exact (κ.hasDerivAt_TM m s).deriv

theorem differentiable_T : Differentiable ℂ κ.T := fun s => by
  have := κ.hasDerivAt_TM 0 s
  rw [TM_zero] at this
  exact this.differentiableAt

/-- The flowed kernel `e^{−t u²} K`. -/
def flow (t : ℝ) : Kernel where
  K := fun u => Real.exp (-t * u ^ 2) * κ.K u
  cont := (Real.continuous_exp.comp (by fun_prop)).mul κ.cont
  dom := by
    intro a b ha hb
    obtain ⟨C, hC0, hC⟩ := κ.dom (a + |t|) b (by positivity) hb
    refine ⟨C, hC0, fun u => ?_⟩
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (a * u ^ 2 + b * |u|) * Real.exp (-t * u ^ 2) ≤
        Real.exp ((a + |t|) * u ^ 2 + b * |u|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := neg_abs_le t
      nlinarith [sq_nonneg u]
    calc Real.exp (a * u ^ 2 + b * |u|) * (Real.exp (-t * u ^ 2) * |κ.K u|)
        = (Real.exp (a * u ^ 2 + b * |u|) * Real.exp (-t * u ^ 2)) * |κ.K u| := by ring
      _ ≤ Real.exp ((a + |t|) * u ^ 2 + b * |u|) * |κ.K u| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ C * Real.exp (-u ^ 2) := hC u

theorem flow_flow (s t : ℝ) : (κ.flow t).flow s = κ.flow (s + t) := by
  unfold flow
  congr 1
  funext u
  simp only
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem flow_zero : κ.flow 0 = κ := by
  unfold flow
  cases κ
  congr 1
  funext u
  simp

theorem hasSum_flow_series (t : ℝ) (z : ℂ) (u : ℝ) :
    HasSum (fun k : ℕ => ((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * κ.lapM (2 * k) z u)
      ((κ.flow t).lap z u) := by
  unfold flow lap lapM lap
  simp only
  have h := NormedSpace.expSeries_div_hasSum_exp (-(t : ℂ) * (u : ℂ) ^ 2)
  rw [← Complex.exp_eq_exp_ℂ] at h
  have hval : Complex.exp (-(t : ℂ) * (u : ℂ) ^ 2) * (Complex.exp ((z - 1 / 2) * u) * (κ.K u : ℂ)) =
      Complex.exp ((z - 1 / 2) * u) * ((Real.exp (-t * u ^ 2) * κ.K u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [← hval]
  refine (h.mul_right (Complex.exp ((z - 1 / 2) * u) * (κ.K u : ℂ))).congr_fun ?_
  intro k
  rw [mul_pow, pow_mul]
  ring

theorem heatTerm_T (t : ℝ) (z : ℂ) (k : ℕ) :
    heatTerm t κ.T z k = ∫ u : ℝ, ((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * κ.lapM (2 * k) z u := by
  unfold heatTerm
  rw [κ.iteratedDeriv_T, integral_const_mul]
  rfl

theorem norm_flow_term (t : ℝ) (z : ℂ) (k : ℕ) (u : ℝ) :
    ‖((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * κ.lapM (2 * k) z u‖ =
      (|t| * u ^ 2) ^ k / (k.factorial : ℝ) * ‖κ.lap z u‖ := by
  unfold lapM
  rw [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_mul, sq_abs,
    mul_pow]
  ring

theorem hasSum_norm_flow (t : ℝ) (z : ℂ) (u : ℝ) :
    HasSum (fun k : ℕ => (|t| * u ^ 2) ^ k / (k.factorial : ℝ) * ‖κ.lap z u‖)
      (Real.exp (|t| * u ^ 2) * ‖κ.lap z u‖) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (|t| * u ^ 2)
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h.mul_right _

theorem norm_lap (s : ℂ) (u : ℝ) : ‖κ.lap s u‖ = Real.exp ((s.re - 1 / 2) * u) * |κ.K u| := by
  have := κ.norm_lapM 0 s u
  unfold lapM at this
  simpa using this

theorem flow_dominant (t : ℝ) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, Real.exp (|t| * u ^ 2) * ‖κ.lap z u‖ ≤ C * Real.exp (-u ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := κ.dom |t| |z.re - 1 / 2| (abs_nonneg _) (abs_nonneg _)
  refine ⟨C, hC0, fun u => ?_⟩
  rw [κ.norm_lap]
  have h1 : Real.exp ((z.re - 1 / 2) * u) ≤ Real.exp (|z.re - 1 / 2| * |u|) := by
    apply Real.exp_le_exp.mpr
    calc (z.re - 1 / 2) * u ≤ |(z.re - 1 / 2) * u| := le_abs_self _
      _ = |z.re - 1 / 2| * |u| := abs_mul _ _
  calc Real.exp (|t| * u ^ 2) * (Real.exp ((z.re - 1 / 2) * u) * |κ.K u|)
      ≤ Real.exp (|t| * u ^ 2) * (Real.exp (|z.re - 1 / 2| * |u|) * |κ.K u|) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = Real.exp (|t| * u ^ 2 + |z.re - 1 / 2| * |u|) * |κ.K u| := by
        rw [Real.exp_add]
        ring
    _ ≤ C * Real.exp (-u ^ 2) := hC u

/-- **The flow identity: `heatE t (T_K) = T_{e^{−t u²} K}`.** -/
theorem heatE_T (t : ℝ) (z : ℂ) : heatE t κ.T z = (κ.flow t).T z := by
  obtain ⟨C, hC0, hdom⟩ := κ.flow_dominant t z
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun u : ℝ => ((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * κ.lapM (2 * k) z u) volume :=
    fun k => (continuous_const.mul (κ.continuous_lapM _ z)).aestronglyMeasurable
  have hpt : ∀ u : ℝ, ∑' k : ℕ, ‖((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * κ.lapM (2 * k) z u‖ₑ =
      ENNReal.ofReal (Real.exp (|t| * u ^ 2) * ‖κ.lap z u‖) := by
    intro u
    rw [← (κ.hasSum_norm_flow t z u).tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (κ.hasSum_norm_flow t z u).summable]
    apply tsum_congr
    intro k
    rw [← ofReal_norm_eq_enorm, κ.norm_flow_term]
  have hfin : ∑' k : ℕ, ∫⁻ u : ℝ, ‖((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * κ.lapM (2 * k) z u‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun k => (hmeas k).enorm)]
    have hcongr : ∫⁻ u : ℝ, ∑' k : ℕ, ‖((-(t : ℂ)) ^ k / (k.factorial : ℂ)) * κ.lapM (2 * k) z u‖ₑ =
        ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (|t| * u ^ 2) * ‖κ.lap z u‖) :=
      lintegral_congr fun u => hpt u
    rw [hcongr]
    apply ne_top_of_le_ne_top (b := ∫⁻ u : ℝ, ENNReal.ofReal (C * Real.exp (-u ^ 2)))
    · rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gauss C)
        (Filter.Eventually.of_forall fun u => by positivity)]
      exact ENNReal.ofReal_ne_top
    · exact lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hdom u)
  have h := integral_tsum hmeas hfin
  unfold heatE
  simp_rw [κ.heatTerm_T]
  rw [← h]
  unfold T
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => (κ.hasSum_flow_series t z u).tsum_eq

end Kernel

/-! ## `Φ` is admissible, and the flow of `ξ` is a semigroup -/

/-- The kernel `Φ` as an admissible kernel. -/
def ΦK : Kernel where
  K := Φ
  cont := continuous_Φ
  dom := by
    intro a b ha hb
    refine ⟨2 * π ^ 2 * C₄ * Real.exp ((a + 1 + (b + 9 / 2)) + (a + 1 + (b + 9 / 2)) ^ 2),
      by have := C₄_nonneg; positivity, fun u => ?_⟩
    rw [abs_of_pos (Φ_pos u)]
    exact exp_mul_Φ_le ha hb u

theorem ΦK_T : ΦK.T = riemannXi := by
  funext s
  rw [riemannXi_eq_L]
  rfl

/-- **`heatE t ξ` is the transform of the flowed kernel `e^{−t u²} Φ`.** -/
theorem heatE_riemannXi_eq_T (t : ℝ) : heatE t riemannXi = (ΦK.flow t).T := by
  funext z
  rw [← ΦK_T, ΦK.heatE_T]

/-- **The flow is a semigroup on `ξ` at the entire face.** -/
theorem heatE_heatE_riemannXi (s t : ℝ) : heatE s (heatE t riemannXi) = heatE (s + t) riemannXi := by
  rw [heatE_riemannXi_eq_T t, heatE_riemannXi_eq_T (s + t), ← Kernel.flow_flow]
  funext z
  exact (ΦK.flow t).heatE_T s z

end Soma.Holonics.RH.KernelFlow
