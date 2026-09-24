import ElementaryHolonics.RH.LogDerivativeRemainder
import ElementaryHolonics.RH.XiEdgeDecomposition
import ElementaryHolonics.RH.XiLowerBoundOnLineTwo

/-!
# The archimedean term is bounded polynomially along a vertical line

`|Γ(s)| ≤ Γ(Re s)` from the integral, the reflection lower bound
`|Γ(a + iy)| ≥ π e^{−π|y|} / Γ(1 − a)` for `0 < a < 1`, and Landau's lemma for `Γ_ℝ` on a disc
about `1 + δ + iT` (no zeros, so the remainder is the whole log derivative) give
`|Γ_ℝ′/Γ_ℝ(1 + δ + it)| ≤ C (1 + |t|)`, hence the same for the archimedean part of `ξ′/ξ`.
A polynomial bound is all the prime side's convergence needs against a decaying weight.
-/

open Complex Metric Set Filter Topology MeasureTheory
open Soma.Holonics.RH.LogDerivativeRemainder
open Soma.Holonics.RH.XiEdgeDecomposition

namespace Soma.Holonics.RH.ArchimedeanPolynomialBound

/-! ## `|Γ(s)| ≤ Γ(Re s)` -/

theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  calc ‖∫ x in Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖
      ≤ ∫ x in Ioi (0 : ℝ), ‖((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (s.re - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Complex.norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]

/-! ## `|sin z| ≤ e^{|Im z|}` and the reflection lower bound -/

theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have e1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have e2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]
        norm_num
    _ ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by rw [h1, h2]; gcongr
    _ = Real.exp |z.im| := by ring

theorem sin_pi_mul_ne_zero {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Complex.sin (Real.pi * ((a : ℂ) + y * I)) ≠ 0 := by
  intro h
  rw [Complex.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hre := congrArg Complex.re hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz : ((a : ℂ) + y * I) = k := by
    have := hk
    rw [mul_comm] at this
    exact mul_right_cancel₀ hpi this
  have hre' := congrArg Complex.re hz
  simp at hre'
  have h0 : (0 : ℝ) < k := by rw [← hre']; exact ha0
  have h1 : (k : ℝ) < 1 := by rw [← hre']; exact ha1
  have h0' : (0 : ℤ) < k := by exact_mod_cast h0
  have h1' : k < (1 : ℤ) := by exact_mod_cast h1
  omega

/-- The reflection lower bound: for `0 < a < 1`,
`|Γ(a + iy)| ≥ π e^{−π|y|} / Γ(1 − a)`. -/
theorem norm_Gamma_ge {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Real.pi * Real.exp (-(Real.pi * |y|)) / Real.Gamma (1 - a) ≤ ‖Gamma ((a : ℂ) + y * I)‖ := by
  set z : ℂ := (a : ℂ) + y * I with hz
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hsin := sin_pi_mul_ne_zero (y := y) ha0 ha1
  rw [← hz] at hsin
  have hn := congrArg norm hrefl
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hn
  have hG1 : ‖Gamma (1 - z)‖ ≤ Real.Gamma (1 - a) := by
    have := norm_Gamma_le_Gamma_re (s := 1 - z) (by rw [hz]; simp; linarith)
    rwa [show (1 - z).re = 1 - a by rw [hz]; simp] at this
  have hsinle : ‖Complex.sin (Real.pi * z)‖ ≤ Real.exp (Real.pi * |y|) := by
    have := norm_sin_le_exp (Real.pi * z)
    rwa [show (Real.pi * z).im = Real.pi * y by rw [hz]; simp, abs_mul, abs_of_pos Real.pi_pos]
      at this
  have hsinpos : 0 < ‖Complex.sin (Real.pi * z)‖ := norm_pos_iff.mpr hsin
  have hGpos : 0 < Real.Gamma (1 - a) := Real.Gamma_pos_of_pos (by linarith)
  have hG1pos : 0 < ‖Gamma (1 - z)‖ := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero
    intro m hm
    have := congrArg Complex.re hm
    rw [hz] at this
    simp at this
    have : (m : ℝ) = a - 1 := by linarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  -- ‖Γ z‖ = π / (‖sin‖ ‖Γ(1−z)‖)
  have hprod : ‖Gamma z‖ * ‖Gamma (1 - z)‖ * ‖Complex.sin (Real.pi * z)‖ = Real.pi :=
    (eq_div_iff hsinpos.ne').mp hn
  have hΓz : ‖Gamma z‖ = Real.pi / (‖Complex.sin (Real.pi * z)‖ * ‖Gamma (1 - z)‖) := by
    rw [eq_div_iff (by positivity)]
    linarith [hprod]
  rw [hΓz]
  rw [div_le_div_iff₀ hGpos (by positivity)]
  calc Real.pi * Real.exp (-(Real.pi * |y|)) * (‖Complex.sin (Real.pi * z)‖ * ‖Gamma (1 - z)‖)
      ≤ Real.pi * Real.exp (-(Real.pi * |y|)) * (Real.exp (Real.pi * |y|) * Real.Gamma (1 - a)) := by
        gcongr
    _ = Real.pi * Real.Gamma (1 - a) := by
        have hE : Real.exp (-(Real.pi * |y|)) * Real.exp (Real.pi * |y|) = 1 := by
          rw [← Real.exp_add]
          simp
        linear_combination (Real.pi * Real.Gamma (1 - a)) * hE

/-! ## `Γ_ℝ` on a closed strip, and Landau on a vertical line -/

/-- `Γ_ℝ` is bounded on every closed strip `a ≤ Re z ≤ b` with `a > 0`. -/
theorem exists_bound_Gammaℝ_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ G : ℝ, 0 < G ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Gammaℝ z‖ ≤ G := by
  have hcont : ContinuousOn (fun u : ℝ => Real.pi ^ (-u) * Real.Gamma u) (Icc (a / 2) (b / 2)) := by
    apply ContinuousOn.mul
    · exact (continuous_const.rpow continuous_neg fun _ => Or.inl Real.pi_ne_zero).continuousOn
    · intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      exact (Real.differentiableAt_Gamma fun m => by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        intro h
        linarith).continuousAt.continuousWithinAt
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max G 1, by positivity, fun z hza hzb => ?_⟩
  rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hre : (-z / 2).re = -(z.re / 2) := by simp; ring
  have hre2 : (z / 2).re = z.re / 2 := by simp
  have hΓ := norm_Gamma_le_Gamma_re (s := z / 2) (by rw [hre2]; linarith)
  rw [hre2] at hΓ
  have hmem : z.re / 2 ∈ Icc (a / 2) (b / 2) := ⟨by linarith, by linarith⟩
  have hb := hG (z.re / 2) hmem
  rw [Real.norm_eq_abs] at hb
  have hpos : 0 ≤ Real.pi ^ (-(z.re / 2)) * Real.Gamma (z.re / 2) :=
    mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by linarith)).le
  calc Real.pi ^ (-z / 2).re * ‖Gamma (z / 2)‖
      ≤ Real.pi ^ (-(z.re / 2)) * Real.Gamma (z.re / 2) := by
        rw [hre]
        gcongr
    _ ≤ G := by rw [abs_of_nonneg hpos] at hb; exact hb
    _ ≤ max G 1 := le_max_left _ _

/-- **Landau on the line.**  For `1 < σ < 2` there is `C` with
`‖Γ_ℝ′/Γ_ℝ (σ + it)‖ ≤ C (1 + |t|)` for all `t`. -/
theorem exists_logDeriv_Gammaℝ_bound {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖logDeriv Gammaℝ ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) := by
  obtain ⟨G, hG0, hG⟩ := exists_bound_Gammaℝ_strip (a := σ / 2) (b := 3 * σ / 2) (by linarith)
    (by linarith)
  have hσ0 : 0 < σ := by linarith
  set L : ℝ := Real.pi ^ (1 - σ / 2) / Real.Gamma (1 - σ / 2) with hL
  have hL0 : 0 < L := by
    rw [hL]
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
  set r : ℝ := σ / 2 with hr_def
  rw [hr_def] at hL
  have hr : 0 < r := by rw [hr_def]; linarith
  set C : ℝ := 16 / σ * (|Real.log (G / L)| + 1 + Real.pi / 2) with hC
  refine ⟨C, by positivity, fun t => ?_⟩
  set z₀ : ℂ := (σ : ℂ) + t * I with hz₀
  -- the lower bound at the base point
  have hlow : L * Real.exp (-(Real.pi * |t| / 2)) ≤ ‖Gammaℝ z₀‖ := by
    rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-z₀ / 2).re = -(σ / 2) := by rw [hz₀]; simp; ring
    have harg : z₀ / 2 = ((σ / 2 : ℝ) : ℂ) + (t / 2 : ℝ) * I := by rw [hz₀]; push_cast; ring
    rw [hre, harg]
    have h := norm_Gamma_ge (a := σ / 2) (y := t / 2) (by linarith) (by linarith)
    rw [abs_div, abs_two] at h
    have hpi : Real.pi ^ (-(σ / 2)) = Real.pi ^ (1 - σ / 2) / Real.pi := by
      have hp := Real.rpow_pos_of_pos Real.pi_pos (σ / 2)
      rw [Real.rpow_sub Real.pi_pos, Real.rpow_one, Real.rpow_neg Real.pi_pos.le]
      field_simp
    calc L * Real.exp (-(Real.pi * |t| / 2))
        = Real.pi ^ (-(σ / 2)) * (Real.pi * Real.exp (-(Real.pi * (|t| / 2))) /
            Real.Gamma (1 - σ / 2)) := by
          rw [hpi, hL]
          field_simp
      _ ≤ Real.pi ^ (-(σ / 2)) * ‖Gamma (((σ / 2 : ℝ) : ℂ) + (t / 2 : ℝ) * I)‖ := by
          gcongr
  -- the Landau budget
  set M : ℝ := |Real.log (G / L)| + 1 + Real.pi * |t| / 2 with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  have hball : ∀ z ∈ ball z₀ r, σ / 2 < z.re ∧ z.re < 3 * σ / 2 := by
    intro z hz
    rw [mem_ball_iff_norm] at hz
    have := Complex.abs_re_le_norm (z - z₀)
    rw [sub_re, hz₀] at this
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
      add_zero] at this
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  have hg : DifferentiableOn ℂ Gammaℝ (ball z₀ r) := fun z hz =>
    (differentiableAt_Gammaℝ_of_re_pos (by linarith [(hball z hz).1])).differentiableWithinAt
  have hne : ∀ z ∈ ball z₀ r, Gammaℝ z ≠ 0 := fun z hz =>
    Gammaℝ_ne_zero_of_re_pos (by linarith [(hball z hz).1])
  have hbound : ∀ z ∈ ball z₀ r, ‖Gammaℝ z‖ ≤ ‖Gammaℝ z₀‖ * Real.exp M := by
    intro z hz
    have h1 := hG z (hball z hz).1.le (hball z hz).2.le
    have hexp : G ≤ L * Real.exp (|Real.log (G / L)| + 1) := by
      have : G / L ≤ Real.exp (|Real.log (G / L)| + 1) := by
        calc G / L = Real.exp (Real.log (G / L)) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp (|Real.log (G / L)| + 1) :=
            Real.exp_le_exp.mpr (by linarith [le_abs_self (Real.log (G / L))])
      rwa [div_le_iff₀ hL0, mul_comm] at this
    calc ‖Gammaℝ z‖ ≤ G := h1
      _ ≤ L * Real.exp (|Real.log (G / L)| + 1) := hexp
      _ = (L * Real.exp (-(Real.pi * |t| / 2))) *
          Real.exp (|Real.log (G / L)| + 1 + Real.pi * |t| / 2) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ ‖Gammaℝ z₀‖ * Real.exp M := by
          rw [hM]
          gcongr
  have hLandau := norm_logDeriv_le hr hM0 hg hne hbound (mem_closedBall_self (by positivity))
  rw [logDeriv_apply]
  refine hLandau.trans ?_
  rw [hC, hM, hr_def]
  have ht := abs_nonneg t
  have hlog := abs_nonneg (Real.log (G / L))
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < σ / 2)]
  have h16 : (16 : ℝ) / σ * (|Real.log (G / L)| + 1 + Real.pi / 2) * (1 + |t|) * (σ / 2) =
      8 * ((|Real.log (G / L)| + 1 + Real.pi / 2) * (1 + |t|)) := by
    field_simp
    ring
  rw [h16]
  have : |Real.log (G / L)| + 1 + Real.pi * |t| / 2 ≤
      (|Real.log (G / L)| + 1 + Real.pi / 2) * (1 + |t|) := by
    nlinarith [Real.pi_pos]
  linarith

/-- **The archimedean term is bounded polynomially on the line `Re s = 1 + δ`.** -/
theorem exists_archimedean_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖archimedean (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ C * (1 + |t|) := by
  obtain ⟨C, hC0, hC⟩ := exists_logDeriv_Gammaℝ_bound (σ := 1 + δ) (by linarith) (by linarith)
  refine ⟨1 + 1 / δ + C, by positivity, fun t => ?_⟩
  set s : ℂ := ((1 + δ : ℝ) : ℂ) + t * I with hs
  have hsre : s.re = 1 + δ := by rw [hs]; simp
  have hs1re : (s - 1).re = δ := by rw [hs]; simp
  have h1 : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have := Complex.abs_re_le_norm s
    rw [hsre, abs_of_pos (by linarith)] at this
    rw [div_le_one (by linarith)]
    linarith
  have h2 : ‖1 / (s - 1)‖ ≤ 1 / δ := by
    rw [norm_div, norm_one]
    have := Complex.abs_re_le_norm (s - 1)
    rw [hs1re, abs_of_pos hδ] at this
    exact one_div_le_one_div_of_le hδ this
  have h3 := hC t
  rw [← hs] at h3
  have ht : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  unfold archimedean
  calc ‖1 / s + 1 / (s - 1) + logDeriv Gammaℝ s‖
      ≤ ‖1 / s + 1 / (s - 1)‖ + ‖logDeriv Gammaℝ s‖ := norm_add_le _ _
    _ ≤ (‖1 / s‖ + ‖1 / (s - 1)‖) + ‖logDeriv Gammaℝ s‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ (1 + 1 / δ) + C * (1 + |t|) := by gcongr
    _ ≤ (1 + 1 / δ) * (1 + |t|) + C * (1 + |t|) := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) ht
    _ = (1 + 1 / δ + C) * (1 + |t|) := by ring

end Soma.Holonics.RH.ArchimedeanPolynomialBound
