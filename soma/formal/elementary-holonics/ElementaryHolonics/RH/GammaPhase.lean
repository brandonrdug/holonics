import Mathlib
import ElementaryHolonics.RH.GammaStirling
import ElementaryHolonics.RH.FlowedGamma

/-!
# RT3 (ii): the phase of the Gamma factor along a segment

The explicit main part of the Gamma factor is
`g(s) = ¼ s(s − 1) e^{−(s/2) log π} √(2π) exp((s/2 − ½) Log(s/2) − s/2)`, so that
`γ(s) = g(s) e^{−μ(s/2)}` by RT2. Its log-derivative is
`ℓ(s) = 1/(2s) + 1/(s − 1) − ½ log π + ½ Log(s/2)` with derivative
`ℓ'(s) = 1/(2s) − 1/(2s²) − 1/(s − 1)²`.

**Returned.** For `Re w ≥ 2` and `‖ζ‖ ≤ ‖w‖/8`:
`g(w + ζ) = g(w) exp(ζ ℓ(w) + ζ² ℓ'(w)/2 + R)` with `‖R‖ ≤ 37 ‖ζ‖³/‖w‖²`, by two applications of the
fundamental theorem along the segment (first for `g`, then for `ℓ`); with the vertical choice
`ζ = iy` this is the expansion RT3 (iii) integrates against the Gaussian, and with a real `ζ` it is
the horizontal ratio RT4 needs.
-/

noncomputable section

namespace Soma.Holonics.RH.GammaPhase

open Real Set Filter Topology MeasureTheory intervalIntegral
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.FlowedGamma

/-! ## The main part and its log-derivative -/

/-- `g(s) = ¼ s(s − 1) e^{−(s/2) log π} √(2π) exp((s/2 − ½) Log(s/2) − s/2)`. -/
def g (s : ℂ) : ℂ :=
  (1 / 4 : ℂ) * (s * (s - 1)) * Complex.exp (s * (-(Real.log π : ℂ) / 2)) *
    ((√(2 * π) : ℝ) : ℂ) * Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2)

/-- `ℓ(s) = 1/(2s) + 1/(s − 1) − ½ log π + ½ Log(s/2)`. -/
def ℓ (s : ℂ) : ℂ :=
  (2 * s)⁻¹ + (s - 1)⁻¹ - (1 / 2 : ℂ) * (Real.log π : ℂ) + (1 / 2 : ℂ) * Complex.log (s / 2)

/-- `ℓ'(s) = 1/(2s) − 1/(2s²) − 1/(s − 1)²`. -/
def ℓ' (s : ℂ) : ℂ := 1 / (2 * s) - 1 / (2 * s ^ 2) - 1 / (s - 1) ^ 2

theorem half_mem_slitPlane {s : ℂ} (hs : s ∈ Complex.slitPlane) : s / 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hs ⊢
  rcases hs with h | h
  · left
    simp
    linarith
  · right
    simp
    exact h

/-- **`γ = g e^{−μ(s/2)}`** whenever `s/2` is in the sector. -/
theorem γ_eq_g {s : ℂ} (hs : s / 2 ∈ Sector) : γ s = g s * Complex.exp (-μ (s / 2)) := by
  unfold γ g
  rw [gamma_eq_sqrt hs]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hcpow : (π : ℂ) ^ (-s / 2) = Complex.exp (s * (-(Real.log π : ℂ) / 2)) := by
    rw [Complex.cpow_def_of_ne_zero hπ, ← Complex.ofReal_log Real.pi_pos.le]
    congr 1
    ring
  rw [hcpow]
  have : Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2 - μ (s / 2)) =
      Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2) * Complex.exp (-μ (s / 2)) := by
    rw [← Complex.exp_add]
    congr 1
    first | done | ring
  rw [this]
  first | done | ring

theorem hasDerivAt_ℓ {s : ℂ} (hs : s ∈ Complex.slitPlane) (h1 : s ≠ 1) :
    HasDerivAt ℓ (ℓ' s) s := by
  have hs0 : s ≠ 0 := ne_zero_of_slit hs
  have hs2 := half_mem_slitPlane hs
  have h2s : (2 : ℂ) * s ≠ 0 := mul_ne_zero two_ne_zero hs0
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hA : HasDerivAt (fun x : ℂ => (2 * x)⁻¹) (-(2 * 1) / (2 * s) ^ 2) s :=
    ((hasDerivAt_id s).const_mul (2 : ℂ)).inv (by simpa using h2s)
  have hB : HasDerivAt (fun x : ℂ => (x - 1)⁻¹) (-1 / (s - 1) ^ 2) s :=
    ((hasDerivAt_id s).sub_const (1 : ℂ)).inv (by simpa using hs1)
  have hC : HasDerivAt (fun x : ℂ => Complex.log (x / 2)) ((1 / 2) / (s / 2)) s :=
    ((hasDerivAt_id s).div_const (2 : ℂ)).clog (by simpa using hs2)
  have h := ((hA.add hB).sub_const ((1 / 2 : ℂ) * (Real.log π : ℂ))).add (hC.const_mul (1 / 2 : ℂ))
  refine h.congr_deriv ?_
  unfold ℓ'
  field_simp
  ring

theorem hasDerivAt_g {s : ℂ} (hs : s ∈ Complex.slitPlane) (h1 : s ≠ 1) :
    HasDerivAt g (g s * ℓ s) s := by
  have hs0 : s ≠ 0 := ne_zero_of_slit hs
  have hs2 := half_mem_slitPlane hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hA : HasDerivAt (fun x : ℂ => (1 / 4 : ℂ) * (x * (x - 1)))
      ((1 / 4 : ℂ) * (1 * (s - 1) + s * 1)) s :=
    ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).const_mul _
  have hB : HasDerivAt (fun x : ℂ => Complex.exp (x * (-(Real.log π : ℂ) / 2)))
      (Complex.exp (s * (-(Real.log π : ℂ) / 2)) * (-(Real.log π : ℂ) / 2)) s := by
    have h0 : HasDerivAt (fun x : ℂ => x * (-(Real.log π : ℂ) / 2)) (-(Real.log π : ℂ) / 2) s := by
      simpa using (hasDerivAt_id s).mul_const (-(Real.log π : ℂ) / 2)
    exact h0.cexp
  have hlog : HasDerivAt (fun x : ℂ => Complex.log (x / 2)) ((1 / 2) / (s / 2)) s :=
    ((hasDerivAt_id s).div_const (2 : ℂ)).clog (by simpa using hs2)
  have hD : HasDerivAt (fun x : ℂ => Complex.exp ((x / 2 - 1 / 2) * Complex.log (x / 2) - x / 2))
      (Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2) *
        ((1 / 2) * Complex.log (s / 2) + (s / 2 - 1 / 2) * ((1 / 2) / (s / 2)) - 1 / 2)) s := by
    have h := ((((hasDerivAt_id s).div_const (2 : ℂ)).sub_const (1 / 2 : ℂ)).mul hlog).sub
      ((hasDerivAt_id s).div_const (2 : ℂ))
    have h2 := h.cexp
    refine h2.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply, id] <;> ring
  have h := ((hA.mul hB).mul_const ((√(2 * π) : ℝ) : ℂ)).mul hD
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply, id]
  unfold g ℓ
  field_simp
  ring

/-! ## The segment facts -/

/-- Points of a short segment from a point with `Re w ≥ 2` stay in the good region. -/
theorem seg_facts {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) {τ : ℝ} (hτ : |τ| ≤ 2) :
    (w + τ * ζ) ∈ Complex.slitPlane ∧ w + τ * ζ ≠ 1 ∧ 3 * ‖w‖ / 4 ≤ ‖w + τ * ζ‖ ∧
      ‖w‖ / 4 ≤ ‖w + τ * ζ - 1‖ ∧ (w + τ * ζ) / 2 ∈ Sector := by
  have hw2 : 2 ≤ ‖w‖ := le_trans hw (Complex.re_le_norm w)
  have hτζ : ‖(τ : ℂ) * ζ‖ ≤ ‖w‖ / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |τ| * ‖ζ‖ ≤ 2 * (‖w‖ / 8) := by gcongr
      _ = ‖w‖ / 4 := by ring
  have hre : (w + τ * ζ).re = w.re + τ * ζ.re := by simp
  have him : (w + τ * ζ).im = w.im + τ * ζ.im := by simp
  have hreζ : |τ * ζ.re| ≤ ‖w‖ / 4 := by
    calc |τ * ζ.re| = |((τ : ℂ) * ζ).re| := by simp
      _ ≤ ‖(τ : ℂ) * ζ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖w‖ / 4 := hτζ
  have himζ : |τ * ζ.im| ≤ ‖w‖ / 4 := by
    calc |τ * ζ.im| = |((τ : ℂ) * ζ).im| := by simp
      _ ≤ ‖(τ : ℂ) * ζ‖ := Complex.abs_im_le_norm _
      _ ≤ ‖w‖ / 4 := hτζ
  have hnw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnorm : 3 * ‖w‖ / 4 ≤ ‖w + τ * ζ‖ := by
    have := norm_sub_norm_le w (-(τ * ζ))
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have hnorm1 : ‖w‖ / 4 ≤ ‖w + τ * ζ - 1‖ := by
    have := norm_sub_norm_le (w + τ * ζ) 1
    rw [norm_one] at this
    linarith
  -- the slit: if the imaginary part vanishes the real part is positive
  have hslit : (w + τ * ζ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff, hre, him]
    by_cases him0 : w.im + τ * ζ.im = 0
    · left
      have h1 : |w.im| ≤ ‖w‖ / 4 := by
        have : w.im = -(τ * ζ.im) := by linarith
        rw [this, abs_neg]
        exact himζ
      have h2 : w.im ^ 2 ≤ ‖w‖ ^ 2 / 16 := by
        have := sq_le_sq' (by linarith [abs_nonneg w.im, neg_abs_le w.im]) (le_abs_self w.im |>.trans h1)
        nlinarith [sq_abs w.im, sq_nonneg w.im]
      have h3 : ‖w‖ ^ 2 / 4 ≤ w.re ^ 2 := by nlinarith
      have h4 : ‖w‖ / 2 ≤ w.re := by
        have hre0 : 0 ≤ w.re := by linarith
        nlinarith [norm_nonneg w]
      have h5 : τ * ζ.re ≥ -(‖w‖ / 4) := by linarith [neg_abs_le (τ * ζ.re)]
      linarith [norm_nonneg w]
    · exact Or.inr him0
  have hne1 : w + τ * ζ ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hnorm1
    linarith
  refine ⟨hslit, hne1, hnorm, hnorm1, ?_⟩
  -- the sector
  refine ⟨?_, ?_⟩
  · intro h
    have : w + τ * ζ = 0 := by
      have h2 : (w + τ * ζ) = 2 * ((w + τ * ζ) / 2) := by ring
      rw [h2, h, mul_zero]
    rw [this, norm_zero] at hnorm
    linarith
  · by_cases hre0 : 0 ≤ (w + τ * ζ).re
    · left
      simp only [Complex.div_ofNat_re]
      linarith
    · right
      push_neg at hre0
      simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, abs_div, Nat.abs_ofNat]
      rw [hre, him] at *
      have h1 : w.re < ‖w‖ / 4 := by linarith [neg_abs_le (τ * ζ.re)]
      have h2 : ‖w‖ ^ 2 * 15 / 16 < w.im ^ 2 := by nlinarith
      have h3 : ‖w‖ / 2 ≤ |w.im| := by
        have hsq : (‖w‖ / 2) ^ 2 ≤ |w.im| ^ 2 := by
          rw [sq_abs]
          nlinarith [norm_nonneg w]
        exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).mp hsq
      have h4 : |w.im| ≤ |w.im + τ * ζ.im| + |τ * ζ.im| := by
        have := abs_sub (w.im + τ * ζ.im) (τ * ζ.im)
        rwa [add_sub_cancel_right] at this
      rw [abs_of_neg hre0]
      have h5 : -(w.re + τ * ζ.re) ≤ ‖w‖ / 4 := by
        linarith [neg_abs_le (τ * ζ.re), le_abs_self (τ * ζ.re)]
      have h6 : ‖w‖ / 4 ≤ |w.im + τ * ζ.im| := by linarith
      linarith

/-! ## The expansion along a segment -/

theorem hasDerivAt_curve (w ζ : ℂ) (τ : ℝ) : HasDerivAt (fun τ : ℝ => w + (τ : ℂ) * ζ) ζ τ := by
  have h : HasDerivAt (fun y : ℂ => w + y * ζ) ζ (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).mul_const ζ).const_add w
  exact h.comp_ofReal

theorem hasDerivAt_g_curve {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) {τ : ℝ} (hτ : |τ| ≤ 2) :
    HasDerivAt (fun τ : ℝ => g (w + τ * ζ)) (g (w + τ * ζ) * ℓ (w + τ * ζ) * ζ) τ := by
  obtain ⟨hs, h1, -, -, -⟩ := seg_facts hw hζ hτ
  have hc : HasDerivAt (fun y : ℂ => w + y * ζ) ζ (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).mul_const ζ).const_add w
  have h := ((hasDerivAt_g hs h1).comp (τ : ℂ) hc).comp_ofReal
  exact h

theorem hasDerivAt_ℓ_curve {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) {τ : ℝ} (hτ : |τ| ≤ 2) :
    HasDerivAt (fun τ : ℝ => ℓ (w + τ * ζ)) (ℓ' (w + τ * ζ) * ζ) τ := by
  obtain ⟨hs, h1, -, -, -⟩ := seg_facts hw hζ hτ
  have hc : HasDerivAt (fun y : ℂ => w + y * ζ) ζ (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).mul_const ζ).const_add w
  have h := ((hasDerivAt_ℓ hs h1).comp (τ : ℂ) hc).comp_ofReal
  exact h

theorem continuousOn_ℓ_curve {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) :
    ContinuousOn (fun τ : ℝ => ℓ (w + τ * ζ)) (Ioo (-2) 2) := by
  intro τ hτ
  have : |τ| ≤ 2 := by
    rw [abs_le]
    exact ⟨hτ.1.le, hτ.2.le⟩
  exact (hasDerivAt_ℓ_curve hw hζ this).continuousAt.continuousWithinAt

theorem continuousOn_ℓ'_curve {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) :
    ContinuousOn (fun τ : ℝ => ℓ' (w + τ * ζ)) (Ioo (-2) 2) := by
  intro τ hτ
  have hτ' : |τ| ≤ 2 := by
    rw [abs_le]
    exact ⟨hτ.1.le, hτ.2.le⟩
  obtain ⟨hs, h1, -, -, -⟩ := seg_facts hw hζ hτ'
  have hs0 : w + τ * ζ ≠ 0 := ne_zero_of_slit hs
  have hs1 : w + τ * ζ - 1 ≠ 0 := sub_ne_zero.mpr h1
  apply ContinuousAt.continuousWithinAt
  unfold ℓ'
  have hc : Continuous fun τ : ℝ => w + (τ : ℂ) * ζ := by fun_prop
  apply ContinuousAt.sub
  · apply ContinuousAt.sub
    · exact (continuousAt_const.div (hc.continuousAt.const_mul 2) (by simpa using hs0))
    · exact continuousAt_const.div ((hc.continuousAt.pow 2).const_mul 2) (by simpa using hs0)
  · exact continuousAt_const.div ((hc.continuousAt.sub continuousAt_const).pow 2) (by simpa using hs1)

theorem mem_Ioo_of_uIcc {τ σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ uIcc 0 σ) : τ ∈ Ioo (-2 : ℝ) 2 := by
  rw [uIcc_of_le hσ.1] at hτ
  exact ⟨by linarith [hτ.1], by linarith [hτ.2, hσ.2]⟩

/-- The integrated phase `Λ(τ) = ∫_0^τ ℓ(w + σζ) dσ`. -/
def Λ (w ζ : ℂ) (τ : ℝ) : ℂ := ∫ σ in (0 : ℝ)..τ, ℓ (w + σ * ζ)

theorem hasDerivAt_Λ {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : HasDerivAt (Λ w ζ) (ℓ (w + τ * ζ)) τ := by
  have hcont := continuousOn_ℓ_curve hw hζ
  have hτ' : τ ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  apply integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    exact hcont.mono fun x hx => mem_Ioo_of_uIcc hτ hx
  · exact hcont.stronglyMeasurableAtFilter isOpen_Ioo τ hτ'
  · exact hcont.continuousAt (isOpen_Ioo.mem_nhds hτ')

/-- **`g` along the segment**: `g(w + ζ) = g(w) exp(ζ Λ(1))`. -/
theorem g_add_eq {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) :
    g (w + ζ) = g w * Complex.exp (ζ * Λ w ζ 1) := by
  set q : ℝ → ℂ := fun τ => g (w + τ * ζ) * Complex.exp (-(ζ * Λ w ζ τ)) with hq
  have hderiv : ∀ τ ∈ uIcc (0 : ℝ) 1, HasDerivAt q 0 τ := by
    intro τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    have h1 := hasDerivAt_g_curve hw hζ (τ := τ)
      (by rw [abs_le]; exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)
    have h2 := ((hasDerivAt_Λ hw hζ hτ).const_mul ζ).neg.cexp
    have h := h1.mul h2
    refine h.congr_deriv ?_
    ring
  have hfund := integral_eq_sub_of_hasDerivAt hderiv
    (by simp : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 1)
  rw [intervalIntegral.integral_zero] at hfund
  have hq1 : q 1 = g (w + ζ) * Complex.exp (-(ζ * Λ w ζ 1)) := by
    simp only [hq, Complex.ofReal_one, one_mul]
  have hq0 : q 0 = g w := by
    simp only [hq, Complex.ofReal_zero, zero_mul, add_zero]
    unfold Λ
    simp
  rw [hq1, hq0] at hfund
  have hexp : Complex.exp (-(ζ * Λ w ζ 1)) * Complex.exp (ζ * Λ w ζ 1) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc g (w + ζ) = g (w + ζ) * (Complex.exp (-(ζ * Λ w ζ 1)) * Complex.exp (ζ * Λ w ζ 1)) := by
        rw [hexp, mul_one]
    _ = (g (w + ζ) * Complex.exp (-(ζ * Λ w ζ 1))) * Complex.exp (ζ * Λ w ζ 1) := by ring
    _ = g w * Complex.exp (ζ * Λ w ζ 1) := by
        have : g (w + ζ) * Complex.exp (-(ζ * Λ w ζ 1)) = g w := by
          linear_combination (-1 : ℂ) * hfund
        rw [this]

/-- **`ℓ` along the segment**: `ℓ(w + σζ) = ℓ(w) + ∫_0^σ ℓ'(w + ηζ) ζ dη`. -/
theorem ℓ_add_eq {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ℓ (w + σ * ζ) = ℓ w + ∫ η in (0 : ℝ)..σ, ℓ' (w + η * ζ) * ζ := by
  have hderiv : ∀ η ∈ uIcc (0 : ℝ) σ, HasDerivAt (fun η : ℝ => ℓ (w + η * ζ)) (ℓ' (w + η * ζ) * ζ) η := by
    intro η hη
    have := mem_Ioo_of_uIcc hσ hη
    exact hasDerivAt_ℓ_curve hw hζ (by rw [abs_le]; exact ⟨this.1.le, this.2.le⟩)
  have hint : IntervalIntegrable (fun η : ℝ => ℓ' (w + η * ζ) * ζ) volume 0 σ := by
    apply ContinuousOn.intervalIntegrable
    exact ((continuousOn_ℓ'_curve hw hζ).mono fun x hx => mem_Ioo_of_uIcc hσ hx).mul continuousOn_const
  have h := integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  simp

/-- The difference of `ℓ'` along the segment. -/
theorem norm_ℓ'_sub_le {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) {η : ℝ}
    (hη : η ∈ Icc (0 : ℝ) 1) : ‖ℓ' (w + η * ζ) - ℓ' w‖ ≤ 402 * ‖ζ‖ / ‖w‖ ^ 2 := by
  obtain ⟨hs, h1, hn, hn1, -⟩ := seg_facts hw hζ (τ := η)
    (by rw [abs_le]; exact ⟨by linarith [hη.1], by linarith [hη.2]⟩)
  obtain ⟨hs0', h10', -, hn10, -⟩ := seg_facts hw hζ (τ := 0) (by simp)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hs0' h10' hn10
  set p : ℂ := w + η * ζ with hp
  have hw2 : 2 ≤ ‖w‖ := le_trans hw (Complex.re_le_norm w)
  have hw0 : 0 < ‖w‖ := by linarith
  have hp0 : p ≠ 0 := ne_zero_of_slit hs
  have hw0' : w ≠ 0 := ne_zero_of_slit hs0'
  have hp1 : p - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h10'
  have hηζ : ‖(η : ℂ) * ζ‖ ≤ ‖ζ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hη.2
  have hpw : ‖p - w‖ ≤ ‖ζ‖ := by
    rw [hp, add_sub_cancel_left]
    exact hηζ
  have hpn : ‖p‖ ≤ 9 * ‖w‖ / 8 := by
    calc ‖p‖ = ‖w + η * ζ‖ := rfl
      _ ≤ ‖w‖ + ‖(η : ℂ) * ζ‖ := norm_add_le _ _
      _ ≤ ‖w‖ + ‖w‖ / 8 := by linarith
      _ = 9 * ‖w‖ / 8 := by ring
  have hpn' : 3 * ‖w‖ / 4 ≤ ‖p‖ := hn
  have hp1n : ‖w‖ / 4 ≤ ‖p - 1‖ := hn1
  have hw1n : ‖w‖ / 4 ≤ ‖w - 1‖ := hn10
  -- the three differences
  have e1 : 1 / (2 * p) - 1 / (2 * w) = (w - p) / (2 * p * w) := by
    field_simp
    try ring
  have e2 : 1 / (2 * p ^ 2) - 1 / (2 * w ^ 2) = (w - p) * (w + p) / (2 * p ^ 2 * w ^ 2) := by
    field_simp
    try ring
  have e3 : 1 / (p - 1) ^ 2 - 1 / (w - 1) ^ 2 = (w - p) * (w + p - 2) / ((p - 1) ^ 2 * (w - 1) ^ 2) := by
    field_simp
    try ring
  have hwp : ‖w - p‖ ≤ ‖ζ‖ := by
    rw [norm_sub_rev]
    exact hpw
  have b1 : ‖1 / (2 * p) - 1 / (2 * w)‖ ≤ (2 / 3) * ‖ζ‖ / ‖w‖ ^ 2 := by
    rw [e1, norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖w - p‖ * ‖w‖ ^ 2 ≤ ‖ζ‖ * ‖w‖ ^ 2 := by gcongr
      _ = (2 / 3) * ‖ζ‖ * (2 * (3 * ‖w‖ / 4) * ‖w‖) := by ring
      _ ≤ (2 / 3) * ‖ζ‖ * (2 * ‖p‖ * ‖w‖) := by gcongr
  have b2 : ‖1 / (2 * p ^ 2) - 1 / (2 * w ^ 2)‖ ≤ ‖ζ‖ / ‖w‖ ^ 2 := by
    rw [e2, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsum : ‖w + p‖ ≤ 17 * ‖w‖ / 8 := by
      calc ‖w + p‖ ≤ ‖w‖ + ‖p‖ := norm_add_le _ _
        _ ≤ ‖w‖ + 9 * ‖w‖ / 8 := by linarith
        _ = 17 * ‖w‖ / 8 := by ring
    have hk : 17 * ‖w‖ / 8 ≤ 2 * (3 * ‖w‖ / 4) ^ 2 := by nlinarith [hw2]
    calc ‖w - p‖ * ‖w + p‖ * ‖w‖ ^ 2 ≤ ‖ζ‖ * (17 * ‖w‖ / 8) * ‖w‖ ^ 2 := by gcongr
      _ ≤ ‖ζ‖ * (2 * (3 * ‖w‖ / 4) ^ 2) * ‖w‖ ^ 2 := by gcongr
      _ ≤ ‖ζ‖ * (2 * ‖p‖ ^ 2) * ‖w‖ ^ 2 := by gcongr
      _ = ‖ζ‖ * (2 * ‖p‖ ^ 2 * ‖w‖ ^ 2) := by ring
  have b3 : ‖1 / (p - 1) ^ 2 - 1 / (w - 1) ^ 2‖ ≤ 400 * ‖ζ‖ / ‖w‖ ^ 2 := by
    rw [e3, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsum : ‖w + p - 2‖ ≤ 25 * ‖w‖ / 8 := by
      calc ‖w + p - 2‖ ≤ ‖w + p‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
        _ ≤ (‖w‖ + ‖p‖) + 2 := by
            rw [Complex.norm_ofNat]
            gcongr
            exact norm_add_le _ _
        _ ≤ (‖w‖ + 9 * ‖w‖ / 8) + ‖w‖ := by linarith
        _ = 25 * ‖w‖ / 8 := by ring
    have hk : 25 * ‖w‖ / 8 * ‖w‖ ^ 2 ≤ 400 * ((‖w‖ / 4) ^ 2 * (‖w‖ / 4) ^ 2) := by
      nlinarith [mul_nonneg (pow_nonneg (norm_nonneg w) 3) (by linarith : (0 : ℝ) ≤ ‖w‖ - 2)]
    calc ‖w - p‖ * ‖w + p - 2‖ * ‖w‖ ^ 2 ≤ ‖ζ‖ * (25 * ‖w‖ / 8) * ‖w‖ ^ 2 := by gcongr
      _ = ‖ζ‖ * (25 * ‖w‖ / 8 * ‖w‖ ^ 2) := by ring
      _ ≤ ‖ζ‖ * (400 * ((‖w‖ / 4) ^ 2 * (‖w‖ / 4) ^ 2)) := by gcongr
      _ = 400 * ‖ζ‖ * ((‖w‖ / 4) ^ 2 * (‖w‖ / 4) ^ 2) := by ring
      _ ≤ 400 * ‖ζ‖ * (‖p - 1‖ ^ 2 * ‖w - 1‖ ^ 2) := by gcongr
  have hsplit : ℓ' p - ℓ' w = (1 / (2 * p) - 1 / (2 * w)) - (1 / (2 * p ^ 2) - 1 / (2 * w ^ 2)) -
      (1 / (p - 1) ^ 2 - 1 / (w - 1) ^ 2) := by
    unfold ℓ'
    ring
  rw [hsplit]
  calc ‖(1 / (2 * p) - 1 / (2 * w)) - (1 / (2 * p ^ 2) - 1 / (2 * w ^ 2)) -
        (1 / (p - 1) ^ 2 - 1 / (w - 1) ^ 2)‖
      ≤ ‖1 / (2 * p) - 1 / (2 * w)‖ + ‖1 / (2 * p ^ 2) - 1 / (2 * w ^ 2)‖ +
          ‖1 / (p - 1) ^ 2 - 1 / (w - 1) ^ 2‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ (2 / 3) * ‖ζ‖ / ‖w‖ ^ 2 + ‖ζ‖ / ‖w‖ ^ 2 + 400 * ‖ζ‖ / ‖w‖ ^ 2 := by gcongr
    _ ≤ 402 * ‖ζ‖ / ‖w‖ ^ 2 := by
        rw [← add_div, ← add_div]
        gcongr
        linarith [norm_nonneg ζ]

/-- **The expansion of `g` along a segment**:
`g(w + ζ) = g(w) exp(ζ ℓ(w) + ζ² ℓ'(w)/2 + R)` with `‖R‖ ≤ 402 ‖ζ‖³/‖w‖²`. -/
theorem g_expansion {w ζ : ℂ} (hw : 2 ≤ w.re) (hζ : ‖ζ‖ ≤ ‖w‖ / 8) :
    ∃ R : ℂ, g (w + ζ) = g w * Complex.exp (ζ * ℓ w + ζ ^ 2 * ℓ' w / 2 + R) ∧
      ‖R‖ ≤ 402 * ‖ζ‖ ^ 3 / ‖w‖ ^ 2 := by
  have hw2 : 2 ≤ ‖w‖ := le_trans hw (Complex.re_le_norm w)
  -- the double integral of the difference
  set D : ℝ → ℂ := fun σ => ∫ η in (0 : ℝ)..σ, (ℓ' (w + η * ζ) - ℓ' w) * ζ with hD
  have hDbound : ∀ σ ∈ Icc (0 : ℝ) 1, ‖D σ‖ ≤ 402 * ‖ζ‖ ^ 2 / ‖w‖ ^ 2 := by
    intro σ hσ
    rw [hD]
    simp only
    have := norm_integral_le_of_norm_le_const (a := 0) (b := σ)
      (C := 402 * ‖ζ‖ / ‖w‖ ^ 2 * ‖ζ‖)
      (f := fun η : ℝ => (ℓ' (w + η * ζ) - ℓ' w) * ζ) (by
        intro η hη
        rw [uIoc_of_le hσ.1] at hη
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_ℓ'_sub_le hw hζ ⟨hη.1.le, hη.2.trans hσ.2⟩)
          (norm_nonneg _))
    calc ‖∫ η in (0 : ℝ)..σ, (ℓ' (w + η * ζ) - ℓ' w) * ζ‖ ≤ 402 * ‖ζ‖ / ‖w‖ ^ 2 * ‖ζ‖ * |σ - 0| :=
          this
      _ ≤ 402 * ‖ζ‖ / ‖w‖ ^ 2 * ‖ζ‖ * 1 := by
          gcongr
          rw [sub_zero, abs_of_nonneg hσ.1]
          exact hσ.2
      _ = 402 * ‖ζ‖ ^ 2 / ‖w‖ ^ 2 := by ring
  -- ℓ on the segment, with the difference isolated
  have hℓ : ∀ σ ∈ Icc (0 : ℝ) 1, ℓ (w + σ * ζ) = ℓ w + σ * (ℓ' w * ζ) + D σ := by
    intro σ hσ
    rw [ℓ_add_eq hw hζ hσ, hD]
    simp only
    have hint1 : IntervalIntegrable (fun η : ℝ => ℓ' (w + η * ζ) * ζ) volume 0 σ := by
      apply ContinuousOn.intervalIntegrable
      exact ((continuousOn_ℓ'_curve hw hζ).mono fun x hx => mem_Ioo_of_uIcc hσ hx).mul
        continuousOn_const
    have hint2 : IntervalIntegrable (fun _ : ℝ => ℓ' w * ζ) volume 0 σ := intervalIntegrable_const
    have hint3 : IntervalIntegrable (fun η : ℝ => (ℓ' (w + η * ζ) - ℓ' w) * ζ) volume 0 σ := by
      apply ContinuousOn.intervalIntegrable
      exact (((continuousOn_ℓ'_curve hw hζ).mono fun x hx => mem_Ioo_of_uIcc hσ hx).sub
        continuousOn_const).mul continuousOn_const
    have : ∫ η in (0 : ℝ)..σ, ℓ' (w + η * ζ) * ζ =
        (∫ η in (0 : ℝ)..σ, ℓ' w * ζ) + ∫ η in (0 : ℝ)..σ, (ℓ' (w + η * ζ) - ℓ' w) * ζ := by
      rw [← intervalIntegral.integral_add hint2 hint3]
      congr 1
      funext η
      ring
    rw [this, intervalIntegral.integral_const]
    simp only [sub_zero, Complex.real_smul]
    ring
  -- Λ(1)
  have hcontD : ContinuousOn D (Icc 0 1) := by
    intro σ hσ
    have hderiv : HasDerivAt D ((ℓ' (w + σ * ζ) - ℓ' w) * ζ) σ := by
      rw [hD]
      apply integral_hasDerivAt_right
      · apply ContinuousOn.intervalIntegrable
        exact (((continuousOn_ℓ'_curve hw hζ).mono fun x hx => mem_Ioo_of_uIcc hσ hx).sub
          continuousOn_const).mul continuousOn_const
      · have hτ' : σ ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
        exact (((continuousOn_ℓ'_curve hw hζ).sub continuousOn_const).mul
          continuousOn_const).stronglyMeasurableAtFilter isOpen_Ioo σ hτ'
      · have hτ' : σ ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
        exact (((continuousOn_ℓ'_curve hw hζ).sub continuousOn_const).mul
          continuousOn_const).continuousAt (isOpen_Ioo.mem_nhds hτ')
    exact hderiv.continuousAt.continuousWithinAt
  have hΛ : Λ w ζ 1 = ℓ w + ℓ' w * ζ / 2 + ∫ σ in (0 : ℝ)..1, D σ := by
    unfold Λ
    rw [intervalIntegral.integral_congr (fun σ hσ => hℓ σ (by rwa [uIcc_of_le zero_le_one] at hσ))]
    have hi3 : IntervalIntegrable (fun σ : ℝ => (σ : ℂ) * (ℓ' w * ζ)) volume 0 1 :=
      (by fun_prop : Continuous fun σ : ℝ => (σ : ℂ) * (ℓ' w * ζ)).intervalIntegrable _ _
    have hi1 : IntervalIntegrable (fun σ : ℝ => ℓ w + (σ : ℂ) * (ℓ' w * ζ)) volume 0 1 :=
      (by fun_prop : Continuous fun σ : ℝ => ℓ w + (σ : ℂ) * (ℓ' w * ζ)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable D volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rwa [uIcc_of_le zero_le_one]
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_add intervalIntegrable_const hi3,
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const]
    simp only [sub_zero, one_smul]
    have : ∫ σ in (0 : ℝ)..1, (σ : ℂ) = 1 / 2 := by
      have h := intervalIntegral.integral_ofReal (μ := volume) (f := fun σ : ℝ => σ) (a := 0) (b := 1)
      rw [h, integral_id]
      push_cast
      ring
    rw [this]
    ring
  refine ⟨ζ * ∫ σ in (0 : ℝ)..1, D σ, ?_, ?_⟩
  · rw [g_add_eq hw hζ, hΛ]
    congr 1
    congr 1
    ring
  · rw [norm_mul]
    have := norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 402 * ‖ζ‖ ^ 2 / ‖w‖ ^ 2)
      (f := D) (by
        intro σ hσ
        rw [uIoc_of_le zero_le_one] at hσ
        exact hDbound σ ⟨hσ.1.le, hσ.2⟩)
    simp only [sub_zero, abs_one, mul_one] at this
    calc ‖ζ‖ * ‖∫ σ in (0 : ℝ)..1, D σ‖ ≤ ‖ζ‖ * (402 * ‖ζ‖ ^ 2 / ‖w‖ ^ 2) := by gcongr
      _ = 402 * ‖ζ‖ ^ 3 / ‖w‖ ^ 2 := by ring

end Soma.Holonics.RH.GammaPhase
