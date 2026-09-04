import Mathlib
import ElementaryHolonics.RH.FlowedGammaContour

/-!
# RT3 (iii-b): the window through the saddle

`Γ_t(w) = (4πt)^{−1/2} ∫_{Re z = 2} e^{(z − w)²/(4t)} γ₁(z) dz/i`, and on the window
`|Im z − y₀| ≤ Y` the line `Re z = 2` may be replaced by the line `Re z = c` through the saddle,
at the cost of the two horizontal pieces of the rectangle (Cauchy on the rectangle, which
contains no pole since `Im z ≥ y₀ − Y > 0`) and the two tails of the line `Re z = 2`.

**Returned.** `Γt_window`: the exact decomposition
`Γ_t(w) = (4πt)^{−1/2} (∫_{−Y}^{Y} f(c + i(y₀ + v)) dv − i (H₊ − H₋) + T)` with
`f(z) = e^{(z−w)²/(4t)} γ₁(z)`, `H_± = ∫_c^2 f(x + i(y₀ ± Y)) dx`, and `T` the tails.
-/

noncomputable section

namespace Soma.Holonics.RH.EventSaddle

open Real Set Filter Topology MeasureTheory intervalIntegral
open Soma.Holonics.RH.FlowedGamma
open Soma.Holonics.RH.FlowedGammaContour

/-- The contour integrand `f(z) = e^{(z − w)²/(4t)} γ₁(z)`. -/
def f (t : ℝ) (w z : ℂ) : ℂ := Complex.exp ((z - w) ^ 2 / (4 * t)) * γ₁ z

attribute [irreducible] f

theorem f_apply (t : ℝ) (w z : ℂ) : f t w z = Complex.exp ((z - w) ^ 2 / (4 * t)) * γ₁ z := by
  unfold f
  rfl

/-- `γ₁` is differentiable off the real axis. -/
theorem differentiableAt_γ₁_of_im {z : ℂ} (hz : z.im ≠ 0) : DifferentiableAt ℂ γ₁ z := by
  unfold γ₁
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2 + 1)) z := by
    apply DifferentiableAt.comp
    · apply Complex.differentiableAt_Gamma
      intro m h
      have him : (z / 2 + 1).im = z.im / 2 := by simp
      have hm : ((-(m : ℂ)) : ℂ).im = 0 := by simp
      rw [h, hm] at him
      apply hz
      linarith
    · fun_prop
  have hcpow : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) z := by
    apply DifferentiableAt.const_cpow (by fun_prop)
    exact Or.inl hπ
  exact ((differentiableAt_const _).mul (by fun_prop)).mul (hcpow.mul hΓ)

theorem differentiableAt_f {t : ℝ} (w : ℂ) {z : ℂ} (hz : z.im ≠ 0) : DifferentiableAt ℂ (f t w) z := by
  have : f t w = fun z => Complex.exp ((z - w) ^ 2 / (4 * t)) * γ₁ z := funext (f_apply t w)
  rw [this]
  exact (((differentiableAt_id.sub_const w).pow 2).div_const _).cexp.mul (differentiableAt_γ₁_of_im hz)

/-- **The window through the saddle.** For `0 < Y < y₀`, any real `c`, and any `w`:
`Γ_t(w) = (4πt)^{−1/2} (∫_{−Y}^{Y} f(c + i(y₀+v)) dv − i(H₊ − H₋) + T)`. -/
theorem Γt_window {t : ℝ} (ht : 0 < t) (w : ℂ) (c y₀ Y : ℝ) (hY : 0 < Y) (hy : Y < y₀) :
    Γt t w = ((√(4 * π * t) : ℝ) : ℂ)⁻¹ *
      ((∫ v in (-Y)..Y, f t w ((c : ℂ) + Complex.I * ((y₀ + v : ℝ) : ℂ)))
        - Complex.I * ((∫ x in c..(2 : ℝ), f t w ((x : ℂ) + ((y₀ + Y : ℝ) : ℂ) * Complex.I))
            - ∫ x in c..(2 : ℝ), f t w ((x : ℂ) + ((y₀ - Y : ℝ) : ℂ) * Complex.I))
        + ((∫ y : ℝ, f t w (2 + Complex.I * y))
            - ∫ y in (y₀ - Y)..(y₀ + Y), f t w (2 + Complex.I * y))) := by
  have hrep := Γt_eq_contour ht (by norm_num : (-2 : ℝ) < 2) w
  have hf2 : ∀ y : ℝ, Complex.exp ((((2 : ℝ) : ℂ) + Complex.I * y - w) ^ 2 / (4 * t)) *
      γ₁ ((2 : ℝ) + Complex.I * y) = f t w (2 + Complex.I * y) := by
    intro y
    rw [f_apply]
    push_cast
    ring_nf
  simp_rw [hf2] at hrep
  rw [hrep]
  congr 1
  -- the rectangle
  set z₀ : ℂ := (c : ℂ) + ((y₀ - Y : ℝ) : ℂ) * Complex.I with hz₀
  set w₀ : ℂ := (2 : ℂ) + ((y₀ + Y : ℝ) : ℂ) * Complex.I with hw₀
  have hz₀re : z₀.re = c := by simp [hz₀]
  have hz₀im : z₀.im = y₀ - Y := by simp [hz₀]
  have hw₀re : w₀.re = 2 := by simp [hw₀]
  have hw₀im : w₀.im = y₀ + Y := by simp [hw₀]
  have hdiff : DifferentiableOn ℂ (f t w) (uIcc z₀.re w₀.re ×ℂ uIcc z₀.im w₀.im) := by
    intro z hz
    rw [Complex.mem_reProdIm, hz₀im, hw₀im] at hz
    have him := hz.2
    rw [uIcc_of_le (by linarith : y₀ - Y ≤ y₀ + Y)] at him
    have : z.im ≠ 0 := by
      have := him.1
      linarith
    exact (differentiableAt_f w this).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (f t w) z₀ w₀ hdiff
  rw [hz₀re, hz₀im, hw₀re, hw₀im] at hrect
  have e2 : (∫ y in (y₀ - Y)..(y₀ + Y), f t w ((2 : ℝ) + (y : ℂ) * Complex.I)) =
      ∫ y in (y₀ - Y)..(y₀ + Y), f t w (2 + Complex.I * y) := by
    apply integral_congr
    intro y _
    congr 1
    push_cast
    ring
  have ec : (∫ y in (y₀ - Y)..(y₀ + Y), f t w ((c : ℝ) + (y : ℂ) * Complex.I)) =
      ∫ v in (-Y)..Y, f t w ((c : ℂ) + Complex.I * ((y₀ + v : ℝ) : ℂ)) := by
    have hshift := intervalIntegral.integral_comp_add_right
      (fun y : ℝ => f t w ((c : ℂ) + Complex.I * (y : ℂ))) y₀ (a := -Y) (b := Y)
    rw [show -Y + y₀ = y₀ - Y by ring, show Y + y₀ = y₀ + Y by ring] at hshift
    calc (∫ y in (y₀ - Y)..(y₀ + Y), f t w ((c : ℝ) + (y : ℂ) * Complex.I))
        = ∫ y in (y₀ - Y)..(y₀ + Y), f t w ((c : ℂ) + Complex.I * (y : ℂ)) := by
          apply integral_congr
          intro y _
          congr 1
          ring
      _ = ∫ x in (-Y)..Y, f t w ((c : ℂ) + Complex.I * ((x + y₀ : ℝ) : ℂ)) := hshift.symm
      _ = ∫ v in (-Y)..Y, f t w ((c : ℂ) + Complex.I * ((y₀ + v : ℝ) : ℂ)) := by
          apply integral_congr
          intro v _
          congr 1
          push_cast
          ring
  rw [e2, ec] at hrect
  simp only [smul_eq_mul] at hrect
  linear_combination (-Complex.I) * hrect +
    ((∫ y in (y₀ - Y)..(y₀ + Y), f t w (2 + Complex.I * y)) -
      ∫ v in (-Y)..Y, f t w ((c : ℂ) + Complex.I * ((y₀ + v : ℝ) : ℂ))) * Complex.I_sq

end Soma.Holonics.RH.EventSaddle
