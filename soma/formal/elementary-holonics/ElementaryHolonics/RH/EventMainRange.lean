import Mathlib
import ElementaryHolonics.RH.EventExplicit

/-!
# RT3 (iii-m): the majorant in `u = (Im s)^{1/3}`

With `y = Im s = u³`, `Y = u²/20`, `L ≤ u`, and `|Re s| ≤ X ≤ u³`, every piece of the explicit
defect bound is majorized by a function of `u` alone: `Bmaj t X u`.
-/

noncomputable section

namespace Soma.Holonics.RH.EventMainRange

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.GammaStirling
open Soma.Holonics.RH.GammaPhase
open Soma.Holonics.RH.EventMain
open Soma.Holonics.RH.EventBounds
open Soma.Holonics.RH.EventGaussian
open Soma.Holonics.RH.EventPieces
open Soma.Holonics.RH.EventHorizontal
open Soma.Holonics.RH.EventExplicit

/-! ## The parameter constants -/

/-- `ξ ≤ cξ u`. -/
def cξ (t X : ℝ) : ℝ := X + 2 * t + 2
/-- `ξ₁ ≤ c₁ u`. -/
def c₁ (t X : ℝ) : ℝ := 2 * X + 2 + 14 * t
/-- `Z ≤ cZ u³`. -/
def cZ (t X : ℝ) : ℝ := cξ t X + 2

/-! ## Elementary majorizations -/

theorem log_le_self_of_one_le {u : ℝ} (hu : 1 ≤ u) : Real.log u ≤ u := by
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < u)]

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem norm_s_le {X : ℝ} {s : ℂ} (hX : |s.re| ≤ X) {u : ℝ} (hy : s.im = u ^ 3) (hXu : X ≤ u ^ 3)
    (hu : 0 ≤ u) : ‖s‖ ≤ 2 * u ^ 3 := by
  calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ X + u ^ 3 := by
        rw [hy, abs_of_nonneg (pow_nonneg hu 3)]
        exact add_le_add hX le_rfl
    _ ≤ 2 * u ^ 3 := by linarith

theorem norm_s_ge {s : ℂ} {u : ℝ} (hy : s.im = u ^ 3) (hu : 0 ≤ u) : u ^ 3 ≤ ‖s‖ := by
  calc u ^ 3 = s.im := hy.symm
    _ ≤ ‖s‖ := Complex.im_le_norm s

theorem log_norm_s_le {X : ℝ} {s : ℂ} (hX : |s.re| ≤ X) {u : ℝ} (hy : s.im = u ^ 3) (hXu : X ≤ u ^ 3)
    (hu : 1 ≤ u) : Real.log ‖s‖ ≤ 1 + 3 * u := by
  have h1 := norm_s_le hX hy hXu (by linarith)
  have hs0 : 0 < ‖s‖ := by
    have := norm_s_ge hy (by linarith)
    nlinarith [pow_pos (by linarith : (0 : ℝ) < u) 3]
  calc Real.log ‖s‖ ≤ Real.log (2 * u ^ 3) := Real.log_le_log hs0 h1
    _ = Real.log 2 + 3 * Real.log u := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
    _ ≤ 1 + 3 * u := by
        have := log_le_self_of_one_le hu
        linarith [log_two_le_one]

theorem ξ_le {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) {L u : ℝ} (hL : 0 ≤ L) (hLu : L ≤ u) (hu : 1 ≤ u) :
    X + 2 * t * L + 2 ≤ cξ t X * u := by
  unfold cξ
  nlinarith

theorem ξ₁_le {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) {s : ℂ} (hXs : |s.re| ≤ X) {L u : ℝ} (hL : 0 ≤ L)
    (hLu : L ≤ u) (hu : 1 ≤ u) (hy : s.im = u ^ 3) (hXu : X ≤ u ^ 3) :
    2 * X + 2 * (2 * t * L) + 2 + t * (Real.log ‖s‖ + 6) ≤ c₁ t X * u := by
  unfold c₁
  have h1 := log_norm_s_le hXs hy hXu hu
  have e1 : t * L ≤ t * u := mul_le_mul_of_nonneg_left hLu ht
  have e2 : t * Real.log ‖s‖ ≤ t * (1 + 3 * u) := mul_le_mul_of_nonneg_left h1 ht
  have e3 : 0 ≤ X * (u - 1) := mul_nonneg hX (sub_nonneg.mpr hu)
  have e4 : 0 ≤ t * (u - 1) := mul_nonneg ht (sub_nonneg.mpr hu)
  nlinarith [e1, e2, e3, e4]

theorem Z_le {t X : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X) {L u : ℝ} (hL : 0 ≤ L) (hLu : L ≤ u) (hu : 1 ≤ u) :
    X + 2 * t * L + 2 + u ^ 3 + u ^ 2 / 20 ≤ cZ t X * u ^ 3 := by
  unfold cZ
  have h1 := ξ_le ht hX hL hLu hu
  have hu0 : 0 ≤ u := by linarith
  have h2 : u ≤ u ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hu0 (sub_nonneg.mpr hu)) (by linarith : 0 ≤ u + 1)]
  have h3 : u ^ 2 / 20 ≤ u ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hu0 2) (sub_nonneg.mpr hu)]
  have hcξ : 0 ≤ cξ t X := by unfold cξ; linarith
  have h4 := mul_le_mul_of_nonneg_left h2 hcξ
  linarith

end Soma.Holonics.RH.EventMainRange
