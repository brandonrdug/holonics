import ElementaryHolonics.Foundation.CoordinateSubsetReceiver
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Coordinate Haar receivers

The Boolean coordinate receiver chooses, at each point, precisely those circle directions where
the second Abel factor is cheaper than the undifferenced near bound.  The totalized penalty

`R / max 1 (R² |1 - exp(2πix)|²)`

is continuous at the singular chart point.  Jordan's chord inequality gives a Lorentz majorant
whose normalized one-circle Haar integral is at most `π/2`, and hence at most `2`.  Fubini then
returns the rational three-torus constant `8`.

The final subset theorem is specialization-independent: if every coordinate face returns its
scale-balanced Abel estimate, the pointwise value is controlled by the product penalty selected
by its unique far face.  This is the exact analytic companion to `CoordinateSubsetReceiver`.
-/

open scoped Real
open MeasureTheory Real

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.CoordinateHaarReceiver

theorem unitAddCircle_four_mul_norm_le_fourier_gap (q : UnitAddCircle) :
    4 * ‖q‖ ≤ ‖1 - fourier 1 q‖ := by
  induction q using QuotientAddGroup.induction_on with
  | _ x =>
      let y : ℝ := x - round x
      have hy : |y| ≤ 1 / 2 := by
        dsimp [y]
        exact abs_sub_round x
      have hyPi : |π * y| ≤ π / 2 := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        nlinarith [Real.pi_pos]
      have hsin := Real.mul_abs_le_abs_sin (x := π * y) hyPi
      have hcoe : ((y : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
        dsimp [y]
        simp
      rw [UnitAddCircle.norm_eq]
      change 4 * |y| ≤ _
      rw [← hcoe, fourier_coe_apply]
      norm_num
      rw [show (2 : ℂ) * π * Complex.I * (y : ℂ) =
          Complex.I * (2 * π * y : ℝ) by
        push_cast
        ring]
      rw [← norm_neg, neg_sub, Complex.norm_exp_I_mul_ofReal_sub_one]
      rw [show (2 * π * y) / 2 = π * y by ring]
      have hsin' : 2 * |y| ≤ |Real.sin (π * y)| := by
        calc
          2 * |y| = 2 / π * |π * y| := by
            rw [abs_mul, abs_of_pos Real.pi_pos]
            field_simp [ne_of_gt Real.pi_pos]
          _ ≤ |Real.sin (π * y)| := hsin
      norm_num
      linarith

def unitCircleChord (q : UnitAddCircle) : ℝ :=
  ‖(1 : ℂ) - fourier 1 q‖

def scalarHaarPenalty (radius gap : ℝ) : ℝ :=
  radius / max 1 (radius ^ 2 * gap ^ 2)

def oneCircleHaarPenalty (radius : ℝ) (q : UnitAddCircle) : ℝ :=
  scalarHaarPenalty radius (unitCircleChord q)

theorem unitAddCircle_norm_coe_eq_abs {x : ℝ}
    (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    ‖(x : UnitAddCircle)‖ = |x| := by
  rw [UnitAddCircle.norm_eq]
  rcases eq_or_ne x (1 / 2) with rfl | hne
  · norm_num
  · have hround : round x = 0 := by
      rw [round_eq_zero_iff]
      exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
    rw [hround, Int.cast_zero, sub_zero]

theorem oneCircleHaarPenalty_le_lorentz
    {radius : ℝ} (hradius : 1 ≤ radius)
    {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    oneCircleHaarPenalty radius (x : UnitAddCircle) ≤
      2 * radius / (1 + (4 * radius * x) ^ 2) := by
  let chord := unitCircleChord (x : UnitAddCircle)
  let u := radius ^ 2 * chord ^ 2
  let v := (4 * radius * x) ^ 2
  have hgap : 4 * |x| ≤ chord := by
    dsimp [chord, unitCircleChord]
    rw [← unitAddCircle_norm_coe_eq_abs hx]
    exact unitAddCircle_four_mul_norm_le_fourier_gap (x : UnitAddCircle)
  have hchord : 0 ≤ chord := by
    dsimp [chord, unitCircleChord]
    positivity
  have hvu : v ≤ u := by
    have hsquare : (4 * |x|) ^ 2 ≤ chord ^ 2 :=
      pow_le_pow_left₀ (by positivity) hgap 2
    dsimp [u, v]
    rw [show (4 * radius * x) ^ 2 = radius ^ 2 * (4 * |x|) ^ 2 by
      simp only [mul_pow, sq_abs]
      ring]
    exact mul_le_mul_of_nonneg_left hsquare (sq_nonneg radius)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hmaxOne : 1 ≤ max 1 u := le_max_left _ _
  have hmaxU : u ≤ max 1 u := le_max_right _ _
  have hdenom : 0 < 1 + v := by dsimp [v]; positivity
  have hmaxPos : 0 < max 1 u := lt_of_lt_of_le zero_lt_one hmaxOne
  unfold oneCircleHaarPenalty
  unfold scalarHaarPenalty
  change radius / max 1 u ≤ 2 * radius / (1 + v)
  rw [div_le_div_iff₀ hmaxPos hdenom]
  nlinarith

theorem integral_lorentz_majorant
    {radius : ℝ} (hradius : 0 < radius) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        2 * radius / (1 + (4 * radius * x) ^ 2) =
      Real.arctan (2 * radius) := by
  let c := 4 * radius
  let f : ℝ → ℝ := fun y ↦ (1 + y ^ 2)⁻¹
  have hsub := intervalIntegral.mul_integral_comp_mul_left
    (a := (-(1 / 2 : ℝ))) (b := (1 / 2 : ℝ)) (f := f) c
  have hintegral :
      ∫ y in -(2 * radius)..(2 * radius), f y =
        2 * Real.arctan (2 * radius) := by
    dsimp [f]
    rw [integral_inv_one_add_sq]
    simp [Real.arctan_neg]
    ring
  calc
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        2 * radius / (1 + (4 * radius * x) ^ 2)) =
      (1 / 2 : ℝ) *
        (c * ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f (c * x)) := by
          rw [← intervalIntegral.integral_const_mul]
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x _
          dsimp [f, c]
          field_simp [ne_of_gt hradius]
          ring
    _ = (1 / 2 : ℝ) *
        (∫ y in c * (-(1 / 2 : ℝ))..c * (1 / 2), f y) := by rw [hsub]
    _ = (1 / 2 : ℝ) *
        (∫ y in -(2 * radius)..(2 * radius), f y) := by
          congr 2 <;> dsimp [c] <;> ring
    _ = Real.arctan (2 * radius) := by rw [hintegral]; ring

theorem continuous_unitCircleChord : Continuous unitCircleChord := by
  unfold unitCircleChord
  fun_prop

theorem continuous_oneCircleHaarPenalty (radius : ℝ) :
    Continuous (oneCircleHaarPenalty radius) := by
  unfold oneCircleHaarPenalty scalarHaarPenalty
  apply continuous_const.div
  · exact continuous_const.max
      (continuous_const.mul (continuous_unitCircleChord.pow 2))
  · intro q
    have : (0 : ℝ) < max 1 (radius ^ 2 * unitCircleChord q ^ 2) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    positivity

theorem integral_oneCircleHaarPenalty_le
    {radius : ℝ} (hradius : 1 ≤ radius) :
    ∫ q : UnitAddCircle, oneCircleHaarPenalty radius q
        ∂AddCircle.haarAddCircle ≤ Real.pi / 2 := by
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← UnitAddCircle.intervalIntegral_preimage (-(1 / 2 : ℝ))]
  norm_num [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by ring]
  have hpenalty : IntervalIntegrable
      (fun x : ℝ ↦ oneCircleHaarPenalty radius (x : UnitAddCircle)) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    have hcoe : Continuous ((↑) : ℝ → UnitAddCircle) := continuous_quotient_mk'
    exact ((continuous_oneCircleHaarPenalty radius).comp hcoe).intervalIntegrable _ _
  have hlorentz : IntervalIntegrable
      (fun x : ℝ ↦ 2 * radius / (1 + (4 * radius * x) ^ 2)) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    apply Continuous.intervalIntegrable
    apply continuous_const.div
    · fun_prop
    · intro x
      positivity
  calc
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
      oneCircleHaarPenalty radius (x : UnitAddCircle)) ≤
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
          2 * radius / (1 + (4 * radius * x) ^ 2) :=
      intervalIntegral.integral_mono_on (by norm_num) hpenalty hlorentz
        (fun x hx ↦ oneCircleHaarPenalty_le_lorentz hradius hx)
    _ = Real.arctan (2 * radius) := integral_lorentz_majorant (by linarith)
    _ ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two _).le

theorem integral_oneCircleHaarPenalty_le_two
    {radius : ℝ} (hradius : 1 ≤ radius) :
    ∫ q : UnitAddCircle, oneCircleHaarPenalty radius q
        ∂AddCircle.haarAddCircle ≤ 2 := by
  have h := integral_oneCircleHaarPenalty_le hradius
  exact h.trans (by linarith [Real.pi_le_four])

theorem integral_volume_oneCircleHaarPenalty_le_two
    {radius : ℝ} (hradius : 1 ≤ radius) :
    ∫ q : UnitAddCircle, oneCircleHaarPenalty radius q ≤ 2 := by
  have h := integral_oneCircleHaarPenalty_le_two hradius
  rw [AddCircle.integral_haarAddCircle] at h
  simpa using h

theorem integral_threeTorus_penaltyProduct_le_eight
    {radius : ℝ} (hradius : 1 ≤ radius) :
    ∫ q : UnitAddTorus (Fin 3),
        ∏ axis, oneCircleHaarPenalty radius (q axis) ≤ 8 := by
  rw [MeasureTheory.integral_fintype_prod_volume_eq_pow]
  have hupper := integral_volume_oneCircleHaarPenalty_le_two hradius
  have hnonneg : 0 ≤ ∫ q : UnitAddCircle, oneCircleHaarPenalty radius q := by
    apply integral_nonneg
    intro q
    unfold oneCircleHaarPenalty
    unfold scalarHaarPenalty
    positivity
  norm_num [Fintype.card_fin]
  exact (pow_le_pow_left₀ hnonneg hupper 3).trans_eq (by norm_num)

def farCoordinateFace {n : ℕ} (radius : ℝ) (gap : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun axis ↦ 1 ≤ radius ^ 2 * gap axis ^ 2

def coordinateSubsetScale {n : ℕ} (radius : ℝ) (face : Finset (Fin n)) : ℝ :=
  radius ^ (n - face.card) * (radius⁻¹) ^ face.card

theorem prod_scalarHaarPenalty_eq_subsetScale_mul_invGap
    {n : ℕ} {radius : ℝ} (hradius : 0 < radius) (gap : Fin n → ℝ) :
    (∏ axis, scalarHaarPenalty radius (gap axis)) =
      coordinateSubsetScale radius (farCoordinateFace radius gap) *
        (∏ axis ∈ farCoordinateFace radius gap, gap axis ^ 2)⁻¹ := by
  classical
  let face := farCoordinateFace radius gap
  have hsplit :
      (∏ axis ∈ face, scalarHaarPenalty radius (gap axis)) *
          (∏ axis ∈ faceᶜ, scalarHaarPenalty radius (gap axis)) =
        ∏ axis, scalarHaarPenalty radius (gap axis) := by
    have hraw := Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun axis : Fin n ↦ axis ∈ face)
      (fun axis ↦ scalarHaarPenalty radius (gap axis))
    have hface : Finset.univ.filter (fun axis : Fin n ↦ axis ∈ face) = face := by
      ext axis
      simp
    have hcomp : Finset.univ.filter (fun axis : Fin n ↦ ¬ axis ∈ face) = faceᶜ := by
      ext axis
      simp
    rw [hface, hcomp] at hraw
    exact hraw
  rw [← hsplit]
  have hfar : (∏ axis ∈ face, scalarHaarPenalty radius (gap axis)) =
      (radius⁻¹) ^ face.card * (∏ axis ∈ face, gap axis ^ 2)⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro axis haxis
    have hlarge : 1 ≤ radius ^ 2 * gap axis ^ 2 := by
      simpa [face, farCoordinateFace] using haxis
    have hgap : gap axis ≠ 0 := by
      intro hzero
      rw [hzero] at hlarge
      norm_num at hlarge
    unfold scalarHaarPenalty
    rw [max_eq_right hlarge]
    field_simp [hradius.ne', hgap]
  have hnear : (∏ axis ∈ faceᶜ, scalarHaarPenalty radius (gap axis)) =
      radius ^ (n - face.card) := by
    have hcard : faceᶜ.card = n - face.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    rw [← hcard, ← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro axis haxis
    have hnot : axis ∉ face := by simpa using haxis
    have hsmall : ¬ 1 ≤ radius ^ 2 * gap axis ^ 2 := by
      simpa [face, farCoordinateFace] using hnot
    unfold scalarHaarPenalty
    rw [max_eq_left (le_of_not_ge hsmall)]
    simp
  rw [hfar, hnear]
  unfold coordinateSubsetScale
  dsimp [face]
  ring

theorem value_le_constant_mul_penaltyProduct_of_all_subset_returns
    {n : ℕ} {radius constant value : ℝ} (hradius : 0 < radius)
    (gap : Fin n → ℝ)
    (hreturns : ∀ face : Finset (Fin n),
      (∏ axis ∈ face, gap axis ^ 2) * value ≤
        constant * coordinateSubsetScale radius face) :
    value ≤ constant * ∏ axis, scalarHaarPenalty radius (gap axis) := by
  classical
  let face := farCoordinateFace radius gap
  let gapProduct := ∏ axis ∈ face, gap axis ^ 2
  have hgapProduct : 0 < gapProduct := by
    dsimp [gapProduct]
    apply Finset.prod_pos
    intro axis haxis
    have hlarge : 1 ≤ radius ^ 2 * gap axis ^ 2 := by
      simpa [face, farCoordinateFace] using haxis
    have hgap : gap axis ≠ 0 := by
      intro hzero
      rw [hzero] at hlarge
      norm_num at hlarge
    positivity
  have hface := hreturns face
  have hscaled : value ≤
      constant * coordinateSubsetScale radius face * gapProduct⁻¹ := by
    calc
      value = (gapProduct * value) * gapProduct⁻¹ := by
        field_simp [hgapProduct.ne']
      _ ≤ (constant * coordinateSubsetScale radius face) * gapProduct⁻¹ :=
        mul_le_mul_of_nonneg_right hface (inv_nonneg.mpr hgapProduct.le)
  rw [prod_scalarHaarPenalty_eq_subsetScale_mul_invGap hradius]
  dsimp [face, gapProduct] at hscaled ⊢
  convert hscaled using 1
  ring

section Audit

#print axioms unitAddCircle_four_mul_norm_le_fourier_gap
#print axioms integral_oneCircleHaarPenalty_le
#print axioms integral_threeTorus_penaltyProduct_le_eight
#print axioms prod_scalarHaarPenalty_eq_subsetScale_mul_invGap
#print axioms value_le_constant_mul_penaltyProduct_of_all_subset_returns

end Audit

end Soma.Holonics.CoordinateHaarReceiver
