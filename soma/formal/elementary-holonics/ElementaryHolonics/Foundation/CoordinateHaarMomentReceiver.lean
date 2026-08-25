import ElementaryHolonics.Foundation.CoordinateHaarReceiver
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Coordinate Haar moment receivers

**[proved-derived]** The coordinate Haar penalty does more than return a uniform mass bound.
Retaining the displacement from the singular chart point returns a decaying second moment.  This
is the exact local difference needed before a product receiver may reconstruct a decaying
three-torus moment.
-/

open scoped Real
open MeasureTheory Real

noncomputable section

namespace Soma.Holonics.CoordinateHaarMomentReceiver

open Soma.Holonics.CoordinateHaarReceiver

open scoped BigOperators

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The Lorentz majorant retains an exact inverse-radius second moment on the centered chart. -/
theorem intervalIntegral_sq_mul_lorentz_le
    {radius : ℝ} (hradius : 1 ≤ radius) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        x ^ 2 * (2 * radius / (1 + (4 * radius * x) ^ 2)) ≤
      1 / (8 * radius) := by
  have hradiusPos : 0 < radius := lt_of_lt_of_le zero_lt_one hradius
  have hintegrable : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 2 * (2 * radius / (1 + (4 * radius * x) ^ 2))) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    apply Continuous.intervalIntegrable
    apply (continuous_id.pow 2).mul
    apply continuous_const.div
    · fun_prop
    · intro x
      positivity
  calc
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        x ^ 2 * (2 * radius / (1 + (4 * radius * x) ^ 2))) ≤
      ∫ _x in (-(1 / 2 : ℝ))..(1 / 2), 1 / (8 * radius) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hintegrable
          (intervalIntegrable_const)
        intro x _hx
        have hdenom : 0 < 1 + (4 * radius * x) ^ 2 := by positivity
        have hscale : 0 < 8 * radius := mul_pos (by norm_num) hradiusPos
        rw [show x ^ 2 * (2 * radius / (1 + (4 * radius * x) ^ 2)) =
          (2 * radius * x ^ 2) / (1 + (4 * radius * x) ^ 2) by ring]
        rw [div_le_div_iff₀ hdenom hscale]
        nlinarith [sq_nonneg (4 * radius * x)]
    _ = 1 / (8 * radius) := by
      rw [intervalIntegral.integral_const]
      norm_num

/-- The centered one-circle Haar receiver has second moment at most `1 / (8R)`. -/
theorem integral_norm_sq_mul_oneCircleHaarPenalty_le
    {radius : ℝ} (hradius : 1 ≤ radius) :
    ∫ q : UnitAddCircle,
        ‖q‖ ^ 2 * oneCircleHaarPenalty radius q
        ∂AddCircle.haarAddCircle ≤
      1 / (8 * radius) := by
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← UnitAddCircle.intervalIntegral_preimage (-(1 / 2 : ℝ))]
  norm_num [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by ring]
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ ‖(x : UnitAddCircle)‖ ^ 2 *
        oneCircleHaarPenalty radius (x : UnitAddCircle)) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    apply Continuous.intervalIntegrable
    have hcoe : Continuous ((↑) : ℝ → UnitAddCircle) := continuous_quotient_mk'
    exact ((continuous_norm.comp hcoe).pow 2).mul
      ((continuous_oneCircleHaarPenalty radius).comp hcoe)
  have hright : IntervalIntegrable
      (fun x : ℝ ↦ x ^ 2 * (2 * radius / (1 + (4 * radius * x) ^ 2))) volume
      (-(1 / 2 : ℝ)) (1 / 2) := by
    apply Continuous.intervalIntegrable
    apply (continuous_id.pow 2).mul
    apply continuous_const.div
    · fun_prop
    · intro x
      positivity
  calc
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        ‖(x : UnitAddCircle)‖ ^ 2 * oneCircleHaarPenalty radius (x : UnitAddCircle)) ≤
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        x ^ 2 * (2 * radius / (1 + (4 * radius * x) ^ 2)) := by
          apply intervalIntegral.integral_mono_on (by norm_num) hleft hright
          intro x hx
          rw [unitAddCircle_norm_coe_eq_abs hx, sq_abs]
          exact mul_le_mul_of_nonneg_left
            (oneCircleHaarPenalty_le_lorentz hradius hx) (sq_nonneg x)
    _ ≤ 1 / (8 * radius) := intervalIntegral_sq_mul_lorentz_le hradius
    _ = radius⁻¹ * (1 / 8) := by
      field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hradius)]

/-- The first displacement moment decays at least as the inverse square root of the receiver
radius.  The proof keeps the exact second moment and uses the positive square
`(2 √R |q| - 1)²` to interpolate it with the already returned mass. -/
theorem integral_norm_mul_oneCircleHaarPenalty_le
    {radius : ℝ} (hradius : 1 ≤ radius) :
    ∫ q : UnitAddCircle,
        ‖q‖ * oneCircleHaarPenalty radius q
        ∂AddCircle.haarAddCircle ≤
      5 / (8 * Real.sqrt radius) := by
  let root := Real.sqrt radius
  have hradiusNonneg : 0 ≤ radius := zero_le_one.trans hradius
  have hrootPos : 0 < root := by
    dsimp [root]
    exact Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hradius)
  have hpenaltyNonneg : ∀ q : UnitAddCircle,
      0 ≤ oneCircleHaarPenalty radius q := by
    intro q
    unfold oneCircleHaarPenalty scalarHaarPenalty
    positivity
  have hyoung : ∀ q : UnitAddCircle,
      ‖q‖ ≤ root * ‖q‖ ^ 2 + 1 / (4 * root) := by
    intro q
    have hsquare : 0 ≤ (2 * root * ‖q‖ - 1) ^ 2 := sq_nonneg _
    have hidentity :
        root * ‖q‖ ^ 2 + 1 / (4 * root) - ‖q‖ =
          (2 * root * ‖q‖ - 1) ^ 2 / (4 * root) := by
      field_simp [ne_of_gt hrootPos]
      ring
    rw [← sub_nonneg, hidentity]
    positivity
  have hleft : Integrable (fun q : UnitAddCircle ↦
      ‖q‖ * oneCircleHaarPenalty radius q) AddCircle.haarAddCircle :=
    (continuous_norm.mul (continuous_oneCircleHaarPenalty radius)).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hsquareIntegrable : Integrable (fun q : UnitAddCircle ↦
      ‖q‖ ^ 2 * oneCircleHaarPenalty radius q) AddCircle.haarAddCircle :=
    ((continuous_norm.pow 2).mul
      (continuous_oneCircleHaarPenalty radius)).integrable_of_hasCompactSupport
        isClosed_closure.isCompact
  have hpenaltyIntegrable :
      Integrable (oneCircleHaarPenalty radius) AddCircle.haarAddCircle :=
    (continuous_oneCircleHaarPenalty radius).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hright : Integrable (fun q : UnitAddCircle ↦
      root * (‖q‖ ^ 2 * oneCircleHaarPenalty radius q) +
        (1 / (4 * root)) * oneCircleHaarPenalty radius q)
      AddCircle.haarAddCircle :=
    (hsquareIntegrable.const_mul root).add
      (hpenaltyIntegrable.const_mul (1 / (4 * root)))
  have hsecond := integral_norm_sq_mul_oneCircleHaarPenalty_le hradius
  have hmass := integral_oneCircleHaarPenalty_le_two hradius
  calc
    (∫ q : UnitAddCircle,
        ‖q‖ * oneCircleHaarPenalty radius q
        ∂AddCircle.haarAddCircle) ≤
      ∫ q : UnitAddCircle,
        root * (‖q‖ ^ 2 * oneCircleHaarPenalty radius q) +
          (1 / (4 * root)) * oneCircleHaarPenalty radius q
        ∂AddCircle.haarAddCircle := by
      apply integral_mono hleft hright
      intro q
      calc
        ‖q‖ * oneCircleHaarPenalty radius q ≤
            (root * ‖q‖ ^ 2 + 1 / (4 * root)) *
              oneCircleHaarPenalty radius q :=
          mul_le_mul_of_nonneg_right (hyoung q) (hpenaltyNonneg q)
        _ = root * (‖q‖ ^ 2 * oneCircleHaarPenalty radius q) +
            (1 / (4 * root)) * oneCircleHaarPenalty radius q := by ring
    _ = root * (∫ q : UnitAddCircle,
          ‖q‖ ^ 2 * oneCircleHaarPenalty radius q
          ∂AddCircle.haarAddCircle) +
        (1 / (4 * root)) *
          (∫ q : UnitAddCircle, oneCircleHaarPenalty radius q
            ∂AddCircle.haarAddCircle) := by
      rw [integral_add (hsquareIntegrable.const_mul root)
        (hpenaltyIntegrable.const_mul (1 / (4 * root))),
        integral_const_mul, integral_const_mul]
    _ ≤ root * (1 / (8 * radius)) + (1 / (4 * root)) * 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsecond (le_of_lt hrootPos))
        (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ = 5 / (8 * Real.sqrt radius) := by
      change root * (1 / (8 * radius)) + (1 / (4 * root)) * 2 =
        5 / (8 * root)
      have hrootSq : root ^ 2 = radius := by
        exact Real.sq_sqrt hradiusNonneg
      rw [← hrootSq]
      field_simp [ne_of_gt hrootPos]
      ring

/-- The coordinatewise weighted product used to retain one displacement face under product Haar
transport. -/
def coordinateMomentPenaltyProduct
    (radius : ℝ) (axis : Fin 3) (q : UnitAddTorus (Fin 3)) : ℝ :=
  ‖q axis‖ * ∏ coordinate, oneCircleHaarPenalty radius (q coordinate)

/-- Product Haar factors a coordinate moment into one first-moment face and two mass faces. -/
theorem integral_coordinateMomentPenaltyProduct_le
    {radius : ℝ} (hradius : 1 ≤ radius) (axis : Fin 3) :
    ∫ q : UnitAddTorus (Fin 3), coordinateMomentPenaltyProduct radius axis q
        ∂(Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) ≤
      5 / (2 * Real.sqrt radius) := by
  classical
  let factor : Fin 3 → UnitAddCircle → ℝ := fun coordinate x ↦
    (if coordinate = axis then ‖x‖ else 1) * oneCircleHaarPenalty radius x
  have hintegral :
      (∫ q : UnitAddTorus (Fin 3), coordinateMomentPenaltyProduct radius axis q
          ∂(Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle)) =
        ∏ coordinate, ∫ x : UnitAddCircle, factor coordinate x
          ∂AddCircle.haarAddCircle := by
    rw [show (fun q : UnitAddTorus (Fin 3) ↦ coordinateMomentPenaltyProduct radius axis q) =
        (fun q ↦ ∏ coordinate, factor coordinate (q coordinate)) by
      funext q
      unfold coordinateMomentPenaltyProduct factor
      rw [Finset.prod_mul_distrib]
      simp]
    exact MeasureTheory.integral_fintype_prod_eq_prod factor
  rw [hintegral]
  have hfactorNonneg (coordinate : Fin 3) :
      0 ≤ ∫ x : UnitAddCircle, factor coordinate x ∂AddCircle.haarAddCircle := by
    apply integral_nonneg
    intro x
    have hpenalty : 0 ≤ oneCircleHaarPenalty radius x := by
      unfold oneCircleHaarPenalty scalarHaarPenalty
      positivity
    dsimp [factor]
    split_ifs <;> positivity
  have hfactorBound (coordinate : Fin 3) :
      (∫ x : UnitAddCircle, factor coordinate x ∂AddCircle.haarAddCircle) ≤
        if coordinate = axis then 5 / (8 * Real.sqrt radius) else 2 := by
    by_cases hcoordinate : coordinate = axis
    · subst coordinate
      simpa [factor] using integral_norm_mul_oneCircleHaarPenalty_le hradius
    · simpa [factor, hcoordinate] using integral_oneCircleHaarPenalty_le_two hradius
  calc
    (∏ coordinate : Fin 3,
        ∫ x : UnitAddCircle, factor coordinate x ∂AddCircle.haarAddCircle) ≤
      ∏ coordinate : Fin 3,
        if coordinate = axis then 5 / (8 * Real.sqrt radius) else 2 := by
      exact Finset.prod_le_prod (fun coordinate _ ↦ hfactorNonneg coordinate)
        (fun coordinate _ ↦ hfactorBound coordinate)
    _ = 5 / (2 * Real.sqrt radius) := by
      fin_cases axis <;> simp [Fin.prod_univ_succ] <;> ring

/-- The product-space sup distance is bounded by the sum of its three coordinate differences. -/
theorem threeTorus_dist_zero_le_sum_coordinate_norm
    (q : UnitAddTorus (Fin 3)) :
    dist q 0 ≤ ∑ axis : Fin 3, ‖q axis‖ := by
  rw [dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2
  intro axis
  exact Finset.single_le_sum (fun coordinate _ ↦ norm_nonneg (q coordinate))
    (Finset.mem_univ axis)

/-- The three-torus distance moment of the product Haar receiver decays as `R⁻¹ᐚ²`. -/
theorem integral_threeTorus_dist_mul_penaltyProduct_le
    {radius : ℝ} (hradius : 1 ≤ radius) :
    ∫ q : UnitAddTorus (Fin 3),
        dist q 0 * ∏ axis, oneCircleHaarPenalty radius (q axis)
        ∂(Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) ≤
      15 / (2 * Real.sqrt radius) := by
  let penaltyProduct : UnitAddTorus (Fin 3) → ℝ := fun q ↦
    ∏ axis, oneCircleHaarPenalty radius (q axis)
  have hpenaltyNonneg : ∀ q, 0 ≤ penaltyProduct q := by
    intro q
    dsimp [penaltyProduct]
    exact Finset.prod_nonneg fun axis _ ↦ by
      unfold oneCircleHaarPenalty scalarHaarPenalty
      positivity
  have hleft : Integrable (fun q : UnitAddTorus (Fin 3) ↦
      dist q 0 * penaltyProduct q)
      (Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) :=
    ((continuous_id.dist continuous_const).mul
      (by
        dsimp [penaltyProduct]
        apply continuous_finset_prod
        intro axis _haxis
        exact (continuous_oneCircleHaarPenalty radius).comp
          (continuous_apply axis))).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hcoordinate (axis : Fin 3) : Integrable
      (coordinateMomentPenaltyProduct radius axis)
      (Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) := by
    apply Continuous.integrable_of_hasCompactSupport
    · unfold coordinateMomentPenaltyProduct
      apply ((continuous_norm.comp (continuous_apply axis)).mul)
      apply continuous_finset_prod
      intro coordinate _hcoordinate
      exact (continuous_oneCircleHaarPenalty radius).comp
        (continuous_apply coordinate)
    · exact isClosed_closure.isCompact
  have hright : Integrable (fun q : UnitAddTorus (Fin 3) ↦
      ∑ axis : Fin 3, coordinateMomentPenaltyProduct radius axis q)
      (Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) :=
    integrable_finset_sum Finset.univ fun axis _ ↦ hcoordinate axis
  calc
    (∫ q : UnitAddTorus (Fin 3),
        dist q 0 * ∏ axis, oneCircleHaarPenalty radius (q axis)
        ∂(Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle)) ≤
      ∫ q : UnitAddTorus (Fin 3),
        ∑ axis : Fin 3, coordinateMomentPenaltyProduct radius axis q
        ∂(Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) := by
      apply integral_mono hleft hright
      intro q
      calc
        dist q 0 * penaltyProduct q ≤
            (∑ axis : Fin 3, ‖q axis‖) * penaltyProduct q :=
          mul_le_mul_of_nonneg_right
            (threeTorus_dist_zero_le_sum_coordinate_norm q) (hpenaltyNonneg q)
        _ = ∑ axis : Fin 3, coordinateMomentPenaltyProduct radius axis q := by
          simp only [Finset.sum_mul]
          rfl
    _ = ∑ axis : Fin 3,
        ∫ q : UnitAddTorus (Fin 3), coordinateMomentPenaltyProduct radius axis q
          ∂(Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) := by
      exact integral_finset_sum Finset.univ fun axis _ ↦ hcoordinate axis
    _ ≤ ∑ _axis : Fin 3, 5 / (2 * Real.sqrt radius) := by
      exact Finset.sum_le_sum fun axis _ ↦
        integral_coordinateMomentPenaltyProduct_le hradius axis
    _ = 15 / (2 * Real.sqrt radius) := by simp; ring

section Audit

#print axioms intervalIntegral_sq_mul_lorentz_le
#print axioms integral_norm_sq_mul_oneCircleHaarPenalty_le
#print axioms integral_norm_mul_oneCircleHaarPenalty_le
#print axioms integral_coordinateMomentPenaltyProduct_le
#print axioms threeTorus_dist_zero_le_sum_coordinate_norm
#print axioms integral_threeTorus_dist_mul_penaltyProduct_le

end Audit

end Soma.Holonics.CoordinateHaarMomentReceiver
