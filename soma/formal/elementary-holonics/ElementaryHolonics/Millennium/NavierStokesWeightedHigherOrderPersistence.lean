import ElementaryHolonics.Millennium.NavierStokesWeightedCommonApertureUniqueness

/-!
# Higher-order persistence across the native H³ restart aperture

**[proved-derived]** The arbitrary-order and native `H³` restart constructors use the same
explicit scalar time law but different nonlinear loads.  This owner compares those loads before
introducing any new existence principle.

Whenever the arbitrary-order tame constant does not exceed the established native `H³` Leray
constant, the high restart aperture contains the complete native `H³` aperture.  Exact Volterra
retiming then restricts the high fixed point to that full aperture, and native fixed-point
uniqueness identifies its `H³` receiver with the independently returned `H³` path.  The currently
proved constants discharge this dominance for every `base ≤ 8`, yielding persistence through
`H⁹` on one native restart aperture.

The mixed low--high tame estimate further sharpens the high path bound from the original coarse
restart radius to `2 ‖initial‖`.  For higher orders the exact one-shot obstruction is retained as
the failed scalar dominance relation; this file does not claim that iterative restart or an energy
Gronwall construction is impossible.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderPersistence

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesDuhamelRestartTime
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedCommonApertureUniqueness
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderDuhamelLift
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Exact retiming of a higher-order path -/

/-- Restrict a high path through the same addressed time inclusion used by the native `H³`
carrier. -/
def weightedHigherOrderPathTimeRestrict
    {base : ℕ} {S T : ℝ} (hST : S ≤ T)
    (path : WeightedHigherOrderPath base T) : WeightedHigherOrderPath base S :=
  path.comp (weightedTimeApertureInclusion hST)

@[simp]
theorem weightedHigherOrderPathTimeRestrict_apply
    {base : ℕ} {S T : ℝ} (hST : S ≤ T)
    (path : WeightedHigherOrderPath base T) (t : Icc (0 : ℝ) S) :
    weightedHigherOrderPathTimeRestrict hST path t =
      path ⟨t.1, t.2.1, t.2.2.trans hST⟩ :=
  rfl

theorem norm_weightedHigherOrderPathTimeRestrict_le
    {base : ℕ} {S T : ℝ} (hST : S ≤ T)
    (path : WeightedHigherOrderPath base T) :
    ‖weightedHigherOrderPathTimeRestrict hST path‖ ≤ ‖path‖ := by
  apply (ContinuousMap.norm_le
    (weightedHigherOrderPathTimeRestrict hST path) (norm_nonneg path)).2
  intro t
  exact path.norm_coe_le_norm ⟨t.1, t.2.1, t.2.2.trans hST⟩

@[simp]
theorem weightedHigherOrderPathTimeRestrict_refl
    {base : ℕ} {T : ℝ} (path : WeightedHigherOrderPath base T) :
    weightedHigherOrderPathTimeRestrict (le_refl T) path = path := by
  apply ContinuousMap.ext
  intro t
  rfl

theorem weightedHigherOrderPathTimeRestrict_trans
    {base : ℕ} {R S T : ℝ} (hRS : R ≤ S) (hST : S ≤ T)
    (path : WeightedHigherOrderPath base T) :
    weightedHigherOrderPathTimeRestrict hRS
        (weightedHigherOrderPathTimeRestrict hST path) =
      weightedHigherOrderPathTimeRestrict (hRS.trans hST) path := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- Spatial restriction and time restriction are commuting receiver faces. -/
theorem higherOrderRestrictionPathToThree_timeRestrict
    (base : ℕ) (hbase : 2 ≤ base)
    {S T : ℝ} (hST : S ≤ T) (path : WeightedHigherOrderPath base T) :
    higherOrderRestrictionPathToThree base hbase
        (weightedHigherOrderPathTimeRestrict hST path) =
      weightedH3PathTimeRestrict hST
        (higherOrderRestrictionPathToThree base hbase path) := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- Endpoint projection of a retimed high path agrees with endpoint projection of its source on
the smaller aperture. -/
theorem weightedHigherOrderPathExtension_timeRestrict_of_mem
    {base : ℕ} {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (path : WeightedHigherOrderPath base T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    weightedHigherOrderPathExtension hS
        (weightedHigherOrderPathTimeRestrict hST path) t =
      weightedHigherOrderPathExtension hT path t := by
  rw [weightedHigherOrderPathExtension_of_mem hS _ ht,
    weightedHigherOrderPathExtension_of_mem hT _ ⟨ht.1, ht.2.trans hST⟩]
  rfl

/-- The high-order Volterra return reads only the retained past population. -/
theorem higherOrderDuhamelReturn_timeRestrict
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (path : WeightedHigherOrderPath base T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hS
          (weightedHigherOrderPathTimeRestrict hST path)) =
      higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hT path) := by
  unfold higherOrderDuhamelReturn
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hsS : s ∈ Icc (0 : ℝ) S := ⟨hs.1, hs.2.trans ht.2⟩
  have hext := weightedHigherOrderPathExtension_timeRestrict_of_mem
    hS hT hST path hsS
  unfold higherOrderDuhamelIntegrand
  split <;> simp only [hext]

theorem higherOrderDuhamelPath_timeRestrict
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (path : WeightedHigherOrderPath base T) :
    weightedHigherOrderPathTimeRestrict hST
        (higherOrderDuhamelPath base hbase nu hnu hT path) =
      higherOrderDuhamelPath base hbase nu hnu hS
        (weightedHigherOrderPathTimeRestrict hST path) := by
  apply ContinuousMap.ext
  intro t
  exact (higherOrderDuhamelReturn_timeRestrict
    base hbase nu hnu hS hT hST path t.2).symm

theorem higherOrderLinearHeatPath_timeRestrict
    (base : ℕ) (nu : ℝ≥0)
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    weightedHigherOrderPathTimeRestrict hST
        (higherOrderLinearHeatPath base nu hT initial) =
      higherOrderLinearHeatPath base nu hS initial := by
  rfl

/-- The complete high mild recurrence commutes through a smaller addressed aperture. -/
theorem higherOrderMildMap_timeRestrict
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (path : WeightedHigherOrderPath base T) :
    weightedHigherOrderPathTimeRestrict hST
        (higherOrderMildMap base hbase nu hnu hT initial path) =
      higherOrderMildMap base hbase nu hnu hS initial
        (weightedHigherOrderPathTimeRestrict hST path) := by
  apply ContinuousMap.ext
  intro t
  have hlinear := ContinuousMap.congr_fun
    (higherOrderLinearHeatPath_timeRestrict base nu hS hT hST initial) t
  have hduhamel := ContinuousMap.congr_fun
    (higherOrderDuhamelPath_timeRestrict base hbase nu hnu hS hT hST path) t
  exact congrArg₂ (fun left right => left - right) hlinear hduhamel

theorem isFixedPt_higherOrderMildMap_timeRestrict
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (path : WeightedHigherOrderPath base T)
    (hfixed : IsFixedPt
      (higherOrderMildMap base hbase nu hnu hT initial) path) :
    IsFixedPt (higherOrderMildMap base hbase nu hnu hS initial)
      (weightedHigherOrderPathTimeRestrict hST path) := by
  calc
    higherOrderMildMap base hbase nu hnu hS initial
        (weightedHigherOrderPathTimeRestrict hST path) =
      weightedHigherOrderPathTimeRestrict hST
        (higherOrderMildMap base hbase nu hnu hT initial path) :=
      (higherOrderMildMap_timeRestrict
        base hbase nu hnu hS hT hST initial path).symm
    _ = weightedHigherOrderPathTimeRestrict hST path :=
      congrArg (weightedHigherOrderPathTimeRestrict hST) hfixed

/-! ## The exact scalar dominance port -/

/-- The one-shot scalar condition under which the high restart aperture contains the native
`H³` aperture. -/
def NativeH3ApertureDominatesOrder (base : ℕ) : Prop :=
  higherOrderTameConstant base ≤ weightedLerayCoefficient

/-- Its exact complement is retained as an obstruction rather than erased by a fallback time. -/
def NativeH3ApertureOrderObstruction (base : ℕ) : Prop :=
  weightedLerayCoefficient < higherOrderTameConstant base

theorem nativeH3ApertureDominance_or_obstruction (base : ℕ) :
    NativeH3ApertureDominatesOrder base ∨
      NativeH3ApertureOrderObstruction base :=
  le_or_gt _ _

/-- The explicit restart time is antitone in its nonnegative nonlinear load. -/
theorem duhamelRestartTime_anti_load
    {nu load₁ load₂ : ℝ} (hnu : 0 < nu)
    (hload₁ : 0 ≤ load₁) (hload₂ : 0 ≤ load₂)
    (hload : load₁ ≤ load₂) :
    duhamelRestartTime nu load₂ ≤ duhamelRestartTime nu load₁ := by
  let d₁ : ℝ := 16 * (1 + nu) * (1 + load₁)
  let d₂ : ℝ := 16 * (1 + nu) * (1 + load₂)
  have hd₁ : 0 < d₁ := by dsimp [d₁]; positivity
  have hd₂ : 0 < d₂ := by dsimp [d₂]; positivity
  have hden : d₁ ≤ d₂ := by
    dsimp [d₁, d₂]
    have honeLoad : 1 + load₁ ≤ 1 + load₂ := by linarith
    exact mul_le_mul_of_nonneg_left
      honeLoad
      (mul_nonneg (by norm_num) (by linarith))
  have hinv : d₂⁻¹ ≤ d₁⁻¹ :=
    (inv_le_inv₀ hd₂ hd₁).2 hden
  have hinvNonneg₁ : 0 ≤ d₁⁻¹ := (inv_pos.mpr hd₁).le
  have hinvNonneg₂ : 0 ≤ d₂⁻¹ := (inv_pos.mpr hd₂).le
  unfold duhamelRestartTime duhamelRestartScale
  change 2 * nu * d₂⁻¹ ^ 2 ≤ 2 * nu * d₁⁻¹ ^ 2
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hinvNonneg₂ hinv 2)
    (mul_nonneg (by norm_num) hnu.le)

/-- Dominance of the high tame constant makes its nonlinear load no larger than the load used by
the native `H³` cap. -/
theorem higherOrderRestartLoad_le_weightedRestartLoadFromCap
    (base : ℕ) (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hdominance : NativeH3ApertureDominatesOrder base) :
    higherOrderRestartLoad base initial ≤
      weightedRestartLoadFromCap ‖initial‖ := by
  unfold higherOrderRestartLoad weightedRestartLoadFromCap
  have hR : 0 ≤ higherOrderRestartRadius initial :=
    (higherOrderRestartRadius_pos initial).le
  rw [show weightedRestartRadiusFromCap ‖initial‖ =
    higherOrderRestartRadius initial by rfl]
  exact mul_le_mul_of_nonneg_right hdominance hR

/-- Hence the entire native `H³` restart aperture is contained in the high aperture. -/
theorem weightedRestartTimeFromCap_le_higherOrderRestartTime
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hdominance : NativeH3ApertureDominatesOrder base) :
    weightedRestartTimeFromCap nu ‖initial‖ ≤
      higherOrderRestartTime base nu initial := by
  exact duhamelRestartTime_anti_load hnu
    (higherOrderRestartLoad_nonneg base initial)
    (weightedRestartLoadFromCap_nonneg (norm_nonneg initial))
    (higherOrderRestartLoad_le_weightedRestartLoadFromCap
      base initial hdominance)

/-- With the currently retained constants, every order through `H⁹` satisfies one-shot native
aperture dominance. -/
theorem nativeH3ApertureDominatesOrder_of_le_eight
    {base : ℕ} (hbase : base ≤ 8) :
    NativeH3ApertureDominatesOrder base := by
  have hpowNat : (2 : ℕ) ^ (base + 1) ≤ (2 : ℕ) ^ 9 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : (2 : ℝ) ^ (base + 1) ≤ (2 : ℝ) ^ 9 := by
    exact_mod_cast hpowNat
  have hE : 0 ≤ periodicH3EmbeddingConstant :=
    periodicH3EmbeddingConstant_nonneg
  unfold NativeH3ApertureDominatesOrder higherOrderTameConstant
  unfold weightedLerayCoefficient
  calc
    36 * (2 : ℝ) ^ (base + 1) * periodicH3EmbeddingConstant ≤
        36 * (2 : ℝ) ^ 9 * periodicH3EmbeddingConstant := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by norm_num)) hE
    _ ≤ 23328 * periodicH3EmbeddingConstant := by
      exact mul_le_mul_of_nonneg_right (by norm_num) hE

/-- The reciprocal-weight population has a nonzero zero-frequency face, so its native embedding
constant is strictly positive. -/
theorem periodicH3EmbeddingConstant_pos :
    0 < periodicH3EmbeddingConstant := by
  unfold periodicH3EmbeddingConstant
  rw [norm_pos_iff]
  intro hzero
  have hface := congrArg
    (fun state : PeriodicRealFourierL2 => state (0 : SpatialFrequency)) hzero
  change (Real.sqrt (periodicSobolevWeight 3 (0 : SpatialFrequency)))⁻¹ = 0 at hface
  simp [periodicSobolevWeight, torusStokesEigenvalue, frequencySquared] at hface

/-- At `base ≥ 9` the present one-shot constants genuinely reverse the dominance inequality.
This is an obstruction to the direct aperture-containment proof, not to a future iterated
persistence argument. -/
theorem nativeH3ApertureOrderObstruction_of_nine_le
    {base : ℕ} (hbase : 9 ≤ base) :
    NativeH3ApertureOrderObstruction base := by
  have hpowNat : (2 : ℕ) ^ 10 ≤ (2 : ℕ) ^ (base + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : (2 : ℝ) ^ 10 ≤ (2 : ℝ) ^ (base + 1) := by
    exact_mod_cast hpowNat
  have hcoefficient : (23328 : ℝ) < 36 * (2 : ℝ) ^ (base + 1) := by
    calc
      (23328 : ℝ) < 36 * (2 : ℝ) ^ 10 := by norm_num
      _ ≤ 36 * (2 : ℝ) ^ (base + 1) :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
  unfold NativeH3ApertureOrderObstruction
  unfold weightedLerayCoefficient higherOrderTameConstant
  exact mul_lt_mul_of_pos_right hcoefficient periodicH3EmbeddingConstant_pos

/-! ## The low--high tame receiver on one full aperture -/

/-- On an `H³`-controlled high path, the complete nonlinear path return is linear in the high
norm and controlled by the actual low path norm. -/
theorem norm_higherOrderDuhamelPath_le_tame_of_H3ControlledLift
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (high : WeightedHigherOrderPath base T) (low : WeightedH3Path T)
    (hlift : IsH3ControlledHigherOrderLift base hbase high low) :
    ‖higherOrderDuhamelPath base hbase nu hnu hT high‖ ≤
      higherOrderTameConstant base * ‖low‖ * ‖high‖ *
        duhamelApertureBudget nu T := by
  have hright : 0 ≤ higherOrderTameConstant base * ‖low‖ * ‖high‖ *
      duhamelApertureBudget nu T :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (higherOrderTameConstant_nonneg base) (norm_nonneg low))
        (norm_nonneg high))
      (duhamelApertureBudget_nonneg nu hT)
  apply (ContinuousMap.norm_le
    (higherOrderDuhamelPath base hbase nu hnu hT high) hright).2
  intro t
  rw [higherOrderDuhamelPath_apply]
  rcases t.2.1.eq_or_lt with hzero | htpos
  · have htzero : t.1 = 0 := hzero.symm
    rw [htzero]
    simpa [higherOrderDuhamelReturn] using hright
  · have hlow : ∀ s ∈ Icc (0 : ℝ) t.1,
        ‖periodicVectorWeightedRestrictToThree (base + 1) (by omega)
          (weightedHigherOrderPathExtension hT high s)‖ ≤ ‖low‖ := by
      intro s hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.2.2⟩
      rw [weightedHigherOrderPathExtension_of_mem hT high hsT]
      have hface := ContinuousMap.congr_fun hlift ⟨s, hsT⟩
      change periodicVectorWeightedRestrictToThree (base + 1) (by omega)
          (high ⟨s, hsT⟩) = low ⟨s, hsT⟩ at hface
      rw [hface]
      exact norm_weightedPath_apply_le low ⟨s, hsT⟩
    have hhigh : ∀ s ∈ Icc (0 : ℝ) t.1,
        ‖weightedHigherOrderPathExtension hT high s‖ ≤ ‖high‖ := by
      intro s _hs
      exact norm_weightedHigherOrderPathExtension_le hT high s
    have hpoint := norm_intervalIntegral_higherOrderDuhamelIntegrand_le
      base hbase nu hnu htpos ‖low‖ ‖high‖
      (weightedHigherOrderPathExtension hT high) hlow hhigh
    have hbudget := duhamelApertureBudget_mono nu hnu t.2.2
    calc
      ‖higherOrderDuhamelReturn base hbase nu hnu t.1
          (weightedHigherOrderPathExtension hT high)‖ ≤
          higherOrderTameConstant base * ‖low‖ * ‖high‖ *
            duhamelApertureBudget nu t.1 := by
        simpa only [higherOrderDuhamelReturn, duhamelApertureBudget] using hpoint
      _ ≤ higherOrderTameConstant base * ‖low‖ * ‖high‖ *
          duhamelApertureBudget nu T := by
        exact mul_le_mul_of_nonneg_left hbudget
          (mul_nonneg
            (mul_nonneg (higherOrderTameConstant_nonneg base) (norm_nonneg low))
            (norm_nonneg high))

/-- A fixed high path therefore satisfies an affine, rather than quadratic, norm inequality. -/
theorem norm_fixedPoint_higherOrderMildMap_le_initial_add_tame
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (high : WeightedHigherOrderPath base T) (low : WeightedH3Path T)
    (hfixed : IsFixedPt
      (higherOrderMildMap base hbase nu hnu hT initial) high)
    (hlift : IsH3ControlledHigherOrderLift base hbase high low) :
    ‖high‖ ≤ ‖initial‖ +
      (higherOrderTameConstant base * ‖low‖ *
        duhamelApertureBudget nu T) * ‖high‖ := by
  have hlinear := norm_higherOrderLinearHeatPath_le base nu hT initial
  have hduhamel := norm_higherOrderDuhamelPath_le_tame_of_H3ControlledLift
    base hbase nu hnu hT high low hlift
  calc
    ‖high‖ = ‖higherOrderMildMap base hbase nu hnu hT initial high‖ :=
      congrArg norm hfixed.symm
    _ ≤ ‖higherOrderLinearHeatPath base nu hT initial‖ +
        ‖higherOrderDuhamelPath base hbase nu hnu hT high‖ := by
      exact norm_sub_le _ _
    _ ≤ ‖initial‖ +
        higherOrderTameConstant base * ‖low‖ * ‖high‖ *
          duhamelApertureBudget nu T :=
      add_le_add hlinear hduhamel
    _ = ‖initial‖ +
        (higherOrderTameConstant base * ‖low‖ *
          duhamelApertureBudget nu T) * ‖high‖ := by ring

/-- On the native restart time, scalar dominance and the native path-ball receipt force the
mixed low--high factor below one half. -/
theorem higherOrderTameFactor_lt_half_on_nativeRestart
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (low : WeightedH3Path (weightedRestartTimeFromCap nu ‖initial‖))
    (hlow : ‖low‖ ≤ weightedRestartRadiusFromCap ‖initial‖)
    (hdominance : NativeH3ApertureDominatesOrder base) :
    higherOrderTameConstant base * ‖low‖ *
        duhamelApertureBudget (Real.toNNReal nu)
          (weightedRestartTimeFromCap nu ‖initial‖) < 1 / 2 := by
  let R := weightedRestartRadiusFromCap ‖initial‖
  let budget := duhamelApertureBudget (Real.toNNReal nu)
    (weightedRestartTimeFromCap nu ‖initial‖)
  have hR : 0 ≤ R := (weightedRestartRadiusFromCap_pos (norm_nonneg initial)).le
  have hbudget : 0 ≤ budget := duhamelApertureBudget_nonneg _
    (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le
  have hpair : higherOrderTameConstant base * ‖low‖ ≤
      weightedLerayCoefficient * R := by
    exact mul_le_mul hdominance hlow (norm_nonneg low)
      weightedLerayCoefficient_nonneg
  have hscaled := mul_le_mul_of_nonneg_right hpair hbudget
  have hcontract :=
    two_weightedDuhamelCoefficient_mul_radiusFromCap_lt_one
      hnu (norm_nonneg initial)
  have hidentify : weightedLerayCoefficient * R * budget =
      weightedDuhamelCoefficient nu
        (weightedRestartTimeFromCap nu ‖initial‖) * R := by
    dsimp [budget, R]
    simp only [weightedDuhamelCoefficient, duhamelApertureBudget,
      Real.coe_toNNReal _ hnu.le]
    ring
  rw [hidentify] at hscaled
  change higherOrderTameConstant base * ‖low‖ * budget < 1 / 2
  nlinarith

/-- Absorbing the strict half-factor sharpens a controlled fixed path to twice its initial norm. -/
theorem norm_fixedPoint_higherOrderMildMap_le_two_initial
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (high : WeightedHigherOrderPath base
      (weightedRestartTimeFromCap nu ‖initial‖))
    (low : WeightedH3Path (weightedRestartTimeFromCap nu ‖initial‖))
    (hfixed : IsFixedPt
      (higherOrderMildMap base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le initial) high)
    (hlift : IsH3ControlledHigherOrderLift base hbase high low)
    (hlow : ‖low‖ ≤ weightedRestartRadiusFromCap ‖initial‖)
    (hdominance : NativeH3ApertureDominatesOrder base) :
    ‖high‖ ≤ 2 * ‖initial‖ := by
  have haffine := norm_fixedPoint_higherOrderMildMap_le_initial_add_tame
    base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
    (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le
    initial high low hfixed hlift
  have hfactor := higherOrderTameFactor_lt_half_on_nativeRestart
    base hnu initial low hlow hdominance
  have hscaled :
      (higherOrderTameConstant base * ‖low‖ *
          duhamelApertureBudget (Real.toNNReal nu)
            (weightedRestartTimeFromCap nu ‖initial‖)) * ‖high‖ ≤
        (1 / 2 : ℝ) * ‖high‖ :=
    mul_le_mul_of_nonneg_right hfactor.le (norm_nonneg high)
  nlinarith [norm_nonneg initial, norm_nonneg high]

/-! ## Full native-aperture persistence -/

/-- Under the exact scalar dominance port, an independently constructed high path persists on
the *entire* native `H³` restart aperture, is fixed by the high mild recurrence there, and has
exactly the independently returned native path as its `H³` receiver. -/
theorem exists_higherOrderPersistence_on_full_nativeH3RestartAperture_of_dominance
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hdominance : NativeH3ApertureDominatesOrder base) :
    ∃ high : WeightedHigherOrderPath base
          (weightedRestartTimeFromCap nu ‖initial‖),
      ∃ low : WeightedH3Path (weightedRestartTimeFromCap nu ‖initial‖),
        IsFixedPt
          (higherOrderMildMap base hbase
            (Real.toNNReal nu) (real_toNNReal_pos hnu)
            (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le initial) high ∧
        IsFixedPt
          (weightedMildRestartMap nu ‖initial‖ hnu (norm_nonneg initial)
            (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)) low ∧
        IsH3ControlledHigherOrderLift base hbase high low ∧
        ‖high‖ ≤ 2 * ‖initial‖ ∧
        ‖low‖ ≤ weightedRestartRadiusFromCap ‖initial‖ ∧
        high ⟨0, ⟨le_rfl,
          (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le⟩⟩ = initial ∧
        low ⟨0, ⟨le_rfl,
          (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le⟩⟩ =
            periodicVectorWeightedRestrictToThree
              (base + 1) (by omega) initial := by
  let Tlow := weightedRestartTimeFromCap nu ‖initial‖
  let Thigh := higherOrderRestartTime base nu initial
  let hTlow : 0 ≤ Tlow :=
    (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le
  let hThigh : 0 ≤ Thigh :=
    (higherOrderRestartTime_pos base hnu initial).le
  have htime : Tlow ≤ Thigh :=
    weightedRestartTimeFromCap_le_higherOrderRestartTime
      base hnu initial hdominance
  obtain ⟨highSource, hhighSourceNorm, hhighSourceFixed, hhighSourceZero⟩ :=
    exists_higherOrderMildRestart_fixedPoint base hbase hnu initial
  have hinitialLow :
      ‖periodicVectorWeightedRestrictToThree
        (base + 1) (by omega) initial‖ ≤ ‖initial‖ :=
    norm_periodicVectorWeightedRestrictToThree_le
      (base + 1) (by omega) initial
  obtain ⟨low, hlowNorm, hlowFixed, hlowZero⟩ :=
    exists_weightedMildRestart_fixedPoint
      hnu (norm_nonneg initial)
      (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)
      hinitialLow
  let high : WeightedHigherOrderPath base Tlow :=
    weightedHigherOrderPathTimeRestrict htime highSource
  have hhighFixed : IsFixedPt
      (higherOrderMildMap base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hTlow initial) high := by
    exact isFixedPt_higherOrderMildMap_timeRestrict
      base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hTlow hThigh htime initial highSource hhighSourceFixed
  have hreceiverFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hTlow
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial))
      (higherOrderRestrictionPathToThree base hbase high) :=
    isFixedPt_restrict_higherOrderMildMap_to_weighted
      base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hTlow initial high hhighFixed
  have hhighNormRadius : ‖high‖ ≤ weightedRestartRadiusFromCap ‖initial‖ := by
    calc
      ‖high‖ ≤ ‖highSource‖ :=
        norm_weightedHigherOrderPathTimeRestrict_le htime highSource
      _ ≤ higherOrderRestartRadius initial := hhighSourceNorm
      _ = weightedRestartRadiusFromCap ‖initial‖ := by rfl
  have hreceiverNorm :
      ‖higherOrderRestrictionPathToThree base hbase high‖ ≤
        weightedRestartRadiusFromCap ‖initial‖ :=
    (norm_higherOrderRestrictionPathToThree_le base hbase high).trans hhighNormRadius
  have hlift : IsH3ControlledHigherOrderLift base hbase high low := by
    exact isFixedPt_weightedMildMap_eq_of_mem_restartBall
      (Real.toNNReal nu) (real_toNNReal_pos hnu) hTlow
      (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)
      (higherOrderRestrictionPathToThree base hbase high) low
      hreceiverFixed hlowFixed hreceiverNorm hlowNorm
      (by
        simpa only [Real.coe_toNNReal _ hnu.le, Tlow] using
          two_weightedDuhamelCoefficient_mul_radiusFromCap_lt_one
            hnu (norm_nonneg initial))
  have hhighSharp : ‖high‖ ≤ 2 * ‖initial‖ :=
    norm_fixedPoint_higherOrderMildMap_le_two_initial
      base hbase hnu initial high low hhighFixed hlift hlowNorm hdominance
  have hhighZero : high ⟨0, ⟨le_rfl, hTlow⟩⟩ = initial := by
    change highSource ⟨0, ⟨le_rfl, hTlow.trans htime⟩⟩ = initial
    have hzero := hhighSourceZero
    simpa only [Thigh, hThigh] using hzero
  exact ⟨high, low, hhighFixed, hlowFixed, hlift, hhighSharp, hlowNorm,
    hhighZero, hlowZero⟩

/-- Unconditional one-shot persistence through `H⁹`, obtained by discharging the exact scalar
dominance port from `base ≤ 8`. -/
theorem exists_higherOrderPersistence_on_full_nativeH3RestartAperture
    (base : ℕ) (hbase : 2 ≤ base) (hbaseEight : base ≤ 8)
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    ∃ high : WeightedHigherOrderPath base
          (weightedRestartTimeFromCap nu ‖initial‖),
      ∃ low : WeightedH3Path (weightedRestartTimeFromCap nu ‖initial‖),
        IsFixedPt
          (higherOrderMildMap base hbase
            (Real.toNNReal nu) (real_toNNReal_pos hnu)
            (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le initial) high ∧
        IsFixedPt
          (weightedMildRestartMap nu ‖initial‖ hnu (norm_nonneg initial)
            (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)) low ∧
        IsH3ControlledHigherOrderLift base hbase high low ∧
        ‖high‖ ≤ 2 * ‖initial‖ ∧
        ‖low‖ ≤ weightedRestartRadiusFromCap ‖initial‖ ∧
        high ⟨0, ⟨le_rfl,
          (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le⟩⟩ = initial ∧
        low ⟨0, ⟨le_rfl,
          (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le⟩⟩ =
            periodicVectorWeightedRestrictToThree
              (base + 1) (by omega) initial :=
  exists_higherOrderPersistence_on_full_nativeH3RestartAperture_of_dominance
    base hbase hnu initial
      (nativeH3ApertureDominatesOrder_of_le_eight hbaseEight)

section Audit

#print axioms higherOrderDuhamelReturn_timeRestrict
#print axioms higherOrderMildMap_timeRestrict
#print axioms duhamelRestartTime_anti_load
#print axioms nativeH3ApertureDominatesOrder_of_le_eight
#print axioms nativeH3ApertureOrderObstruction_of_nine_le
#print axioms norm_higherOrderDuhamelPath_le_tame_of_H3ControlledLift
#print axioms norm_fixedPoint_higherOrderMildMap_le_two_initial
#print axioms exists_higherOrderPersistence_on_full_nativeH3RestartAperture_of_dominance
#print axioms exists_higherOrderPersistence_on_full_nativeH3RestartAperture

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderPersistence
