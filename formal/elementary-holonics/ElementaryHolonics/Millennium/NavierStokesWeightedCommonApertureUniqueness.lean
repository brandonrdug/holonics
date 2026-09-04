import ElementaryHolonics.Millennium.NavierStokesWeightedHigherOrderMildRestart

/-!
# Common-aperture uniqueness for the weighted mild recurrence

**[proved-derived]** A higher-order fixed path and the established native `H³` fixed path are
initially returned on generally different positive apertures.  This owner retains their actual
overlap rather than identifying those two time populations by assertion.

Restriction along an inclusion `[0,S] ⊆ [0,T]` is nonexpanding and commutes exactly with the
linear heat word, the Volterra return, and hence the complete weighted mild map.  The native
two-path estimate then makes fixed points unique inside any common restart ball whose explicit
factor is below one.  Applying this at the minimum of the high-order and native `H³` apertures
identifies the spatial restriction of the high fixed point with the independently constructed
`H³` fixed point on every shared time face.

No continuation past either local aperture is asserted here.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedCommonApertureUniqueness

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesQuadraticContraction
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
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

/-! ## The addressed inclusion of one closed time aperture into another -/

/-- The continuous inclusion of a smaller closed aperture into a larger one. -/
def weightedTimeApertureInclusion
    {S T : ℝ} (hST : S ≤ T) : C(Icc (0 : ℝ) S, Icc (0 : ℝ) T) where
  toFun := fun t ↦ ⟨t.1, t.2.1, t.2.2.trans hST⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem weightedTimeApertureInclusion_apply
    {S T : ℝ} (hST : S ≤ T) (t : Icc (0 : ℝ) S) :
    (weightedTimeApertureInclusion hST t).1 = t.1 :=
  rfl

/-- Restrict a native `H³` path by precomposition with the addressed aperture inclusion. -/
def weightedH3PathTimeRestrict
    {S T : ℝ} (hST : S ≤ T) (path : WeightedH3Path T) : WeightedH3Path S :=
  path.comp (weightedTimeApertureInclusion hST)

@[simp]
theorem weightedH3PathTimeRestrict_apply
    {S T : ℝ} (hST : S ≤ T) (path : WeightedH3Path T)
    (t : Icc (0 : ℝ) S) :
    weightedH3PathTimeRestrict hST path t =
      path ⟨t.1, t.2.1, t.2.2.trans hST⟩ :=
  rfl

/-- Time restriction cannot enlarge the compact supremum receiver. -/
theorem norm_weightedH3PathTimeRestrict_le
    {S T : ℝ} (hST : S ≤ T) (path : WeightedH3Path T) :
    ‖weightedH3PathTimeRestrict hST path‖ ≤ ‖path‖ := by
  apply (ContinuousMap.norm_le
    (weightedH3PathTimeRestrict hST path) (norm_nonneg path)).2
  intro t
  exact path.norm_coe_le_norm
    ⟨t.1, t.2.1, t.2.2.trans hST⟩

/-- Restriction along the identity inclusion changes no addressed occurrence. -/
@[simp]
theorem weightedH3PathTimeRestrict_refl
    {T : ℝ} (path : WeightedH3Path T) :
    weightedH3PathTimeRestrict (le_refl T) path = path := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- Nested restriction retains the composite inclusion rather than introducing a second path. -/
theorem weightedH3PathTimeRestrict_trans
    {R S T : ℝ} (hRS : R ≤ S) (hST : S ≤ T)
    (path : WeightedH3Path T) :
    weightedH3PathTimeRestrict hRS
        (weightedH3PathTimeRestrict hST path) =
      weightedH3PathTimeRestrict (hRS.trans hST) path := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The initial face is retained exactly by every addressed time restriction. -/
@[simp]
theorem weightedH3PathTimeRestrict_zero
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (path : WeightedH3Path T) :
    weightedH3PathTimeRestrict hST path ⟨0, ⟨le_rfl, hS⟩⟩ =
      path ⟨0, ⟨le_rfl, hS.trans hST⟩⟩ :=
  rfl

/-- On the smaller aperture, endpoint projection of the restricted path is literally endpoint
projection of the source path. -/
theorem weightedPathExtension_timeRestrict_of_mem
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (path : WeightedH3Path T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    weightedPathExtension hS (weightedH3PathTimeRestrict hST path) t =
      weightedPathExtension hT path t := by
  rw [weightedPathExtension_of_mem hS _ ht,
    weightedPathExtension_of_mem hT _ ⟨ht.1, ht.2.trans hST⟩]
  rfl

/-! ## Exact Volterra causality under time restriction -/

/-- The variable-terminal nonlinear return only reads source history at times no later than its
terminal face, so restricting a larger path does not alter any return on the smaller aperture. -/
theorem weightedDuhamelReturn_timeRestrict
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (path : WeightedH3Path T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    weightedDuhamelReturn nu hnu hS
        (weightedH3PathTimeRestrict hST path) t =
      weightedDuhamelReturn nu hnu hT path t := by
  unfold weightedDuhamelReturn
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hsS : s ∈ Icc (0 : ℝ) S :=
    ⟨hs.1, hs.2.trans ht.2⟩
  have hext := weightedPathExtension_timeRestrict_of_mem
    hS hT hST path hsS
  unfold weightedDuhamelIntegrand
  split <;> simp only [hext]

/-- The complete nonlinear path commutes with time restriction. -/
theorem weightedDuhamelPath_timeRestrict
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (path : WeightedH3Path T) :
    weightedH3PathTimeRestrict hST
        (weightedDuhamelPath nu hnu hT path) =
      weightedDuhamelPath nu hnu hS
        (weightedH3PathTimeRestrict hST path) := by
  apply ContinuousMap.ext
  intro t
  exact (weightedDuhamelReturn_timeRestrict
    nu hnu hS hT hST path t.2).symm

/-- The same-order linear heat word commutes definitionally with time restriction. -/
theorem weightedLinearHeatPath_timeRestrict
    (nu : ℝ≥0) {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) :
    weightedH3PathTimeRestrict hST
        (weightedLinearHeatPath nu hT initial) =
      weightedLinearHeatPath nu hS initial := by
  rfl

/-- **Exact retiming intertwiner.** The complete mild recurrence commutes through every addressed
closed subaperture. -/
theorem weightedMildMap_timeRestrict
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) (path : WeightedH3Path T) :
    weightedH3PathTimeRestrict hST
        (weightedMildMap nu hnu hT initial path) =
      weightedMildMap nu hnu hS initial
        (weightedH3PathTimeRestrict hST path) := by
  apply ContinuousMap.ext
  intro t
  change
    weightedLinearHeatPath nu hT initial
          ⟨t.1, t.2.1, t.2.2.trans hST⟩ -
        weightedDuhamelPath nu hnu hT path
          ⟨t.1, t.2.1, t.2.2.trans hST⟩ =
      weightedLinearHeatPath nu hS initial t -
        weightedDuhamelPath nu hnu hS
          (weightedH3PathTimeRestrict hST path) t
  have hlinear := ContinuousMap.congr_fun
    (weightedLinearHeatPath_timeRestrict nu hS hT hST initial) t
  have hduhamel := ContinuousMap.congr_fun
    (weightedDuhamelPath_timeRestrict nu hnu hS hT hST path) t
  exact congrArg₂ (fun left right => left - right) hlinear hduhamel

/-- A fixed path on a larger aperture remains a fixed path of the same Volterra recurrence on
every smaller aperture. -/
theorem isFixedPt_weightedMildMap_timeRestrict
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) (path : WeightedH3Path T)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) path) :
    IsFixedPt (weightedMildMap nu hnu hS initial)
      (weightedH3PathTimeRestrict hST path) := by
  calc
    weightedMildMap nu hnu hS initial
        (weightedH3PathTimeRestrict hST path) =
      weightedH3PathTimeRestrict hST
        (weightedMildMap nu hnu hT initial path) :=
      (weightedMildMap_timeRestrict
        nu hnu hS hT hST initial path).symm
    _ = weightedH3PathTimeRestrict hST path :=
      congrArg (weightedH3PathTimeRestrict hST) hfixed

/-! ## Fixed-point uniqueness inside a common native path ball -/

/-- Pairwise strictness of the exact Duhamel separation forces two fixed paths to coincide. -/
theorem isFixedPt_weightedMildMap_eq_of_pair_factor_lt_one
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3)
    (u v : WeightedH3Path T)
    (hu : IsFixedPt (weightedMildMap nu hnu hT initial) u)
    (hv : IsFixedPt (weightedMildMap nu hnu hT initial) v)
    (hfactor : weightedDuhamelCoefficient (nu : ℝ) T *
        (‖u‖ + ‖v‖) < 1) :
    u = v := by
  have hdifference := norm_weightedMildMap_remainder_sub_le
    nu hnu hT initial u v
  have hrearrange :
      ((weightedMildMap nu hnu hT initial u -
          weightedLinearHeatPath nu hT initial) -
        (weightedMildMap nu hnu hT initial v -
          weightedLinearHeatPath nu hT initial)) =
        weightedMildMap nu hnu hT initial u -
          weightedMildMap nu hnu hT initial v := by
    abel
  rw [hrearrange, hu, hv] at hdifference
  by_cases hzero : ‖u - v‖ = 0
  · exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · have hpositive : 0 < ‖u - v‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hstrict :
        weightedDuhamelCoefficient (nu : ℝ) T * (‖u‖ + ‖v‖) * ‖u - v‖ <
          ‖u - v‖ := by
      simpa only [one_mul] using
        (mul_lt_mul_of_pos_right hfactor hpositive)
    exact False.elim ((not_lt_of_ge hdifference) hstrict)

/-- The explicit common-ball factor supplies the pairwise strictness needed above. -/
theorem isFixedPt_weightedMildMap_eq_of_mem_restartBall
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T R : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3)
    (u v : WeightedH3Path T)
    (hu : IsFixedPt (weightedMildMap nu hnu hT initial) u)
    (hv : IsFixedPt (weightedMildMap nu hnu hT initial) v)
    (huR : ‖u‖ ≤ R) (hvR : ‖v‖ ≤ R)
    (hcontract : 2 * weightedDuhamelCoefficient (nu : ℝ) T * R < 1) :
    u = v := by
  apply isFixedPt_weightedMildMap_eq_of_pair_factor_lt_one
    nu hnu hT initial u v hu hv
  have hsum : ‖u‖ + ‖v‖ ≤ 2 * R := by linarith
  have hA : 0 ≤ weightedDuhamelCoefficient (nu : ℝ) T :=
    weightedDuhamelCoefficient_nonneg hT
  calc
    weightedDuhamelCoefficient (nu : ℝ) T * (‖u‖ + ‖v‖) ≤
        weightedDuhamelCoefficient (nu : ℝ) T * (2 * R) :=
      mul_le_mul_of_nonneg_left hsum hA
    _ = 2 * weightedDuhamelCoefficient (nu : ℝ) T * R := by ring
    _ < 1 := hcontract

/-! ## The actual common high/native aperture -/

/-- The retained time population shared by the arbitrary-order and native `H³` Banach returns. -/
def weightedHigherOrderCommonRestartTime
    (base : ℕ) (nu : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) : ℝ :=
  min (higherOrderRestartTime base nu initial)
    (weightedRestartTimeFromCap nu ‖initial‖)

theorem weightedHigherOrderCommonRestartTime_pos
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    0 < weightedHigherOrderCommonRestartTime base nu initial := by
  unfold weightedHigherOrderCommonRestartTime
  exact lt_min
    (higherOrderRestartTime_pos base hnu initial)
    (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial))

theorem weightedHigherOrderCommonRestartTime_le_high
    (base : ℕ) (nu : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    weightedHigherOrderCommonRestartTime base nu initial ≤
      higherOrderRestartTime base nu initial :=
  min_le_left _ _

theorem weightedHigherOrderCommonRestartTime_le_weighted
    (base : ℕ) (nu : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    weightedHigherOrderCommonRestartTime base nu initial ≤
      weightedRestartTimeFromCap nu ‖initial‖ :=
  min_le_right _ _

/-- The native integrated coefficient is monotone under enlargement of a nonnegative time
aperture. -/
theorem weightedDuhamelCoefficient_mono_time
    {nu : ℝ} (hnu : 0 < nu) {S T : ℝ} (hST : S ≤ T) :
    weightedDuhamelCoefficient nu S ≤ weightedDuhamelCoefficient nu T := by
  have hbudget := duhamelApertureBudget_mono
    (Real.toNNReal nu) (real_toNNReal_pos hnu) hST
  have hscaled := mul_le_mul_of_nonneg_left
    hbudget weightedLerayCoefficient_nonneg
  simpa only [weightedDuhamelCoefficient, duhamelApertureBudget,
    Real.coe_toNNReal _ hnu.le] using hscaled

/-- The minimum aperture inherits the native common-ball strict contraction receipt. -/
theorem two_weightedDuhamelCoefficient_mul_radius_common_lt_one
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    2 * weightedDuhamelCoefficient nu
          (weightedHigherOrderCommonRestartTime base nu initial) *
        weightedRestartRadiusFromCap ‖initial‖ < 1 := by
  have hcoefficient := weightedDuhamelCoefficient_mono_time hnu
    (weightedHigherOrderCommonRestartTime_le_weighted base nu initial)
  have hR : 0 ≤ weightedRestartRadiusFromCap ‖initial‖ :=
    (weightedRestartRadiusFromCap_pos (norm_nonneg initial)).le
  calc
    2 * weightedDuhamelCoefficient nu
          (weightedHigherOrderCommonRestartTime base nu initial) *
        weightedRestartRadiusFromCap ‖initial‖ ≤
      2 * weightedDuhamelCoefficient nu
          (weightedRestartTimeFromCap nu ‖initial‖) *
        weightedRestartRadiusFromCap ‖initial‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoefficient (by norm_num)) hR
    _ < 1 :=
      two_weightedDuhamelCoefficient_mul_radiusFromCap_lt_one
        hnu (norm_nonneg initial)

/-! ## Identification of independently returned paths on the shared aperture -/

/-- A high fixed path and a native `H³` fixed path below their common radius have identical
`H³` histories on the minimum of their two returned apertures. -/
theorem higherOrderRestriction_eq_weightedPath_on_commonAperture
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (high : WeightedHigherOrderPath base
      (higherOrderRestartTime base nu initial))
    (low : WeightedH3Path (weightedRestartTimeFromCap nu ‖initial‖))
    (hhighFixed : IsFixedPt
      (higherOrderMildRestartMap base hbase nu hnu initial) high)
    (hlowFixed : IsFixedPt
      (weightedMildRestartMap nu ‖initial‖ hnu (norm_nonneg initial)
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)) low)
    (hhighNorm : ‖high‖ ≤ higherOrderRestartRadius initial)
    (hlowNorm : ‖low‖ ≤ weightedRestartRadiusFromCap ‖initial‖) :
    weightedH3PathTimeRestrict
        (weightedHigherOrderCommonRestartTime_le_high base nu initial)
        (higherOrderRestrictionPathToThree base hbase high) =
      weightedH3PathTimeRestrict
        (weightedHigherOrderCommonRestartTime_le_weighted base nu initial) low := by
  let common := weightedHigherOrderCommonRestartTime base nu initial
  let hcommon : 0 ≤ common :=
    (weightedHigherOrderCommonRestartTime_pos base hnu initial).le
  let hhighTime : 0 ≤ higherOrderRestartTime base nu initial :=
    (higherOrderRestartTime_pos base hnu initial).le
  let hlowTime : 0 ≤ weightedRestartTimeFromCap nu ‖initial‖ :=
    (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le
  let highReceiver := higherOrderRestrictionPathToThree base hbase high
  let highCommon := weightedH3PathTimeRestrict
    (weightedHigherOrderCommonRestartTime_le_high base nu initial) highReceiver
  let lowCommon := weightedH3PathTimeRestrict
    (weightedHigherOrderCommonRestartTime_le_weighted base nu initial) low
  have hhighReceiverFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hhighTime
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial))
      highReceiver := by
    exact isFixedPt_restrict_higherOrderMildMap_to_weighted
      base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hhighTime initial high hhighFixed
  have hhighCommonFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hcommon
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial))
      highCommon := by
    exact isFixedPt_weightedMildMap_timeRestrict
      (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hcommon hhighTime
      (weightedHigherOrderCommonRestartTime_le_high base nu initial)
      (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)
      highReceiver hhighReceiverFixed
  have hlowCommonFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hcommon
        (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial))
      lowCommon := by
    exact isFixedPt_weightedMildMap_timeRestrict
      (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hcommon hlowTime
      (weightedHigherOrderCommonRestartTime_le_weighted base nu initial)
      (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)
      low hlowFixed
  have hhighCommonNorm : ‖highCommon‖ ≤
      weightedRestartRadiusFromCap ‖initial‖ := by
    calc
      ‖highCommon‖ ≤ ‖highReceiver‖ :=
        norm_weightedH3PathTimeRestrict_le _ _
      _ ≤ ‖high‖ :=
        norm_higherOrderRestrictionPathToThree_le base hbase high
      _ ≤ higherOrderRestartRadius initial := hhighNorm
      _ = weightedRestartRadiusFromCap ‖initial‖ := by
        rfl
  have hlowCommonNorm : ‖lowCommon‖ ≤
      weightedRestartRadiusFromCap ‖initial‖ :=
    (norm_weightedH3PathTimeRestrict_le _ low).trans hlowNorm
  exact isFixedPt_weightedMildMap_eq_of_mem_restartBall
    (Real.toNNReal nu) (real_toNNReal_pos hnu) hcommon
    (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)
    highCommon lowCommon hhighCommonFixed hlowCommonFixed
    hhighCommonNorm hlowCommonNorm
    (by
      simpa only [Real.coe_toNNReal _ hnu.le, common] using
        two_weightedDuhamelCoefficient_mul_radius_common_lt_one
          base hnu initial)

/-- **Independent Banach returns agree on overlap.**  The existing high-order and native `H³`
constructors can be chosen simultaneously, and their two independently generated paths are
identified on every face of the exact common aperture. -/
theorem exists_compatible_higherOrder_and_weightedMildRestart
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    ∃ high : WeightedHigherOrderPath base
          (higherOrderRestartTime base nu initial),
      ∃ low : WeightedH3Path (weightedRestartTimeFromCap nu ‖initial‖),
        ‖high‖ ≤ higherOrderRestartRadius initial ∧
        IsFixedPt (higherOrderMildRestartMap base hbase nu hnu initial) high ∧
        ‖low‖ ≤ weightedRestartRadiusFromCap ‖initial‖ ∧
        IsFixedPt
          (weightedMildRestartMap nu ‖initial‖ hnu (norm_nonneg initial)
            (periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial)) low ∧
        weightedH3PathTimeRestrict
            (weightedHigherOrderCommonRestartTime_le_high base nu initial)
            (higherOrderRestrictionPathToThree base hbase high) =
          weightedH3PathTimeRestrict
            (weightedHigherOrderCommonRestartTime_le_weighted base nu initial) low ∧
        high ⟨0, ⟨le_rfl, (higherOrderRestartTime_pos base hnu initial).le⟩⟩ = initial ∧
        low ⟨0, ⟨le_rfl,
          (weightedRestartTimeFromCap_pos hnu (norm_nonneg initial)).le⟩⟩ =
            periodicVectorWeightedRestrictToThree
              (base + 1) (by omega) initial := by
  obtain ⟨high, hhighNorm, hhighFixed, hhighZero⟩ :=
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
  refine ⟨high, low, hhighNorm, hhighFixed, hlowNorm, hlowFixed, ?_,
    hhighZero, hlowZero⟩
  exact higherOrderRestriction_eq_weightedPath_on_commonAperture
    base hbase hnu initial high low hhighFixed hlowFixed hhighNorm hlowNorm

section Audit

#print axioms weightedDuhamelReturn_timeRestrict
#print axioms weightedMildMap_timeRestrict
#print axioms isFixedPt_weightedMildMap_eq_of_mem_restartBall
#print axioms higherOrderRestriction_eq_weightedPath_on_commonAperture
#print axioms exists_compatible_higherOrder_and_weightedMildRestart

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedCommonApertureUniqueness
