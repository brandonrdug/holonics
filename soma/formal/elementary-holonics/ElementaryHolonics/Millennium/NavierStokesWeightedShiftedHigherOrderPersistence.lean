import ElementaryHolonics.Millennium.NavierStokesWeightedHigherOrderPersistence

/-!
# Shifted higher-order persistence along one native H³ aperture

**[proved-derived]** This owner turns the local arbitrary-order mild return into an addressed
continuation step based at an arbitrary time face of an already returned native `H³` path.
Time translation preserves the complete Volterra population: the earlier history is carried by
the heat semigroup and the newly exposed tail is exactly the local Duhamel return.

The resulting shifted high segment is identified with the shifted native path on a strictly
positive compatibility aperture.  Its size is selected from the actual high endpoint norm and a
declared bound for the already existing low path.  Successive compatible segments can therefore
be glued without assuming their equality.  The final section isolates the only remaining
quantitative obstruction to a finite cover of the full native aperture: a uniform positive lower
bound for these state-dependent shifted apertures (equivalently, a finite bound for the high
endpoint population).  No such bound is inferred from local existence alone.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedShiftedHigherOrderPersistence

open Soma.Holonics.Millennium.NavierStokesDuhamelKernelIntegral
open Soma.Holonics.Millennium.NavierStokesDuhamelRestartTime
open Soma.Holonics.Millennium.NavierStokesWeightedCommonApertureUniqueness
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderDuhamelLift
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Addressed time translation -/

/-- Translate a native path based at `a` back to a local aperture `[0,S]`. -/
def weightedH3PathTimeShift
    {T : ℝ} (path : WeightedH3Path T) (a S : ℝ)
    (ha : 0 ≤ a) (haS : a + S ≤ T) : WeightedH3Path S where
  toFun := fun t ↦ path ⟨a + t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  continuous_toFun := path.continuous.comp
    ((continuous_const.add continuous_subtype_val).subtype_mk _)

@[simp]
theorem weightedH3PathTimeShift_apply
    {T : ℝ} (path : WeightedH3Path T) (a S : ℝ)
    (ha : 0 ≤ a) (haS : a + S ≤ T) (t : Icc (0 : ℝ) S) :
    weightedH3PathTimeShift path a S ha haS t =
      path ⟨a + t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ :=
  rfl

/-- Translation cannot enlarge the supremum receiver of the source path. -/
theorem norm_weightedH3PathTimeShift_le
    {T : ℝ} (path : WeightedH3Path T) (a S : ℝ)
    (ha : 0 ≤ a) (haS : a + S ≤ T) :
    ‖weightedH3PathTimeShift path a S ha haS‖ ≤ ‖path‖ := by
  apply (ContinuousMap.norm_le
    (weightedH3PathTimeShift path a S ha haS) (norm_nonneg path)).2
  intro t
  exact path.norm_coe_le_norm
    ⟨a + t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- Translate a high path based at `a` back to a local aperture `[0,S]`. -/
def weightedHigherOrderPathTimeShift
    {base : ℕ} {T : ℝ} (path : WeightedHigherOrderPath base T) (a S : ℝ)
    (ha : 0 ≤ a) (haS : a + S ≤ T) : WeightedHigherOrderPath base S where
  toFun := fun t ↦ path ⟨a + t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
  continuous_toFun := path.continuous.comp
    ((continuous_const.add continuous_subtype_val).subtype_mk _)

@[simp]
theorem weightedHigherOrderPathTimeShift_apply
    {base : ℕ} {T : ℝ} (path : WeightedHigherOrderPath base T) (a S : ℝ)
    (ha : 0 ≤ a) (haS : a + S ≤ T) (t : Icc (0 : ℝ) S) :
    weightedHigherOrderPathTimeShift path a S ha haS t =
      path ⟨a + t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩ :=
  rfl

theorem norm_weightedHigherOrderPathTimeShift_le
    {base : ℕ} {T : ℝ} (path : WeightedHigherOrderPath base T) (a S : ℝ)
    (ha : 0 ≤ a) (haS : a + S ≤ T) :
    ‖weightedHigherOrderPathTimeShift path a S ha haS‖ ≤ ‖path‖ := by
  apply (ContinuousMap.norm_le
    (weightedHigherOrderPathTimeShift path a S ha haS) (norm_nonneg path)).2
  intro t
  exact path.norm_coe_le_norm
    ⟨a + t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- Spatial restriction commutes exactly with time translation. -/
theorem higherOrderRestrictionPathToThree_timeShift
    (base : ℕ) (hbase : 2 ≤ base) {T : ℝ}
    (path : WeightedHigherOrderPath base T) (a S : ℝ)
    (ha : 0 ≤ a) (haS : a + S ≤ T) :
    higherOrderRestrictionPathToThree base hbase
        (weightedHigherOrderPathTimeShift path a S ha haS) =
      weightedH3PathTimeShift
        (higherOrderRestrictionPathToThree base hbase path) a S ha haS := by
  apply ContinuousMap.ext
  intro t
  rfl

/-! ## Exact binary gluing of adjacent local apertures -/

/-- Glue two continuous local paths on adjacent nonnegative apertures.  The join equality is an
explicit input and is the only identification made at the common face. -/
def weightedIntervalPathConcat
    {E : Type*} [NormedAddCommGroup E]
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (left : C(Icc (0 : ℝ) A, E)) (right : C(Icc (0 : ℝ) B, E))
    (hjoin : left ⟨A, ⟨hA, le_rfl⟩⟩ = right ⟨0, ⟨le_rfl, hB⟩⟩) :
    C(Icc (0 : ℝ) (A + B), E) where
  toFun := fun t ↦ if t.1 ≤ A then
    ContinuousMap.IccExtend hA left t.1
  else
    ContinuousMap.IccExtend hB right (t.1 - A)
  continuous_toFun := by
    apply Continuous.if_le
      ((ContinuousMap.IccExtend hA left).continuous.comp continuous_subtype_val)
      ((ContinuousMap.IccExtend hB right).continuous.comp
        (continuous_subtype_val.sub continuous_const))
      continuous_subtype_val continuous_const
    intro t ht
    simpa [Function.comp_apply, ContinuousMap.IccExtend, Set.IccExtend,
      Set.projIcc, ht, hA, hB] using hjoin

theorem weightedIntervalPathConcat_apply_left
    {E : Type*} [NormedAddCommGroup E]
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (left : C(Icc (0 : ℝ) A, E)) (right : C(Icc (0 : ℝ) B, E))
    (hjoin : left ⟨A, ⟨hA, le_rfl⟩⟩ = right ⟨0, ⟨le_rfl, hB⟩⟩)
    (t : Icc (0 : ℝ) (A + B)) (htA : t.1 ≤ A) :
    weightedIntervalPathConcat hA hB left right hjoin t =
      left ⟨t.1, ⟨t.2.1, htA⟩⟩ := by
  change (if t.1 ≤ A then ContinuousMap.IccExtend hA left t.1
    else ContinuousMap.IccExtend hB right (t.1 - A)) = _
  rw [if_pos htA]
  simp [ContinuousMap.IccExtend, Set.IccExtend, Set.projIcc, t.2.1, htA]

theorem weightedIntervalPathConcat_apply_right
    {E : Type*} [NormedAddCommGroup E]
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (left : C(Icc (0 : ℝ) A, E)) (right : C(Icc (0 : ℝ) B, E))
    (hjoin : left ⟨A, ⟨hA, le_rfl⟩⟩ = right ⟨0, ⟨le_rfl, hB⟩⟩)
    (t : Icc (0 : ℝ) (A + B)) (hAt : A ≤ t.1) :
    weightedIntervalPathConcat hA hB left right hjoin t =
      right ⟨t.1 - A, ⟨sub_nonneg.mpr hAt, by linarith [t.2.2]⟩⟩ := by
  rcases hAt.eq_or_lt with hEq | hLt
  · have htval : t.1 = A := hEq.symm
    rw [weightedIntervalPathConcat_apply_left hA hB left right hjoin t hEq.ge]
    simpa [htval] using hjoin
  · have hnot : ¬ t.1 ≤ A := not_le.mpr hLt
    change (if t.1 ≤ A then ContinuousMap.IccExtend hA left t.1
      else ContinuousMap.IccExtend hB right (t.1 - A)) = _
    rw [if_neg hnot]
    have hupper : t.1 - A ≤ B := by linarith [t.2.2]
    simp [ContinuousMap.IccExtend, Set.IccExtend, Set.projIcc,
      sub_nonneg.mpr hAt, hupper]

/-- Gluing commutes with the bounded high-to-`H³` receiver. -/
theorem higherOrderRestrictionPathToThree_concat
    (base : ℕ) (hbase : 2 ≤ base)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (left : WeightedHigherOrderPath base A)
    (right : WeightedHigherOrderPath base B)
    (hjoin : left ⟨A, ⟨hA, le_rfl⟩⟩ = right ⟨0, ⟨le_rfl, hB⟩⟩) :
    higherOrderRestrictionPathToThree base hbase
        (weightedIntervalPathConcat hA hB left right hjoin) =
      weightedIntervalPathConcat hA hB
        (higherOrderRestrictionPathToThree base hbase left)
        (higherOrderRestrictionPathToThree base hbase right)
        (congrArg
          (periodicVectorWeightedRestrictToThree (base + 1) (by omega)) hjoin) := by
  apply ContinuousMap.ext
  intro t
  by_cases htA : t.1 ≤ A
  · rw [higherOrderRestrictionPathToThree_apply,
      weightedIntervalPathConcat_apply_left hA hB left right hjoin t htA,
      weightedIntervalPathConcat_apply_left hA hB
        (higherOrderRestrictionPathToThree base hbase left)
        (higherOrderRestrictionPathToThree base hbase right) _ t htA]
    rfl
  · have hAt : A ≤ t.1 := le_of_not_ge htA
    rw [higherOrderRestrictionPathToThree_apply,
      weightedIntervalPathConcat_apply_right hA hB left right hjoin t hAt,
      weightedIntervalPathConcat_apply_right hA hB
        (higherOrderRestrictionPathToThree base hbase left)
        (higherOrderRestrictionPathToThree base hbase right) _ t hAt]
    rfl

/-- Adjacent translations of one native path have the same addressed value at their common
face. -/
theorem weightedH3PathTimeShift_join
    {T : ℝ} (low : WeightedH3Path T)
    {a A B : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haAB : a + (A + B) ≤ T) :
    weightedH3PathTimeShift low a A ha (by linarith)
        ⟨A, ⟨hA, le_rfl⟩⟩ =
      weightedH3PathTimeShift low (a + A) B (by linarith)
        (by linarith) ⟨0, ⟨le_rfl, hB⟩⟩ := by
  apply congrArg low
  apply Subtype.ext
  simp

/-- Gluing two adjacent time translations recovers the single translation over their sum. -/
theorem weightedH3PathTimeShift_concat
    {T : ℝ} (low : WeightedH3Path T)
    {a A B : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haAB : a + (A + B) ≤ T) :
    weightedIntervalPathConcat hA hB
        (weightedH3PathTimeShift low a A ha (by linarith))
        (weightedH3PathTimeShift low (a + A) B (by linarith) (by linarith))
        (weightedH3PathTimeShift_join low ha hA hB haAB) =
      weightedH3PathTimeShift low a (A + B) ha haAB := by
  apply ContinuousMap.ext
  intro t
  by_cases htA : t.1 ≤ A
  · rw [weightedIntervalPathConcat_apply_left hA hB _ _ _ t htA]
    apply congrArg low
    apply Subtype.ext
    rfl
  · have hAt : A ≤ t.1 := le_of_not_ge htA
    rw [weightedIntervalPathConcat_apply_right hA hB _ _ _ t hAt]
    apply congrArg low
    apply Subtype.ext
    dsimp only
    ring

/-- Two compatible high segments controlled by adjacent faces of one native path glue to a high
path controlled by the complete combined native face. -/
theorem IsH3ControlledHigherOrderLift.concat
    (base : ℕ) (hbase : 2 ≤ base)
    {T : ℝ} (low : WeightedH3Path T)
    {a A B : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haAB : a + (A + B) ≤ T)
    (left : WeightedHigherOrderPath base A)
    (right : WeightedHigherOrderPath base B)
    (hjoin : left ⟨A, ⟨hA, le_rfl⟩⟩ = right ⟨0, ⟨le_rfl, hB⟩⟩)
    (hleft : IsH3ControlledHigherOrderLift base hbase left
      (weightedH3PathTimeShift low a A ha (by linarith)))
    (hright : IsH3ControlledHigherOrderLift base hbase right
      (weightedH3PathTimeShift low (a + A) B (by linarith) (by linarith))) :
    IsH3ControlledHigherOrderLift base hbase
      (weightedIntervalPathConcat hA hB left right hjoin)
      (weightedH3PathTimeShift low a (A + B) ha haAB) := by
  unfold IsH3ControlledHigherOrderLift at hleft hright ⊢
  apply ContinuousMap.ext
  intro t
  by_cases htA : t.1 ≤ A
  · have hleftAt := congrArg
      (fun path : WeightedH3Path A ↦ path ⟨t.1, ⟨t.2.1, htA⟩⟩) hleft
    change periodicVectorWeightedRestrictToThree (base + 1) (by omega)
        (weightedIntervalPathConcat hA hB left right hjoin t) = _
    rw [weightedIntervalPathConcat_apply_left hA hB left right hjoin t htA]
    exact hleftAt
  · have hAt : A ≤ t.1 := le_of_not_ge htA
    have hrightAt := congrArg
      (fun path : WeightedH3Path B ↦
        path ⟨t.1 - A, ⟨sub_nonneg.mpr hAt, by linarith [t.2.2]⟩⟩) hright
    change periodicVectorWeightedRestrictToThree (base + 1) (by omega)
        (weightedIntervalPathConcat hA hB left right hjoin t) = _
    rw [weightedIntervalPathConcat_apply_right hA hB left right hjoin t hAt]
    calc
      periodicVectorWeightedRestrictToThree (base + 1) (by omega)
          (right ⟨t.1 - A, ⟨sub_nonneg.mpr hAt, by linarith [t.2.2]⟩⟩) =
        weightedH3PathTimeShift low (a + A) B (by linarith) (by linarith)
          ⟨t.1 - A, ⟨sub_nonneg.mpr hAt, by linarith [t.2.2]⟩⟩ := hrightAt
      _ = weightedH3PathTimeShift low a (A + B) ha haAB t := by
        apply congrArg low
        apply Subtype.ext
        dsimp only
        ring

/-! ## Translation of the autonomous Volterra word -/

/-- The componentwise same-order heat transport has the exact additive semigroup law. -/
theorem periodicVectorWeightedHeat_add
    (order : ℕ) (nu s t : ℝ≥0) :
    periodicVectorWeightedHeat order nu (s + t) =
      (periodicVectorWeightedHeat order nu s).comp
        (periodicVectorWeightedHeat order nu t) := by
  apply ContinuousLinearMap.ext
  intro state
  funext component
  exact congrArg (fun operator ↦ operator (state component))
    (periodicWeightedHeat_add order nu s t)

/-- Endpoint projection of a shifted path agrees with the source at every local time face. -/
theorem weightedPathExtension_timeShift_of_mem
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    {a S t : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T)
    (ht : t ∈ Icc (0 : ℝ) S) :
    weightedPathExtension hS (weightedH3PathTimeShift path a S ha haS) t =
      weightedPathExtension hT path (a + t) := by
  have hat : a + t ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2]
  rw [weightedPathExtension_of_mem hS _ ht,
    weightedPathExtension_of_mem hT _ hat]
  rfl

/-- Translation preserves the full positive-time integrand on its addressed local interval. -/
theorem weightedDuhamelIntegrand_timeShift
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    {a S s t : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T)
    (hs : s ∈ Icc (0 : ℝ) S) :
    weightedDuhamelIntegrand nu hnu (a + t)
        (weightedPathExtension hT path) (a + s) =
      weightedDuhamelIntegrand nu hnu t
        (weightedPathExtension hS
          (weightedH3PathTimeShift path a S ha haS)) s := by
  have hext := weightedPathExtension_timeShift_of_mem
    hT path ha hS haS hs
  unfold weightedDuhamelIntegrand
  by_cases hst : s < t
  · rw [dif_pos (by linarith : a + s < a + t), dif_pos hst]
    have helapsed : positiveElapsed (a + t) (a + s) (by linarith) =
        positiveElapsed t s hst := by
      apply NNReal.eq
      simp only [coe_positiveElapsed]
      ring
    simp only [helapsed, hext]
  · rw [dif_neg (by linarith : ¬ a + s < a + t), dif_neg hst]

/-- The recent absolute-time tail is exactly the local Duhamel return after translation. -/
theorem intervalIntegral_weightedDuhamelTail_eq_timeShift
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    {a S t : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T)
    (ht : t ∈ Icc (0 : ℝ) S) :
    (∫ s in a..(a + t),
        weightedDuhamelIntegrand nu hnu (a + t)
          (weightedPathExtension hT path) s) =
      weightedDuhamelReturn nu hnu hS
        (weightedH3PathTimeShift path a S ha haS) t := by
  rw [weightedDuhamelReturn]
  let f := fun s ↦ weightedDuhamelIntegrand nu hnu (a + t)
    (weightedPathExtension hT path) s
  calc
    (∫ s in a..(a + t), f s) = ∫ s in (0 : ℝ)..t, f (s + a) := by
      simpa only [zero_add, add_zero, add_comm] using
        (intervalIntegral.integral_comp_add_right
          (a := (0 : ℝ)) (b := t) f a).symm
    _ = ∫ s in (0 : ℝ)..t,
        weightedDuhamelIntegrand nu hnu t
          (weightedPathExtension hS
            (weightedH3PathTimeShift path a S ha haS)) s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      simpa only [f, add_comm] using
        weightedDuhamelIntegrand_timeShift nu hnu hT path ha hS haS
          ⟨hs.1, hs.2.trans ht.2⟩

/-- The elapsed nonnegative time from `a` to `a+t` is exactly the local coordinate `t`. -/
theorem elapsedBetween_add_eq_toNNReal
    {a t : ℝ} (ht : 0 ≤ t) :
    elapsedBetween (a + t) a (by linarith) = Real.toNNReal t := by
  apply NNReal.eq
  simp only [coe_elapsedBetween, Real.coe_toNNReal _ ht]
  ring

/-- The global linear orbit translated from `a` is the local linear orbit from its `a` face. -/
theorem weightedLinearHeatPath_add
    (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3)
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hat : a + t ≤ T) :
    weightedLinearHeatPath nu hT initial
        ⟨a + t, ⟨by linarith, hat⟩⟩ =
      periodicVectorWeightedHeat 3 nu (Real.toNNReal t)
        (weightedLinearHeatPath nu hT initial
          ⟨a, ⟨ha, by linarith⟩⟩) := by
  have hadd : Real.toNNReal (a + t) =
      Real.toNNReal t + Real.toNNReal a := by
    apply NNReal.eq
    simp only [Real.coe_toNNReal _ (by linarith : 0 ≤ a + t),
      Real.coe_toNNReal _ ht, Real.coe_toNNReal _ ha, NNReal.coe_add]
    ring
  change periodicVectorWeightedHeat 3 nu (Real.toNNReal (a + t)) initial =
    periodicVectorWeightedHeat 3 nu (Real.toNNReal t)
      (periodicVectorWeightedHeat 3 nu (Real.toNNReal a) initial)
  rw [hadd, periodicVectorWeightedHeat_add]
  rfl

/-- Exact translated Volterra split: the absolute return at `a+t` consists of transported old
history plus the local return of the shifted path. -/
theorem weightedDuhamelReturn_add_eq_heat_add_timeShift
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    {a S t : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T)
    (ht : t ∈ Icc (0 : ℝ) S) :
    weightedDuhamelReturn nu hnu hT path (a + t) =
      periodicVectorWeightedHeat 3 nu (Real.toNNReal t)
          (weightedDuhamelReturn nu hnu hT path a) +
        weightedDuhamelReturn nu hnu hS
          (weightedH3PathTimeShift path a S ha haS) t := by
  have haT : a ∈ Icc (0 : ℝ) T := by
    constructor
    · exact ha
    · linarith [haS, hS]
  have hatT : a + t ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2, haS]
  have hasub : a ≤ a + t := by linarith [ht.1]
  rw [weightedDuhamelReturn_eq_heat_add_tail
    nu hnu hT path haT hatT hasub]
  rw [elapsedBetween_add_eq_toNNReal ht.1]
  rw [intervalIntegral_weightedDuhamelTail_eq_timeShift
    nu hnu hT path ha hS haS ht]

/-- **Autonomous shifted recurrence.** Every fixed native mild path remains a fixed mild path
after rebasing at an arbitrary time face; its new initial state is the actual value at that face.
This is derived from the semigroup and Volterra split, not assumed as a second solution. -/
theorem isFixedPt_weightedMildMap_timeShift
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3)
    (path : WeightedH3Path T)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) path)
    {a S : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T) :
    IsFixedPt
      (weightedMildMap nu hnu hS
        (path ⟨a, ⟨ha, by linarith⟩⟩))
      (weightedH3PathTimeShift path a S ha haS) := by
  apply ContinuousMap.ext
  intro t
  have haT : a ∈ Icc (0 : ℝ) T := by
    constructor
    · exact ha
    · linarith [haS, hS]
  have hatT : a + t.1 ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith [t.2.1, t.2.2, haS]
  have hfixedA := congrArg (fun candidate : WeightedH3Path T ↦
    candidate ⟨a, haT⟩) hfixed
  have hfixedAt := congrArg (fun candidate : WeightedH3Path T ↦
    candidate ⟨a + t.1, hatT⟩) hfixed
  change
    weightedLinearHeatPath nu hT initial ⟨a, haT⟩ -
        weightedDuhamelReturn nu hnu hT path a = path ⟨a, haT⟩ at hfixedA
  change
    weightedLinearHeatPath nu hT initial ⟨a + t.1, hatT⟩ -
        weightedDuhamelReturn nu hnu hT path (a + t.1) =
      path ⟨a + t.1, hatT⟩ at hfixedAt
  have hlinear := weightedLinearHeatPath_add
    nu hT initial ha t.2.1 hatT.2
  have hreturn := weightedDuhamelReturn_add_eq_heat_add_timeShift
    nu hnu hT path ha hS haS t.2
  change
    periodicVectorWeightedHeat 3 nu (Real.toNNReal t.1) (path ⟨a, haT⟩) -
        weightedDuhamelReturn nu hnu hS
          (weightedH3PathTimeShift path a S ha haS) t.1 =
      path ⟨a + t.1, hatT⟩
  rw [← hfixedAt, hlinear, hreturn, ← hfixedA]
  rw [(periodicVectorWeightedHeat 3 nu (Real.toNNReal t.1)).map_sub]
  abel

/-! ## One positive shifted higher-order continuation step -/

/-- The native uniqueness load for a local high restart compared with a shifted low path whose
global norm is bounded by `lowBound`. -/
def shiftedHigherOrderCompatibilityLoad
    {base : ℕ} (initial : PeriodicVectorWeightedSobolev (base + 1))
    (lowBound : ℝ) : ℝ :=
  weightedLerayCoefficient * (higherOrderRestartRadius initial + lowBound)

theorem shiftedHigherOrderCompatibilityLoad_nonneg
    {base : ℕ} (initial : PeriodicVectorWeightedSobolev (base + 1))
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound) :
    0 ≤ shiftedHigherOrderCompatibilityLoad initial lowBound := by
  unfold shiftedHigherOrderCompatibilityLoad
  exact mul_nonneg weightedLerayCoefficient_nonneg
    (add_nonneg (higherOrderRestartRadius_pos initial).le hlowBound)

/-- The local shifted step retains both the actual high existence aperture and an independent
native uniqueness aperture. -/
def shiftedHigherOrderCompatibilityTime
    (base : ℕ) (nu : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (lowBound : ℝ) : ℝ :=
  min (higherOrderRestartTime base nu initial)
    (duhamelRestartTime nu
      (shiftedHigherOrderCompatibilityLoad initial lowBound))

theorem shiftedHigherOrderCompatibilityTime_pos
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound) :
    0 < shiftedHigherOrderCompatibilityTime base nu initial lowBound := by
  unfold shiftedHigherOrderCompatibilityTime
  exact lt_min
    (higherOrderRestartTime_pos base hnu initial)
    (duhamelRestartTime_pos hnu
      (shiftedHigherOrderCompatibilityLoad_nonneg initial hlowBound))

theorem shiftedHigherOrderCompatibilityTime_le_high
    (base : ℕ) (nu : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (lowBound : ℝ) :
    shiftedHigherOrderCompatibilityTime base nu initial lowBound ≤
      higherOrderRestartTime base nu initial :=
  min_le_left _ _

theorem shiftedHigherOrderCompatibilityTime_le_uniqueness
    (base : ℕ) (nu : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (lowBound : ℝ) :
    shiftedHigherOrderCompatibilityTime base nu initial lowBound ≤
      duhamelRestartTime nu
        (shiftedHigherOrderCompatibilityLoad initial lowBound) :=
  min_le_right _ _

/-- The selected shifted aperture makes the actual native pairwise uniqueness factor strict. -/
theorem weightedDuhamelCoefficient_mul_shiftedBounds_lt_one
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound) :
    weightedDuhamelCoefficient nu
          (shiftedHigherOrderCompatibilityTime base nu initial lowBound) *
        (higherOrderRestartRadius initial + lowBound) < 1 := by
  let load := shiftedHigherOrderCompatibilityLoad initial lowBound
  let U := duhamelRestartTime nu load
  let S := shiftedHigherOrderCompatibilityTime base nu initial lowBound
  have hload : 0 ≤ load :=
    shiftedHigherOrderCompatibilityLoad_nonneg initial hlowBound
  have hraw := two_load_mul_restartKernelBound_lt_one hnu hload
  have hmono := weightedDuhamelCoefficient_mono_time hnu
    (shiftedHigherOrderCompatibilityTime_le_uniqueness
      base nu initial lowBound)
  have hsum : 0 ≤ higherOrderRestartRadius initial + lowBound :=
    add_nonneg (higherOrderRestartRadius_pos initial).le hlowBound
  have hscaled := mul_le_mul_of_nonneg_right hmono hsum
  have hU : weightedDuhamelCoefficient nu U *
      (higherOrderRestartRadius initial + lowBound) < 1 := by
    have hnonneg : 0 ≤ load *
        (U + 2 * Real.sqrt (U / (2 * nu))) := by
      exact mul_nonneg hload
        (add_nonneg (duhamelRestartTime_pos hnu hload).le
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    have hid : weightedDuhamelCoefficient nu U *
          (higherOrderRestartRadius initial + lowBound) =
        load * (U + 2 * Real.sqrt (U / (2 * nu))) := by
      dsimp [load, U]
      unfold shiftedHigherOrderCompatibilityLoad weightedDuhamelCoefficient
      ring
    rw [hid]
    dsimp [U, load] at hraw ⊢
    nlinarith
  exact hscaled.trans_lt hU

/-- **One noncircular shifted persistence step.** Given an actual high endpoint over the low
receiver at `a`, local high existence returns a segment on the explicit compatibility aperture.
The shifted low path is independently shown to satisfy the rebased mild recurrence, and native
pairwise uniqueness then proves exact restriction equality. -/
theorem exists_shiftedHigherOrderPersistenceStep
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {T : ℝ} (hT : 0 ≤ T)
    (lowInitial : PeriodicVectorWeightedSobolev 3)
    (low : WeightedH3Path T)
    (hlowFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        hT lowInitial) low)
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound) (hlowNorm : ‖low‖ ≤ lowBound)
    {a : ℝ} (ha : 0 ≤ a)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (haStep : a + shiftedHigherOrderCompatibilityTime
        base nu initial lowBound ≤ T)
    (hinitialReceiver :
      periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial =
        low ⟨a, ⟨ha, by
          have hstepPos := shiftedHigherOrderCompatibilityTime_pos
            base hnu initial hlowBound
          linarith [haStep]⟩⟩) :
    ∃ high : WeightedHigherOrderPath base
        (shiftedHigherOrderCompatibilityTime base nu initial lowBound),
      IsFixedPt
          (higherOrderMildMap base hbase
            (Real.toNNReal nu) (real_toNNReal_pos hnu)
            (shiftedHigherOrderCompatibilityTime_pos
              base hnu initial hlowBound).le initial) high ∧
        ‖high‖ ≤ higherOrderRestartRadius initial ∧
        IsH3ControlledHigherOrderLift base hbase high
          (weightedH3PathTimeShift low a
            (shiftedHigherOrderCompatibilityTime base nu initial lowBound)
            ha haStep) ∧
        high ⟨0, ⟨le_rfl,
          (shiftedHigherOrderCompatibilityTime_pos
            base hnu initial hlowBound).le⟩⟩ = initial := by
  let S := shiftedHigherOrderCompatibilityTime base nu initial lowBound
  let Thigh := higherOrderRestartTime base nu initial
  let hS : 0 ≤ S :=
    (shiftedHigherOrderCompatibilityTime_pos base hnu initial hlowBound).le
  let hThigh : 0 ≤ Thigh := (higherOrderRestartTime_pos base hnu initial).le
  have hST : S ≤ Thigh :=
    shiftedHigherOrderCompatibilityTime_le_high base nu initial lowBound
  obtain ⟨highSource, hhighSourceNorm, hhighSourceFixed, hhighSourceZero⟩ :=
    exists_higherOrderMildRestart_fixedPoint base hbase hnu initial
  let high : WeightedHigherOrderPath base S :=
    weightedHigherOrderPathTimeRestrict hST highSource
  have hhighFixed : IsFixedPt
      (higherOrderMildMap base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hS initial) high := by
    exact isFixedPt_higherOrderMildMap_timeRestrict
      base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hS hThigh hST initial highSource hhighSourceFixed
  have hhighNorm : ‖high‖ ≤ higherOrderRestartRadius initial :=
    (norm_weightedHigherOrderPathTimeRestrict_le hST highSource).trans
      hhighSourceNorm
  let lowShift : WeightedH3Path S :=
    weightedH3PathTimeShift low a S ha haStep
  have hlowShiftFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hS
        (periodicVectorWeightedRestrictToThree
          (base + 1) (by omega) initial)) lowShift := by
    have hshift := isFixedPt_weightedMildMap_timeShift
      (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hT lowInitial low hlowFixed ha hS haStep
    rw [hinitialReceiver]
    exact hshift
  let receiver := higherOrderRestrictionPathToThree base hbase high
  have hreceiverFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hS
        (periodicVectorWeightedRestrictToThree
          (base + 1) (by omega) initial)) receiver :=
    isFixedPt_restrict_higherOrderMildMap_to_weighted
      base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hS initial high hhighFixed
  have hreceiverNorm : ‖receiver‖ ≤ higherOrderRestartRadius initial :=
    (norm_higherOrderRestrictionPathToThree_le base hbase high).trans hhighNorm
  have hlowShiftNorm : ‖lowShift‖ ≤ lowBound :=
    (norm_weightedH3PathTimeShift_le low a S ha haStep).trans hlowNorm
  have hfactor : weightedDuhamelCoefficient nu S *
      (‖receiver‖ + ‖lowShift‖) < 1 := by
    have hsum : ‖receiver‖ + ‖lowShift‖ ≤
        higherOrderRestartRadius initial + lowBound :=
      add_le_add hreceiverNorm hlowShiftNorm
    have hA : 0 ≤ weightedDuhamelCoefficient nu S :=
      weightedDuhamelCoefficient_nonneg hS
    exact (mul_le_mul_of_nonneg_left hsum hA).trans_lt
      (weightedDuhamelCoefficient_mul_shiftedBounds_lt_one
        base hnu initial hlowBound)
  have hlift : IsH3ControlledHigherOrderLift base hbase high lowShift := by
    exact isFixedPt_weightedMildMap_eq_of_pair_factor_lt_one
      (Real.toNNReal nu) (real_toNNReal_pos hnu) hS
      (periodicVectorWeightedRestrictToThree
        (base + 1) (by omega) initial)
      receiver lowShift hreceiverFixed hlowShiftFixed
      (by simpa only [Real.coe_toNNReal _ hnu.le, S] using hfactor)
  have hhighZero : high ⟨0, ⟨le_rfl, hS⟩⟩ = initial := by
    change highSource ⟨0, ⟨le_rfl, hS.trans hST⟩⟩ = initial
    simpa only [Thigh, hThigh] using hhighSourceZero
  exact ⟨high, hhighFixed, hhighNorm, hlift, hhighZero⟩

/-- The same shifted step on any smaller addressed aperture.  This is the form used for the final
piece of a finite cover, where the remaining native time may be shorter than the next full local
restart aperture. -/
theorem exists_shiftedHigherOrderPersistenceStep_of_le
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {T : ℝ} (hT : 0 ≤ T)
    (lowInitial : PeriodicVectorWeightedSobolev 3)
    (low : WeightedH3Path T)
    (hlowFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        hT lowInitial) low)
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound) (hlowNorm : ‖low‖ ≤ lowBound)
    {a S : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hSCompatibility : S ≤
      shiftedHigherOrderCompatibilityTime base nu initial lowBound)
    (haS : a + S ≤ T)
    (hinitialReceiver :
      periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial =
        low ⟨a, ⟨ha, by linarith [haS, hS]⟩⟩) :
    ∃ high : WeightedHigherOrderPath base S,
      IsFixedPt
          (higherOrderMildMap base hbase
            (Real.toNNReal nu) (real_toNNReal_pos hnu) hS initial) high ∧
        ‖high‖ ≤ higherOrderRestartRadius initial ∧
        IsH3ControlledHigherOrderLift base hbase high
          (weightedH3PathTimeShift low a S ha haS) ∧
        high ⟨0, ⟨le_rfl, hS⟩⟩ = initial := by
  let Thigh := higherOrderRestartTime base nu initial
  let hThigh : 0 ≤ Thigh := (higherOrderRestartTime_pos base hnu initial).le
  have hST : S ≤ Thigh := hSCompatibility.trans
    (shiftedHigherOrderCompatibilityTime_le_high base nu initial lowBound)
  obtain ⟨highSource, hhighSourceNorm, hhighSourceFixed, hhighSourceZero⟩ :=
    exists_higherOrderMildRestart_fixedPoint base hbase hnu initial
  let high : WeightedHigherOrderPath base S :=
    weightedHigherOrderPathTimeRestrict hST highSource
  have hhighFixed : IsFixedPt
      (higherOrderMildMap base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hS initial) high := by
    exact isFixedPt_higherOrderMildMap_timeRestrict
      base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hS hThigh hST initial highSource hhighSourceFixed
  have hhighNorm : ‖high‖ ≤ higherOrderRestartRadius initial :=
    (norm_weightedHigherOrderPathTimeRestrict_le hST highSource).trans
      hhighSourceNorm
  let lowShift : WeightedH3Path S := weightedH3PathTimeShift low a S ha haS
  have hlowShiftFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hS
        (periodicVectorWeightedRestrictToThree
          (base + 1) (by omega) initial)) lowShift := by
    have hshift := isFixedPt_weightedMildMap_timeShift
      (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hT lowInitial low hlowFixed ha hS haS
    rw [hinitialReceiver]
    exact hshift
  let receiver := higherOrderRestrictionPathToThree base hbase high
  have hreceiverFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hS
        (periodicVectorWeightedRestrictToThree
          (base + 1) (by omega) initial)) receiver :=
    isFixedPt_restrict_higherOrderMildMap_to_weighted
      base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hS initial high hhighFixed
  have hreceiverNorm : ‖receiver‖ ≤ higherOrderRestartRadius initial :=
    (norm_higherOrderRestrictionPathToThree_le base hbase high).trans hhighNorm
  have hlowShiftNorm : ‖lowShift‖ ≤ lowBound :=
    (norm_weightedH3PathTimeShift_le low a S ha haS).trans hlowNorm
  have hfactor : weightedDuhamelCoefficient nu S *
      (‖receiver‖ + ‖lowShift‖) < 1 := by
    have hsum : ‖receiver‖ + ‖lowShift‖ ≤
        higherOrderRestartRadius initial + lowBound :=
      add_le_add hreceiverNorm hlowShiftNorm
    have hcoefficient := weightedDuhamelCoefficient_mono_time hnu hSCompatibility
    have hA : 0 ≤ weightedDuhamelCoefficient nu S :=
      weightedDuhamelCoefficient_nonneg hS
    have hbound : weightedDuhamelCoefficient nu S *
          (‖receiver‖ + ‖lowShift‖) ≤
        weightedDuhamelCoefficient nu
            (shiftedHigherOrderCompatibilityTime base nu initial lowBound) *
          (higherOrderRestartRadius initial + lowBound) := by
      calc
        weightedDuhamelCoefficient nu S * (‖receiver‖ + ‖lowShift‖) ≤
            weightedDuhamelCoefficient nu S *
              (higherOrderRestartRadius initial + lowBound) :=
          mul_le_mul_of_nonneg_left hsum hA
        _ ≤ weightedDuhamelCoefficient nu
              (shiftedHigherOrderCompatibilityTime base nu initial lowBound) *
            (higherOrderRestartRadius initial + lowBound) :=
          mul_le_mul_of_nonneg_right hcoefficient
            (add_nonneg (higherOrderRestartRadius_pos initial).le hlowBound)
    exact hbound.trans_lt
      (weightedDuhamelCoefficient_mul_shiftedBounds_lt_one
        base hnu initial hlowBound)
  have hlift : IsH3ControlledHigherOrderLift base hbase high lowShift := by
    exact isFixedPt_weightedMildMap_eq_of_pair_factor_lt_one
      (Real.toNNReal nu) (real_toNNReal_pos hnu) hS
      (periodicVectorWeightedRestrictToThree
        (base + 1) (by omega) initial)
      receiver lowShift hreceiverFixed hlowShiftFixed
      (by simpa only [Real.coe_toNNReal _ hnu.le] using hfactor)
  have hhighZero : high ⟨0, ⟨le_rfl, hS⟩⟩ = initial := by
    change highSource ⟨0, ⟨le_rfl, hS.trans hST⟩⟩ = initial
    simpa only [Thigh, hThigh] using hhighSourceZero
  exact ⟨high, hhighFixed, hhighNorm, hlift, hhighZero⟩

/-- The next duration is the smaller of the remaining native aperture and the actual local
compatibility aperture. -/
def shiftedHigherOrderContinuationDuration
    (base : ℕ) (nu : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (lowBound remaining : ℝ) : ℝ :=
  min remaining (shiftedHigherOrderCompatibilityTime base nu initial lowBound)

theorem shiftedHigherOrderContinuationDuration_pos
    (base : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    {lowBound remaining : ℝ}
    (hlowBound : 0 ≤ lowBound) (hremaining : 0 < remaining) :
    0 < shiftedHigherOrderContinuationDuration
      base nu initial lowBound remaining := by
  unfold shiftedHigherOrderContinuationDuration
  exact lt_min hremaining
    (shiftedHigherOrderCompatibilityTime_pos
      base hnu initial hlowBound)

/-- Every nonterminal time face therefore emits a strictly positive compatible high segment,
truncated exactly at the terminal native face when that face is closer. -/
theorem exists_shiftedHigherOrderPersistenceStepWithin
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {T : ℝ} (hT : 0 ≤ T)
    (lowInitial : PeriodicVectorWeightedSobolev 3)
    (low : WeightedH3Path T)
    (hlowFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        hT lowInitial) low)
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound) (hlowNorm : ‖low‖ ≤ lowBound)
    {a : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hinitialReceiver :
      periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial =
        low ⟨a, ⟨ha, haT.le⟩⟩) :
    let S := shiftedHigherOrderContinuationDuration
      base nu initial lowBound (T - a)
    ∃ high : WeightedHigherOrderPath base S,
      0 < S ∧
      a + S ≤ T ∧
      IsFixedPt
          (higherOrderMildMap base hbase
            (Real.toNNReal nu) (real_toNNReal_pos hnu)
            ((shiftedHigherOrderContinuationDuration_pos
              base hnu initial hlowBound (sub_pos.mpr haT)).le) initial) high ∧
      ‖high‖ ≤ higherOrderRestartRadius initial ∧
      IsH3ControlledHigherOrderLift base hbase high
        (weightedH3PathTimeShift low a S ha (by
          dsimp [S, shiftedHigherOrderContinuationDuration]
          linarith [min_le_left (T - a)
            (shiftedHigherOrderCompatibilityTime base nu initial lowBound)])) ∧
      high ⟨0, ⟨le_rfl,
        ((shiftedHigherOrderContinuationDuration_pos
          base hnu initial hlowBound (sub_pos.mpr haT)).le)⟩⟩ = initial := by
  dsimp only
  let S := shiftedHigherOrderContinuationDuration
    base nu initial lowBound (T - a)
  have hremaining : 0 < T - a := sub_pos.mpr haT
  have hSpos : 0 < S := shiftedHigherOrderContinuationDuration_pos
    base hnu initial hlowBound hremaining
  have hSCompatibility : S ≤
      shiftedHigherOrderCompatibilityTime base nu initial lowBound :=
    min_le_right _ _
  have haS : a + S ≤ T := by
    have hSRemaining : S ≤ T - a := min_le_left _ _
    linarith
  obtain ⟨high, hfixed, hnorm, hlift, hzero⟩ :=
    exists_shiftedHigherOrderPersistenceStep_of_le
      base hbase hnu hT lowInitial low hlowFixed hlowBound hlowNorm
      ha hSpos.le initial hSCompatibility haS hinitialReceiver
  exact ⟨high, hSpos, haS, hfixed, hnorm, hlift, hzero⟩

/-! ## The exact finite-cover port and its obstruction -/

/-- A uniform compatibility aperture for every high endpoint whose norm is at most `highBound`.
Both the high existence load and the native uniqueness load are retained. -/
def shiftedHigherOrderUniformCompatibilityTime
    (base : ℕ) (nu highBound lowBound : ℝ) : ℝ :=
  min
    (duhamelRestartTime nu
      (higherOrderTameConstant base * (2 * (1 + highBound))))
    (duhamelRestartTime nu
      (weightedLerayCoefficient * (2 * (1 + highBound) + lowBound)))

theorem shiftedHigherOrderUniformCompatibilityTime_pos
    (base : ℕ) {nu highBound lowBound : ℝ}
    (hnu : 0 < nu) (hhighBound : 0 ≤ highBound) (hlowBound : 0 ≤ lowBound) :
    0 < shiftedHigherOrderUniformCompatibilityTime
      base nu highBound lowBound := by
  unfold shiftedHigherOrderUniformCompatibilityTime
  apply lt_min <;> apply duhamelRestartTime_pos hnu
  · exact mul_nonneg (higherOrderTameConstant_nonneg base) (by positivity)
  · exact mul_nonneg weightedLerayCoefficient_nonneg (by positivity)

/-- A bound for one high endpoint gives the declared uniform aperture as a lower bound for its
actual state-dependent shifted aperture. -/
theorem shiftedHigherOrderUniformCompatibilityTime_le
    (base : ℕ) {nu highBound lowBound : ℝ}
    (hnu : 0 < nu) (hhighBound : 0 ≤ highBound) (hlowBound : 0 ≤ lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hinitial : ‖initial‖ ≤ highBound) :
    shiftedHigherOrderUniformCompatibilityTime base nu highBound lowBound ≤
      shiftedHigherOrderCompatibilityTime base nu initial lowBound := by
  have hradius : higherOrderRestartRadius initial ≤ 2 * (1 + highBound) := by
    unfold higherOrderRestartRadius
    linarith
  have hhighLoad : higherOrderRestartLoad base initial ≤
      higherOrderTameConstant base * (2 * (1 + highBound)) := by
    unfold higherOrderRestartLoad
    exact mul_le_mul_of_nonneg_left hradius
      (higherOrderTameConstant_nonneg base)
  have hhighLoadCap :
      0 ≤ higherOrderTameConstant base * (2 * (1 + highBound)) :=
    mul_nonneg (higherOrderTameConstant_nonneg base) (by positivity)
  have hhighTime : duhamelRestartTime nu
        (higherOrderTameConstant base * (2 * (1 + highBound))) ≤
      higherOrderRestartTime base nu initial := by
    unfold higherOrderRestartTime
    exact duhamelRestartTime_anti_load hnu
      (higherOrderRestartLoad_nonneg base initial) hhighLoadCap hhighLoad
  have huniqueLoad : shiftedHigherOrderCompatibilityLoad initial lowBound ≤
      weightedLerayCoefficient * (2 * (1 + highBound) + lowBound) := by
    unfold shiftedHigherOrderCompatibilityLoad
    apply mul_le_mul_of_nonneg_left _ weightedLerayCoefficient_nonneg
    linarith
  have huniqueLoadCap :
      0 ≤ weightedLerayCoefficient * (2 * (1 + highBound) + lowBound) :=
    mul_nonneg weightedLerayCoefficient_nonneg (by positivity)
  have huniqueTime : duhamelRestartTime nu
        (weightedLerayCoefficient * (2 * (1 + highBound) + lowBound)) ≤
      duhamelRestartTime nu
        (shiftedHigherOrderCompatibilityLoad initial lowBound) := by
    exact duhamelRestartTime_anti_load hnu
      (shiftedHigherOrderCompatibilityLoad_nonneg initial hlowBound)
      huniqueLoadCap huniqueLoad
  exact min_le_min hhighTime huniqueTime

/-- A bounded family of successive high endpoints has a common strictly positive shifted
restart aperture.  This is the quantitative input needed by finite covering. -/
theorem exists_uniform_positive_shiftedAperture_of_endpointBound
    {I : Type*} (base : ℕ) {nu lowBound highBound : ℝ}
    (hnu : 0 < nu) (hlowBound : 0 ≤ lowBound) (hhighBound : 0 ≤ highBound)
    (endpoint : I → PeriodicVectorWeightedSobolev (base + 1))
    (hendpoint : ∀ i, ‖endpoint i‖ ≤ highBound) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ i,
      delta ≤ shiftedHigherOrderCompatibilityTime
        base nu (endpoint i) lowBound := by
  refine ⟨shiftedHigherOrderUniformCompatibilityTime
    base nu highBound lowBound,
    shiftedHigherOrderUniformCompatibilityTime_pos
      base hnu hhighBound hlowBound, ?_⟩
  intro i
  exact shiftedHigherOrderUniformCompatibilityTime_le
    base hnu hhighBound hlowBound (endpoint i) (hendpoint i)

/-- If successive shifted apertures collapse below every positive scale, their high endpoint
norms must escape every finite bound.  Thus a Zeno continuation is not an independent loophole:
it is exactly the currently unclosed high-norm blow-up alternative. -/
theorem unbounded_endpoints_of_collapsing_shiftedApertures
    {I : Type*} (base : ℕ) {nu lowBound : ℝ}
    (hnu : 0 < nu) (hlowBound : 0 ≤ lowBound)
    (endpoint : I → PeriodicVectorWeightedSobolev (base + 1))
    (hcollapse : ∀ delta : ℝ, 0 < delta → ∃ i,
      shiftedHigherOrderCompatibilityTime base nu (endpoint i) lowBound < delta) :
    ∀ highBound : ℝ, 0 ≤ highBound → ∃ i, highBound < ‖endpoint i‖ := by
  intro highBound hhighBound
  let delta := shiftedHigherOrderUniformCompatibilityTime
    base nu highBound lowBound
  have hdelta : 0 < delta := shiftedHigherOrderUniformCompatibilityTime_pos
    base hnu hhighBound hlowBound
  obtain ⟨i, hi⟩ := hcollapse delta hdelta
  refine ⟨i, ?_⟩
  by_contra hnot
  have hnorm : ‖endpoint i‖ ≤ highBound := le_of_not_gt hnot
  have hlower := shiftedHigherOrderUniformCompatibilityTime_le
    base hnu hhighBound hlowBound (endpoint i) hnorm
  exact (not_lt_of_ge hlower) hi

/-- Under a high endpoint bound, one truncated continuation step either reaches the terminal
native face or advances by at least the common positive aperture. -/
theorem shiftedHigherOrderContinuation_reaches_or_uniform_progress
    (base : ℕ) {nu highBound lowBound T a : ℝ}
    (hnu : 0 < nu) (hhighBound : 0 ≤ highBound) (hlowBound : 0 ≤ lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hinitial : ‖initial‖ ≤ highBound) :
    let delta := shiftedHigherOrderUniformCompatibilityTime
      base nu highBound lowBound
    let S := shiftedHigherOrderContinuationDuration
      base nu initial lowBound (T - a)
    a + S = T ∨ a + delta ≤ a + S := by
  dsimp only
  let delta := shiftedHigherOrderUniformCompatibilityTime
    base nu highBound lowBound
  let compatibility := shiftedHigherOrderCompatibilityTime
    base nu initial lowBound
  have hdeltaCompatibility : delta ≤ compatibility :=
    shiftedHigherOrderUniformCompatibilityTime_le
      base hnu hhighBound hlowBound initial hinitial
  by_cases hremaining : T - a ≤ compatibility
  · left
    rw [shiftedHigherOrderContinuationDuration, min_eq_left hremaining]
    ring
  · right
    have hcompatibilityRemaining : compatibility ≤ T - a :=
      le_of_not_ge hremaining
    rw [shiftedHigherOrderContinuationDuration,
      min_eq_right hcompatibilityRemaining]
    linarith

/-- A uniformly positive sequence of nonterminal advances cannot remain strictly below a finite
terminal face through any number `N` satisfying `T ≤ Nδ`.  This is the exact finite-cover
arithmetic used by an iterated gluing construction. -/
theorem finite_cover_excludes_strictly_uncovered_schedule
    {T delta : ℝ}
    (time : ℕ → ℝ) (htimeZero : time 0 = 0)
    (htimeUpper : ∀ n, time n ≤ T)
    (hadvance : ∀ n, time n < T →
      time (n + 1) = T ∨ time n + delta ≤ time (n + 1))
    (N : ℕ) (hcover : T ≤ (N : ℝ) * delta)
    (huncovered : ∀ n, n ≤ N → time n < T) : False := by
  have hprogress : ∀ n, n ≤ N → (n : ℝ) * delta ≤ time n := by
    intro n hn
    induction n with
    | zero => norm_num [htimeZero]
    | succ n ih =>
        have hnN : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
        have hnlt : time n < T := huncovered n hnN
        rcases hadvance n hnlt with hterminal | hstep
        · have hsuccN : n + 1 ≤ N := by simpa only [Nat.succ_eq_add_one] using hn

          exact False.elim ((ne_of_lt (huncovered (n + 1) hsuccN)) hterminal)
        · have ih' := ih hnN
          push_cast
          nlinarith
  have hNprogress := hprogress N le_rfl
  have hNupper := htimeUpper N
  have hNlt := huncovered N le_rfl
  nlinarith

/-- Every positive uniform aperture admits a finite arithmetic cover count. -/
theorem exists_finite_shiftedCoverCount
    {T delta : ℝ} (hdelta : 0 < delta) :
    ∃ N : ℕ, T ≤ (N : ℝ) * delta := by
  obtain ⟨N, hN⟩ := exists_nat_gt (T / delta)
  refine ⟨N, ?_⟩
  have hscaled := (div_lt_iff₀ hdelta).mp hN
  nlinarith

section Audit

#print axioms isFixedPt_weightedMildMap_timeShift
#print axioms higherOrderRestrictionPathToThree_concat
#print axioms weightedDuhamelCoefficient_mul_shiftedBounds_lt_one
#print axioms exists_shiftedHigherOrderPersistenceStepWithin
#print axioms shiftedHigherOrderUniformCompatibilityTime_le
#print axioms unbounded_endpoints_of_collapsing_shiftedApertures
#print axioms finite_cover_excludes_strictly_uncovered_schedule

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedShiftedHigherOrderPersistence
