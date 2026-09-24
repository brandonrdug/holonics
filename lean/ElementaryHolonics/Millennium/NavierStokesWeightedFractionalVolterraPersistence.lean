import ElementaryHolonics.Millennium.NavierStokesWeightedShiftedHigherOrderPersistence

/-!
# Uniform finite-aperture higher-order bounds from the fractional Volterra word

**[proved-derived]** The mixed tame return is linear in the high norm once its exact `H³`
receiver is fixed.  This owner retains that receiver on successive translated time blocks whose
width is chosen solely from viscosity, Sobolev order, and the native path bound.  On each block
the integrable one-derivative heat kernel gives a strict half-factor, so the high norm grows by at
most two.  A finite arithmetic cover therefore yields an explicit bound on every high mild path
over a finite native aperture, independent of the number and sizes of the local existence
restarts used to construct it.

The construction is a coarse fractional-Volterra Gronwall law: it uses the actual singular
kernel budget and autonomous rebasing, not a pre-assumed high endpoint bound.  Its final theorem
feeds the uniform shifted compatibility time and excludes the previously exposed Zeno
alternative for every finite Sobolev order.
-/

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesWeightedFractionalVolterraPersistence

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
open Soma.Holonics.Millennium.NavierStokesWeightedShiftedHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Autonomous rebasing of the high Volterra recurrence -/

theorem weightedHigherOrderPathExtension_timeShift_of_mem
    {base : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedHigherOrderPath base T)
    {a S t : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T)
    (ht : t ∈ Icc (0 : ℝ) S) :
    weightedHigherOrderPathExtension hS
        (weightedHigherOrderPathTimeShift path a S ha haS) t =
      weightedHigherOrderPathExtension hT path (a + t) := by
  have hat : a + t ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2]
  rw [weightedHigherOrderPathExtension_of_mem hS _ ht,
    weightedHigherOrderPathExtension_of_mem hT _ hat]
  rfl

theorem higherOrderDuhamelIntegrand_timeShift
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedHigherOrderPath base T)
    {a S s t : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T)
    (hs : s ∈ Icc (0 : ℝ) S) :
    higherOrderDuhamelIntegrand base hbase nu hnu (a + t)
        (weightedHigherOrderPathExtension hT path) (a + s) =
      higherOrderDuhamelIntegrand base hbase nu hnu t
        (weightedHigherOrderPathExtension hS
          (weightedHigherOrderPathTimeShift path a S ha haS)) s := by
  have hext := weightedHigherOrderPathExtension_timeShift_of_mem
    hT path ha hS haS hs
  unfold higherOrderDuhamelIntegrand
  by_cases hst : s < t
  · rw [dif_pos (by linarith : a + s < a + t), dif_pos hst]
    have helapsed : positiveElapsed (a + t) (a + s) (by linarith) =
        positiveElapsed t s hst := by
      apply NNReal.eq
      simp only [coe_positiveElapsed]
      ring
    simp only [helapsed, hext]
  · rw [dif_neg (by linarith : ¬ a + s < a + t), dif_neg hst]

theorem intervalIntegral_higherOrderDuhamelTail_eq_timeShift
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedHigherOrderPath base T)
    {a S t : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T)
    (ht : t ∈ Icc (0 : ℝ) S) :
    (∫ s in a..(a + t),
        higherOrderDuhamelIntegrand base hbase nu hnu (a + t)
          (weightedHigherOrderPathExtension hT path) s) =
      higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hS
          (weightedHigherOrderPathTimeShift path a S ha haS)) := by
  unfold higherOrderDuhamelReturn
  let f := fun s ↦ higherOrderDuhamelIntegrand base hbase nu hnu (a + t)
    (weightedHigherOrderPathExtension hT path) s
  calc
    (∫ s in a..(a + t), f s) = ∫ s in (0 : ℝ)..t, f (s + a) := by
      simpa only [zero_add, add_zero, add_comm] using
        (intervalIntegral.integral_comp_add_right
          (a := (0 : ℝ)) (b := t) f a).symm
    _ = ∫ s in (0 : ℝ)..t,
        higherOrderDuhamelIntegrand base hbase nu hnu t
          (weightedHigherOrderPathExtension hS
            (weightedHigherOrderPathTimeShift path a S ha haS)) s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      simpa only [f, add_comm] using
        higherOrderDuhamelIntegrand_timeShift
          base hbase nu hnu hT path ha hS haS
            ⟨hs.1, hs.2.trans ht.2⟩

theorem higherOrderLinearHeatPath_add
    (base : ℕ) (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hat : a + t ≤ T) :
    higherOrderLinearHeatPath base nu hT initial
        ⟨a + t, ⟨by linarith, hat⟩⟩ =
      periodicVectorWeightedHeat (base + 1) nu (Real.toNNReal t)
        (higherOrderLinearHeatPath base nu hT initial
          ⟨a, ⟨ha, by linarith⟩⟩) := by
  have hadd : Real.toNNReal (a + t) =
      Real.toNNReal t + Real.toNNReal a := by
    apply NNReal.eq
    simp only [Real.coe_toNNReal _ (by linarith : 0 ≤ a + t),
      Real.coe_toNNReal _ ht, Real.coe_toNNReal _ ha, NNReal.coe_add]
    ring
  change periodicVectorWeightedHeat (base + 1) nu
      (Real.toNNReal (a + t)) initial =
    periodicVectorWeightedHeat (base + 1) nu (Real.toNNReal t)
      (periodicVectorWeightedHeat (base + 1) nu (Real.toNNReal a) initial)
  rw [hadd, periodicVectorWeightedHeat_add]
  rfl

theorem higherOrderDuhamelReturn_add_eq_heat_add_timeShift
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedHigherOrderPath base T)
    {a S t : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T)
    (ht : t ∈ Icc (0 : ℝ) S) :
    higherOrderDuhamelReturn base hbase nu hnu (a + t)
        (weightedHigherOrderPathExtension hT path) =
      periodicVectorWeightedHeat (base + 1) nu (Real.toNNReal t)
          (higherOrderDuhamelReturn base hbase nu hnu a
            (weightedHigherOrderPathExtension hT path)) +
        higherOrderDuhamelReturn base hbase nu hnu t
          (weightedHigherOrderPathExtension hS
            (weightedHigherOrderPathTimeShift path a S ha haS)) := by
  have haT : a ∈ Icc (0 : ℝ) T := by
    constructor
    · exact ha
    · linarith [haS, hS]
  have hatT : a + t ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2, haS]
  have hasub : a ≤ a + t := by linarith [ht.1]
  rw [higherOrderDuhamelReturn_eq_heat_add_tail
    base hbase nu hnu hT path haT hatT hasub]
  rw [elapsedBetween_add_eq_toNNReal ht.1]
  rw [intervalIntegral_higherOrderDuhamelTail_eq_timeShift
    base hbase nu hnu hT path ha hS haS ht]

/-- A high mild fixed path remains an exact high mild fixed path after rebasing at any time
face. -/
theorem isFixedPt_higherOrderMildMap_timeShift
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (path : WeightedHigherOrderPath base T)
    (hfixed : IsFixedPt
      (higherOrderMildMap base hbase nu hnu hT initial) path)
    {a S : ℝ} (ha : 0 ≤ a) (hS : 0 ≤ S) (haS : a + S ≤ T) :
    IsFixedPt
      (higherOrderMildMap base hbase nu hnu hS
        (path ⟨a, ⟨ha, by linarith⟩⟩))
      (weightedHigherOrderPathTimeShift path a S ha haS) := by
  apply ContinuousMap.ext
  intro t
  have haT : a ∈ Icc (0 : ℝ) T := by
    constructor
    · exact ha
    · linarith [haS, hS]
  have hatT : a + t.1 ∈ Icc (0 : ℝ) T := by
    constructor <;> linarith [t.2.1, t.2.2, haS]
  have hfixedA := congrArg (fun candidate : WeightedHigherOrderPath base T ↦
    candidate ⟨a, haT⟩) hfixed
  have hfixedAt := congrArg (fun candidate : WeightedHigherOrderPath base T ↦
    candidate ⟨a + t.1, hatT⟩) hfixed
  change
    higherOrderLinearHeatPath base nu hT initial ⟨a, haT⟩ -
        higherOrderDuhamelReturn base hbase nu hnu a
          (weightedHigherOrderPathExtension hT path) = path ⟨a, haT⟩ at hfixedA
  change
    higherOrderLinearHeatPath base nu hT initial ⟨a + t.1, hatT⟩ -
        higherOrderDuhamelReturn base hbase nu hnu (a + t.1)
          (weightedHigherOrderPathExtension hT path) =
      path ⟨a + t.1, hatT⟩ at hfixedAt
  have hlinear := higherOrderLinearHeatPath_add
    base nu hT initial ha t.2.1 hatT.2
  have hreturn := higherOrderDuhamelReturn_add_eq_heat_add_timeShift
    base hbase nu hnu hT path ha hS haS t.2
  change
    periodicVectorWeightedHeat (base + 1) nu (Real.toNNReal t.1)
          (path ⟨a, haT⟩) -
        higherOrderDuhamelReturn base hbase nu hnu t.1
          (weightedHigherOrderPathExtension hS
            (weightedHigherOrderPathTimeShift path a S ha haS)) =
      path ⟨a + t.1, hatT⟩
  rw [← hfixedAt, hlinear, hreturn, ← hfixedA]
  rw [(periodicVectorWeightedHeat
    (base + 1) nu (Real.toNNReal t.1)).map_sub]
  abel

/-- High-to-low control is retained by autonomous time translation. -/
theorem IsH3ControlledHigherOrderLift.timeShift
    (base : ℕ) (hbase : 2 ≤ base)
    {T : ℝ} {high : WeightedHigherOrderPath base T} {low : WeightedH3Path T}
    (hlift : IsH3ControlledHigherOrderLift base hbase high low)
    {a S : ℝ} (ha : 0 ≤ a) (haS : a + S ≤ T) :
    IsH3ControlledHigherOrderLift base hbase
      (weightedHigherOrderPathTimeShift high a S ha haS)
      (weightedH3PathTimeShift low a S ha haS) := by
  unfold IsH3ControlledHigherOrderLift at hlift ⊢
  rw [higherOrderRestrictionPathToThree_timeShift, hlift]

/-! ## Global fixed-point law under binary restart gluing -/

theorem higherOrderDuhamelReturn_concat_of_le
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (left : WeightedHigherOrderPath base A)
    (right : WeightedHigherOrderPath base B)
    (hjoin : left ⟨A, ⟨hA, le_rfl⟩⟩ = right ⟨0, ⟨le_rfl, hB⟩⟩)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) A) :
    higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension (add_nonneg hA hB)
          (weightedIntervalPathConcat hA hB left right hjoin)) =
      higherOrderDuhamelReturn base hbase nu hnu t
        (weightedHigherOrderPathExtension hA left) := by
  unfold higherOrderDuhamelReturn
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hsA : s ∈ Icc (0 : ℝ) A := ⟨hs.1, hs.2.trans ht.2⟩
  have hsAB : s ∈ Icc (0 : ℝ) (A + B) :=
    ⟨hs.1, hsA.2.trans (le_add_of_nonneg_right hB)⟩
  have hextJoined :
      weightedHigherOrderPathExtension (add_nonneg hA hB)
          (weightedIntervalPathConcat hA hB left right hjoin) s =
        left ⟨s, hsA⟩ := by
    rw [weightedHigherOrderPathExtension_of_mem _ _ hsAB,
      weightedIntervalPathConcat_apply_left hA hB left right hjoin _ hsA.2]
  have hextLeft : weightedHigherOrderPathExtension hA left s =
      left ⟨s, hsA⟩ :=
    weightedHigherOrderPathExtension_of_mem hA left hsA
  unfold higherOrderDuhamelIntegrand
  split <;> simp only [hextJoined, hextLeft]

theorem weightedHigherOrderPathTimeShift_concat_right
    {base : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (left : WeightedHigherOrderPath base A)
    (right : WeightedHigherOrderPath base B)
    (hjoin : left ⟨A, ⟨hA, le_rfl⟩⟩ = right ⟨0, ⟨le_rfl, hB⟩⟩) :
    weightedHigherOrderPathTimeShift
        (weightedIntervalPathConcat hA hB left right hjoin)
        A B hA (by ring_nf; exact le_rfl) = right := by
  apply ContinuousMap.ext
  intro t
  rw [weightedHigherOrderPathTimeShift_apply]
  have hAt : A ≤ A + t.1 := by linarith [t.2.1]
  rw [weightedIntervalPathConcat_apply_right hA hB left right hjoin _ hAt]
  apply congrArg right
  apply Subtype.ext
  dsimp only
  ring

/-- **Binary restart gluing preserves the full high mild recurrence.** The second segment is
based at the actual endpoint of the first, and the explicit join equality is retained. -/
theorem isFixedPt_higherOrderMildMap_concat
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (left : WeightedHigherOrderPath base A)
    (right : WeightedHigherOrderPath base B)
    (hleftFixed : IsFixedPt
      (higherOrderMildMap base hbase nu hnu hA initial) left)
    (hjoin : left ⟨A, ⟨hA, le_rfl⟩⟩ = right ⟨0, ⟨le_rfl, hB⟩⟩)
    (hrightFixed : IsFixedPt
      (higherOrderMildMap base hbase nu hnu hB
        (left ⟨A, ⟨hA, le_rfl⟩⟩)) right) :
    IsFixedPt
      (higherOrderMildMap base hbase nu hnu (add_nonneg hA hB) initial)
      (weightedIntervalPathConcat hA hB left right hjoin) := by
  let joined := weightedIntervalPathConcat hA hB left right hjoin
  apply ContinuousMap.ext
  intro t
  by_cases htA : t.1 ≤ A
  · have htLeft : t.1 ∈ Icc (0 : ℝ) A := ⟨t.2.1, htA⟩
    have hleftAt := congrArg (fun candidate : WeightedHigherOrderPath base A ↦
      candidate ⟨t.1, htLeft⟩) hleftFixed
    change higherOrderLinearHeatPath base nu (add_nonneg hA hB) initial t -
        higherOrderDuhamelReturn base hbase nu hnu t.1
          (weightedHigherOrderPathExtension (add_nonneg hA hB) joined) = joined t
    have hreturn := higherOrderDuhamelReturn_concat_of_le
      base hbase nu hnu hA hB left right hjoin htLeft
    have hjoined := weightedIntervalPathConcat_apply_left
      hA hB left right hjoin t htA
    change higherOrderLinearHeatPath base nu hA initial ⟨t.1, htLeft⟩ -
        higherOrderDuhamelReturn base hbase nu hnu t.1
          (weightedHigherOrderPathExtension hA left) = left ⟨t.1, htLeft⟩ at hleftAt
    dsimp only [joined]
    rw [hreturn, hjoined]
    change higherOrderLinearHeatPath base nu hA initial ⟨t.1, htLeft⟩ -
        higherOrderDuhamelReturn base hbase nu hnu t.1
          (weightedHigherOrderPathExtension hA left) = left ⟨t.1, htLeft⟩
    exact hleftAt
  · have hAt : A ≤ t.1 := (lt_of_not_ge htA).le
    let tau : ℝ := t.1 - A
    have htau : tau ∈ Icc (0 : ℝ) B := by
      constructor
      · dsimp [tau]; exact sub_nonneg.mpr hAt
      · dsimp [tau]; linarith [t.2.2]
    have hrightAt := congrArg (fun candidate : WeightedHigherOrderPath base B ↦
      candidate ⟨tau, htau⟩) hrightFixed
    have hleftEnd := congrArg (fun candidate : WeightedHigherOrderPath base A ↦
      candidate ⟨A, ⟨hA, le_rfl⟩⟩) hleftFixed
    have hreturnLeft := higherOrderDuhamelReturn_concat_of_le
      base hbase nu hnu hA hB left right hjoin
        (⟨hA, le_rfl⟩ : A ∈ Icc (0 : ℝ) A)
    have hshift : weightedHigherOrderPathTimeShift joined A B hA
        le_rfl = right := by
      exact weightedHigherOrderPathTimeShift_concat_right
        hA hB left right hjoin
    have htDecomp : A + tau = t.1 := by dsimp [tau]; ring
    have hreturnSplit := higherOrderDuhamelReturn_add_eq_heat_add_timeShift
      base hbase nu hnu (add_nonneg hA hB) joined
      hA hB le_rfl htau
    have hlinearSplit := higherOrderLinearHeatPath_add
      base nu (add_nonneg hA hB) initial hA htau.1
        (by dsimp [tau]; linarith [t.2.2])
    have htimeArg :
        (⟨A + tau, ⟨by linarith [hA, htau.1], by linarith [htau.2]⟩⟩ :
            Icc (0 : ℝ) (A + B)) = t := by
      apply Subtype.ext
      exact htDecomp
    have hlinearAt := hlinearSplit
    rw [htimeArg] at hlinearAt
    change higherOrderLinearHeatPath base nu (add_nonneg hA hB) initial t -
        higherOrderDuhamelReturn base hbase nu hnu t.1
          (weightedHigherOrderPathExtension (add_nonneg hA hB) joined) = joined t
    rw [← htDecomp, hlinearAt, hreturnSplit, hreturnLeft, hshift]
    rw [weightedIntervalPathConcat_apply_right hA hB left right hjoin _ hAt]
    change periodicVectorWeightedHeat (base + 1) nu (Real.toNNReal tau)
          (higherOrderLinearHeatPath base nu hA initial
            ⟨A, ⟨hA, le_rfl⟩⟩) -
        (periodicVectorWeightedHeat (base + 1) nu (Real.toNNReal tau)
            (higherOrderDuhamelReturn base hbase nu hnu A
              (weightedHigherOrderPathExtension hA left)) +
          higherOrderDuhamelReturn base hbase nu hnu tau
            (weightedHigherOrderPathExtension hB right)) = right ⟨tau, htau⟩
    change higherOrderLinearHeatPath base nu hA initial ⟨A, ⟨hA, le_rfl⟩⟩ -
        higherOrderDuhamelReturn base hbase nu hnu A
          (weightedHigherOrderPathExtension hA left) =
      left ⟨A, ⟨hA, le_rfl⟩⟩ at hleftEnd
    change periodicVectorWeightedHeat (base + 1) nu (Real.toNNReal tau)
          (left ⟨A, ⟨hA, le_rfl⟩⟩) -
        higherOrderDuhamelReturn base hbase nu hnu tau
          (weightedHigherOrderPathExtension hB right) = right ⟨tau, htau⟩ at hrightAt
    rw [← hrightAt, ← hleftEnd]
    rw [(periodicVectorWeightedHeat
      (base + 1) nu (Real.toNNReal tau)).map_sub]
    abel

/-! ## One receiver-controlled fractional-Volterra block -/

/-- The mixed low--high load.  Unlike the original high restart load, it contains no high norm. -/
def higherOrderLowControlledLoad (base : ℕ) (lowBound : ℝ) : ℝ :=
  higherOrderTameConstant base * lowBound

theorem higherOrderLowControlledLoad_nonneg
    (base : ℕ) {lowBound : ℝ} (hlowBound : 0 ≤ lowBound) :
    0 ≤ higherOrderLowControlledLoad base lowBound :=
  mul_nonneg (higherOrderTameConstant_nonneg base) hlowBound

/-- A positive block width selected solely from viscosity, order, and the native receiver bound. -/
def higherOrderLowControlledPersistenceTime
    (base : ℕ) (nu lowBound : ℝ) : ℝ :=
  duhamelRestartTime nu (higherOrderLowControlledLoad base lowBound)

theorem higherOrderLowControlledPersistenceTime_pos
    (base : ℕ) {nu lowBound : ℝ}
    (hnu : 0 < nu) (hlowBound : 0 ≤ lowBound) :
    0 < higherOrderLowControlledPersistenceTime base nu lowBound :=
  duhamelRestartTime_pos hnu
    (higherOrderLowControlledLoad_nonneg base hlowBound)

/-- On the receiver-controlled block, the exact tame fractional-kernel factor is below one half. -/
theorem higherOrderLowControlledFactor_lt_half
    (base : ℕ) {nu lowBound : ℝ}
    (hnu : 0 < nu) (hlowBound : 0 ≤ lowBound) :
    higherOrderTameConstant base * lowBound *
        duhamelApertureBudget (Real.toNNReal nu)
          (higherOrderLowControlledPersistenceTime base nu lowBound) < 1 / 2 := by
  have hraw := two_load_mul_restartKernelBound_lt_one hnu
    (higherOrderLowControlledLoad_nonneg base hlowBound)
  unfold higherOrderLowControlledPersistenceTime
  unfold higherOrderLowControlledLoad at hraw ⊢
  simp only [duhamelApertureBudget, Real.coe_toNNReal _ hnu.le]
  nlinarith

/-- Every controlled high fixed path on one receiver-selected block has norm at most twice its
initial high norm.  No bound for the high path appears among the hypotheses. -/
theorem norm_higherOrderFixedPath_le_two_on_lowControlledBlock
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {lowBound S : ℝ} (hlowBound : 0 ≤ lowBound) (hS : 0 ≤ S)
    (hSBlock : S ≤ higherOrderLowControlledPersistenceTime base nu lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (high : WeightedHigherOrderPath base S) (low : WeightedH3Path S)
    (hfixed : IsFixedPt
      (higherOrderMildMap base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hS initial) high)
    (hlift : IsH3ControlledHigherOrderLift base hbase high low)
    (hlowNorm : ‖low‖ ≤ lowBound) :
    ‖high‖ ≤ 2 * ‖initial‖ := by
  have haffine := norm_fixedPoint_higherOrderMildMap_le_initial_add_tame
    base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      hS initial high low hfixed hlift
  have hbudget := duhamelApertureBudget_mono
    (Real.toNNReal nu) (real_toNNReal_pos hnu) hSBlock
  have hconstant : 0 ≤ higherOrderTameConstant base :=
    higherOrderTameConstant_nonneg base
  have hlowNonneg : 0 ≤ ‖low‖ := norm_nonneg low
  have hbudgetNonneg : 0 ≤ duhamelApertureBudget (Real.toNNReal nu) S :=
    duhamelApertureBudget_nonneg _ hS
  have hblockBudgetNonneg :
      0 ≤ duhamelApertureBudget (Real.toNNReal nu)
        (higherOrderLowControlledPersistenceTime base nu lowBound) :=
    duhamelApertureBudget_nonneg _
      (higherOrderLowControlledPersistenceTime_pos base hnu hlowBound).le
  have hfactor : higherOrderTameConstant base * ‖low‖ *
      duhamelApertureBudget (Real.toNNReal nu) S < 1 / 2 := by
    have hlowScaled : higherOrderTameConstant base * ‖low‖ ≤
        higherOrderTameConstant base * lowBound :=
      mul_le_mul_of_nonneg_left hlowNorm hconstant
    calc
      higherOrderTameConstant base * ‖low‖ *
          duhamelApertureBudget (Real.toNNReal nu) S ≤
        higherOrderTameConstant base * lowBound *
          duhamelApertureBudget (Real.toNNReal nu) S :=
        mul_le_mul_of_nonneg_right hlowScaled hbudgetNonneg
      _ ≤ higherOrderTameConstant base * lowBound *
          duhamelApertureBudget (Real.toNNReal nu)
            (higherOrderLowControlledPersistenceTime base nu lowBound) :=
        mul_le_mul_of_nonneg_left hbudget
          (mul_nonneg hconstant hlowBound)
      _ < 1 / 2 :=
        higherOrderLowControlledFactor_lt_half base hnu hlowBound
  nlinarith [norm_nonneg high, norm_nonneg initial]

/-! ## Finite iteration of receiver-controlled blocks -/

theorem IsH3ControlledHigherOrderLift.timeRestrict
    (base : ℕ) (hbase : 2 ≤ base)
    {T : ℝ} {high : WeightedHigherOrderPath base T} {low : WeightedH3Path T}
    (hlift : IsH3ControlledHigherOrderLift base hbase high low)
    {S : ℝ} (hST : S ≤ T) :
    IsH3ControlledHigherOrderLift base hbase
      (weightedHigherOrderPathTimeRestrict hST high)
      (weightedH3PathTimeRestrict hST low) := by
  unfold IsH3ControlledHigherOrderLift at hlift ⊢
  rw [higherOrderRestrictionPathToThree_timeRestrict, hlift]

/-- A controlled high fixed path covered by `N` receiver-selected blocks has an explicit
`2^(N+1)` finite-aperture bound.  The extra initial factor covers the zero-width base case and
keeps the induction uniform. -/
theorem norm_higherOrderFixedPath_le_pow_two_of_time_le
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {lowBound S : ℝ} (hlowBound : 0 ≤ lowBound) (hS : 0 ≤ S)
    (N : ℕ)
    (hcover : S ≤ (N : ℝ) *
      higherOrderLowControlledPersistenceTime base nu lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (high : WeightedHigherOrderPath base S) (low : WeightedH3Path S)
    (hfixed : IsFixedPt
      (higherOrderMildMap base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hS initial) high)
    (hlift : IsH3ControlledHigherOrderLift base hbase high low)
    (hlowNorm : ‖low‖ ≤ lowBound) :
    ‖high‖ ≤ (2 : ℝ) ^ (N + 1) * ‖initial‖ := by
  let delta := higherOrderLowControlledPersistenceTime base nu lowBound
  have hdeltaPos : 0 < delta :=
    higherOrderLowControlledPersistenceTime_pos base hnu hlowBound
  have hdelta : 0 ≤ delta := hdeltaPos.le
  induction N generalizing S initial with
  | zero =>
      have hSzero : S = 0 := by
        norm_num at hcover
        linarith
      have hSBlock : S ≤ delta := by linarith
      have hlocal := norm_higherOrderFixedPath_le_two_on_lowControlledBlock
        base hbase hnu hlowBound hS hSBlock initial high low
          hfixed hlift hlowNorm
      simpa only [Nat.zero_add, pow_one] using hlocal
  | succ N ih =>
      by_cases hshort : S ≤ delta
      · have hlocal := norm_higherOrderFixedPath_le_two_on_lowControlledBlock
          base hbase hnu hlowBound hS hshort initial high low
            hfixed hlift hlowNorm
        have hp : 1 ≤ (2 : ℝ) ^ (N + 1) := one_le_pow₀ (by norm_num)
        have hpowEq : (2 : ℝ) ^ (Nat.succ N + 1) =
            2 * (2 : ℝ) ^ (N + 1) := by
          rw [show Nat.succ N + 1 = (N + 1) + 1 by omega, pow_succ]
          ring
        rw [hpowEq]
        nlinarith [norm_nonneg initial]
      · have hdeltaS : delta ≤ S := (lt_of_not_ge hshort).le
        let R : ℝ := S - delta
        have hR : 0 ≤ R := by dsimp [R]; linarith
        have hdeltaR : delta + R ≤ S := by dsimp [R]; linarith
        have hRcover : R ≤ (N : ℝ) * delta := by
          dsimp [R, delta] at hcover ⊢
          push_cast at hcover
          nlinarith
        let highFirst : WeightedHigherOrderPath base delta :=
          weightedHigherOrderPathTimeRestrict hdeltaS high
        let lowFirst : WeightedH3Path delta :=
          weightedH3PathTimeRestrict hdeltaS low
        have hfirstFixed : IsFixedPt
            (higherOrderMildMap base hbase
              (Real.toNNReal nu) (real_toNNReal_pos hnu) hdelta initial)
            highFirst := by
          exact isFixedPt_higherOrderMildMap_timeRestrict
            base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
            hdelta hS hdeltaS initial high hfixed
        have hfirstLift : IsH3ControlledHigherOrderLift
            base hbase highFirst lowFirst :=
          IsH3ControlledHigherOrderLift.timeRestrict
            base hbase hlift hdeltaS
        have hlowFirstNorm : ‖lowFirst‖ ≤ lowBound :=
          (norm_weightedH3PathTimeRestrict_le hdeltaS low).trans hlowNorm
        have hfirstBound : ‖highFirst‖ ≤ 2 * ‖initial‖ :=
          norm_higherOrderFixedPath_le_two_on_lowControlledBlock
            base hbase hnu hlowBound hdelta le_rfl initial
              highFirst lowFirst hfirstFixed hfirstLift hlowFirstNorm
        have hendpoint : ‖high ⟨delta, ⟨hdelta, hdeltaS⟩⟩‖ ≤
            2 * ‖initial‖ := by
          calc
            ‖high ⟨delta, ⟨hdelta, hdeltaS⟩⟩‖ =
                ‖highFirst ⟨delta, ⟨hdelta, le_rfl⟩⟩‖ := rfl
            _ ≤ ‖highFirst‖ := highFirst.norm_coe_le_norm _
            _ ≤ 2 * ‖initial‖ := hfirstBound
        let highShift : WeightedHigherOrderPath base R :=
          weightedHigherOrderPathTimeShift high delta R hdelta hdeltaR
        let lowShift : WeightedH3Path R :=
          weightedH3PathTimeShift low delta R hdelta hdeltaR
        have hshiftFixed : IsFixedPt
            (higherOrderMildMap base hbase
              (Real.toNNReal nu) (real_toNNReal_pos hnu) hR
              (high ⟨delta, ⟨hdelta, hdeltaS⟩⟩)) highShift := by
          exact isFixedPt_higherOrderMildMap_timeShift
            base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
              hS initial high hfixed hdelta hR hdeltaR
        have hshiftLift : IsH3ControlledHigherOrderLift
            base hbase highShift lowShift :=
          IsH3ControlledHigherOrderLift.timeShift
            base hbase hlift hdelta hdeltaR
        have hlowShiftNorm : ‖lowShift‖ ≤ lowBound :=
          (norm_weightedH3PathTimeShift_le low delta R hdelta hdeltaR).trans
            hlowNorm
        have hshiftBound : ‖highShift‖ ≤
            (2 : ℝ) ^ (N + 1) *
              ‖high ⟨delta, ⟨hdelta, hdeltaS⟩⟩‖ := by
          exact ih hR hRcover
            (high ⟨delta, ⟨hdelta, hdeltaS⟩⟩)
            highShift lowShift hshiftFixed hshiftLift hlowShiftNorm
        have hshiftBoundInitial : ‖highShift‖ ≤
            (2 : ℝ) ^ (Nat.succ N + 1) * ‖initial‖ := by
          have hscaled : (2 : ℝ) ^ (N + 1) *
                ‖high ⟨delta, ⟨hdelta, hdeltaS⟩⟩‖ ≤
              (2 : ℝ) ^ (N + 1) * (2 * ‖initial‖) :=
            mul_le_mul_of_nonneg_left hendpoint
              (pow_nonneg (by norm_num) (N + 1))
          calc
            ‖highShift‖ ≤ (2 : ℝ) ^ (N + 1) *
                ‖high ⟨delta, ⟨hdelta, hdeltaS⟩⟩‖ := hshiftBound
            _ ≤ (2 : ℝ) ^ (N + 1) * (2 * ‖initial‖) := hscaled
            _ = (2 : ℝ) ^ (Nat.succ N + 1) * ‖initial‖ := by
              rw [show Nat.succ N + 1 = (N + 1) + 1 by omega, pow_succ]
              ring
        have htargetNonneg : 0 ≤
            (2 : ℝ) ^ (Nat.succ N + 1) * ‖initial‖ :=
          mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg initial)
        apply (ContinuousMap.norm_le high htargetNonneg).2
        intro t
        by_cases ht : t.1 ≤ delta
        · have hp : 1 ≤ (2 : ℝ) ^ (N + 1) :=
            one_le_pow₀ (by norm_num)
          have hvalue : ‖high t‖ ≤ ‖highFirst‖ := by
            change ‖highFirst ⟨t.1, ⟨t.2.1, ht⟩⟩‖ ≤ ‖highFirst‖
            exact highFirst.norm_coe_le_norm _
          have hpowEq : (2 : ℝ) ^ (Nat.succ N + 1) =
              2 * (2 : ℝ) ^ (N + 1) := by
            rw [show Nat.succ N + 1 = (N + 1) + 1 by omega, pow_succ]
            ring
          rw [hpowEq]
          exact hvalue.trans (hfirstBound.trans (by
            nlinarith [norm_nonneg initial]))
        · have hdeltaT : delta ≤ t.1 := (lt_of_not_ge ht).le
          have htR : t.1 - delta ∈ Icc (0 : ℝ) R := by
            constructor
            · exact sub_nonneg.mpr hdeltaT
            · dsimp [R]; linarith [t.2.2]
          have hvalue : ‖high t‖ ≤ ‖highShift‖ := by
            have hval : high t = highShift ⟨t.1 - delta, htR⟩ := by
              apply congrArg high
              apply Subtype.ext
              dsimp only [highShift, weightedHigherOrderPathTimeShift]
              ring
            rw [hval]
            exact highShift.norm_coe_le_norm _
          exact hvalue.trans hshiftBoundInitial

/-! ## The explicit finite-aperture bound and no-Zeno return -/

/-- Number of receiver-controlled Volterra blocks needed to cover a declared finite aperture. -/
def higherOrderFiniteApertureCoverCount
    (base : ℕ) (nu lowBound T : ℝ) : ℕ :=
  Nat.ceil (T / higherOrderLowControlledPersistenceTime base nu lowBound)

theorem time_le_coverCount_mul_lowControlledTime
    (base : ℕ) {nu lowBound T : ℝ}
    (hnu : 0 < nu) (hlowBound : 0 ≤ lowBound) :
    T ≤ (higherOrderFiniteApertureCoverCount base nu lowBound T : ℝ) *
      higherOrderLowControlledPersistenceTime base nu lowBound := by
  have hdelta := higherOrderLowControlledPersistenceTime_pos
    base hnu hlowBound
  have hceil : T / higherOrderLowControlledPersistenceTime base nu lowBound ≤
      (higherOrderFiniteApertureCoverCount base nu lowBound T : ℝ) := by
    exact Nat.le_ceil _
  exact (div_le_iff₀ hdelta).mp hceil

/-- Explicit high-order bound on a finite native aperture. -/
def higherOrderFiniteApertureBound
    (base : ℕ) (nu lowBound T : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) : ℝ :=
  (2 : ℝ) ^ (higherOrderFiniteApertureCoverCount base nu lowBound T + 1) *
    ‖initial‖

theorem higherOrderFiniteApertureBound_nonneg
    (base : ℕ) (nu lowBound T : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    0 ≤ higherOrderFiniteApertureBound base nu lowBound T initial :=
  mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg initial)

/-- **Uniform finite-aperture persistence bound.** Every actual high fixed path controlled by a
bounded native `H³` receiver is bounded solely by its initial high norm, viscosity, order, native
bound, and terminal aperture.  No restart count or high endpoint norm enters the assumptions. -/
theorem norm_higherOrderFixedPath_le_finiteApertureBound
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {lowBound T S : ℝ} (hlowBound : 0 ≤ lowBound)
    (hS : 0 ≤ S) (hST : S ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (high : WeightedHigherOrderPath base S) (low : WeightedH3Path S)
    (hfixed : IsFixedPt
      (higherOrderMildMap base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hS initial) high)
    (hlift : IsH3ControlledHigherOrderLift base hbase high low)
    (hlowNorm : ‖low‖ ≤ lowBound) :
    ‖high‖ ≤ higherOrderFiniteApertureBound
      base nu lowBound T initial := by
  let N := higherOrderFiniteApertureCoverCount base nu lowBound T
  have hcoverT : T ≤ (N : ℝ) *
      higherOrderLowControlledPersistenceTime base nu lowBound :=
    time_le_coverCount_mul_lowControlledTime base hnu hlowBound
  have hcoverS : S ≤ (N : ℝ) *
      higherOrderLowControlledPersistenceTime base nu lowBound :=
    hST.trans hcoverT
  exact norm_higherOrderFixedPath_le_pow_two_of_time_le
    base hbase hnu hlowBound hS N hcoverS initial high low
      hfixed hlift hlowNorm

/-- Every endpoint of such a partial high path inherits the same finite-aperture bound. -/
theorem norm_higherOrderFixedPath_endpoint_le_finiteApertureBound
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {lowBound T S : ℝ} (hlowBound : 0 ≤ lowBound)
    (hS : 0 ≤ S) (hST : S ≤ T)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (high : WeightedHigherOrderPath base S) (low : WeightedH3Path S)
    (hfixed : IsFixedPt
      (higherOrderMildMap base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) hS initial) high)
    (hlift : IsH3ControlledHigherOrderLift base hbase high low)
    (hlowNorm : ‖low‖ ≤ lowBound) :
    ‖high ⟨S, ⟨hS, le_rfl⟩⟩‖ ≤
      higherOrderFiniteApertureBound base nu lowBound T initial := by
  exact (high.norm_coe_le_norm ⟨S, ⟨hS, le_rfl⟩⟩).trans
    (norm_higherOrderFixedPath_le_finiteApertureBound
      base hbase hnu hlowBound hS hST initial high low
        hfixed hlift hlowNorm)

/-- **No-Zeno receipt for the actual partial-path family.** Any family of compatible partial
high mild paths along one bounded native path has a common positive shifted restart aperture.
This feeds `shiftedHigherOrderUniformCompatibilityTime` directly and rules out collapse of the
successive local apertures. -/
theorem exists_uniform_positive_shiftedAperture_for_partialFixedPaths
    {I : Type*} (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {lowBound T : ℝ} (hlowBound : 0 ≤ lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (native : WeightedH3Path T) (hnativeNorm : ‖native‖ ≤ lowBound)
    (time : I → ℝ) (htime : ∀ i, 0 ≤ time i ∧ time i ≤ T)
    (high : (i : I) → WeightedHigherOrderPath base (time i))
    (hfixed : ∀ i, IsFixedPt
      (higherOrderMildMap base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu) (htime i).1 initial) (high i))
    (hlift : ∀ i, IsH3ControlledHigherOrderLift base hbase (high i)
      (weightedH3PathTimeRestrict (htime i).2 native)) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ i,
      delta ≤ shiftedHigherOrderCompatibilityTime base nu
        (high i ⟨time i, ⟨(htime i).1, le_rfl⟩⟩) lowBound := by
  let highBound := higherOrderFiniteApertureBound
    base nu lowBound T initial
  have hhighBound : 0 ≤ highBound :=
    higherOrderFiniteApertureBound_nonneg base nu lowBound T initial
  have hendpoint : ∀ i,
      ‖high i ⟨time i, ⟨(htime i).1, le_rfl⟩⟩‖ ≤ highBound := by
    intro i
    have hnativeRestrict :
        ‖weightedH3PathTimeRestrict (htime i).2 native‖ ≤ lowBound :=
      (norm_weightedH3PathTimeRestrict_le (htime i).2 native).trans hnativeNorm
    exact norm_higherOrderFixedPath_endpoint_le_finiteApertureBound
      base hbase hnu hlowBound (htime i).1 (htime i).2 initial
      (high i) (weightedH3PathTimeRestrict (htime i).2 native)
      (hfixed i) (hlift i) hnativeRestrict
  exact exists_uniform_positive_shiftedAperture_of_endpointBound
    base hnu hlowBound hhighBound
      (fun i ↦ high i ⟨time i, ⟨(htime i).1, le_rfl⟩⟩) hendpoint

/-! ## Kernel audit -/

section Audit

#print axioms isFixedPt_higherOrderMildMap_timeShift
#print axioms isFixedPt_higherOrderMildMap_concat
#print axioms higherOrderLowControlledFactor_lt_half
#print axioms norm_higherOrderFixedPath_le_two_on_lowControlledBlock
#print axioms norm_higherOrderFixedPath_le_pow_two_of_time_le
#print axioms norm_higherOrderFixedPath_le_finiteApertureBound
#print axioms exists_uniform_positive_shiftedAperture_for_partialFixedPaths

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedFractionalVolterraPersistence
