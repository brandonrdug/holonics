import ElementaryHolonics.Millennium.NavierStokesWeightedFractionalVolterraPersistence
import ElementaryHolonics.Millennium.NavierStokesWeightedSmoothPathTower

/-!
# Finite-aperture arbitrary-order persistence

**[proved-derived]** The receiver-controlled fractional-Volterra bound supplies a uniform
positive restart width for every endpoint of every partial higher-order fixed path.  This owner
spends that width through a finite dependent recurrence, glues each returned segment with its
retained endpoint equality, and returns one higher-order mild fixed path on the complete native
`H³` aperture.  Repeating the construction at every finite Sobolev order packages the paths as
the coherent smooth tower consumed by the classical restart carrier.

No compactness, limiting path, bounded-endpoint premise, or additional analytic inequality enters
the construction.  The recurrence is finite and its cover count is the ceiling of the declared
terminal aperture divided by the already proved uniform positive width.
-/

noncomputable section

open Function Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedFiniteApertureHigherOrderPersistence

open Soma.Holonics.Millennium.NavierStokesWeightedCommonApertureUniqueness
open Soma.Holonics.Millennium.NavierStokesWeightedFractionalVolterraPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderDuhamelLift
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedShiftedHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## A finite uniform restart grid -/

/-- Successive time faces obtained by spending a fixed width until the terminal face is reached. -/
def finiteApertureRestartGridTime (T delta : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      let a := finiteApertureRestartGridTime T delta n
      a + min (T - a) delta

@[simp]
theorem finiteApertureRestartGridTime_zero (T delta : ℝ) :
    finiteApertureRestartGridTime T delta 0 = 0 :=
  rfl

theorem finiteApertureRestartGridTime_le_terminal
    {T delta : ℝ} (hT : 0 ≤ T) :
    ∀ n, finiteApertureRestartGridTime T delta n ≤ T := by
  intro n
  induction n with
  | zero => simpa using hT
  | succ n ih =>
      rw [finiteApertureRestartGridTime]
      have hstep := min_le_left
        (T - finiteApertureRestartGridTime T delta n) delta
      linarith

theorem finiteApertureRestartGridTime_nonneg
    {T delta : ℝ} (hT : 0 ≤ T) (hdelta : 0 ≤ delta) :
    ∀ n, 0 ≤ finiteApertureRestartGridTime T delta n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finiteApertureRestartGridTime]
      exact add_nonneg ih
        (le_min
          (sub_nonneg.mpr (finiteApertureRestartGridTime_le_terminal hT n))
          hdelta)

theorem finiteApertureRestartGridTime_mono_step
    {T delta : ℝ} (hT : 0 ≤ T) (hdelta : 0 ≤ delta) (n : ℕ) :
    finiteApertureRestartGridTime T delta n ≤
      finiteApertureRestartGridTime T delta (n + 1) := by
  rw [finiteApertureRestartGridTime]
  exact le_add_of_nonneg_right (le_min
    (sub_nonneg.mpr (finiteApertureRestartGridTime_le_terminal hT n)) hdelta)

theorem monotone_finiteApertureRestartGridTime
    {T delta : ℝ} (hT : 0 ≤ T) (hdelta : 0 ≤ delta) :
    Monotone (finiteApertureRestartGridTime T delta) := by
  exact monotone_nat_of_le_succ
    (finiteApertureRestartGridTime_mono_step hT hdelta)

theorem finiteApertureRestartGridTime_reaches_or_advances
    {T delta : ℝ} (n : ℕ) :
    finiteApertureRestartGridTime T delta n < T →
      finiteApertureRestartGridTime T delta (n + 1) = T ∨
        finiteApertureRestartGridTime T delta n + delta ≤
          finiteApertureRestartGridTime T delta (n + 1) := by
  intro hnT
  rw [finiteApertureRestartGridTime]
  by_cases hremaining :
      T - finiteApertureRestartGridTime T delta n ≤ delta
  · left
    rw [min_eq_left hremaining]
    ring
  · right
    rw [min_eq_right (le_of_not_ge hremaining)]

theorem finiteApertureRestartGridTime_eq_terminal_of_cover
    {T delta : ℝ} (hT : 0 ≤ T) (hdelta : 0 < delta)
    (N : ℕ) (hcover : T ≤ (N : ℝ) * delta) :
    finiteApertureRestartGridTime T delta N = T := by
  have hupper := finiteApertureRestartGridTime_le_terminal (delta := delta) hT
  by_contra hne
  have hNlt : finiteApertureRestartGridTime T delta N < T :=
    lt_of_le_of_ne (hupper N) hne
  have hmono := monotone_finiteApertureRestartGridTime hT hdelta.le
  have huncovered : ∀ n, n ≤ N →
      finiteApertureRestartGridTime T delta n < T := by
    intro n hn
    exact (hmono hn).trans_lt hNlt
  exact finite_cover_excludes_strictly_uncovered_schedule
    (finiteApertureRestartGridTime T delta)
    (finiteApertureRestartGridTime_zero T delta)
    hupper
    (finiteApertureRestartGridTime_reaches_or_advances)
    N hcover huncovered

/-! ## The uniform endpoint-controlled width -/

/-- The positive continuation width obtained after substituting the proved finite-aperture high
bound into both state-dependent restart loads. -/
def finiteApertureHigherOrderUniformStep
    (base : ℕ) (nu lowBound T : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) : ℝ :=
  shiftedHigherOrderUniformCompatibilityTime base nu
    (higherOrderFiniteApertureBound base nu lowBound T initial) lowBound

theorem finiteApertureHigherOrderUniformStep_pos
    (base : ℕ) {nu lowBound T : ℝ}
    (hnu : 0 < nu) (hlowBound : 0 ≤ lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    0 < finiteApertureHigherOrderUniformStep
      base nu lowBound T initial := by
  exact shiftedHigherOrderUniformCompatibilityTime_pos
    base hnu
      (higherOrderFiniteApertureBound_nonneg
        base nu lowBound T initial)
      hlowBound

/-- The explicit ceiling count for the finite dependent continuation. -/
def finiteApertureHigherOrderCoverCount
    (base : ℕ) (nu lowBound T : ℝ)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) : ℕ :=
  Nat.ceil (T / finiteApertureHigherOrderUniformStep
    base nu lowBound T initial)

theorem terminal_le_finiteApertureHigherOrderCover
    (base : ℕ) {nu lowBound T : ℝ}
    (hnu : 0 < nu) (hlowBound : 0 ≤ lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1)) :
    T ≤ (finiteApertureHigherOrderCoverCount
        base nu lowBound T initial : ℝ) *
      finiteApertureHigherOrderUniformStep base nu lowBound T initial := by
  have hdelta := finiteApertureHigherOrderUniformStep_pos
    base (T := T) hnu hlowBound initial
  have hceil :
      T / finiteApertureHigherOrderUniformStep base nu lowBound T initial ≤
        (finiteApertureHigherOrderCoverCount
          base nu lowBound T initial : ℝ) :=
    Nat.le_ceil _
  exact (div_le_iff₀ hdelta).mp hceil

/-! ## Dependent partial paths -/

/-- One constructed partial high path, retaining its complete recurrence and its exact receiver
identity with the corresponding initial face of the native path. -/
structure HigherOrderPartialPersistence
    (base : ℕ) (hbase : 2 ≤ base)
    (nu : ℝ) (hnu : 0 < nu)
    {T : ℝ}
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (native : WeightedH3Path T) (A : ℝ) where
  time_nonneg : 0 ≤ A
  time_le : A ≤ T
  path : WeightedHigherOrderPath base A
  fixed : IsFixedPt
    (higherOrderMildMap base hbase
      (Real.toNNReal nu) (real_toNNReal_pos hnu) time_nonneg initial) path
  controlled : IsH3ControlledHigherOrderLift base hbase path
    (weightedH3PathTimeShift native 0 A le_rfl (by simpa using time_le))

/-- The zero face is a genuine (zero-aperture) partial persistence witness, returned through the
same local existence and uniqueness owner used at every later step. -/
theorem exists_higherOrderPartialPersistence_zero
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {T : ℝ} (hT : 0 ≤ T)
    (lowInitial : PeriodicVectorWeightedSobolev 3)
    (native : WeightedH3Path T)
    (hnativeFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        hT lowInitial) native)
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound)
    (hnativeNorm : ‖native‖ ≤ lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hinitialReceiver :
      periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial =
        native ⟨0, ⟨le_rfl, hT⟩⟩) :
    Nonempty (HigherOrderPartialPersistence
      base hbase nu hnu initial native 0) := by
  have hcompat : 0 ≤
      shiftedHigherOrderCompatibilityTime base nu initial lowBound :=
    (shiftedHigherOrderCompatibilityTime_pos
      base hnu initial hlowBound).le
  obtain ⟨high, hfixed, _hnorm, hlift, _hzero⟩ :=
    exists_shiftedHigherOrderPersistenceStep_of_le
      base hbase hnu hT lowInitial native hnativeFixed
      hlowBound hnativeNorm le_rfl le_rfl initial hcompat
      (by simpa using hT) hinitialReceiver
  refine ⟨{
    time_nonneg := le_rfl
    time_le := hT
    path := high
    fixed := ?_
    controlled := ?_ }⟩
  · exact hfixed
  · exact hlift

/-- Extend one partial path by any nonnegative duration below the uniform endpoint-controlled
width.  The new local path is based at the actual old endpoint; its returned zero-face equality
is the join witness for both the global mild recurrence and the native receiver. -/
theorem HigherOrderPartialPersistence.extend_of_le_uniformStep
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {T : ℝ} (hT : 0 ≤ T)
    (lowInitial : PeriodicVectorWeightedSobolev 3)
    (native : WeightedH3Path T)
    (hnativeFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        hT lowInitial) native)
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound)
    (hnativeNorm : ‖native‖ ≤ lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    {A B : ℝ}
    (prior : HigherOrderPartialPersistence
      base hbase nu hnu initial native A)
    (hB : 0 ≤ B) (hABT : A + B ≤ T)
    (hBstep : B ≤ finiteApertureHigherOrderUniformStep
      base nu lowBound T initial) :
    Nonempty (HigherOrderPartialPersistence
      base hbase nu hnu initial native (A + B)) := by
  let lowPartial : WeightedH3Path A :=
    weightedH3PathTimeShift native 0 A le_rfl (by simpa using prior.time_le)
  have hlowPartialNorm : ‖lowPartial‖ ≤ lowBound :=
    (norm_weightedH3PathTimeShift_le
      native 0 A le_rfl (by simpa using prior.time_le)).trans hnativeNorm
  let endpoint : PeriodicVectorWeightedSobolev (base + 1) :=
    prior.path ⟨A, ⟨prior.time_nonneg, le_rfl⟩⟩
  let highBound := higherOrderFiniteApertureBound
    base nu lowBound T initial
  have hhighBound : 0 ≤ highBound :=
    higherOrderFiniteApertureBound_nonneg
      base nu lowBound T initial
  have hendpointBound : ‖endpoint‖ ≤ highBound := by
    exact norm_higherOrderFixedPath_endpoint_le_finiteApertureBound
      base hbase hnu hlowBound prior.time_nonneg prior.time_le
      initial prior.path lowPartial prior.fixed prior.controlled
      hlowPartialNorm
  have hstepCompatibility :
      finiteApertureHigherOrderUniformStep base nu lowBound T initial ≤
        shiftedHigherOrderCompatibilityTime base nu endpoint lowBound := by
    exact shiftedHigherOrderUniformCompatibilityTime_le
      base hnu hhighBound hlowBound endpoint hendpointBound
  have hBCompatibility : B ≤
      shiftedHigherOrderCompatibilityTime base nu endpoint lowBound :=
    hBstep.trans hstepCompatibility
  have hinitialReceiver :
      periodicVectorWeightedRestrictToThree (base + 1) (by omega) endpoint =
        native ⟨A, ⟨prior.time_nonneg, prior.time_le⟩⟩ := by
    have hreceiverAt := congrArg
      (fun path : WeightedH3Path A ↦
        path ⟨A, ⟨prior.time_nonneg, le_rfl⟩⟩)
      prior.controlled
    simpa only [lowPartial, weightedH3PathTimeShift_apply, zero_add]
      using hreceiverAt
  obtain ⟨right, hrightFixed, _hrightNorm, hrightControlled, hrightZero⟩ :=
    exists_shiftedHigherOrderPersistenceStep_of_le
      base hbase hnu hT lowInitial native hnativeFixed
      hlowBound hnativeNorm prior.time_nonneg hB endpoint
      hBCompatibility hABT hinitialReceiver
  have hjoin :
      prior.path ⟨A, ⟨prior.time_nonneg, le_rfl⟩⟩ =
        right ⟨0, ⟨le_rfl, hB⟩⟩ :=
    hrightZero.symm
  let joined : WeightedHigherOrderPath base (A + B) :=
    weightedIntervalPathConcat prior.time_nonneg hB
      prior.path right hjoin
  have hjoinedFixed : IsFixedPt
      (higherOrderMildMap base hbase
        (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (add_nonneg prior.time_nonneg hB) initial) joined := by
    exact isFixedPt_higherOrderMildMap_concat
      base hbase (Real.toNNReal nu) (real_toNNReal_pos hnu)
      prior.time_nonneg hB initial prior.path right
      prior.fixed hjoin hrightFixed
  have hjoinedControlled : IsH3ControlledHigherOrderLift
      base hbase joined
        (weightedH3PathTimeShift native 0 (A + B) le_rfl
          (by simpa using hABT)) := by
    have hrightControlled' : IsH3ControlledHigherOrderLift base hbase right
        (weightedH3PathTimeShift native (0 + A) B
          (by simpa using prior.time_nonneg) (by simpa using hABT)) := by
      simpa only [zero_add] using hrightControlled
    exact IsH3ControlledHigherOrderLift.concat
      base hbase native le_rfl prior.time_nonneg hB
      (by simpa using hABT) prior.path right hjoin
      prior.controlled hrightControlled'
  refine ⟨{
    time_nonneg := add_nonneg prior.time_nonneg hB
    time_le := hABT
    path := joined
    fixed := ?_
    controlled := ?_ }⟩
  · exact hjoinedFixed
  · exact hjoinedControlled

/-! ## Finite dependent iteration -/

theorem exists_higherOrderPartialPersistence_on_restartGrid
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {T : ℝ} (hT : 0 ≤ T)
    (lowInitial : PeriodicVectorWeightedSobolev 3)
    (native : WeightedH3Path T)
    (hnativeFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        hT lowInitial) native)
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound)
    (hnativeNorm : ‖native‖ ≤ lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hinitialReceiver :
      periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial =
        native ⟨0, ⟨le_rfl, hT⟩⟩) :
    ∀ n : ℕ,
      Nonempty (HigherOrderPartialPersistence
        base hbase nu hnu initial native
        (finiteApertureRestartGridTime T
          (finiteApertureHigherOrderUniformStep
            base nu lowBound T initial) n)) := by
  intro n
  induction n with
  | zero =>
      simpa only [finiteApertureRestartGridTime_zero] using
        exists_higherOrderPartialPersistence_zero
          base hbase hnu hT lowInitial native hnativeFixed
          hlowBound hnativeNorm initial hinitialReceiver
  | succ n ih =>
      let delta := finiteApertureHigherOrderUniformStep
        base nu lowBound T initial
      let A := finiteApertureRestartGridTime T delta n
      let B := min (T - A) delta
      have hdelta : 0 < delta :=
        finiteApertureHigherOrderUniformStep_pos
          base (T := T) hnu hlowBound initial
      have hA : 0 ≤ A :=
        finiteApertureRestartGridTime_nonneg hT hdelta.le n
      have hAT : A ≤ T :=
        finiteApertureRestartGridTime_le_terminal hT n
      have hB : 0 ≤ B :=
        le_min (sub_nonneg.mpr hAT) hdelta.le
      have hABT : A + B ≤ T := by
        have hleft := min_le_left (T - A) delta
        dsimp only [B]
        linarith
      have hBstep : B ≤ delta := min_le_right _ _
      change Nonempty (HigherOrderPartialPersistence
        base hbase nu hnu initial native A) at ih
      obtain ⟨prior⟩ := ih
      have hnext :=
        HigherOrderPartialPersistence.extend_of_le_uniformStep
          base hbase hnu hT lowInitial native hnativeFixed
          hlowBound hnativeNorm initial prior hB hABT hBstep
      simpa only [finiteApertureRestartGridTime, delta, A, B,
        Nat.succ_eq_add_one] using hnext

/-- Translating a path from its zero face over its complete aperture returns the path itself. -/
theorem weightedH3PathTimeShift_zero_full
    {T : ℝ} (path : WeightedH3Path T) :
    weightedH3PathTimeShift path 0 T le_rfl (by simp) = path := by
  apply ContinuousMap.ext
  intro t
  apply congrArg path
  apply Subtype.ext
  simp

/-- **Full finite-aperture arbitrary-order persistence.** For every finite high Sobolev order,
one complete high mild fixed path exists on the actual native `H³` aperture and restricts exactly
to that native path.  Its explicit norm bound is inherited from the fractional-Volterra owner. -/
theorem exists_higherOrderPersistence_on_finite_nativeAperture
    (base : ℕ) (hbase : 2 ≤ base)
    {nu : ℝ} (hnu : 0 < nu)
    {T : ℝ} (hT : 0 ≤ T)
    (lowInitial : PeriodicVectorWeightedSobolev 3)
    (native : WeightedH3Path T)
    (hnativeFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        hT lowInitial) native)
    {lowBound : ℝ} (hlowBound : 0 ≤ lowBound)
    (hnativeNorm : ‖native‖ ≤ lowBound)
    (initial : PeriodicVectorWeightedSobolev (base + 1))
    (hinitialReceiver :
      periodicVectorWeightedRestrictToThree (base + 1) (by omega) initial =
        native ⟨0, ⟨le_rfl, hT⟩⟩) :
    ∃ high : WeightedHigherOrderPath base T,
      IsFixedPt
          (higherOrderMildMap base hbase
            (Real.toNNReal nu) (real_toNNReal_pos hnu) hT initial) high ∧
        IsH3ControlledHigherOrderLift base hbase high native ∧
        ‖high‖ ≤ higherOrderFiniteApertureBound
          base nu lowBound T initial := by
  let delta := finiteApertureHigherOrderUniformStep
    base nu lowBound T initial
  let N := finiteApertureHigherOrderCoverCount
    base nu lowBound T initial
  have hdelta : 0 < delta :=
    finiteApertureHigherOrderUniformStep_pos
      base (T := T) hnu hlowBound initial
  have hcover : T ≤ (N : ℝ) * delta :=
    terminal_le_finiteApertureHigherOrderCover
      base hnu hlowBound initial
  have hgrid : finiteApertureRestartGridTime T delta N = T :=
    finiteApertureRestartGridTime_eq_terminal_of_cover
      hT hdelta N hcover
  have hgridWitness :=
    exists_higherOrderPartialPersistence_on_restartGrid
      base hbase hnu hT lowInitial native hnativeFixed
      hlowBound hnativeNorm initial hinitialReceiver N
  change Nonempty (HigherOrderPartialPersistence
    base hbase nu hnu initial native
      (finiteApertureRestartGridTime T delta N)) at hgridWitness
  rw [hgrid] at hgridWitness
  obtain ⟨complete⟩ := hgridWitness
  have hcontrolled : IsH3ControlledHigherOrderLift
      base hbase complete.path native := by
    have hcontrolledShift := complete.controlled
    unfold IsH3ControlledHigherOrderLift at hcontrolledShift ⊢
    exact hcontrolledShift.trans
      (weightedH3PathTimeShift_zero_full native)
  have hnorm : ‖complete.path‖ ≤
      higherOrderFiniteApertureBound base nu lowBound T initial :=
    norm_higherOrderFixedPath_le_finiteApertureBound
      base hbase hnu hlowBound complete.time_nonneg complete.time_le
      initial complete.path native complete.fixed hcontrolled hnativeNorm
  exact ⟨complete.path, complete.fixed, hcontrolled, hnorm⟩

/-! ## All finite orders on one native path -/

/-- A fixed native mild path whose initial state is supplied coherently at every finite weighted
Sobolev order carries one coherent smooth path tower on its complete aperture.  Every tower lift
retains its own exact arbitrary-order mild recurrence and explicit finite-aperture bound. -/
theorem exists_coherentWeightedSmoothPathTower_of_nativeFixed
    {nu : ℝ} (hnu : 0 < nu)
    {T : ℝ} (hT : 0 ≤ T)
    (initialTower : CompatibleNativeWeightedSobolevTower)
    (native : WeightedH3Path T)
    (hnativeFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        hT initialTower.base) native) :
    ∃ tower : CoherentWeightedSmoothPathTower native,
      (∀ m : ℕ, IsFixedPt
        (higherOrderMildMap (m + 2) (by omega)
          (Real.toNNReal nu) (real_toNNReal_pos hnu) hT
          (initialTower.lift m)) (tower.lift m)) ∧
      (∀ m : ℕ, ‖tower.lift m‖ ≤
        higherOrderFiniteApertureBound
          (m + 2) nu ‖native‖ T (initialTower.lift m)) := by
  have hnativeInitial : initialTower.base = native ⟨0, ⟨le_rfl, hT⟩⟩ := by
    have hfixedZero := congrArg
      (fun path : WeightedH3Path T ↦ path ⟨0, ⟨le_rfl, hT⟩⟩)
      hnativeFixed
    simpa only [weightedMildMap_zero] using hfixedZero
  have hexists : ∀ m : ℕ,
      ∃ high : WeightedHigherOrderPath (m + 2) T,
        IsFixedPt
            (higherOrderMildMap (m + 2) (by omega)
              (Real.toNNReal nu) (real_toNNReal_pos hnu) hT
              (initialTower.lift m)) high ∧
          IsH3ControlledHigherOrderLift (m + 2) (by omega) high native ∧
          ‖high‖ ≤ higherOrderFiniteApertureBound
            (m + 2) nu ‖native‖ T (initialTower.lift m) := by
    intro m
    apply exists_higherOrderPersistence_on_finite_nativeAperture
      (m + 2) (by omega) hnu hT initialTower.base native hnativeFixed
      (norm_nonneg native) le_rfl (initialTower.lift m)
    exact (initialTower.restrict_lift m).trans hnativeInitial
  choose high hhighFixed hhighControlled hhighNorm using hexists
  let tower : CoherentWeightedSmoothPathTower native :=
    { lift := high
      restrict_lift := by
        intro m t
        have hpath := hhighControlled m
        unfold IsH3ControlledHigherOrderLift at hpath
        have hface := congrArg
          (fun path : WeightedH3Path T ↦ path t) hpath
        exact hface }
  refine ⟨tower, ?_, ?_⟩
  · intro m
    exact hhighFixed m
  · intro m
    exact hhighNorm m

/-- Consequently every addressed face of the constructed all-order path population reconstructs
as one actual real periodic spatially smooth velocity. -/
theorem exists_coherentWeightedSmoothPathTower_with_spatialSmoothness
    {nu : ℝ} (hnu : 0 < nu)
    {T : ℝ} (hT : 0 ≤ T)
    (initialTower : CompatibleNativeWeightedSobolevTower)
    (native : WeightedH3Path T)
    (hnativeFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        hT initialTower.base) native) :
    ∃ tower : CoherentWeightedSmoothPathTower native,
      (∀ m : ℕ, IsFixedPt
        (higherOrderMildMap (m + 2) (by omega)
          (Real.toNNReal nu) (real_toNNReal_pos hnu) hT
          (initialTower.lift m)) (tower.lift m)) ∧
      ∀ t : Icc (0 : ℝ) T,
        ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
          (tower.reconstructedVelocity t) := by
  obtain ⟨tower, hfixed, _hnorm⟩ :=
    exists_coherentWeightedSmoothPathTower_of_nativeFixed
      hnu hT initialTower native hnativeFixed
  exact ⟨tower, hfixed,
    fun t ↦ tower.contDiff_infty_reconstructedVelocity t⟩

/-! ## Kernel audit -/

section Audit

#print axioms finiteApertureRestartGridTime_eq_terminal_of_cover
#print axioms HigherOrderPartialPersistence.extend_of_le_uniformStep
#print axioms exists_higherOrderPartialPersistence_on_restartGrid
#print axioms exists_higherOrderPersistence_on_finite_nativeAperture
#print axioms exists_coherentWeightedSmoothPathTower_of_nativeFixed
#print axioms exists_coherentWeightedSmoothPathTower_with_spatialSmoothness

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedFiniteApertureHigherOrderPersistence
