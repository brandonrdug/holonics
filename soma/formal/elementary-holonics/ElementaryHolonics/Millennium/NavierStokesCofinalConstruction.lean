import ElementaryHolonics.Millennium.NavierStokesPressureNormalization

/-!
# Cofinal construction from local existence and compatible continuation

**[proved-derived]** Origin-normalized open periodic solutions agree exactly on overlaps.  The
supremum of their attainable lifetimes can therefore be realized by a locally selected union.  If
that supremum were finite, the universally supplied compatible extension would produce a strictly
larger attainable lifetime.  Hence normalized lifetimes are unbounded, and one shared selected
union supplies every finite open slab of a `CofinalPeriodicAtlas`.
-/

noncomputable section

open Filter Set

namespace Soma.Holonics.Millennium.NavierStokesCofinalConstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOfficialBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOverlapUniqueness
open Soma.Holonics.Millennium.NavierStokesPressureNormalization
open Soma.Holonics.Millennium.NavierStokesRestartSeam

/-- Every positive-viscosity official open solution has a strict compatible extension. -/
def PositivePeriodicCompatibleExtensionLaw : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      Nonempty (CompatibleOpenPeriodicExtension solution)

/-- One pressure-normalized member of the official open-lifespan family. -/
structure NormalizedPeriodicState (nu : ℝ) (initial : InitialVelocity) where
  lifetime : ℝ
  velocity : VelocityField
  pressure : PressureField
  solution : OpenPeriodicSolutionOn lifetime nu initial (0 : VelocityField) velocity pressure
  pressureNormalized : PressureNormalized pressure

/-- Rebase any official open solution into the origin-normalized state family. -/
def normalizedPeriodicStateOfSolution
    {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    NormalizedPeriodicState nu initial where
  lifetime := T
  velocity := velocity
  pressure := anchoredPressure pressure
  solution :=
    Soma.Holonics.Millennium.NavierStokesPressureNormalization.OpenPeriodicSolutionOn.normalizePressure
      solution
  pressureNormalized :=
    Soma.Holonics.Millennium.NavierStokesPressureNormalization.OpenPeriodicSolutionOn.normalizePressure_pressureNormalized
      solution

/-- Local existence supplies a first normalized state. -/
theorem nonempty_normalizedPeriodicState
    (localExistence : HasPeriodicLocalExistence)
    {nu : ℝ} (hnu : 0 < nu) {initial : InitialVelocity}
    (hinitial : InitialVelocityConditionPeriodic initial) :
    Nonempty (NormalizedPeriodicState nu initial) := by
  obtain ⟨T, velocity, pressure, _hT, solution⟩ :=
    localExistence nu hnu initial hinitial
  exact ⟨normalizedPeriodicStateOfSolution solution⟩

/-- The set of lifetimes represented by normalized official states. -/
def normalizedPeriodicLifetimes (nu : ℝ) (initial : InitialVelocity) : Set ℝ :=
  Set.range (NormalizedPeriodicState.lifetime (nu := nu) (initial := initial))

theorem normalizedPeriodicLifetimes_nonempty
    {nu : ℝ} {initial : InitialVelocity}
    (base : NormalizedPeriodicState nu initial) :
    (normalizedPeriodicLifetimes nu initial).Nonempty :=
  ⟨base.lifetime, ⟨base, rfl⟩⟩

/-! ## Exact normalized overlap -/

/-- Two normalized official states have exactly equal velocity at every common admitted time. -/
theorem normalizedPeriodicState_velocity_eq
    {nu : ℝ} {initial : InitialVelocity}
    (uniqueness : PeriodicOpenUniqueness) (hnu : 0 < nu)
    (left right : NormalizedPeriodicState nu initial)
    (x : Space) {t : ℝ} (ht : 0 ≤ t)
    (htLeft : t < left.lifetime) (htRight : t < right.lifetime) :
    left.velocity x t = right.velocity x t := by
  let overlap : ℝ := min left.lifetime right.lifetime
  have hoverlap : 0 < overlap :=
    lt_min left.solution.terminal_pos right.solution.terminal_pos
  let leftOn := left.solution.restrict hoverlap (min_le_left _ _)
  let rightOn := right.solution.restrict hoverlap (min_le_right _ _)
  have hagree := uniqueness.unique hnu leftOn rightOn
  exact hagree.velocity x t ⟨ht, lt_min htLeft htRight⟩

/-- Pressure normalization turns overlap agreement modulo gradient into exact pressure equality. -/
theorem normalizedPeriodicState_pressure_eq
    {nu : ℝ} {initial : InitialVelocity}
    (uniqueness : PeriodicOpenUniqueness) (hnu : 0 < nu)
    (left right : NormalizedPeriodicState nu initial)
    (x : Space) {t : ℝ} (ht : 0 ≤ t)
    (htLeft : t < left.lifetime) (htRight : t < right.lifetime) :
    left.pressure x t = right.pressure x t := by
  let overlap : ℝ := min left.lifetime right.lifetime
  have hoverlap : 0 < overlap :=
    lt_min left.solution.terminal_pos right.solution.terminal_pos
  let leftOn := left.solution.restrict hoverlap (min_le_left _ _)
  let rightOn := right.solution.restrict hoverlap (min_le_right _ _)
  have hagree := uniqueness.unique hnu leftOn rightOn
  have hleftSmooth :=
    Soma.Holonics.Millennium.NavierStokesOverlapUniqueness.OpenPeriodicSolutionOn.pressureSpatialSmooth
      left.solution ⟨ht, htLeft⟩
  have hrightSmooth :=
    Soma.Holonics.Millennium.NavierStokesOverlapUniqueness.OpenPeriodicSolutionOn.pressureSpatialSmooth
      right.solution ⟨ht, htRight⟩
  have hanchored := anchored_eq_of_gradient_eq
    (fun y ↦ left.pressure y t) (fun y ↦ right.pressure y t)
    hleftSmooth hrightSmooth
    (fun y ↦ hagree.pressureGradient y t ⟨ht, lt_min htLeft htRight⟩) x
  rw [left.pressureNormalized t ht, right.pressureNormalized t ht] at hanchored
  simpa only [sub_zero] using hanchored

/-! ## Local gluing of a selected normalized family -/

/-- A selection chooses one normalized lifespan occurrence at every time receiver. -/
abbrev NormalizedPeriodicSelection (nu : ℝ) (initial : InitialVelocity) :=
  ℝ → NormalizedPeriodicState nu initial

def selectedPeriodicVelocity
    {nu : ℝ} {initial : InitialVelocity}
    (selection : NormalizedPeriodicSelection nu initial) : VelocityField :=
  fun x t ↦ (selection t).velocity x t

def selectedPeriodicPressure
    {nu : ℝ} {initial : InitialVelocity}
    (selection : NormalizedPeriodicSelection nu initial) : PressureField :=
  fun x t ↦ (selection t).pressure x t

/-- Coverage means the selected occurrence at every admitted time extends strictly past it. -/
def SelectionCoversBefore
    {nu : ℝ} {initial : InitialVelocity}
    (selection : NormalizedPeriodicSelection nu initial) (T : ℝ) : Prop :=
  ∀ t, t ∈ openTimeSlab T → t < (selection t).lifetime

theorem selectedPeriodicPressure_normalized
    {nu : ℝ} {initial : InitialVelocity}
    (selection : NormalizedPeriodicSelection nu initial) :
    PressureNormalized (selectedPeriodicPressure selection) := by
  intro t ht
  exact (selection t).pressureNormalized t ht

/-- Two half-open time slabs with a common admitted time have the same germ there. -/
theorem openTimeSlab_eventuallyEq_of_lt
    {t S T : ℝ} (htS : t < S) (htT : t < T) :
    openTimeSlab S =ᶠ[nhds t] openTimeSlab T := by
  filter_upwards [Iio_mem_nhds htS, Iio_mem_nhds htT] with s hsS hsT
  apply propext
  constructor
  · rintro ⟨hs, _⟩
    exact ⟨hs, hsT⟩
  · rintro ⟨hs, _⟩
    exact ⟨hs, hsS⟩

/-- The corresponding space--time slabs have the same germ at a common admitted point. -/
theorem openSpaceTimeSlab_eventuallyEq_of_lt
    {z : Space × ℝ} {S T : ℝ} (hzS : z.2 < S) (hzT : z.2 < T) :
    openSpaceTimeSlab S =ᶠ[nhds z] openSpaceTimeSlab T := by
  have hS : {w : Space × ℝ | w.2 < S} ∈ nhds z :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hzS
  have hT : {w : Space × ℝ | w.2 < T} ∈ nhds z :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hzT
  filter_upwards [hS, hT] with w hwS hwT
  apply propext
  constructor
  · rintro ⟨_, hw⟩
    exact ⟨Set.mem_univ _, hw.1, hwT⟩
  · rintro ⟨_, hw⟩
    exact ⟨Set.mem_univ _, hw.1, hwS⟩

theorem selectedPeriodicVelocity_eventuallyEq
    {nu T : ℝ} {initial : InitialVelocity}
    (uniqueness : PeriodicOpenUniqueness) (hnu : 0 < nu)
    (selection : NormalizedPeriodicSelection nu initial)
    (hcover : SelectionCoversBefore selection T)
    (x : Space) {t : ℝ} (ht : t ∈ openTimeSlab T) :
    (fun s ↦ selectedPeriodicVelocity selection x s) =ᶠ[nhdsWithin t (openTimeSlab T)]
      (selection t).velocity x := by
  have hfuture : Iio (selection t).lifetime ∈ nhds t :=
    Iio_mem_nhds (hcover t ht)
  have hfuture' : Iio (selection t).lifetime ∈ nhdsWithin t (openTimeSlab T) :=
    Filter.Eventually.filter_mono inf_le_left hfuture
  filter_upwards [self_mem_nhdsWithin, hfuture'] with s hs hst
  exact normalizedPeriodicState_velocity_eq uniqueness hnu
    (selection s) (selection t) x hs.1 (hcover s hs) hst

theorem selectedPeriodicVelocity_uncurry_eventuallyEq
    {nu T : ℝ} {initial : InitialVelocity}
    (uniqueness : PeriodicOpenUniqueness) (hnu : 0 < nu)
    (selection : NormalizedPeriodicSelection nu initial)
    (hcover : SelectionCoversBefore selection T)
    {z : Space × ℝ} (hz : z ∈ openSpaceTimeSlab T) :
    Function.uncurry (selectedPeriodicVelocity selection) =ᶠ[
        nhdsWithin z (openSpaceTimeSlab T)]
      Function.uncurry (selection z.2).velocity := by
  have hfuture : {w : Space × ℝ | w.2 < (selection z.2).lifetime} ∈ nhds z :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds (hcover z.2 hz.2)
  have hfuture' : {w : Space × ℝ | w.2 < (selection z.2).lifetime} ∈
      nhdsWithin z (openSpaceTimeSlab T) :=
    Filter.Eventually.filter_mono inf_le_left hfuture
  filter_upwards [self_mem_nhdsWithin, hfuture'] with w hw hwt
  exact normalizedPeriodicState_velocity_eq uniqueness hnu
    (selection w.2) (selection z.2) w.1 hw.2.1 (hcover w.2 hw.2) hwt

theorem selectedPeriodicPressure_uncurry_eventuallyEq
    {nu T : ℝ} {initial : InitialVelocity}
    (uniqueness : PeriodicOpenUniqueness) (hnu : 0 < nu)
    (selection : NormalizedPeriodicSelection nu initial)
    (hcover : SelectionCoversBefore selection T)
    {z : Space × ℝ} (hz : z ∈ openSpaceTimeSlab T) :
    Function.uncurry (selectedPeriodicPressure selection) =ᶠ[
        nhdsWithin z (openSpaceTimeSlab T)]
      Function.uncurry (selection z.2).pressure := by
  have hfuture : {w : Space × ℝ | w.2 < (selection z.2).lifetime} ∈ nhds z :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds (hcover z.2 hz.2)
  have hfuture' : {w : Space × ℝ | w.2 < (selection z.2).lifetime} ∈
      nhdsWithin z (openSpaceTimeSlab T) :=
    Filter.Eventually.filter_mono inf_le_left hfuture
  filter_upwards [self_mem_nhdsWithin, hfuture'] with w hw hwt
  exact normalizedPeriodicState_pressure_eq uniqueness hnu
    (selection w.2) (selection z.2) w.1 hw.2.1 (hcover w.2 hw.2) hwt

/-- A covered normalized selection is one genuine official solution on the chosen horizon. -/
theorem openPeriodicSolutionOnOfSelection
    {nu T : ℝ} {initial : InitialVelocity}
    (uniqueness : PeriodicOpenUniqueness) (hnu : 0 < nu)
    (selection : NormalizedPeriodicSelection nu initial)
    (hT : 0 < T) (hcover : SelectionCoversBefore selection T) :
    OpenPeriodicSolutionOn T nu initial (0 : VelocityField)
      (selectedPeriodicVelocity selection) (selectedPeriodicPressure selection) where
  terminal_pos := hT
  momentum x t ht := by
    let fixed := selection t
    have htfixed : t ∈ openTimeSlab fixed.lifetime := ⟨ht.1, hcover t ht⟩
    have hderiv := (selectedPeriodicVelocity_eventuallyEq
      uniqueness hnu selection hcover x ht).derivWithin_eq (by rfl)
    rw [hderiv, ← derivWithin_congr_set
      (openTimeSlab_eventuallyEq_of_lt (hcover t ht) ht.2)]
    simpa [selectedPeriodicVelocity, selectedPeriodicPressure, fixed] using
      fixed.solution.momentum x t htfixed
  incompressible x t ht := by
    simpa [selectedPeriodicVelocity] using
      (selection t).solution.incompressible x t ⟨ht.1, hcover t ht⟩
  initial x := by
    simpa [selectedPeriodicVelocity] using (selection 0).solution.initial x
  velocitySmooth := by
    intro z hz
    let fixed := selection z.2
    have hzfixed : z ∈ openSpaceTimeSlab fixed.lifetime :=
      ⟨Set.mem_univ _, hz.2.1, hcover z.2 hz.2⟩
    have hsource := fixed.solution.velocitySmooth.contDiffWithinAt hzfixed
    have hrebase := hsource.congr_set
      (openSpaceTimeSlab_eventuallyEq_of_lt (hcover z.2 hz.2) hz.2.2)
    exact hrebase.congr_of_eventuallyEq
      (selectedPeriodicVelocity_uncurry_eventuallyEq
        uniqueness hnu selection hcover hz) (by rfl)
  pressureSmooth := by
    intro z hz
    let fixed := selection z.2
    have hzfixed : z ∈ openSpaceTimeSlab fixed.lifetime :=
      ⟨Set.mem_univ _, hz.2.1, hcover z.2 hz.2⟩
    have hsource := fixed.solution.pressureSmooth.contDiffWithinAt hzfixed
    have hrebase := hsource.congr_set
      (openSpaceTimeSlab_eventuallyEq_of_lt (hcover z.2 hz.2) hz.2.2)
    exact hrebase.congr_of_eventuallyEq
      (selectedPeriodicPressure_uncurry_eventuallyEq
        uniqueness hnu selection hcover hz) (by rfl)
  velocityPeriodic t ht := by
    simpa [selectedPeriodicVelocity] using
      (selection t).solution.velocityPeriodic t ⟨ht.1, hcover t ht⟩
  pressurePeriodic t ht := by
    simpa [selectedPeriodicPressure] using
      (selection t).solution.pressurePeriodic t ⟨ht.1, hcover t ht⟩

/-! ## Supremum descent and unbounded lifetime -/

theorem exists_normalizedPeriodicState_lifetime_gt_of_lt_csSup
    {nu : ℝ} {initial : InitialVelocity}
    (hne : (normalizedPeriodicLifetimes nu initial).Nonempty)
    {t : ℝ} (ht : t < sSup (normalizedPeriodicLifetimes nu initial)) :
    ∃ state : NormalizedPeriodicState nu initial, t < state.lifetime := by
  obtain ⟨lifetime, ⟨state, rfl⟩, htlifetime⟩ :=
    exists_lt_of_lt_csSup hne ht
  exact ⟨state, htlifetime⟩

/-- Below a candidate supremum, choose an occurrence extending past the current time. -/
def selectionBelowSup
    {nu : ℝ} {initial : InitialVelocity}
    (base : NormalizedPeriodicState nu initial)
    (hne : (normalizedPeriodicLifetimes nu initial).Nonempty) :
    NormalizedPeriodicSelection nu initial :=
  fun t ↦ if ht : t < sSup (normalizedPeriodicLifetimes nu initial) then
    Classical.choose
      (exists_normalizedPeriodicState_lifetime_gt_of_lt_csSup hne ht)
  else base

theorem selectionBelowSup_covers
    {nu : ℝ} {initial : InitialVelocity}
    (base : NormalizedPeriodicState nu initial)
    (hne : (normalizedPeriodicLifetimes nu initial).Nonempty)
    {t : ℝ} (ht : t < sSup (normalizedPeriodicLifetimes nu initial)) :
    t < (selectionBelowSup base hne t).lifetime := by
  rw [selectionBelowSup, dif_pos ht]
  exact Classical.choose_spec
    (exists_normalizedPeriodicState_lifetime_gt_of_lt_csSup hne ht)

/-- Compatible extension rules out a finite upper bound on normalized official lifetimes. -/
theorem normalizedPeriodicLifetimes_not_bddAbove
    {nu : ℝ} {initial : InitialVelocity}
    (uniqueness : PeriodicOpenUniqueness)
    (extensionLaw : PositivePeriodicCompatibleExtensionLaw)
    (hnu : 0 < nu) (base : NormalizedPeriodicState nu initial) :
    ¬ BddAbove (normalizedPeriodicLifetimes nu initial) := by
  intro hbdd
  let lifetimes := normalizedPeriodicLifetimes nu initial
  let limit := sSup lifetimes
  have hne : lifetimes.Nonempty := normalizedPeriodicLifetimes_nonempty base
  have hbase_le : base.lifetime ≤ limit := le_csSup hbdd ⟨base, rfl⟩
  have hlimit : 0 < limit := base.solution.terminal_pos.trans_le hbase_le
  let selection := selectionBelowSup base hne
  have hcover : SelectionCoversBefore selection limit := by
    intro t ht
    exact selectionBelowSup_covers base hne ht.2
  let unionSolution := openPeriodicSolutionOnOfSelection
    uniqueness hnu selection hlimit hcover
  obtain ⟨extension⟩ := extensionLaw hnu unionSolution
  let next : NormalizedPeriodicState nu initial :=
    normalizedPeriodicStateOfSolution extension.extendedSolution
  have hnext_mem : next.lifetime ∈ lifetimes := ⟨next, rfl⟩
  have hnext_le : next.lifetime ≤ limit := le_csSup hbdd hnext_mem
  exact (not_lt_of_ge hnext_le) extension.terminal_lt

theorem exists_normalizedPeriodicState_lifetime_gt_of_not_bddAbove
    {nu : ℝ} {initial : InitialVelocity}
    (hunbounded : ¬ BddAbove (normalizedPeriodicLifetimes nu initial))
    (t : ℝ) : ∃ state : NormalizedPeriodicState nu initial, t < state.lifetime := by
  obtain ⟨lifetime, ⟨state, rfl⟩, htlifetime⟩ :=
    (not_bddAbove_iff.mp hunbounded) t
  exact ⟨state, htlifetime⟩

/-- An unbounded lifetime population supplies a normalized occurrence past every real time. -/
def cofinalNormalizedSelection
    {nu : ℝ} {initial : InitialVelocity}
    (hunbounded : ¬ BddAbove (normalizedPeriodicLifetimes nu initial)) :
    NormalizedPeriodicSelection nu initial :=
  fun t ↦ Classical.choose
    (exists_normalizedPeriodicState_lifetime_gt_of_not_bddAbove hunbounded t)

theorem cofinalNormalizedSelection_covers
    {nu : ℝ} {initial : InitialVelocity}
    (hunbounded : ¬ BddAbove (normalizedPeriodicLifetimes nu initial))
    (t : ℝ) : t < (cofinalNormalizedSelection hunbounded t).lifetime :=
  Classical.choose_spec
    (exists_normalizedPeriodicState_lifetime_gt_of_not_bddAbove hunbounded t)

/-! ## The cofinal atlas -/

/-- Local existence, positive-viscosity overlap uniqueness, and universal compatible extension
construct one shared pressure-normalized periodic atlas on all finite open slabs. -/
theorem cofinalPeriodicAtlas_of_local_extension_unique
    (localExistence : HasPeriodicLocalExistence)
    (uniqueness : PeriodicOpenUniqueness)
    (extensionLaw : PositivePeriodicCompatibleExtensionLaw) :
    ∀ nu : ℝ, 0 < nu → ∀ initial : InitialVelocity,
      InitialVelocityConditionPeriodic initial →
        Nonempty (CofinalPeriodicAtlas nu initial) := by
  intro nu hnu initial hinitial
  let base := Classical.choice
    (nonempty_normalizedPeriodicState localExistence hnu hinitial)
  have hunbounded := normalizedPeriodicLifetimes_not_bddAbove
    uniqueness extensionLaw hnu base
  let selection := cofinalNormalizedSelection hunbounded
  refine ⟨{
    velocity := selectedPeriodicVelocity selection
    pressure := selectedPeriodicPressure selection
    pressureNormalized := selectedPeriodicPressure_normalized selection
    onOpenSlab := ?_ }⟩
  intro T hT
  apply openPeriodicSolutionOnOfSelection uniqueness hnu selection hT
  intro t ht
  exact cofinalNormalizedSelection_covers hunbounded t

section Audit

#print axioms normalizedPeriodicState_velocity_eq
#print axioms normalizedPeriodicState_pressure_eq
#print axioms openPeriodicSolutionOnOfSelection
#print axioms normalizedPeriodicLifetimes_not_bddAbove
#print axioms cofinalPeriodicAtlas_of_local_extension_unique

end Audit

end Soma.Holonics.Millennium.NavierStokesCofinalConstruction
