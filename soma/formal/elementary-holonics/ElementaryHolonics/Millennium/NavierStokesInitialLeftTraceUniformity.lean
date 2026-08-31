import ElementaryHolonics.Millennium.NavierStokesCriticalOfficialPassage
import ElementaryHolonics.Millennium.NavierStokesRestartMatchedEndpointTrace

/-!
# Uniform control of the initial-side terminal exhaustion

**[proved-derived; formal-checked]** The literal full vorticity coefficient mass has a fixed
weighted-`H3` service on every smooth periodic solution slice.  The derivative calibration is
retained as the addressed unit-torus curl occurrence rather than restated as a bare
transcendental literal.

For an arbitrary positive-viscosity open periodic solution, its actual initial datum then starts
the native local mild restart.  Open-slab uniqueness identifies that source-detached restart with
the original solution on a positive common interval.  The concrete left terminal exhaustion is
eventually inside that interval; its finite prefix is paid separately.  Consequently both the
full coefficient mass and the restart coefficient payment are uniformly bounded along every
left-exhaustion occurrence.

This is an initial-face theorem only.  It supplies no terminal-face estimate and asserts no
global Navier--Stokes continuation.
-/

noncomputable section

open ContDiff Function Set
open scoped BigOperators NNReal

namespace Soma.Holonics.Millennium.NavierStokesInitialLeftTraceUniformity

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesCoordinateNativeMildRestart
open Soma.Holonics.Millennium.NavierStokesCriticalOfficialPassage
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOverlapUniqueness
open Soma.Holonics.Millennium.NavierStokesRestartMatchedEndpointTrace
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedTower
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesTerminalCompactEndpointExhaustion
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartSupply
open Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteApertureHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothSliceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

set_option maxHeartbeats 2400000

/-! ## A fixed weighted-H3 service for the complete vorticity coefficient population -/

/-- The radius-zero Jacobian tail service, calibrated by the addressed unit-torus curl
occurrence.  The zero frequency carries no derivative, so this complement is the entire
derivative population. -/
def initialVorticityCurlCalibration : ℝ :=
  ‖frequencyCurlMultiplier (![1, 0, 0] : SpatialFrequency)
    (![0, 1, 0] : ComplexVector) 2‖

def initialVorticityCoefficientH3Service : ℝ :=
  6 * (initialVorticityCurlCalibration *
    Real.sqrt (jacobianTailScale 0 * jacobianTailLatticeMass))

theorem initialVorticityCoefficientH3Service_nonneg :
    0 ≤ initialVorticityCoefficientH3Service := by
  unfold initialVorticityCoefficientH3Service initialVorticityCurlCalibration
  exact mul_nonneg (by norm_num)
    (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))

private theorem eq_zero_of_mem_frequencyCube_zero
    {frequency : SpatialFrequency} (hfrequency : frequency ∈ frequencyCube 0) :
    frequency = 0 := by
  ext coordinate
  change frequency coordinate = 0
  have h := (mem_frequencyCube_iff 0 frequency).mp hfrequency coordinate
  simp only [Nat.cast_zero, neg_zero] at h
  omega

private theorem openPeriodicVorticityFourierMode_eq_zero_of_mem_frequencyCube_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube 0) :
    openPeriodicVorticityFourierMode solution t frequency = 0 := by
  rw [eq_zero_of_mem_frequencyCube_zero hfrequency,
    openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier,
    frequencyCurlMultiplier_zero]

private theorem vorticityMass_le_six_mul_radiusZeroJacobianTail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    openPeriodicFullVorticityCoefficientMass solution t ≤
      6 * openPeriodicJacobianCoefficientTailMass solution t (frequencyCube 0) := by
  let vorticityMass : SpatialFrequency → ℝ := fun frequency ↦
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency)
  let complement := {frequency : SpatialFrequency // frequency ∉ frequencyCube 0}
  have hvorticity : Summable vorticityMass :=
    summable_complexVectorL1_openPeriodicVorticityFourierMode solution t
  have hzero : (∑ frequency ∈ frequencyCube 0, vorticityMass frequency) = 0 := by
    apply Finset.sum_eq_zero
    intro frequency hfrequency
    simp only [vorticityMass,
      openPeriodicVorticityFourierMode_eq_zero_of_mem_frequencyCube_zero
        solution t hfrequency,
      complexVectorL1, Pi.zero_apply, norm_zero, zero_add]
  have hpartition := hvorticity.sum_add_tsum_subtype_compl (frequencyCube 0)
  have hfull : openPeriodicFullVorticityCoefficientMass solution t =
      ∑' frequency : complement, vorticityMass frequency.1 := by
    unfold openPeriodicFullVorticityCoefficientMass
    change (∑' frequency : SpatialFrequency, vorticityMass frequency) = _
    rw [← hpartition, hzero, zero_add]
  have hcurl : Summable fun frequency : complement ↦
      openPeriodicVorticityCurlEntryMass solution t frequency.1 :=
    (summable_openPeriodicVorticityCurlEntryMass solution t).subtype _
  have hmajorize :
      (∑' frequency : complement, vorticityMass frequency.1) ≤
        ∑' frequency : complement,
          openPeriodicVorticityCurlEntryMass solution t frequency.1 := by
    exact (hvorticity.subtype _).tsum_le_tsum
      (fun frequency ↦
        complexVectorL1_openPeriodicVorticityFourierMode_le
          solution t frequency.1)
      hcurl
  let entryMass : Fin 3 → Fin 3 → ℝ := fun component coordinate ↦
    ∑' frequency : complement,
      ‖openPeriodicJacobianFourierMode solution t frequency.1
        component coordinate‖
  have hentry (component coordinate : Fin 3) :
      entryMass component coordinate ≤
        openPeriodicJacobianCoefficientTailMass solution t (frequencyCube 0) := by
    have hnonneg : 0 ≤ entryMass component coordinate := by
      dsimp only [entryMass]
      exact tsum_nonneg fun _ ↦ norm_nonneg _
    calc
      entryMass component coordinate =
          ‖entryMass component coordinate‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ ≤ ‖fun innerCoordinate : Fin 3 ↦
          entryMass component innerCoordinate‖ :=
        norm_le_pi_norm _ coordinate
      _ ≤ ‖fun outerComponent : Fin 3 ↦ fun innerCoordinate : Fin 3 ↦
          entryMass outerComponent innerCoordinate‖ :=
        norm_le_pi_norm
          (fun outerComponent : Fin 3 ↦ fun innerCoordinate : Fin 3 ↦
            entryMass outerComponent innerCoordinate) component
      _ = openPeriodicJacobianCoefficientTailMass
          solution t (frequencyCube 0) := rfl
  have h21 : Summable fun frequency : complement ↦
      ‖openPeriodicJacobianFourierMode solution t frequency.1 2 1‖ :=
    (summable_norm_openPeriodicJacobianFourierMode_entry solution t 2 1).subtype _
  have h12 : Summable fun frequency : complement ↦
      ‖openPeriodicJacobianFourierMode solution t frequency.1 1 2‖ :=
    (summable_norm_openPeriodicJacobianFourierMode_entry solution t 1 2).subtype _
  have h02 : Summable fun frequency : complement ↦
      ‖openPeriodicJacobianFourierMode solution t frequency.1 0 2‖ :=
    (summable_norm_openPeriodicJacobianFourierMode_entry solution t 0 2).subtype _
  have h20 : Summable fun frequency : complement ↦
      ‖openPeriodicJacobianFourierMode solution t frequency.1 2 0‖ :=
    (summable_norm_openPeriodicJacobianFourierMode_entry solution t 2 0).subtype _
  have h10 : Summable fun frequency : complement ↦
      ‖openPeriodicJacobianFourierMode solution t frequency.1 1 0‖ :=
    (summable_norm_openPeriodicJacobianFourierMode_entry solution t 1 0).subtype _
  have h01 : Summable fun frequency : complement ↦
      ‖openPeriodicJacobianFourierMode solution t frequency.1 0 1‖ :=
    (summable_norm_openPeriodicJacobianFourierMode_entry solution t 0 1).subtype _
  have hcurlTsum :
      (∑' frequency : complement,
          openPeriodicVorticityCurlEntryMass solution t frequency.1) =
        entryMass 2 1 + entryMass 1 2 + entryMass 0 2 +
          entryMass 2 0 + entryMass 1 0 + entryMass 0 1 := by
    simp only [openPeriodicVorticityCurlEntryMass, complexCurlEntryMass,
      entryMass]
    rw [(((((h21.add h12).add h02).add h20).add h10)).tsum_add h01,
      ((((h21.add h12).add h02).add h20)).tsum_add h10,
      (((h21.add h12).add h02)).tsum_add h20,
      ((h21.add h12)).tsum_add h02,
      h21.tsum_add h12]
  rw [hfull]
  refine hmajorize.trans ?_
  rw [hcurlTsum]
  have htailNonneg :
      0 ≤ openPeriodicJacobianCoefficientTailMass solution t (frequencyCube 0) := by
    unfold openPeriodicJacobianCoefficientTailMass
    exact norm_nonneg _
  nlinarith [hentry 2 1, hentry 1 2, hentry 0 2,
    hentry 2 0, hentry 1 0, hentry 0 1]

/-- Every smooth interior slice has a literal full vorticity coefficient-mass bound paid by its
native weighted-`H3` norm. -/
theorem openPeriodicFullVorticityCoefficientMass_le_weightedH3Service
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    openPeriodicFullVorticityCoefficientMass solution t ≤
      initialVorticityCoefficientH3Service *
        ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
          (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
          (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖ := by
  have htail := openPeriodicJacobianCoefficientTailMass_frequencyCube_le
    solution t 0
  have htailNamed :
      openPeriodicJacobianCoefficientTailMass solution t (frequencyCube 0) ≤
        initialVorticityCurlCalibration *
          Real.sqrt (jacobianTailScale 0 * jacobianTailLatticeMass) *
            ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
              (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
              (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖ := by
    convert htail using 1
    simp [initialVorticityCurlCalibration, frequencyCurlMultiplier, complexCross,
      crossProduct, complexFrequencyVector]
    exact Or.inl (Or.inl (by positivity))
  exact (vorticityMass_le_six_mul_radiusZeroJacobianTail solution t).trans
    (by
      unfold initialVorticityCoefficientH3Service
      nlinarith [htailNamed])

/-! ## Exact recovery of a native path face from its smooth physical slice -/

private theorem smoothSliceVectorWeightedH3_eq_of_reconstructedVelocity
    (state : PeriodicVectorWeightedSobolev 3)
    (hreal : IsWeightedFourierReal 3 state)
    (hu : ContDiff ℝ ∞ (reconstructedVelocity state))
    (hperiodic : IsOnePeriodic (reconstructedVelocity state)) :
    smoothSliceVectorWeightedH3 (reconstructedVelocity state) hu hperiodic = state := by
  funext component
  let source := smoothSliceVectorWeightedH3
    (reconstructedVelocity state) hu hperiodic component
  have hcoeff : weightedSobolevCoefficients 3 source =
      weightedSobolevCoefficients 3 (state component) := by
    apply Subtype.ext
    apply Subtype.ext
    funext frequency
    change (weightedSobolevCoefficients 3
        (smoothSliceVectorWeightedH3
          (reconstructedVelocity state) hu hperiodic component)).1 frequency =
      (weightedSobolevCoefficients 3 (state component)).1 frequency
    rw [unweighted_smoothSliceVectorWeightedH3_apply]
    exact vectorSpatialFourierCoeff_reconstructedVelocity_eq_unweighted
      hreal frequency component
  calc
    smoothSliceVectorWeightedH3
        (reconstructedVelocity state) hu hperiodic component =
        coefficientWeightedRealization 3
          (weightedSobolevCoefficients 3 source) := by
      symm
      exact coefficientWeightedRealization_weightedSobolevCoefficients 3 source
    _ = coefficientWeightedRealization 3
          (weightedSobolevCoefficients 3 (state component)) := by rw [hcoeff]
    _ = state component :=
      coefficientWeightedRealization_weightedSobolevCoefficients 3 (state component)

private theorem smoothSliceVectorWeightedH3_congr
    {left right : InitialVelocity} (hfield : left = right)
    (hleft : ContDiff ℝ ∞ left) (hright : ContDiff ℝ ∞ right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right) :
    smoothSliceVectorWeightedH3 left hleft hleftPeriodic =
      smoothSliceVectorWeightedH3 right hright hrightPeriodic := by
  subst right
  rfl

/-! ## Source-detached local restart and the literal left exhaustion -/

/-- The complete vorticity coefficient population is uniformly bounded along the concrete
initial-side terminal exhaustion.  The witness consists of the native local-restart service and
the finitely many exhaustion occurrences preceding its common uniqueness aperture. -/
theorem exists_uniform_smoothTerminalExhaustionLeft_fullMass_bound
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) :
    ∃ massBound : ℝ, ∀ n : ℕ,
      openPeriodicFullVorticityCoefficientMass solution
        ⟨smoothTerminalExhaustionLeft T n,
          smoothTerminalExhaustionLeft_pos solution.terminal_pos n,
          (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
            (smoothTerminalExhaustionRight_lt solution.terminal_pos n)⟩ ≤ massBound := by
  let hinitial : InitialVelocityConditionPeriodic initial :=
    initialVelocityConditionPeriodic_of_openPeriodicSolution solution
  let base : PeriodicVectorWeightedSobolev 3 :=
    smoothSliceVectorWeightedH3 initial hinitial.smooth hinitial.periodic
  let cap : ℝ := ‖base‖
  have hcap : 0 ≤ cap := norm_nonneg base
  have hbaseReal : IsWeightedFourierReal 3 base := by
    dsimp only [base]
    exact isWeightedFourierReal_smoothSliceVectorWeightedH3
      initial hinitial.smooth hinitial.periodic
  have hbaseDivergenceFree : IsModewiseDivergenceFree base := by
    dsimp only [base]
    exact isModewiseDivergenceFree_smoothSliceVectorWeightedH3
      initial hinitial.smooth hinitial.periodic hinitial.divergenceFree
  let restart : NativeMildRestartAtCap nu cap hnu hcap base :=
    nativeMildRestartAtCap hnu hcap base le_rfl hbaseReal hbaseDivergenceFree
  let initialTower : CompatibleNativeWeightedSobolevTower :=
    smoothSliceCompatibleNativeWeightedSobolevTower
      initial hinitial.smooth hinitial.periodic
  have hbaseTower : initialTower.base = base := by
    rfl
  have hrestartFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu hcap).le initialTower.base) restart.path := by
    rw [hbaseTower]
    simpa only [weightedMildRestartMap] using restart.fixed
  let towerWitness := exists_coherentWeightedSmoothPathTower_of_nativeFixed
    hnu (weightedRestartTimeFromCap_pos hnu hcap).le
    initialTower restart.path hrestartFixed
  let tower := Classical.choose towerWitness
  let carrier := weightedClassicalRestartCarrierOfNative
    hnu hcap base restart tower
  let localT : ℝ := weightedRestartTimeFromCap nu cap
  have hlocalT : 0 < localT := weightedRestartTimeFromCap_pos hnu hcap
  have hlocalTNonneg : 0 ≤ localT := hlocalT.le
  let localVelocity : VelocityField :=
    weightedClassicalRestartVelocity hlocalTNonneg carrier.path
  let localPressure : PressureField :=
    weightedClassicalRestartPressure hlocalTNonneg carrier.path
  have hreconstruct : weightedClassicalRestartInitial base = initial := by
    unfold weightedClassicalRestartInitial
    dsimp only [base]
    exact reconstructedVelocity_smoothSliceVectorWeightedH3
      initial hinitial.smooth hinitial.periodic
  have localSolution :
      OpenPeriodicSolutionOn localT nu initial (0 : VelocityField)
        localVelocity localPressure := by
    let raw := carrier.toOpenPeriodicSolutionOn
      (jointSpacetimeSmoothnessUpgradeOfWeightedClassicalRestartCarrier carrier)
    simpa only [localT, localVelocity, localPressure, hreconstruct] using raw
  let commonT : ℝ := min T localT
  have hcommonT : 0 < commonT := by
    dsimp only [commonT]
    exact lt_min solution.terminal_pos hlocalT
  have hcommonOriginal : commonT ≤ T := min_le_left _ _
  have hcommonLocal : commonT ≤ localT := min_le_right _ _
  have hunique : ∀ x, ∀ t ∈ openTimeSlab commonT,
      velocity x t = localVelocity x t :=
    openPeriodicSolutionOn_velocity_eq_before solution localSolution hnu.le
      hcommonT hcommonOriginal hcommonLocal
  have heventually : ∀ᶠ n in Filter.atTop,
      smoothTerminalExhaustionLeft T n < commonT :=
    (tendsto_smoothTerminalExhaustionLeft T).eventually
      (Iio_mem_nhds hcommonT)
  rcases Filter.eventually_atTop.1 heventually with ⟨N, hN⟩
  let localBound : ℝ :=
    initialVorticityCoefficientH3Service * weightedRestartRadiusFromCap cap
  have hlocalBoundNonneg : 0 ≤ localBound := by
    dsimp only [localBound]
    exact mul_nonneg initialVorticityCoefficientH3Service_nonneg
      (by unfold weightedRestartRadiusFromCap; positivity)
  have htail : ∀ n : ℕ, N ≤ n →
      openPeriodicFullVorticityCoefficientMass solution
        ⟨smoothTerminalExhaustionLeft T n,
          smoothTerminalExhaustionLeft_pos solution.terminal_pos n,
          (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
            (smoothTerminalExhaustionRight_lt solution.terminal_pos n)⟩ ≤ localBound := by
    intro n hn
    let s : ℝ := smoothTerminalExhaustionLeft T n
    have hsPos : 0 < s := smoothTerminalExhaustionLeft_pos solution.terminal_pos n
    have hsT : s < T :=
      (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
        (smoothTerminalExhaustionRight_lt solution.terminal_pos n)
    have hsCommon : s < commonT := hN n hn
    have hsLocal : s < localT := hsCommon.trans_le hcommonLocal
    let stime : Icc (0 : ℝ) localT := ⟨s, hsPos.le, hsLocal.le⟩
    let state : PeriodicVectorWeightedSobolev 3 := carrier.path stime
    have hfield : (fun x ↦ velocity x s) = reconstructedVelocity state := by
      funext x
      calc
        velocity x s = localVelocity x s :=
          hunique x s ⟨hsPos.le, hsCommon⟩
        _ = reconstructedVelocity state x := by
          simp only [localVelocity, weightedClassicalRestartVelocity,
            weightedReconstructedVelocity, state, stime]
          rw [weightedPathExtension_of_mem hlocalTNonneg carrier.path stime.2]
    have hstateReal : IsWeightedFourierReal 3 state := carrier.fourierReal stime
    have hstateSmooth : ContDiff ℝ ∞ (reconstructedVelocity state) := by
      simpa only [state, carrier.tower.reconstructedVelocity_eq_base] using
        carrier.tower.contDiff_infty_reconstructedVelocity stime
    have hstatePeriodic : IsOnePeriodic (reconstructedVelocity state) :=
      isOnePeriodic_reconstructedVelocity state
    have hactualSmooth :=
      openPeriodicSolutionOn_velocitySlice_contDiff solution ⟨hsPos, hsT⟩
    have hactualPeriodic : IsOnePeriodic (fun x ↦ velocity x s) :=
      solution.velocityPeriodic s ⟨hsPos.le, hsT⟩
    have hactualState :
        smoothSliceVectorWeightedH3 (fun x ↦ velocity x s)
            hactualSmooth hactualPeriodic = state :=
      (smoothSliceVectorWeightedH3_congr hfield hactualSmooth hstateSmooth
        hactualPeriodic hstatePeriodic).trans
          (smoothSliceVectorWeightedH3_eq_of_reconstructedVelocity
            state hstateReal hstateSmooth hstatePeriodic)
    have hstateNorm : ‖state‖ ≤ weightedRestartRadiusFromCap cap :=
      (norm_weightedPath_apply_le carrier.path stime).trans restart.pathNorm
    have hmass := openPeriodicFullVorticityCoefficientMass_le_weightedH3Service
      solution ⟨s, hsPos, hsT⟩
    change openPeriodicFullVorticityCoefficientMass solution ⟨s, hsPos, hsT⟩ ≤
      localBound
    calc
      openPeriodicFullVorticityCoefficientMass solution ⟨s, hsPos, hsT⟩ ≤
          initialVorticityCoefficientH3Service *
            ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x s)
              hactualSmooth hactualPeriodic‖ := hmass
      _ = initialVorticityCoefficientH3Service * ‖state‖ := by rw [hactualState]
      _ ≤ initialVorticityCoefficientH3Service * weightedRestartRadiusFromCap cap :=
        mul_le_mul_of_nonneg_left hstateNorm
          initialVorticityCoefficientH3Service_nonneg
      _ = localBound := rfl
  let exhaustionMass : ℕ → ℝ := fun n ↦
      openPeriodicFullVorticityCoefficientMass solution
        ⟨smoothTerminalExhaustionLeft T n,
          smoothTerminalExhaustionLeft_pos solution.terminal_pos n,
          (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
            (smoothTerminalExhaustionRight_lt solution.terminal_pos n)⟩
  let prefixBound : ℝ :=
    ∑ n ∈ Finset.range N, exhaustionMass n
  have hprefixNonneg : 0 ≤ prefixBound := by
    dsimp only [prefixBound]
    exact Finset.sum_nonneg fun n _ ↦
      openPeriodicFullVorticityCoefficientMass_nonneg solution _
  refine ⟨prefixBound + localBound, ?_⟩
  intro n
  by_cases hn : n < N
  · have hprefixTerm :
        openPeriodicFullVorticityCoefficientMass solution
          ⟨smoothTerminalExhaustionLeft T n,
            smoothTerminalExhaustionLeft_pos solution.terminal_pos n,
            (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
              (smoothTerminalExhaustionRight_lt solution.terminal_pos n)⟩ ≤
          prefixBound := by
      change exhaustionMass n ≤ prefixBound
      dsimp only [prefixBound]
      exact Finset.single_le_sum
        (fun m _ ↦ by
          dsimp only [exhaustionMass]
          exact openPeriodicFullVorticityCoefficientMass_nonneg solution _)
        (Finset.mem_range.mpr hn)
    exact hprefixTerm.trans (le_add_of_nonneg_right hlocalBoundNonneg)
  · exact (htail n (le_of_not_gt hn)).trans
      (le_add_of_nonneg_left hprefixNonneg)

/-- The same unconditional source-detached bound pays the actual restart coefficient payment on
every initial-side exhaustion occurrence. -/
theorem exists_uniform_smoothTerminalExhaustionLeft_restartPayment_bound
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) :
    ∃ paymentBound : ℝ, ∀ n : ℕ,
      smoothRestartCoefficientPayment solution
        (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
        ((smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
          (smoothTerminalExhaustionRight_lt solution.terminal_pos n)) ≤ paymentBound := by
  rcases exists_uniform_smoothTerminalExhaustionLeft_fullMass_bound solution hnu with
    ⟨massBound, hmass⟩
  refine ⟨2 * massBound, fun n ↦ ?_⟩
  exact (smoothRestartCoefficientPayment_le_two_mul_fullMass solution
    (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
    ((smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
      (smoothTerminalExhaustionRight_lt solution.terminal_pos n))).trans
    (mul_le_mul_of_nonneg_left (hmass n) (by norm_num))

section Audit

#print axioms openPeriodicFullVorticityCoefficientMass_le_weightedH3Service
#print axioms exists_uniform_smoothTerminalExhaustionLeft_fullMass_bound
#print axioms exists_uniform_smoothTerminalExhaustionLeft_restartPayment_bound

end Audit

end Soma.Holonics.Millennium.NavierStokesInitialLeftTraceUniformity
