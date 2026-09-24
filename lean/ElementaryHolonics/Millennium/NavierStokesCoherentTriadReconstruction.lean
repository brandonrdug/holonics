import ElementaryHolonics.Millennium.NavierStokesCoherentTriadWitness
import ElementaryHolonics.Millennium.NavierStokesFinitePicardNativePathJoin
import ElementaryHolonics.Millennium.NavierStokesWeightedFourierDivergenceReconstruction
import ElementaryHolonics.Millennium.NavierStokesFiniteFourierSmoothReconstruction
import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
import ElementaryHolonics.Millennium.NavierStokesFiniteNativeQuadraticCoefficientBridge
import ElementaryHolonics.Millennium.NavierStokesPeriodicLocalExistence
import ElementaryHolonics.Millennium.NavierStokesInitialSpatialContinuity

/-!
# Real periodic reconstruction of the finite coherent triad

The coefficient witness is placed in the existing finite native `H³` carrier and then passed
through the existing weighted Fourier reconstruction.  Its support, native reality, and
modewise divergence receipts are proved explicitly.  The resulting actual field is `C∞`, real,
one-periodic, and pointwise incompressible, with exact recovery of the four-mode coefficient
population.  No global continuation claim is introduced here; the existing local-existence owner
is applied once to the reconstructed initial datum.
-/

noncomputable section

open Set Filter
open scoped BigOperators ComplexConjugate ENNReal Topology

namespace Soma.Holonics.Millennium.NavierStokesCoherentTriadReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFinitePicardNativePathJoin
open Soma.Holonics.Millennium.NavierStokesFiniteFourierSmoothReconstruction
open Soma.Holonics.Millennium.NavierStokesFiniteNativeQuadraticCoefficientBridge
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesFiniteScaleAncestry
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesCoherentTriadWitness
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
open Soma.Holonics.Millennium.NavierStokesWeightedFourierDivergenceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.NavierStokesPeriodicLocalExistence
open Soma.Holonics.Millennium.NavierStokesInitialSpatialContinuity

def nativeWitnessState : PeriodicVectorWeightedSobolev 3 :=
  finiteCubeNativeH3State 1 coefficientPopulation

def witnessVelocity : InitialVelocity := reconstructedVelocity nativeWitnessState

theorem finiteSupport_subset_frequencyCube_one :
    finiteSupport ⊆ frequencyCube 1 := by
  intro frequency hfrequency
  simp only [finiteSupport, Finset.mem_insert, Finset.mem_singleton] at hfrequency
  rcases hfrequency with rfl | rfl | rfl | rfl
  all_goals rw [mem_frequencyCube_iff]
  all_goals intro coordinate
  all_goals fin_cases coordinate <;> norm_num [p, q]

theorem coefficientPopulation_supportedInFrequencyCube_one :
    SupportedInFrequencyCube 1 coefficientPopulation := by
  intro frequency hfrequency
  apply coefficientPopulation_zero_of_not_mem
  intro hpopulation
  exact hfrequency (finiteSupport_subset_frequencyCube_one hpopulation)

theorem nativeWitnessState_isWeightedFourierReal :
    IsWeightedFourierReal 3 nativeWitnessState := by
  apply (isWeightedFourierReal_iff_native 3 nativeWitnessState).2
  unfold nativeWitnessState
  intro component frequency
  rw [finiteCubeNativeH3State_apply, finiteCubeNativeH3State_apply]
  by_cases hfrequency : frequency ∈ frequencyCube 1
  · have hnegative : -frequency ∈ frequencyCube 1 := by
      rw [mem_frequencyCube_iff] at hfrequency ⊢
      intro coordinate
      exact ⟨neg_le_neg (hfrequency coordinate).2,
        neg_le_neg (hfrequency coordinate).1⟩
    rw [if_pos hnegative, if_pos hfrequency]
    have hpopulation := congrArg (fun z : ComplexVector ↦ z component)
      (coefficientPopulation_conjugate_symmetric frequency)
    simp only [map_mul, Complex.conj_ofReal, hpopulation]
    rw [show periodicSobolevWeight 3 (-frequency) = periodicSobolevWeight 3 frequency by
      simp]
  · have hnegative : -frequency ∉ frequencyCube 1 := by
      intro hnegative
      apply hfrequency
      rw [mem_frequencyCube_iff] at hnegative ⊢
      intro coordinate
      exact ⟨by simpa using neg_le_neg (hnegative coordinate).2,
        by simpa using neg_le_neg (hnegative coordinate).1⟩
    rw [if_neg hnegative, if_neg hfrequency]
    simp

theorem nativeWitnessState_isModewiseDivergenceFree :
    IsModewiseDivergenceFree nativeWitnessState := by
  intro frequency
  change ∑ component : Fin 3,
      (frequency component : ℂ) *
        (finiteCubeNativeH3State 1 coefficientPopulation component frequency) = 0
  simp_rw [finiteCubeNativeH3State_apply]
  by_cases hfrequency : frequency ∈ frequencyCube 1
  · simp only [if_pos hfrequency]
    calc
      (∑ component : Fin 3,
          (frequency component : ℂ) *
            (↑√(periodicSobolevWeight 3 frequency) * coefficientPopulation frequency component)) =
          (↑√(periodicSobolevWeight 3 frequency) : ℂ) *
            ∑ component : Fin 3,
              (frequency component : ℂ) * coefficientPopulation frequency component := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro component _
        ring
      _ = 0 := by
        change (↑√(periodicSobolevWeight 3 frequency) : ℂ) *
          complexDot (complexFrequencyVector frequency)
            (coefficientPopulation frequency) = 0
        rw [coefficientPopulation_divergence_free frequency, mul_zero]
  · simp only [if_neg hfrequency]
    simp

theorem nativeWitnessState_isNativeFiniteSupport :
    NativeFiniteSupport nativeWitnessState := by
  refine ⟨finiteSupport, ?_⟩
  intro component frequency hfrequency
  have hcoeff : nativeUnweightedComponent nativeWitnessState component frequency =
      coefficientPopulation frequency component := by
    change weightedPhysicalCoefficient 3 component frequency nativeWitnessState = _
    exact weightedPhysicalCoefficient_finiteCubeNativeH3State 1
      coefficientPopulation_supportedInFrequencyCube_one component frequency
  rw [hcoeff]
  exact congrArg (fun z : ComplexVector ↦ z component)
    (coefficientPopulation_zero_of_not_mem hfrequency)

theorem witnessVelocity_smooth_periodic_divergenceFree :
    ContDiff ℝ (↑(⊤ : ℕ∞)) witnessVelocity ∧
      IsOnePeriodic witnessVelocity ∧
        ∀ x, divergence witnessVelocity x = 0 := by
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) witnessVelocity := by
    simpa [witnessVelocity] using
      contDiff_infty_reconstructedVelocity_of_nativeFiniteSupport nativeWitnessState
        nativeWitnessState_isNativeFiniteSupport
  have hperiodic : IsOnePeriodic witnessVelocity := by
    exact isOnePeriodic_reconstructedVelocity nativeWitnessState
  have hdivfree := divergence_reconstructedVelocity_eq_zero
    nativeWitnessState_isModewiseDivergenceFree
  exact ⟨hsmooth, hperiodic, hdivfree⟩

theorem witnessVelocity_c1_periodic_divergenceFree :
    ContDiff ℝ 1 witnessVelocity ∧
      IsOnePeriodic witnessVelocity ∧
        ∀ x, divergence witnessVelocity x = 0 := by
  exact reconstructedVelocity_c1_onePeriodic_divergenceFree
    nativeWitnessState_isModewiseDivergenceFree

theorem witnessVelocity_fourierCoefficient (frequency : SpatialFrequency) :
    vectorSpatialFourierCoeff witnessVelocity
        (continuous_reconstructedVelocity nativeWitnessState)
        (isOnePeriodic_reconstructedVelocity nativeWitnessState) frequency =
      fun component ↦ coefficientPopulation frequency component := by
  change vectorSpatialFourierCoeff (reconstructedVelocity nativeWitnessState)
      (continuous_reconstructedVelocity nativeWitnessState)
      (isOnePeriodic_reconstructedVelocity nativeWitnessState) frequency = _
  rw [vectorSpatialFourierCoeff_reconstructedVelocity
    nativeWitnessState_isWeightedFourierReal frequency]
  funext component
  change weightedPhysicalCoefficient 3 component frequency nativeWitnessState = _
  exact weightedPhysicalCoefficient_finiteCubeNativeH3State 1
    coefficientPopulation_supportedInFrequencyCube_one component frequency

theorem nativeWitnessState_unweightedPopulation_eq_coefficientPopulation :
    unweightedNativeModePopulation nativeWitnessState = coefficientPopulation := by
  funext frequency component
  change weightedPhysicalCoefficient 3 component frequency nativeWitnessState = _
  exact weightedPhysicalCoefficient_finiteCubeNativeH3State 1
    coefficientPopulation_supportedInFrequencyCube_one component frequency

theorem smoothWitnessState_eq_nativeWitnessState_unweighted :
    smoothSliceH3State witnessVelocity
        (witnessVelocity_smooth_periodic_divergenceFree.1)
        (witnessVelocity_smooth_periodic_divergenceFree.2.1) =
      unweightedVectorThree nativeWitnessState := by
  funext component
  apply Subtype.ext
  apply lp.ext
  funext frequency
  change smoothSliceFourierL2 witnessVelocity
      witnessVelocity_smooth_periodic_divergenceFree.1
      witnessVelocity_smooth_periodic_divergenceFree.2.1 component frequency = _
  rw [smoothSliceFourierL2_apply,
    witnessVelocity_fourierCoefficient frequency]
  exact congrFun (congrFun
    (nativeWitnessState_unweightedPopulation_eq_coefficientPopulation.symm) frequency) component

theorem actualAdvectionField_fourierCoefficient_eq_completeAdvectiveSourceAt :
    vectorSpatialFourierCoeff (actualAdvectionField witnessVelocity)
        (actualAdvectionField_contDiff witnessVelocity_smooth_periodic_divergenceFree.1).continuous
        (actualAdvectionField_isOnePeriodic witnessVelocity_smooth_periodic_divergenceFree.2.1) k =
      completeAdvectiveSourceAt := by
  rw [vectorSpatialFourierCoeff_actualAdvectionField_eq_h3AdvectiveConvolution
    witnessVelocity witnessVelocity_smooth_periodic_divergenceFree.1
      witnessVelocity_smooth_periodic_divergenceFree.2.1 k]
  rw [smoothWitnessState_eq_nativeWitnessState_unweighted]
  funext output
  change h3AdvectiveConvolution
      (unweightedVectorThree nativeWitnessState)
      (unweightedVectorThree nativeWitnessState) output k = _
  rw [h3AdvectiveConvolution_coefficient_eq_tsum_advectiveInteractions]
  have hsumDirect : Summable (fun parent : SpatialFrequency ↦
      complexAdvectiveInteraction parent (k - parent)
        (coefficientPopulation parent) (coefficientPopulation (k - parent))) := by
    apply summable_of_ne_finset_zero (s := finiteSupport)
    intro parent hparent
    exact completeSource_term_zero_outside_support parent hparent
  unfold completeAdvectiveSourceAt
  rw [tsum_apply hsumDirect]
  apply tsum_congr
  intro parent
  have hpopulation :
      unweightedNativeModePopulation nativeWitnessState parent = coefficientPopulation parent := by
    exact congrFun (nativeWitnessState_unweightedPopulation_eq_coefficientPopulation) parent
  have htransported :
      unweightedNativeModePopulation nativeWitnessState
          (transportedFrequencyAt k parent) =
        coefficientPopulation (k - parent) := by
    exact (congrFun (nativeWitnessState_unweightedPopulation_eq_coefficientPopulation)
      (transportedFrequencyAt k parent)).trans (by rfl)
  rw [hpopulation, htransported]
  rfl

theorem witness_initial_velocity_condition_periodic :
    InitialVelocityConditionPeriodic witnessVelocity := by
  refine { divergenceFree := ?_, smooth := ?_, periodic := ?_ }
  · exact witnessVelocity_smooth_periodic_divergenceFree.2.2
  · exact witnessVelocity_smooth_periodic_divergenceFree.1
  · exact witnessVelocity_smooth_periodic_divergenceFree.2.1

theorem witness_periodic_local_existence (nu : ℝ) (hnu : 0 < nu) :
    ∃ T velocity pressure, 0 < T ∧
      OpenPeriodicSolutionOn T nu witnessVelocity (0 : VelocityField) velocity pressure := by
  exact periodicLocalExistence nu hnu witnessVelocity witness_initial_velocity_condition_periodic

theorem witness_local_solution_has_positiveTime_nonzero_actual_advection_source
    (nu : ℝ) (hnu : 0 < nu) :
    ∃ T velocity pressure,
      ∃ solution : OpenPeriodicSolutionOn T nu witnessVelocity
          (0 : VelocityField) velocity pressure,
        0 < T ∧ ∃ t : Ioo 0 T, openActualAdvectionMode solution t k 2 ≠ 0 := by
  rcases witness_periodic_local_existence nu hnu with
    ⟨T, velocity, pressure, hT, solution⟩
  let hperiodic : ∀ s ∈ openTimeSlab T, IsOnePeriodic (fun x ↦ velocity x s) :=
    fun s hs ↦ solution.velocityPeriodic s hs
  let tzero : openTimeSlab T := ⟨0, ⟨le_rfl, hT⟩⟩
  let mode : openTimeSlab T → ℂ := fun t ↦
    initialActualAdvectionMode solution.toOpenSmoothSolutionOn hperiodic t k 2
  have hmodeContinuous : Continuous mode := by
    exact (continuous_apply 2).comp
      (continuous_initialActualAdvectionMode solution.toOpenSmoothSolutionOn hperiodic k)
  have hmodeZero : mode tzero ≠ 0 := by
    have hslice : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : Space ↦ velocity x 0) :=
      by
        rw [show (fun x : Space ↦ velocity x 0) = witnessVelocity by
          funext x
          exact solution.initial x]
        exact witnessVelocity_smooth_periodic_divergenceFree.1
    have haccessor := initialActualAdvectionMode_eq_vectorSpatialFourierCoeff
      solution.toOpenSmoothSolutionOn hperiodic tzero k hslice
    have hinitial : (fun x : Space ↦ velocity x 0) = witnessVelocity := by
      funext x
      exact solution.initial x
    have hmodeEq : mode tzero =
        vectorSpatialFourierCoeff (actualAdvectionField witnessVelocity)
          (actualAdvectionField_contDiff witnessVelocity_smooth_periodic_divergenceFree.1).continuous
          (actualAdvectionField_isOnePeriodic witnessVelocity_smooth_periodic_divergenceFree.2.1) k 2 := by
      rw [show mode tzero = initialActualAdvectionMode
          solution.toOpenSmoothSolutionOn hperiodic tzero k 2 by rfl,
        haccessor]
      congr 2
    have hactualNonzero :
        vectorSpatialFourierCoeff (actualAdvectionField witnessVelocity)
          (actualAdvectionField_contDiff witnessVelocity_smooth_periodic_divergenceFree.1).continuous
          (actualAdvectionField_isOnePeriodic witnessVelocity_smooth_periodic_divergenceFree.2.1) k 2 ≠ 0 := by
      have hactual := congrArg (fun z : ComplexVector ↦ z 2)
        actualAdvectionField_fourierCoefficient_eq_completeAdvectiveSourceAt
      rw [hactual]
      have hsum : completeAdvectiveSourceAt 2 = 2 * firstFeed 2 := by
        rw [completeAdvectiveSourceAt_eq_feedSum, feedSum, Pi.add_apply,
          feed_component_two_eq]
        ring
      rw [hsum]
      exact mul_ne_zero (by norm_num) feed_component_two_ne_zero
    rw [hmodeEq]
    exact hactualNonzero
  have hnonzero : {t : openTimeSlab T | mode t ≠ 0} ∈ 𝓝 tzero := by
    change mode ⁻¹' ({0}ᶜ) ∈ 𝓝 tzero
    exact hmodeContinuous.continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hmodeZero)
  have hnonzeroImage :
      ((fun t : openTimeSlab T ↦ (t : ℝ)) '' {t | mode t ≠ 0}) ∈
        𝓝[(openTimeSlab T)] (0 : ℝ) :=
    (mem_nhds_subtype_iff_nhdsWithin.mp hnonzero)
  rcases (mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnonzeroImage) with
    ⟨U, hU, hUS⟩
  rcases (mem_nhds_iff_exists_Ioo_subset.mp hU) with ⟨left, right, hzero, hinterval⟩
  let candidate : ℝ := min (right / 2) (T / 2)
  have hright : 0 < right := hzero.2
  have hcandidate : 0 < candidate := by
    dsimp [candidate]
    positivity
  have hcandidateRight : candidate < right := by
    dsimp [candidate]
    exact (min_lt_iff).2 (Or.inl (by linarith))
  have hcandidateT : candidate < T := by
    dsimp [candidate]
    exact (min_lt_iff).2 (Or.inr (by linarith))
  have hcandidateLeft : left < candidate := lt_of_lt_of_le hzero.1 hcandidate.le
  have hcandidateInterval : candidate ∈ Ioo left right :=
    ⟨hcandidateLeft, hcandidateRight⟩
  have hcandidateOpen : candidate ∈ openTimeSlab T :=
    ⟨hcandidate.le, hcandidateT⟩
  have hcandidateImage : candidate ∈
      ((fun t : openTimeSlab T ↦ (t : ℝ)) '' {t | mode t ≠ 0}) :=
    hUS ⟨hinterval hcandidateInterval, hcandidateOpen⟩
  rcases hcandidateImage with ⟨t, htmode, htval⟩
  have htpos : 0 < (t : ℝ) := by simpa [htval] using hcandidate
  refine ⟨T, velocity, pressure, solution, hT, ?_⟩
  let tInterior : Ioo 0 T := ⟨(t : ℝ), htpos, t.property.2⟩
  refine ⟨tInterior, ?_⟩
  rw [← initialActualAdvectionMode_eq_openActualAdvectionMode solution
    (by exact (show 0 ≤ (tInterior : ℝ) from tInterior.property.1.le)) k]
  exact htmode

theorem lerayProjectMode_output_preserved (mode : ComplexVector) :
    lerayProjectMode k mode 2 = mode 2 := by
  simp [lerayProjectMode, k, p, q, complexFrequencyVector]

/-- At this frequency the third output direction survives the pressure projection, so the
positive-time actual nonlinear source has a nonzero signed projected component. -/
theorem witness_local_solution_has_nonzero_projected_source
    (nu : ℝ) (hnu : 0 < nu) :
    ∃ T velocity pressure,
      ∃ solution : OpenPeriodicSolutionOn T nu witnessVelocity
          (0 : VelocityField) velocity pressure,
        0 < T ∧ ∃ t : Ioo 0 T,
          (-lerayProjectMode k (openActualAdvectionMode solution t k)) 2 ≠ 0 := by
  obtain ⟨T, velocity, pressure, solution, hT, t, ht⟩ :=
    witness_local_solution_has_positiveTime_nonzero_actual_advection_source nu hnu
  refine ⟨T, velocity, pressure, solution, hT, t, ?_⟩
  change -(lerayProjectMode k (openActualAdvectionMode solution t k) 2) ≠ 0
  rw [lerayProjectMode_output_preserved]
  exact neg_ne_zero.mpr ht

theorem actualAdvectionField_fourierCoefficient_component_two_eq_completeSource_component_two :
    vectorSpatialFourierCoeff (actualAdvectionField witnessVelocity)
        (actualAdvectionField_contDiff witnessVelocity_smooth_periodic_divergenceFree.1).continuous
        (actualAdvectionField_isOnePeriodic witnessVelocity_smooth_periodic_divergenceFree.2.1) k 2 =
      completeAdvectiveSourceAt 2 := by
  exact congrArg (fun z : ComplexVector ↦ z 2)
    actualAdvectionField_fourierCoefficient_eq_completeAdvectiveSourceAt

theorem actualAdvectionField_fourierCoefficient_component_two_norm_sq_eq_twice_diagonal :
    ‖vectorSpatialFourierCoeff (actualAdvectionField witnessVelocity)
        (actualAdvectionField_contDiff witnessVelocity_smooth_periodic_divergenceFree.1).continuous
        (actualAdvectionField_isOnePeriodic witnessVelocity_smooth_periodic_divergenceFree.2.1) k 2‖ ^ 2 =
      2 * completeDiagonalFeedSquareAt := by
  rw [actualAdvectionField_fourierCoefficient_component_two_eq_completeSource_component_two]
  exact completeAdvectiveSourceAt_component_two_norm_sq_eq_twice_diagonal

theorem actualAdvectionField_fourierCoefficient_component_two_ne_zero :
    vectorSpatialFourierCoeff (actualAdvectionField witnessVelocity)
        (actualAdvectionField_contDiff witnessVelocity_smooth_periodic_divergenceFree.1).continuous
        (actualAdvectionField_isOnePeriodic witnessVelocity_smooth_periodic_divergenceFree.2.1) k 2 ≠ 0 := by
  have hdiagonal : 0 < completeDiagonalFeedSquareAt := by
    rw [completeDiagonalFeedSquareAt_eq_first_second, firstFeed_component_two,
      secondFeed_component_two]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
      Complex.norm_I, mul_one]
    rw [abs_of_pos Real.pi_pos]
    positivity
  intro hzero
  have hsquare := actualAdvectionField_fourierCoefficient_component_two_norm_sq_eq_twice_diagonal
  rw [hzero, norm_zero] at hsquare
  norm_num at hsquare
  nlinarith

theorem actualAdvectionField_coefficient_inequality_iff (κ : ℝ) :
    ‖vectorSpatialFourierCoeff (actualAdvectionField witnessVelocity)
        (actualAdvectionField_contDiff witnessVelocity_smooth_periodic_divergenceFree.1).continuous
        (actualAdvectionField_isOnePeriodic witnessVelocity_smooth_periodic_divergenceFree.2.1) k 2‖ ^ 2 ≤
        (1 + κ) * completeDiagonalFeedSquareAt ↔ 1 ≤ κ := by
  simpa only [actualAdvectionField_fourierCoefficient_component_two_eq_completeSource_component_two]
    using complete_coefficient_inequality_iff κ

#print axioms finiteSupport_subset_frequencyCube_one
#print axioms coefficientPopulation_supportedInFrequencyCube_one
#print axioms nativeWitnessState_isWeightedFourierReal
#print axioms nativeWitnessState_isModewiseDivergenceFree
#print axioms witnessVelocity_c1_periodic_divergenceFree
#print axioms witnessVelocity_fourierCoefficient
#print axioms nativeWitnessState_isNativeFiniteSupport
#print axioms witnessVelocity_smooth_periodic_divergenceFree
#print axioms nativeWitnessState_unweightedPopulation_eq_coefficientPopulation
#print axioms smoothWitnessState_eq_nativeWitnessState_unweighted
#print axioms actualAdvectionField_fourierCoefficient_eq_completeAdvectiveSourceAt
#print axioms witness_initial_velocity_condition_periodic
#print axioms witness_periodic_local_existence
#print axioms witness_local_solution_has_positiveTime_nonzero_actual_advection_source
#print axioms witness_local_solution_has_nonzero_projected_source
#print axioms actualAdvectionField_fourierCoefficient_component_two_eq_completeSource_component_two
#print axioms actualAdvectionField_fourierCoefficient_component_two_norm_sq_eq_twice_diagonal
#print axioms actualAdvectionField_fourierCoefficient_component_two_ne_zero
#print axioms actualAdvectionField_coefficient_inequality_iff

end Soma.Holonics.Millennium.NavierStokesCoherentTriadReconstruction
