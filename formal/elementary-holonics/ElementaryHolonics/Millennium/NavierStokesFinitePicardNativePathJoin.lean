import ElementaryHolonics.Millennium.NavierStokesFiniteNativeQuadraticCoefficientBridge
import ElementaryHolonics.Millennium.NavierStokesWeightedMildInvariantRestart
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite Picard chronology as native continuous weighted paths

**[proved-derived; formal-checked]** A Fourier population supported in a finite frequency cube
has a canonical realization in the complete native weighted `H³` carrier: take the finite sum of
weighted singleton modes.  Applied at every clock face, the heat-seeded finite Picard chronology
is a genuine continuous `WeightedH3Path`, and unweighting it returns exactly the original finite
coefficient population.

This file then joins the support-containing finite quadratic coefficient to the actual native
weighted Duhamel coefficient.  The passage is finite-support and finite-generation.  It makes no
Galerkin-limit, Picard-convergence, or Navier--Stokes regularity claim.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators ENNReal Interval NNReal

namespace Soma.Holonics.Millennium.NavierStokesFinitePicardNativePathJoin

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFiniteNativeQuadraticCoefficientBridge
open Soma.Holonics.Millennium.NavierStokesFinitePicardChronology
open Soma.Holonics.Millennium.NavierStokesFiniteScaleAncestry
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
open Soma.Holonics.Millennium.NavierStokesWeightedMildInvariantRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The exact finite-support native realization -/

/-- Realize a declared finite Fourier cube directly in the complete native weighted carrier.
Outside-cube values are deliberately discarded; exact reconstruction therefore requires a
separate support hypothesis. -/
def finiteCubeNativeH3State
    (radius : ℕ) (field : ComplexFourierModePopulation) :
    PeriodicVectorWeightedSobolev 3 :=
  fun component ↦
    ∑ frequency ∈ frequencyCube radius,
      lp.single 2 frequency
        ((Real.sqrt (periodicSobolevWeight 3 frequency) : ℂ) *
          field frequency component)

@[simp]
theorem finiteCubeNativeH3State_apply
    (radius : ℕ) (field : ComplexFourierModePopulation)
    (component : Fin 3) (frequency : SpatialFrequency) :
    finiteCubeNativeH3State radius field component frequency =
      if frequency ∈ frequencyCube radius then
        (Real.sqrt (periodicSobolevWeight 3 frequency) : ℂ) *
          field frequency component
      else 0 := by
  classical
  unfold finiteCubeNativeH3State
  by_cases hfrequency : frequency ∈ frequencyCube radius
  · simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
    simp [hfrequency]
  · simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
    simp [hfrequency]

/-- Unweighting the finite native realization returns every coefficient of a supported field. -/
@[simp]
theorem weightedPhysicalCoefficient_finiteCubeNativeH3State
    (radius : ℕ) {field : ComplexFourierModePopulation}
    (hsupport : SupportedInFrequencyCube radius field)
    (component : Fin 3) (frequency : SpatialFrequency) :
    weightedPhysicalCoefficient 3 component frequency
        (finiteCubeNativeH3State radius field) =
      field frequency component := by
  rw [weightedPhysicalCoefficient_apply]
  change ((((Real.sqrt (periodicSobolevWeight 3 frequency))⁻¹ : ℝ) : ℂ) *
      finiteCubeNativeH3State radius field component frequency) = _
  rw [finiteCubeNativeH3State_apply]
  by_cases hfrequency : frequency ∈ frequencyCube radius
  · rw [if_pos hfrequency]
    have hsqrt : Real.sqrt (periodicSobolevWeight 3 frequency) ≠ 0 :=
      (Real.sqrt_pos.2 (periodicSobolevWeight_pos 3 frequency)).ne'
    rw [← mul_assoc]
    norm_cast
    field_simp
    simp
  · rw [if_neg hfrequency, mul_zero, hsupport frequency hfrequency]
    rfl

/-- Physical coefficients are faithful on the complete native weighted state carrier. -/
theorem weightedH3State_eq_of_physicalCoefficient_eq
    {left right : PeriodicVectorWeightedSobolev 3}
    (hcoeff : ∀ component frequency,
      weightedPhysicalCoefficient 3 component frequency left =
        weightedPhysicalCoefficient 3 component frequency right) :
    left = right := by
  funext component
  rw [← coefficientWeightedRealization_weightedSobolevCoefficients 3 (left component),
    ← coefficientWeightedRealization_weightedSobolevCoefficients 3 (right component)]
  congr 1
  apply Subtype.ext
  apply lp.ext
  funext frequency
  exact hcoeff component frequency

/-! ## Clock continuity of the finite chronology -/

theorem continuous_finiteProjectedAdvectiveCoefficient
    (aperture : Finset SpatialFrequency)
    (advecting transported : ℝ → ComplexFourierModePopulation)
    (output : SpatialFrequency)
    (hadvecting : ∀ frequency,
      Continuous fun time ↦ advecting time frequency)
    (htransported : ∀ frequency,
      Continuous fun time ↦ transported time frequency) :
    Continuous fun time ↦
      finiteProjectedAdvectiveCoefficient aperture
        (advecting time) (transported time) output := by
  unfold finiteProjectedAdvectiveCoefficient finiteAdvectiveCoefficient
  by_cases houtput : output = 0
  · subst output
    simp only [lerayProjectMode_zero]
    apply continuous_finsetSum
    intro parent _hparent
    unfold complexAdvectiveInteraction complexDot
    fun_prop
  · simp_rw [lerayProjectMode, if_neg houtput]
    unfold complexAdvectiveInteraction complexDot
    fun_prop

theorem continuous_diagonalHeatModeTransport_fixedTarget
    (nu targetTime : ℝ) (field : ℝ → ComplexFourierModePopulation)
    (frequency : SpatialFrequency)
    (hfield : Continuous fun sourceTime ↦ field sourceTime frequency) :
    Continuous fun sourceTime ↦
      diagonalHeatModeTransport nu (targetTime - sourceTime)
        (field sourceTime) frequency := by
  unfold diagonalHeatModeTransport heatStokesMultiplier
  fun_prop

/-- Every fixed Fourier mode of every finite heat-seeded generation varies continuously with the
target clock. -/
theorem continuous_finiteHeatSeededPicardGeneration_mode
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) :
    ∀ depth frequency,
      Continuous fun targetTime ↦
        finiteHeatSeededPicardGeneration nu restartTime aperture
          seed depth targetTime frequency := by
  intro depth
  induction depth with
  | zero =>
      intro frequency
      unfold finiteHeatSeededPicardGeneration diagonalHeatModeTransport
      unfold heatStokesMultiplier
      fun_prop
  | succ depth inductionHypothesis =>
      intro frequency
      unfold finiteHeatSeededPicardGeneration
      apply Continuous.sub
      · unfold diagonalHeatModeTransport heatStokesMultiplier
        fun_prop
      · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        · unfold Function.uncurry finiteHeatTransportedProjectedInteraction
            diagonalHeatModeTransport
          change Continuous fun times : ℝ × ℝ ↦
            (heatStokesMultiplier nu (times.1 - times.2) frequency : ℂ) •
              finiteProjectedAdvectiveCoefficient aperture
                (finiteHeatSeededPicardGeneration nu restartTime aperture
                  seed depth times.2)
                (finiteHeatSeededPicardGeneration nu restartTime aperture
                  seed depth times.2) frequency
          exact (Complex.continuous_ofReal.comp (by
            unfold heatStokesMultiplier
            fun_prop)).smul
            ((continuous_finiteProjectedAdvectiveCoefficient aperture
              (fun sourceTime ↦
                finiteHeatSeededPicardGeneration nu restartTime aperture
                  seed depth sourceTime)
              (fun sourceTime ↦
                finiteHeatSeededPicardGeneration nu restartTime aperture
                  seed depth sourceTime)
              frequency inductionHypothesis inductionHypothesis).comp continuous_snd)
        · exact continuous_id

/-- The vector-valued finite source at one output mode is interval integrable on every clock
interval. -/
theorem intervalIntegrable_finiteHeatTransportedProjectedInteraction_mode
    (nu restartTime targetTime : ℝ) (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) (depth : ℕ)
    (output : SpatialFrequency) :
    IntervalIntegrable
      (fun sourceTime ↦
        finiteHeatTransportedProjectedInteraction nu targetTime sourceTime aperture
          (finiteHeatSeededPicardGeneration nu restartTime aperture
            seed depth sourceTime)
          (finiteHeatSeededPicardGeneration nu restartTime aperture
            seed depth sourceTime) output)
      volume restartTime targetTime := by
  apply Continuous.intervalIntegrable
  exact continuous_diagonalHeatModeTransport_fixedTarget nu targetTime
    (fun sourceTime ↦
      finiteProjectedAdvectiveCoefficient aperture
        (finiteHeatSeededPicardGeneration nu restartTime aperture
          seed depth sourceTime)
        (finiteHeatSeededPicardGeneration nu restartTime aperture
          seed depth sourceTime)) output
    (continuous_finiteProjectedAdvectiveCoefficient aperture _ _ output
      (continuous_finiteHeatSeededPicardGeneration_mode
        nu restartTime aperture seed depth)
      (continuous_finiteHeatSeededPicardGeneration_mode
        nu restartTime aperture seed depth))

/-- Component evaluation commutes with the finite vector-valued interval integral in the
successor chronology. -/
theorem finiteHeatSeededPicardGeneration_succ_component
    (nu restartTime : ℝ) (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) (depth : ℕ)
    (targetTime : ℝ) (frequency : SpatialFrequency) (component : Fin 3) :
    finiteHeatSeededPicardGeneration nu restartTime aperture seed (depth + 1)
        targetTime frequency component =
      diagonalHeatModeTransport nu (targetTime - restartTime) seed
          frequency component -
        ∫ sourceTime in restartTime..targetTime,
          finiteHeatTransportedProjectedInteraction
            nu targetTime sourceTime aperture
              (finiteHeatSeededPicardGeneration
                nu restartTime aperture seed depth sourceTime)
              (finiteHeatSeededPicardGeneration
                nu restartTime aperture seed depth sourceTime) frequency component := by
  let interaction : ℝ → ComplexVector := fun sourceTime ↦
    finiteHeatTransportedProjectedInteraction
      nu targetTime sourceTime aperture
        (finiteHeatSeededPicardGeneration
          nu restartTime aperture seed depth sourceTime)
        (finiteHeatSeededPicardGeneration
          nu restartTime aperture seed depth sourceTime) frequency
  let projection : ComplexVector →L[ℂ] ℂ :=
    ContinuousLinearMap.proj component
  have hintegrable : IntervalIntegrable interaction volume restartTime targetTime :=
    intervalIntegrable_finiteHeatTransportedProjectedInteraction_mode
      nu restartTime targetTime aperture seed depth frequency
  have hcommute := projection.intervalIntegral_comp_comm hintegrable
  change
    (diagonalHeatModeTransport nu (targetTime - restartTime) seed frequency -
      ∫ sourceTime in restartTime..targetTime, interaction sourceTime) component = _
  rw [Pi.sub_apply]
  change diagonalHeatModeTransport nu (targetTime - restartTime) seed frequency
      component - projection (∫ sourceTime in restartTime..targetTime,
        interaction sourceTime) = _
  rw [← hcommute]
  simp only [projection, ContinuousLinearMap.proj_apply, interaction]

/-- A uniformly cube-supported continuous physical coefficient population is a continuous curve
in the complete native weighted carrier. -/
theorem continuous_finiteCubeNativeH3State
    (radius : ℕ) (field : ℝ → ComplexFourierModePopulation)
    (hfield : ∀ frequency, Continuous fun time ↦ field time frequency) :
    Continuous fun time ↦ finiteCubeNativeH3State radius (field time) := by
  classical
  apply continuous_pi
  intro component
  unfold finiteCubeNativeH3State
  apply continuous_finsetSum
  intro frequency _hfrequency
  exact (lp.singleContinuousLinearMap ℂ (fun _ : SpatialFrequency ↦ ℂ)
    2 frequency).continuous.comp
      (continuous_const.mul ((continuous_apply component).comp (hfield frequency)))

/-- Every supported finite heat-seeded generation is an actual continuous native weighted path. -/
def finiteHeatSeededPicardNativePath
    (nu : ℝ) {T : ℝ} (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) (baseLevel depth : ℕ)
    (_hseed : SupportedInFrequencyCube (dyadicRadius baseLevel) seed) :
    WeightedH3Path T where
  toFun := fun targetTime ↦
    finiteCubeNativeH3State (dyadicRadius (baseLevel + depth))
      (finiteHeatSeededPicardGeneration nu 0 aperture seed depth targetTime.1)
  continuous_toFun :=
    (continuous_finiteCubeNativeH3State (dyadicRadius (baseLevel + depth))
      (finiteHeatSeededPicardGeneration nu 0 aperture seed depth)
      (continuous_finiteHeatSeededPicardGeneration_mode nu 0 aperture seed depth)).comp
        continuous_subtype_val

@[simp]
theorem weightedPhysicalCoefficient_finiteHeatSeededPicardNativePath
    (nu : ℝ) {T : ℝ} (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) (baseLevel depth : ℕ)
    (hseed : SupportedInFrequencyCube (dyadicRadius baseLevel) seed)
    (targetTime : Icc (0 : ℝ) T) (component : Fin 3)
    (frequency : SpatialFrequency) :
    weightedPhysicalCoefficient 3 component frequency
        (finiteHeatSeededPicardNativePath nu aperture seed baseLevel depth hseed targetTime) =
      finiteHeatSeededPicardGeneration nu 0 aperture seed depth targetTime.1
        frequency component := by
  apply weightedPhysicalCoefficient_finiteCubeNativeH3State
  exact finiteHeatSeededPicardGeneration_supported nu 0 aperture hseed depth targetTime.1

/-- The native path's complete unweighted vector population is exactly the finite Picard
generation, not merely an equal norm or a finite receiver shadow. -/
theorem unweightedNativeModePopulation_finiteHeatSeededPicardNativePath
    (nu : ℝ) {T : ℝ} (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) (baseLevel depth : ℕ)
    (hseed : SupportedInFrequencyCube (dyadicRadius baseLevel) seed)
    (targetTime : Icc (0 : ℝ) T) :
    unweightedNativeModePopulation
        (finiteHeatSeededPicardNativePath nu aperture seed baseLevel depth hseed
          targetTime) =
      finiteHeatSeededPicardGeneration nu 0 aperture seed depth targetTime.1 := by
  funext frequency component
  change weightedPhysicalCoefficient 3 component frequency
      (finiteHeatSeededPicardNativePath nu aperture seed baseLevel depth hseed
        targetTime) = _
  exact weightedPhysicalCoefficient_finiteHeatSeededPicardNativePath
    nu aperture seed baseLevel depth hseed targetTime component frequency

/-! ## The exact finite/native Duhamel join -/

/-- For a divergence-free bundled generation and an aperture containing its complete finite
support, the physical coefficient of the actual native Bochner Duhamel return is exactly the
chronology's scalar finite coefficient integral.  The time history is retained inside the
integral; it is not replaced by a supremum. -/
theorem weightedPhysicalCoefficient_weightedDuhamelReturn_finitePicardNativePath
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (aperture : Finset SpatialFrequency)
    (seed : ComplexFourierModePopulation) (baseLevel depth : ℕ)
    (hseed : SupportedInFrequencyCube (dyadicRadius baseLevel) seed)
    (hcontains : frequencyCube (dyadicRadius (baseLevel + depth)) ⊆ aperture)
    (hdivergence : IsWeightedDivergenceFreePath
      (finiteHeatSeededPicardNativePath nu aperture seed baseLevel depth hseed :
        WeightedH3Path (weightedRestartTimeFromCap nu cap)))
    (targetTime : Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap))
    (component : Fin 3) (frequency : SpatialFrequency) :
    weightedPhysicalCoefficient 3 component frequency
        (weightedDuhamelReturn (Real.toNNReal nu) (real_toNNReal_pos hnu)
          (weightedRestartTimeFromCap_pos hnu hcap).le
          (finiteHeatSeededPicardNativePath nu aperture seed baseLevel depth hseed)
          targetTime.1) =
      ∫ sourceTime in (0 : ℝ)..targetTime.1,
        finiteHeatTransportedProjectedInteraction
          nu targetTime.1 sourceTime aperture
            (finiteHeatSeededPicardGeneration
              nu 0 aperture seed depth sourceTime)
            (finiteHeatSeededPicardGeneration
              nu 0 aperture seed depth sourceTime) frequency component := by
  let T : ℝ := weightedRestartTimeFromCap nu cap
  let path : WeightedH3Path T :=
    finiteHeatSeededPicardNativePath nu aperture seed baseLevel depth hseed
  rw [weightedPhysicalCoefficient_weightedDuhamelReturn
    (Real.toNNReal nu) (real_toNNReal_pos hnu)
      (weightedRestartTimeFromCap_pos hnu hcap).le path component frequency
      targetTime.2]
  apply intervalIntegral.integral_congr
  intro sourceTime hsourceTime
  rw [uIcc_of_le targetTime.2.1] at hsourceTime
  have hsourceT : sourceTime ∈ Icc (0 : ℝ) T :=
    ⟨hsourceTime.1, hsourceTime.2.trans targetTime.2.2⟩
  have hpathPopulation :
      unweightedNativeModePopulation
          (path ⟨sourceTime, hsourceT⟩) =
        finiteHeatSeededPicardGeneration
          nu 0 aperture seed depth sourceTime := by
    exact unweightedNativeModePopulation_finiteHeatSeededPicardNativePath
      nu aperture seed baseLevel depth hseed ⟨sourceTime, hsourceT⟩
  have hpathSupport :
      SupportedInFrequencyCube (dyadicRadius (baseLevel + depth))
        (unweightedNativeModePopulation (path ⟨sourceTime, hsourceT⟩)) := by
    rw [hpathPopulation]
    exact finiteHeatSeededPicardGeneration_supported
      nu 0 aperture hseed depth sourceTime
  have hbridge :=
    finiteProjectedAdvectiveCoefficient_component_eq_weightedPhysicalCoefficient
      aperture (dyadicRadius (baseLevel + depth))
      (path ⟨sourceTime, hsourceT⟩)
      (hdivergence ⟨sourceTime, hsourceT⟩) hpathSupport hcontains
      frequency component
  have hbridge' :
      finiteProjectedAdvectiveCoefficient aperture
          (unweightedNativeModePopulation (path ⟨sourceTime, hsourceT⟩))
          (unweightedNativeModePopulation (path ⟨sourceTime, hsourceT⟩))
          frequency component =
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (path ⟨sourceTime, hsourceT⟩))
          (unweightedVectorThree (path ⟨sourceTime, hsourceT⟩)) component).1
            frequency := by
    simpa only [weightedPhysicalCoefficient_apply, weightedLerayQuadratic_apply,
      unweighted_weightedLerayDivergenceConvolution_apply] using hbridge
  have hfiniteCoefficient :
      finiteProjectedAdvectiveCoefficient aperture
          (finiteHeatSeededPicardGeneration
            nu 0 aperture seed depth sourceTime)
          (finiteHeatSeededPicardGeneration
            nu 0 aperture seed depth sourceTime) frequency component =
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (path ⟨sourceTime, hsourceT⟩))
          (unweightedVectorThree (path ⟨sourceTime, hsourceT⟩)) component).1
            frequency := by
    rw [← hpathPopulation]
    exact hbridge'
  change
    (heatStokesMultiplier ((Real.toNNReal nu : ℝ))
        (targetTime.1 - sourceTime) frequency : ℂ) *
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree
            (weightedPathExtension
              (weightedRestartTimeFromCap_pos hnu hcap).le path sourceTime))
          (unweightedVectorThree
            (weightedPathExtension
              (weightedRestartTimeFromCap_pos hnu hcap).le path sourceTime))
          component).1 frequency = _
  rw [weightedPathExtension_of_mem
    (weightedRestartTimeFromCap_pos hnu hcap).le path hsourceT]
  unfold finiteHeatTransportedProjectedInteraction diagonalHeatModeTransport
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Real.coe_toNNReal _ hnu.le, hfiniteCoefficient]

/-! ## Finite generations are the native mild iterates -/

/-- Generation zero is exactly the native linear heat path when the finite seed is the complete
physical coefficient population of the native initial state. -/
theorem finiteHeatSeededPicardNativePath_zero_eq_weightedLinearHeatPath
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (aperture : Finset SpatialFrequency)
    (initial : PeriodicVectorWeightedSobolev 3) (baseLevel : ℕ)
    (hsupport : SupportedInFrequencyCube (dyadicRadius baseLevel)
      (unweightedNativeModePopulation initial)) :
    (finiteHeatSeededPicardNativePath nu aperture
        (unweightedNativeModePopulation initial) baseLevel 0 hsupport :
      WeightedH3Path (weightedRestartTimeFromCap nu cap)) =
      weightedLinearHeatPath (Real.toNNReal nu)
        (weightedRestartTimeFromCap_pos hnu hcap).le initial := by
  apply ContinuousMap.ext
  intro targetTime
  apply weightedH3State_eq_of_physicalCoefficient_eq
  intro component frequency
  rw [weightedPhysicalCoefficient_finiteHeatSeededPicardNativePath,
    weightedPhysicalCoefficient_weightedLinearHeatPath]
  unfold finiteHeatSeededPicardGeneration
  rw [sub_zero]
  unfold diagonalHeatModeTransport unweightedNativeModePopulation
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Real.coe_toNNReal _ hnu.le]
  simp only [unweightedVectorThree]

/-- One support-containing finite successor is exactly one application of the actual native mild
restart map to the bundled previous generation. -/
theorem finiteHeatSeededPicardNativePath_succ_eq_weightedMildRestartMap
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (aperture : Finset SpatialFrequency)
    (initial : PeriodicVectorWeightedSobolev 3) (baseLevel depth : ℕ)
    (hsupport : SupportedInFrequencyCube (dyadicRadius baseLevel)
      (unweightedNativeModePopulation initial))
    (hcontains : frequencyCube (dyadicRadius (baseLevel + depth)) ⊆ aperture)
    (hdivergence : IsWeightedDivergenceFreePath
      (finiteHeatSeededPicardNativePath nu aperture
        (unweightedNativeModePopulation initial) baseLevel depth hsupport :
          WeightedH3Path (weightedRestartTimeFromCap nu cap))) :
    (finiteHeatSeededPicardNativePath nu aperture
        (unweightedNativeModePopulation initial) baseLevel (depth + 1) hsupport :
      WeightedH3Path (weightedRestartTimeFromCap nu cap)) =
      weightedMildRestartMap nu cap hnu hcap initial
        (finiteHeatSeededPicardNativePath nu aperture
          (unweightedNativeModePopulation initial) baseLevel depth hsupport) := by
  let previous : WeightedH3Path (weightedRestartTimeFromCap nu cap) :=
    finiteHeatSeededPicardNativePath nu aperture
      (unweightedNativeModePopulation initial) baseLevel depth hsupport
  apply ContinuousMap.ext
  intro targetTime
  apply weightedH3State_eq_of_physicalCoefficient_eq
  intro component frequency
  rw [weightedPhysicalCoefficient_finiteHeatSeededPicardNativePath,
    finiteHeatSeededPicardGeneration_succ_component]
  change _ = weightedPhysicalCoefficient 3 component frequency
    (weightedLinearHeatPath (Real.toNNReal nu)
        (weightedRestartTimeFromCap_pos hnu hcap).le initial targetTime -
      weightedDuhamelPath (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu hcap).le previous targetTime)
  rw [map_sub, weightedPhysicalCoefficient_weightedLinearHeatPath,
    weightedDuhamelPath_apply,
    weightedPhysicalCoefficient_weightedDuhamelReturn_finitePicardNativePath
      hnu hcap aperture (unweightedNativeModePopulation initial) baseLevel depth
        hsupport hcontains hdivergence targetTime component frequency]
  unfold diagonalHeatModeTransport unweightedNativeModePopulation
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Real.coe_toNNReal _ hnu.le]
  simp only [sub_zero, unweightedVectorThree]

/-- The native quadratic return of the zero path vanishes, so the first native mild iterate is
exactly the linear heat path. -/
theorem weightedMildRestartMap_zero_eq_weightedLinearHeatPath
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) :
    weightedMildRestartMap nu cap hnu hcap initial
        (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap)) =
      weightedLinearHeatPath (Real.toNNReal nu)
        (weightedRestartTimeFromCap_pos hnu hcap).le initial := by
  let hT : 0 ≤ weightedRestartTimeFromCap nu cap :=
    (weightedRestartTimeFromCap_pos hnu hcap).le
  have hbound := norm_weightedDuhamelPath_le
    (Real.toNNReal nu) (real_toNNReal_pos hnu) hT
      (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap))
  have hduhamel :
      weightedDuhamelPath (Real.toNNReal nu) (real_toNNReal_pos hnu) hT
        (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap)) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm
    · simpa using hbound
    · exact norm_nonneg _
  unfold weightedMildRestartMap weightedMildMap
  rw [hduhamel, sub_zero]

/-- Every finite native mild iterate is modewise divergence-free once the initial state is. -/
theorem isWeightedDivergenceFreePath_iterate_weightedMildRestartMap
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    {initial : PeriodicVectorWeightedSobolev 3}
    (hinitial : IsModewiseDivergenceFree initial) :
    ∀ iterateDepth : ℕ,
      IsWeightedDivergenceFreePath
        (((weightedMildRestartMap nu cap hnu hcap initial)^[iterateDepth])
          (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap))) := by
  intro iterateDepth
  induction iterateDepth with
  | zero =>
      simp only [Function.iterate_zero_apply]
      intro targetTime frequency
      change (∑ component : Fin 3,
        (frequency component : ℂ) *
          (0 : PeriodicVectorWeightedSobolev 3) component frequency) = 0
      simp
  | succ iterateDepth _inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      exact isWeightedDivergenceFreePath_weightedMildRestartMap
        hnu hcap hinitial _

/-- Exact finite-generation/native-iterate identification when the aperture contains every
predecessor support cube used before the requested generation. -/
theorem finiteHeatSeededPicardNativePath_eq_weightedMildRestartMap_iterate_of_predecessors
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (aperture : Finset SpatialFrequency)
    (initial : PeriodicVectorWeightedSobolev 3)
    (hinitialDivergence : IsModewiseDivergenceFree initial)
    (baseLevel : ℕ)
    (hsupport : SupportedInFrequencyCube (dyadicRadius baseLevel)
      (unweightedNativeModePopulation initial)) :
    ∀ depth : ℕ,
      (∀ predecessor, predecessor < depth →
        frequencyCube (dyadicRadius (baseLevel + predecessor)) ⊆ aperture) →
      (finiteHeatSeededPicardNativePath nu aperture
          (unweightedNativeModePopulation initial) baseLevel depth hsupport :
        WeightedH3Path (weightedRestartTimeFromCap nu cap)) =
        (((weightedMildRestartMap nu cap hnu hcap initial)^[depth + 1])
          (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap))) := by
  intro depth hcontains
  induction depth with
  | zero =>
      calc
        (finiteHeatSeededPicardNativePath nu aperture
            (unweightedNativeModePopulation initial) baseLevel 0 hsupport :
          WeightedH3Path (weightedRestartTimeFromCap nu cap)) =
            weightedLinearHeatPath (Real.toNNReal nu)
              (weightedRestartTimeFromCap_pos hnu hcap).le initial :=
          finiteHeatSeededPicardNativePath_zero_eq_weightedLinearHeatPath
            hnu hcap aperture initial baseLevel hsupport
        _ = weightedMildRestartMap nu cap hnu hcap initial 0 :=
          (weightedMildRestartMap_zero_eq_weightedLinearHeatPath
            hnu hcap initial).symm
        _ = (((weightedMildRestartMap nu cap hnu hcap initial)^[0 + 1])
            (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap))) := by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  | succ depth inductionHypothesis =>
      have hcontainsPrevious : ∀ predecessor, predecessor < depth →
          frequencyCube (dyadicRadius (baseLevel + predecessor)) ⊆ aperture := by
        intro predecessor hpredecessor
        exact hcontains predecessor (hpredecessor.trans (Nat.lt_succ_self depth))
      have hprevious := inductionHypothesis hcontainsPrevious
      have hpreviousDivergence : IsWeightedDivergenceFreePath
          (finiteHeatSeededPicardNativePath nu aperture
            (unweightedNativeModePopulation initial) baseLevel depth hsupport :
              WeightedH3Path (weightedRestartTimeFromCap nu cap)) := by
        rw [hprevious]
        exact isWeightedDivergenceFreePath_iterate_weightedMildRestartMap
          hnu hcap hinitialDivergence (depth + 1)
      calc
        (finiteHeatSeededPicardNativePath nu aperture
            (unweightedNativeModePopulation initial) baseLevel (depth + 1) hsupport :
          WeightedH3Path (weightedRestartTimeFromCap nu cap)) =
            weightedMildRestartMap nu cap hnu hcap initial
              (finiteHeatSeededPicardNativePath nu aperture
                (unweightedNativeModePopulation initial) baseLevel depth hsupport) :=
          finiteHeatSeededPicardNativePath_succ_eq_weightedMildRestartMap
            hnu hcap aperture initial baseLevel depth hsupport
              (hcontains depth (Nat.lt_succ_self depth)) hpreviousDivergence
        _ = weightedMildRestartMap nu cap hnu hcap initial
              (((weightedMildRestartMap nu cap hnu hcap initial)^[depth + 1])
                (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap))) := by
          rw [hprevious]
        _ = (((weightedMildRestartMap nu cap hnu hcap initial)^[(depth + 1) + 1])
              (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap))) := by
          simpa only [Nat.succ_eq_add_one] using
            (Function.iterate_succ_apply'
              (weightedMildRestartMap nu cap hnu hcap initial) (depth + 1)
              (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap))).symm

/-- **NS-facing finite chronology join.** A single aperture containing the largest generation
cube identifies generation `depth` with `(weightedMildRestartMap)^[depth+1] 0`; containment of all
earlier predecessor cubes follows from dyadic-radius monotonicity. -/
theorem finiteHeatSeededPicardNativePath_eq_weightedMildRestartMap_iterate
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (aperture : Finset SpatialFrequency)
    (initial : PeriodicVectorWeightedSobolev 3)
    (hinitialDivergence : IsModewiseDivergenceFree initial)
    (baseLevel depth : ℕ)
    (hsupport : SupportedInFrequencyCube (dyadicRadius baseLevel)
      (unweightedNativeModePopulation initial))
    (hcontains : frequencyCube (dyadicRadius (baseLevel + depth)) ⊆ aperture) :
    (finiteHeatSeededPicardNativePath nu aperture
        (unweightedNativeModePopulation initial) baseLevel depth hsupport :
      WeightedH3Path (weightedRestartTimeFromCap nu cap)) =
      (((weightedMildRestartMap nu cap hnu hcap initial)^[depth + 1])
        (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap))) := by
  apply finiteHeatSeededPicardNativePath_eq_weightedMildRestartMap_iterate_of_predecessors
    hnu hcap aperture initial hinitialDivergence baseLevel hsupport depth
  intro predecessor hpredecessor
  apply fun frequency hfrequency ↦ hcontains
    (frequencyCube_mono (show dyadicRadius (baseLevel + predecessor) ≤
      dyadicRadius (baseLevel + depth) by
        unfold dyadicRadius
        exact Nat.pow_le_pow_right (by norm_num)
          (Nat.add_le_add_left hpredecessor.le baseLevel)) hfrequency)

section Audit

#print axioms weightedPhysicalCoefficient_finiteCubeNativeH3State
#print axioms continuous_finiteHeatSeededPicardGeneration_mode
#print axioms finiteHeatSeededPicardGeneration_succ_component
#print axioms weightedPhysicalCoefficient_finiteHeatSeededPicardNativePath
#print axioms weightedPhysicalCoefficient_weightedDuhamelReturn_finitePicardNativePath
#print axioms finiteHeatSeededPicardNativePath_succ_eq_weightedMildRestartMap
#print axioms isWeightedDivergenceFreePath_iterate_weightedMildRestartMap
#print axioms finiteHeatSeededPicardNativePath_eq_weightedMildRestartMap_iterate

end Audit

end Soma.Holonics.Millennium.NavierStokesFinitePicardNativePathJoin
