import ElementaryHolonics.Millennium.NavierStokesFinitePicardChronology
import ElementaryHolonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
import ElementaryHolonics.Millennium.NavierStokesWeightedMildCoefficientEquation

/-!
# Finite-aperture coefficients meet the native quadratic source

**[proved-derived; formal-checked]** A native weighted `H³` state has an exact unweighted
complex-vector coefficient population.  If that population is supported in a frequency cube and
the finite aperture contains the cube, every term outside the aperture in the complete advective
convolution vanishes.  Hence the finite projected advective coefficient is exactly the physical
Fourier coefficient of the native weighted Leray quadratic source on the incompressible fibre.

This is a finite-support coefficient passage.  It asserts neither convergence of expanding
apertures nor convergence of the finite Picard chronology.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace Soma.Holonics.Millennium.NavierStokesFiniteNativeQuadraticCoefficientBridge

open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFinitePicardChronology
open Soma.Holonics.Millennium.NavierStokesFiniteScaleAncestry
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The exact native-to-physical coefficient chart -/

/-- The unweighted complex-vector mode population carried by one native weighted `H³` state. -/
def unweightedNativeModePopulation
    (state : PeriodicVectorWeightedSobolev 3) : ComplexFourierModePopulation :=
  fun frequency component ↦
    (unweightedVectorThree state component).1 frequency

@[simp]
theorem unweightedNativeModePopulation_apply
    (state : PeriodicVectorWeightedSobolev 3)
    (frequency : SpatialFrequency) (component : Fin 3) :
    unweightedNativeModePopulation state frequency component =
      (unweightedVectorThree state component).1 frequency :=
  rfl

/-- Modewise incompressibility survives removal of the common positive Sobolev weight at each
frequency. -/
theorem isModewiseDivergenceFree_unweightedVectorThree
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsModewiseDivergenceFree state) :
    IsModewiseDivergenceFree
      (periodicVectorSobolevThreeCoefficients (unweightedVectorThree state)) := by
  intro frequency
  have hweighted := hstate frequency
  change (∑ component : Fin 3,
      (frequency component : ℂ) * state component frequency) = 0 at hweighted
  change (∑ component : Fin 3,
      (frequency component : ℂ) *
        (unweightedVectorThree state component).1 frequency) = 0
  rw [show (∑ component : Fin 3,
      (frequency component : ℂ) *
        (unweightedVectorThree state component).1 frequency) =
      (((Real.sqrt (periodicSobolevWeight 3 frequency))⁻¹ : ℝ) : ℂ) *
        ∑ component : Fin 3,
          (frequency component : ℂ) * state component frequency by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro component _hcomponent
    rw [unweightedVectorThree_coefficient]
    ring,
    hweighted, mul_zero]

/-! ## A support-containing finite aperture is the complete advective coefficient -/

/-- The complete `H³` advective coefficient is the sum of the same addressed interactions used
by the finite chronology. -/
theorem h3AdvectiveConvolution_coefficient_eq_tsum_advectiveInteractions
    (state : PeriodicVectorWeightedSobolev 3)
    (frequency : SpatialFrequency) (output : Fin 3) :
    h3AdvectiveConvolution
        (unweightedVectorThree state) (unweightedVectorThree state) output frequency =
      ∑' parent : SpatialFrequency,
        complexAdvectiveInteraction parent (transportedFrequencyAt frequency parent)
          (unweightedNativeModePopulation state parent)
          (unweightedNativeModePopulation state
            (transportedFrequencyAt frequency parent)) output := by
  have habsolute := periodicVectorSobolevThree_hasAbsolutelySummableComponents
    (unweightedVectorThree state)
  have hterms : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun parent : SpatialFrequency ↦
        (unweightedVectorThree state coordinate).1 parent *
          periodicSobolevThreeDerivative coordinate
            (unweightedVectorThree state output) (frequency - parent) := by
    intro coordinate _hcoordinate
    apply Summable.of_norm
    have hbound := (habsolute coordinate).mul_right
      ‖periodicSobolevThreeDerivative coordinate
        (unweightedVectorThree state output)‖
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun parent ↦ ?_) hbound
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (periodicSobolevThreeDerivative coordinate
          (unweightedVectorThree state output)) (frequency - parent))
      (norm_nonneg _)
  rw [h3AdvectiveConvolution_apply habsolute]
  simp_rw [← periodicSobolevThreeDerivative_apply]
  rw [← Summable.tsum_finsetSum hterms]
  apply tsum_congr
  intro parent
  unfold complexAdvectiveInteraction transportedFrequencyAt
  simp only [complexDot, dotProduct, smul_eq_mul, Pi.smul_apply,
    complexFrequencyVector, unweightedNativeModePopulation_apply,
    periodicSobolevThreeDerivative_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  ring

/-- If the physical coefficient population is supported in a cube contained by the aperture,
the finite advective coefficient is the complete `H³` advective coefficient at every output
mode. -/
theorem finiteAdvectiveCoefficient_eq_h3AdvectiveConvolution_of_cube_support
    (aperture : Finset SpatialFrequency) (radius : ℕ)
    (state : PeriodicVectorWeightedSobolev 3)
    (hsupport : SupportedInFrequencyCube radius
      (unweightedNativeModePopulation state))
    (hcontains : frequencyCube radius ⊆ aperture)
    (frequency : SpatialFrequency) :
    finiteAdvectiveCoefficient aperture
        (unweightedNativeModePopulation state)
        (unweightedNativeModePopulation state) frequency =
      vectorCoefficientAt
        (h3AdvectiveConvolution
          (unweightedVectorThree state) (unweightedVectorThree state)) frequency := by
  funext output
  change finiteAdvectiveCoefficient aperture
      (unweightedNativeModePopulation state)
      (unweightedNativeModePopulation state) frequency output =
    h3AdvectiveConvolution
      (unweightedVectorThree state) (unweightedVectorThree state) output frequency
  rw [h3AdvectiveConvolution_coefficient_eq_tsum_advectiveInteractions]
  unfold finiteAdvectiveCoefficient
  simp only [Finset.sum_apply]
  exact (tsum_eq_sum fun parent hparent ↦ by
    have hparentCube : parent ∉ frequencyCube radius := by
      intro hcube
      exact hparent (hcontains hcube)
    rw [hsupport parent hparentCube]
    simp [complexAdvectiveInteraction, complexDot]).symm

/-! ## The finite projected coefficient is the native quadratic coefficient -/

/-- **Exact finite/native quadratic coefficient bridge.** On a modewise incompressible native
state, a finite aperture containing the complete physical support returns exactly the unweighted
Fourier coefficient of `weightedLerayQuadratic`. -/
theorem finiteProjectedAdvectiveCoefficient_eq_weightedLerayQuadratic_physicalMode
    (aperture : Finset SpatialFrequency) (radius : ℕ)
    (state : PeriodicVectorWeightedSobolev 3)
    (hstate : IsModewiseDivergenceFree state)
    (hsupport : SupportedInFrequencyCube radius
      (unweightedNativeModePopulation state))
    (hcontains : frequencyCube radius ⊆ aperture)
    (frequency : SpatialFrequency) :
    finiteProjectedAdvectiveCoefficient aperture
        (unweightedNativeModePopulation state)
        (unweightedNativeModePopulation state) frequency =
      fun output ↦
        (weightedSobolevCoefficients 2
          (weightedLerayQuadratic state output)).1 frequency := by
  rw [finiteProjectedAdvectiveCoefficient]
  rw [finiteAdvectiveCoefficient_eq_h3AdvectiveConvolution_of_cube_support
    aperture radius state hsupport hcontains frequency]
  have hdivergence :=
    isModewiseDivergenceFree_unweightedVectorThree hstate
  have hidentify :
      (fun output ↦
        (h3DivergenceConvolution
          (unweightedVectorThree state) (unweightedVectorThree state) output).1 frequency) =
      vectorCoefficientAt
        (h3AdvectiveConvolution
          (unweightedVectorThree state) (unweightedVectorThree state)) frequency := by
    funext output
    exact h3DivergenceConvolution_eq_h3AdvectiveConvolution_of_divergenceFree
      hdivergence output frequency
  rw [← hidentify]
  funext output
  rw [weightedLerayQuadratic_apply,
    unweighted_weightedLerayDivergenceConvolution_apply]
  rfl

/-- Componentwise receiver form of the same exact bridge. -/
theorem finiteProjectedAdvectiveCoefficient_component_eq_weightedPhysicalCoefficient
    (aperture : Finset SpatialFrequency) (radius : ℕ)
    (state : PeriodicVectorWeightedSobolev 3)
    (hstate : IsModewiseDivergenceFree state)
    (hsupport : SupportedInFrequencyCube radius
      (unweightedNativeModePopulation state))
    (hcontains : frequencyCube radius ⊆ aperture)
    (frequency : SpatialFrequency) (output : Fin 3) :
    finiteProjectedAdvectiveCoefficient aperture
        (unweightedNativeModePopulation state)
        (unweightedNativeModePopulation state) frequency output =
      weightedPhysicalCoefficient 2 output frequency
        (weightedLerayQuadratic state) := by
  rw [finiteProjectedAdvectiveCoefficient_eq_weightedLerayQuadratic_physicalMode
    aperture radius state hstate hsupport hcontains frequency]
  rfl

section Audit

#print axioms isModewiseDivergenceFree_unweightedVectorThree
#print axioms h3AdvectiveConvolution_coefficient_eq_tsum_advectiveInteractions
#print axioms finiteAdvectiveCoefficient_eq_h3AdvectiveConvolution_of_cube_support
#print axioms finiteProjectedAdvectiveCoefficient_eq_weightedLerayQuadratic_physicalMode
#print axioms finiteProjectedAdvectiveCoefficient_component_eq_weightedPhysicalCoefficient

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteNativeQuadraticCoefficientBridge
