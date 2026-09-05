import ElementaryHolonics.Millennium.NavierStokesOpenFourierMildIdentity
import ElementaryHolonics.Millennium.NavierStokesH3DivergenceBilinear
import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
import ElementaryHolonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration

/-!
# Axial pressure Fourier mode

This owner exposes the actual scalar pressure coefficient and its exact vertical gradient
multiplier for an admitted open periodic solution.  The pressure zero mode remains free.  The
nonlinear identity reducing the vertical advective mode to the Fourier coefficient of the square
of the vertical velocity is derived from the actual divergence-form Fourier source.
-/

noncomputable section

open ContDiff Function Set Topology MeasureTheory
open scoped BigOperators ComplexConjugate Laplacian

namespace Soma.Holonics.Millennium.NavierStokesAxialPressureMode

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesWeightedProductReconstruction
open Soma.Holonics.Millennium.NavierStokesH3Bilinear

/-- The actual scalar Fourier coefficient of an admitted pressure slice. -/
def axialPressureScalarMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ℂ :=
  scalarFourierMode (fun x ↦ pressure x t.1)
    (openPeriodicSolutionOn_pressureSlice_contDiff solution t.2).continuous
    (solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k

theorem openPressureGradientMode_component_two_eq_multiplier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    openPressureGradientMode solution t k 2 =
      (2 * (Real.pi : ℂ) * Complex.I * (k 2 : ℂ)) *
        axialPressureScalarMode solution t k := by
  unfold openPressureGradientMode axialPressureScalarMode
  have h := vectorSpatialFourierCoeff_gradient_eq_frequency
    (fun x ↦ pressure x t.1)
    (openPeriodicSolutionOn_pressureSlice_contDiff solution t.2)
    (solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k
  exact congrArg (fun v : ComplexVector => v 2) h

theorem openPressureGradientMode_component_eq_zero_of_zero_frequency_two
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) (hk : k 2 = 0) :
    openPressureGradientMode solution t k 2 = 0 := by
  rw [openPressureGradientMode_component_two_eq_multiplier solution t k, hk]
  simp

/-- The exact unforced axial velocity-mode equation, retaining the actual nonlinear and pressure
source coefficients. -/
theorem axial_velocity_mode_hasDerivAt_unforced
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (k : SpatialFrequency) :
    HasDerivAt (velocityModeComponent velocity k 2)
      (unforcedMomentumModeComponent nu velocity pressure k 2 t) t :=
  openPeriodicSolutionOn_hasDerivAt_velocityModeComponent_unforced solution ht k 2

theorem h3DivergenceConvolution_vertical_component_eq
    (state : NavierStokesInfiniteFourierHeatRestart.PeriodicVectorSobolevThree)
    (k : SpatialFrequency)
    (hk0 : k 0 = 0) (hk1 : k 1 = 0) :
    (h3DivergenceConvolution state state 2).1 k =
      (2 * (Real.pi : ℂ) * Complex.I * (k 2 : ℂ)) *
        (∑' p, (state 2).1 p * (state 2).1 (k - p)) := by
  rw [h3DivergenceConvolution_apply]
  simp [Fin.sum_univ_succ, hk0, hk1]

theorem scalarFourierMode_square_eq_h3Product
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (k : SpatialFrequency) :
    scalarFourierMode (fun x ↦ (u x 2) ^ 2)
        (((EuclideanSpace.proj (2 : Fin 3)).contDiff.comp hu).pow 2).continuous
        ((fun x i ↦ congrArg (fun r : ℝ => r ^ 2)
          (congrArg (fun z : Space => z 2) (hperiodic x i)))) k =
      (scalarH3Product
        (smoothSliceSobolevCoefficients u hu hperiodic 2)
        (smoothSliceSobolevCoefficients u hu hperiodic 2)).1 k := by
  let hsquare : Space → ℝ := fun x ↦ (u x 2) ^ 2
  have hsqLift :
      periodicTorusLift (complexScalarField hsquare)
          (continuous_complexScalarField
            (((EuclideanSpace.proj (2 : Fin 3)).contDiff.comp hu).pow 2).continuous)
          (isOnePeriodic_complexScalarField
          (fun x i ↦ congrArg (fun r : ℝ => r ^ 2)
              (congrArg (fun z : Space => z 2) (hperiodic x i)))) =
        smoothSliceComponentLift u hu hperiodic 2 *
          smoothSliceComponentLift u hu hperiodic 2 := by
    ext q
    rw [← euclideanToSpatialTorus_representative q]
    unfold smoothSliceComponentLift
    simp only [ContinuousMap.mul_apply]
    rw [periodicTorusLift_projection, periodicTorusLift_projection]
    simp [complexScalarField, complexVelocityComponent, hsquare]
    ring
  unfold scalarFourierMode
  rw [hsqLift]
  exact torusSpatialFourierCoeff_smoothSliceComponentLift_mul
    u u hu hu hperiodic hperiodic 2 2 k

theorem openActualAdvectionMode_component_two_eq_vertical_square
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency)
    (hk0 : k 0 = 0) (hk1 : k 1 = 0) :
    openActualAdvectionMode solution t k 2 =
      (2 * (Real.pi : ℂ) * Complex.I * (k 2 : ℂ)) *
        scalarFourierMode (fun x ↦ (velocity x t.1 2) ^ 2)
          (((EuclideanSpace.proj (2 : Fin 3)).contDiff.comp
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)).pow 2).continuous
          ((fun x i ↦ congrArg (fun r : ℝ => r ^ 2)
            (congrArg (fun z : Space => z 2)
              (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩ x i)))) k := by
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let hu : ContDiff ℝ ∞ u := openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let hperiodic : IsOnePeriodic u := solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  let state : PeriodicVectorSobolevThree := openVelocityH3State solution t
  have hdivfree := openVelocityH3State_divergenceFree solution t
  have hdiv := h3DivergenceConvolution_vertical_component_eq
    state k hk0 hk1
  have hconvert := h3DivergenceConvolution_eq_h3AdvectiveConvolution_of_divergenceFree
    hdivfree 2 k
  have hadv := openActualAdvectionMode_eq_h3AdvectiveConvolution solution t k
  have hadv2 := congrArg (fun v : ComplexVector => v 2) hadv
  change openActualAdvectionMode solution t k 2 =
    (h3AdvectiveConvolution state state 2 k) at hadv2
  rw [← hconvert] at hadv2
  change openActualAdvectionMode solution t k 2 =
    (h3DivergenceConvolution state state 2).1 k at hadv2
  rw [hdiv] at hadv2
  rw [hadv2]
  have hprod := (scalarH3Product_apply
    (smoothSliceSobolevCoefficients u hu hperiodic 2)
    (smoothSliceSobolevCoefficients u hu hperiodic 2) k).symm
  dsimp [state, openVelocityH3State, smoothSliceH3State]
  rw [hprod]
  rw [← scalarFourierMode_square_eq_h3Product u hu hperiodic k]

theorem axial_velocity_mode_eq_zero_of_vertical_frequency
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency)
    (hk0 : k 0 = 0) (hk1 : k 1 = 0) (hk2 : k 2 ≠ 0) :
    velocityModeComponent velocity k 2 t.1 = 0 := by
  have hdot := openPeriodicSolutionOn_complexDot_velocityMode_eq_zero solution t k
  change (∑ j : Fin 3, (k j : ℂ) * velocityModeComponent velocity k j t.1) = 0 at hdot
  have hk1' : k (Fin.succ 0) = 0 := by simpa using hk1
  simp only [Fin.sum_univ_succ, hk0, hk1'] at hdot
  have hkc : (k 2 : ℂ) ≠ 0 := by
    exact_mod_cast hk2
  have hdot' : (k 2 : ℂ) * velocityModeComponent velocity k 2 t.1 = 0 := by
    simpa using hdot
  exact (mul_eq_zero.mp hdot').resolve_left hkc

theorem unforced_axial_momentum_mode_component_eq_zero_of_vertical_frequency
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (k : SpatialFrequency)
    (hk0 : k 0 = 0) (hk1 : k 1 = 0) (hk2 : k 2 ≠ 0) :
    unforcedMomentumModeComponent nu velocity pressure k 2 t = 0 := by
  have hzero : ∀ τ ∈ Ioo (0 : ℝ) T,
      velocityModeComponent velocity k 2 τ = 0 := by
    intro τ hτ
    exact axial_velocity_mode_eq_zero_of_vertical_frequency solution ⟨τ, hτ⟩ k hk0 hk1 hk2
  have heq : velocityModeComponent velocity k 2 =ᶠ[𝓝 t] (fun _ : ℝ ↦ 0) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
    exact hzero τ hτ
  have hderiv := axial_velocity_mode_hasDerivAt_unforced solution ht k
  calc
    unforcedMomentumModeComponent nu velocity pressure k 2 t =
        deriv (velocityModeComponent velocity k 2) t := hderiv.deriv.symm
    _ = 0 := by rw [heq.deriv_eq, deriv_const]

theorem openPressureGradientMode_component_two_eq_neg_openActualAdvectionMode_component_two
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency)
    (hk0 : k 0 = 0) (hk1 : k 1 = 0) (hk2 : k 2 ≠ 0) :
    openPressureGradientMode solution t k 2 =
      - openActualAdvectionMode solution t k 2 := by
  have hmode := axial_velocity_mode_eq_zero_of_vertical_frequency
    solution t k hk0 hk1 hk2
  have hmom := unforced_axial_momentum_mode_component_eq_zero_of_vertical_frequency
    solution t.2 k hk0 hk1 hk2
  have hlap := congrArg (fun v : ComplexVector => v 2)
    (openPeriodicSolutionOn_velocityLaplacianMode_eq_stokes solution t k)
  change openVelocityLaplacianMode solution t k 2 =
    (-(torusStokesEigenvalue k : ℂ)) * velocityModeComponent velocity k 2 t.1 at hlap
  rw [hmode] at hlap
  simp at hlap
  have hpf := congrArg (fun v : ComplexVector => v 2)
    (pressureFreeMomentumMode_eq_viscous_sub_advection solution t k)
  rw [pressureFreeMomentumMode,
    Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration.openAdvectionMode_eq_openActualAdvectionMode]
    at hpf
  change unforcedMomentumModeComponent nu velocity pressure k 2 t.1 +
      openPressureGradientMode solution t k 2 =
    (nu : ℂ) * openVelocityLaplacianMode solution t k 2 -
      openActualAdvectionMode solution t k 2 at hpf
  rw [hmom, hlap] at hpf
  simpa using hpf

theorem axial_pressure_scalar_mode_eq_neg_vertical_velocity_square_mode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency)
    (hk0 : k 0 = 0) (hk1 : k 1 = 0) (hk2 : k 2 ≠ 0) :
    axialPressureScalarMode solution t k =
      - scalarFourierMode (fun x ↦ (velocity x t.1 2) ^ 2)
          (((EuclideanSpace.proj (2 : Fin 3)).contDiff.comp
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)).pow 2).continuous
          ((fun x i ↦ congrArg (fun r : ℝ => r ^ 2)
            (congrArg (fun z : Space => z 2)
              (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩ x i)))) k := by
  let squareMode : ℂ := scalarFourierMode (fun x ↦ (velocity x t.1 2) ^ 2)
      (((EuclideanSpace.proj (2 : Fin 3)).contDiff.comp
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)).pow 2).continuous
      ((fun x i ↦ congrArg (fun r : ℝ => r ^ 2)
        (congrArg (fun z : Space => z 2)
          (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩ x i))))
      k
  let multiplier : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (k 2 : ℂ)
  have hgrad := openPressureGradientMode_component_two_eq_neg_openActualAdvectionMode_component_two
    solution t k hk0 hk1 hk2
  have hadv := openActualAdvectionMode_component_two_eq_vertical_square
    solution t k hk0 hk1
  have hmult := openPressureGradientMode_component_two_eq_multiplier solution t k
  have hcancel : multiplier * axialPressureScalarMode solution t k = multiplier * (-squareMode) := by
    calc
      multiplier * axialPressureScalarMode solution t k =
          openPressureGradientMode solution t k 2 := by
            dsimp [multiplier]
            exact hmult.symm
      _ = -openActualAdvectionMode solution t k 2 := hgrad
      _ = -(multiplier * squareMode) := by
        rw [hadv]
      _ = multiplier * (-squareMode) := by ring
  have hmult_ne : multiplier ≠ 0 := by
    dsimp [multiplier]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hkc : (k 2 : ℂ) ≠ 0 := by exact_mod_cast hk2
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero) hkc
  apply mul_left_cancel₀ hmult_ne
  exact hcancel

#print axioms openPressureGradientMode_component_two_eq_multiplier
#print axioms openPressureGradientMode_component_eq_zero_of_zero_frequency_two
#print axioms axial_velocity_mode_hasDerivAt_unforced
#print axioms h3DivergenceConvolution_vertical_component_eq
#print axioms scalarFourierMode_square_eq_h3Product
#print axioms openActualAdvectionMode_component_two_eq_vertical_square
#print axioms axial_velocity_mode_eq_zero_of_vertical_frequency
#print axioms unforced_axial_momentum_mode_component_eq_zero_of_vertical_frequency
#print axioms openPressureGradientMode_component_two_eq_neg_openActualAdvectionMode_component_two
#print axioms axial_pressure_scalar_mode_eq_neg_vertical_velocity_square_mode

end Soma.Holonics.Millennium.NavierStokesAxialPressureMode
