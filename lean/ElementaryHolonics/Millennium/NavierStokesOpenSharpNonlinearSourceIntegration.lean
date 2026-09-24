import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
import ElementaryHolonics.Millennium.NavierStokesSharpNonlinearSource
import ElementaryHolonics.Millennium.NavierStokesWeightedDivergenceFree
import ElementaryHolonics.Millennium.NavierStokesWeightedMildPhysicalSource

/-!
# The actual open vorticity source is the sharp nonlinear source coefficient

**[proved-derived]** The actual smooth open slice and its native weighted `H³` realization carry
the same complete coefficient population.  Its exact incompressibility incidence identifies the
advective and divergence-form quadratic coefficients.  After the already-founded Leray and curl
receivers, the named open vorticity source is therefore exactly the curl of the unweighted
coefficient of `sharpNonlinearSource`.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildPhysicalSource
open Soma.Holonics.Millennium.NavierStokesWeightedProductReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- The native weighted `H³` state of one actual strict-interior velocity slice. -/
def openVelocityWeightedH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : PeriodicVectorWeightedSobolev 3 :=
  smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)

/-- Unweighting the actual native slice returns exactly the old complete `H³` coefficient state
used by the open advection bridge. -/
theorem unweightedVectorThree_openVelocityWeightedH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    unweightedVectorThree (openVelocityWeightedH3State solution t) =
      openVelocityH3State solution t := by
  funext component
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change
    (weightedSobolevCoefficients 3
      (smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) component)).1 k =
      (smoothSliceSobolevCoefficients (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) component).1 k
  rw [smoothSliceVectorWeightedH3,
    weightedSobolevCoefficients_smoothSliceWeightedH3Component]

/-- The actual weighted open slice lies in the exact modewise incompressible fibre. -/
theorem openVelocityWeightedH3State_divergenceFree
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    IsModewiseDivergenceFree (openVelocityWeightedH3State solution t) := by
  apply isModewiseDivergenceFree_smoothSliceVectorWeightedH3
  intro x
  exact solution.incompressible x t.1 ⟨t.2.1.le, t.2.2⟩

/-- The identical unweighted coefficient state carries the same exact incompressibility
incidence. -/
theorem openVelocityH3State_divergenceFree
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    IsModewiseDivergenceFree
      (periodicVectorSobolevThreeCoefficients (openVelocityH3State solution t)) := by
  intro k
  have hmode := complexDot_vectorSpatialFourierCoeff_eq_zero_of_divergenceFree
    (fun x ↦ velocity x t.1)
    ((openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).of_le (by norm_num))
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
    (fun x ↦ solution.incompressible x t.1 ⟨t.2.1.le, t.2.2⟩) k
  change (∑ component : Fin 3, (k component : ℂ) *
    vectorSpatialFourierCoeff (fun x ↦ velocity x t.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).continuous
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k component) = 0 at hmode
  change (∑ component : Fin 3,
    (k component : ℂ) * (openVelocityH3State solution t component).1 k) = 0
  unfold openVelocityH3State smoothSliceH3State
  simpa only [smoothSliceSobolevCoefficients,
    smoothSliceFourierL2_apply] using hmode

/-! ## Exact divergence/advection coefficient identification -/

/-- On the modewise incompressible fibre, the complete divergence-form coefficient is the
complete advective coefficient. -/
theorem h3DivergenceConvolution_eq_h3AdvectiveConvolution_of_divergenceFree
    {state : PeriodicVectorSobolevThree}
    (hstate : IsModewiseDivergenceFree
      (periodicVectorSobolevThreeCoefficients state))
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution state state output).1 k =
      h3AdvectiveConvolution state state output k := by
  have habsolute :=
    periodicVectorSobolevThree_hasAbsolutelySummableComponents state
  rw [h3DivergenceConvolution_apply,
    h3AdvectiveConvolution_apply habsolute]
  let derivativeScale : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hleft : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun p : SpatialFrequency ↦
        (derivativeScale * (k coordinate : ℂ)) *
          ((state coordinate).1 p * (state output).1 (k - p)) := by
    intro coordinate _hcoordinate
    exact (summable_scalarH3ConvolutionTerms
      (state coordinate) (state output) k).mul_left _
  have hpMoment : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun p : SpatialFrequency ↦
        derivativeScale * ((p coordinate : ℂ) * (state coordinate).1 p) *
          (state output).1 (k - p) := by
    intro coordinate _hcoordinate
    have hmomentNorm :=
      summable_coordinate_mul_norm_periodicSobolevThreeCoefficient
        (state coordinate) coordinate
    have hmoment : Summable fun p : SpatialFrequency ↦
        (p coordinate : ℂ) * (state coordinate).1 p := by
      apply Summable.of_norm
      simpa only [norm_mul, Complex.norm_intCast, Int.cast_abs] using hmomentNorm
    have hproduct : Summable fun p : SpatialFrequency ↦
        ((p coordinate : ℂ) * (state coordinate).1 p) *
          (state output).1 (k - p) := by
      apply Summable.of_norm
      have hbound := (hmoment.norm).mul_right ‖(state output).1‖
      refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) hbound
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (state output).1 (k - p)) (norm_nonneg _)
    apply (hproduct.mul_left derivativeScale).congr
    intro p
    ring
  have hright : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun p : SpatialFrequency ↦
        (state coordinate).1 p *
          ((derivativeScale * ((k - p) coordinate : ℂ)) *
            (state output).1 (k - p)) := by
    intro coordinate hcoordinate
    apply ((hleft coordinate hcoordinate).sub
      (hpMoment coordinate hcoordinate)).congr
    intro p
    dsimp only [derivativeScale]
    rw [show (((k - p) coordinate : ℤ) : ℂ) =
      (k coordinate : ℂ) - (p coordinate : ℂ) by simp [Pi.sub_apply]]
    ring
  change
    (∑ coordinate : Fin 3,
      (derivativeScale * (k coordinate : ℂ)) *
        ∑' p, (state coordinate).1 p * (state output).1 (k - p)) =
      ∑ coordinate : Fin 3, ∑' p,
        (state coordinate).1 p *
          ((derivativeScale * ((k - p) coordinate : ℂ)) *
            (state output).1 (k - p))
  calc
    (∑ coordinate : Fin 3,
        (derivativeScale * (k coordinate : ℂ)) *
          ∑' p, (state coordinate).1 p * (state output).1 (k - p)) =
        ∑ coordinate : Fin 3, ∑' p,
          (derivativeScale * (k coordinate : ℂ)) *
            ((state coordinate).1 p * (state output).1 (k - p)) := by
      apply Finset.sum_congr rfl
      intro coordinate hcoordinate
      symm
      exact (summable_scalarH3ConvolutionTerms
        (state coordinate) (state output) k).tsum_mul_left _
    _ = ∑' p : SpatialFrequency, ∑ coordinate : Fin 3,
          (derivativeScale * (k coordinate : ℂ)) *
            ((state coordinate).1 p * (state output).1 (k - p)) := by
      rw [← Summable.tsum_finsetSum hleft]
    _ = ∑' p : SpatialFrequency, ∑ coordinate : Fin 3,
          (state coordinate).1 p *
            ((derivativeScale * ((k - p) coordinate : ℂ)) *
              (state output).1 (k - p)) := by
      apply tsum_congr
      intro p
      have hpdiv :
          (∑ coordinate : Fin 3,
            (p coordinate : ℂ) * (state coordinate).1 p) = 0 := by
        simpa only [complexDot, dotProduct, complexFrequencyVector,
          vectorCoefficientAt, periodicVectorSobolevThreeCoefficients] using hstate p
      calc
        (∑ coordinate : Fin 3,
            (derivativeScale * (k coordinate : ℂ)) *
              ((state coordinate).1 p * (state output).1 (k - p))) =
            ∑ coordinate : Fin 3,
              ((state coordinate).1 p *
                  ((derivativeScale * ((k - p) coordinate : ℂ)) *
                    (state output).1 (k - p)) +
                derivativeScale * ((p coordinate : ℂ) * (state coordinate).1 p) *
                  (state output).1 (k - p)) := by
          apply Finset.sum_congr rfl
          intro coordinate _hcoordinate
          rw [show (((k - p) coordinate : ℤ) : ℂ) =
            (k coordinate : ℂ) - (p coordinate : ℂ) by simp [Pi.sub_apply]]
          ring
        _ = (∑ coordinate : Fin 3,
              (state coordinate).1 p *
                ((derivativeScale * ((k - p) coordinate : ℂ)) *
                  (state output).1 (k - p))) +
            derivativeScale *
              (∑ coordinate : Fin 3,
                (p coordinate : ℂ) * (state coordinate).1 p) *
              (state output).1 (k - p) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
        _ = _ := by rw [hpdiv]; ring
    _ = ∑ coordinate : Fin 3, ∑' p,
          (state coordinate).1 p *
            ((derivativeScale * ((k - p) coordinate : ℂ)) *
              (state output).1 (k - p)) :=
      Summable.tsum_finsetSum hright

/-! ## The sharp source receiver -/

/-- The unweighted coefficient vector carried by the native weighted sharp nonlinear source. -/
def unweightedSharpNonlinearSourceCoefficient
    (state : PeriodicVectorWeightedSobolev 3) (k : SpatialFrequency) : ComplexVector :=
  fun output ↦
    (weightedSobolevCoefficients 2 (sharpNonlinearSource state output)).1 k

/-- Unweighting `sharpNonlinearSource` exposes exactly its complete projected divergence-form
coefficient. -/
theorem unweightedSharpNonlinearSourceCoefficient_eq
    (state : PeriodicVectorWeightedSobolev 3) (k : SpatialFrequency) :
    unweightedSharpNonlinearSourceCoefficient state k =
      lerayProjectMode k
        (fun output ↦
          (h3DivergenceConvolution
            (unweightedVectorThree state) (unweightedVectorThree state) output).1 k) := by
  funext output
  unfold unweightedSharpNonlinearSourceCoefficient sharpNonlinearSource
  rw [weightedLerayDivergenceConvolution_apply,
    weightedSobolevCoefficients_coefficientWeightedRealization]
  rfl

/-- For the actual open slice, the unweighted sharp source coefficient is the existing
Leray-projected complete advective coefficient. -/
theorem unweightedSharpNonlinearSourceCoefficient_open_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    unweightedSharpNonlinearSourceCoefficient
        (openVelocityWeightedH3State solution t) k =
      lerayProjectedH3AdvectiveCoefficient
        (openVelocityH3State solution t) (openVelocityH3State solution t) k := by
  rw [unweightedSharpNonlinearSourceCoefficient_eq,
    unweightedVectorThree_openVelocityWeightedH3State]
  unfold lerayProjectedH3AdvectiveCoefficient
  congr 1
  funext output
  exact h3DivergenceConvolution_eq_h3AdvectiveConvolution_of_divergenceFree
    (openVelocityH3State_divergenceFree solution t)
    output k

/-- The actual named open vorticity source is exactly the frequency curl of the corresponding
unweighted coefficient of `sharpNonlinearSource`. -/
theorem vorticityNonlinearMode_eq_unweightedSharpNonlinearSourceCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    vorticityNonlinearMode solution t k =
      -frequencyCurlMultiplier k
        (unweightedSharpNonlinearSourceCoefficient
          (openVelocityWeightedH3State solution t) k) := by
  rw [vorticityNonlinearMode_eq_lerayProjectedH3AdvectiveCoefficient,
    unweightedSharpNonlinearSourceCoefficient_open_eq]

section Audit

#print axioms unweightedVectorThree_openVelocityWeightedH3State
#print axioms openVelocityWeightedH3State_divergenceFree
#print axioms openVelocityH3State_divergenceFree
#print axioms h3DivergenceConvolution_eq_h3AdvectiveConvolution_of_divergenceFree
#print axioms unweightedSharpNonlinearSourceCoefficient_eq
#print axioms unweightedSharpNonlinearSourceCoefficient_open_eq
#print axioms vorticityNonlinearMode_eq_unweightedSharpNonlinearSourceCoefficient

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
