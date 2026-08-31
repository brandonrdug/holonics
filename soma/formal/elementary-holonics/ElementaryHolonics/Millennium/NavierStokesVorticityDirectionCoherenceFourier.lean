import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction

/-!
# The cross-direction population is the Fourier chart of a two-point coherence field

**[proved-derived]** Fixing one receiving vorticity occurrence turns cross product into a complex
continuous-linear map.  It therefore commutes with the genuine-torus Bochner Fourier integral.
The cross of the receiver with every actual vorticity coefficient is exactly the coefficient of
the two-point field `y ↦ omega(x) × omega(y)`, and character transport preserves its exact `L¹`
mass.  This removes the final coefficient-side interpretation gap before a spatial coherence
estimate can act.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceFourier

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Cross with a fixed receiver, bundled as the continuous-linear transport through which the
Fourier integral factors. -/
def complexCrossLeftCLM (receiver : ComplexVector) :
    ComplexVector →L[ℂ] ComplexVector :=
  LinearMap.toContinuousLinearMap (crossProduct receiver)

@[simp]
theorem complexCrossLeftCLM_apply
    (receiver source : ComplexVector) :
    complexCrossLeftCLM receiver source = receiverCrossDifference receiver source :=
  rfl

/-- The genuine-torus two-point cross field obtained by fixing one receiving occurrence and
letting the source vorticity vary over the other torus point. -/
def periodicCrossDirectionField
    (receiver : ComplexVector) (field : Space → Space)
    (hcontinuous : Continuous field) (hperiodic : IsOnePeriodic field) :
    C(SpatialTorus, ComplexVector) where
  toFun := fun q ↦ receiverCrossDifference receiver
    (periodicTorusLift (fun x ↦ complexifySpace (field x))
      (continuous_complexify_field hcontinuous)
      (isOnePeriodic_complexify_field hperiodic) q)
  continuous_toFun := (complexCrossLeftCLM receiver).continuous.comp
    (periodicTorusLift (fun x ↦ complexifySpace (field x))
      (continuous_complexify_field hcontinuous)
      (isOnePeriodic_complexify_field hperiodic)).continuous

/-- **Exact Fourier/coherence interchange.**  The cross difference of one vector coefficient is
the coefficient of the complete quotient-descended cross-direction field. -/
theorem receiverCrossDifference_vectorSpatialFourierCoeff
    (receiver : ComplexVector) (field : Space → Space)
    (hcontinuous : Continuous field) (hperiodic : IsOnePeriodic field)
    (frequency : SpatialFrequency) :
    receiverCrossDifference receiver
        (vectorSpatialFourierCoeff field hcontinuous hperiodic frequency) =
      UnitAddTorus.mFourierCoeff
        (periodicCrossDirectionField receiver field hcontinuous hperiodic) frequency := by
  let vectorLift : C(SpatialTorus, ComplexVector) :=
    periodicTorusLift (fun x ↦ complexifySpace (field x))
      (continuous_complexify_field hcontinuous)
      (isOnePeriodic_complexify_field hperiodic)
  let integrand : C(SpatialTorus, ComplexVector) := {
    toFun := fun q ↦ UnitAddTorus.mFourier (-frequency) q • vectorLift q
    continuous_toFun :=
      (UnitAddTorus.mFourier (-frequency)).continuous.smul vectorLift.continuous }
  have hintegrable : Integrable integrand :=
    continuousMap_integrable_on_compact integrand
  let L := complexCrossLeftCLM receiver
  rw [receiverCrossDifference, vectorSpatialFourierCoeff,
    UnitAddTorus.mFourierCoeff, periodicCrossDirectionField,
    UnitAddTorus.mFourierCoeff]
  change L (∫ q : SpatialTorus, integrand q) =
    ∫ q : SpatialTorus,
      UnitAddTorus.mFourier (-frequency) q • L (vectorLift q)
  rw [← L.integral_comp_comm hintegrable]
  apply integral_congr_ae
  filter_upwards [] with q
  exact L.map_smul_of_tower (UnitAddTorus.mFourier (-frequency) q) (vectorLift q)

/-- The actual two-point vorticity coherence field at receiver `q`. -/
def openPeriodicCrossDirectionField
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : C(SpatialTorus, ComplexVector) :=
  periodicCrossDirectionField (openPeriodicComplexVorticityAt solution t q)
    (fun x ↦ vorticityAt (fun y ↦ velocity y t.1) x)
    (continuous_vorticityAt
      (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2))
    (isOnePeriodic_vorticityAt
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩))

/-- Every actual cross-direction coefficient is exactly the Fourier coefficient of the two-point
coherence field. -/
theorem mFourierCoeff_openPeriodicCrossDirectionField
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (openPeriodicCrossDirectionField solution t q) frequency =
      receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
        (openPeriodicVorticityFourierMode solution t frequency) := by
  exact (receiverCrossDifference_vectorSpatialFourierCoeff
    (openPeriodicComplexVorticityAt solution t q)
    (fun x ↦ vorticityAt (fun y ↦ velocity y t.1) x)
    (continuous_vorticityAt
      (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2))
    (isOnePeriodic_vorticityAt
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)) frequency).symm

/-- Character transport moves the coherence coefficient to the receiver point without changing
its oriented cross lineage. -/
theorem receiverCrossDifference_openPeriodicTransportedVorticityMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (frequency : SpatialFrequency) :
    receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
        (openPeriodicTransportedVorticityMode solution t q frequency) =
      UnitAddTorus.mFourier frequency q •
        UnitAddTorus.mFourierCoeff
          (openPeriodicCrossDirectionField solution t q) frequency := by
  rw [openPeriodicTransportedVorticityMode,
    mFourierCoeff_openPeriodicCrossDirectionField]
  exact map_smul (crossProduct (openPeriodicComplexVorticityAt solution t q))
    (UnitAddTorus.mFourier frequency q)
    (openPeriodicVorticityFourierMode solution t frequency)

/-- Finite absolute coefficient mass of the actual two-point coherence field. -/
def openPeriodicCrossDirectionCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) : ℝ :=
  ∑ frequency ∈ modes,
    complexVectorL1
      (UnitAddTorus.mFourierCoeff
        (openPeriodicCrossDirectionField solution t q) frequency)

/-- **[proved-derived; formal-checked]** The finite cross mass in the physical stretching bound is
exactly the finite absolute Fourier-coefficient mass of the two-point spatial coherence field.
Characters contribute no norm factor. -/
theorem openPeriodicFiniteCrossDirectionMass_eq_coherenceCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) :
    openPeriodicFiniteCrossDirectionMass solution t q modes =
      openPeriodicCrossDirectionCoefficientMass solution t q modes := by
  unfold openPeriodicFiniteCrossDirectionMass finiteCrossDirectionMass
    openPeriodicCrossDirectionCoefficientMass
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  rw [receiverCrossDifference_openPeriodicTransportedVorticityMode,
    complexVectorL1_smul]
  have hcharacter : ‖UnitAddTorus.mFourier frequency q‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
      fourier_apply, Circle.norm_coe, Finset.prod_const_one]
  rw [hcharacter, one_mul]

/-- The complete physical stretching inequality now consumes the literal Fourier coefficient
population of the spatial two-point coherence field. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le_coherenceCoefficients
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (radius : ℕ) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
          (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
                (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
              openPeriodicCrossDirectionCoefficientMass solution t q
                (frequencyCube radius)) +
        ((2 * Real.pi) *
            Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
              ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
                (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
                (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  rw [← openPeriodicFiniteCrossDirectionMass_eq_coherenceCoefficientMass]
  exact
    abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le_crossDirection
      solution t q radius

section Audit

#print axioms complexCrossLeftCLM_apply
#print axioms receiverCrossDifference_vectorSpatialFourierCoeff
#print axioms mFourierCoeff_openPeriodicCrossDirectionField
#print axioms receiverCrossDifference_openPeriodicTransportedVorticityMode
#print axioms openPeriodicFiniteCrossDirectionMass_eq_coherenceCoefficientMass
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le_coherenceCoefficients

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceFourier
