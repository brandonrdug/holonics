import ElementaryHolonics.Millennium.NavierStokesTranslationDissipation
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionSourceModulus

/-!
# Physical vorticity translation differences are controlled by dissipation

**[proved-derived]** The coefficient-space translation law is returned to the genuine spatial
torus.  Translation of a continuous scalar field multiplies its complete Fourier population by
the exact character residue.  Parseval therefore identifies the coefficient difference mass with
the physical `L²` translation-difference population.  Applied componentwise to actual vorticity,
the result is controlled by the physical vorticity dissipation already carried by the enstrophy
identity.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Soma.Holonics.Millennium.NavierStokesPhysicalTranslationDissipation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Translate one continuous scalar torus field by an addressed torus occurrence. -/
def torusTranslateScalar (field : C(SpatialTorus, ℂ)) (shift : SpatialTorus) :
    C(SpatialTorus, ℂ) where
  toFun q := field (q + shift)
  continuous_toFun := field.continuous.comp (continuous_id.add continuous_const)

/-- The physical scalar difference returned by one torus translation. -/
def torusTranslationDifferenceScalar
    (field : C(SpatialTorus, ℂ)) (shift : SpatialTorus) : C(SpatialTorus, ℂ) :=
  torusTranslateScalar field shift - field

/-- Translation acts diagonally on the genuine torus Fourier receiver. -/
theorem mFourierCoeff_torusTranslateScalar
    (field : C(SpatialTorus, ℂ)) (shift : SpatialTorus) (k : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff (torusTranslateScalar field shift) k =
      UnitAddTorus.mFourier k shift * UnitAddTorus.mFourierCoeff field k := by
  rw [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourierCoeff]
  change (∫ q : SpatialTorus,
      UnitAddTorus.mFourier (-k) q * field (q + shift)) =
    UnitAddTorus.mFourier k shift *
      ∫ q : SpatialTorus, UnitAddTorus.mFourier (-k) q * field q
  let translatedIntegrand : SpatialTorus → ℂ := fun q ↦
    UnitAddTorus.mFourier (-k) (q - shift) * field q
  have htranslate := integral_add_right_eq_self
    (μ := (volume : Measure SpatialTorus)) translatedIntegrand shift
  have hrewrite :
      (∫ q : SpatialTorus,
          UnitAddTorus.mFourier (-k) q * field (q + shift)) =
        ∫ q : SpatialTorus,
          UnitAddTorus.mFourier (-k) (q - shift) * field q := by
    simpa [translatedIntegrand] using htranslate
  rw [hrewrite, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [mFourier_sub_apply]
  simp only [neg_neg]
  ring

/-- The returned Fourier coefficient is exactly the character difference times the source
coefficient. -/
theorem mFourierCoeff_torusTranslationDifferenceScalar
    (field : C(SpatialTorus, ℂ)) (shift : SpatialTorus) (k : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff (torusTranslationDifferenceScalar field shift) k =
      (UnitAddTorus.mFourier k shift - 1) *
        UnitAddTorus.mFourierCoeff field k := by
  let sourceIntegrand : C(SpatialTorus, ℂ) := {
    toFun := fun q ↦ UnitAddTorus.mFourier (-k) q * field q
    continuous_toFun := by fun_prop }
  let translated : C(SpatialTorus, ℂ) := torusTranslateScalar field shift
  let translatedIntegrand : C(SpatialTorus, ℂ) := {
    toFun := fun q ↦ UnitAddTorus.mFourier (-k) q * translated q
    continuous_toFun := by fun_prop }
  have hsource : Integrable sourceIntegrand := continuousMap_integrable_on_compact sourceIntegrand
  have htranslated : Integrable translatedIntegrand :=
    continuousMap_integrable_on_compact translatedIntegrand
  rw [UnitAddTorus.mFourierCoeff]
  change (∫ q : SpatialTorus,
      UnitAddTorus.mFourier (-k) q * (translated q - field q)) = _
  rw [show (∫ q : SpatialTorus,
      UnitAddTorus.mFourier (-k) q * (translated q - field q)) =
      (∫ q : SpatialTorus, translatedIntegrand q) -
        ∫ q : SpatialTorus, sourceIntegrand q by
    rw [← integral_sub htranslated hsource]
    apply integral_congr_ae
    filter_upwards [] with q
    simp [translatedIntegrand, sourceIntegrand]
    ring]
  rw [show (∫ q : SpatialTorus, translatedIntegrand q) =
      UnitAddTorus.mFourierCoeff translated k by rfl]
  rw [show (∫ q : SpatialTorus, sourceIntegrand q) =
      UnitAddTorus.mFourierCoeff field k by rfl]
  rw [mFourierCoeff_torusTranslateScalar]
  ring

/-- The complete Fourier `ℓ2` carrier of one physical scalar translation difference. -/
def torusTranslationDifferenceFourierL2
    (field : C(SpatialTorus, ℂ)) (shift : SpatialTorus) : PeriodicFourierL2 :=
  periodicFourierRepresentation
    ((torusTranslationDifferenceScalar field shift).toLp 2 volume ℂ)

@[simp]
theorem torusTranslationDifferenceFourierL2_apply
    (field : C(SpatialTorus, ℂ)) (shift : SpatialTorus) (k : SpatialFrequency) :
    torusTranslationDifferenceFourierL2 field shift k =
      (UnitAddTorus.mFourier k shift - 1) *
        UnitAddTorus.mFourierCoeff field k := by
  rw [torusTranslationDifferenceFourierL2, periodicFourierRepresentation_apply,
    UnitAddTorus.mFourierCoeff_toLp,
    mFourierCoeff_torusTranslationDifferenceScalar]

/-- Parseval returns the complete coefficient difference mass as the literal physical square
integral of the translated field difference. -/
theorem tsum_sq_torusTranslationDifferenceFourierL2_eq_integral
    (field : C(SpatialTorus, ℂ)) (shift : SpatialTorus) :
    (∑' k : SpatialFrequency,
      ‖torusTranslationDifferenceFourierL2 field shift k‖ ^ 2) =
      ∫ q : SpatialTorus, ‖field (q + shift) - field q‖ ^ 2 := by
  have hparseval := UnitAddTorus.hasSum_sq_mFourierCoeff
    ((torusTranslationDifferenceScalar field shift).toLp 2 volume ℂ)
  have hintegral :
      (∫ q : SpatialTorus,
          ‖((torusTranslationDifferenceScalar field shift).toLp 2 volume ℂ) q‖ ^ 2) =
        ∫ q : SpatialTorus, ‖field (q + shift) - field q‖ ^ 2 := by
    have hcoe :
        (((torusTranslationDifferenceScalar field shift).toLp 2 volume ℂ :
            SpatialTorus → ℂ)) =ᵐ[volume]
          torusTranslationDifferenceScalar field shift :=
      (torusTranslationDifferenceScalar field shift).coeFn_toLp volume
    apply integral_congr_ae
    filter_upwards [hcoe] with q hq
    rw [hq]
    rfl
  rw [← hintegral]
  exact (HasSum.congr_fun hparseval (fun k ↦ by
    apply congrArg (fun z : ℂ ↦ ‖z‖ ^ 2)
    exact periodicFourierRepresentation_apply
      ((torusTranslationDifferenceScalar field shift).toLp 2 volume ℂ) k)).tsum_eq

/-- One scalar component of the actual complex vorticity torus field. -/
def openPeriodicComplexVorticityComponent
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) : C(SpatialTorus, ℂ) where
  toFun q := complexTorusVorticitySlice solution t q component
  continuous_toFun := continuous_apply component |>.comp
    (complexTorusVorticitySlice solution t).continuous

/-- The generic physical translation Parseval identity is exactly the coefficient mass already
attached to the actual vorticity component. -/
theorem integral_translationDifference_openPeriodicVorticityComponent_eq_fourierMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) (displacement : Space) :
    (∫ q : SpatialTorus,
      ‖openPeriodicComplexVorticityComponent solution t component
          (q + euclideanToSpatialTorus displacement) -
        openPeriodicComplexVorticityComponent solution t component q‖ ^ 2) =
      fourierTranslationDifferenceMass
        (openPeriodicVorticityComponentFourierL2 solution t component) displacement := by
  rw [← tsum_sq_torusTranslationDifferenceFourierL2_eq_integral]
  unfold fourierTranslationDifferenceMass
  apply tsum_congr
  intro k
  apply congrArg (fun z : ℝ ↦ z ^ 2)
  rw [torusTranslationDifferenceFourierL2_apply,
    ← euclideanFourierCharacter_eq_mFourier]
  apply congrArg norm
  congr 1
  rw [openPeriodicVorticityComponentFourierL2_apply]
  rw [openPeriodicVorticityFourierMode_eq_mFourierCoeff,
    mFourierCoeff_apply]
  rfl

/-- The real geometric `L²` translation-difference population of the actual vorticity field. -/
def openPeriodicVorticityTranslationSquareMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (shift : SpatialTorus) : ℝ :=
  ∫ q : SpatialTorus,
    ‖torusVorticityEvolution solution t (q + shift) -
      torusVorticityEvolution solution t q‖ ^ 2

/-- Componentwise complex Parseval and the real Euclidean metric identify the complete physical
translation population with the sum of the three scalar Fourier difference masses. -/
theorem openPeriodicVorticityTranslationSquareMass_eq_sum_fourierMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (displacement : Space) :
    openPeriodicVorticityTranslationSquareMass solution t
        (euclideanToSpatialTorus displacement) =
      ∑ component : Fin 3,
        fourierTranslationDifferenceMass
          (openPeriodicVorticityComponentFourierL2 solution t component) displacement := by
  let shift := euclideanToSpatialTorus displacement
  have hcomponentIntegrable : ∀ component : Fin 3,
      Integrable (fun q : SpatialTorus ↦
        ‖openPeriodicComplexVorticityComponent solution t component (q + shift) -
          openPeriodicComplexVorticityComponent solution t component q‖ ^ 2) := by
    intro component
    exact continuousMap_integrable_on_compact {
      toFun := fun q : SpatialTorus ↦
        ‖openPeriodicComplexVorticityComponent solution t component (q + shift) -
          openPeriodicComplexVorticityComponent solution t component q‖ ^ 2
      continuous_toFun := by fun_prop }
  unfold openPeriodicVorticityTranslationSquareMass
  calc
    (∫ q : SpatialTorus,
        ‖torusVorticityEvolution solution t (q + euclideanToSpatialTorus displacement) -
          torusVorticityEvolution solution t q‖ ^ 2) =
      ∫ q : SpatialTorus,
        ∑ component : Fin 3,
          ‖openPeriodicComplexVorticityComponent solution t component (q + shift) -
            openPeriodicComplexVorticityComponent solution t component q‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [] with q
          rw [EuclideanSpace.norm_sq_eq]
          apply Finset.sum_congr rfl
          intro component _hcomponent
          simp [openPeriodicComplexVorticityComponent, complexTorusVorticitySlice,
            complexifySpace, Real.norm_eq_abs, sq_abs, shift]
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ∑ component : Fin 3,
        ∫ q : SpatialTorus,
          ‖openPeriodicComplexVorticityComponent solution t component (q + shift) -
            openPeriodicComplexVorticityComponent solution t component q‖ ^ 2 := by
      rw [integral_finset_sum Finset.univ
        (fun component _hcomponent ↦ hcomponentIntegrable component)]
    _ = ∑ component : Fin 3,
        fourierTranslationDifferenceMass
          (openPeriodicVorticityComponentFourierL2 solution t component) displacement := by
      apply Finset.sum_congr rfl
      intro component _hcomponent
      exact integral_translationDifference_openPeriodicVorticityComponent_eq_fourierMass
        solution t component displacement

/-- **[proved-derived; formal-checked]** The literal physical vorticity translation population
factors through the physical dissipation population. -/
theorem openPeriodicVorticityTranslationSquareMass_le_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (displacement : Space) :
    openPeriodicVorticityTranslationSquareMass solution t
        (euclideanToSpatialTorus displacement) ≤
      3 * ‖displacement‖ ^ 2 * periodicVorticityDissipation velocity t.1 := by
  rw [openPeriodicVorticityTranslationSquareMass_eq_sum_fourierMass]
  exact sum_fourierTranslationDifferenceMass_openPeriodicVorticity_le_dissipation
    solution t displacement

/-- Centering the displacement chart turns the Euclidean factor into an exact torus-distance
factor. -/
theorem openPeriodicVorticityTranslationSquareMass_le_torusDistance_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (shift : SpatialTorus) :
    openPeriodicVorticityTranslationSquareMass solution t shift ≤
      27 * dist shift 0 ^ 2 * periodicVorticityDissipation velocity t.1 := by
  let displacement := centeredEuclideanRepresentative shift
  have hsource := openPeriodicVorticityTranslationSquareMass_le_dissipation
    solution t displacement
  rw [euclideanToSpatialTorus_centeredEuclideanRepresentative] at hsource
  have hnorm := norm_centeredEuclideanRepresentative_le_three_mul_dist shift
  have hsquare : ‖displacement‖ ^ 2 ≤ (3 * dist shift 0) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg displacement) hnorm 2
  have hcoefficientNonneg :
      0 ≤ ∑ component : Fin 3,
        stokesDissipationMass
          (openPeriodicVorticityComponentFourierL2 solution t component) := by
    apply Finset.sum_nonneg
    intro component _hcomponent
    unfold stokesDissipationMass
    exact tsum_nonneg fun k ↦
      mul_nonneg (torusStokesEigenvalue_nonneg k) (sq_nonneg _)
  have hdissipation : 0 ≤ periodicVorticityDissipation velocity t.1 := by
    rw [sum_stokesDissipationMass_openPeriodicVorticityComponent_eq_dissipation
      solution t] at hcoefficientNonneg
    exact hcoefficientNonneg
  calc
    openPeriodicVorticityTranslationSquareMass solution t shift ≤
        3 * ‖displacement‖ ^ 2 * periodicVorticityDissipation velocity t.1 := hsource
    _ ≤ 3 * (3 * dist shift 0) ^ 2 *
        periodicVorticityDissipation velocity t.1 := by gcongr
    _ = 27 * dist shift 0 ^ 2 * periodicVorticityDissipation velocity t.1 := by ring

section Audit

#print axioms mFourierCoeff_torusTranslateScalar
#print axioms mFourierCoeff_torusTranslationDifferenceScalar
#print axioms torusTranslationDifferenceFourierL2_apply
#print axioms tsum_sq_torusTranslationDifferenceFourierL2_eq_integral
#print axioms integral_translationDifference_openPeriodicVorticityComponent_eq_fourierMass
#print axioms openPeriodicVorticityTranslationSquareMass_eq_sum_fourierMass
#print axioms openPeriodicVorticityTranslationSquareMass_le_dissipation
#print axioms openPeriodicVorticityTranslationSquareMass_le_torusDistance_dissipation

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalTranslationDissipation
