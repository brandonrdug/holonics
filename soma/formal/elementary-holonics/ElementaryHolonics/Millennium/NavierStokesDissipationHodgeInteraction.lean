import ElementaryHolonics.Millennium.NavierStokesPhysicalTranslationDissipation
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionEnstrophyClosure

/-!
# Dissipation enters the physical Hodge interaction before pointwise collapse

**[proved-derived]** The exact physical translation current is paired with the actual dyadic
Hodge kernel reading.  A positive receiver parameter retains the two Young branches separately:
one branch is paid by physical vorticity dissipation, while the other returns the spatial fourth-
power vorticity population.  The already proved first-distance kernel moment then glues every
dyadic scale without reintroducing a global vorticity Lipschitz coefficient.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Soma.Holonics.Millennium.NavierStokesDissipationHodgeInteraction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPhysicalTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionEnstrophyClosure
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesTranslationDissipation

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The physical source populations -/

/-- The spatial fourth-power population left after an `L² × L²` difference interaction. -/
def openPeriodicVorticityFourthPowerMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  ∫ q : SpatialTorus, ‖torusVorticityEvolution solution t q‖ ^ 4

theorem openPeriodicVorticityFourthPowerMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    0 ≤ openPeriodicVorticityFourthPowerMass solution t := by
  unfold openPeriodicVorticityFourthPowerMass
  exact integral_nonneg fun q ↦ pow_nonneg (norm_nonneg _) 4

/-- Physical vorticity dissipation is nonnegative on every admitted strict-interior slice. -/
theorem periodicVorticityDissipation_nonneg_of_openPeriodicSolution
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    0 ≤ periodicVorticityDissipation velocity t.1 := by
  have hsum : 0 ≤ ∑ component : Fin 3,
      stokesDissipationMass
        (openPeriodicVorticityComponentFourierL2 solution t component) := by
    exact Finset.sum_nonneg fun component _ ↦ tsum_nonneg fun k ↦
      mul_nonneg
        (Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat.torusStokesEigenvalue_nonneg k)
        (sq_nonneg _)
  rw [sum_stokesDissipationMass_openPeriodicVorticityComponent_eq_dissipation
    solution t] at hsum
  exact hsum

/-- The complete physical interaction between one addressed translation difference and the
quadratic receiving-vorticity population.  Bundling the displacement as a continuous map keeps
the chart available to the outer Hodge-kernel integral. -/
def openPeriodicVorticityDifferenceInteractionCarrier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : C(SpatialTorus, ℝ) where
  toFun shift := ∫ q : SpatialTorus,
    ‖torusVorticityEvolution solution t (q + shift) -
      torusVorticityEvolution solution t q‖ *
        ‖torusVorticityEvolution solution t q‖ ^ 2
  continuous_toFun := by
    have hintegrand : Continuous (Function.uncurry (fun shift : SpatialTorus ↦
        fun q : SpatialTorus ↦
          ‖torusVorticityEvolution solution t (q + shift) -
            torusVorticityEvolution solution t q‖ *
              ‖torusVorticityEvolution solution t q‖ ^ 2)) := by
      fun_prop
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous
        (μ := (volume : Measure SpatialTorus)) hintegrand (s := Set.univ) isCompact_univ

theorem openPeriodicVorticityDifferenceInteractionCarrier_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (shift : SpatialTorus) :
    0 ≤ openPeriodicVorticityDifferenceInteractionCarrier solution t shift := by
  unfold openPeriodicVorticityDifferenceInteractionCarrier
  exact integral_nonneg fun q ↦ mul_nonneg (norm_nonneg _) (sq_nonneg _)

/-! ## Exact parameterized Young transport -/

/-- Before division by the positive receiver parameter and displacement, the complete interaction
obeys the exact square-completion law. -/
theorem two_mul_parameter_mul_distance_mul_differenceInteraction_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (parameter : ℝ) (shift : SpatialTorus) :
    2 * parameter * dist shift 0 *
        openPeriodicVorticityDifferenceInteractionCarrier solution t shift ≤
      openPeriodicVorticityTranslationSquareMass solution t shift +
        (parameter * dist shift 0) ^ 2 *
          openPeriodicVorticityFourthPowerMass solution t := by
  let omega : C(SpatialTorus, Space) := torusVorticityEvolution solution t
  let distance := dist shift 0
  let leftIntegrand : C(SpatialTorus, ℝ) := {
    toFun := fun q ↦
      2 * parameter * distance *
        (‖omega (q + shift) - omega q‖ * ‖omega q‖ ^ 2)
    continuous_toFun := by fun_prop }
  let rightIntegrand : C(SpatialTorus, ℝ) := {
    toFun := fun q ↦
      ‖omega (q + shift) - omega q‖ ^ 2 +
        (parameter * distance * ‖omega q‖ ^ 2) ^ 2
    continuous_toFun := by fun_prop }
  have hleft : Integrable leftIntegrand :=
    continuousMap_integrable_on_compact leftIntegrand
  have hright : Integrable rightIntegrand :=
    continuousMap_integrable_on_compact rightIntegrand
  have hpoint : ∀ q : SpatialTorus, leftIntegrand q ≤ rightIntegrand q := by
    intro q
    dsimp [leftIntegrand, rightIntegrand]
    nlinarith [sq_nonneg
      (‖omega (q + shift) - omega q‖ -
        parameter * distance * ‖omega q‖ ^ 2)]
  have hintegral : (∫ q : SpatialTorus, leftIntegrand q) ≤
      ∫ q : SpatialTorus, rightIntegrand q :=
    integral_mono hleft hright hpoint
  have hleftEq : (∫ q : SpatialTorus, leftIntegrand q) =
      2 * parameter * dist shift 0 *
        ∫ q : SpatialTorus,
          ‖omega (q + shift) - omega q‖ * ‖omega q‖ ^ 2 := by
    rw [← integral_const_mul]
    rfl
  have hrightEq : (∫ q : SpatialTorus, rightIntegrand q) =
      (∫ q : SpatialTorus, ‖omega (q + shift) - omega q‖ ^ 2) +
        (parameter * dist shift 0) ^ 2 *
          ∫ q : SpatialTorus, ‖omega q‖ ^ 4 := by
    rw [show (∫ q : SpatialTorus, rightIntegrand q) =
        (∫ q : SpatialTorus, ‖omega (q + shift) - omega q‖ ^ 2) +
          ∫ q : SpatialTorus, (parameter * dist shift 0) ^ 2 * ‖omega q‖ ^ 4 by
    rw [← integral_add]
    · apply integral_congr_ae
      filter_upwards [] with q
      dsimp [rightIntegrand]
      ring
    · exact continuousMap_integrable_on_compact {
        toFun := fun q : SpatialTorus ↦ ‖omega (q + shift) - omega q‖ ^ 2
        continuous_toFun := by fun_prop }
    · exact continuousMap_integrable_on_compact {
        toFun := fun q : SpatialTorus ↦
          (parameter * dist shift 0) ^ 2 * ‖omega q‖ ^ 4
        continuous_toFun := by fun_prop }]
    rw [integral_const_mul]
  rw [hleftEq, hrightEq] at hintegral
  exact hintegral

/-- **[proved-derived; formal-checked]** Every addressed physical difference interaction is paid
by an exact tunable pair: vorticity dissipation and the spatial fourth-power population. -/
theorem openPeriodicVorticityDifferenceInteractionCarrier_le_dissipation_fourthPower
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {parameter : ℝ} (hparameter : 0 < parameter)
    (shift : SpatialTorus) :
    openPeriodicVorticityDifferenceInteractionCarrier solution t shift ≤
      dist shift 0 *
        (27 * periodicVorticityDissipation velocity t.1 +
          parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
            (2 * parameter) := by
  by_cases hshift : shift = 0
  · subst shift
    simp [openPeriodicVorticityDifferenceInteractionCarrier]
  have hdistance : 0 < dist shift 0 := dist_pos.mpr hshift
  have hraw := two_mul_parameter_mul_distance_mul_differenceInteraction_le
    solution t parameter shift
  have htranslation :=
    openPeriodicVorticityTranslationSquareMass_le_torusDistance_dissipation
      solution t shift
  have hcombined :
      (2 * parameter *
        openPeriodicVorticityDifferenceInteractionCarrier solution t shift) *
          dist shift 0 ≤
        (dist shift 0 *
          (27 * periodicVorticityDissipation velocity t.1 +
            parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t)) *
              dist shift 0 := by
    calc
      (2 * parameter *
          openPeriodicVorticityDifferenceInteractionCarrier solution t shift) *
            dist shift 0 =
          2 * parameter * dist shift 0 *
            openPeriodicVorticityDifferenceInteractionCarrier solution t shift := by ring
      _ ≤ openPeriodicVorticityTranslationSquareMass solution t shift +
          (parameter * dist shift 0) ^ 2 *
            openPeriodicVorticityFourthPowerMass solution t := hraw
      _ ≤ 27 * dist shift 0 ^ 2 * periodicVorticityDissipation velocity t.1 +
          (parameter * dist shift 0) ^ 2 *
            openPeriodicVorticityFourthPowerMass solution t :=
        add_le_add htranslation le_rfl
      _ = (dist shift 0 *
          (27 * periodicVorticityDissipation velocity t.1 +
            parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t)) *
              dist shift 0 := by ring
  have hcancel :
      2 * parameter *
          openPeriodicVorticityDifferenceInteractionCarrier solution t shift ≤
        dist shift 0 *
          (27 * periodicVorticityDissipation velocity t.1 +
            parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) :=
    le_of_mul_le_mul_right hcombined hdistance
  rw [le_div_iff₀ (by positivity : 0 < 2 * parameter)]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel

/-! ## The actual Hodge kernel consumes the current -/

/-- One dyadic Hodge kernel population tested against the physical difference interaction. -/
def openPeriodicDyadicDissipationHodgeInteractionMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : ℝ :=
  ∫ y : SpatialTorus,
    dyadicHodgeJacobianKernelPointMass scale y *
      openPeriodicVorticityDifferenceInteractionCarrier solution t (-y)

theorem openPeriodicDyadicDissipationHodgeInteractionMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    0 ≤ openPeriodicDyadicDissipationHodgeInteractionMass solution t scale := by
  unfold openPeriodicDyadicDissipationHodgeInteractionMass
  exact integral_nonneg fun y ↦ mul_nonneg
    (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
    (openPeriodicVorticityDifferenceInteractionCarrier_nonneg solution t (-y))

/-- One scale is controlled by its exact first-distance kernel moment and the common tunable
dissipation/fourth-power receiver. -/
theorem openPeriodicDyadicDissipationHodgeInteractionMass_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {parameter : ℝ} (hparameter : 0 < parameter) (scale : ℕ) :
    openPeriodicDyadicDissipationHodgeInteractionMass solution t scale ≤
      dyadicHodgeJacobianKernelModulusMoment (torusDistancePowerModulus 1) scale *
        ((27 * periodicVorticityDissipation velocity t.1 +
          parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
            (2 * parameter)) := by
  let coefficient :=
    (27 * periodicVorticityDissipation velocity t.1 +
      parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
        (2 * parameter)
  have hleft : Integrable (fun y : SpatialTorus ↦
      dyadicHodgeJacobianKernelPointMass scale y *
        openPeriodicVorticityDifferenceInteractionCarrier solution t (-y)) :=
    continuousMap_integrable_on_compact {
      toFun := fun y : SpatialTorus ↦
        dyadicHodgeJacobianKernelPointMass scale y *
          openPeriodicVorticityDifferenceInteractionCarrier solution t (-y)
      continuous_toFun := by
        unfold dyadicHodgeJacobianKernelPointMass
        fun_prop }
  have hright : Integrable (fun y : SpatialTorus ↦
      dyadicHodgeJacobianKernelPointMass scale y * (dist y 0 * coefficient)) :=
    continuousMap_integrable_on_compact {
      toFun := fun y : SpatialTorus ↦
        dyadicHodgeJacobianKernelPointMass scale y * (dist y 0 * coefficient)
      continuous_toFun := by
        unfold dyadicHodgeJacobianKernelPointMass
        fun_prop }
  unfold openPeriodicDyadicDissipationHodgeInteractionMass
  calc
    (∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelPointMass scale y *
          openPeriodicVorticityDifferenceInteractionCarrier solution t (-y)) ≤
      ∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelPointMass scale y * (dist y 0 * coefficient) := by
      apply integral_mono hleft hright
      intro y
      apply mul_le_mul_of_nonneg_left _
        (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
      simpa [coefficient, dist_neg_neg, div_eq_mul_inv, mul_assoc] using
        openPeriodicVorticityDifferenceInteractionCarrier_le_dissipation_fourthPower
          solution t hparameter (-y)
    _ = (∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelPointMass scale y * dist y 0) * coefficient := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = dyadicHodgeJacobianKernelModulusMoment
          (torusDistancePowerModulus 1) scale * coefficient := by
      congr 1
      unfold dyadicHodgeJacobianKernelModulusMoment torusDistancePowerModulus
      simp

/-- The actual absolute stretching-kernel population at one scale, integrated first over the
physical receiver and then over displacement. -/
def openPeriodicDyadicDissipationHodgeStretchingMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : ℝ :=
  ∫ y : SpatialTorus, ∫ q : SpatialTorus,
    ‖dyadicHodgeStretchingKernelReading scale y
      (complexTorusVorticitySlice solution t q)
      (complexTorusVorticitySlice solution t (q - y))‖

/-- Aligned cancellation inserts the literal source-minus-receiver difference into the actual
Hodge reading.  Coordinate `L¹` comparison then costs exactly `3 × 3² = 27`. -/
theorem openPeriodicDyadicDissipationHodgeStretchingMass_le_interaction
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicDyadicDissipationHodgeStretchingMass solution t scale ≤
      27 * openPeriodicDyadicDissipationHodgeInteractionMass solution t scale := by
  let omega : C(SpatialTorus, Space) := torusVorticityEvolution solution t
  have hinner : ∀ y : SpatialTorus,
      (∫ q : SpatialTorus,
        ‖dyadicHodgeStretchingKernelReading scale y
          (complexTorusVorticitySlice solution t q)
          (complexTorusVorticitySlice solution t (q - y))‖) ≤
        27 * dyadicHodgeJacobianKernelPointMass scale y *
          openPeriodicVorticityDifferenceInteractionCarrier solution t (-y) := by
    intro y
    let leftIntegrand : C(SpatialTorus, ℝ) := {
      toFun := fun q ↦
        ‖dyadicHodgeStretchingKernelReading scale y
          (complexTorusVorticitySlice solution t q)
          (complexTorusVorticitySlice solution t (q - y))‖
      continuous_toFun := by
        unfold dyadicHodgeStretchingKernelReading dyadicHodgeJacobianKernelAction
          complexStretchingReading complexDot dotProduct complexMatrixAction
          Matrix.mulVec dyadicHodgeJacobianKernelEntry
        fun_prop }
    let rightIntegrand : C(SpatialTorus, ℝ) := {
      toFun := fun q ↦
        27 * dyadicHodgeJacobianKernelPointMass scale y *
          (‖omega (q - y) - omega q‖ * ‖omega q‖ ^ 2)
      continuous_toFun := by fun_prop }
    have hleft : Integrable leftIntegrand :=
      continuousMap_integrable_on_compact leftIntegrand
    have hright : Integrable rightIntegrand :=
      continuousMap_integrable_on_compact rightIntegrand
    have hpoint : ∀ q : SpatialTorus, leftIntegrand q ≤ rightIntegrand q := by
      intro q
      have hreceiver : complexTorusVorticitySlice solution t q =
          complexOfRealSpace (omega q) := by
        rfl
      have hsource : complexTorusVorticitySlice solution t (q - y) =
          complexOfRealSpace (omega (q - y)) := by
        rfl
      have hdifference :
          complexTorusVorticitySlice solution t (q - y) -
              complexTorusVorticitySlice solution t q =
            complexOfRealSpace (omega (q - y) - omega q) := by
        rw [hreceiver, hsource]
        funext component
        simp [complexOfRealSpace]
      have hreading := norm_dyadicHodgeStretchingKernelReading_le scale y
        (complexTorusVorticitySlice solution t q)
        (complexTorusVorticitySlice solution t (q - y) -
          (1 : ℂ) • complexTorusVorticitySlice solution t q)
      have hdifferenceL1 :
          complexVectorL1
              (complexTorusVorticitySlice solution t (q - y) -
                complexTorusVorticitySlice solution t q) ≤
            3 * ‖omega (q - y) - omega q‖ := by
        rw [hdifference]
        exact complexVectorL1_complexOfRealSpace_le_three_norm _
      have hreceiverL1 :
          complexVectorL1 (complexTorusVorticitySlice solution t q) ≤
            3 * ‖omega q‖ := by
        rw [hreceiver]
        exact complexVectorL1_complexOfRealSpace_le_three_norm _
      have hsame := dyadicHodgeStretchingKernelReading_sub_aligned scale y
        (complexTorusVorticitySlice solution t q)
        (complexTorusVorticitySlice solution t (q - y)) (1 : ℂ)
      dsimp [leftIntegrand, rightIntegrand]
      rw [← hsame]
      simp only [one_smul]
      calc
        ‖dyadicHodgeStretchingKernelReading scale y
            (complexTorusVorticitySlice solution t q)
            (complexTorusVorticitySlice solution t (q - y) -
              complexTorusVorticitySlice solution t q)‖ ≤
          dyadicHodgeJacobianKernelPointMass scale y *
              complexVectorL1
                (complexTorusVorticitySlice solution t (q - y) -
                  complexTorusVorticitySlice solution t q) *
            complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2 :=
          by simpa only [one_smul] using hreading
        _ ≤ dyadicHodgeJacobianKernelPointMass scale y *
              (3 * ‖omega (q - y) - omega q‖) *
            (3 * ‖omega q‖) ^ 2 := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hdifferenceL1
              (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
          · exact pow_le_pow_left₀ (complexVectorL1_nonneg _) hreceiverL1 2
          · exact sq_nonneg _
          · exact mul_nonneg
              (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
              (mul_nonneg (by norm_num) (norm_nonneg _))
        _ = 27 * dyadicHodgeJacobianKernelPointMass scale y *
            (‖omega (q - y) - omega q‖ * ‖omega q‖ ^ 2) := by ring
    calc
      (∫ q : SpatialTorus, leftIntegrand q) ≤
          ∫ q : SpatialTorus, rightIntegrand q :=
        integral_mono hleft hright hpoint
      _ = 27 * dyadicHodgeJacobianKernelPointMass scale y *
          openPeriodicVorticityDifferenceInteractionCarrier solution t (-y) := by
        change (∫ q : SpatialTorus,
          (27 * dyadicHodgeJacobianKernelPointMass scale y) *
            (‖omega (q - y) - omega q‖ * ‖omega q‖ ^ 2)) = _
        rw [integral_const_mul]
        apply congrArg
        unfold openPeriodicVorticityDifferenceInteractionCarrier
        apply integral_congr_ae
        filter_upwards [] with q
        simp [sub_eq_add_neg, omega]
  unfold openPeriodicDyadicDissipationHodgeStretchingMass
    openPeriodicDyadicDissipationHodgeInteractionMass
  have hleft : Integrable (fun y : SpatialTorus ↦ ∫ q : SpatialTorus,
      ‖dyadicHodgeStretchingKernelReading scale y
        (complexTorusVorticitySlice solution t q)
        (complexTorusVorticitySlice solution t (q - y))‖) :=
    continuousMap_integrable_on_compact {
      toFun := fun y : SpatialTorus ↦ ∫ q : SpatialTorus,
        ‖dyadicHodgeStretchingKernelReading scale y
          (complexTorusVorticitySlice solution t q)
          (complexTorusVorticitySlice solution t (q - y))‖
      continuous_toFun := by
        simpa only [Measure.restrict_univ] using
          continuous_parametric_integral_of_continuous
            (μ := (volume : Measure SpatialTorus))
            (s := Set.univ) (by
              unfold dyadicHodgeStretchingKernelReading dyadicHodgeJacobianKernelAction
                complexStretchingReading complexDot dotProduct complexMatrixAction
                Matrix.mulVec dyadicHodgeJacobianKernelEntry
              fun_prop) isCompact_univ }
  have hright : Integrable (fun y : SpatialTorus ↦
      27 * dyadicHodgeJacobianKernelPointMass scale y *
        openPeriodicVorticityDifferenceInteractionCarrier solution t (-y)) :=
    continuousMap_integrable_on_compact {
      toFun := fun y : SpatialTorus ↦
        27 * dyadicHodgeJacobianKernelPointMass scale y *
          openPeriodicVorticityDifferenceInteractionCarrier solution t (-y)
      continuous_toFun := by
        unfold dyadicHodgeJacobianKernelPointMass
        fun_prop }
  calc
    (∫ y : SpatialTorus, ∫ q : SpatialTorus,
        ‖dyadicHodgeStretchingKernelReading scale y
          (complexTorusVorticitySlice solution t q)
          (complexTorusVorticitySlice solution t (q - y))‖) ≤
      ∫ y : SpatialTorus,
        27 * dyadicHodgeJacobianKernelPointMass scale y *
          openPeriodicVorticityDifferenceInteractionCarrier solution t (-y) :=
        integral_mono hleft hright hinner
    _ = 27 * ∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelPointMass scale y *
          openPeriodicVorticityDifferenceInteractionCarrier solution t (-y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring

/-! ## Infinite scale gluing -/

/-- The complete nonnegative Hodge interaction population over every dyadic scale. -/
def openPeriodicFullDissipationHodgeInteractionMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  ∑' scale : ℕ, openPeriodicDyadicDissipationHodgeInteractionMass solution t scale

/-- The first-distance localization theorem makes the new physical interaction summable. -/
theorem summable_openPeriodicDyadicDissipationHodgeInteractionMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {parameter : ℝ} (hparameter : 0 < parameter) :
    Summable (openPeriodicDyadicDissipationHodgeInteractionMass solution t) := by
  let coefficient :=
    (27 * periodicVorticityDissipation velocity t.1 +
      parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
        (2 * parameter)
  have hdissipation : 0 ≤ periodicVorticityDissipation velocity t.1 :=
    periodicVorticityDissipation_nonneg_of_openPeriodicSolution solution t
  have hcoefficient : 0 ≤ coefficient := by
    dsimp [coefficient]
    exact div_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num) hdissipation)
        (mul_nonneg (sq_nonneg parameter)
          (openPeriodicVorticityFourthPowerMass_nonneg solution t)))
      (le_of_lt (by positivity : 0 < 2 * parameter))
  apply Summable.of_nonneg_of_le
    (fun scale ↦ openPeriodicDyadicDissipationHodgeInteractionMass_nonneg solution t scale)
    (fun scale ↦ openPeriodicDyadicDissipationHodgeInteractionMass_le
      solution t hparameter scale)
  exact summableDyadicHodgeJacobianKernelDistanceMoments_inhabited.mul_right coefficient

/-- **[proved-derived; formal-checked]** The full scale population factors through the complete
first-distance Hodge moment and the exact dissipation/fourth-power Young receiver. -/
theorem openPeriodicFullDissipationHodgeInteractionMass_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {parameter : ℝ} (hparameter : 0 < parameter) :
    openPeriodicFullDissipationHodgeInteractionMass solution t ≤
      totalDyadicHodgeDistanceMoment *
        ((27 * periodicVorticityDissipation velocity t.1 +
          parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
            (2 * parameter)) := by
  let coefficient :=
    (27 * periodicVorticityDissipation velocity t.1 +
      parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
        (2 * parameter)
  have hinteraction :=
    summable_openPeriodicDyadicDissipationHodgeInteractionMass solution t hparameter
  have hmoment :=
    summableDyadicHodgeJacobianKernelDistanceMoments_inhabited.mul_right coefficient
  unfold openPeriodicFullDissipationHodgeInteractionMass
  calc
    (∑' scale : ℕ,
        openPeriodicDyadicDissipationHodgeInteractionMass solution t scale) ≤
      ∑' scale : ℕ,
        dyadicHodgeJacobianKernelModulusMoment
          (torusDistancePowerModulus 1) scale * coefficient :=
      hinteraction.tsum_le_tsum
        (fun scale ↦ openPeriodicDyadicDissipationHodgeInteractionMass_le
          solution t hparameter scale) hmoment
    _ = totalDyadicHodgeDistanceMoment * coefficient := by
      rw [_root_.tsum_mul_right]
      rfl

/-- The complete actual dyadic stretching population is summable and is controlled by the new
physical interaction carrier. -/
theorem summable_openPeriodicDyadicDissipationHodgeStretchingMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {parameter : ℝ} (hparameter : 0 < parameter) :
    Summable (openPeriodicDyadicDissipationHodgeStretchingMass solution t) := by
  apply Summable.of_nonneg_of_le
    (fun scale ↦ by
      unfold openPeriodicDyadicDissipationHodgeStretchingMass
      exact integral_nonneg fun y ↦ integral_nonneg fun q ↦ norm_nonneg _)
    (fun scale ↦ openPeriodicDyadicDissipationHodgeStretchingMass_le_interaction
      solution t scale)
  exact (summable_openPeriodicDyadicDissipationHodgeInteractionMass
    solution t hparameter).mul_left 27

/-- **[proved-derived; formal-checked]** The complete actual stretching-kernel population over all
dyadic scales inherits the tunable dissipation/fourth-power estimate. -/
theorem tsum_openPeriodicDyadicDissipationHodgeStretchingMass_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {parameter : ℝ} (hparameter : 0 < parameter) :
    (∑' scale : ℕ,
        openPeriodicDyadicDissipationHodgeStretchingMass solution t scale) ≤
      27 * totalDyadicHodgeDistanceMoment *
        ((27 * periodicVorticityDissipation velocity t.1 +
          parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
            (2 * parameter)) := by
  have hstretching :=
    summable_openPeriodicDyadicDissipationHodgeStretchingMass solution t hparameter
  have hinteraction :=
    summable_openPeriodicDyadicDissipationHodgeInteractionMass solution t hparameter
  calc
    (∑' scale : ℕ,
        openPeriodicDyadicDissipationHodgeStretchingMass solution t scale) ≤
      ∑' scale : ℕ,
        27 * openPeriodicDyadicDissipationHodgeInteractionMass solution t scale :=
      hstretching.tsum_le_tsum
        (fun scale ↦ openPeriodicDyadicDissipationHodgeStretchingMass_le_interaction
          solution t scale)
        (hinteraction.mul_left 27)
    _ = 27 * openPeriodicFullDissipationHodgeInteractionMass solution t := by
      rw [_root_.tsum_mul_left]
      rfl
    _ ≤ 27 * (totalDyadicHodgeDistanceMoment *
        ((27 * periodicVorticityDissipation velocity t.1 +
          parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
            (2 * parameter))) := by
      gcongr
      exact openPeriodicFullDissipationHodgeInteractionMass_le
        solution t hparameter
    _ = 27 * totalDyadicHodgeDistanceMoment *
        ((27 * periodicVorticityDissipation velocity t.1 +
          parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
            (2 * parameter)) := by ring

/-! ## Exact viscous absorption -/

/-- The positive receiver parameter which makes the dissipation branch no larger than half of the
available positive viscosity.  The added one keeps the chart valid even if the Hodge moment
population vanishes. -/
def hodgeDissipationAbsorptionParameter (nu : ℝ) : ℝ :=
  1 + 729 * totalDyadicHodgeDistanceMoment / nu

theorem hodgeDissipationAbsorptionParameter_pos
    {nu : ℝ} (hnu : 0 < nu) :
    0 < hodgeDissipationAbsorptionParameter nu := by
  unfold hodgeDissipationAbsorptionParameter
  have hquotient : 0 ≤ 729 * totalDyadicHodgeDistanceMoment / nu :=
    div_nonneg
      (mul_nonneg (by norm_num) totalDyadicHodgeDistanceMoment_nonneg)
      hnu.le
  linarith

/-- The coefficient of physical dissipation under the absorption chart is at most `nu / 2`. -/
theorem hodgeDissipationCoefficient_le_half_viscosity
    {nu : ℝ} (hnu : 0 < nu) :
    729 * totalDyadicHodgeDistanceMoment /
        (2 * hodgeDissipationAbsorptionParameter nu) ≤ nu / 2 := by
  have hparameter := hodgeDissipationAbsorptionParameter_pos hnu
  rw [div_le_iff₀ (by positivity : 0 < 2 * hodgeDissipationAbsorptionParameter nu)]
  have hidentity :
      nu * hodgeDissipationAbsorptionParameter nu =
        nu + 729 * totalDyadicHodgeDistanceMoment := by
    unfold hodgeDissipationAbsorptionParameter
    field_simp
  rw [show nu / 2 * (2 * hodgeDissipationAbsorptionParameter nu) =
      nu * hodgeDissipationAbsorptionParameter nu by ring]
  rw [hidentity]
  linarith [hnu]

/-- **[proved-derived; formal-checked]** Positive viscosity absorbs half of the complete all-scale
Hodge difference interaction.  The sole returned high-frequency population is the exact spatial
fourth-power vorticity mass. -/
theorem tsum_openPeriodicDyadicDissipationHodgeStretchingMass_le_absorbed
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (hnu : 0 < nu) :
    (∑' scale : ℕ,
        openPeriodicDyadicDissipationHodgeStretchingMass solution t scale) ≤
      (nu / 2) * periodicVorticityDissipation velocity t.1 +
        (27 * totalDyadicHodgeDistanceMoment *
          hodgeDissipationAbsorptionParameter nu / 2) *
            openPeriodicVorticityFourthPowerMass solution t := by
  let parameter := hodgeDissipationAbsorptionParameter nu
  have hparameter : 0 < parameter := hodgeDissipationAbsorptionParameter_pos hnu
  have hsource := tsum_openPeriodicDyadicDissipationHodgeStretchingMass_le
    solution t hparameter
  have hdissipation : 0 ≤ periodicVorticityDissipation velocity t.1 :=
    periodicVorticityDissipation_nonneg_of_openPeriodicSolution solution t
  have hcoefficient := hodgeDissipationCoefficient_le_half_viscosity hnu
  calc
    (∑' scale : ℕ,
        openPeriodicDyadicDissipationHodgeStretchingMass solution t scale) ≤
      27 * totalDyadicHodgeDistanceMoment *
        ((27 * periodicVorticityDissipation velocity t.1 +
          parameter ^ 2 * openPeriodicVorticityFourthPowerMass solution t) /
            (2 * parameter)) := hsource
    _ = (729 * totalDyadicHodgeDistanceMoment / (2 * parameter)) *
          periodicVorticityDissipation velocity t.1 +
        (27 * totalDyadicHodgeDistanceMoment * parameter / 2) *
          openPeriodicVorticityFourthPowerMass solution t := by
      field_simp
      ring
    _ ≤ (nu / 2) * periodicVorticityDissipation velocity t.1 +
        (27 * totalDyadicHodgeDistanceMoment * parameter / 2) *
          openPeriodicVorticityFourthPowerMass solution t := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoefficient hdissipation) le_rfl
    _ = (nu / 2) * periodicVorticityDissipation velocity t.1 +
        (27 * totalDyadicHodgeDistanceMoment *
          hodgeDissipationAbsorptionParameter nu / 2) *
            openPeriodicVorticityFourthPowerMass solution t := by rfl

section Audit

#print axioms openPeriodicVorticityFourthPowerMass_nonneg
#print axioms periodicVorticityDissipation_nonneg_of_openPeriodicSolution
#print axioms openPeriodicVorticityDifferenceInteractionCarrier_nonneg
#print axioms two_mul_parameter_mul_distance_mul_differenceInteraction_le
#print axioms openPeriodicVorticityDifferenceInteractionCarrier_le_dissipation_fourthPower
#print axioms openPeriodicDyadicDissipationHodgeInteractionMass_nonneg
#print axioms openPeriodicDyadicDissipationHodgeInteractionMass_le
#print axioms openPeriodicDyadicDissipationHodgeStretchingMass_le_interaction
#print axioms summable_openPeriodicDyadicDissipationHodgeInteractionMass
#print axioms openPeriodicFullDissipationHodgeInteractionMass_le
#print axioms summable_openPeriodicDyadicDissipationHodgeStretchingMass
#print axioms tsum_openPeriodicDyadicDissipationHodgeStretchingMass_le
#print axioms hodgeDissipationAbsorptionParameter_pos
#print axioms hodgeDissipationCoefficient_le_half_viscosity
#print axioms tsum_openPeriodicDyadicDissipationHodgeStretchingMass_le_absorbed

end Audit

end Soma.Holonics.Millennium.NavierStokesDissipationHodgeInteraction
