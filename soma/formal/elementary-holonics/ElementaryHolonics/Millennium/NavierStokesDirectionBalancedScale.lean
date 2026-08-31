import ElementaryHolonics.Millennium.NavierStokesDirectionThresholdBalance
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay

/-!
# The balanced direction current is summable across Hodge scales

**[proved-derived]** The exact threshold balance exposes two apparatus moments.  The high/high
moment contains one torus displacement and inherits inverse-square-root dyadic decay.  The
low-endpoint moment contains no displacement but is uniformly bounded.  Their balanced geometric
mean therefore decays with the fourth root of the dyadic radius, which is still a summable
geometric population.

This closes the infinite-depth spatial scale passage at every strict-interior time for the actual
periodic Navier--Stokes solution.  It does not prove that the returned time-dependent coefficient
is integrable at the maximal terminal time.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDirectionBalancedScale

open Soma.Holonics.CoordinateHaarReceiver
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeRemainingSubsetMasses
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay
open Soma.Holonics.Millennium.NavierStokesHighVorticityDirection
open Soma.Holonics.Millennium.NavierStokesDirectionThresholdBalance
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus

private theorem kernel_threshold_circle_volume_eq :
    @volume UnitAddCircle
        Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment.instMeasureSpaceUnitAddCircle_elementaryHolonics =
      @volume UnitAddCircle
        Soma.Holonics.Millennium.NavierStokesDirectionThresholdBalance.instMeasureSpaceUnitAddCircle_elementaryHolonics := by
  rfl

private theorem kernel_threshold_torus_volume_eq :
    @volume SpatialTorus
        (@MeasureSpace.pi (Fin 3) (Fin.fintype 3) (fun _ ↦ UnitAddCircle)
          (fun _ ↦
            Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment.instMeasureSpaceUnitAddCircle_elementaryHolonics)) =
      @volume SpatialTorus
        (@MeasureSpace.pi (Fin 3) (Fin.fintype 3) (fun _ ↦ UnitAddCircle)
          (fun _ ↦
            Soma.Holonics.Millennium.NavierStokesDirectionThresholdBalance.instMeasureSpaceUnitAddCircle_elementaryHolonics)) := by
  rfl

local instance : MeasureSpace UnitAddCircle :=
  Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment.instMeasureSpaceUnitAddCircle_elementaryHolonics
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The zeroth physical Hodge-kernel moment. -/
def dyadicHodgeJacobianKernelZeroMoment (scale : ℕ) : ℝ :=
  dyadicHodgeJacobianKernelModulusMoment (torusDistancePowerModulus 0) scale

/-- Large-scale zeroth moments are uniformly bounded by the same returned product-Haar carrier. -/
theorem dyadicHodgeJacobianKernelZeroMoment_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    dyadicHodgeJacobianKernelZeroMoment scale ≤
      216 * dyadicHodgeUniformSubsetMassConstant := by
  let penaltyProduct : SpatialTorus → ℝ := fun y ↦
    ∏ axis, oneCircleHaarPenalty (dyadicRadius scale : ℝ) (y axis)
  let constant : ℝ := 27 * dyadicHodgeUniformSubsetMassConstant
  have hconstantNonneg : 0 ≤ constant := by
    dsimp [constant, dyadicHodgeUniformSubsetMassConstant]
    positivity
  have hkernelContinuous : Continuous (fun y : SpatialTorus ↦
      dyadicHodgeJacobianKernelPointMass scale y) := by
    unfold dyadicHodgeJacobianKernelPointMass
    fun_prop
  have hleft : Integrable (fun y : SpatialTorus ↦
      dyadicHodgeJacobianKernelPointMass scale y) :=
    hkernelContinuous.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hright : Integrable (fun y : SpatialTorus ↦
      constant * penaltyProduct y) := by
    apply Continuous.integrable_of_hasCompactSupport
    · apply continuous_const.mul
      dsimp [penaltyProduct]
      apply continuous_finset_prod
      intro axis _haxis
      exact (continuous_oneCircleHaarPenalty _).comp (continuous_apply axis)
    · exact isClosed_closure.isCompact
  have hproduct' : (∫ y : SpatialTorus, penaltyProduct y) ≤ 8 := by
    dsimp [penaltyProduct]
    rw [MeasureTheory.integral_fintype_prod_volume_eq_pow]
    have hradius : 1 ≤ (dyadicRadius scale : ℝ) := by
      exact_mod_cast (Nat.one_le_pow scale 2 (by norm_num))
    have hupper :
        (∫ q : UnitAddCircle,
          oneCircleHaarPenalty (dyadicRadius scale : ℝ) q) ≤ 2 := by
      change (∫ q : UnitAddCircle,
        oneCircleHaarPenalty (dyadicRadius scale : ℝ) q
          ∂AddCircle.haarAddCircle) ≤ 2
      exact integral_oneCircleHaarPenalty_le_two hradius
    have hnonneg :
        0 ≤ ∫ q : UnitAddCircle,
          oneCircleHaarPenalty (dyadicRadius scale : ℝ) q := by
      apply integral_nonneg
      intro q
      unfold oneCircleHaarPenalty scalarHaarPenalty
      positivity
    norm_num [Fintype.card_fin]
    exact (pow_le_pow_left₀ hnonneg hupper 3).trans_eq (by norm_num)
  unfold dyadicHodgeJacobianKernelZeroMoment
    dyadicHodgeJacobianKernelModulusMoment torusDistancePowerModulus
  simp only [ContinuousMap.coe_mk, pow_zero, mul_one]
  calc
    (∫ y : SpatialTorus, dyadicHodgeJacobianKernelPointMass scale y) ≤
        ∫ y : SpatialTorus, constant * penaltyProduct y := by
      apply integral_mono hleft hright
      intro y
      exact dyadicHodgeJacobianKernelPointMass_le_penaltyProduct scale hscale y
    _ = constant * ∫ y : SpatialTorus, penaltyProduct y := by
      rw [integral_const_mul]
    _ ≤ constant * 8 := mul_le_mul_of_nonneg_left hproduct' hconstantNonneg
    _ = 216 * dyadicHodgeUniformSubsetMassConstant := by
      dsimp [constant]
      ring

/-- The exact supremum receiver of one actual torus-vorticity slice. -/
def sliceVorticitySup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ‖torusVorticityEvolution solution t‖

theorem norm_torusVorticityEvolution_le_sliceVorticitySup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    ‖torusVorticityEvolution solution t q‖ ≤ sliceVorticitySup solution t :=
  (torusVorticityEvolution solution t).norm_coe_le_norm q

/-- The high/high source moment is bounded by the square of the exact slice supremum times the
distance-bearing kernel moment. -/
theorem highDirectionKernelMoment_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    highDirectionKernelMoment solution t q scale ≤
      sliceVorticitySup solution t ^ 2 *
        dyadicHodgeJacobianKernelModulusMoment (torusDistancePowerModulus 1) scale := by
  let leftIntegrand : SpatialTorus → ℝ := fun y ↦
    dyadicHodgeJacobianKernelPointMass scale y *
      (‖torusVorticityEvolution solution t q‖ *
        ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0)
  let rightIntegrand : SpatialTorus → ℝ := fun y ↦
    sliceVorticitySup solution t ^ 2 *
      (dyadicHodgeJacobianKernelPointMass scale y * dist y 0)
  have hleft : Integrable leftIntegrand :=
    continuousMap_integrable_on_compact
      { toFun := leftIntegrand
        continuous_toFun := by
          dsimp [leftIntegrand]
          unfold dyadicHodgeJacobianKernelPointMass
          fun_prop }
  have hright : Integrable rightIntegrand :=
    continuousMap_integrable_on_compact
      { toFun := rightIntegrand
        continuous_toFun := by
          dsimp [rightIntegrand]
          unfold dyadicHodgeJacobianKernelPointMass
          fun_prop }
  unfold highDirectionKernelMoment dyadicHodgeJacobianKernelModulusMoment
    torusDistancePowerModulus
  simp only [pow_one]
  calc
    (∫ y : SpatialTorus, leftIntegrand y) ≤
        ∫ y : SpatialTorus, rightIntegrand y := by
      apply integral_mono hleft hright
      intro y
      dsimp [leftIntegrand, rightIntegrand]
      have hq := norm_torusVorticityEvolution_le_sliceVorticitySup solution t q
      have hy := norm_torusVorticityEvolution_le_sliceVorticitySup solution t (q - y)
      have hsup : 0 ≤ sliceVorticitySup solution t := norm_nonneg _
      have hkernel := dyadicHodgeJacobianKernelPointMass_nonneg scale y
      have hdist : 0 ≤ dist y 0 := dist_nonneg
      have hamp :
          ‖torusVorticityEvolution solution t q‖ *
              ‖torusVorticityEvolution solution t (q - y)‖ ≤
            sliceVorticitySup solution t ^ 2 := by
        simpa [pow_two] using
          (mul_le_mul hq hy (norm_nonneg _) hsup)
      calc
        dyadicHodgeJacobianKernelPointMass scale y *
              (‖torusVorticityEvolution solution t q‖ *
                  ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0) ≤
            dyadicHodgeJacobianKernelPointMass scale y *
              (sliceVorticitySup solution t ^ 2 * dist y 0) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hamp hdist) hkernel
        _ = sliceVorticitySup solution t ^ 2 *
              (dyadicHodgeJacobianKernelPointMass scale y * dist y 0) := by ring
    _ = sliceVorticitySup solution t ^ 2 *
        ∫ y : SpatialTorus,
          dyadicHodgeJacobianKernelPointMass scale y * dist y 0 := by
      rw [integral_const_mul]

/-- The low-endpoint population is bounded by twice the slice supremum times the zeroth kernel
moment. -/
theorem lowAmplitudeKernelMoment_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    lowAmplitudeKernelMoment solution t q scale ≤
      (2 * sliceVorticitySup solution t) * dyadicHodgeJacobianKernelZeroMoment scale := by
  let leftIntegrand : SpatialTorus → ℝ := fun y ↦
    dyadicHodgeJacobianKernelPointMass scale y *
      (‖torusVorticityEvolution solution t q‖ +
        ‖torusVorticityEvolution solution t (q - y)‖)
  let rightIntegrand : SpatialTorus → ℝ := fun y ↦
    (2 * sliceVorticitySup solution t) *
      dyadicHodgeJacobianKernelPointMass scale y
  have hleft : Integrable leftIntegrand :=
    continuousMap_integrable_on_compact
      { toFun := leftIntegrand
        continuous_toFun := by
          dsimp [leftIntegrand]
          unfold dyadicHodgeJacobianKernelPointMass
          fun_prop }
  have hright : Integrable rightIntegrand :=
    continuousMap_integrable_on_compact
      { toFun := rightIntegrand
        continuous_toFun := by
          dsimp [rightIntegrand]
          unfold dyadicHodgeJacobianKernelPointMass
          fun_prop }
  unfold lowAmplitudeKernelMoment dyadicHodgeJacobianKernelZeroMoment
    dyadicHodgeJacobianKernelModulusMoment torusDistancePowerModulus
  simp only [ContinuousMap.coe_mk, pow_zero, mul_one]
  calc
    (∫ y : SpatialTorus, leftIntegrand y) ≤
        ∫ y : SpatialTorus, rightIntegrand y := by
      apply integral_mono hleft hright
      intro y
      dsimp [leftIntegrand, rightIntegrand]
      have hq := norm_torusVorticityEvolution_le_sliceVorticitySup solution t q
      have hy := norm_torusVorticityEvolution_le_sliceVorticitySup solution t (q - y)
      have hkernel := dyadicHodgeJacobianKernelPointMass_nonneg scale y
      have hsum :
          ‖torusVorticityEvolution solution t q‖ +
              ‖torusVorticityEvolution solution t (q - y)‖ ≤
            2 * sliceVorticitySup solution t := by
        linarith
      calc
        dyadicHodgeJacobianKernelPointMass scale y *
              (‖torusVorticityEvolution solution t q‖ +
                ‖torusVorticityEvolution solution t (q - y)‖) ≤
            dyadicHodgeJacobianKernelPointMass scale y *
              (2 * sliceVorticitySup solution t) :=
          mul_le_mul_of_nonneg_left hsum hkernel
        _ = (2 * sliceVorticitySup solution t) *
              dyadicHodgeJacobianKernelPointMass scale y := by ring
    _ = (2 * sliceVorticitySup solution t) *
        ∫ y : SpatialTorus, dyadicHodgeJacobianKernelPointMass scale y := by
      rw [integral_const_mul]

/-- The fourth-root dyadic denominator is an exact geometric power. -/
theorem sqrt_sqrt_dyadicRadius (scale : ℕ) :
    Real.sqrt (Real.sqrt (dyadicRadius scale : ℝ)) =
      Real.sqrt (Real.sqrt 2) ^ scale := by
  rw [show (dyadicRadius scale : ℝ) = (2 : ℝ) ^ scale by simp [dyadicRadius],
    sqrt_two_pow]
  induction scale with
  | zero => simp
  | succ scale ih =>
      rw [pow_succ,
        Real.sqrt_mul (pow_nonneg (Real.sqrt_nonneg 2) scale), ih, pow_succ]

/-- Every constant multiple of inverse fourth-root dyadic radius is summable. -/
theorem summable_const_div_sqrt_sqrt_dyadicRadius (constant : ℝ) :
    Summable (fun scale : ℕ ↦
      constant / Real.sqrt (Real.sqrt (dyadicRadius scale : ℝ))) := by
  have honeLtRoot : (1 : ℝ) < Real.sqrt (Real.sqrt 2) := by
    have honeLtSqrtTwo : (1 : ℝ) < Real.sqrt 2 :=
      (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by norm_num)
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by
      simpa using honeLtSqrtTwo)
  have hratio : ‖(Real.sqrt (Real.sqrt 2))⁻¹‖ < (1 : ℝ) := by
    rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact inv_lt_one_of_one_lt₀ honeLtRoot
  have hgeometric : Summable
      (fun scale : ℕ ↦ (Real.sqrt (Real.sqrt 2))⁻¹ ^ scale) :=
    summable_geometric_of_norm_lt_one hratio
  exact (hgeometric.mul_left constant).congr fun scale ↦ by
    rw [sqrt_sqrt_dyadicRadius, div_eq_mul_inv, inv_pow]

theorem summable_sqrt_const_div_sqrt_dyadicRadius
    {constant : ℝ} (hconstant : 0 ≤ constant) :
    Summable (fun scale : ℕ ↦
      Real.sqrt (constant / Real.sqrt (dyadicRadius scale : ℝ))) := by
  have h := summable_const_div_sqrt_sqrt_dyadicRadius (Real.sqrt constant)
  convert h using 1
  funext scale
  rw [Real.sqrt_div hconstant]

/-- The exact balanced geometric-mean current at one receiver and time. -/
def canonicalBalancedScaleCurrent
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) : ℝ :=
  Real.sqrt
      (2 * (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) *
        highDirectionKernelMoment solution t q scale) *
    Real.sqrt (lowAmplitudeKernelMoment solution t q scale)

/-- **Uniform-scale theorem.**  At every strict-interior time and receiver, the exact balanced
direction current is summable across all dyadic Hodge scales. -/
theorem summable_canonicalBalancedScaleCurrent
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    Summable (canonicalBalancedScaleCurrent solution t q) := by
  let omega : ℝ := sliceVorticitySup solution t
  let L : ℝ := openPeriodicCanonicalVorticityLipschitzConstant solution t
  let kernelConstant : ℝ := dyadicHodgeUniformSubsetMassConstant
  let highConstant : ℝ := omega ^ 2 * (405 * kernelConstant / 2)
  let lowConstant : ℝ := (2 * omega) * (216 * kernelConstant)
  let majorant : ℕ → ℝ := fun scale ↦
    Real.sqrt (2 * L *
      (highConstant / Real.sqrt (dyadicRadius (scale + 3) : ℝ))) *
      Real.sqrt lowConstant
  have homega : 0 ≤ omega := norm_nonneg _
  have hL : 0 ≤ L :=
    (openPeriodicCanonicalVorticityLipschitzConstant solution t).coe_nonneg
  have hkernel : 0 ≤ kernelConstant := by
    dsimp [kernelConstant, dyadicHodgeUniformSubsetMassConstant]
    norm_num
  have hhighConstant : 0 ≤ highConstant := by
    dsimp [highConstant]
    positivity
  have hlowConstant : 0 ≤ lowConstant := by
    dsimp [lowConstant]
    positivity
  have hmajorant : Summable majorant := by
    have htwoLhigh : 0 ≤ 2 * L * highConstant :=
      mul_nonneg (mul_nonneg (by norm_num) hL) hhighConstant
    have hsqrt := summable_sqrt_const_div_sqrt_dyadicRadius
      (constant := 2 * L * highConstant) htwoLhigh
    have hshift : Summable (fun scale ↦
        Real.sqrt
          ((2 * L * highConstant) /
            Real.sqrt (dyadicRadius (scale + 3) : ℝ))) :=
      (summable_nat_add_iff 3).2 hsqrt
    have hmul := hshift.mul_right (Real.sqrt lowConstant)
    exact hmul.congr fun scale ↦ by
      dsimp [majorant]
      rw [show 2 * L *
          (highConstant / Real.sqrt (dyadicRadius (scale + 3) : ℝ)) =
        (2 * L * highConstant) /
          Real.sqrt (dyadicRadius (scale + 3) : ℝ) by ring]
  have htail : Summable (fun scale ↦
      canonicalBalancedScaleCurrent solution t q (scale + 3)) := by
    apply Summable.of_nonneg_of_le
      (fun scale ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (fun scale ↦ ?_)
      hmajorant
    have hscale : 3 ≤ scale + 3 := by omega
    have hdistance := dyadicHodgeJacobianKernelDistanceMoment_le
      (scale + 3) hscale
    have hzero := dyadicHodgeJacobianKernelZeroMoment_le (scale + 3) hscale
    have hhigh := highDirectionKernelMoment_le solution t q (scale + 3)
    have hlow := lowAmplitudeKernelMoment_le solution t q (scale + 3)
    have hhighBound :
        highDirectionKernelMoment solution t q (scale + 3) ≤
          highConstant / Real.sqrt (dyadicRadius (scale + 3) : ℝ) := by
      calc
        highDirectionKernelMoment solution t q (scale + 3) ≤
            omega ^ 2 * dyadicHodgeJacobianKernelModulusMoment
              (torusDistancePowerModulus 1) (scale + 3) := hhigh
        _ ≤ omega ^ 2 *
            ((405 * kernelConstant) /
              (2 * Real.sqrt (dyadicRadius (scale + 3) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hdistance (sq_nonneg omega)
        _ = highConstant / Real.sqrt (dyadicRadius (scale + 3) : ℝ) := by
          dsimp [highConstant]
          ring
    have hlowBound :
        lowAmplitudeKernelMoment solution t q (scale + 3) ≤ lowConstant := by
      calc
        lowAmplitudeKernelMoment solution t q (scale + 3) ≤
            (2 * omega) * dyadicHodgeJacobianKernelZeroMoment (scale + 3) := hlow
        _ ≤ (2 * omega) * (216 * kernelConstant) :=
          mul_le_mul_of_nonneg_left hzero (mul_nonneg (by norm_num) homega)
        _ = lowConstant := rfl
    change
      Real.sqrt (2 * L * highDirectionKernelMoment solution t q (scale + 3)) *
          Real.sqrt (lowAmplitudeKernelMoment solution t q (scale + 3)) ≤
        majorant scale
    dsimp [majorant]
    exact mul_le_mul
      (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hhighBound
          (mul_nonneg (by norm_num) hL)))
      (Real.sqrt_le_sqrt hlowBound)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact htail.comp_nat_add

section Audit

#print axioms dyadicHodgeJacobianKernelZeroMoment_le
#print axioms norm_torusVorticityEvolution_le_sliceVorticitySup
#print axioms highDirectionKernelMoment_le
#print axioms lowAmplitudeKernelMoment_le
#print axioms sqrt_sqrt_dyadicRadius
#print axioms summable_const_div_sqrt_sqrt_dyadicRadius
#print axioms summable_sqrt_const_div_sqrt_dyadicRadius
#print axioms summable_canonicalBalancedScaleCurrent

end Audit

end Soma.Holonics.Millennium.NavierStokesDirectionBalancedScale
