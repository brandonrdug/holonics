import ElementaryHolonics.Foundation.CoordinateHaarMomentReceiver
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeRemainingSubsetMasses
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelMoment

/-!
# Dyadic Hodge distance-moment decay

**[proved-derived]** The eight returned Abel faces localize every large-scale Hodge-kernel entry
by the coordinate Haar penalty.  Retaining the torus displacement through that product receiver
returns inverse-square-root dyadic decay.  The resulting physical kernel moments are summable
across every dyadic scale, including the finite low-scale prefix.

This closes the apparatus-side half of the spatial vorticity-direction constitutive law.  The
remaining source-side edge is the construction of the corresponding distance modulus for the
oriented vorticity cross difference.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay

open Soma.Holonics.CoordinateHaarReceiver
open Soma.Holonics.CoordinateHaarMomentReceiver
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarReceiver
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeRemainingSubsetMasses
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The twenty-seven Hodge entries inherit the same localized product receiver. -/
theorem dyadicHodgeJacobianKernelPointMass_le_penaltyProduct
    (scale : ℕ) (hscale : 3 ≤ scale) (y : SpatialTorus) :
    dyadicHodgeJacobianKernelPointMass scale y ≤
      27 * dyadicHodgeUniformSubsetMassConstant *
        ∏ axis, oneCircleHaarPenalty (dyadicRadius scale : ℝ) (y axis) := by
  unfold dyadicHodgeJacobianKernelPointMass
  calc
    (∑ component : Fin 3, ∑ coordinate : Fin 3, ∑ input : Fin 3,
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖) ≤
      ∑ _component : Fin 3, ∑ _coordinate : Fin 3, ∑ _input : Fin 3,
        dyadicHodgeUniformSubsetMassConstant *
          ∏ axis, oneCircleHaarPenalty (dyadicRadius scale : ℝ) (y axis) := by
      apply Finset.sum_le_sum
      intro component _hcomponent
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      apply Finset.sum_le_sum
      intro input _hinput
      exact norm_dyadicHodgeJacobianKernelEntry_le_penaltyProduct
        scale component coordinate input
          (uniformLargeScaleDyadicHodgeSubsetMassReturn_inhabited.2
            scale hscale component coordinate input) y
    _ = 27 * dyadicHodgeUniformSubsetMassConstant *
        ∏ axis, oneCircleHaarPenalty (dyadicRadius scale : ℝ) (y axis) := by
      simp
      ring

/-- Every large-scale physical distance moment decays by the exact product-Haar return. -/
theorem dyadicHodgeJacobianKernelDistanceMoment_le
    (scale : ℕ) (hscale : 3 ≤ scale) :
    dyadicHodgeJacobianKernelModulusMoment (torusDistancePowerModulus 1) scale ≤
      (405 * dyadicHodgeUniformSubsetMassConstant) /
        (2 * Real.sqrt (dyadicRadius scale : ℝ)) := by
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
      dyadicHodgeJacobianKernelPointMass scale y * dist y 0) :=
    (hkernelContinuous.mul
      (continuous_id.dist continuous_const)).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hright : Integrable (fun y : SpatialTorus ↦
      constant * (dist y 0 * penaltyProduct y)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · apply continuous_const.mul
      apply (continuous_id.dist continuous_const).mul
      dsimp [penaltyProduct]
      apply continuous_finset_prod
      intro axis _haxis
      exact (continuous_oneCircleHaarPenalty _).comp (continuous_apply axis)
    · exact isClosed_closure.isCompact
  have hproduct := integral_threeTorus_dist_mul_penaltyProduct_le
    (show 1 ≤ (dyadicRadius scale : ℝ) by
      exact_mod_cast (Nat.one_le_pow scale 2 (by norm_num)))
  unfold dyadicHodgeJacobianKernelModulusMoment torusDistancePowerModulus
  simp only [pow_one]
  calc
    (∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelPointMass scale y * dist y 0) ≤
      ∫ y : SpatialTorus, constant * (dist y 0 * penaltyProduct y) := by
      apply integral_mono hleft hright
      intro y
      calc
        dyadicHodgeJacobianKernelPointMass scale y * dist y 0 ≤
            (constant * penaltyProduct y) * dist y 0 :=
          mul_le_mul_of_nonneg_right
            (dyadicHodgeJacobianKernelPointMass_le_penaltyProduct scale hscale y)
            dist_nonneg
        _ = constant * (dist y 0 * penaltyProduct y) := by ring
    _ = constant * ∫ y : SpatialTorus, dist y 0 * penaltyProduct y := by
      rw [integral_const_mul]
    _ ≤ constant * (15 / (2 * Real.sqrt (dyadicRadius scale : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hproduct hconstantNonneg
    _ = (405 * dyadicHodgeUniformSubsetMassConstant) /
        (2 * Real.sqrt (dyadicRadius scale : ℝ)) := by
      dsimp [constant]
      ring

/-- Square root commutes with the exact positive dyadic power. -/
theorem sqrt_two_pow (scale : ℕ) :
    Real.sqrt ((2 : ℝ) ^ scale) = Real.sqrt 2 ^ scale := by
  induction scale with
  | zero => simp
  | succ scale ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- Every constant multiple of the inverse square-root dyadic radius is summable. -/
theorem summable_const_div_sqrt_dyadicRadius (constant : ℝ) :
    Summable (fun scale : ℕ ↦
      constant / Real.sqrt (dyadicRadius scale : ℝ)) := by
  have honeLtRoot : (1 : ℝ) < Real.sqrt 2 := by
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by norm_num)
  have hratio : ‖(Real.sqrt 2)⁻¹‖ < (1 : ℝ) := by
    rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg 2))]
    exact inv_lt_one_of_one_lt₀ honeLtRoot
  have hgeometric : Summable (fun scale : ℕ ↦ (Real.sqrt 2)⁻¹ ^ scale) :=
    summable_geometric_of_norm_lt_one hratio
  exact (hgeometric.mul_left constant).congr fun scale ↦ by
    rw [show (dyadicRadius scale : ℝ) = (2 : ℝ) ^ scale by
      simp [dyadicRadius], sqrt_two_pow, div_eq_mul_inv, inv_pow]

/-- **Uniform-scale theorem.** The actual distance-weighted dyadic Hodge-kernel moments are
summable across all scales.  The first three scales form a retained finite prefix; every later
scale is dominated by the geometric Haar localization return. -/
theorem summableDyadicHodgeJacobianKernelDistanceMoments_inhabited :
    SummableDyadicHodgeJacobianKernelModulusMoments
      (torusDistancePowerModulus 1) := by
  let majorant : ℕ → ℝ := fun scale ↦
    (405 * dyadicHodgeUniformSubsetMassConstant) /
      (2 * Real.sqrt (dyadicRadius scale : ℝ))
  have hmajorant : Summable majorant := by
    have h := summable_const_div_sqrt_dyadicRadius
      ((405 * dyadicHodgeUniformSubsetMassConstant) / 2)
    convert h using 1
    funext scale
    dsimp [majorant]
    ring
  have htailMajorant : Summable (fun scale ↦ majorant (scale + 3)) :=
    (summable_nat_add_iff 3).2 hmajorant
  have htail : Summable (fun scale ↦
      dyadicHodgeJacobianKernelModulusMoment
        (torusDistancePowerModulus 1) (scale + 3)) := by
    apply Summable.of_nonneg_of_le
      (fun scale ↦ dyadicHodgeJacobianKernelModulusMoment_nonneg
        (torusDistancePowerModulus 1) (torusDistancePowerModulus_nonneg 1) (scale + 3))
      (fun scale ↦ by
        exact dyadicHodgeJacobianKernelDistanceMoment_le (scale + 3) (by omega))
      htailMajorant
  exact htail.comp_nat_add

/-- Once the source returns a linear torus-distance law, the now-inhabited kernel moments
construct the exact infinite-depth spatial cross-coherence carrier.  No additional apparatus-side
summability hypothesis remains. -/
theorem openPeriodicDyadicSpatialCrossCoherenceSummable_of_distanceCross
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (constant : ℝ)
    (hconstant : 0 ≤ constant)
    (hcross : ∀ y,
      complexVectorL1
          (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
            (complexTorusVorticitySlice solution t (q - y))) ≤
        constant * dist y 0) :
    OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q := by
  let carrier := openPeriodicTorusDistancePowerCrossModulus
    solution t q constant 1 hconstant (by
      intro y
      simpa using hcross y)
  exact openPeriodicDyadicSpatialCrossCoherenceSummable_of_modulusMoments
    solution t q carrier
      summableDyadicHodgeJacobianKernelDistanceMoments_inhabited

section Audit

#print axioms dyadicHodgeJacobianKernelPointMass_le_penaltyProduct
#print axioms dyadicHodgeJacobianKernelDistanceMoment_le
#print axioms sqrt_two_pow
#print axioms summable_const_div_sqrt_dyadicRadius
#print axioms summableDyadicHodgeJacobianKernelDistanceMoments_inhabited
#print axioms openPeriodicDyadicSpatialCrossCoherenceSummable_of_distanceCross

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay
