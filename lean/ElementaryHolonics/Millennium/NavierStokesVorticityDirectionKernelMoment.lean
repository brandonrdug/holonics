import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit

/-!
# Spatial modulus transport into the dyadic Hodge kernel moments

**[proved-derived]** The infinite-depth carrier exposed scale summability as the remaining
constitutive law.  This owner factors that law into two independently testable geometric parts:
a receiver-relative modulus for the oriented vorticity difference, and summability of the matching
kernel moments.  It also proves that a scale-uniform mass bound alone cannot imply the required
summability, so the missing localization/decay may not be replaced by the already established
uniform kernel `L1` estimate.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A nonnegative spatial modulus and its receiver-relative cross bound.  The modulus is a
geometric chart on displacement, not a scalar replacement for the source field. -/
structure OpenPeriodicSpatialCrossModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) where
  modulus : C(SpatialTorus, ℝ)
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  modulus_nonneg : ∀ y, 0 ≤ modulus y
  cross_le : ∀ y,
    complexVectorL1
        (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
          (complexTorusVorticitySlice solution t (q - y))) ≤
      constant * modulus y

/-- The physical Hodge kernel moment tested against one declared displacement modulus. -/
def dyadicHodgeJacobianKernelModulusMoment
    (modulus : C(SpatialTorus, ℝ)) (scale : ℕ) : ℝ :=
  ∫ y : SpatialTorus,
    dyadicHodgeJacobianKernelPointMass scale y * modulus y

theorem dyadicHodgeJacobianKernelModulusMoment_nonneg
    (modulus : C(SpatialTorus, ℝ))
    (hmodulus : ∀ y, 0 ≤ modulus y) (scale : ℕ) :
    0 ≤ dyadicHodgeJacobianKernelModulusMoment modulus scale := by
  unfold dyadicHodgeJacobianKernelModulusMoment
  exact integral_nonneg fun y ↦
    mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y) (hmodulus y)

/-- A source direction modulus transports exactly into the matching physical kernel moment. -/
theorem openPeriodicDyadicSpatialCrossCoherenceMass_le_modulusMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (carrier : OpenPeriodicSpatialCrossModulus solution t q) (scale : ℕ) :
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
      carrier.constant *
        dyadicHodgeJacobianKernelModulusMoment carrier.modulus scale := by
  unfold openPeriodicDyadicSpatialCrossCoherenceMass
    dyadicHodgeJacobianKernelModulusMoment
  have hleft : Integrable (fun y : SpatialTorus ↦
      dyadicHodgeJacobianKernelPointMass scale y *
        complexVectorL1
          (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
            (complexTorusVorticitySlice solution t (q - y)))) :=
    continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦
          dyadicHodgeJacobianKernelPointMass scale y *
            complexVectorL1
              (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
                (complexTorusVorticitySlice solution t (q - y)))
        continuous_toFun := by
          unfold dyadicHodgeJacobianKernelPointMass complexVectorL1
            receiverCrossDifference complexCross
          fun_prop }
  have hright : Integrable (fun y : SpatialTorus ↦
      dyadicHodgeJacobianKernelPointMass scale y *
        (carrier.constant * carrier.modulus y)) :=
    continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦
          dyadicHodgeJacobianKernelPointMass scale y *
            (carrier.constant * carrier.modulus y)
        continuous_toFun := by
          unfold dyadicHodgeJacobianKernelPointMass
          fun_prop }
  calc
    (∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelPointMass scale y *
          complexVectorL1
            (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
              (complexTorusVorticitySlice solution t (q - y)))) ≤
      ∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelPointMass scale y *
          (carrier.constant * carrier.modulus y) := by
      apply integral_mono hleft hright
      intro y
      exact mul_le_mul_of_nonneg_left (carrier.cross_le y)
        (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
    _ = ∫ y : SpatialTorus,
        carrier.constant *
          (dyadicHodgeJacobianKernelPointMass scale y * carrier.modulus y) := by
      congr 1
      funext y
      ring
    _ = carrier.constant *
        ∫ y : SpatialTorus,
          dyadicHodgeJacobianKernelPointMass scale y * carrier.modulus y := by
      rw [integral_const_mul]

/-- Summable matching kernel moments are the precise scale-localization law consumed by the full
spatial receiver. -/
def SummableDyadicHodgeJacobianKernelModulusMoments
    (modulus : C(SpatialTorus, ℝ)) : Prop :=
  Summable (dyadicHodgeJacobianKernelModulusMoment modulus)

/-- **Constitutive-law composition.** A geometric source modulus plus summable matching kernel
moments constructs the exact cross-coherence summability carrier required by the infinite-depth
passage. -/
theorem openPeriodicDyadicSpatialCrossCoherenceSummable_of_modulusMoments
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (carrier : OpenPeriodicSpatialCrossModulus solution t q)
    (hmoments : SummableDyadicHodgeJacobianKernelModulusMoments carrier.modulus) :
    OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q := by
  apply Summable.of_nonneg_of_le
    (fun scale ↦ by
      unfold openPeriodicDyadicSpatialCrossCoherenceMass
      exact integral_nonneg fun y ↦
        mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
          (complexVectorL1_nonneg _))
    (fun scale ↦
      openPeriodicDyadicSpatialCrossCoherenceMass_le_modulusMoment
        solution t q carrier scale)
  exact hmoments.mul_left carrier.constant

/-- The full spatial cross mass is controlled by the complete matching kernel-moment population. -/
theorem openPeriodicFullSpatialCrossCoherenceMass_le_modulusMoments
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (carrier : OpenPeriodicSpatialCrossModulus solution t q)
    (hmoments : SummableDyadicHodgeJacobianKernelModulusMoments carrier.modulus) :
    openPeriodicFullSpatialCrossCoherenceMass solution t q ≤
      carrier.constant *
        ∑' scale : ℕ,
          dyadicHodgeJacobianKernelModulusMoment carrier.modulus scale := by
  unfold openPeriodicFullSpatialCrossCoherenceMass
  have hcross :=
    openPeriodicDyadicSpatialCrossCoherenceSummable_of_modulusMoments
      solution t q carrier hmoments
  calc
    (∑' scale : ℕ,
        openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale) ≤
      ∑' scale : ℕ,
        carrier.constant *
          dyadicHodgeJacobianKernelModulusMoment carrier.modulus scale :=
      hcross.tsum_le_tsum
        (fun scale ↦ openPeriodicDyadicSpatialCrossCoherenceMass_le_modulusMoment
          solution t q carrier scale)
        (hmoments.mul_left carrier.constant)
    _ = carrier.constant *
        ∑' scale : ℕ,
          dyadicHodgeJacobianKernelModulusMoment carrier.modulus scale := by
      rw [tsum_mul_left]

/-- Integer-power torus distance is one exact geometric modulus family.  Fractional Hölder
moduli can enter through the general continuous-modulus carrier above without changing the scale
composition theorem. -/
def torusDistancePowerModulus (power : ℕ) : C(SpatialTorus, ℝ) where
  toFun := fun y ↦ dist y 0 ^ power
  continuous_toFun := (continuous_id.dist continuous_const).pow power

theorem torusDistancePowerModulus_nonneg (power : ℕ) (y : SpatialTorus) :
    0 ≤ torusDistancePowerModulus power y := by
  unfold torusDistancePowerModulus
  exact pow_nonneg (dist_nonneg : 0 ≤ dist y 0) power

/-- A pointwise integer-power direction law constructs the general modulus carrier. -/
def openPeriodicTorusDistancePowerCrossModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (constant : ℝ) (power : ℕ)
    (hconstant : 0 ≤ constant)
    (hcross : ∀ y,
      complexVectorL1
          (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
            (complexTorusVorticitySlice solution t (q - y))) ≤
        constant * dist y 0 ^ power) :
    OpenPeriodicSpatialCrossModulus solution t q where
  modulus := torusDistancePowerModulus power
  constant := constant
  constant_nonneg := hconstant
  modulus_nonneg := torusDistancePowerModulus_nonneg power
  cross_le := by
    intro y
    simpa [torusDistancePowerModulus] using hcross y

/-- **Receiver-insufficiency counterexample.** Nonnegative scale masses can be uniformly bounded
without being summable.  Therefore the completed uniform kernel `L1` law cannot by itself inhabit
the infinite-depth spatial cross receiver; a genuine decaying moment/localization law is required.
-/
theorem uniform_nonnegative_scale_bound_does_not_imply_summable :
    ∃ mass : ℕ → ℝ,
      (∀ scale, 0 ≤ mass scale ∧ mass scale ≤ 1) ∧ ¬ Summable mass := by
  refine ⟨fun _scale ↦ 1, ?_, ?_⟩
  · intro scale
    exact ⟨by norm_num, by norm_num⟩
  · simpa only [summable_const_iff] using (one_ne_zero : (1 : ℝ) ≠ 0)

section Audit

#print axioms dyadicHodgeJacobianKernelModulusMoment_nonneg
#print axioms openPeriodicDyadicSpatialCrossCoherenceMass_le_modulusMoment
#print axioms openPeriodicDyadicSpatialCrossCoherenceSummable_of_modulusMoments
#print axioms openPeriodicFullSpatialCrossCoherenceMass_le_modulusMoments
#print axioms torusDistancePowerModulus_nonneg
#print axioms uniform_nonnegative_scale_bound_does_not_imply_summable

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
