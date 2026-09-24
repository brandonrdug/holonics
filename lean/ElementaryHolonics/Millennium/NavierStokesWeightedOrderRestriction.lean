import ElementaryHolonics.Millennium.NavierStokesWeightedSobolevHilbert

/-!
# Exact restriction from a higher native Sobolev scale

**[proved-derived]** A higher-order native state and its lower-order receiver must denote the
same unweighted Fourier occurrence, not two unrelated `ℓ²` arrays.  This owner proves monotonicity
of the complete inhomogeneous weights, retains the raw coefficient population exactly, and bundles
the high-to-low reweighting as a norm-nonexpanding continuous linear map.

This passage forgets receiver resolution only.  It supplies no higher-order state from lower-order
data and therefore cannot serve as a smoothing theorem.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- The inhomogeneous periodic Sobolev weight is monotone in its addressed natural order. -/
theorem periodicSobolevWeight_mono
    {low high : ℕ} (hlowhigh : low ≤ high) (k : SpatialFrequency) :
    periodicSobolevWeight low k ≤ periodicSobolevWeight high k := by
  unfold periodicSobolevWeight
  exact pow_le_pow_right₀
    (by linarith [torusStokesEigenvalue_nonneg k]) hlowhigh

/-- Retain the raw coefficient population while lowering only its Sobolev receiver. -/
def periodicSobolevCoefficientsRestrict
    (low high : ℕ) (hlowhigh : low ≤ high)
    (coeff : PeriodicSobolevCoefficients high) :
    PeriodicSobolevCoefficients low :=
  ⟨coeff.1, by
    unfold HasPeriodicSobolevCoefficients
    exact Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (periodicSobolevWeight_nonneg low k) (sq_nonneg _))
      (fun k ↦ mul_le_mul_of_nonneg_right
        (periodicSobolevWeight_mono hlowhigh k) (sq_nonneg _)) coeff.2⟩

@[simp]
theorem periodicSobolevCoefficientsRestrict_apply
    (low high : ℕ) (hlowhigh : low ≤ high)
    (coeff : PeriodicSobolevCoefficients high) (k : SpatialFrequency) :
    (periodicSobolevCoefficientsRestrict low high hlowhigh coeff).1 k = coeff.1 k :=
  rfl

/-- Exact native high-to-low reweighting through the common unweighted occurrence. -/
def periodicWeightedSobolevRestrict
    (low high : ℕ) (hlowhigh : low ≤ high)
    (state : PeriodicWeightedSobolev high) :
    PeriodicWeightedSobolev low :=
  coefficientWeightedRealization low
    (periodicSobolevCoefficientsRestrict low high hlowhigh
      (weightedSobolevCoefficients high state))

@[simp]
theorem periodicWeightedSobolevRestrict_apply
    (low high : ℕ) (hlowhigh : low ≤ high)
    (state : PeriodicWeightedSobolev high) (k : SpatialFrequency) :
    periodicWeightedSobolevRestrict low high hlowhigh state k =
      (Real.sqrt (periodicSobolevWeight low k) : ℂ) *
        ((((Real.sqrt (periodicSobolevWeight high k))⁻¹ : ℝ) : ℂ) * state k) :=
  rfl

/-- Unweighting after high-to-low restriction returns literally the same raw coefficient at every
addressed mode. -/
theorem weightedSobolevCoefficients_restrict_apply
    (low high : ℕ) (hlowhigh : low ≤ high)
    (state : PeriodicWeightedSobolev high) (k : SpatialFrequency) :
    (weightedSobolevCoefficients low
      (periodicWeightedSobolevRestrict low high hlowhigh state)).1 k =
        (weightedSobolevCoefficients high state).1 k := by
  have hreconstruct := weightedSobolevCoefficients_coefficientWeightedRealization low
    (periodicSobolevCoefficientsRestrict low high hlowhigh
      (weightedSobolevCoefficients high state))
  exact congrArg (fun coeff : PeriodicSobolevCoefficients low ↦ coeff.1 k) hreconstruct

/-- Lowering the receiver cannot increase the complete native Hilbert norm. -/
theorem norm_periodicWeightedSobolevRestrict_le
    (low high : ℕ) (hlowhigh : low ≤ high)
    (state : PeriodicWeightedSobolev high) :
    ‖periodicWeightedSobolevRestrict low high hlowhigh state‖ ≤ ‖state‖ := by
  let source := weightedSobolevCoefficients high state
  let target := periodicSobolevCoefficientsRestrict low high hlowhigh source
  have htargetNorm := norm_coefficientWeightedRealization_sq_eq low target
  have hsourceNorm := norm_coefficientWeightedRealization_sq_eq high source
  have hsum :
      (∑' k, periodicSobolevWeight low k * ‖target.1 k‖ ^ 2) ≤
        ∑' k, periodicSobolevWeight high k * ‖source.1 k‖ ^ 2 := by
    exact target.2.tsum_le_tsum
      (fun k ↦ mul_le_mul_of_nonneg_right
        (periodicSobolevWeight_mono hlowhigh k) (sq_nonneg _)) source.2
  have hsquare : ‖periodicWeightedSobolevRestrict low high hlowhigh state‖ ^ 2 ≤
      ‖state‖ ^ 2 := by
    change ‖coefficientWeightedRealization low target‖ ^ 2 ≤ ‖state‖ ^ 2
    rw [htargetNorm]
    calc
      (∑' k, periodicSobolevWeight low k * ‖target.1 k‖ ^ 2) ≤
          ∑' k, periodicSobolevWeight high k * ‖source.1 k‖ ^ 2 := hsum
      _ = ‖coefficientWeightedRealization high source‖ ^ 2 := hsourceNorm.symm
      _ = ‖state‖ ^ 2 := by
        rw [coefficientWeightedRealization_weightedSobolevCoefficients]
  nlinarith [norm_nonneg (periodicWeightedSobolevRestrict low high hlowhigh state),
    norm_nonneg state]

/-- High-to-low reweighting as a genuine contraction. -/
def periodicWeightedSobolevRestrictCLM
    (low high : ℕ) (hlowhigh : low ≤ high) :
    PeriodicWeightedSobolev high →L[ℂ] PeriodicWeightedSobolev low :=
  LinearMap.mkContinuous
    { toFun := periodicWeightedSobolevRestrict low high hlowhigh
      map_add' := by
        intro left right
        apply Subtype.ext
        funext k
        simp only [periodicWeightedSobolevRestrict_apply, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := by
        intro scalar state
        apply Subtype.ext
        funext k
        simp only [periodicWeightedSobolevRestrict_apply, lp.coeFn_smul, Pi.smul_apply,
          RingHom.id_apply, smul_eq_mul]
        ring }
    1 (fun state ↦ by
      simpa using norm_periodicWeightedSobolevRestrict_le low high hlowhigh state)

/-- Componentwise restriction retains all three mode addresses. -/
def periodicVectorWeightedSobolevRestrictCLM
    (low high : ℕ) (hlowhigh : low ≤ high) :
    PeriodicVectorWeightedSobolev high →L[ℂ]
      PeriodicVectorWeightedSobolev low :=
  LinearMap.mkContinuous
    { toFun := fun state component ↦
        periodicWeightedSobolevRestrict low high hlowhigh (state component)
      map_add' := by
        intro left right
        funext component
        exact (periodicWeightedSobolevRestrictCLM low high hlowhigh).map_add
          (left component) (right component)
      map_smul' := by
        intro scalar state
        funext component
        exact (periodicWeightedSobolevRestrictCLM low high hlowhigh).map_smul
          scalar (state component) }
    1 (fun state ↦ by
      rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1 * ‖state‖)]
      intro component
      calc
        ‖periodicWeightedSobolevRestrict low high hlowhigh (state component)‖ ≤
            ‖state component‖ :=
          norm_periodicWeightedSobolevRestrict_le low high hlowhigh (state component)
        _ ≤ ‖state‖ := norm_le_pi_norm state component
        _ = 1 * ‖state‖ := by ring)

section Audit

#print axioms periodicSobolevWeight_mono
#print axioms weightedSobolevCoefficients_restrict_apply
#print axioms norm_periodicWeightedSobolevRestrict_le
#print axioms periodicWeightedSobolevRestrictCLM
#print axioms periodicVectorWeightedSobolevRestrictCLM

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
