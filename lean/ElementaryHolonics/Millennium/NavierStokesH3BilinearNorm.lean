import ElementaryHolonics.Millennium.NavierStokesH3Bilinear

/-!
# Quantitative norms for the periodic scalar H³ algebra

The qualitative Fourier owner already constructs the complete scalar convolution in weighted
`H³`.  This file keeps the same coefficient populations and returns explicit norm bounds.  The
main inputs are the exact reciprocal-weight summability, ℓ2 Cauchy--Schwarz, and the already
constructed ℓ1–ℓ2 Young envelope.

This is one analytic component of a later uniform local-restart construction.  It does not itself
construct a Navier--Stokes solution or identify scalar convolution with a physical-space product.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesH3BilinearNorm

open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Quantitative H³-to-ℓ1 embedding -/

private theorem norm_reciprocalSobolevThreeSqrtReal_sq
    (k : SpatialFrequency) :
    ‖(Real.sqrt (periodicSobolevWeight 3 k))⁻¹‖ ^ 2 =
      (periodicSobolevWeight 3 k)⁻¹ := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), inv_pow,
    Real.sq_sqrt (periodicSobolevWeight_nonneg 3 k)]

/-- The real nonnegative reciprocal square-root weight in ℓ2. -/
def reciprocalSobolevThreeSqrtReal : PeriodicRealFourierL2 :=
  ⟨fun k ↦ (Real.sqrt (periodicSobolevWeight 3 k))⁻¹, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    simpa only [Real.rpow_two, norm_reciprocalSobolevThreeSqrtReal_sq] using
      summable_periodicSobolevWeight_three_inv⟩

/-- The fixed periodic `H³ → ℓ1` embedding constant returned by the reciprocal weight. -/
def periodicH3EmbeddingConstant : ℝ :=
  ‖reciprocalSobolevThreeSqrtReal‖

/-- The exact scalar weighted H³ coefficient norm. -/
def periodicH3CoefficientNorm
    (coeff : PeriodicSobolevCoefficients 3) : ℝ :=
  ‖weightedAbsoluteCoefficient coeff‖

/-- The complete absolute coefficient mass. -/
def coefficientL1Mass
    (coeff : PeriodicSobolevCoefficients 3) : ℝ :=
  ∑' k, ‖coeff.1 k‖

theorem periodicH3EmbeddingConstant_nonneg :
    0 ≤ periodicH3EmbeddingConstant :=
  norm_nonneg _

theorem periodicH3CoefficientNorm_nonneg
    (coeff : PeriodicSobolevCoefficients 3) :
    0 ≤ periodicH3CoefficientNorm coeff :=
  norm_nonneg _

private theorem reciprocal_mul_weighted_eq_coefficientNorm
    (coeff : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    ‖reciprocalSobolevThreeSqrtReal k‖ *
        ‖weightedAbsoluteCoefficient coeff k‖ = ‖coeff.1 k‖ := by
  have hweightPos : 0 < periodicSobolevWeight 3 k := by
    unfold periodicSobolevWeight
    exact pow_pos (by linarith [torusStokesEigenvalue_nonneg k]) 3
  have hsqrtPos : 0 < Real.sqrt (periodicSobolevWeight 3 k) :=
    Real.sqrt_pos.2 hweightPos
  simp only [reciprocalSobolevThreeSqrtReal, weightedAbsoluteCoefficient,
    sobolevThreeAmplitude, Real.norm_eq_abs, abs_inv, abs_of_pos hsqrtPos,
    abs_mul, abs_norm]
  field_simp

/-- Quantitative Cauchy--Schwarz: every scalar periodic H³ population is in ℓ1 with the fixed
reciprocal-weight constant. -/
theorem coefficientL1Mass_le_periodicH3EmbeddingConstant_mul
    (coeff : PeriodicSobolevCoefficients 3) :
    coefficientL1Mass coeff ≤
      periodicH3EmbeddingConstant * periodicH3CoefficientNorm coeff := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hcs := lp.tsum_mul_le_mul_norm' hholder
    reciprocalSobolevThreeSqrtReal (weightedAbsoluteCoefficient coeff)
  calc
    coefficientL1Mass coeff =
        ∑' k, ‖reciprocalSobolevThreeSqrtReal k‖ *
          ‖weightedAbsoluteCoefficient coeff k‖ := by
      unfold coefficientL1Mass
      apply tsum_congr
      intro k
      exact (reciprocal_mul_weighted_eq_coefficientNorm coeff k).symm
    _ ≤ ‖reciprocalSobolevThreeSqrtReal‖ *
        ‖weightedAbsoluteCoefficient coeff‖ := hcs
    _ = periodicH3EmbeddingConstant * periodicH3CoefficientNorm coeff := rfl

/-! ## The quantitative Young envelope -/

/-- The complete weighted product envelope is bounded by the two possible placements of the H³
weight. -/
theorem norm_scalarProductEnvelope_le_l1_h3
    (left right : PeriodicSobolevCoefficients 3) :
    ‖scalarProductEnvelope left right‖ ≤
      8 * (coefficientL1Mass left * periodicH3CoefficientNorm right +
        coefficientL1Mass right * periodicH3CoefficientNorm left) := by
  let first := realL1L2FourierConvolution (absoluteCoefficient left)
    (weightedAbsoluteCoefficient right)
  let second := realL1L2FourierConvolution (absoluteCoefficient right)
    (weightedAbsoluteCoefficient left)
  have hfirst : ‖first‖ ≤
      coefficientL1Mass left * periodicH3CoefficientNorm right := by
    simpa [first, coefficientL1Mass, periodicH3CoefficientNorm,
      absoluteCoefficient] using
      norm_realL1L2FourierConvolution_le
        (summable_norm_absoluteCoefficient left) (weightedAbsoluteCoefficient right)
  have hsecond : ‖second‖ ≤
      coefficientL1Mass right * periodicH3CoefficientNorm left := by
    simpa [second, coefficientL1Mass, periodicH3CoefficientNorm,
      absoluteCoefficient] using
      norm_realL1L2FourierConvolution_le
        (summable_norm_absoluteCoefficient right) (weightedAbsoluteCoefficient left)
  calc
    ‖scalarProductEnvelope left right‖ = 8 * ‖first + second‖ := by
      change ‖(8 : ℝ) • (first + second)‖ = 8 * ‖first + second‖
      rw [norm_smul]
      norm_num
    _ ≤ 8 * (‖first‖ + ‖second‖) := by
      gcongr
      exact norm_add_le first second
    _ ≤ 8 * (coefficientL1Mass left * periodicH3CoefficientNorm right +
        coefficientL1Mass right * periodicH3CoefficientNorm left) := by
      gcongr

/-- After the H³-to-ℓ1 return, the envelope is bilinear in the exact weighted H³ norms with
explicit constant sixteen. -/
theorem norm_scalarProductEnvelope_le_periodicH3
    (left right : PeriodicSobolevCoefficients 3) :
    ‖scalarProductEnvelope left right‖ ≤
      16 * periodicH3EmbeddingConstant * periodicH3CoefficientNorm left *
        periodicH3CoefficientNorm right := by
  have hbase := norm_scalarProductEnvelope_le_l1_h3 left right
  have hleft := coefficientL1Mass_le_periodicH3EmbeddingConstant_mul left
  have hright := coefficientL1Mass_le_periodicH3EmbeddingConstant_mul right
  have hleftNorm := periodicH3CoefficientNorm_nonneg left
  have hrightNorm := periodicH3CoefficientNorm_nonneg right
  have hC := periodicH3EmbeddingConstant_nonneg
  calc
    ‖scalarProductEnvelope left right‖ ≤
        8 * (coefficientL1Mass left * periodicH3CoefficientNorm right +
          coefficientL1Mass right * periodicH3CoefficientNorm left) := hbase
    _ ≤ 8 *
        ((periodicH3EmbeddingConstant * periodicH3CoefficientNorm left) *
            periodicH3CoefficientNorm right +
          (periodicH3EmbeddingConstant * periodicH3CoefficientNorm right) *
            periodicH3CoefficientNorm left) := by
      gcongr
    _ = 16 * periodicH3EmbeddingConstant * periodicH3CoefficientNorm left *
        periodicH3CoefficientNorm right := by ring

/-! ## The scalar H³ product norm -/

private theorem norm_weightedScalarH3Product_apply_le_envelope
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    ‖weightedAbsoluteCoefficient (scalarH3Product left right) k‖ ≤
      ‖scalarProductEnvelope left right k‖ := by
  have hbound :=
    norm_sobolevThreeAmplitude_mul_scalarH3ProductConvolution_le_envelope
      left right k
  have hleftNonneg :
      0 ≤ sobolevThreeAmplitude k *
        ‖scalarH3ProductConvolution left right k‖ :=
    mul_nonneg (sobolevThreeAmplitude_nonneg k) (norm_nonneg _)
  have hrightNonneg := scalarProductEnvelope_nonneg left right k
  simpa only [weightedAbsoluteCoefficient, scalarH3Product,
    Real.norm_eq_abs, abs_of_nonneg hleftNonneg, abs_of_nonneg hrightNonneg,
    norm_mul, Complex.norm_real,
    abs_of_nonneg (sobolevThreeAmplitude_nonneg k), abs_norm] using hbound

/-- The weighted H³ norm of the constructed scalar product is bounded by its complete Young
envelope. -/
theorem periodicH3CoefficientNorm_scalarH3Product_le_envelope
    (left right : PeriodicSobolevCoefficients 3) :
    periodicH3CoefficientNorm (scalarH3Product left right) ≤
      ‖scalarProductEnvelope left right‖ := by
  let product := weightedAbsoluteCoefficient (scalarH3Product left right)
  let envelope := scalarProductEnvelope left right
  have hproductSummable : Summable fun k ↦ ‖product k‖ ^ 2 := by
    have h := (lp.memℓp product).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have henvelopeSummable : Summable fun k ↦ ‖envelope k‖ ^ 2 := by
    have h := (lp.memℓp envelope).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hpoint : ∀ k, ‖product k‖ ^ 2 ≤ ‖envelope k‖ ^ 2 := by
    intro k
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_weightedScalarH3Product_apply_le_envelope left right k) 2
  have hsum : (∑' k, ‖product k‖ ^ 2) ≤ ∑' k, ‖envelope k‖ ^ 2 :=
    hproductSummable.tsum_le_tsum hpoint henvelopeSummable
  have hproductNorm : (∑' k, ‖product k‖ ^ 2) = ‖product‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) product
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  have henvelopeNorm : (∑' k, ‖envelope k‖ ^ 2) = ‖envelope‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) envelope
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  unfold periodicH3CoefficientNorm
  change ‖product‖ ≤ ‖envelope‖
  rw [hproductNorm, henvelopeNorm] at hsum
  nlinarith [norm_nonneg product, norm_nonneg envelope]

/-- Quantitative scalar H³ algebra closure. -/
theorem periodicH3CoefficientNorm_scalarH3Product_le
    (left right : PeriodicSobolevCoefficients 3) :
    periodicH3CoefficientNorm (scalarH3Product left right) ≤
      16 * periodicH3EmbeddingConstant * periodicH3CoefficientNorm left *
        periodicH3CoefficientNorm right :=
  (periodicH3CoefficientNorm_scalarH3Product_le_envelope left right).trans
    (norm_scalarProductEnvelope_le_periodicH3 left right)

section Audit

#print axioms coefficientL1Mass_le_periodicH3EmbeddingConstant_mul
#print axioms norm_scalarProductEnvelope_le_periodicH3
#print axioms periodicH3CoefficientNorm_scalarH3Product_le_envelope
#print axioms periodicH3CoefficientNorm_scalarH3Product_le

end Audit

end Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
