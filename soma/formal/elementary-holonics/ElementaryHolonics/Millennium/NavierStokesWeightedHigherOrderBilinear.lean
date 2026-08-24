import ElementaryHolonics.Millennium.NavierStokesWeightedHigherOrderTame
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The higher-order Leray word as a continuous bilinear operator

**[proved-derived]** The complete native arbitrary-order Leray--divergence population already
has an explicit product norm bound.  This owner retains every Fourier mode and proves its exact
additive and scalar transport laws through the infinite convolution.  The result is the genuinely
bundled operator

`H^m →L[ℂ] (H^m →L[ℂ] H^(m-1))`, for every `m ≥ 3`.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderBilinear

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Exact coefficient algebra -/

private theorem weightedSobolevRawCoefficients_injective (order : ℕ) :
    Function.Injective (weightedSobolevRawCoefficients order) := by
  intro left right h
  rw [← coefficientWeightedRealization_weightedSobolevCoefficients order left,
    ← coefficientWeightedRealization_weightedSobolevCoefficients order right]
  congr 1
  apply Subtype.ext
  exact h

private theorem nativeVectorUnderlyingAtOrder_injective (order : ℕ) :
    Function.Injective (nativeVectorUnderlyingAtOrder order) := by
  intro left right h
  funext component
  exact weightedSobolevRawCoefficients_injective order (congrFun h component)

private theorem nativeVectorUnderlyingAtOrder_add
    (order : ℕ)
    (left right : PeriodicVectorWeightedSobolev order) :
    nativeVectorUnderlyingAtOrder order (left + right) =
      nativeVectorUnderlyingAtOrder order left +
        nativeVectorUnderlyingAtOrder order right := by
  funext component
  apply Subtype.ext
  funext k
  simp only [nativeVectorUnderlyingAtOrder, weightedSobolevRawCoefficients_apply,
    Pi.add_apply, lp.coeFn_add]
  ring

private theorem nativeVectorUnderlyingAtOrder_smul
    (order : ℕ) (c : ℂ)
    (state : PeriodicVectorWeightedSobolev order) :
    nativeVectorUnderlyingAtOrder order (c • state) =
      c • nativeVectorUnderlyingAtOrder order state := by
  funext component
  apply Subtype.ext
  funext k
  simp only [nativeVectorUnderlyingAtOrder, weightedSobolevRawCoefficients_apply,
    Pi.smul_apply, lp.coeFn_smul, smul_eq_mul]
  ring

private theorem physicalCoefficient_add
    (order : ℕ) (left right : PeriodicVectorWeightedSobolev order)
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients order ((left + right) component)).1 k =
      (weightedSobolevCoefficients order (left component)).1 k +
        (weightedSobolevCoefficients order (right component)).1 k := by
  change (((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
      ((left component) k + (right component) k) =
    (((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
        (left component) k +
      (((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
        (right component) k
  ring

private theorem physicalCoefficient_smul
    (order : ℕ) (c : ℂ) (state : PeriodicVectorWeightedSobolev order)
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients order ((c • state) component)).1 k =
      c * (weightedSobolevCoefficients order (state component)).1 k := by
  change (((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
      (c * (state component) k) =
    c * ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
      (state component) k)
  ring

private theorem summable_higherOrderConvolutionTerms
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicVectorWeightedSobolev order)
    (input output : Fin 3) (k : SpatialFrequency) :
    Summable fun p ↦
      (weightedSobolevCoefficients order (left input)).1 p *
        (weightedSobolevCoefficients order (right output)).1 (k - p) := by
  apply Summable.of_norm
  have hleft := summable_norm_periodicSobolevCoefficient_of_three_le
    order horder (weightedSobolevCoefficients order (left input))
  have hbound : Summable fun p ↦
      ‖(weightedSobolevCoefficients order (left input)).1 p‖ *
        ‖(weightedSobolevCoefficients order (right output)).1‖ :=
    hleft.mul_right _
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_) hbound
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (weightedSobolevCoefficients order (right output)).1 (k - p))
    (norm_nonneg _)

/-- The unprojected complete divergence mode retained inside the generic native operation. -/
private def higherOrderDivergenceMode
    (order : ℕ)
    (left right : PeriodicVectorWeightedSobolev order)
    (k : SpatialFrequency) : ComplexVector := fun output ↦
  ∑ input : Fin 3,
    (2 * (Real.pi : ℂ) * Complex.I * (k input : ℂ)) *
      (∑' p,
        (weightedSobolevCoefficients order (left input)).1 p *
          (weightedSobolevCoefficients order (right output)).1 (k - p))

private theorem higherOrderDivergenceMode_add_left
    (order : ℕ) (horder : 3 ≤ order)
    (first second transported : PeriodicVectorWeightedSobolev order)
    (k : SpatialFrequency) :
    higherOrderDivergenceMode order (first + second) transported k =
      higherOrderDivergenceMode order first transported k +
        higherOrderDivergenceMode order second transported k := by
  funext output
  simp only [higherOrderDivergenceMode, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro input _
  have hfirst := summable_higherOrderConvolutionTerms
    order horder first transported input output k
  have hsecond := summable_higherOrderConvolutionTerms
    order horder second transported input output k
  have hinner :
      (∑' p,
        (weightedSobolevCoefficients order ((first + second) input)).1 p *
          (weightedSobolevCoefficients order (transported output)).1 (k - p)) =
        (∑' p,
          (weightedSobolevCoefficients order (first input)).1 p *
            (weightedSobolevCoefficients order (transported output)).1 (k - p)) +
        ∑' p,
          (weightedSobolevCoefficients order (second input)).1 p *
            (weightedSobolevCoefficients order (transported output)).1 (k - p) := by
    rw [← hfirst.tsum_add hsecond]
    apply tsum_congr
    intro p
    rw [physicalCoefficient_add]
    ring
  simp only [Pi.add_apply] at hinner
  rw [hinner]
  ring

private theorem higherOrderDivergenceMode_add_right
    (order : ℕ) (horder : 3 ≤ order)
    (advecting first second : PeriodicVectorWeightedSobolev order)
    (k : SpatialFrequency) :
    higherOrderDivergenceMode order advecting (first + second) k =
      higherOrderDivergenceMode order advecting first k +
        higherOrderDivergenceMode order advecting second k := by
  funext output
  simp only [higherOrderDivergenceMode, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro input _
  have hfirst := summable_higherOrderConvolutionTerms
    order horder advecting first input output k
  have hsecond := summable_higherOrderConvolutionTerms
    order horder advecting second input output k
  have hinner :
      (∑' p,
        (weightedSobolevCoefficients order (advecting input)).1 p *
          (weightedSobolevCoefficients order ((first + second) output)).1 (k - p)) =
        (∑' p,
          (weightedSobolevCoefficients order (advecting input)).1 p *
            (weightedSobolevCoefficients order (first output)).1 (k - p)) +
        ∑' p,
          (weightedSobolevCoefficients order (advecting input)).1 p *
            (weightedSobolevCoefficients order (second output)).1 (k - p) := by
    rw [← hfirst.tsum_add hsecond]
    apply tsum_congr
    intro p
    rw [physicalCoefficient_add]
    ring
  simp only [Pi.add_apply] at hinner
  rw [hinner]
  ring

private theorem higherOrderDivergenceMode_smul_left
    (order : ℕ) (horder : 3 ≤ order) (c : ℂ)
    (advecting transported : PeriodicVectorWeightedSobolev order)
    (k : SpatialFrequency) :
    higherOrderDivergenceMode order (c • advecting) transported k =
      c • higherOrderDivergenceMode order advecting transported k := by
  funext output
  simp only [higherOrderDivergenceMode, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  have hterms := summable_higherOrderConvolutionTerms
    order horder advecting transported input output k
  have hinner :
      (∑' p,
        (weightedSobolevCoefficients order ((c • advecting) input)).1 p *
          (weightedSobolevCoefficients order (transported output)).1 (k - p)) =
        c * ∑' p,
          (weightedSobolevCoefficients order (advecting input)).1 p *
            (weightedSobolevCoefficients order (transported output)).1 (k - p) := by
    rw [← hterms.tsum_mul_left c]
    apply tsum_congr
    intro p
    rw [physicalCoefficient_smul]
    ring
  simp only [Pi.smul_apply] at hinner
  rw [hinner]
  ring

private theorem higherOrderDivergenceMode_smul_right
    (order : ℕ) (horder : 3 ≤ order) (c : ℂ)
    (advecting transported : PeriodicVectorWeightedSobolev order)
    (k : SpatialFrequency) :
    higherOrderDivergenceMode order advecting (c • transported) k =
      c • higherOrderDivergenceMode order advecting transported k := by
  funext output
  simp only [higherOrderDivergenceMode, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  have hterms := summable_higherOrderConvolutionTerms
    order horder advecting transported input output k
  have hinner :
      (∑' p,
        (weightedSobolevCoefficients order (advecting input)).1 p *
          (weightedSobolevCoefficients order ((c • transported) output)).1 (k - p)) =
        c * ∑' p,
          (weightedSobolevCoefficients order (advecting input)).1 p *
            (weightedSobolevCoefficients order (transported output)).1 (k - p) := by
    rw [← hterms.tsum_mul_left c]
    apply tsum_congr
    intro p
    rw [physicalCoefficient_smul]
    ring
  simp only [Pi.smul_apply] at hinner
  rw [hinner]
  ring

private theorem lerayProjectMode_add_native
    (k : SpatialFrequency) (left right : ComplexVector) :
    lerayProjectMode k (left + right) =
      lerayProjectMode k left + lerayProjectMode k right := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [lerayProjectMode, if_neg hk, lerayProjectMode, if_neg hk,
      lerayProjectMode, if_neg hk]
    ext output
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      complexDot, dotProduct_add]
    ring

private theorem lerayProjectMode_smul_native
    (c : ℂ) (k : SpatialFrequency) (mode : ComplexVector) :
    lerayProjectMode k (c • mode) = c • lerayProjectMode k mode := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [lerayProjectMode, if_neg hk, lerayProjectMode, if_neg hk]
    ext output
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, complexDot,
      dotProduct_smul]
    ring

private theorem vectorCoefficientAt_higherOrderLerayDivergenceConvolution
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order)
    (k : SpatialFrequency) :
    vectorCoefficientAt
        (nativeVectorUnderlyingAtOrder (order - 1)
          (periodicVectorWeightedLerayDivergenceConvolution
            order horder advecting transported)) k =
      lerayProjectMode k
        (higherOrderDivergenceMode order advecting transported k) := by
  simpa only [higherOrderDivergenceMode] using
    vectorCoefficientAt_periodicVectorWeightedLerayDivergenceConvolution
      order horder advecting transported k

/-! ## Bilinearity on the native carriers -/

theorem periodicVectorWeightedLerayDivergenceConvolution_add_left
    (order : ℕ) (horder : 3 ≤ order)
    (first second transported : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedLerayDivergenceConvolution
        order horder (first + second) transported =
      periodicVectorWeightedLerayDivergenceConvolution order horder first transported +
        periodicVectorWeightedLerayDivergenceConvolution
          order horder second transported := by
  apply nativeVectorUnderlyingAtOrder_injective (order - 1)
  rw [nativeVectorUnderlyingAtOrder_add]
  funext output
  apply Subtype.ext
  funext k
  change vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder (first + second) transported)) k output =
    vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder first transported)) k output +
    vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder second transported)) k output
  rw [vectorCoefficientAt_higherOrderLerayDivergenceConvolution
        order horder (first + second) transported,
    vectorCoefficientAt_higherOrderLerayDivergenceConvolution
      order horder first transported,
    vectorCoefficientAt_higherOrderLerayDivergenceConvolution
      order horder second transported,
    higherOrderDivergenceMode_add_left
      order horder first second transported k,
    lerayProjectMode_add_native]
  rfl

theorem periodicVectorWeightedLerayDivergenceConvolution_add_right
    (order : ℕ) (horder : 3 ≤ order)
    (advecting first second : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedLerayDivergenceConvolution
        order horder advecting (first + second) =
      periodicVectorWeightedLerayDivergenceConvolution order horder advecting first +
        periodicVectorWeightedLerayDivergenceConvolution
          order horder advecting second := by
  apply nativeVectorUnderlyingAtOrder_injective (order - 1)
  rw [nativeVectorUnderlyingAtOrder_add]
  funext output
  apply Subtype.ext
  funext k
  change vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder advecting (first + second))) k output =
    vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder advecting first)) k output +
    vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder advecting second)) k output
  rw [vectorCoefficientAt_higherOrderLerayDivergenceConvolution
        order horder advecting (first + second),
    vectorCoefficientAt_higherOrderLerayDivergenceConvolution
      order horder advecting first,
    vectorCoefficientAt_higherOrderLerayDivergenceConvolution
      order horder advecting second,
    higherOrderDivergenceMode_add_right
      order horder advecting first second k,
    lerayProjectMode_add_native]
  rfl

theorem periodicVectorWeightedLerayDivergenceConvolution_smul_left
    (order : ℕ) (horder : 3 ≤ order) (c : ℂ)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedLerayDivergenceConvolution
        order horder (c • advecting) transported =
      c • periodicVectorWeightedLerayDivergenceConvolution
        order horder advecting transported := by
  apply nativeVectorUnderlyingAtOrder_injective (order - 1)
  rw [nativeVectorUnderlyingAtOrder_smul]
  funext output
  apply Subtype.ext
  funext k
  change vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder (c • advecting) transported)) k output =
    c * vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder advecting transported)) k output
  rw [vectorCoefficientAt_higherOrderLerayDivergenceConvolution
        order horder (c • advecting) transported,
    vectorCoefficientAt_higherOrderLerayDivergenceConvolution
      order horder advecting transported,
    higherOrderDivergenceMode_smul_left
      order horder c advecting transported k,
    lerayProjectMode_smul_native]
  rfl

theorem periodicVectorWeightedLerayDivergenceConvolution_smul_right
    (order : ℕ) (horder : 3 ≤ order) (c : ℂ)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedLerayDivergenceConvolution
        order horder advecting (c • transported) =
      c • periodicVectorWeightedLerayDivergenceConvolution
        order horder advecting transported := by
  apply nativeVectorUnderlyingAtOrder_injective (order - 1)
  rw [nativeVectorUnderlyingAtOrder_smul]
  funext output
  apply Subtype.ext
  funext k
  change vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder advecting (c • transported))) k output =
    c * vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder (order - 1)
        (periodicVectorWeightedLerayDivergenceConvolution
          order horder advecting transported)) k output
  rw [vectorCoefficientAt_higherOrderLerayDivergenceConvolution
        order horder advecting (c • transported),
    vectorCoefficientAt_higherOrderLerayDivergenceConvolution
      order horder advecting transported,
    higherOrderDivergenceMode_smul_right
      order horder c advecting transported k,
    lerayProjectMode_smul_native]
  rfl

/-! ## The bundled continuous bilinear return -/

/-- The complete arbitrary-order operation as a curried bilinear linear map. -/
def periodicVectorWeightedLerayDivergenceConvolutionLinear
    (order : ℕ) (horder : 3 ≤ order) :
    PeriodicVectorWeightedSobolev order →ₗ[ℂ]
      PeriodicVectorWeightedSobolev order →ₗ[ℂ]
        PeriodicVectorWeightedSobolev (order - 1) :=
  LinearMap.mk₂ ℂ
    (periodicVectorWeightedLerayDivergenceConvolution order horder)
    (periodicVectorWeightedLerayDivergenceConvolution_add_left order horder)
    (periodicVectorWeightedLerayDivergenceConvolution_smul_left order horder)
    (periodicVectorWeightedLerayDivergenceConvolution_add_right order horder)
    (periodicVectorWeightedLerayDivergenceConvolution_smul_right order horder)

/-- The complete arbitrary-order operation as a genuinely continuous curried bilinear map. -/
def periodicVectorWeightedLerayDivergenceConvolutionContinuous
    (order : ℕ) (horder : 3 ≤ order) :
    PeriodicVectorWeightedSobolev order →L[ℂ]
      PeriodicVectorWeightedSobolev order →L[ℂ]
        PeriodicVectorWeightedSobolev (order - 1) :=
  (periodicVectorWeightedLerayDivergenceConvolutionLinear order horder).mkContinuous₂
    (36 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant)
    (norm_periodicVectorWeightedLerayDivergenceConvolution_le order horder)

@[simp]
theorem periodicVectorWeightedLerayDivergenceConvolutionContinuous_apply
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedLerayDivergenceConvolutionContinuous
        order horder advecting transported =
      periodicVectorWeightedLerayDivergenceConvolution
        order horder advecting transported :=
  rfl

/-- The bundled operator retains the explicit coarse high-high norm constant. -/
theorem norm_periodicVectorWeightedLerayDivergenceConvolutionContinuous_le
    (order : ℕ) (horder : 3 ≤ order) :
    ‖periodicVectorWeightedLerayDivergenceConvolutionContinuous order horder‖ ≤
      36 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant := by
  exact LinearMap.mkContinuous₂_norm_le
    (periodicVectorWeightedLerayDivergenceConvolutionLinear order horder)
    (mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) order))
      periodicH3EmbeddingConstant_nonneg)
    (norm_periodicVectorWeightedLerayDivergenceConvolution_le order horder)

section Audit

#print axioms periodicVectorWeightedLerayDivergenceConvolution_add_left
#print axioms periodicVectorWeightedLerayDivergenceConvolution_smul_right
#print axioms periodicVectorWeightedLerayDivergenceConvolutionContinuous
#print axioms norm_periodicVectorWeightedLerayDivergenceConvolutionContinuous_le

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderBilinear
