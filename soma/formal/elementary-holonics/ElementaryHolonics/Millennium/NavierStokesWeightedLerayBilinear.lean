import ElementaryHolonics.Millennium.NavierStokesWeightedSobolevHilbert
import ElementaryHolonics.Millennium.NavierStokesH3LerayBilinearNorm
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The Leray bilinear passage on the complete weighted Sobolev carrier

The earlier Fourier owner constructs the exact complete-lattice passage

`P div (u ⊗ v) : H³ × H³ → H²`

and proves a quantitative estimate in Euclidean sums of coefficient Sobolev norms.  The complete
weighted carrier is instead a product of native weighted `ℓ2` spaces, equipped with Mathlib's
finite-product supremum norm.  This owner proves the two norm changes explicitly, transports the
coefficient passage through the exact weight/unweight equivalence, and bundles the result as a
continuous bilinear map.

The constant `23328 = 2592 · 3 · 3` is deliberately coarse: each Euclidean three-component
input norm is bounded by three times its native product norm.  No divergence-free or Fourier
reality condition is imposed on the domain; those are later closed subspaces.  The output itself
retains the exact modewise Leray divergence constraint.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear

open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Exact scalar norm transport -/

/-- The older real-envelope `H³` norm is exactly the norm of its native complex weighted
realization. -/
theorem periodicH3CoefficientNorm_eq_nativeNorm
    (coeff : PeriodicSobolevCoefficients 3) :
    periodicH3CoefficientNorm coeff =
      ‖coefficientWeightedRealization 3 coeff‖ := by
  have hleft := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (weightedAbsoluteCoefficient coeff)
  have hleftSquare : periodicH3CoefficientNorm coeff ^ 2 =
      ∑' k, periodicSobolevWeight 3 k * ‖coeff.1 k‖ ^ 2 := by
    rw [periodicH3CoefficientNorm]
    calc
      ‖weightedAbsoluteCoefficient coeff‖ ^ 2 =
          ∑' k, ‖weightedAbsoluteCoefficient coeff k‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hleft
      _ = ∑' k, periodicSobolevWeight 3 k * ‖coeff.1 k‖ ^ 2 := by
        apply tsum_congr
        intro k
        simp only [weightedAbsoluteCoefficient, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sobolevThreeAmplitude_nonneg k) (norm_nonneg _)),
          mul_pow, sobolevThreeAmplitude_sq]
  have hrightSquare := norm_coefficientWeightedRealization_sq_eq 3 coeff
  nlinarith [periodicH3CoefficientNorm_nonneg coeff,
    norm_nonneg (coefficientWeightedRealization 3 coeff)]

/-- The older real-envelope `H²` norm is exactly the norm of its native complex weighted
realization. -/
theorem periodicH2CoefficientNorm_eq_nativeNorm
    (coeff : PeriodicSobolevCoefficients 2) :
    periodicH2CoefficientNorm coeff =
      ‖coefficientWeightedRealization 2 coeff‖ := by
  have hleft := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (weightedAbsoluteCoefficientTwo coeff)
  have hleftSquare : periodicH2CoefficientNorm coeff ^ 2 =
      ∑' k, periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2 := by
    rw [periodicH2CoefficientNorm]
    calc
      ‖weightedAbsoluteCoefficientTwo coeff‖ ^ 2 =
          ∑' k, ‖weightedAbsoluteCoefficientTwo coeff k‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hleft
      _ = ∑' k, periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2 := by
        apply tsum_congr
        intro k
        simp only [weightedAbsoluteCoefficientTwo, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sobolevTwoAmplitude_nonneg k) (norm_nonneg _)),
          mul_pow, sobolevTwoAmplitude_sq]
  have hrightSquare := norm_coefficientWeightedRealization_sq_eq 2 coeff
  nlinarith [periodicH2CoefficientNorm_nonneg coeff,
    norm_nonneg (coefficientWeightedRealization 2 coeff)]

/-- Unweighting a native order-three state preserves its norm exactly. -/
theorem periodicH3CoefficientNorm_weightedSobolevCoefficients
    (state : PeriodicWeightedSobolev 3) :
    periodicH3CoefficientNorm (weightedSobolevCoefficients 3 state) = ‖state‖ := by
  rw [periodicH3CoefficientNorm_eq_nativeNorm,
    coefficientWeightedRealization_weightedSobolevCoefficients]

/-- Unweighting a native order-two state preserves its norm exactly. -/
theorem periodicH2CoefficientNorm_weightedSobolevCoefficients
    (state : PeriodicWeightedSobolev 2) :
    periodicH2CoefficientNorm (weightedSobolevCoefficients 2 state) = ‖state‖ := by
  rw [periodicH2CoefficientNorm_eq_nativeNorm,
    coefficientWeightedRealization_weightedSobolevCoefficients]

/-! ## The transported coefficient passage -/

/-- Componentwise unweighting from the native vector carrier into the older coefficient
realization. -/
def unweightedVectorThree (state : PeriodicVectorWeightedSobolev 3) :
    PeriodicVectorSobolevThree :=
  fun component ↦ weightedSobolevCoefficients 3 (state component)

@[simp]
theorem unweightedVectorThree_coefficient
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) :
    (unweightedVectorThree state component).1 k =
      (((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) * state component k :=
  rfl

/-- Unweight every input coefficient, apply the exact complete-lattice Leray divergence
convolution, and weight the returned `H²` population back into the complete native carrier. -/
def weightedLerayDivergenceConvolution
    (advecting transported : PeriodicVectorWeightedSobolev 3) :
    PeriodicVectorWeightedSobolev 2 :=
  fun output ↦ coefficientWeightedRealization 2
    (lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree advecting) (unweightedVectorThree transported) output)

@[simp]
theorem weightedLerayDivergenceConvolution_apply
    (advecting transported : PeriodicVectorWeightedSobolev 3) (output : Fin 3) :
    weightedLerayDivergenceConvolution advecting transported output =
      coefficientWeightedRealization 2
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree advecting) (unweightedVectorThree transported) output) :=
  rfl

/-- Exact addressed coefficient law after transport to the native weighted carrier. -/
theorem weightedLerayDivergenceConvolution_coefficient
    (advecting transported : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    weightedLerayDivergenceConvolution advecting transported output k =
      (Real.sqrt (periodicSobolevWeight 2 k) : ℂ) *
        lerayProjectMode k
          (fun component ↦
            (h3DivergenceConvolution
              (unweightedVectorThree advecting)
              (unweightedVectorThree transported) component).1 k) output := by
  rw [weightedLerayDivergenceConvolution_apply,
    coefficientWeightedRealization_apply]
  congr 1

private theorem lerayProjectMode_add
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

private theorem lerayProjectMode_smul
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

private theorem summable_scalarConvolutionTerms
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    Summable fun p ↦ left.1 p * right.1 (k - p) := by
  apply Summable.of_norm
  have hleft := summable_norm_periodicSobolevThreeCoefficient left
  have hbound : Summable fun p ↦ ‖left.1 p‖ * ‖right.1‖ :=
    hleft.mul_right ‖right.1‖
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_) hbound
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) right.1 (k - p))
    (norm_nonneg _)

private theorem h3DivergenceConvolution_unweighted_add_left_coefficient
    (first second transported : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution
      (unweightedVectorThree (first + second))
      (unweightedVectorThree transported) output).1 k =
      (h3DivergenceConvolution
        (unweightedVectorThree first) (unweightedVectorThree transported) output).1 k +
      (h3DivergenceConvolution
        (unweightedVectorThree second) (unweightedVectorThree transported) output).1 k := by
  rw [h3DivergenceConvolution_apply, h3DivergenceConvolution_apply,
    h3DivergenceConvolution_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  let right := (unweightedVectorThree transported output)
  let leftFirst := (unweightedVectorThree first coordinate)
  let leftSecond := (unweightedVectorThree second coordinate)
  have hfirst := summable_scalarConvolutionTerms leftFirst right k
  have hsecond := summable_scalarConvolutionTerms leftSecond right k
  have hinner :
      (∑' p, (unweightedVectorThree (first + second) coordinate).1 p *
        (unweightedVectorThree transported output).1 (k - p)) =
        (∑' p, (unweightedVectorThree first coordinate).1 p *
          (unweightedVectorThree transported output).1 (k - p)) +
        ∑' p, (unweightedVectorThree second coordinate).1 p *
          (unweightedVectorThree transported output).1 (k - p) := by
    rw [← hfirst.tsum_add hsecond]
    apply tsum_congr
    intro p
    simp only [unweightedVectorThree_coefficient, Pi.add_apply, lp.coeFn_add]
    dsimp [leftFirst, leftSecond, right]
    ring
  rw [hinner]
  ring

private theorem h3DivergenceConvolution_unweighted_add_right_coefficient
    (advecting first second : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution
      (unweightedVectorThree advecting)
      (unweightedVectorThree (first + second)) output).1 k =
      (h3DivergenceConvolution
        (unweightedVectorThree advecting) (unweightedVectorThree first) output).1 k +
      (h3DivergenceConvolution
        (unweightedVectorThree advecting) (unweightedVectorThree second) output).1 k := by
  rw [h3DivergenceConvolution_apply, h3DivergenceConvolution_apply,
    h3DivergenceConvolution_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  let left := (unweightedVectorThree advecting coordinate)
  let rightFirst := (unweightedVectorThree first output)
  let rightSecond := (unweightedVectorThree second output)
  have hfirst := summable_scalarConvolutionTerms left rightFirst k
  have hsecond := summable_scalarConvolutionTerms left rightSecond k
  have hinner :
      (∑' p, (unweightedVectorThree advecting coordinate).1 p *
        (unweightedVectorThree (first + second) output).1 (k - p)) =
        (∑' p, (unweightedVectorThree advecting coordinate).1 p *
          (unweightedVectorThree first output).1 (k - p)) +
        ∑' p, (unweightedVectorThree advecting coordinate).1 p *
          (unweightedVectorThree second output).1 (k - p) := by
    rw [← hfirst.tsum_add hsecond]
    apply tsum_congr
    intro p
    simp only [unweightedVectorThree_coefficient, Pi.add_apply, lp.coeFn_add]
    dsimp [left, rightFirst, rightSecond]
    ring
  rw [hinner]
  ring

private theorem h3DivergenceConvolution_unweighted_smul_left_coefficient
    (c : ℂ) (advecting transported : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution
      (unweightedVectorThree (c • advecting))
      (unweightedVectorThree transported) output).1 k =
      c * (h3DivergenceConvolution
        (unweightedVectorThree advecting)
        (unweightedVectorThree transported) output).1 k := by
  rw [h3DivergenceConvolution_apply, h3DivergenceConvolution_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  let left := unweightedVectorThree advecting coordinate
  let right := unweightedVectorThree transported output
  have hterms := summable_scalarConvolutionTerms left right k
  have hinner :
      (∑' p, (unweightedVectorThree (c • advecting) coordinate).1 p *
        (unweightedVectorThree transported output).1 (k - p)) =
        c * ∑' p, (unweightedVectorThree advecting coordinate).1 p *
          (unweightedVectorThree transported output).1 (k - p) := by
    rw [← hterms.tsum_mul_left c]
    apply tsum_congr
    intro p
    simp only [unweightedVectorThree_coefficient, Pi.smul_apply, lp.coeFn_smul,
      smul_eq_mul]
    dsimp [left, right]
    ring
  rw [hinner]
  ring

private theorem h3DivergenceConvolution_unweighted_smul_right_coefficient
    (c : ℂ) (advecting transported : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution
      (unweightedVectorThree advecting)
      (unweightedVectorThree (c • transported)) output).1 k =
      c * (h3DivergenceConvolution
        (unweightedVectorThree advecting)
        (unweightedVectorThree transported) output).1 k := by
  rw [h3DivergenceConvolution_apply, h3DivergenceConvolution_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  let left := unweightedVectorThree advecting coordinate
  let right := unweightedVectorThree transported output
  have hterms := summable_scalarConvolutionTerms left right k
  have hinner :
      (∑' p, (unweightedVectorThree advecting coordinate).1 p *
        (unweightedVectorThree (c • transported) output).1 (k - p)) =
        c * ∑' p, (unweightedVectorThree advecting coordinate).1 p *
          (unweightedVectorThree transported output).1 (k - p) := by
    rw [← hterms.tsum_mul_left c]
    apply tsum_congr
    intro p
    simp only [unweightedVectorThree_coefficient, Pi.smul_apply, lp.coeFn_smul,
      smul_eq_mul]
    dsimp [left, right]
    ring
  rw [hinner]
  ring

private theorem periodicVectorH3CoefficientNorm_le_component_sum
    (state : PeriodicVectorSobolevThree) :
    periodicVectorH3CoefficientNorm state ≤
      ∑ component : Fin 3, periodicH3CoefficientNorm (state component) := by
  unfold periodicVectorH3CoefficientNorm
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun component _ ↦
      periodicH3CoefficientNorm_nonneg (state component)
  · exact Finset.sum_sq_le_sq_sum_of_nonneg fun component _ ↦
      periodicH3CoefficientNorm_nonneg (state component)

/-- Replacing the Euclidean direct-sum coefficient norm by the native finite-product norm costs
at most the explicit factor three. -/
theorem periodicVectorH3CoefficientNorm_unweighted_le
    (state : PeriodicVectorWeightedSobolev 3) :
    periodicVectorH3CoefficientNorm
        (fun component ↦ weightedSobolevCoefficients 3 (state component)) ≤
      3 * ‖state‖ := by
  calc
    periodicVectorH3CoefficientNorm
        (fun component ↦ weightedSobolevCoefficients 3 (state component)) ≤
        ∑ component : Fin 3,
          periodicH3CoefficientNorm (weightedSobolevCoefficients 3 (state component)) :=
      periodicVectorH3CoefficientNorm_le_component_sum _
    _ = ∑ component : Fin 3, ‖state component‖ := by
      apply Finset.sum_congr rfl
      intro component _
      exact periodicH3CoefficientNorm_weightedSobolevCoefficients (state component)
    _ ≤ ∑ _component : Fin 3, ‖state‖ := by
      apply Finset.sum_le_sum
      intro component _
      exact norm_le_pi_norm state component
    _ = 3 * ‖state‖ := by simp

/-- The native output product norm is no larger than the older Euclidean direct-sum `H²` norm. -/
theorem norm_weightedVectorRealization_le_periodicVectorH2CoefficientNorm
    (state : PeriodicVectorSobolevTwo) :
    ‖fun component ↦ coefficientWeightedRealization 2 (state component)‖ ≤
      periodicVectorH2CoefficientNorm state := by
  rw [pi_norm_le_iff_of_nonempty]
  intro component
  rw [← periodicH2CoefficientNorm_eq_nativeNorm]
  exact periodicH2CoefficientNorm_component_le_vector state component

/-- Quantitative native-carrier bound for the exact Leray-projected divergence convolution. -/
theorem norm_weightedLerayDivergenceConvolution_le
    (advecting transported : PeriodicVectorWeightedSobolev 3) :
    ‖weightedLerayDivergenceConvolution advecting transported‖ ≤
      (23328 * periodicH3EmbeddingConstant) * ‖advecting‖ * ‖transported‖ := by
  let oldAdvecting : PeriodicVectorSobolevThree :=
    fun component ↦ weightedSobolevCoefficients 3 (advecting component)
  let oldTransported : PeriodicVectorSobolevThree :=
    fun component ↦ weightedSobolevCoefficients 3 (transported component)
  have hbase :=
    periodicVectorH2CoefficientNorm_lerayProjectedH3DivergenceConvolution_le
      oldAdvecting oldTransported
  have hu := periodicVectorH3CoefficientNorm_unweighted_le advecting
  have hv := periodicVectorH3CoefficientNorm_unweighted_le transported
  have hC := periodicH3EmbeddingConstant_nonneg
  have hu0 := norm_nonneg advecting
  have hv0 := norm_nonneg transported
  have holdU0 := periodicVectorH3CoefficientNorm_nonneg oldAdvecting
  have holdV0 := periodicVectorH3CoefficientNorm_nonneg oldTransported
  calc
    ‖weightedLerayDivergenceConvolution advecting transported‖ ≤
        periodicVectorH2CoefficientNorm
          (lerayProjectedH3DivergenceConvolution oldAdvecting oldTransported) :=
      norm_weightedVectorRealization_le_periodicVectorH2CoefficientNorm _
    _ ≤ 2592 * periodicH3EmbeddingConstant *
        periodicVectorH3CoefficientNorm oldAdvecting *
          periodicVectorH3CoefficientNorm oldTransported := hbase
    _ ≤ 2592 * periodicH3EmbeddingConstant * (3 * ‖advecting‖) *
        (3 * ‖transported‖) := by
      gcongr
    _ = (23328 * periodicH3EmbeddingConstant) * ‖advecting‖ * ‖transported‖ := by
      ring

/-! ## Bilinearity and continuous bundling -/

theorem weightedLerayDivergenceConvolution_add_left
    (first second transported : PeriodicVectorWeightedSobolev 3) :
    weightedLerayDivergenceConvolution (first + second) transported =
      weightedLerayDivergenceConvolution first transported +
        weightedLerayDivergenceConvolution second transported := by
  funext output
  apply Subtype.ext
  funext k
  simp only [lp.coeFn_add, Pi.add_apply]
  rw [weightedLerayDivergenceConvolution_coefficient,
    weightedLerayDivergenceConvolution_coefficient,
    weightedLerayDivergenceConvolution_coefficient]
  have hmode :
      (fun component ↦
        (h3DivergenceConvolution
          (unweightedVectorThree (first + second))
          (unweightedVectorThree transported) component).1 k) =
        (fun component ↦
          (h3DivergenceConvolution
            (unweightedVectorThree first)
            (unweightedVectorThree transported) component).1 k) +
        fun component ↦
          (h3DivergenceConvolution
            (unweightedVectorThree second)
            (unweightedVectorThree transported) component).1 k := by
    funext component
    exact h3DivergenceConvolution_unweighted_add_left_coefficient
      first second transported component k
  rw [hmode, lerayProjectMode_add]
  simp only [Pi.add_apply]
  ring

theorem weightedLerayDivergenceConvolution_smul_left
    (c : ℂ) (advecting transported : PeriodicVectorWeightedSobolev 3) :
    weightedLerayDivergenceConvolution (c • advecting) transported =
      c • weightedLerayDivergenceConvolution advecting transported := by
  funext output
  apply Subtype.ext
  funext k
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [weightedLerayDivergenceConvolution_coefficient,
    weightedLerayDivergenceConvolution_coefficient]
  have hmode :
      (fun component ↦
        (h3DivergenceConvolution
          (unweightedVectorThree (c • advecting))
          (unweightedVectorThree transported) component).1 k) =
        c • fun component ↦
          (h3DivergenceConvolution
            (unweightedVectorThree advecting)
            (unweightedVectorThree transported) component).1 k := by
    funext component
    exact h3DivergenceConvolution_unweighted_smul_left_coefficient
      c advecting transported component k
  rw [hmode, lerayProjectMode_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem weightedLerayDivergenceConvolution_add_right
    (advecting first second : PeriodicVectorWeightedSobolev 3) :
    weightedLerayDivergenceConvolution advecting (first + second) =
      weightedLerayDivergenceConvolution advecting first +
        weightedLerayDivergenceConvolution advecting second := by
  funext output
  apply Subtype.ext
  funext k
  simp only [lp.coeFn_add, Pi.add_apply]
  rw [weightedLerayDivergenceConvolution_coefficient,
    weightedLerayDivergenceConvolution_coefficient,
    weightedLerayDivergenceConvolution_coefficient]
  have hmode :
      (fun component ↦
        (h3DivergenceConvolution
          (unweightedVectorThree advecting)
          (unweightedVectorThree (first + second)) component).1 k) =
        (fun component ↦
          (h3DivergenceConvolution
            (unweightedVectorThree advecting)
            (unweightedVectorThree first) component).1 k) +
        fun component ↦
          (h3DivergenceConvolution
            (unweightedVectorThree advecting)
            (unweightedVectorThree second) component).1 k := by
    funext component
    exact h3DivergenceConvolution_unweighted_add_right_coefficient
      advecting first second component k
  rw [hmode, lerayProjectMode_add]
  simp only [Pi.add_apply]
  ring

theorem weightedLerayDivergenceConvolution_smul_right
    (c : ℂ) (advecting transported : PeriodicVectorWeightedSobolev 3) :
    weightedLerayDivergenceConvolution advecting (c • transported) =
      c • weightedLerayDivergenceConvolution advecting transported := by
  funext output
  apply Subtype.ext
  funext k
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [weightedLerayDivergenceConvolution_coefficient,
    weightedLerayDivergenceConvolution_coefficient]
  have hmode :
      (fun component ↦
        (h3DivergenceConvolution
          (unweightedVectorThree advecting)
          (unweightedVectorThree (c • transported)) component).1 k) =
        c • fun component ↦
          (h3DivergenceConvolution
            (unweightedVectorThree advecting)
            (unweightedVectorThree transported) component).1 k := by
    funext component
    exact h3DivergenceConvolution_unweighted_smul_right_coefficient
      c advecting transported component k
  rw [hmode, lerayProjectMode_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The exact transported coefficient operation as a genuinely bilinear linear map. -/
def weightedLerayDivergenceConvolutionLinear :
    PeriodicVectorWeightedSobolev 3 →ₗ[ℂ]
      PeriodicVectorWeightedSobolev 3 →ₗ[ℂ]
        PeriodicVectorWeightedSobolev 2 :=
  LinearMap.mk₂ ℂ weightedLerayDivergenceConvolution
    weightedLerayDivergenceConvolution_add_left
    weightedLerayDivergenceConvolution_smul_left
    weightedLerayDivergenceConvolution_add_right
    weightedLerayDivergenceConvolution_smul_right

/-- The complete native `H³ × H³ → H²` Leray passage as a continuous curried bilinear
operator. -/
def weightedLerayDivergenceConvolutionContinuous :
    PeriodicVectorWeightedSobolev 3 →L[ℂ]
      PeriodicVectorWeightedSobolev 3 →L[ℂ]
        PeriodicVectorWeightedSobolev 2 :=
  weightedLerayDivergenceConvolutionLinear.mkContinuous₂
    (23328 * periodicH3EmbeddingConstant)
    norm_weightedLerayDivergenceConvolution_le

@[simp]
theorem weightedLerayDivergenceConvolutionContinuous_apply
    (advecting transported : PeriodicVectorWeightedSobolev 3) :
    weightedLerayDivergenceConvolutionContinuous advecting transported =
      weightedLerayDivergenceConvolution advecting transported :=
  rfl

/-- Explicit operator-norm bound for the bundled continuous bilinear passage. -/
theorem norm_weightedLerayDivergenceConvolutionContinuous_le :
    ‖weightedLerayDivergenceConvolutionContinuous‖ ≤
      23328 * periodicH3EmbeddingConstant := by
  exact LinearMap.mkContinuous₂_norm_le weightedLerayDivergenceConvolutionLinear
    (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
    norm_weightedLerayDivergenceConvolution_le

/-! ## Retained projection constraint -/

/-- Forget the native order-two weights componentwise while retaining every addressed Fourier
coefficient. -/
def nativeVectorTwoUnderlying (state : PeriodicVectorWeightedSobolev 2) :
    PeriodicVectorFourierL2 :=
  fun component ↦ weightedSobolevRawCoefficients 2 (state component)

/-- Although the unrestricted domain does not assume divergence freedom or Fourier reality, the
returned population satisfies the exact modewise Leray divergence constraint. -/
theorem weightedLerayDivergenceConvolution_divergenceFree
    (advecting transported : PeriodicVectorWeightedSobolev 3) :
    IsModewiseDivergenceFree
      (nativeVectorTwoUnderlying
        (weightedLerayDivergenceConvolution advecting transported)) := by
  let oldOutput := lerayProjectedH3DivergenceConvolution
    (unweightedVectorThree advecting) (unweightedVectorThree transported)
  have hunderlying :
      nativeVectorTwoUnderlying
        (weightedLerayDivergenceConvolution advecting transported) =
        periodicVectorSobolevTwoUnderlying oldOutput := by
    funext component
    simpa only [nativeVectorTwoUnderlying,
      weightedLerayDivergenceConvolution_apply,
      periodicVectorSobolevTwoUnderlying] using
        congrArg Subtype.val
          (weightedSobolevCoefficients_coefficientWeightedRealization 2
            (oldOutput component))
  rw [hunderlying]
  exact lerayProjectedH3DivergenceConvolution_divergenceFree _ _

section Audit

#print axioms periodicH3CoefficientNorm_eq_nativeNorm
#print axioms periodicH2CoefficientNorm_eq_nativeNorm
#print axioms norm_weightedLerayDivergenceConvolution_le
#print axioms weightedLerayDivergenceConvolutionContinuous
#print axioms norm_weightedLerayDivergenceConvolutionContinuous_le
#print axioms weightedLerayDivergenceConvolution_divergenceFree

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
