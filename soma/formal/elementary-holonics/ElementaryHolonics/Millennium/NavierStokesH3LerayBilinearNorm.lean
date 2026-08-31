import ElementaryHolonics.Millennium.NavierStokesH3BilinearNorm
import ElementaryHolonics.Millennium.NavierStokesH3LerayBilinear

/-!
# Quantitative norm of the periodic Leray-projected H³ bilinear passage

The scalar predecessor returns an explicit quantitative `H³` convolution bound.  This owner
spends one derivative, assembles the three divergence faces, and then applies the exact modewise
Leray projection.  Both scalar Sobolev norms are norms of genuine weighted `ℓ²(ℤ³)` carriers;
the vector norms are their Euclidean direct sums over the three retained component addresses.

The final constant is deliberately conservative.  It comes only from the already proved scalar
constant sixteen, three finite divergence faces, and the predecessor's uniform Leray estimate.
No Fourier cutoff, local-existence premise, or conclusion-shaped continuation assumption enters.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal lp

namespace Soma.Holonics.Millennium.NavierStokesH3LerayBilinearNorm

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear

/-! ## Honest weighted scalar `H²` norm -/

/-- The positive square-root of the exact order-two periodic Sobolev weight. -/
def sobolevTwoAmplitude (k : SpatialFrequency) : ℝ :=
  Real.sqrt (periodicSobolevWeight 2 k)

theorem sobolevTwoAmplitude_nonneg (k : SpatialFrequency) :
    0 ≤ sobolevTwoAmplitude k :=
  Real.sqrt_nonneg _

theorem sobolevTwoAmplitude_sq (k : SpatialFrequency) :
    sobolevTwoAmplitude k ^ 2 = periodicSobolevWeight 2 k := by
  rw [sobolevTwoAmplitude,
    Real.sq_sqrt (periodicSobolevWeight_nonneg 2 k)]

/-- The exact weighted absolute coefficient population of a scalar `H²` carrier. -/
def weightedAbsoluteCoefficientTwo
    (coeff : PeriodicSobolevCoefficients 2) : PeriodicRealFourierL2 :=
  ⟨fun k ↦ sobolevTwoAmplitude k * ‖coeff.1 k‖, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hnonneg (k : SpatialFrequency) :
        0 ≤ sobolevTwoAmplitude k * ‖coeff.1 k‖ :=
      mul_nonneg (sobolevTwoAmplitude_nonneg k) (norm_nonneg _)
    have hcoeff := coeff.property
    unfold HasPeriodicSobolevCoefficients at hcoeff
    simpa only [Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (hnonneg _), mul_pow, sobolevTwoAmplitude_sq] using hcoeff⟩

/-- The scalar weighted `H²` norm, literally the norm of the preceding complete `ℓ²` carrier. -/
def periodicH2CoefficientNorm
    (coeff : PeriodicSobolevCoefficients 2) : ℝ :=
  ‖weightedAbsoluteCoefficientTwo coeff‖

theorem periodicH2CoefficientNorm_nonneg
    (coeff : PeriodicSobolevCoefficients 2) :
    0 ≤ periodicH2CoefficientNorm coeff :=
  norm_nonneg _

private theorem norm_weightedAbsoluteCoefficientTwo_apply_sq
    (coeff : PeriodicSobolevCoefficients 2) (k : SpatialFrequency) :
    ‖weightedAbsoluteCoefficientTwo coeff k‖ ^ 2 =
      periodicSobolevWeight 2 k * ‖coeff.1 k‖ ^ 2 := by
  simp only [weightedAbsoluteCoefficientTwo, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sobolevTwoAmplitude_nonneg k) (norm_nonneg _)),
    mul_pow, sobolevTwoAmplitude_sq]

private theorem norm_weightedAbsoluteCoefficientThree_apply_sq
    (coeff : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    ‖weightedAbsoluteCoefficient coeff k‖ ^ 2 =
      periodicSobolevWeight 3 k * ‖coeff.1 k‖ ^ 2 := by
  simp only [weightedAbsoluteCoefficient, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sobolevThreeAmplitude_nonneg k) (norm_nonneg _)),
    mul_pow, sobolevThreeAmplitude_sq]

private theorem periodicRealFourierL2_norm_le_of_pointwise_sq_le
    (left right : PeriodicRealFourierL2)
    (hpoint : ∀ k, ‖left k‖ ^ 2 ≤ ‖right k‖ ^ 2) :
    ‖left‖ ≤ ‖right‖ := by
  have hleftSummable : Summable fun k ↦ ‖left k‖ ^ 2 := by
    have h := (lp.memℓp left).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hrightSummable : Summable fun k ↦ ‖right k‖ ^ 2 := by
    have h := (lp.memℓp right).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hsum : (∑' k, ‖left k‖ ^ 2) ≤ ∑' k, ‖right k‖ ^ 2 :=
    hleftSummable.tsum_le_tsum hpoint hrightSummable
  have hleftNorm : (∑' k, ‖left k‖ ^ 2) = ‖left‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) left
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  have hrightNorm : (∑' k, ‖right k‖ ^ 2) = ‖right‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) right
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  rw [hleftNorm, hrightNorm] at hsum
  nlinarith [norm_nonneg left, norm_nonneg right]

/-! ## One derivative contracts `H³` into `H²` -/

private theorem norm_periodicSobolevThreeDerivativeIntoTwo_apply_sq
    (coordinate : Fin 3) (coeff : PeriodicSobolevCoefficients 3)
    (k : SpatialFrequency) :
    ‖(periodicSobolevThreeDerivativeIntoTwo coordinate coeff).1 k‖ ^ 2 =
      ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) * ‖coeff.1 k‖ ^ 2 := by
  rw [periodicSobolevThreeDerivativeIntoTwo_apply]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
    Complex.norm_I, Complex.norm_intCast, mul_one]
  rw [abs_of_pos Real.pi_pos]
  ring_nf
  rw [sq_abs]
  ring

/-- Spending one coordinate derivative has operator norm at most one from the exact scalar
weighted `H³` carrier to the exact scalar weighted `H²` carrier. -/
theorem periodicH2CoefficientNorm_derivativeIntoTwo_le
    (coordinate : Fin 3) (coeff : PeriodicSobolevCoefficients 3) :
    periodicH2CoefficientNorm
        (periodicSobolevThreeDerivativeIntoTwo coordinate coeff) ≤
      periodicH3CoefficientNorm coeff := by
  unfold periodicH2CoefficientNorm periodicH3CoefficientNorm
  apply periodicRealFourierL2_norm_le_of_pointwise_sq_le
  intro k
  rw [norm_weightedAbsoluteCoefficientTwo_apply_sq,
    norm_weightedAbsoluteCoefficientThree_apply_sq,
    norm_periodicSobolevThreeDerivativeIntoTwo_apply_sq]
  calc
    periodicSobolevWeight 2 k *
        (((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) * ‖coeff.1 k‖ ^ 2) =
        (periodicSobolevWeight 2 k *
          ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2)) * ‖coeff.1 k‖ ^ 2 := by
      ring
    _ ≤ periodicSobolevWeight 3 k * ‖coeff.1 k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (periodicSobolevWeight_two_mul_coordinate_symbol_sq_le_three coordinate k)
        (sq_nonneg _)

/-- One addressed divergence face inherits the explicit scalar H³ algebra constant. -/
theorem periodicH2CoefficientNorm_scalarH3DivergenceProduct_le
    (coordinate : Fin 3) (left right : PeriodicSobolevCoefficients 3) :
    periodicH2CoefficientNorm (scalarH3DivergenceProduct coordinate left right) ≤
      16 * periodicH3EmbeddingConstant * periodicH3CoefficientNorm left *
        periodicH3CoefficientNorm right :=
  (periodicH2CoefficientNorm_derivativeIntoTwo_le coordinate
      (scalarH3Product left right)).trans
    (periodicH3CoefficientNorm_scalarH3Product_le left right)

/-! ## The three divergence faces -/

/-- A positive `ℓ²` envelope retaining all three addressed divergence faces. -/
def h3DivergenceComponentNormEnvelope
    (advecting transported : PeriodicVectorSobolevThree) (output : Fin 3) :
    PeriodicRealFourierL2 :=
  ∑ coordinate : Fin 3,
    weightedAbsoluteCoefficientTwo
      (scalarH3DivergenceProduct coordinate (advecting coordinate)
        (transported output))

private theorem norm_weighted_h3DivergenceComponent_le_envelope
    (advecting transported : PeriodicVectorSobolevThree)
    (output : Fin 3) (k : SpatialFrequency) :
    ‖weightedAbsoluteCoefficientTwo
        (h3DivergenceConvolutionComponent advecting transported output) k‖ ≤
      ‖h3DivergenceComponentNormEnvelope advecting transported output k‖ := by
  have htriangle :
      ‖∑ coordinate : Fin 3,
          (scalarH3DivergenceProduct coordinate (advecting coordinate)
            (transported output)).1 k‖ ≤
        ∑ coordinate : Fin 3,
          ‖(scalarH3DivergenceProduct coordinate (advecting coordinate)
            (transported output)).1 k‖ :=
    norm_sum_le _ _
  have henvelopeNonneg :
      0 ≤ h3DivergenceComponentNormEnvelope advecting transported output k := by
    unfold h3DivergenceComponentNormEnvelope
    simp only [lp.coeFn_sum, Finset.sum_apply, weightedAbsoluteCoefficientTwo]
    exact Finset.sum_nonneg fun coordinate _ ↦
      mul_nonneg (sobolevTwoAmplitude_nonneg k) (norm_nonneg _)
  have henvelopeNorm :
      ‖h3DivergenceComponentNormEnvelope advecting transported output k‖ =
        h3DivergenceComponentNormEnvelope advecting transported output k := by
    rw [Real.norm_eq_abs, abs_of_nonneg henvelopeNonneg]
  rw [henvelopeNorm]
  change
    |sobolevTwoAmplitude k *
        ‖(∑ coordinate : Fin 3,
          (scalarH3DivergenceProduct coordinate (advecting coordinate)
            (transported output)).1) k‖| ≤ _
  rw [abs_of_nonneg
    (mul_nonneg (sobolevTwoAmplitude_nonneg k) (norm_nonneg _))]
  simp only [h3DivergenceComponentNormEnvelope, lp.coeFn_sum, Finset.sum_apply,
    weightedAbsoluteCoefficientTwo]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [lp.coeFn_sum, Finset.sum_apply] using htriangle)
    (sobolevTwoAmplitude_nonneg k)

/-- The weighted `H²` norm of one assembled output component is no larger than the sum of the
three addressed scalar-face norms. -/
theorem periodicH2CoefficientNorm_h3DivergenceConvolutionComponent_le_sum
    (advecting transported : PeriodicVectorSobolevThree) (output : Fin 3) :
    periodicH2CoefficientNorm
        (h3DivergenceConvolutionComponent advecting transported output) ≤
      ∑ coordinate : Fin 3,
        periodicH2CoefficientNorm
          (scalarH3DivergenceProduct coordinate (advecting coordinate)
            (transported output)) := by
  calc
    periodicH2CoefficientNorm
        (h3DivergenceConvolutionComponent advecting transported output) ≤
        ‖h3DivergenceComponentNormEnvelope advecting transported output‖ := by
      unfold periodicH2CoefficientNorm
      apply periodicRealFourierL2_norm_le_of_pointwise_sq_le
      intro k
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_weighted_h3DivergenceComponent_le_envelope
          advecting transported output k) 2
    _ ≤ ∑ coordinate : Fin 3,
        ‖weightedAbsoluteCoefficientTwo
          (scalarH3DivergenceProduct coordinate (advecting coordinate)
            (transported output))‖ := by
      unfold h3DivergenceComponentNormEnvelope
      exact norm_sum_le _ _
    _ = ∑ coordinate : Fin 3,
        periodicH2CoefficientNorm
          (scalarH3DivergenceProduct coordinate (advecting coordinate)
            (transported output)) := rfl

/-- Quantitative bound for one assembled divergence output component. -/
theorem periodicH2CoefficientNorm_h3DivergenceConvolutionComponent_le
    (advecting transported : PeriodicVectorSobolevThree) (output : Fin 3) :
    periodicH2CoefficientNorm
        (h3DivergenceConvolutionComponent advecting transported output) ≤
      16 * periodicH3EmbeddingConstant *
        (∑ coordinate : Fin 3, periodicH3CoefficientNorm (advecting coordinate)) *
          periodicH3CoefficientNorm (transported output) := by
  calc
    periodicH2CoefficientNorm
        (h3DivergenceConvolutionComponent advecting transported output) ≤
        ∑ coordinate : Fin 3,
          periodicH2CoefficientNorm
            (scalarH3DivergenceProduct coordinate (advecting coordinate)
              (transported output)) :=
      periodicH2CoefficientNorm_h3DivergenceConvolutionComponent_le_sum
        advecting transported output
    _ ≤ ∑ coordinate : Fin 3,
        16 * periodicH3EmbeddingConstant *
          periodicH3CoefficientNorm (advecting coordinate) *
            periodicH3CoefficientNorm (transported output) := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact periodicH2CoefficientNorm_scalarH3DivergenceProduct_le coordinate
        (advecting coordinate) (transported output)
    _ = 16 * periodicH3EmbeddingConstant *
        (∑ coordinate : Fin 3, periodicH3CoefficientNorm (advecting coordinate)) *
          periodicH3CoefficientNorm (transported output) := by
      simp only [Fin.sum_univ_succ]
      ring

/-! ## Euclidean direct-sum vector norms -/

/-- The Euclidean direct sum of the three exact scalar weighted `H³` norms. -/
def periodicVectorH3CoefficientNorm
    (state : PeriodicVectorSobolevThree) : ℝ :=
  Real.sqrt (∑ component : Fin 3,
    periodicH3CoefficientNorm (state component) ^ 2)

/-- The Euclidean direct sum of the three exact scalar weighted `H²` norms. -/
def periodicVectorH2CoefficientNorm
    (state : PeriodicVectorSobolevTwo) : ℝ :=
  Real.sqrt (∑ component : Fin 3,
    periodicH2CoefficientNorm (state component) ^ 2)

theorem periodicVectorH3CoefficientNorm_nonneg
    (state : PeriodicVectorSobolevThree) :
    0 ≤ periodicVectorH3CoefficientNorm state :=
  Real.sqrt_nonneg _

theorem periodicVectorH2CoefficientNorm_nonneg
    (state : PeriodicVectorSobolevTwo) :
    0 ≤ periodicVectorH2CoefficientNorm state :=
  Real.sqrt_nonneg _

theorem periodicH3CoefficientNorm_component_le_vector
    (state : PeriodicVectorSobolevThree) (component : Fin 3) :
    periodicH3CoefficientNorm (state component) ≤
      periodicVectorH3CoefficientNorm state := by
  have hsquare : periodicH3CoefficientNorm (state component) ^ 2 ≤
      ∑ c : Fin 3, periodicH3CoefficientNorm (state c) ^ 2 :=
    Finset.single_le_sum (fun c _ ↦ sq_nonneg (periodicH3CoefficientNorm (state c)))
      (Finset.mem_univ component)
  calc
    periodicH3CoefficientNorm (state component) =
        Real.sqrt (periodicH3CoefficientNorm (state component) ^ 2) := by
      rw [Real.sqrt_sq (periodicH3CoefficientNorm_nonneg (state component))]
    _ ≤ Real.sqrt (∑ c : Fin 3,
        periodicH3CoefficientNorm (state c) ^ 2) :=
      Real.sqrt_le_sqrt hsquare
    _ = periodicVectorH3CoefficientNorm state := rfl

theorem periodicH2CoefficientNorm_component_le_vector
    (state : PeriodicVectorSobolevTwo) (component : Fin 3) :
    periodicH2CoefficientNorm (state component) ≤
      periodicVectorH2CoefficientNorm state := by
  have hsquare : periodicH2CoefficientNorm (state component) ^ 2 ≤
      ∑ c : Fin 3, periodicH2CoefficientNorm (state c) ^ 2 :=
    Finset.single_le_sum (fun c _ ↦ sq_nonneg (periodicH2CoefficientNorm (state c)))
      (Finset.mem_univ component)
  calc
    periodicH2CoefficientNorm (state component) =
        Real.sqrt (periodicH2CoefficientNorm (state component) ^ 2) := by
      rw [Real.sqrt_sq (periodicH2CoefficientNorm_nonneg (state component))]
    _ ≤ Real.sqrt (∑ c : Fin 3,
        periodicH2CoefficientNorm (state c) ^ 2) :=
      Real.sqrt_le_sqrt hsquare
    _ = periodicVectorH2CoefficientNorm state := rfl

theorem sum_periodicH3CoefficientNorm_le_three_mul_vector
    (state : PeriodicVectorSobolevThree) :
    (∑ component : Fin 3, periodicH3CoefficientNorm (state component)) ≤
      3 * periodicVectorH3CoefficientNorm state := by
  calc
    (∑ component : Fin 3, periodicH3CoefficientNorm (state component)) ≤
        ∑ _component : Fin 3, periodicVectorH3CoefficientNorm state := by
      apply Finset.sum_le_sum
      intro component _
      exact periodicH3CoefficientNorm_component_le_vector state component
    _ = 3 * periodicVectorH3CoefficientNorm state := by
      simp

theorem sum_periodicH2CoefficientNorm_le_three_mul_vector
    (state : PeriodicVectorSobolevTwo) :
    (∑ component : Fin 3, periodicH2CoefficientNorm (state component)) ≤
      3 * periodicVectorH2CoefficientNorm state := by
  calc
    (∑ component : Fin 3, periodicH2CoefficientNorm (state component)) ≤
        ∑ _component : Fin 3, periodicVectorH2CoefficientNorm state := by
      apply Finset.sum_le_sum
      intro component _
      exact periodicH2CoefficientNorm_component_le_vector state component
    _ = 3 * periodicVectorH2CoefficientNorm state := by
      simp

theorem periodicVectorH2CoefficientNorm_le_component_sum
    (state : PeriodicVectorSobolevTwo) :
    periodicVectorH2CoefficientNorm state ≤
      ∑ component : Fin 3, periodicH2CoefficientNorm (state component) := by
  unfold periodicVectorH2CoefficientNorm
  rw [Real.sqrt_le_iff]
  constructor
  · exact Finset.sum_nonneg fun component _ ↦
      periodicH2CoefficientNorm_nonneg (state component)
  · exact Finset.sum_sq_le_sq_sum_of_nonneg fun component _ ↦
      periodicH2CoefficientNorm_nonneg (state component)

/-- The complete unprojected divergence population is quantitatively bilinear between the exact
Euclidean vector Sobolev norms. -/
theorem periodicVectorH2CoefficientNorm_h3DivergenceConvolution_le
    (advecting transported : PeriodicVectorSobolevThree) :
    periodicVectorH2CoefficientNorm
        (h3DivergenceConvolution advecting transported) ≤
      144 * periodicH3EmbeddingConstant *
        periodicVectorH3CoefficientNorm advecting *
          periodicVectorH3CoefficientNorm transported := by
  have hC := periodicH3EmbeddingConstant_nonneg
  have hU := periodicVectorH3CoefficientNorm_nonneg advecting
  have hV := periodicVectorH3CoefficientNorm_nonneg transported
  calc
    periodicVectorH2CoefficientNorm
        (h3DivergenceConvolution advecting transported) ≤
        ∑ output : Fin 3,
          periodicH2CoefficientNorm
            (h3DivergenceConvolution advecting transported output) :=
      periodicVectorH2CoefficientNorm_le_component_sum _
    _ ≤ ∑ output : Fin 3,
        16 * periodicH3EmbeddingConstant *
          (∑ coordinate : Fin 3,
            periodicH3CoefficientNorm (advecting coordinate)) *
            periodicH3CoefficientNorm (transported output) := by
      apply Finset.sum_le_sum
      intro output _
      exact periodicH2CoefficientNorm_h3DivergenceConvolutionComponent_le
        advecting transported output
    _ = 16 * periodicH3EmbeddingConstant *
        (∑ coordinate : Fin 3, periodicH3CoefficientNorm (advecting coordinate)) *
          (∑ output : Fin 3, periodicH3CoefficientNorm (transported output)) := by
      simp only [Fin.sum_univ_succ]
      ring
    _ ≤ 16 * periodicH3EmbeddingConstant *
        (3 * periodicVectorH3CoefficientNorm advecting) *
          (3 * periodicVectorH3CoefficientNorm transported) := by
      have hsumU := sum_periodicH3CoefficientNorm_le_three_mul_vector advecting
      have hsumV := sum_periodicH3CoefficientNorm_le_three_mul_vector transported
      have hsumUnonneg :
          0 ≤ ∑ coordinate : Fin 3,
            periodicH3CoefficientNorm (advecting coordinate) :=
        Finset.sum_nonneg fun coordinate _ ↦
          periodicH3CoefficientNorm_nonneg (advecting coordinate)
      have hsumVnonneg :
          0 ≤ ∑ output : Fin 3,
            periodicH3CoefficientNorm (transported output) :=
        Finset.sum_nonneg fun output _ ↦
          periodicH3CoefficientNorm_nonneg (transported output)
      have hrightUnonneg : 0 ≤ 3 * periodicVectorH3CoefficientNorm advecting :=
        mul_nonneg (by norm_num) hU
      have hproduct := mul_le_mul hsumU hsumV hsumVnonneg hrightUnonneg
      calc
        16 * periodicH3EmbeddingConstant *
            (∑ coordinate : Fin 3, periodicH3CoefficientNorm (advecting coordinate)) *
              (∑ output : Fin 3, periodicH3CoefficientNorm (transported output)) =
            (16 * periodicH3EmbeddingConstant) *
              ((∑ coordinate : Fin 3,
                  periodicH3CoefficientNorm (advecting coordinate)) *
                (∑ output : Fin 3,
                  periodicH3CoefficientNorm (transported output))) := by ring
        _ ≤ (16 * periodicH3EmbeddingConstant) *
            ((3 * periodicVectorH3CoefficientNorm advecting) *
              (3 * periodicVectorH3CoefficientNorm transported)) :=
          mul_le_mul_of_nonneg_left hproduct (mul_nonneg (by norm_num) hC)
        _ = 16 * periodicH3EmbeddingConstant *
            (3 * periodicVectorH3CoefficientNorm advecting) *
              (3 * periodicVectorH3CoefficientNorm transported) := by ring
    _ = 144 * periodicH3EmbeddingConstant *
        periodicVectorH3CoefficientNorm advecting *
          periodicVectorH3CoefficientNorm transported := by ring

/-! ## Quantitative Leray projection -/

/-- The positive weighted envelope for one Leray output component. -/
def lerayProjectionComponentNormEnvelope
    (state : PeriodicVectorSobolevTwo) : PeriodicRealFourierL2 :=
  (2 : ℝ) • ∑ component : Fin 3, weightedAbsoluteCoefficientTwo (state component)

private theorem norm_weighted_lerayProjectionComponent_le_envelope
    (state : PeriodicVectorSobolevTwo) (output : Fin 3) (k : SpatialFrequency) :
    ‖weightedAbsoluteCoefficientTwo
        (lerayProjectPeriodicVectorSobolevTwo state output) k‖ ≤
      ‖lerayProjectionComponentNormEnvelope state k‖ := by
  have hmode := norm_lerayProjectMode_coordinate_le k
    (fun component ↦ (state component).1 k) output
  have henvelopeNonneg : 0 ≤ lerayProjectionComponentNormEnvelope state k := by
    unfold lerayProjectionComponentNormEnvelope
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sum,
      Finset.sum_apply, weightedAbsoluteCoefficientTwo]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun component _ ↦
      mul_nonneg (sobolevTwoAmplitude_nonneg k) (norm_nonneg _))
  have henvelopeNorm : ‖lerayProjectionComponentNormEnvelope state k‖ =
      lerayProjectionComponentNormEnvelope state k := by
    rw [Real.norm_eq_abs, abs_of_nonneg henvelopeNonneg]
  rw [henvelopeNorm]
  change |sobolevTwoAmplitude k *
      ‖lerayProjectMode k (fun component ↦ (state component).1 k) output‖| ≤ _
  rw [abs_of_nonneg
    (mul_nonneg (sobolevTwoAmplitude_nonneg k) (norm_nonneg _))]
  simp only [lerayProjectionComponentNormEnvelope, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, lp.coeFn_sum, Finset.sum_apply, weightedAbsoluteCoefficientTwo]
  have hscaled := mul_le_mul_of_nonneg_left hmode (sobolevTwoAmplitude_nonneg k)
  calc
    sobolevTwoAmplitude k *
        ‖lerayProjectMode k (fun component ↦ (state component).1 k) output‖ ≤
        sobolevTwoAmplitude k *
          (2 * ∑ component : Fin 3, ‖(state component).1 k‖) := hscaled
    _ = (2 * sobolevTwoAmplitude k) *
        ∑ component : Fin 3, ‖(state component).1 k‖ := by ring
    _ = ∑ component : Fin 3,
        (2 * sobolevTwoAmplitude k) * ‖(state component).1 k‖ := by
      rw [Finset.mul_sum]
    _ = ∑ component : Fin 3,
        2 * (sobolevTwoAmplitude k * ‖(state component).1 k‖) := by
      apply Finset.sum_congr rfl
      intro component _
      ring
    _ = 2 * ∑ component : Fin 3,
        sobolevTwoAmplitude k * ‖(state component).1 k‖ := by
      rw [Finset.mul_sum]

/-- Each projected output component has `H²` norm at most twice the component-sum norm of the
input vector. -/
theorem periodicH2CoefficientNorm_lerayProjectComponent_le
    (state : PeriodicVectorSobolevTwo) (output : Fin 3) :
    periodicH2CoefficientNorm (lerayProjectPeriodicVectorSobolevTwo state output) ≤
      2 * ∑ component : Fin 3, periodicH2CoefficientNorm (state component) := by
  calc
    periodicH2CoefficientNorm (lerayProjectPeriodicVectorSobolevTwo state output) ≤
        ‖lerayProjectionComponentNormEnvelope state‖ := by
      unfold periodicH2CoefficientNorm
      apply periodicRealFourierL2_norm_le_of_pointwise_sq_le
      intro k
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_weighted_lerayProjectionComponent_le_envelope state output k) 2
    _ ≤ 2 * ∑ component : Fin 3,
        ‖weightedAbsoluteCoefficientTwo (state component)‖ := by
      unfold lerayProjectionComponentNormEnvelope
      rw [norm_smul]
      norm_num only [Real.norm_ofNat]
      gcongr
      exact norm_sum_le _ _
    _ = 2 * ∑ component : Fin 3,
        periodicH2CoefficientNorm (state component) := rfl

/-- The exact modewise Leray projection is bounded on the Euclidean vector `H²` norm with the
explicit conservative constant eighteen. -/
theorem periodicVectorH2CoefficientNorm_lerayProject_le
    (state : PeriodicVectorSobolevTwo) :
    periodicVectorH2CoefficientNorm (lerayProjectPeriodicVectorSobolevTwo state) ≤
      18 * periodicVectorH2CoefficientNorm state := by
  have hstate := periodicVectorH2CoefficientNorm_nonneg state
  calc
    periodicVectorH2CoefficientNorm (lerayProjectPeriodicVectorSobolevTwo state) ≤
        ∑ output : Fin 3,
          periodicH2CoefficientNorm
            (lerayProjectPeriodicVectorSobolevTwo state output) :=
      periodicVectorH2CoefficientNorm_le_component_sum _
    _ ≤ ∑ _output : Fin 3,
        2 * ∑ component : Fin 3,
          periodicH2CoefficientNorm (state component) := by
      apply Finset.sum_le_sum
      intro output _
      exact periodicH2CoefficientNorm_lerayProjectComponent_le state output
    _ = 6 * ∑ component : Fin 3,
        periodicH2CoefficientNorm (state component) := by
      simp [Fin.sum_univ_succ]
      ring
    _ ≤ 6 * (3 * periodicVectorH2CoefficientNorm state) := by
      gcongr
      exact sum_periodicH2CoefficientNorm_le_three_mul_vector state
    _ = 18 * periodicVectorH2CoefficientNorm state := by ring

/-- Quantitative norm bound for the existing complete-lattice
`lerayProjectedH3DivergenceConvolution`. -/
theorem periodicVectorH2CoefficientNorm_lerayProjectedH3DivergenceConvolution_le
    (advecting transported : PeriodicVectorSobolevThree) :
    periodicVectorH2CoefficientNorm
        (lerayProjectedH3DivergenceConvolution advecting transported) ≤
      2592 * periodicH3EmbeddingConstant *
        periodicVectorH3CoefficientNorm advecting *
          periodicVectorH3CoefficientNorm transported := by
  have hprojection := periodicVectorH2CoefficientNorm_lerayProject_le
    (h3DivergenceConvolution advecting transported)
  have hdivergence := periodicVectorH2CoefficientNorm_h3DivergenceConvolution_le
    advecting transported
  calc
    periodicVectorH2CoefficientNorm
        (lerayProjectedH3DivergenceConvolution advecting transported) ≤
        18 * periodicVectorH2CoefficientNorm
          (h3DivergenceConvolution advecting transported) := hprojection
    _ ≤ 18 * (144 * periodicH3EmbeddingConstant *
        periodicVectorH3CoefficientNorm advecting *
          periodicVectorH3CoefficientNorm transported) := by
      gcongr
    _ = 2592 * periodicH3EmbeddingConstant *
        periodicVectorH3CoefficientNorm advecting *
          periodicVectorH3CoefficientNorm transported := by ring

section Audit

#print axioms periodicH2CoefficientNorm_derivativeIntoTwo_le
#print axioms periodicH2CoefficientNorm_h3DivergenceConvolutionComponent_le
#print axioms periodicVectorH2CoefficientNorm_h3DivergenceConvolution_le
#print axioms periodicVectorH2CoefficientNorm_lerayProject_le
#print axioms periodicVectorH2CoefficientNorm_lerayProjectedH3DivergenceConvolution_le

end Audit

end Soma.Holonics.Millennium.NavierStokesH3LerayBilinearNorm
