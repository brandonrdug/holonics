import ElementaryHolonics.Millennium.NavierStokesCompleteLinearWorkCofinalLimit
import ElementaryHolonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage
import ElementaryHolonics.Millennium.NavierStokesSharpNonlinearSource
import ElementaryHolonics.Millennium.NavierStokesWeightedHigherOrderTame

/-!
# Compact-time strong cofinal passage for the actual linear multiplier work

**[proved-derived; formal-checked]**  This owner supplies the depth-independent analytic
majorant omitted by the fixed-time Tannery passage.  It realizes each frequency curl as a
complete Fourier `ℓ2` population, spends one derivative on the native weighted Sobolev state,
and applies Cauchy--Schwarz before taking the finite output aperture.  Consequently the actual
depth work is bounded by one cubic weighted-`H³` service independent of depth.

The fixed-time cofinal theorem then bounds its pointwise limit by the same service.  On every
strict compact time interval the continuous native path supplies a constant integrable majorant,
so dominated convergence gives strong `L¹` convergence.  The cofinal receiver is unchanged: its
scale-zero stretching and transport boundaries remain explicit in
`completeCofinalLinearMultiplierWork`.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators Interval ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesCompleteLinearWorkCompactL1

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteLinearWorkCofinalLimit
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Native complete Fourier curl and its scale-uniform norm -/

@[simp]
theorem periodicFourierL2_sub_apply
    (left right : PeriodicFourierL2) (k : SpatialFrequency) :
    (left - right) k = left k - right k := by
  rw [lp.coeFn_sub]
  rfl

/-- Forgetting an inhomogeneous Sobolev weight is a contraction into raw Fourier `ℓ2`. -/
theorem norm_rawPeriodicSobolevCoefficients_le
    (order : ℕ) (coeff : PeriodicSobolevCoefficients order) :
    ‖coeff.1‖ ≤ periodicSobolevCoefficientNorm order coeff := by
  let raw : PeriodicFourierL2 := coeff.1
  let weighted := weightedAbsoluteCoefficientAtOrder order coeff
  have hraw : Summable fun k ↦ ‖raw k‖ ^ 2 := by
    have h := (lp.memℓp raw).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hweighted : Summable fun k ↦ ‖weighted k‖ ^ 2 := by
    have h := (lp.memℓp weighted).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hpoint (k : SpatialFrequency) : ‖raw k‖ ^ 2 ≤ ‖weighted k‖ ^ 2 := by
    simp only [raw, weighted, weightedAbsoluteCoefficientAtOrder,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (sobolevAmplitudeAtOrder_nonneg order k) (norm_nonneg _)), mul_pow,
      sobolevAmplitudeAtOrder_sq]
    exact le_mul_of_one_le_left (sq_nonneg _)
      (one_le_periodicSobolevWeight order k)
  have hsum := hraw.tsum_le_tsum hpoint hweighted
  have hrawNorm : (∑' k, ‖raw k‖ ^ 2) = ‖raw‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) raw
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  have hweightedNorm : (∑' k, ‖weighted k‖ ^ 2) = ‖weighted‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) weighted
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm
  rw [hrawNorm, hweightedNorm] at hsum
  change ‖raw‖ ≤ ‖weighted‖
  nlinarith [norm_nonneg raw, norm_nonneg weighted]

/-- One raw adjacent derivative is controlled by the native norm before spending the
derivative. -/
theorem norm_periodicSobolevDerivativeFourier_le
    (order : ℕ) (hpositive : 1 ≤ order) (coordinate : Fin 3)
    (state : PeriodicWeightedSobolev order) :
    ‖periodicSobolevDerivativeFourier order hpositive coordinate
        (weightedSobolevCoefficients order state)‖ ≤ ‖state‖ := by
  calc
    ‖periodicSobolevDerivativeFourier order hpositive coordinate
        (weightedSobolevCoefficients order state)‖ ≤
      periodicSobolevCoefficientNorm (order - 1)
        (periodicSobolevDerivativeIntoPred order hpositive coordinate
          (weightedSobolevCoefficients order state)) :=
      norm_rawPeriodicSobolevCoefficients_le (order - 1)
        (periodicSobolevDerivativeIntoPred order hpositive coordinate
          (weightedSobolevCoefficients order state))
    _ ≤ periodicSobolevCoefficientNorm order
        (weightedSobolevCoefficients order state) :=
      periodicSobolevCoefficientNorm_derivativeIntoPred_le _ _ _ _
    _ = ‖state‖ :=
      periodicSobolevCoefficientNorm_weightedSobolevCoefficients order state

/-- One component of the complete raw frequency curl, retained as an honest Fourier `ℓ2`
population. -/
def nativePeriodicCurlComponentFourier
    (order : ℕ) (hpositive : 1 ≤ order)
    (state : PeriodicVectorWeightedSobolev order) (output : Fin 3) :
    PeriodicFourierL2 :=
  ![
    periodicSobolevDerivativeFourier order hpositive 1
        (weightedSobolevCoefficients order (state 2)) -
      periodicSobolevDerivativeFourier order hpositive 2
        (weightedSobolevCoefficients order (state 1)),
    periodicSobolevDerivativeFourier order hpositive 2
        (weightedSobolevCoefficients order (state 0)) -
      periodicSobolevDerivativeFourier order hpositive 0
        (weightedSobolevCoefficients order (state 2)),
    periodicSobolevDerivativeFourier order hpositive 0
        (weightedSobolevCoefficients order (state 1)) -
      periodicSobolevDerivativeFourier order hpositive 1
        (weightedSobolevCoefficients order (state 0))] output

/-- The native Fourier curl carrier has exactly the repository's frequency-curl coefficient. -/
theorem nativePeriodicCurlComponentFourier_apply
    (order : ℕ) (hpositive : 1 ≤ order)
    (state : PeriodicVectorWeightedSobolev order)
    (output : Fin 3) (k : SpatialFrequency) :
    nativePeriodicCurlComponentFourier order hpositive state output k =
      frequencyCurlMultiplier k
        (fun component ↦
          (weightedSobolevCoefficients order (state component)).1 k) output := by
  fin_cases output <;>
    simp [nativePeriodicCurlComponentFourier, periodicFourierL2_sub_apply,
      periodicSobolevDerivativeFourier,
      frequencyCurlMultiplier, complexCross, crossProduct, complexFrequencyVector] <;>
    ring_nf

/-- Each complete curl component spends one derivative and costs at most two copies of the
native vector norm. -/
theorem norm_nativePeriodicCurlComponentFourier_le
    (order : ℕ) (hpositive : 1 ≤ order)
    (state : PeriodicVectorWeightedSobolev order) (output : Fin 3) :
    ‖nativePeriodicCurlComponentFourier order hpositive state output‖ ≤
      2 * ‖state‖ := by
  fin_cases output
  · simp only [nativePeriodicCurlComponentFourier]
    calc
      _ ≤ ‖periodicSobolevDerivativeFourier order hpositive 1
            (weightedSobolevCoefficients order (state 2))‖ +
          ‖periodicSobolevDerivativeFourier order hpositive 2
            (weightedSobolevCoefficients order (state 1))‖ := norm_sub_le _ _
      _ ≤ ‖state 2‖ + ‖state 1‖ := add_le_add
        (norm_periodicSobolevDerivativeFourier_le order hpositive 1 (state 2))
        (norm_periodicSobolevDerivativeFourier_le order hpositive 2 (state 1))
      _ ≤ 2 * ‖state‖ := by
        have h2 := norm_le_pi_norm state 2
        have h1 := norm_le_pi_norm state 1
        linarith
  · simp only [nativePeriodicCurlComponentFourier]
    calc
      _ ≤ ‖periodicSobolevDerivativeFourier order hpositive 2
            (weightedSobolevCoefficients order (state 0))‖ +
          ‖periodicSobolevDerivativeFourier order hpositive 0
            (weightedSobolevCoefficients order (state 2))‖ := norm_sub_le _ _
      _ ≤ ‖state 0‖ + ‖state 2‖ := add_le_add
        (norm_periodicSobolevDerivativeFourier_le order hpositive 2 (state 0))
        (norm_periodicSobolevDerivativeFourier_le order hpositive 0 (state 2))
      _ ≤ 2 * ‖state‖ := by
        have h0 := norm_le_pi_norm state 0
        have h2 := norm_le_pi_norm state 2
        linarith
  · simp only [nativePeriodicCurlComponentFourier]
    calc
      _ ≤ ‖periodicSobolevDerivativeFourier order hpositive 0
            (weightedSobolevCoefficients order (state 1))‖ +
          ‖periodicSobolevDerivativeFourier order hpositive 1
            (weightedSobolevCoefficients order (state 0))‖ := norm_sub_le _ _
      _ ≤ ‖state 1‖ + ‖state 0‖ := add_le_add
        (norm_periodicSobolevDerivativeFourier_le order hpositive 0 (state 1))
        (norm_periodicSobolevDerivativeFourier_le order hpositive 1 (state 0))
      _ ≤ 2 * ‖state‖ := by
        have h1 := norm_le_pi_norm state 1
        have h0 := norm_le_pi_norm state 0
        linarith

/-! ## Depth-independent actual work service -/

/-- A multiplier bounded by one cannot make a finite native-curl work exceed the complete
Fourier Cauchy--Schwarz population.  The coarse constant retains all three-by-three component
addresses explicitly. -/
theorem norm_linearMultiplierCoefficientWork_nativeCurl_le
    (leftOrder rightOrder : ℕ)
    (hleftPositive : 1 ≤ leftOrder) (hrightPositive : 1 ≤ rightOrder)
    (left : PeriodicVectorWeightedSobolev leftOrder)
    (right : PeriodicVectorWeightedSobolev rightOrder)
    (multiplier : SpatialFrequency → ℂ) (aperture : Finset SpatialFrequency)
    (hmultiplier : ∀ k ∈ aperture, ‖multiplier k‖ ≤ 1) :
    ‖linearMultiplierCoefficientWork multiplier aperture
        (fun k output ↦ nativePeriodicCurlComponentFourier
          leftOrder hleftPositive left output k)
        (fun k output ↦ nativePeriodicCurlComponentFourier
          rightOrder hrightPositive right output k)‖ ≤
      108 * ‖left‖ * ‖right‖ := by
  let leftCurl : Fin 3 → PeriodicFourierL2 :=
    nativePeriodicCurlComponentFourier leftOrder hleftPositive left
  let rightCurl : Fin 3 → PeriodicFourierL2 :=
    nativePeriodicCurlComponentFourier rightOrder hrightPositive right
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hproduct (i j : Fin 3) : Summable fun k ↦
      ‖leftCurl i k‖ * ‖rightCurl j k‖ :=
    lp.summable_mul hholder (leftCurl i) (rightCurl j)
  calc
    ‖linearMultiplierCoefficientWork multiplier aperture
        (fun k output ↦ leftCurl output k)
        (fun k output ↦ rightCurl output k)‖ ≤
      ∑ k ∈ aperture, 3 *
        (∑ i : Fin 3, ‖leftCurl i k‖) *
        (∑ j : Fin 3, ‖rightCurl j k‖) := by
      unfold linearMultiplierCoefficientWork
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
      rw [norm_mul]
      have hpair := norm_complexVectorSymmetricPhasePairing_le
        (fun output ↦ leftCurl output k) (fun output ↦ rightCurl output k)
      calc
        ‖multiplier k‖ *
            ‖complexVectorSymmetricPhasePairing
              (fun output ↦ leftCurl output k)
              (fun output ↦ rightCurl output k)‖ ≤
          3 * ‖fun output ↦ leftCurl output k‖ *
            ‖fun output ↦ rightCurl output k‖ := by
          simpa using
            (mul_le_mul (hmultiplier k hk) hpair (norm_nonneg _) (by norm_num))
        _ ≤ 3 * (∑ i : Fin 3, ‖leftCurl i k‖) *
            (∑ j : Fin 3, ‖rightCurl j k‖) := by
          have hl : ‖fun output ↦ leftCurl output k‖ ≤
              ∑ i : Fin 3, ‖leftCurl i k‖ := by
            rw [pi_norm_le_iff_of_nonempty]
            intro i
            exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (leftCurl j k))
              (Finset.mem_univ i)
          have hr : ‖fun output ↦ rightCurl output k‖ ≤
              ∑ j : Fin 3, ‖rightCurl j k‖ := by
            rw [pi_norm_le_iff_of_nonempty]
            intro j
            exact Finset.single_le_sum (fun i _ ↦ norm_nonneg (rightCurl i k))
              (Finset.mem_univ j)
          calc
            3 * ‖fun output ↦ leftCurl output k‖ *
                ‖fun output ↦ rightCurl output k‖ ≤
              3 * (∑ i : Fin 3, ‖leftCurl i k‖) *
                ‖fun output ↦ rightCurl output k‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hl (by norm_num)) (norm_nonneg _)
            _ ≤ 3 * (∑ i : Fin 3, ‖leftCurl i k‖) *
                (∑ j : Fin 3, ‖rightCurl j k‖) :=
              mul_le_mul_of_nonneg_left hr
                (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ ↦ norm_nonneg _))
    _ = ∑ k ∈ aperture, ∑ i : Fin 3, ∑ j : Fin 3,
        3 * (‖leftCurl i k‖ * ‖rightCurl j k‖) := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      ring
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        3 * (‖leftCurl i‖ * ‖rightCurl j‖) := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro i _hi
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro j _hj
      rw [← Finset.mul_sum]
      calc
        3 * (∑ k ∈ aperture, ‖leftCurl i k‖ * ‖rightCurl j k‖) ≤
            3 * (∑' k, ‖leftCurl i k‖ * ‖rightCurl j k‖) := by
          gcongr
          exact (hproduct i j).sum_le_tsum aperture
            (fun k _hk ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ 3 * (‖leftCurl i‖ * ‖rightCurl j‖) := by
          gcongr
          exact lp.tsum_mul_le_mul_norm' hholder (leftCurl i) (rightCurl j)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3,
        3 * ((2 * ‖left‖) * (2 * ‖right‖)) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      gcongr
      · exact norm_nativePeriodicCurlComponentFourier_le
          leftOrder hleftPositive left i
      · exact norm_nativePeriodicCurlComponentFourier_le
          rightOrder hrightPositive right j
    _ = 108 * ‖left‖ * ‖right‖ := by
      simp only [Fin.sum_univ_three]
      ring

/-- Negating the right curl negates the complete symmetric work before any norm is taken. -/
theorem linearMultiplierCoefficientWork_neg_right
    (multiplier : SpatialFrequency → ℂ) (aperture : Finset SpatialFrequency)
    (coefficient source : SpatialFrequency → ComplexVector) :
    linearMultiplierCoefficientWork multiplier aperture coefficient
        (fun k ↦ -source k) =
      -linearMultiplierCoefficientWork multiplier aperture coefficient source := by
  unfold linearMultiplierCoefficientWork
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  unfold complexVectorSymmetricPhasePairing complexVectorHermitianPairing
  simp only [Pi.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The actual velocity coefficient is the native raw `H³` curl coefficient. -/
theorem openPeriodicVorticityFourierMode_eq_nativePeriodicCurl
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    openPeriodicVorticityFourierMode solution t k =
      fun output ↦ nativePeriodicCurlComponentFourier 3 (by norm_num)
        (openVelocityWeightedH3State solution t) output k := by
  funext output
  rw [nativePeriodicCurlComponentFourier_apply]
  rw [openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier]
  congr 1
  funext component
  have hunweighted := congrFun
    (unweightedVectorThree_openVelocityWeightedH3State solution t) component
  have hmode := openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode
    solution t component k
  exact (congrArg (fun coeff ↦ coeff.1 k) hunweighted |>.trans hmode).symm

/-- The actual nonlinear vorticity source is the negative native raw `H²` curl coefficient. -/
theorem vorticityNonlinearMode_eq_neg_nativePeriodicCurl
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    vorticityNonlinearMode solution t k =
      -(fun output ↦ nativePeriodicCurlComponentFourier 2 (by norm_num)
        (sharpNonlinearSource (openVelocityWeightedH3State solution t)) output k) := by
  rw [vorticityNonlinearMode_eq_unweightedSharpNonlinearSourceCoefficient]
  congr 1
  funext output
  rw [nativePeriodicCurlComponentFourier_apply]
  rfl

/-- The exact depth work has a cubic native weighted-`H³` bound independent of depth and its
finite output aperture. -/
theorem norm_actualLinearMultiplierCoefficientWork_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    ‖linearMultiplierCoefficientWork
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)
        (vorticityNonlinearMode solution t)‖ ≤
      (2519424 * periodicH3EmbeddingConstant) *
        ‖openVelocityWeightedH3State solution t‖ ^ 3 := by
  let state := openVelocityWeightedH3State solution t
  let source := sharpNonlinearSource state
  let leftCurl : SpatialFrequency → ComplexVector := fun k output ↦
    nativePeriodicCurlComponentFourier 3 (by norm_num) state output k
  let rightCurl : SpatialFrequency → ComplexVector := fun k output ↦
    nativePeriodicCurlComponentFourier 2 (by norm_num) source output k
  have hmultiplier : ∀ k ∈ smoothDyadicBandNativeAperture depth,
      ‖smoothDyadicCumulativeBoundaryMultiplier depth k‖ ≤ 1 := by
    intro k _hk
    rw [smoothDyadicCumulativeBoundaryMultiplier]
    have hcast :
      (NavierStokesDeLaValleePoussin.tensorValleePoussinWeight
          (NavierStokesDyadicHodgeScaleChain.dyadicHodgeParameter depth) k : ℂ) -
        (NavierStokesDeLaValleePoussin.tensorValleePoussinWeight
          (NavierStokesDyadicHodgeScaleChain.dyadicHodgeParameter 0) k : ℂ) =
        ((finiteDepthBoundaryWeight depth k : ℝ) : ℂ) := by
      simp [finiteDepthBoundaryWeight]
    rw [hcast]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      abs_finiteDepthBoundaryWeight_le_one depth k
  have hnative := norm_linearMultiplierCoefficientWork_nativeCurl_le
    3 2 (by norm_num) (by norm_num) state source
    (smoothDyadicCumulativeBoundaryMultiplier depth)
    (smoothDyadicBandNativeAperture depth) hmultiplier
  have hactual :
      linearMultiplierCoefficientWork
          (smoothDyadicCumulativeBoundaryMultiplier depth)
          (smoothDyadicBandNativeAperture depth)
          (openPeriodicVorticityFourierMode solution t)
          (vorticityNonlinearMode solution t) =
        -linearMultiplierCoefficientWork
          (smoothDyadicCumulativeBoundaryMultiplier depth)
          (smoothDyadicBandNativeAperture depth) leftCurl rightCurl := by
    rw [← linearMultiplierCoefficientWork_neg_right]
    congr 1
    · funext k
      exact openPeriodicVorticityFourierMode_eq_nativePeriodicCurl solution t k
    · funext k
      exact vorticityNonlinearMode_eq_neg_nativePeriodicCurl solution t k
  rw [hactual, norm_neg]
  calc
    ‖linearMultiplierCoefficientWork
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth) leftCurl rightCurl‖ ≤
      108 * ‖state‖ * ‖source‖ := hnative
    _ ≤ 108 * ‖state‖ *
        ((23328 * periodicH3EmbeddingConstant) * ‖state‖ ^ 2) := by
      dsimp only [source]
      exact mul_le_mul_of_nonneg_left (norm_sharpNonlinearSource_le state)
        (mul_nonneg (by norm_num) (norm_nonneg state))
    _ = (2519424 * periodicH3EmbeddingConstant) * ‖state‖ ^ 3 := by ring

/-! ## Compact-time chart and depth-independent domination -/

/-- The actual finite-depth work, extended continuously outside the addressed compact interval
by projection to its endpoints. -/
def compactActualLinearMultiplierCoefficientWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) (time : ℝ) : ℂ :=
  linearMultiplierCoefficientWork
    (smoothDyadicCumulativeBoundaryMultiplier depth)
    (smoothDyadicBandNativeAperture depth)
    (openPeriodicVorticityFourierMode solution
      (compactInteriorTime ha hab hbT time))
    (vorticityNonlinearMode solution
      (compactInteriorTime ha hab hbT time))

/-- The exact fixed-time cofinal receiver in the same compact endpoint-projection chart. -/
def compactCofinalLinearMultiplierWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) : ℂ :=
  completeCofinalLinearMultiplierWork solution
    (compactInteriorTime ha hab hbT time)

theorem continuous_actualLinearMultiplierCoefficientWork_time
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (depth : ℕ) :
    Continuous (fun t : Ioo 0 T ↦
      linearMultiplierCoefficientWork
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)
        (vorticityNonlinearMode solution t)) := by
  unfold linearMultiplierCoefficientWork
  apply continuous_finsetSum
  intro k _hk
  apply Continuous.mul continuous_const
  have hleft :=
    NavierStokesPhaseLocalLowFaceIntegrability.continuous_openPeriodicVorticityFourierMode
      solution k
  have hright := continuous_vorticityNonlinearMode solution k
  unfold complexVectorSymmetricPhasePairing complexVectorHermitianPairing
  apply Continuous.mul continuous_const
  apply Continuous.add <;>
    apply continuous_finsetSum <;> intro component _hcomponent
  · exact (Complex.continuous_conj.comp
      ((continuous_apply component).comp hleft)).mul
        ((continuous_apply component).comp hright)
  · exact (Complex.continuous_conj.comp
      ((continuous_apply component).comp hright)).mul
        ((continuous_apply component).comp hleft)

theorem continuous_compactActualLinearMultiplierCoefficientWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    Continuous (compactActualLinearMultiplierCoefficientWork
      solution ha hab hbT depth) :=
  (continuous_actualLinearMultiplierCoefficientWork_time solution depth).comp
    (continuous_compactInteriorTime ha hab hbT)

/-- Every compactly projected native state is bounded by the norm of the actual continuous
weighted-`H³` chart. -/
theorem norm_openVelocityWeightedH3State_compactInteriorTime_le_chart
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) :
    ‖openVelocityWeightedH3State solution
        (compactInteriorTime ha hab hbT time)‖ ≤
      ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ := by
  let clamped : Icc a b := Set.projIcc a b hab time
  have hchart := ContinuousMap.norm_coe_le_norm
    (compactOpenVelocityWeightedH3StateChart solution ha hab hbT) clamped
  change ‖openVelocityWeightedH3State solution
      ⟨clamped.1, ha.trans_le clamped.2.1, clamped.2.2.trans_lt hbT⟩‖ ≤ _ at hchart
  convert hchart using 1
  congr 2

/-- One constant compact-time service dominates both the finite work and its cofinal limit. -/
def compactCompleteLinearWorkErrorBound
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  2 * (2519424 * periodicH3EmbeddingConstant) *
    ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3

theorem norm_compactActualLinearMultiplierCoefficientWork_le_halfBound
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) (time : ℝ) :
    ‖compactActualLinearMultiplierCoefficientWork
        solution ha hab hbT depth time‖ ≤
      (2519424 * periodicH3EmbeddingConstant) *
        ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3 := by
  have hactual := norm_actualLinearMultiplierCoefficientWork_le solution
    (compactInteriorTime ha hab hbT time) depth
  have hstate := norm_openVelocityWeightedH3State_compactInteriorTime_le_chart
    solution ha hab hbT time
  exact hactual.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hstate 3)
    (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg))

theorem norm_compactCofinalLinearMultiplierWork_le_halfBound
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) :
    ‖compactCofinalLinearMultiplierWork solution ha hab hbT time‖ ≤
      (2519424 * periodicH3EmbeddingConstant) *
        ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3 := by
  let interior := compactInteriorTime ha hab hbT time
  let bound := (2519424 * periodicH3EmbeddingConstant) *
    ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3
  have hlimit := tendsto_actualLinearMultiplierCoefficientWork_atTop solution interior
  have hnorm : Tendsto
      (fun depth ↦ ‖compactActualLinearMultiplierCoefficientWork
        solution ha hab hbT depth time‖) atTop
      (nhds ‖compactCofinalLinearMultiplierWork solution ha hab hbT time‖) := by
    exact continuous_norm.tendsto _ |>.comp hlimit
  exact le_of_tendsto hnorm (Filter.Eventually.of_forall fun depth ↦
    norm_compactActualLinearMultiplierCoefficientWork_le_halfBound
      solution ha hab hbT depth time)

theorem norm_compactLinearWorkError_le
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) (time : ℝ) :
    ‖compactActualLinearMultiplierCoefficientWork solution ha hab hbT depth time -
        compactCofinalLinearMultiplierWork solution ha hab hbT time‖ ≤
      compactCompleteLinearWorkErrorBound solution ha hab hbT := by
  calc
    _ ≤ ‖compactActualLinearMultiplierCoefficientWork
          solution ha hab hbT depth time‖ +
        ‖compactCofinalLinearMultiplierWork
          solution ha hab hbT time‖ := norm_sub_le _ _
    _ ≤ (2519424 * periodicH3EmbeddingConstant) *
          ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3 +
        (2519424 * periodicH3EmbeddingConstant) *
          ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ ^ 3 :=
      add_le_add
        (norm_compactActualLinearMultiplierCoefficientWork_le_halfBound
          solution ha hab hbT depth time)
        (norm_compactCofinalLinearMultiplierWork_le_halfBound
          solution ha hab hbT time)
    _ = compactCompleteLinearWorkErrorBound solution ha hab hbT := by
      unfold compactCompleteLinearWorkErrorBound
      ring

theorem tendsto_compactLinearWorkError_zero
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) :
    Tendsto
      (fun depth ↦ ‖compactActualLinearMultiplierCoefficientWork
          solution ha hab hbT depth time -
        compactCofinalLinearMultiplierWork solution ha hab hbT time‖)
      atTop (nhds 0) := by
  have hlimit := tendsto_actualLinearMultiplierCoefficientWork_atTop solution
    (compactInteriorTime ha hab hbT time)
  have hconst : Tendsto
      (fun _depth : ℕ ↦ compactCofinalLinearMultiplierWork
        solution ha hab hbT time) atTop
      (nhds (compactCofinalLinearMultiplierWork solution ha hab hbT time)) :=
    tendsto_const_nhds
  have hsub := hlimit.sub hconst
  have hsubZero : Tendsto
      (fun depth ↦
        linearMultiplierCoefficientWork
            (smoothDyadicCumulativeBoundaryMultiplier depth)
            (smoothDyadicBandNativeAperture depth)
            (openPeriodicVorticityFourierMode solution
              (compactInteriorTime ha hab hbT time))
            (vorticityNonlinearMode solution
              (compactInteriorTime ha hab hbT time)) -
          compactCofinalLinearMultiplierWork solution ha hab hbT time)
      atTop (nhds (0 : ℂ)) := by
    simpa [compactCofinalLinearMultiplierWork] using hsub
  have hnorm := (continuous_norm.tendsto (0 : ℂ)).comp hsubZero
  simpa [Function.comp_def, compactActualLinearMultiplierCoefficientWork,
    compactCofinalLinearMultiplierWork] using hnorm

theorem measurable_compactCofinalLinearMultiplierWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Measurable (compactCofinalLinearMultiplierWork solution ha hab hbT) := by
  apply measurable_of_tendsto_metrizable
    (f := fun depth ↦ compactActualLinearMultiplierCoefficientWork
      solution ha hab hbT depth)
  · intro depth
    exact (continuous_compactActualLinearMultiplierCoefficientWork
      solution ha hab hbT depth).measurable
  · rw [tendsto_pi_nhds]
    intro time
    exact tendsto_actualLinearMultiplierCoefficientWork_atTop solution
      (compactInteriorTime ha hab hbT time)

/-! ## Strong compact-time passage -/

/-- **Strong compact-time depth-cofinal passage.**  The actual cumulative linear work converges
in time `L¹([a,b])` to the exact cofinal receiver, retaining the scale-zero stretching and
transport boundaries occurring in `completeCofinalLinearMultiplierWork`. -/
theorem tendsto_integral_norm_compactLinearWorkError_zero
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    Tendsto
      (fun depth ↦ ∫ time in a..b,
        ‖compactActualLinearMultiplierCoefficientWork
            solution ha hab hbT depth time -
          compactCofinalLinearMultiplierWork solution ha hab hbT time‖)
      atTop (nhds 0) := by
  let bound : ℝ → ℝ := fun _time ↦
    compactCompleteLinearWorkErrorBound solution ha hab hbT
  have hcofinal := measurable_compactCofinalLinearMultiplierWork
    solution ha hab hbT
  have hdominated := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := a) (b := b) (μ := volume) (l := atTop)
    (F := fun depth time ↦
      ‖compactActualLinearMultiplierCoefficientWork
          solution ha hab hbT depth time -
        compactCofinalLinearMultiplierWork solution ha hab hbT time‖)
    (f := fun _time ↦ (0 : ℝ)) bound
  have hpassage := hdominated
    (Filter.Eventually.of_forall fun depth ↦
      (((continuous_compactActualLinearMultiplierCoefficientWork
          solution ha hab hbT depth).measurable.sub hcofinal).norm
        |>.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun depth ↦ ae_of_all _ fun time _htime ↦ by
      simpa only [Real.norm_eq_abs, abs_norm, bound] using
        norm_compactLinearWorkError_le solution ha hab hbT depth time)
    (continuous_const.intervalIntegrable _ _)
    (ae_of_all _ fun time _htime ↦
      tendsto_compactLinearWorkError_zero solution ha hab hbT time)
  simpa using hpassage

section Audit

#print axioms norm_linearMultiplierCoefficientWork_nativeCurl_le
#print axioms norm_actualLinearMultiplierCoefficientWork_le
#print axioms tendsto_integral_norm_compactLinearWorkError_zero

end Audit

end Soma.Holonics.Millennium.NavierStokesCompleteLinearWorkCompactL1
