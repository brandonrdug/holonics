import ElementaryHolonics.Millennium.NavierStokesWeightedJointSmoothnessScale

/-!
# Joint Fourier smoothness from coherent native path lifts

**[open]** This owner closes the bounded operator-valued Fourier evaluation passage needed by the
joint bridge.  It retains the native coefficient population, proves equality with the actual
high-order reconstruction, and returns the exact summable first-mode derivative envelope.  The
remaining operator-valued derivative summation and finite-order `ContDiff` induction are not
asserted here.
-/

noncomputable section

open Function Set Filter
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedJointFourierSmoothnessBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessScale
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Summable operator-valued Fourier evaluation -/

/-- The bounded high-order coefficient receiver, viewed over the real scalar field used by the
spacetime calculus. -/
def highOrderVectorCoefficientCLM
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency) :
    PeriodicVectorWeightedSobolev order →L[ℝ] ℂ :=
  (weightedVectorSobolevCoefficientCLM order component k).restrictScalars ℝ

@[simp]
theorem highOrderVectorCoefficientCLM_apply
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency)
    (state : PeriodicVectorWeightedSobolev order) :
    highOrderVectorCoefficientCLM order component k state =
      (weightedSobolevCoefficients order (state component)).1 k :=
  rfl

/-- Exact coefficient evaluation has the reciprocal square-root Sobolev weight as an operator
norm bound. -/
theorem norm_highOrderVectorCoefficientCLM_le
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency) :
    ‖highOrderVectorCoefficientCLM order component k‖ ≤
      (Real.sqrt (periodicSobolevWeight order k))⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro state
  exact norm_weightedSobolevCoefficients_apply_le
    order state component k

/-- Every order at least six has coefficient operator norm dominated by the common summable
reciprocal `H³` receiver. -/
theorem inv_sqrt_periodicSobolevWeight_le_weight_three_inv
    {order : ℕ} (horder : 6 ≤ order) (k : SpatialFrequency) :
    (Real.sqrt (periodicSobolevWeight order k))⁻¹ ≤
      (periodicSobolevWeight 3 k)⁻¹ := by
  rw [← inv_sqrt_weight_six_eq_weight_three_inv]
  apply (inv_le_inv₀
    (Real.sqrt_pos.2 (periodicSobolevWeight_pos order k))
    (Real.sqrt_pos.2 (periodicSobolevWeight_pos 6 k))).2
  exact Real.sqrt_le_sqrt (periodicSobolevWeight_mono horder k)

/-- One complete Fourier evaluation mode as a bounded real-linear receiver of the native
high-order state. -/
def highOrderFourierEvaluationModeCLM
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency) (x : Space) :
    PeriodicVectorWeightedSobolev order →L[ℝ] ℂ :=
  euclideanFourierCharacter k x •
    highOrderVectorCoefficientCLM order component k

theorem norm_highOrderFourierEvaluationModeCLM_le
    {order : ℕ} (horder : 6 ≤ order) (component : Fin 3)
    (k : SpatialFrequency) (x : Space) :
    ‖highOrderFourierEvaluationModeCLM order component k x‖ ≤
      (periodicSobolevWeight 3 k)⁻¹ := by
  rw [highOrderFourierEvaluationModeCLM, norm_smul,
    norm_euclideanFourierCharacter, one_mul]
  exact (norm_highOrderVectorCoefficientCLM_le order component k).trans
    (inv_sqrt_periodicSobolevWeight_le_weight_three_inv horder k)

/-- The complete operator-valued Fourier evaluation population is summable at every spatial
receiver once six native orders are retained. -/
theorem summable_highOrderFourierEvaluationModeCLM
    {order : ℕ} (horder : 6 ≤ order) (component : Fin 3) (x : Space) :
    Summable (fun k : SpatialFrequency ↦
      highOrderFourierEvaluationModeCLM order component k x) :=
  Summable.of_norm_bounded summable_periodicSobolevWeight_three_inv
    (fun k ↦ norm_highOrderFourierEvaluationModeCLM_le
      horder component k x)

/-- Parameterized reconstruction evaluation.  The `r` excess orders are retained above the
common order-six absolute-summation aperture. -/
def reconstructedHighOrderComplexEvaluationCLM
    (r : ℕ) (component : Fin 3) (x : Space) :
    PeriodicVectorWeightedSobolev (r + 6) →L[ℝ] ℂ :=
  ∑' k : SpatialFrequency,
    highOrderFourierEvaluationModeCLM (r + 6) component k x

/-- Applying the parameterized evaluation operator returns the actual high-order Fourier
reconstruction, with no replacement of the native coefficient lineage. -/
theorem reconstructedHighOrderComplexEvaluationCLM_apply
    (r : ℕ) (component : Fin 3) (x : Space)
    (state : PeriodicVectorWeightedSobolev (r + 6)) :
    reconstructedHighOrderComplexEvaluationCLM r component x state =
      reconstructedHigherOrderComplexComponent (r + 3) state component x := by
  rw [reconstructedHighOrderComplexEvaluationCLM,
    show (∑' k : SpatialFrequency,
        highOrderFourierEvaluationModeCLM (r + 6) component k x) state =
      ∑' k : SpatialFrequency,
        highOrderFourierEvaluationModeCLM (r + 6) component k x state by
      exact (ContinuousLinearMap.apply ℝ ℂ state).map_tsum
        (summable_highOrderFourierEvaluationModeCLM
          (by omega : 6 ≤ r + 6) component x)]
  change (∑' k : SpatialFrequency,
      euclideanFourierCharacter k x *
        (weightedSobolevCoefficients (r + 6) (state component)).1 k) = _
  change (∑' k : SpatialFrequency,
      euclideanFourierCharacter k x *
        (weightedSobolevCoefficients (r + 6) (state component)).1 k) =
    reconstructedTorusComplexComponent
      (finiteOrderVectorDerivativeToThree
        (r + 3) 0 (Nat.zero_le _) (fun i ↦ Fin.elim0 i) state)
      component (euclideanToSpatialTorus x)
  rw [reconstructedTorusComplexComponent_apply]
  apply tsum_congr
  intro k
  rw [euclideanFourierCharacter_eq_mFourier]
  change UnitAddTorus.mFourier k (euclideanToSpatialTorus x) *
      (weightedSobolevCoefficients (r + 6) (state component)).1 k =
    (weightedSobolevCoefficients 3
      (finiteOrderVectorDerivativeToThree
        (r + 3) 0 (Nat.zero_le _) (fun i ↦ Fin.elim0 i) state component)).1 k *
      UnitAddTorus.mFourier k (euclideanToSpatialTorus x)
  rw [weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply]
  simp [orderedDerivativeMultiplier]
  ring

/-- The operator-valued evaluation field is continuous at every retained excess order. -/
theorem continuous_reconstructedHighOrderComplexEvaluationCLM
    (r : ℕ) (component : Fin 3) :
    Continuous (reconstructedHighOrderComplexEvaluationCLM r component) := by
  apply continuous_tsum
  · intro k
    exact (continuous_iff_continuousAt.mpr (fun x ↦
      (hasFDerivAt_euclideanFourierCharacter k x).continuousAt)).smul
        continuous_const
  · exact summable_periodicSobolevWeight_three_inv
  · intro k x
    exact norm_highOrderFourierEvaluationModeCLM_le
      (by omega : 6 ≤ r + 6) component k x

/-! ## One spatial derivative of the operator-valued series -/

/-- Spending one adjacent native order dominates one coordinate character derivative. -/
theorem two_pi_abs_mul_inv_sqrt_weight_le_pred
    (order : ℕ) (hpositive : 1 ≤ order)
    (coordinate : Fin 3) (k : SpatialFrequency) :
    (2 * Real.pi * |(k coordinate : ℝ)|) *
        (Real.sqrt (periodicSobolevWeight order k))⁻¹ ≤
      (Real.sqrt (periodicSobolevWeight (order - 1) k))⁻¹ := by
  have hhigh : 0 < Real.sqrt (periodicSobolevWeight order k) :=
    Real.sqrt_pos.2 (periodicSobolevWeight_pos order k)
  have hlow : 0 < Real.sqrt (periodicSobolevWeight (order - 1) k) :=
    Real.sqrt_pos.2 (periodicSobolevWeight_pos (order - 1) k)
  rw [← div_eq_mul_inv, ← one_div]
  rw [div_le_div_iff₀ hhigh hlow, one_mul]
  apply (sq_le_sq₀
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) (abs_nonneg _))
      (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (periodicSobolevWeight_nonneg _ _),
    Real.sq_sqrt (periodicSobolevWeight_nonneg _ _)]
  have hweight := periodicSobolevWeight_pred_mul_coordinate_symbol_sq_le
    order hpositive coordinate k
  calc
    (2 * Real.pi * |(k coordinate : ℝ)|) ^ 2 *
        periodicSobolevWeight (order - 1) k =
      periodicSobolevWeight (order - 1) k *
        ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) := by
          rw [mul_pow, sq_abs]
          ring
    _ ≤ periodicSobolevWeight order k := hweight

/-- After one derivative, every order at least seven is still dominated by the common summable
order-three receiver. -/
theorem two_pi_abs_mul_inv_sqrt_weight_le_weight_three_inv
    {order : ℕ} (horder : 7 ≤ order)
    (coordinate : Fin 3) (k : SpatialFrequency) :
    (2 * Real.pi * |(k coordinate : ℝ)|) *
        (Real.sqrt (periodicSobolevWeight order k))⁻¹ ≤
      (periodicSobolevWeight 3 k)⁻¹ :=
  (two_pi_abs_mul_inv_sqrt_weight_le_pred
    order (by omega) coordinate k).trans
      (inv_sqrt_periodicSobolevWeight_le_weight_three_inv
        (by omega : 6 ≤ order - 1) k)

/-- The exact derivative of one operator-valued Fourier evaluation mode. -/
def highOrderFourierEvaluationModeFDeriv
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency) (x : Space) :
    Space →L[ℝ] (PeriodicVectorWeightedSobolev order →L[ℝ] ℂ) :=
  (euclideanFourierCharacterFDeriv k x).smulRight
    (highOrderVectorCoefficientCLM order component k)

theorem hasFDerivAt_highOrderFourierEvaluationModeCLM
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency) (x : Space) :
    HasFDerivAt
      (highOrderFourierEvaluationModeCLM order component k)
      (highOrderFourierEvaluationModeFDeriv order component k x) x := by
  exact (hasFDerivAt_euclideanFourierCharacter k x).smul_const
    (highOrderVectorCoefficientCLM order component k)

/-- The complete coordinate-frequency envelope spends one order and leaves three copies of the
common summable receiver. -/
theorem two_pi_sum_abs_mul_inv_sqrt_weight_le
    {order : ℕ} (horder : 7 ≤ order) (k : SpatialFrequency) :
    (2 * Real.pi * ∑ coordinate : Fin 3, |(k coordinate : ℝ)|) *
        (Real.sqrt (periodicSobolevWeight order k))⁻¹ ≤
      3 * (periodicSobolevWeight 3 k)⁻¹ := by
  calc
    (2 * Real.pi * ∑ coordinate : Fin 3, |(k coordinate : ℝ)|) *
        (Real.sqrt (periodicSobolevWeight order k))⁻¹ =
      ∑ coordinate : Fin 3,
        (2 * Real.pi * |(k coordinate : ℝ)|) *
          (Real.sqrt (periodicSobolevWeight order k))⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ _coordinate : Fin 3,
        (periodicSobolevWeight 3 k)⁻¹ := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact two_pi_abs_mul_inv_sqrt_weight_le_weight_three_inv
        horder coordinate k
    _ = 3 * (periodicSobolevWeight 3 k)⁻¹ := by
      simp

/-- One complete mode derivative is bounded by three copies of the common reciprocal `H³`
receiver. -/
theorem norm_highOrderFourierEvaluationModeFDeriv_le
    {order : ℕ} (horder : 7 ≤ order) (component : Fin 3)
    (k : SpatialFrequency) (x : Space) :
    ‖highOrderFourierEvaluationModeFDeriv order component k x‖ ≤
      3 * (periodicSobolevWeight 3 k)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num)
      (inv_nonneg.mpr (periodicSobolevWeight_nonneg 3 k)))
  intro direction
  change ‖(euclideanFourierCharacterFDeriv k x direction) •
      highOrderVectorCoefficientCLM order component k‖ ≤
    (3 * (periodicSobolevWeight 3 k)⁻¹) * ‖direction‖
  rw [norm_smul]
  calc
    ‖euclideanFourierCharacterFDeriv k x direction‖ *
        ‖highOrderVectorCoefficientCLM order component k‖ ≤
      (‖euclideanFourierCharacterFDeriv k x‖ * ‖direction‖) *
        (Real.sqrt (periodicSobolevWeight order k))⁻¹ := by
      exact mul_le_mul
        ((euclideanFourierCharacterFDeriv k x).le_opNorm direction)
        (norm_highOrderVectorCoefficientCLM_le order component k)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖euclideanFourierCharacterFDeriv k x‖ *
        (Real.sqrt (periodicSobolevWeight order k))⁻¹) * ‖direction‖ := by
      ring
    _ ≤ (2 * Real.pi * ∑ coordinate : Fin 3, |(k coordinate : ℝ)|) *
        (Real.sqrt (periodicSobolevWeight order k))⁻¹ * ‖direction‖ := by
      gcongr
      exact norm_euclideanFourierCharacterFDeriv_le k x
    _ ≤ (3 * (periodicSobolevWeight 3 k)⁻¹) * ‖direction‖ := by
      exact mul_le_mul_of_nonneg_right
        (two_pi_sum_abs_mul_inv_sqrt_weight_le horder k) (norm_nonneg _)

end Soma.Holonics.Millennium.NavierStokesWeightedJointFourierSmoothnessBridge
