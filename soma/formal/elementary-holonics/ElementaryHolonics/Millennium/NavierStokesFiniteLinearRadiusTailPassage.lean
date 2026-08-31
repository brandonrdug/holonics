import ElementaryHolonics.Millennium.NavierStokesFiniteLinearSignedWorkTailLedger
import ElementaryHolonics.Millennium.NavierStokesOpenCompactWeightedPath
import ElementaryHolonics.Millennium.NavierStokesH3BilinearNorm
import ElementaryHolonics.Millennium.NavierStokesH3LerayBilinearNorm

/-!
# Compact interaction-radius passage for the finite linear work

**[proved-derived; formal-checked]** For every compact strict-interior time interval and fixed
finite scale depth, the literal actual-minus-pair-compatible interaction-radius tail converges to
zero strongly in time `L¹`.  The proof derives a radius-independent cubic bound from the actual
continuous weighted `H³` path and then applies dominated convergence; it assumes no terminal or
critical-vorticity receiver.

The physical output tail is separated into two exact populations.  Interaction radius can remove
only the cofinal source tail.  A distinct fixed output-receiver defect remains, and its exact
compact-slab closure obligation is named without being postulated or discharged here.
-/

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped BigOperators Interval ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteLinearSignedWorkTailLedger
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkPhysicalJoin
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## A radius-independent finite-convolution envelope -/

/-- Every raw coefficient of an `H²` carrier is controlled by its weighted coefficient norm. -/
theorem norm_periodicSobolevTwoCoefficient_le
    (coeff : PeriodicSobolevCoefficients 2) (k : SpatialFrequency) :
    ‖coeff.1 k‖ ≤ periodicH2CoefficientNorm coeff := by
  let weighted := weightedAbsoluteCoefficientTwo coeff
  calc
    ‖coeff.1 k‖ ≤ Real.sqrt (periodicSobolevWeight 2 k) * ‖coeff.1 k‖ := by
      exact le_mul_of_one_le_left (norm_nonneg _)
        (Real.one_le_sqrt.mpr (one_le_periodicSobolevWeight 2 k))
    _ = ‖weighted k‖ := by
      simp only [weighted, weightedAbsoluteCoefficientTwo, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sobolevTwoAmplitude_nonneg k) (norm_nonneg _))]
      rfl
    _ ≤ ‖weighted‖ := lp.norm_apply_le_norm (by norm_num) weighted k
    _ = periodicH2CoefficientNorm coeff := rfl

/-- Every raw coefficient of an `H³` carrier is controlled by its weighted coefficient norm. -/
theorem norm_periodicSobolevThreeCoefficient_le
    (coeff : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    ‖coeff.1 k‖ ≤ periodicH3CoefficientNorm coeff := by
  let weighted := weightedAbsoluteCoefficient coeff
  calc
    ‖coeff.1 k‖ ≤ Real.sqrt (periodicSobolevWeight 3 k) * ‖coeff.1 k‖ := by
      exact le_mul_of_one_le_left (norm_nonneg _)
        (Real.one_le_sqrt.mpr (one_le_periodicSobolevWeight 3 k))
    _ = ‖weighted k‖ := by
      simp only [weighted, weightedAbsoluteCoefficient, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sobolevThreeAmplitude_nonneg k) (norm_nonneg _))]
      rfl
    _ ≤ ‖weighted‖ := lp.norm_apply_le_norm (by norm_num) weighted k
    _ = periodicH3CoefficientNorm coeff := rfl

/-- A differentiated coefficient is controlled by the original exact `H³` norm. -/
theorem norm_periodicSobolevThreeDerivative_apply_le
    (coordinate : Fin 3) (coeff : PeriodicSobolevCoefficients 3)
    (k : SpatialFrequency) :
    ‖periodicSobolevThreeDerivative coordinate coeff k‖ ≤
      periodicH3CoefficientNorm coeff := by
  calc
    ‖periodicSobolevThreeDerivative coordinate coeff k‖ =
        ‖(periodicSobolevThreeDerivativeIntoTwo coordinate coeff).1 k‖ := rfl
    _ ≤ periodicH2CoefficientNorm
        (periodicSobolevThreeDerivativeIntoTwo coordinate coeff) :=
      norm_periodicSobolevTwoCoefficient_le _ k
    _ ≤ periodicH3CoefficientNorm coeff :=
      periodicH2CoefficientNorm_derivativeIntoTwo_le coordinate coeff

private theorem complexAdvectiveInteraction_state_apply
    (state : PeriodicVectorSobolevThree) (k p : SpatialFrequency)
    (output : Fin 3) :
    complexAdvectiveInteraction p (transportedFrequencyAt k p)
        (fun component ↦ (state component).1 p)
        (fun component ↦ (state component).1 (transportedFrequencyAt k p)) output =
      ∑ coordinate : Fin 3,
        (state coordinate).1 p *
          periodicSobolevThreeDerivative coordinate (state output)
            (transportedFrequencyAt k p) := by
  simp only [complexAdvectiveInteraction, complexDot, dotProduct,
    Pi.smul_apply, smul_eq_mul, periodicSobolevThreeDerivative_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  simp only [complexFrequencyVector]
  ring

/-- A finite advective population is bounded independently of its aperture.  The payment is the
complete `H³ → ℓ¹` embedding on the advecting pin and one `H³` derivative payment on the paired
pin. -/
theorem norm_finiteAdvectiveCoefficient_state_le
    (state : PeriodicVectorSobolevThree)
    (aperture : Finset SpatialFrequency) (k : SpatialFrequency) :
    ‖finiteAdvectiveCoefficient aperture
        (fun frequency component ↦ (state component).1 frequency)
        (fun frequency component ↦ (state component).1 frequency) k‖ ≤
      periodicH3EmbeddingConstant *
        (∑ component : Fin 3, periodicH3CoefficientNorm (state component)) ^ 2 := by
  rw [pi_norm_le_iff_of_nonempty]
  intro output
  calc
    ‖finiteAdvectiveCoefficient aperture
        (fun frequency component ↦ (state component).1 frequency)
        (fun frequency component ↦ (state component).1 frequency) k output‖ ≤
      ∑ p ∈ aperture, ∑ coordinate : Fin 3,
        ‖(state coordinate).1 p‖ *
          ‖periodicSobolevThreeDerivative coordinate (state output)
            (transportedFrequencyAt k p)‖ := by
      unfold finiteAdvectiveCoefficient
      rw [Finset.sum_apply]
      calc
        ‖∑ p ∈ aperture,
            complexAdvectiveInteraction p (transportedFrequencyAt k p)
              (fun component ↦ (state component).1 p)
              (fun component ↦ (state component).1 (transportedFrequencyAt k p)) output‖ ≤
            ∑ p ∈ aperture,
              ‖complexAdvectiveInteraction p (transportedFrequencyAt k p)
                (fun component ↦ (state component).1 p)
                (fun component ↦ (state component).1 (transportedFrequencyAt k p)) output‖ :=
          norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro p _hp
          rw [complexAdvectiveInteraction_state_apply]
          simpa only [norm_mul] using (norm_sum_le Finset.univ
            (fun coordinate : Fin 3 ↦
              (state coordinate).1 p *
                periodicSobolevThreeDerivative coordinate (state output)
                  (transportedFrequencyAt k p)))
    _ ≤ ∑ p ∈ aperture, ∑ coordinate : Fin 3,
        ‖(state coordinate).1 p‖ * periodicH3CoefficientNorm (state output) := by
      apply Finset.sum_le_sum
      intro p _hp
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      exact mul_le_mul_of_nonneg_left
        (norm_periodicSobolevThreeDerivative_apply_le coordinate
          (state output) (transportedFrequencyAt k p)) (norm_nonneg _)
    _ = ∑ coordinate : Fin 3,
        (∑ p ∈ aperture, ‖(state coordinate).1 p‖) *
          periodicH3CoefficientNorm (state output) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      rw [Finset.sum_mul]
    _ ≤ ∑ coordinate : Fin 3,
        coefficientL1Mass (state coordinate) *
          periodicH3CoefficientNorm (state output) := by
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      apply mul_le_mul_of_nonneg_right _
        (periodicH3CoefficientNorm_nonneg (state output))
      exact (summable_norm_periodicSobolevThreeCoefficient
        (state coordinate)).sum_le_tsum aperture (fun p _hp ↦ norm_nonneg _)
    _ ≤ ∑ coordinate : Fin 3,
        (periodicH3EmbeddingConstant *
          periodicH3CoefficientNorm (state coordinate)) *
            periodicH3CoefficientNorm (state output) := by
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      exact mul_le_mul_of_nonneg_right
        (coefficientL1Mass_le_periodicH3EmbeddingConstant_mul (state coordinate))
        (periodicH3CoefficientNorm_nonneg (state output))
    _ ≤ periodicH3EmbeddingConstant *
        (∑ component : Fin 3, periodicH3CoefficientNorm (state component)) ^ 2 := by
      let total := ∑ component : Fin 3, periodicH3CoefficientNorm (state component)
      have houtput : periodicH3CoefficientNorm (state output) ≤ total :=
        Finset.single_le_sum
          (fun component _ ↦ periodicH3CoefficientNorm_nonneg (state component))
          (Finset.mem_univ output)
      have htotal : 0 ≤ total := Finset.sum_nonneg fun component _ ↦
        periodicH3CoefficientNorm_nonneg (state component)
      calc
        (∑ coordinate : Fin 3,
            (periodicH3EmbeddingConstant *
              periodicH3CoefficientNorm (state coordinate)) *
                periodicH3CoefficientNorm (state output)) =
            periodicH3EmbeddingConstant * total *
              periodicH3CoefficientNorm (state output) := by
          rw [Finset.mul_sum]
          rw [Finset.sum_mul]
        _ ≤ periodicH3EmbeddingConstant * total * total := by
          exact mul_le_mul_of_nonneg_left houtput
            (mul_nonneg periodicH3EmbeddingConstant_nonneg htotal)
        _ = periodicH3EmbeddingConstant * total ^ 2 := by ring

/-- The symmetric complex phase receiver costs at most three products in the ambient sup norm. -/
theorem norm_complexVectorSymmetricPhasePairing_le
    (left right : ComplexVector) :
    ‖complexVectorSymmetricPhasePairing left right‖ ≤ 3 * ‖left‖ * ‖right‖ := by
  unfold complexVectorSymmetricPhasePairing complexVectorHermitianPairing
  have hforward :
      ‖∑ component : Fin 3, starRingEnd ℂ (left component) * right component‖ ≤
        ∑ _component : Fin 3, ‖left‖ * ‖right‖ := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun component _ ↦ by
      rw [norm_mul, starRingEnd_apply, norm_star]
      exact mul_le_mul (norm_le_pi_norm left component)
        (norm_le_pi_norm right component) (norm_nonneg _) (norm_nonneg _))
  have hreverse :
      ‖∑ component : Fin 3, starRingEnd ℂ (right component) * left component‖ ≤
        ∑ _component : Fin 3, ‖right‖ * ‖left‖ := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun component _ ↦ by
      rw [norm_mul, starRingEnd_apply, norm_star]
      exact mul_le_mul (norm_le_pi_norm right component)
        (norm_le_pi_norm left component) (norm_nonneg _) (norm_nonneg _))
  calc
    ‖(1 / 2 : ℂ) *
        ((∑ component : Fin 3, starRingEnd ℂ (left component) * right component) +
          ∑ component : Fin 3, starRingEnd ℂ (right component) * left component)‖ ≤
      (1 / 2 : ℝ) *
        ((∑ _component : Fin 3, ‖left‖ * ‖right‖) +
          ∑ _component : Fin 3, ‖right‖ * ‖left‖) := by
      rw [norm_mul]
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hhalf]
      exact mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add hforward hreverse)) (by norm_num)
    _ = 3 * ‖left‖ * ‖right‖ := by simp; ring

/-- The finite output-frequency work service; it depends on the fixed depth but not on the
interaction radius or time. -/
def finiteDepthRadiusIndependentWorkService (depth : ℕ) : ℝ :=
  ∑ k ∈ smoothDyadicBandNativeAperture depth,
    3 * periodicH3EmbeddingConstant * |finiteDepthBoundaryWeight depth k| *
      ‖frequencyCurlMultiplierCLM k‖ ^ 2

theorem finiteDepthRadiusIndependentWorkService_nonneg (depth : ℕ) :
    0 ≤ finiteDepthRadiusIndependentWorkService depth := by
  unfold finiteDepthRadiusIndependentWorkService
  exact Finset.sum_nonneg fun k _ ↦
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)
        (abs_nonneg _))
      (sq_nonneg _)

private theorem norm_periodicVectorCoefficientAt_le_total
    (state : PeriodicVectorSobolevThree) (k : SpatialFrequency) :
    ‖fun component ↦ (state component).1 k‖ ≤
      ∑ component : Fin 3, periodicH3CoefficientNorm (state component) := by
  rw [pi_norm_le_iff_of_nonempty]
  intro component
  exact (norm_periodicSobolevThreeCoefficient_le (state component) k).trans
    (Finset.single_le_sum
      (fun other _ ↦ periodicH3CoefficientNorm_nonneg (state other))
      (Finset.mem_univ component))

/-- Every finite pair-compatible boundary work is paid by one radius-independent cubic `H³`
service. -/
theorem norm_finitePairCompatibleBoundaryNonlinearWork_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    ‖finitePairCompatibleBoundaryNonlinearWork solution t depth radius‖ ≤
      finiteDepthRadiusIndependentWorkService depth *
        (∑ component : Fin 3,
          periodicH3CoefficientNorm (openVelocityH3State solution t component)) ^ 3 := by
  let state := openVelocityH3State solution t
  let total := ∑ component : Fin 3, periodicH3CoefficientNorm (state component)
  have htotal : 0 ≤ total := Finset.sum_nonneg fun component _ ↦
    periodicH3CoefficientNorm_nonneg (state component)
  unfold finitePairCompatibleBoundaryNonlinearWork
  calc
    ‖∑ k ∈ smoothDyadicBandNativeAperture depth,
        (finiteDepthBoundaryWeight depth k : ℂ) *
          complexVectorSymmetricPhasePairing
            (openPeriodicVorticityFourierMode solution t k)
            (finiteOpenVorticityNonlinearCoefficient solution t
              (pairCompatibleFrequencyAperture k radius) k)‖ ≤
      ∑ k ∈ smoothDyadicBandNativeAperture depth,
        3 * periodicH3EmbeddingConstant * |finiteDepthBoundaryWeight depth k| *
          ‖frequencyCurlMultiplierCLM k‖ ^ 2 * total ^ 3 := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _hk ↦ ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hmode : ‖openPeriodicVelocityFourierMode solution t k‖ ≤ total := by
        simpa only [state, openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode]
          using norm_periodicVectorCoefficientAt_le_total state k
      have hvorticity : ‖openPeriodicVorticityFourierMode solution t k‖ ≤
          ‖frequencyCurlMultiplierCLM k‖ * total := by
        rw [openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier,
          ← frequencyCurlMultiplierCLM_apply]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left hmode (norm_nonneg _))
      have hadvection :
          ‖finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture k radius)
              (openPeriodicVelocityFourierMode solution t)
              (openPeriodicVelocityFourierMode solution t) k‖ ≤
            periodicH3EmbeddingConstant * total ^ 2 := by
        simpa only [state, openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode]
          using norm_finiteAdvectiveCoefficient_state_le state
            (pairCompatibleFrequencyAperture k radius) k
      have hsource :
          ‖finiteOpenVorticityNonlinearCoefficient solution t
              (pairCompatibleFrequencyAperture k radius) k‖ ≤
            ‖frequencyCurlMultiplierCLM k‖ *
              (periodicH3EmbeddingConstant * total ^ 2) := by
        unfold finiteOpenVorticityNonlinearCoefficient
        rw [norm_neg, ← frequencyCurlMultiplierCLM_apply]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left hadvection (norm_nonneg _))
      have hpair := norm_complexVectorSymmetricPhasePairing_le
        (openPeriodicVorticityFourierMode solution t k)
        (finiteOpenVorticityNonlinearCoefficient solution t
          (pairCompatibleFrequencyAperture k radius) k)
      calc
        |finiteDepthBoundaryWeight depth k| *
            ‖complexVectorSymmetricPhasePairing
              (openPeriodicVorticityFourierMode solution t k)
              (finiteOpenVorticityNonlinearCoefficient solution t
                (pairCompatibleFrequencyAperture k radius) k)‖ ≤
          |finiteDepthBoundaryWeight depth k| *
            (3 * ‖openPeriodicVorticityFourierMode solution t k‖ *
              ‖finiteOpenVorticityNonlinearCoefficient solution t
                (pairCompatibleFrequencyAperture k radius) k‖) :=
          mul_le_mul_of_nonneg_left hpair (abs_nonneg _)
        _ ≤ |finiteDepthBoundaryWeight depth k| *
            (3 * (‖frequencyCurlMultiplierCLM k‖ * total) *
              (‖frequencyCurlMultiplierCLM k‖ *
                (periodicH3EmbeddingConstant * total ^ 2))) := by
          gcongr
        _ = 3 * periodicH3EmbeddingConstant * |finiteDepthBoundaryWeight depth k| *
              ‖frequencyCurlMultiplierCLM k‖ ^ 2 * total ^ 3 := by ring
    _ = finiteDepthRadiusIndependentWorkService depth * total ^ 3 := by
      unfold finiteDepthRadiusIndependentWorkService
      rw [Finset.sum_mul]
    _ = finiteDepthRadiusIndependentWorkService depth *
        (∑ component : Fin 3,
          periodicH3CoefficientNorm (openVelocityH3State solution t component)) ^ 3 := rfl

theorem sum_periodicH3CoefficientNorm_unweightedVectorThree_le
    (state : PeriodicVectorWeightedSobolev 3) :
    (∑ component : Fin 3,
      periodicH3CoefficientNorm (unweightedVectorThree state component)) ≤
        3 * ‖state‖ := by
  calc
    (∑ component : Fin 3,
        periodicH3CoefficientNorm (unweightedVectorThree state component)) =
      ∑ component : Fin 3, ‖state component‖ := by
        apply Finset.sum_congr rfl
        intro component _hcomponent
        exact periodicH3CoefficientNorm_weightedSobolevCoefficients (state component)
    _ ≤ ∑ _component : Fin 3, ‖state‖ := by
      apply Finset.sum_le_sum
      intro component _hcomponent
      exact norm_le_pi_norm state component
    _ = 3 * ‖state‖ := by simp

/-- One continuous compact-time native state chart used only to expose its actual uniform norm. -/
def compactOpenVelocityWeightedH3StateChart
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    C(Icc a b, PeriodicVectorWeightedSobolev 3) :=
  ⟨compactOpenVelocityWeightedH3State solution ha hbT,
    continuous_compactOpenVelocityWeightedH3State solution ha hab hbT⟩

/-- The compact interaction-radius tail has an explicit radius-independent constant majorant.
The factor two retains both endpoints of the actual-minus-finite difference. -/
def compactFiniteLinearRadiusTailBound
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  2 * finiteDepthRadiusIndependentWorkService depth *
    (3 * ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖) ^ 3

theorem compactFiniteLinearRadiusTailBound_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    0 ≤ compactFiniteLinearRadiusTailBound solution ha hab hbT depth := by
  unfold compactFiniteLinearRadiusTailBound
  exact mul_nonneg
    (mul_nonneg (by norm_num) (finiteDepthRadiusIndependentWorkService_nonneg depth))
    (pow_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) 3)

private theorem sum_openVelocityH3State_norm_le_compactChart
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (time : ℝ) :
    (∑ component : Fin 3,
      periodicH3CoefficientNorm
        (openVelocityH3State solution
          (compactInteriorTime ha hab hbT time) component)) ≤
      3 * ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ := by
  let clamped : Icc a b := Set.projIcc a b hab time
  let interior := compactInteriorTime ha hab hbT time
  let native := openVelocityWeightedH3State solution interior
  have hunweighted : unweightedVectorThree native = openVelocityH3State solution interior :=
    unweightedVectorThree_openVelocityWeightedH3State solution interior
  have hsum := sum_periodicH3CoefficientNorm_unweightedVectorThree_le native
  rw [hunweighted] at hsum
  have hnative : ‖native‖ ≤
      ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖ := by
    have hchart := ContinuousMap.norm_coe_le_norm
      (compactOpenVelocityWeightedH3StateChart solution ha hab hbT) clamped
    change ‖openVelocityWeightedH3State solution interior‖ ≤ _
    change ‖openVelocityWeightedH3State solution
      ⟨clamped.1, ha.trans_le clamped.2.1, clamped.2.2.trans_lt hbT⟩‖ ≤ _ at hchart
    convert hchart using 1
    congr 2
  exact hsum.trans (mul_le_mul_of_nonneg_left hnative (by norm_num))

private theorem norm_actualBoundaryWork_le_compactHalfBound
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) (time : ℝ) :
    |compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time| ≤
      finiteDepthRadiusIndependentWorkService depth *
        (3 * ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖) ^ 3 := by
  let t := compactInteriorTime ha hab hbT time
  let target := linearMultiplierCoefficientWork
    (smoothDyadicCumulativeBoundaryMultiplier depth)
    (smoothDyadicBandNativeAperture depth)
    (openPeriodicVorticityFourierMode solution t)
    (vorticityNonlinearMode solution t)
  let bound := finiteDepthRadiusIndependentWorkService depth *
    (3 * ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖) ^ 3
  have hlimit := tendsto_finitePairCompatibleBoundaryNonlinearWork solution t depth
  have hnorm : Tendsto
      (fun radius : ℕ ↦ ‖finitePairCompatibleBoundaryNonlinearWork
        solution t depth radius‖) atTop (nhds ‖target‖) := by
    exact continuous_norm.tendsto target |>.comp hlimit
  have hfinite : ∀ radius : ℕ,
      ‖finitePairCompatibleBoundaryNonlinearWork solution t depth radius‖ ≤ bound := by
    intro radius
    have hwork := norm_finitePairCompatibleBoundaryNonlinearWork_le
      solution t depth radius
    have hsum := sum_openVelocityH3State_norm_le_compactChart
      solution ha hab hbT time
    have hsum0 : 0 ≤ ∑ component : Fin 3,
        periodicH3CoefficientNorm (openVelocityH3State solution t component) :=
      Finset.sum_nonneg fun component _ ↦
        periodicH3CoefficientNorm_nonneg (openVelocityH3State solution t component)
    have hservice := finiteDepthRadiusIndependentWorkService_nonneg depth
    exact hwork.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hsum0 hsum 3) hservice)
  have htarget : ‖target‖ ≤ bound :=
    le_of_tendsto hnorm (Filter.Eventually.of_forall hfinite)
  calc
    |compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time| = |target.re| := rfl
    _ ≤ ‖target‖ := Complex.abs_re_le_norm target
    _ ≤ bound := htarget

theorem abs_compactFiniteLinearInteractionRadiusTailRate_le
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) (time : ℝ) :
    |compactFiniteLinearInteractionRadiusTailRate
        solution ha hab hbT depth radius time| ≤
      compactFiniteLinearRadiusTailBound solution ha hab hbT depth := by
  let half := finiteDepthRadiusIndependentWorkService depth *
    (3 * ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖) ^ 3
  have hactual := norm_actualBoundaryWork_le_compactHalfBound
    solution ha hab hbT depth time
  have hfiniteNorm := norm_finitePairCompatibleBoundaryNonlinearWork_le solution
    (compactInteriorTime ha hab hbT time) depth radius
  have hsum := sum_openVelocityH3State_norm_le_compactChart
    solution ha hab hbT time
  have hsum0 : 0 ≤ ∑ component : Fin 3,
      periodicH3CoefficientNorm
        (openVelocityH3State solution
          (compactInteriorTime ha hab hbT time) component) :=
    Finset.sum_nonneg fun component _ ↦
      periodicH3CoefficientNorm_nonneg
        (openVelocityH3State solution
          (compactInteriorTime ha hab hbT time) component)
  have hservice := finiteDepthRadiusIndependentWorkService_nonneg depth
  have hfinite :
      |compactFinitePairCompatibleBoundaryNonlinearWorkRate
        solution ha hab hbT depth radius time| ≤ half := by
    calc
      |compactFinitePairCompatibleBoundaryNonlinearWorkRate
          solution ha hab hbT depth radius time| ≤
        ‖finitePairCompatibleBoundaryNonlinearWork solution
          (compactInteriorTime ha hab hbT time) depth radius‖ :=
        Complex.abs_re_le_norm _
      _ ≤ finiteDepthRadiusIndependentWorkService depth *
          (∑ component : Fin 3,
            periodicH3CoefficientNorm
              (openVelocityH3State solution
                (compactInteriorTime ha hab hbT time) component)) ^ 3 := hfiniteNorm
      _ ≤ half := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hsum0 hsum 3) hservice
  unfold compactFiniteLinearInteractionRadiusTailRate
    compactFiniteLinearRadiusTailBound
  calc
    |compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time -
        compactFinitePairCompatibleBoundaryNonlinearWorkRate
          solution ha hab hbT depth radius time| ≤
      |compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time| +
        |compactFinitePairCompatibleBoundaryNonlinearWorkRate
          solution ha hab hbT depth radius time| := abs_sub _ _
    _ ≤ half + half := add_le_add hactual hfinite
    _ = 2 * finiteDepthRadiusIndependentWorkService depth *
        (3 * ‖compactOpenVelocityWeightedH3StateChart solution ha hab hbT‖) ^ 3 := by
      dsimp [half]
      ring

/-! ## Compact-time `L¹` radius passage -/

@[fun_prop]
theorem continuous_openPeriodicVelocityFourierMode_time
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (k : SpatialFrequency) :
    Continuous (fun t : Ioo 0 T ↦ openPeriodicVelocityFourierMode solution t k) := by
  have hvelocity : Continuous (fun t : Ioo 0 T ↦ velocityMode velocity k t.1) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (openPeriodicSolutionOn_hasDerivAt_velocityMode_unforced
      solution t.2 k).continuousAt.comp continuousAt_subtype_val
  apply hvelocity.congr
  intro t
  ext component
  exact velocityModeComponent_eq_openPeriodicVelocityFourierMode
    solution t k component

attribute [local fun_prop] continuous_openPeriodicVorticityFourierMode

theorem continuous_finitePairCompatibleBoundaryNonlinearWork_time
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (depth radius : ℕ) :
    Continuous (fun t : Ioo 0 T ↦
      finitePairCompatibleBoundaryNonlinearWork solution t depth radius) := by
  unfold finitePairCompatibleBoundaryNonlinearWork
    finiteOpenVorticityNonlinearCoefficient finiteAdvectiveCoefficient
    complexAdvectiveInteraction complexDot dotProduct frequencyCurlMultiplier
    complexCross crossProduct complexVectorSymmetricPhasePairing
    complexVectorHermitianPairing
  fun_prop

theorem continuous_compactFiniteLinearInteractionRadiusTailRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) :
    Continuous (compactFiniteLinearInteractionRadiusTailRate
      solution ha hab hbT depth radius) := by
  have hactual : Continuous
      (compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth) := by
    let bands : ℝ → ℝ := fun time ↦
      ∑ scale ∈ Finset.range depth,
        compactOpenSmoothDyadicLinearBandActualSignedWorkRate
          solution ha hab hbT scale time
    have hbands : Continuous bands := by
      unfold bands
      apply continuous_finsetSum
      intro scale _hscale
      exact (continuous_openSmoothDyadicLinearBandActualSignedWorkRate
        solution scale).comp (continuous_compactInteriorTime ha hab hbT)
    apply hbands.congr
    intro time
    exact sum_compactOpenSmoothDyadicLinearBandActualSignedWorkRate_eq_boundary
      solution ha hab hbT depth time
  have hfinite : Continuous
      (compactFinitePairCompatibleBoundaryNonlinearWorkRate
        solution ha hab hbT depth radius) := by
    unfold compactFinitePairCompatibleBoundaryNonlinearWorkRate
    exact Complex.continuous_re.comp
      ((continuous_finitePairCompatibleBoundaryNonlinearWork_time
        solution depth radius).comp
          (continuous_compactInteriorTime ha hab hbT))
  exact hactual.sub hfinite

/-- **Compact-time strong radius passage.**  At every fixed finite scale depth, the literal
actual-minus-finite interaction-radius tail tends to zero in `L¹([a,b])`.  The dominating
constant comes from the actual compact weighted `H³` path and is independent of radius. -/
theorem tendsto_integral_abs_compactFiniteLinearInteractionRadiusTailRate_zero
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    Tendsto
      (fun radius : ℕ ↦ ∫ time in a..b,
        |compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time|)
      atTop (nhds 0) := by
  let bound : ℝ → ℝ := fun _time ↦
    compactFiniteLinearRadiusTailBound solution ha hab hbT depth
  have hdominated := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := a) (b := b) (μ := volume) (l := atTop)
    (F := fun radius time ↦
      |compactFiniteLinearInteractionRadiusTailRate
        solution ha hab hbT depth radius time|)
    (f := fun _time ↦ (0 : ℝ)) bound
  have hpassage := hdominated
    (Filter.Eventually.of_forall fun radius ↦
      (continuous_compactFiniteLinearInteractionRadiusTailRate
        solution ha hab hbT depth radius).abs.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun radius ↦ ae_of_all _ fun time _htime ↦ by
      simpa only [Real.norm_eq_abs, abs_abs, bound] using
        abs_compactFiniteLinearInteractionRadiusTailRate_le
          solution ha hab hbT depth radius time)
    (continuous_const.intervalIntegrable _ _)
    (ae_of_all _ fun time _htime ↦ by
      have htail := tendsto_compactFiniteLinearInteractionRadiusTailRate_zero
        solution ha hab hbT depth time
      have habs := continuous_abs.tendsto 0 |>.comp htail
      change Tendsto
        (fun radius : ℕ ↦ |compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time|) atTop (nhds |(0 : ℝ)|) at habs
      simpa using habs)
  simpa using hpassage

/-- The same strong passage in the positive set-integral chart. -/
theorem tendsto_setIntegral_abs_compactFiniteLinearInteractionRadiusTailRate_zero
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    Tendsto
      (fun radius : ℕ ↦ ∫ time in Ioc a b,
        |compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time|)
      atTop (nhds 0) := by
  simpa only [intervalIntegral.integral_of_le hab] using
    tendsto_integral_abs_compactFiniteLinearInteractionRadiusTailRate_zero
      solution ha hab hbT depth

/-- In particular, the signed interval integral converges to zero; this is a consequence of the
strong `L¹` passage, not a cancellation-only substitute for it. -/
theorem tendsto_integral_compactFiniteLinearInteractionRadiusTailRate_zero
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    Tendsto
      (fun radius : ℕ ↦ ∫ time in a..b,
        compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time)
      atTop (nhds 0) := by
  let bound : ℝ → ℝ := fun _time ↦
    compactFiniteLinearRadiusTailBound solution ha hab hbT depth
  have hdominated := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := a) (b := b) (μ := volume) (l := atTop)
    (F := fun radius time ↦
      compactFiniteLinearInteractionRadiusTailRate
        solution ha hab hbT depth radius time)
    (f := fun _time ↦ (0 : ℝ)) bound
  have hpassage := hdominated
    (Filter.Eventually.of_forall fun radius ↦
      (continuous_compactFiniteLinearInteractionRadiusTailRate
        solution ha hab hbT depth radius).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun radius ↦ ae_of_all _ fun time _htime ↦ by
      simpa only [Real.norm_eq_abs, bound] using
        abs_compactFiniteLinearInteractionRadiusTailRate_le
          solution ha hab hbT depth radius time)
    (continuous_const.intervalIntegrable _ _)
    (ae_of_all _ fun time _htime ↦
      tendsto_compactFiniteLinearInteractionRadiusTailRate_zero
        solution ha hab hbT depth time)
  simpa using hpassage

/-! ## The distinct receiver-frequency output closure -/

/-- The complete interaction-radius endpoint of the strain-filtered source.  This removes only
the interaction aperture; the fixed finite output-frequency receiver remains unchanged. -/
def cofinalStrainFilteredSource
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (k : SpatialFrequency) : ComplexVector :=
  ∑' p : SpatialFrequency,
    complexAdvectiveInteraction p (transportedFrequencyAt k p)
      (openPeriodicVorticityFourierMode solution t p)
      (multiplierFilter
        (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
        (openPeriodicVelocityFourierMode solution t)
        (transportedFrequencyAt k p))

/-- The receiver-truncated physical reading after only the interaction-radius passage has been
completed. -/
def cofinalReceiverTruncatedStrainReading
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (q : SpatialTorus) : ℂ :=
  complexVectorSymmetricPhasePairing
    (finiteFourierSynthesis
      (openPeriodicVorticityFourierMode solution t)
      (smoothDyadicBandNativeAperture depth) q)
    (finiteFourierSynthesis
      (cofinalStrainFilteredSource solution t depth)
      (smoothDyadicBandNativeAperture depth) q)

/-- The fixed output-receiver mismatch left after the interaction radius is complete. -/
def finiteDepthCofinalOutputReceiverDefect
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (q : SpatialTorus) : ℂ :=
  finiteDepthDyadicHodgeStrainReading solution t q depth -
    cofinalReceiverTruncatedStrainReading solution t depth q

/-- The still-cofinal interaction part of the output tail. -/
def finiteRadiusCofinalStrainSourceTail
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) (q : SpatialTorus) : ℂ :=
  cofinalReceiverTruncatedStrainReading solution t depth q -
    finitePairCompatibleReceiverTruncatedStrainReading
      solution t depth radius q

/-- Exact separation of the two distinct tails.  Increasing the interaction radius can affect
only the second summand; it cannot by itself establish equality between the complete physical
reading and the fixed finite output receiver. -/
theorem finitePairCompatibleStrainOutputTail_eq_outputDefect_add_radiusTail
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) (q : SpatialTorus) :
    finitePairCompatibleStrainOutputTail solution t depth radius q =
      finiteDepthCofinalOutputReceiverDefect solution t depth q +
        finiteRadiusCofinalStrainSourceTail solution t depth radius q := by
  unfold finitePairCompatibleStrainOutputTail
    finiteDepthCofinalOutputReceiverDefect finiteRadiusCofinalStrainSourceTail
  ring

/-- The exact source-owner obligation exposed by the preceding separation.  It is an equality of
the complete physical reading with the interaction-complete finite output receiver on the whole
addressed compact slab.  This is not implied by radius cofinality and is intentionally not
installed as a premise of the radius-tail theorem above. -/
def CompactFiniteDepthOutputReceiverClosure
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) (depth : ℕ) : Prop :=
  ∀ time : Icc a b, ∀ q : SpatialTorus,
    finiteDepthCofinalOutputReceiverDefect solution
      ⟨time.1, ha.trans_le time.2.1, time.2.2.trans_lt hbT⟩ depth q = 0

section Audit

#print axioms norm_finiteAdvectiveCoefficient_state_le
#print axioms norm_finitePairCompatibleBoundaryNonlinearWork_le
#print axioms abs_compactFiniteLinearInteractionRadiusTailRate_le
#print axioms tendsto_integral_abs_compactFiniteLinearInteractionRadiusTailRate_zero
#print axioms tendsto_setIntegral_abs_compactFiniteLinearInteractionRadiusTailRate_zero
#print axioms tendsto_integral_compactFiniteLinearInteractionRadiusTailRate_zero
#print axioms finitePairCompatibleStrainOutputTail_eq_outputDefect_add_radiusTail

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage
