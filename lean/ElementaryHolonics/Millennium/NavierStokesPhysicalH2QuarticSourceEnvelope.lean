import ElementaryHolonics.Millennium.NavierStokesCalibratedTriadicFaceBound
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedQuarticInteractionPullback
import ElementaryHolonics.Millennium.NavierStokesWeightedSmoothPathTower

/-!
# A time-independent complete-address envelope for the quartic source insertion

**[proved-derived; formal-checked]** A coherent smooth path tower supplies uniform order-eighteen
coefficient bounds for both the velocity and its projected quadratic source.  After the physical
`H2` exchange multiplier and transported derivative are retained, six powers of the two free
address weights remain.  Three pay the integer-lattice count in each address axis, giving one
time-independent summable majorant on `CompleteTransportAddress`.

This is the quartic source insertion `S`, not the cubic exchanged face `F`.  Its bound is furnished
by higher-order coefficient persistence and does not use an `H3` occupation integral.
-/

noncomputable section

open Function Set
open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2QuarticSourceEnvelope

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCalibratedTriadicFaceBound
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.Turn

/-! ## Order-eighteen coefficient receivers -/

/-- The order-nineteen quadratic lift has the same order-eighteen projected source coefficient
as the common base path. -/
theorem CoherentWeightedSmoothPathTower.higherLeraySourceEighteen_coefficient_eq_base
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 18
      (periodicVectorWeightedLerayDivergenceConvolution
        19 (by norm_num) (tower.lift 16 t) (tower.lift 16 t) component)).1 k =
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) component).1 k := by
  have hhigh := congrFun
    (vectorCoefficientAt_periodicVectorWeightedLerayDivergenceConvolution
      19 (by norm_num) (tower.lift 16 t) (tower.lift 16 t) k) component
  have hbase := congrFun
    (vectorCoefficientAt_lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree (base t))
      (unweightedVectorThree (base t)) k) component
  change
    vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder 18
        (periodicVectorWeightedLerayDivergenceConvolution
          19 (by norm_num) (tower.lift 16 t) (tower.lift 16 t))) k component =
      vectorCoefficientAt
        (periodicVectorSobolevTwoUnderlying
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree (base t))
            (unweightedVectorThree (base t)))) k component
  rw [hhigh, hbase]
  congr 1
  funext output
  rw [h3DivergenceConvolution_apply]
  apply Finset.sum_congr rfl
  intro coordinate _
  congr 1
  apply tsum_congr
  intro p
  rw [tower.weightedSobolevCoefficients_lift_eq_base,
    tower.weightedSobolevCoefficients_lift_eq_base]
  rfl

/-- Uniform native norm of the order-eighteen projected quadratic source. -/
def CoherentWeightedSmoothPathTower.higherLeraySourceEighteenUniformBound
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) : ℝ :=
  (36 * (2 : ℝ) ^ 19 * periodicH3EmbeddingConstant) *
    ‖tower.lift 16‖ ^ 2

theorem CoherentWeightedSmoothPathTower.higherLeraySourceEighteenUniformBound_nonneg
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) :
    0 ≤ higherLeraySourceEighteenUniformBound tower := by
  unfold CoherentWeightedSmoothPathTower.higherLeraySourceEighteenUniformBound
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 19))
      periodicH3EmbeddingConstant_nonneg)
    (sq_nonneg _)

/-- The common velocity coefficient has uniform reciprocal order-nine decay. -/
theorem CoherentWeightedSmoothPathTower.norm_baseVelocityCoefficient_le_weightNine
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (k : SpatialFrequency) :
    ‖(weightedSobolevCoefficients 3 (base t component)).1 k‖ ≤
      ‖tower.lift 15‖ * (periodicSobolevWeight 9 k)⁻¹ := by
  rw [← tower.weightedSobolevCoefficients_lift_eq_base 15 t component k]
  have hcoefficient := norm_weightedSobolevCoefficients_apply_le
    18 (tower.lift 15 t) component k
  have hstate : ‖tower.lift 15 t‖ ≤ ‖tower.lift 15‖ :=
    (tower.lift 15).norm_coe_le_norm t
  calc
    ‖(weightedSobolevCoefficients 18 (tower.lift 15 t component)).1 k‖ ≤
        (Real.sqrt (periodicSobolevWeight 18 k))⁻¹ * ‖tower.lift 15 t‖ :=
      hcoefficient
    _ ≤ (Real.sqrt (periodicSobolevWeight 18 k))⁻¹ * ‖tower.lift 15‖ :=
      mul_le_mul_of_nonneg_left hstate (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = ‖tower.lift 15‖ * (periodicSobolevWeight 9 k)⁻¹ := by
      rw [show (18 : ℕ) = 2 * 9 by norm_num,
        sqrt_periodicSobolevWeight_even]
      ring

/-- The projected source coefficient has the same uniform reciprocal order-nine decay. -/
theorem CoherentWeightedSmoothPathTower.norm_baseLeraySourceCoefficient_le_weightNine
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (k : SpatialFrequency) :
    ‖(lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree (base t))
      (unweightedVectorThree (base t)) component).1 k‖ ≤
      higherLeraySourceEighteenUniformBound tower *
        (periodicSobolevWeight 9 k)⁻¹ := by
  rw [← higherLeraySourceEighteen_coefficient_eq_base tower t component k]
  let source : PeriodicVectorWeightedSobolev 18 :=
    periodicVectorWeightedLerayDivergenceConvolution
      19 (by norm_num) (tower.lift 16 t) (tower.lift 16 t)
  have hcoefficient := norm_weightedSobolevCoefficients_apply_le
    18 source component k
  have hsource := norm_periodicVectorWeightedLerayDivergenceConvolution_le
    19 (by norm_num) (tower.lift 16 t) (tower.lift 16 t)
  have hstate : ‖tower.lift 16 t‖ ≤ ‖tower.lift 16‖ :=
    (tower.lift 16).norm_coe_le_norm t
  have hconstant :
      0 ≤ 36 * (2 : ℝ) ^ 19 * periodicH3EmbeddingConstant := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 19))
      periodicH3EmbeddingConstant_nonneg
  have hstatesSquare :
      ‖tower.lift 16 t‖ * ‖tower.lift 16 t‖ ≤ ‖tower.lift 16‖ ^ 2 := by
    nlinarith [norm_nonneg (tower.lift 16 t), norm_nonneg (tower.lift 16)]
  have hscaledStates :
      (36 * (2 : ℝ) ^ 19 * periodicH3EmbeddingConstant) *
          ‖tower.lift 16 t‖ * ‖tower.lift 16 t‖ ≤
        (36 * (2 : ℝ) ^ 19 * periodicH3EmbeddingConstant) *
          ‖tower.lift 16‖ ^ 2 := by
    calc
      _ = (36 * (2 : ℝ) ^ 19 * periodicH3EmbeddingConstant) *
          (‖tower.lift 16 t‖ * ‖tower.lift 16 t‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hstatesSquare hconstant
  calc
    ‖(weightedSobolevCoefficients 18 (source component)).1 k‖ ≤
        (Real.sqrt (periodicSobolevWeight 18 k))⁻¹ * ‖source‖ := hcoefficient
    _ ≤ (Real.sqrt (periodicSobolevWeight 18 k))⁻¹ *
        ((36 * (2 : ℝ) ^ 19 * periodicH3EmbeddingConstant) *
          ‖tower.lift 16 t‖ * ‖tower.lift 16 t‖) := by
      exact mul_le_mul_of_nonneg_left (by simpa [source] using hsource)
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ (Real.sqrt (periodicSobolevWeight 18 k))⁻¹ *
        ((36 * (2 : ℝ) ^ 19 * periodicH3EmbeddingConstant) *
          ‖tower.lift 16‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hscaledStates
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = higherLeraySourceEighteenUniformBound tower *
        (periodicSobolevWeight 9 k)⁻¹ := by
      rw [show (18 : ℕ) = 2 * 9 by norm_num,
        sqrt_periodicSobolevWeight_even]
      unfold CoherentWeightedSmoothPathTower.higherLeraySourceEighteenUniformBound
      ring

end Soma.Holonics.Millennium.NavierStokesPhysicalH2QuarticSourceEnvelope
