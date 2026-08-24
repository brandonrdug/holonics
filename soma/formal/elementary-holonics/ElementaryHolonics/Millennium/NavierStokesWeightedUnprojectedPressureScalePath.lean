import ElementaryHolonics.Millennium.NavierStokesWeightedPressureScale

/-!
# Continuous unprojected quadratic and pressure paths on the complete Sobolev scale

**[proved-derived]** The arbitrary-order unprojected divergence population already exists with
an exact tame bound, but only its Leray projection had been bundled as a continuous bilinear map.
This owner closes that missing edge, then conducts every coherent smooth velocity lift through the
unprojected source and the scale-indexed zero-gauge pressure passage.

The returned paths retain the complete convolution population, exact base-path coefficients,
Fourier reality, and pairwise high-to-low restriction compatibility.
-/

noncomputable section

open Function Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedUnprojectedPressureScalePath

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPressureCoefficient
open Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedPressureScale
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Native coefficient linearity -/

private theorem periodicWeightedSobolev_eq_of_coefficients_eq
    {order : ℕ} {left right : PeriodicWeightedSobolev order}
    (hcoeff : ∀ k,
      (weightedSobolevCoefficients order left).1 k =
        (weightedSobolevCoefficients order right).1 k) :
    left = right := by
  calc
    left = coefficientWeightedRealization order
        (weightedSobolevCoefficients order left) :=
      (coefficientWeightedRealization_weightedSobolevCoefficients order left).symm
    _ = coefficientWeightedRealization order
        (weightedSobolevCoefficients order right) := by
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      funext k
      exact hcoeff k
    _ = right := coefficientWeightedRealization_weightedSobolevCoefficients order right

private theorem weightedSobolevCoefficients_add_apply
    (order : ℕ) (left right : PeriodicWeightedSobolev order)
    (k : SpatialFrequency) :
    (weightedSobolevCoefficients order (left + right)).1 k =
      (weightedSobolevCoefficients order left).1 k +
        (weightedSobolevCoefficients order right).1 k := by
  change
    ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
      (left k + right k)) =
    ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * left k) +
      ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * right k)
  ring

private theorem weightedSobolevCoefficients_smul_apply
    (order : ℕ) (c : ℂ) (state : PeriodicWeightedSobolev order)
    (k : SpatialFrequency) :
    (weightedSobolevCoefficients order (c • state)).1 k =
      c * (weightedSobolevCoefficients order state).1 k := by
  change
    ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
      (c * state k)) =
    c * ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) * state k)
  ring

private theorem summable_physicalConvolutionAtOrder
    (order : ℕ) (horder : 3 ≤ order)
    (left right : PeriodicWeightedSobolev order)
    (k : SpatialFrequency) :
    Summable fun p ↦
      (weightedSobolevCoefficients order left).1 p *
        (weightedSobolevCoefficients order right).1 (k - p) := by
  apply Summable.of_norm
  let leftThree : PeriodicSobolevCoefficients 3 :=
    periodicSobolevCoefficientsRestrict 3 order horder
      (weightedSobolevCoefficients order left)
  have hleftThree := summable_norm_periodicSobolevThreeCoefficient leftThree
  have hleft : Summable fun p ↦
      ‖(weightedSobolevCoefficients order left).1 p‖ := by
    simpa only [leftThree, periodicSobolevCoefficientsRestrict_apply] using hleftThree
  have hbound : Summable fun p ↦
      ‖(weightedSobolevCoefficients order left).1 p‖ *
        ‖(weightedSobolevCoefficients order right).1‖ :=
    hleft.mul_right _
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_) hbound
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (weightedSobolevCoefficients order right).1 (k - p))
    (norm_nonneg _)

/-! ## The missing continuous unprojected bilinear owner -/

theorem periodicVectorWeightedDivergenceConvolution_add_left
    (order : ℕ) (horder : 3 ≤ order)
    (first second transported : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedDivergenceConvolution
        order horder (first + second) transported =
      periodicVectorWeightedDivergenceConvolution order horder first transported +
        periodicVectorWeightedDivergenceConvolution
          order horder second transported := by
  funext output
  apply periodicWeightedSobolev_eq_of_coefficients_eq
  intro k
  change
    (weightedSobolevCoefficients (order - 1)
      (periodicVectorWeightedDivergenceConvolution
        order horder (first + second) transported output)).1 k =
    (weightedSobolevCoefficients (order - 1)
      (periodicVectorWeightedDivergenceConvolution
          order horder first transported output +
        periodicVectorWeightedDivergenceConvolution
          order horder second transported output)).1 k
  rw [weightedSobolevCoefficients_add_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.add_apply]
  simp_rw [weightedSobolevCoefficients_add_apply]
  have hfirst := summable_physicalConvolutionAtOrder
    order horder (first coordinate) (transported output) k
  have hsecond := summable_physicalConvolutionAtOrder
    order horder (second coordinate) (transported output) k
  rw [← mul_add, ← hfirst.tsum_add hsecond]
  congr 1
  apply tsum_congr
  intro p
  ring

theorem periodicVectorWeightedDivergenceConvolution_add_right
    (order : ℕ) (horder : 3 ≤ order)
    (advecting first second : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedDivergenceConvolution
        order horder advecting (first + second) =
      periodicVectorWeightedDivergenceConvolution order horder advecting first +
        periodicVectorWeightedDivergenceConvolution
          order horder advecting second := by
  funext output
  apply periodicWeightedSobolev_eq_of_coefficients_eq
  intro k
  change
    (weightedSobolevCoefficients (order - 1)
      (periodicVectorWeightedDivergenceConvolution
        order horder advecting (first + second) output)).1 k =
    (weightedSobolevCoefficients (order - 1)
      (periodicVectorWeightedDivergenceConvolution
          order horder advecting first output +
        periodicVectorWeightedDivergenceConvolution
          order horder advecting second output)).1 k
  rw [weightedSobolevCoefficients_add_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.add_apply]
  simp_rw [weightedSobolevCoefficients_add_apply]
  have hfirst := summable_physicalConvolutionAtOrder
    order horder (advecting coordinate) (first output) k
  have hsecond := summable_physicalConvolutionAtOrder
    order horder (advecting coordinate) (second output) k
  rw [← mul_add, ← hfirst.tsum_add hsecond]
  congr 1
  apply tsum_congr
  intro p
  ring

theorem periodicVectorWeightedDivergenceConvolution_smul_left
    (order : ℕ) (horder : 3 ≤ order) (c : ℂ)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedDivergenceConvolution
        order horder (c • advecting) transported =
      c • periodicVectorWeightedDivergenceConvolution
        order horder advecting transported := by
  funext output
  apply periodicWeightedSobolev_eq_of_coefficients_eq
  intro k
  change
    (weightedSobolevCoefficients (order - 1)
      (periodicVectorWeightedDivergenceConvolution
        order horder (c • advecting) transported output)).1 k =
    (weightedSobolevCoefficients (order - 1)
      (c • periodicVectorWeightedDivergenceConvolution
        order horder advecting transported output)).1 k
  rw [weightedSobolevCoefficients_smul_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply]
  simp_rw [weightedSobolevCoefficients_smul_apply]
  calc
    (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        (∑' p,
          (c * (weightedSobolevCoefficients order
              (advecting coordinate)).1 p) *
            (weightedSobolevCoefficients order (transported output)).1 (k - p)) =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        (∑' p, c *
          ((weightedSobolevCoefficients order (advecting coordinate)).1 p *
            (weightedSobolevCoefficients order (transported output)).1 (k - p))) := by
          congr 1
          apply tsum_congr
          intro p
          ring
    _ = c * ((2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        (∑' p,
          (weightedSobolevCoefficients order (advecting coordinate)).1 p *
            (weightedSobolevCoefficients order (transported output)).1 (k - p))) := by
          rw [tsum_mul_left]
          ring

theorem periodicVectorWeightedDivergenceConvolution_smul_right
    (order : ℕ) (horder : 3 ≤ order) (c : ℂ)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedDivergenceConvolution
        order horder advecting (c • transported) =
      c • periodicVectorWeightedDivergenceConvolution
        order horder advecting transported := by
  funext output
  apply periodicWeightedSobolev_eq_of_coefficients_eq
  intro k
  change
    (weightedSobolevCoefficients (order - 1)
      (periodicVectorWeightedDivergenceConvolution
        order horder advecting (c • transported) output)).1 k =
    (weightedSobolevCoefficients (order - 1)
      (c • periodicVectorWeightedDivergenceConvolution
        order horder advecting transported output)).1 k
  rw [weightedSobolevCoefficients_smul_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply]
  simp_rw [weightedSobolevCoefficients_smul_apply]
  calc
    (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        (∑' p,
          (weightedSobolevCoefficients order (advecting coordinate)).1 p *
            (c * (weightedSobolevCoefficients order
              (transported output)).1 (k - p))) =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        (∑' p, c *
          ((weightedSobolevCoefficients order (advecting coordinate)).1 p *
            (weightedSobolevCoefficients order (transported output)).1 (k - p))) := by
          congr 1
          apply tsum_congr
          intro p
          ring
    _ = c * ((2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        (∑' p,
          (weightedSobolevCoefficients order (advecting coordinate)).1 p *
            (weightedSobolevCoefficients order (transported output)).1 (k - p))) := by
          rw [tsum_mul_left]
          ring

/-- Coarse high-high norm receipt for the complete unprojected divergence population. -/
theorem norm_periodicVectorWeightedDivergenceConvolution_le
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    ‖periodicVectorWeightedDivergenceConvolution
        order horder advecting transported‖ ≤
      (6 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        ‖advecting‖ * ‖transported‖ := by
  have hbase := norm_periodicVectorWeightedDivergenceConvolution_le_tame
    order horder advecting transported
  have hu := norm_periodicVectorWeightedRestrictToThree_le
    order horder advecting
  have hv := norm_periodicVectorWeightedRestrictToThree_le
    order horder transported
  have hconstant : 0 ≤ 3 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant :=
    mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) order))
      periodicH3EmbeddingConstant_nonneg
  calc
    ‖periodicVectorWeightedDivergenceConvolution
        order horder advecting transported‖ ≤
      (3 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        (‖periodicVectorWeightedRestrictToThree order horder advecting‖ *
            ‖transported‖ +
          ‖periodicVectorWeightedRestrictToThree order horder transported‖ *
            ‖advecting‖) := hbase
    _ ≤ (3 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        (‖advecting‖ * ‖transported‖ + ‖transported‖ * ‖advecting‖) := by
      gcongr
    _ = (6 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant) *
        ‖advecting‖ * ‖transported‖ := by ring

/-- The arbitrary-order unprojected divergence as a genuinely continuous curried bilinear map. -/
def periodicVectorWeightedDivergenceConvolutionContinuous
    (order : ℕ) (horder : 3 ≤ order) :
    PeriodicVectorWeightedSobolev order →L[ℂ]
      PeriodicVectorWeightedSobolev order →L[ℂ]
        PeriodicVectorWeightedSobolev (order - 1) :=
  (LinearMap.mk₂ ℂ
    (periodicVectorWeightedDivergenceConvolution order horder)
    (periodicVectorWeightedDivergenceConvolution_add_left order horder)
    (periodicVectorWeightedDivergenceConvolution_smul_left order horder)
    (periodicVectorWeightedDivergenceConvolution_add_right order horder)
    (periodicVectorWeightedDivergenceConvolution_smul_right order horder)).mkContinuous₂
      (6 * (2 : ℝ) ^ order * periodicH3EmbeddingConstant)
      (norm_periodicVectorWeightedDivergenceConvolution_le order horder)

@[simp]
theorem periodicVectorWeightedDivergenceConvolutionContinuous_apply
    (order : ℕ) (horder : 3 ≤ order)
    (advecting transported : PeriodicVectorWeightedSobolev order) :
    periodicVectorWeightedDivergenceConvolutionContinuous
        order horder advecting transported =
      periodicVectorWeightedDivergenceConvolution
        order horder advecting transported :=
  rfl

/-! ## Coherent unprojected quadratic paths -/

/-- Conduct one coherent native `H^(m+3)` lift through the complete unprojected divergence
population. -/
def CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ) :
    C(Icc (0 : ℝ) T, PeriodicVectorWeightedSobolev (m + 2)) where
  toFun t := periodicVectorWeightedDivergenceConvolution
    (m + 3) (by omega) (tower.lift m t) (tower.lift m t)
  continuous_toFun := by
    let B : PeriodicVectorWeightedSobolev (m + 3) →L[ℂ]
        PeriodicVectorWeightedSobolev (m + 3) →L[ℂ]
          PeriodicVectorWeightedSobolev (m + 2) :=
      periodicVectorWeightedDivergenceConvolutionContinuous (m + 3) (by omega)
    have hoperator : Continuous (fun t ↦ B (tower.lift m t)) :=
      B.continuous.comp (tower.lift m).continuous
    simpa only [B,
      periodicVectorWeightedDivergenceConvolutionContinuous_apply] using
        hoperator.clm_apply (tower.lift m).continuous

@[simp]
theorem CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_apply
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ)
    (t : Icc (0 : ℝ) T) :
    CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder tower m t =
      periodicVectorWeightedDivergenceConvolution
        (m + 3) (by omega) (tower.lift m t) (tower.lift m t) :=
  rfl

/-- Every unweighted coefficient of the high-order source is exactly the complete unprojected
quadratic coefficient carried by the common base path face. -/
theorem CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_coefficient_eq_base
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ)
    (t : Icc (0 : ℝ) T) (output : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (m + 2)
      (CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder tower m t output)).1 k =
      (h3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) output).1 k := by
  rw [CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_apply]
  have hsource :=
    weightedSobolevCoefficients_periodicVectorWeightedDivergenceConvolution_apply
      (m + 3) (by omega) (tower.lift m t) (tower.lift m t) output k
  have hsource' :
      (weightedSobolevCoefficients (m + 2)
        (periodicVectorWeightedDivergenceConvolution
          (m + 3) (by omega) (tower.lift m t) (tower.lift m t) output)).1 k =
        ∑ coordinate : Fin 3,
          (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
            (∑' p,
              (weightedSobolevCoefficients (m + 3)
                (tower.lift m t coordinate)).1 p *
              (weightedSobolevCoefficients (m + 3)
                (tower.lift m t output)).1 (k - p)) := by
    simpa only [show m + 3 - 1 = m + 2 by omega] using hsource
  rw [hsource', h3DivergenceConvolution_apply]
  apply Finset.sum_congr rfl
  intro coordinate _
  congr 1
  apply tsum_congr
  intro p
  rw [tower.weightedSobolevCoefficients_lift_eq_base,
    tower.weightedSobolevCoefficients_lift_eq_base]
  rfl

/-- The scale-indexed source presents exactly the common base physical mode. -/
theorem CoherentWeightedSmoothPathTower.physicalModeAtOrder_unprojectedQuadraticPath
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ)
    (t : Icc (0 : ℝ) T) (k : SpatialFrequency) :
    physicalModeAtOrder m
        (CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder tower m t) k =
      fun output ↦ (h3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) output).1 k := by
  funext output
  exact CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_coefficient_eq_base
    tower m t output k

/-- A Fourier-real coherent velocity path returns a Fourier-real unprojected source at every
scale and addressed time. -/
theorem CoherentWeightedSmoothPathTower.isWeightedFourierReal_unprojectedQuadraticPathAtOrder
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (hreal : IsWeightedFourierRealPath base)
    (m : ℕ) (t : Icc (0 : ℝ) T) :
    IsWeightedFourierReal (m + 2)
      (CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder tower m t) := by
  intro output k
  rw [CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_coefficient_eq_base,
    CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_coefficient_eq_base]
  exact h3DivergenceConvolution_neg_eq_conj
    (unweightedVectorThree (base t))
    (unweightedVectorThree (base t))
    (hreal t) (hreal t) output k

/-- Pairwise restriction of the coherent source paths retains the identical unweighted
convolution occurrence. -/
theorem CoherentWeightedSmoothPathTower.restrict_unprojectedQuadraticPathAtOrder
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (low high : ℕ) (hlowhigh : low ≤ high) (t : Icc (0 : ℝ) T) :
    periodicVectorWeightedSobolevRestrictCLM
        (low + 2) (high + 2) (by omega)
        (CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder tower high t) =
      CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder tower low t := by
  funext output
  apply periodicWeightedSobolev_eq_of_coefficients_eq
  intro k
  change
    (weightedSobolevCoefficients (low + 2)
      (periodicWeightedSobolevRestrict
        (low + 2) (high + 2) (by omega)
        (CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder
          tower high t output))).1 k =
      (weightedSobolevCoefficients (low + 2)
        (CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder
          tower low t output)).1 k
  rw [weightedSobolevCoefficients_restrict_apply,
    CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_coefficient_eq_base,
    CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_coefficient_eq_base]

/-! ## Coherent scale-indexed pressure paths -/

/-- Apply the scale-indexed elliptic gain to the complete unprojected source path. -/
def CoherentWeightedSmoothPathTower.nativePressurePathAtOrder
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ) :
    C(Icc (0 : ℝ) T, PeriodicWeightedSobolev (m + 3)) where
  toFun t := nativePressureAtOrder m
    (CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder tower m t)
  continuous_toFun := (nativePressureAtOrder m).continuous.comp
    (CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder tower m).continuous

@[simp]
theorem CoherentWeightedSmoothPathTower.nativePressurePathAtOrder_apply
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ)
    (t : Icc (0 : ℝ) T) :
    CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower m t =
      nativePressureAtOrder m
        (CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder tower m t) :=
  rfl

/-- Every pressure path face retains the exact zero-gauge coefficient selected from the common
base unprojected quadratic mode. -/
theorem CoherentWeightedSmoothPathTower.nativePressurePathAtOrder_coefficient_eq_base
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ)
    (t : Icc (0 : ℝ) T) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (m + 3)
      (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower m t)).1 k =
      pressureCoefficientOfMode k (fun output ↦
        (h3DivergenceConvolution
          (unweightedVectorThree (base t))
          (unweightedVectorThree (base t)) output).1 k) := by
  rw [CoherentWeightedSmoothPathTower.nativePressurePathAtOrder_apply,
    weightedSobolevCoefficients_nativePressureAtOrder,
    CoherentWeightedSmoothPathTower.physicalModeAtOrder_unprojectedQuadraticPath]

/-- Fourier reality propagates from the coherent velocity face through the complete source and
the zero-gauge elliptic passage at every order. -/
theorem CoherentWeightedSmoothPathTower.isScalarWeightedFourierReal_nativePressurePathAtOrder
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (hreal : IsWeightedFourierRealPath base)
    (m : ℕ) (t : Icc (0 : ℝ) T) :
    IsScalarWeightedFourierReal (m + 3)
      (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower m t) :=
  isScalarWeightedFourierReal_nativePressureAtOrder m
    (CoherentWeightedSmoothPathTower.isWeightedFourierReal_unprojectedQuadraticPathAtOrder
      tower hreal m t)

/-- The complete scalar pressure paths form an exact coherent tower under every high-to-low
restriction. -/
theorem CoherentWeightedSmoothPathTower.restrict_nativePressurePathAtOrder
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (low high : ℕ) (hlowhigh : low ≤ high) (t : Icc (0 : ℝ) T) :
    periodicWeightedSobolevRestrictCLM
        (low + 3) (high + 3) (by omega)
        (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower high t) =
      CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower low t := by
  rw [CoherentWeightedSmoothPathTower.nativePressurePathAtOrder_apply,
    CoherentWeightedSmoothPathTower.nativePressurePathAtOrder_apply,
    restrict_nativePressureAtOrder low high hlowhigh]
  congr 1
  exact CoherentWeightedSmoothPathTower.restrict_unprojectedQuadraticPathAtOrder
    tower low high hlowhigh t

section Audit

#print axioms periodicVectorWeightedDivergenceConvolutionContinuous
#print axioms CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder
#print axioms CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_coefficient_eq_base
#print axioms CoherentWeightedSmoothPathTower.restrict_unprojectedQuadraticPathAtOrder
#print axioms CoherentWeightedSmoothPathTower.nativePressurePathAtOrder
#print axioms CoherentWeightedSmoothPathTower.nativePressurePathAtOrder_coefficient_eq_base
#print axioms CoherentWeightedSmoothPathTower.restrict_nativePressurePathAtOrder

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedUnprojectedPressureScalePath
