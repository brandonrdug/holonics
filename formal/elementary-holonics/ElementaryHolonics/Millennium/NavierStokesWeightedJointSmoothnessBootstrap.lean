import ElementaryHolonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
import ElementaryHolonics.Millennium.NavierStokesWeightedHigherOrderBilinear
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Joint spacetime regularity forced by the weighted smooth mild tower

**[proved-derived]** The coherent all-spatial-order tower and the exact interior modal
momentum law already force a genuine jointly `C¹` velocity on the open restart slab.  The proof
does not assume joint differentiability: it differentiates every complete Fourier passage on
`Space × ℝ`, controls the resulting operator population by one summable lattice receiver, and
then applies Mathlib's uniform derivative theorem.

The pressure owner currently supplies a jointly continuous pressure and gradient but no native
time derivative of its quadratic source.  The last section isolates that exact elliptic input as
an `H²`-valued source derivative with its constitutive formula; no pressure smoothness or final
solution record is placed in the premise.
-/

noncomputable section

open Function Set Filter
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The exact complete modal first jet -/

/-- The projected modal right-hand side, totalized through the same endpoint extension as the
weighted path.  On the open aperture this is exactly the derivative in the fixed-point modal
equation. -/
def projectedModalTimeDerivativeCoefficient
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T) (nu : ℝ≥0)
    (component : Fin 3) (k : SpatialFrequency) (t : ℝ) : ℂ :=
  ((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
      (weightedSobolevCoefficients 3
        (weightedPathExtension hT base t component)).1 k -
    (weightedSobolevCoefficients 2
      (weightedLerayDivergenceConvolution
        (weightedPathExtension hT base t)
        (weightedPathExtension hT base t) component)).1 k

/-- On the addressed aperture the native projected source coefficient is literally the older
unweighted Leray-divergence coefficient used by the modal ODE. -/
theorem projectedModalTimeDerivativeCoefficient_of_mem
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T) (nu : ℝ≥0)
    (component : Fin 3) (k : SpatialFrequency) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    projectedModalTimeDerivativeCoefficient hT base nu component k t =
      ((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          (weightedSobolevCoefficients 3
            (base ⟨t, ht⟩ component)).1 k -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base ⟨t, ht⟩))
          (unweightedVectorThree (base ⟨t, ht⟩)) component).1 k := by
  rw [projectedModalTimeDerivativeCoefficient,
    weightedPathExtension_of_mem hT base ht,
    weightedLerayDivergenceConvolution_apply,
    weightedSobolevCoefficients_coefficientWeightedRealization]

/-- One weighted native coefficient depends continuously on a continuously varying vector
state. -/
theorem continuous_weightedVectorSobolevCoefficient
    {X : Type*} [TopologicalSpace X] {order : ℕ}
    {state : X → PeriodicVectorWeightedSobolev order}
    (hstate : Continuous state) (component : Fin 3)
    (k : SpatialFrequency) :
    Continuous (fun x ↦
      (weightedSobolevCoefficients order (state x component)).1 k) := by
  change Continuous (fun x ↦
    ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
      state x component k))
  have hcomponent : Continuous (fun x ↦ state x component) :=
    (continuous_apply component).comp hstate
  have hcoe : Continuous (fun x ↦ (state x component : SpatialFrequency → ℂ)) :=
    lp.uniformContinuous_coe.continuous.comp hcomponent
  exact continuous_const.mul ((continuous_apply k).comp hcoe)

/-- The modal coefficient and its projected momentum right-hand side are continuous on all real
times after endpoint totalization. -/
theorem continuous_projectedModalTimeDerivativeCoefficient
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T) (nu : ℝ≥0)
    (component : Fin 3) (k : SpatialFrequency) :
    Continuous
      (projectedModalTimeDerivativeCoefficient hT base nu component k) := by
  have hpath : Continuous (fun t ↦ weightedPathExtension hT base t) :=
    (weightedPathExtension hT base).continuous
  have hsource : Continuous (fun t ↦
      weightedLerayDivergenceConvolution
        (weightedPathExtension hT base t)
        (weightedPathExtension hT base t)) := by
    exact (weightedLerayDivergenceConvolutionContinuous.continuous.comp hpath).clm_apply hpath
  exact (continuous_const.mul
      (continuous_weightedVectorSobolevCoefficient hpath component k)).sub
    (continuous_weightedVectorSobolevCoefficient hsource component k)

/-- The exact complex Fourier passage of one velocity component on spacetime. -/
def velocitySpacetimeFourierPassage
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T)
    (component : Fin 3) (k : SpatialFrequency) (z : Space × ℝ) : ℂ :=
  (weightedSobolevCoefficients 3
      (weightedPathExtension hT base z.2 component)).1 k *
    euclideanFourierCharacter k z.1

/-- The exact real Fréchet derivative of one spacetime Fourier passage. -/
def velocitySpacetimeFourierPassageFDeriv
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T) (nu : ℝ≥0)
    (component : Fin 3) (k : SpatialFrequency) (z : Space × ℝ) :
    (Space × ℝ) →L[ℝ] ℂ :=
  (weightedSobolevCoefficients 3
      (weightedPathExtension hT base z.2 component)).1 k •
        ((euclideanFourierCharacterFDeriv k z.1).comp
          (ContinuousLinearMap.fst ℝ Space ℝ)) +
    euclideanFourierCharacter k z.1 •
      ((ContinuousLinearMap.toSpanSingleton ℝ
          (projectedModalTimeDerivativeCoefficient
            hT base nu component k z.2)).comp
        (ContinuousLinearMap.snd ℝ Space ℝ))

/-- Every individual spacetime mode carries the displayed complete first derivative throughout
the open restart slab. -/
theorem hasFDerivAt_velocitySpacetimeFourierPassage
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (k : SpatialFrequency) (z : Space × ℝ)
    (hz : z.2 ∈ Ioo (0 : ℝ) T) :
    HasFDerivAt
      (velocitySpacetimeFourierPassage hT base component k)
      (velocitySpacetimeFourierPassageFDeriv
        hT base nu component k z) z := by
  have hcoefficient :=
    fixedPoint_weightedMildMap_reconstructedCoefficient_hasDerivAt_projected
      nu hnu hT initial hfixed hreal component k hz
  rw [← projectedModalTimeDerivativeCoefficient_of_mem hT base nu component k
    ⟨hz.1.le, hz.2.le⟩] at hcoefficient
  have hcoefficientFunction :
      (fun tau ↦ weightedReconstructedVelocityCoefficient
        hT base component k tau) =
      (fun tau ↦ (weightedSobolevCoefficients 3
        (weightedPathExtension hT base tau component)).1 k) := by
    funext tau
    exact weightedReconstructedVelocityCoefficient_eq_native
      hT hreal component k tau
  rw [hcoefficientFunction] at hcoefficient
  have htime := hcoefficient.hasFDerivAt.comp z hasFDerivAt_snd
  have hspace :=
    (hasFDerivAt_euclideanFourierCharacter k z.1).comp z hasFDerivAt_fst
  change HasFDerivAt
    (((fun tau : ℝ ↦ (weightedSobolevCoefficients 3
      (weightedPathExtension hT base tau component)).1 k) ∘ Prod.snd) *
        (euclideanFourierCharacter k ∘ Prod.fst))
    (velocitySpacetimeFourierPassageFDeriv
      hT base nu component k z) z
  exact htime.mul hspace

/-- The derivative field of every individual spacetime mode is continuous. -/
theorem continuous_velocitySpacetimeFourierPassageFDeriv
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T) (nu : ℝ≥0)
    (component : Fin 3) (k : SpatialFrequency) :
    Continuous
      (velocitySpacetimeFourierPassageFDeriv
        hT base nu component k) := by
  have hcoefficient : Continuous (fun z : Space × ℝ ↦
      (weightedSobolevCoefficients 3
        (weightedPathExtension hT base z.2 component)).1 k) :=
    (continuous_weightedVectorSobolevCoefficient
      (weightedPathExtension hT base).continuous component k).comp continuous_snd
  have htime : Continuous (fun z : Space × ℝ ↦
      projectedModalTimeDerivativeCoefficient
        hT base nu component k z.2) :=
    (continuous_projectedModalTimeDerivativeCoefficient
      hT base nu component k).comp continuous_snd
  have hcharacterDerivative :
      Continuous (euclideanFourierCharacterFDeriv k) := by
    unfold euclideanFourierCharacterFDeriv euclideanFourierFactorFDeriv
      euclideanFourierFactor
    fun_prop
  have hcharacter : Continuous (euclideanFourierCharacter k) :=
    (show Differentiable ℝ (euclideanFourierCharacter k) from
      fun x ↦ (hasFDerivAt_euclideanFourierCharacter k x).differentiableAt).continuous
  have hspan : Continuous (fun z : Space × ℝ ↦
      ContinuousLinearMap.toSpanSingleton ℝ
        (projectedModalTimeDerivativeCoefficient
          hT base nu component k z.2)) := by
    exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ 1).continuous.comp htime).congr
      (fun _ ↦ rfl)
  unfold velocitySpacetimeFourierPassageFDeriv
  fun_prop

/-! ## One summable uniform receiver for the complete spacetime derivative -/

/-- One coordinate frequency is bounded by the complete shifted Stokes frequency. -/
theorem abs_frequency_coordinate_le_one_add_stokes
    (k : SpatialFrequency) (coordinate : Fin 3) :
    |(k coordinate : ℝ)| ≤ 1 + torusStokesEigenvalue k := by
  have hcoordinate : (k coordinate : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
      (Finset.mem_univ coordinate)
  have hscale : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hfrequency : frequencySquared k ≤ torusStokesEigenvalue k := by
    rw [torusStokesEigenvalue]
    exact le_mul_of_one_le_left
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg (k i : ℝ)) hscale
  have habs : |(k coordinate : ℝ)| ≤ 1 + (k coordinate : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(k coordinate : ℝ)| - (1 / 2 : ℝ)),
      sq_abs (k coordinate : ℝ)]
  linarith

/-- The order-eight pointwise envelope spends one frequency and leaves the summable reciprocal
`H³` lattice receiver. -/
theorem coordinate_mul_inv_sqrt_weight_eight_le_weight_three_inv
    (k : SpatialFrequency) (coordinate : Fin 3) :
    |(k coordinate : ℝ)| *
        (Real.sqrt (periodicSobolevWeight 8 k))⁻¹ ≤
      (periodicSobolevWeight 3 k)⁻¹ := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num,
    sqrt_periodicSobolevWeight_even]
  let a : ℝ := 1 + torusStokesEigenvalue k
  have ha : 0 < a := by
    dsimp [a]
    linarith [torusStokesEigenvalue_nonneg k]
  have hk := abs_frequency_coordinate_le_one_add_stokes k coordinate
  rw [periodicSobolevWeight, periodicSobolevWeight]
  change |(k coordinate : ℝ)| * (a ^ 4)⁻¹ ≤ (a ^ 3)⁻¹
  calc
    |(k coordinate : ℝ)| * (a ^ 4)⁻¹ ≤
        a * (a ^ 4)⁻¹ :=
      mul_le_mul_of_nonneg_right hk (inv_nonneg.mpr (pow_nonneg ha.le 4))
    _ = (a ^ 3)⁻¹ := by
      field_simp [ne_of_gt ha]

/-- Every base coefficient times one addressed frequency has a common summable envelope supplied
by the continuous order-eight lift. -/
theorem CoherentWeightedSmoothPathTower.coordinate_mul_norm_baseCoefficient_le
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component coordinate : Fin 3)
    (k : SpatialFrequency) :
    |(k coordinate : ℝ)| *
        ‖(weightedSobolevCoefficients 3 (base t component)).1 k‖ ≤
      ‖tower.lift 5‖ * (periodicSobolevWeight 3 k)⁻¹ := by
  rw [← tower.weightedSobolevCoefficients_lift_eq_base
    5 t component k]
  have hcoefficient := norm_weightedSobolevCoefficients_apply_le
    8 (tower.lift 5 t) component k
  have hstate : ‖tower.lift 5 t‖ ≤ ‖tower.lift 5‖ :=
    (tower.lift 5).norm_coe_le_norm t
  calc
    |(k coordinate : ℝ)| *
        ‖(weightedSobolevCoefficients 8
          (tower.lift 5 t component)).1 k‖ ≤
      |(k coordinate : ℝ)| *
        ((Real.sqrt (periodicSobolevWeight 8 k))⁻¹ *
          ‖tower.lift 5 t‖) :=
      mul_le_mul_of_nonneg_left hcoefficient (abs_nonneg _)
    _ ≤ |(k coordinate : ℝ)| *
        ((Real.sqrt (periodicSobolevWeight 8 k))⁻¹ *
          ‖tower.lift 5‖) := by
      gcongr
    _ = (|(k coordinate : ℝ)| *
        (Real.sqrt (periodicSobolevWeight 8 k))⁻¹) *
          ‖tower.lift 5‖ := by ring
    _ ≤ (periodicSobolevWeight 3 k)⁻¹ * ‖tower.lift 5‖ :=
      mul_le_mul_of_nonneg_right
        (coordinate_mul_inv_sqrt_weight_eight_le_weight_three_inv
          k coordinate) (norm_nonneg _)
    _ = ‖tower.lift 5‖ * (periodicSobolevWeight 3 k)⁻¹ := by ring

/-- Uniform majorant for one complete modal spacetime derivative. -/
def CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) : ℝ :=
  6 * Real.pi * ‖tower.lift 5‖ +
    tower.modalTimeDerivativeUniformBound nu

theorem CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound_nonneg
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) :
    0 ≤ CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound
      tower nu := by
  unfold CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) (norm_nonneg _))
    (tower.modalTimeDerivativeUniformBound_nonneg nu)

/-- The common modal spacetime derivative majorant is summable on the complete lattice. -/
theorem CoherentWeightedSmoothPathTower.summable_spacetimeFirstDerivativeMajorant
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) :
    Summable (fun k : SpatialFrequency ↦
      CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound tower nu *
        (periodicSobolevWeight 3 k)⁻¹) :=
  summable_periodicSobolevWeight_three_inv.mul_left
    (CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound tower nu)

/-- Operator-norm domination of every complete spacetime mode derivative by the common summable
receiver. -/
theorem CoherentWeightedSmoothPathTower.norm_velocitySpacetimeFourierPassageFDeriv_le
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (k : SpatialFrequency) (z : Space × ℝ)
    (hz : z.2 ∈ Ioo (0 : ℝ) T) :
    ‖velocitySpacetimeFourierPassageFDeriv
        hT base nu component k z‖ ≤
      CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound tower nu *
        (periodicSobolevWeight 3 k)⁻¹ := by
  let a : ℂ := (weightedSobolevCoefficients 3
    (weightedPathExtension hT base z.2 component)).1 k
  let b : ℂ := projectedModalTimeDerivativeCoefficient
    hT base nu component k z.2
  let D : Space →L[ℝ] ℂ := euclideanFourierCharacterFDeriv k z.1
  let fstCLM : (Space × ℝ) →L[ℝ] Space :=
    ContinuousLinearMap.fst ℝ Space ℝ
  let sndCLM : (Space × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ Space ℝ
  have htime : ‖b‖ ≤ tower.modalTimeDerivativeUniformBound nu *
      (periodicSobolevWeight 3 k)⁻¹ := by
    dsimp only [b]
    rw [projectedModalTimeDerivativeCoefficient_of_mem
      hT base nu component k ⟨hz.1.le, hz.2.le⟩,
      ← weightedReconstructedVelocityCoefficient_eq_base
        hT hreal component k ⟨hz.1.le, hz.2.le⟩]
    exact tower.norm_modalDerivativeCoefficient_le
      hT nu hreal component k hz
  have hspaceCoordinate : ∀ coordinate : Fin 3,
      |(k coordinate : ℝ)| *
          ‖a‖ ≤
        ‖tower.lift 5‖ * (periodicSobolevWeight 3 k)⁻¹ :=
    fun coordinate ↦ by
      dsimp only [a]
      rw [weightedPathExtension_of_mem hT base
        ⟨hz.1.le, hz.2.le⟩]
      exact CoherentWeightedSmoothPathTower.coordinate_mul_norm_baseCoefficient_le tower
        ⟨z.2, ⟨hz.1.le, hz.2.le⟩⟩ component coordinate k
  have hspaceSum :
      (2 * Real.pi * ∑ coordinate : Fin 3, |(k coordinate : ℝ)|) *
          ‖a‖ ≤
        (6 * Real.pi * ‖tower.lift 5‖) *
          (periodicSobolevWeight 3 k)⁻¹ := by
    simp only [Fin.sum_univ_three] at hspaceCoordinate ⊢
    have h0 := hspaceCoordinate (0 : Fin 3)
    have h1 := hspaceCoordinate (1 : Fin 3)
    have h2 := hspaceCoordinate (2 : Fin 3)
    nlinarith [Real.pi_nonneg,
      norm_nonneg a,
      norm_nonneg (tower.lift 5),
      inv_nonneg.mpr (periodicSobolevWeight_nonneg 3 k)]
  have hfst : ‖fstCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro direction
    simpa [fstCLM] using (norm_fst_le direction)
  have hsnd : ‖sndCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro direction
    simpa [sndCLM] using (norm_snd_le direction)
  have hDcomp : ‖D.comp fstCLM‖ ≤ ‖D‖ := by
    calc
      ‖D.comp fstCLM‖ ≤ ‖D‖ * ‖fstCLM‖ :=
        ContinuousLinearMap.opNorm_comp_le D fstCLM
      _ ≤ ‖D‖ * 1 := mul_le_mul_of_nonneg_left hfst (norm_nonneg D)
      _ = ‖D‖ := mul_one _
  have hspanComp :
      ‖(ContinuousLinearMap.toSpanSingleton ℝ b).comp sndCLM‖ ≤ ‖b‖ := by
    calc
      ‖(ContinuousLinearMap.toSpanSingleton ℝ b).comp sndCLM‖ ≤
          ‖ContinuousLinearMap.toSpanSingleton ℝ b‖ * ‖sndCLM‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ b‖ * 1 :=
        mul_le_mul_of_nonneg_left hsnd (norm_nonneg _)
      _ = ‖b‖ := by
        rw [mul_one, ContinuousLinearMap.norm_toSpanSingleton]
  change ‖a • D.comp fstCLM +
    euclideanFourierCharacter k z.1 •
      (ContinuousLinearMap.toSpanSingleton ℝ b).comp sndCLM‖ ≤ _
  calc
    ‖a • D.comp fstCLM + euclideanFourierCharacter k z.1 •
        (ContinuousLinearMap.toSpanSingleton ℝ b).comp sndCLM‖ ≤
      ‖a • D.comp fstCLM‖ +
        ‖euclideanFourierCharacter k z.1 •
          (ContinuousLinearMap.toSpanSingleton ℝ b).comp sndCLM‖ :=
      norm_add_le _ _
    _ = ‖a‖ * ‖D.comp fstCLM‖ +
        ‖euclideanFourierCharacter k z.1‖ *
          ‖(ContinuousLinearMap.toSpanSingleton ℝ b).comp sndCLM‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ ‖a‖ * ‖D‖ + ‖b‖ := by
      rw [norm_euclideanFourierCharacter, one_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hDcomp (norm_nonneg a)) hspanComp
    _ ≤ ‖a‖ *
          (2 * Real.pi * ∑ coordinate : Fin 3, |(k coordinate : ℝ)|) +
        tower.modalTimeDerivativeUniformBound nu *
          (periodicSobolevWeight 3 k)⁻¹ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (norm_euclideanFourierCharacterFDeriv_le k z.1)
          (norm_nonneg a)) htime
    _ = (2 * Real.pi * ∑ coordinate : Fin 3, |(k coordinate : ℝ)|) *
          ‖a‖ + tower.modalTimeDerivativeUniformBound nu *
            (periodicSobolevWeight 3 k)⁻¹ := by ring
    _ ≤ (6 * Real.pi * ‖tower.lift 5‖) *
          (periodicSobolevWeight 3 k)⁻¹ +
        tower.modalTimeDerivativeUniformBound nu *
          (periodicSobolevWeight 3 k)⁻¹ :=
      add_le_add hspaceSum le_rfl
    _ = CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound tower nu *
        (periodicSobolevWeight 3 k)⁻¹ := by
      unfold CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound
      ring

/-! ## Joint `C¹` reconstruction -/

/-- The complete complex component series has the exact joint spacetime Fréchet derivative on
the open restart slab. -/
theorem CoherentWeightedSmoothPathTower.hasFDerivAt_joint_complexVelocityComponent
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (z : Space × ℝ)
    (hz : z ∈ (univ : Set Space) ×ˢ Ioo (0 : ℝ) T) :
    HasFDerivAt
      (fun y : Space × ℝ ↦
        (weightedReconstructedVelocity hT base y.2 y.1 component : ℂ))
      (∑' k : SpatialFrequency,
        velocitySpacetimeFourierPassageFDeriv
          hT base nu component k z) z := by
  let u : SpatialFrequency → ℝ := fun k ↦
    CoherentWeightedSmoothPathTower.spacetimeFirstDerivativeUniformBound tower nu *
      (periodicSobolevWeight 3 k)⁻¹
  have hu : Summable u :=
    CoherentWeightedSmoothPathTower.summable_spacetimeFirstDerivativeMajorant tower nu
  have hmode : ∀ k y, y ∈ (univ : Set Space) ×ˢ Ioo (0 : ℝ) T →
      HasFDerivAt
        (velocitySpacetimeFourierPassage hT base component k)
        (velocitySpacetimeFourierPassageFDeriv
          hT base nu component k y) y := by
    intro k y hy
    exact hasFDerivAt_velocitySpacetimeFourierPassage
      hT nu hnu initial hfixed hreal component k y hy.2
  have hbound : ∀ k y, y ∈ (univ : Set Space) ×ˢ Ioo (0 : ℝ) T →
      ‖velocitySpacetimeFourierPassageFDeriv
        hT base nu component k y‖ ≤ u k := by
    intro k y hy
    exact CoherentWeightedSmoothPathTower.norm_velocitySpacetimeFourierPassageFDeriv_le
      hT tower nu hreal component k y hy.2
  have hbase : Summable (fun k ↦
      velocitySpacetimeFourierPassage hT base component k z) := by
    apply Summable.of_norm
    have hnative := summable_norm_nativeUnweightedComponent
      (base ⟨z.2, ⟨hz.2.1.le, hz.2.2.le⟩⟩) component
    apply hnative.congr
    intro k
    rw [velocitySpacetimeFourierPassage,
      weightedPathExtension_of_mem hT base ⟨hz.2.1.le, hz.2.2.le⟩,
      norm_mul, norm_euclideanFourierCharacter, mul_one]
    rfl
  have hseries := hasFDerivAt_tsum_of_isPreconnected
    (x₀ := z) (x := z) hu (isOpen_univ.prod isOpen_Ioo)
    (isPreconnected_univ.prod isPreconnected_Ioo)
    hmode hbound hz hbase hz
  have hfunction :
      (fun y : Space × ℝ ↦ ∑' k : SpatialFrequency,
        velocitySpacetimeFourierPassage hT base component k y) =
      (fun y : Space × ℝ ↦
        (weightedReconstructedVelocity hT base y.2 y.1 component : ℂ)) := by
    funext y
    rw [← tsum_weightedReconstructedVelocityCoefficient_mul_character
      hT hreal component y.1 y.2]
    apply tsum_congr
    intro k
    rw [velocitySpacetimeFourierPassage,
      weightedReconstructedVelocityCoefficient_eq_native hT hreal]
  rw [hfunction] at hseries
  exact hseries

/-- The operator-valued derivative series is continuous on the complete open slab. -/
theorem CoherentWeightedSmoothPathTower.continuousOn_joint_complexVelocityFDeriv
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) :
    ContinuousOn
      (fun z : Space × ℝ ↦ ∑' k : SpatialFrequency,
        velocitySpacetimeFourierPassageFDeriv
          hT base nu component k z)
      ((univ : Set Space) ×ˢ Ioo (0 : ℝ) T) := by
  apply continuousOn_tsum
  · intro k
    exact (continuous_velocitySpacetimeFourierPassageFDeriv
      hT base nu component k).continuousOn
  · exact CoherentWeightedSmoothPathTower.summable_spacetimeFirstDerivativeMajorant tower nu
  · intro k z hz
    exact CoherentWeightedSmoothPathTower.norm_velocitySpacetimeFourierPassageFDeriv_le
      hT tower nu hreal component k z hz.2

/-- Each complexified velocity component is genuinely jointly `C¹` on the open spacetime slab. -/
theorem CoherentWeightedSmoothPathTower.contDiffOn_one_joint_complexVelocityComponent
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) :
    ContDiffOn ℝ 1
      (fun z : Space × ℝ ↦
        (weightedReconstructedVelocity hT base z.2 z.1 component : ℂ))
      ((univ : Set Space) ×ˢ Ioo (0 : ℝ) T) := by
  rw [(isOpen_univ.prod isOpen_Ioo).contDiffOn_iff]
  intro z hz
  rw [contDiffAt_one_iff]
  refine ⟨fun y ↦ ∑' k : SpatialFrequency,
      velocitySpacetimeFourierPassageFDeriv
        hT base nu component k y,
    (univ : Set Space) ×ˢ Ioo (0 : ℝ) T,
    (isOpen_univ.prod isOpen_Ioo).mem_nhds hz,
    CoherentWeightedSmoothPathTower.continuousOn_joint_complexVelocityFDeriv
      hT tower nu hreal component, ?_⟩
  intro y hy
  exact CoherentWeightedSmoothPathTower.hasFDerivAt_joint_complexVelocityComponent
    hT tower nu hnu initial hfixed hreal component y hy

/-- **First joint spacetime bootstrap.**  The actual real reconstructed velocity is jointly
`C¹`; this is derived from the mild fixed equation and arbitrary spatial persistence, not placed
in a regularity premise. -/
theorem CoherentWeightedSmoothPathTower.contDiffOn_one_joint_reconstructedVelocity
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    ContDiffOn ℝ 1
      (fun z : Space × ℝ ↦
        weightedReconstructedVelocity hT base z.2 z.1)
      ((univ : Set Space) ×ˢ Ioo (0 : ℝ) T) := by
  apply contDiffOn_piLp'
  intro component
  have hcomplex :=
    CoherentWeightedSmoothPathTower.contDiffOn_one_joint_complexVelocityComponent
      hT tower nu hnu initial hfixed hreal component
  have hrealComponent := Complex.reCLM.contDiff.comp_contDiffOn hcomplex
  exact hrealComponent.congr (fun _ _ ↦ rfl)

/-! ## Cap-selected carrier receipt and the exact next elliptic port -/

/-- The cap-selected classical carrier therefore has joint spacetime `C¹` velocity on its native
open aperture. -/
theorem WeightedClassicalRestartCarrier.velocityJointC1
    {nu cap : ℝ} {hnu : 0 < nu} {hcap : 0 ≤ cap}
    {initial : PeriodicVectorWeightedSobolev 3}
    (carrier : WeightedClassicalRestartCarrier nu cap hnu hcap initial) :
    ContDiffOn ℝ 1
      (Function.uncurry
        (weightedClassicalRestartVelocity
          (weightedRestartTimeFromCap_pos hnu hcap).le carrier.path))
      ((univ : Set Space) ×ˢ
        Ioo (0 : ℝ) (weightedRestartTimeFromCap nu cap)) := by
  let hT := (weightedRestartTimeFromCap_pos hnu hcap).le
  have h :=
    CoherentWeightedSmoothPathTower.contDiffOn_one_joint_reconstructedVelocity
      hT carrier.tower (Real.toNNReal nu) (real_toNNReal_pos hnu) initial
    carrier.fixed carrier.fourierReal
  change ContDiffOn ℝ 1
    (fun z : Space × ℝ ↦
      weightedReconstructedVelocity hT carrier.path z.2 z.1)
    ((univ : Set Space) ×ˢ
      Ioo (0 : ℝ) (weightedRestartTimeFromCap nu cap))
  exact h

/-! ## The native first time jet forced by higher spatial persistence -/

/-- The native `H³` projected momentum state furnished by the coherent order-five velocity
face and order-four quadratic face.  This is an actual bounded Sobolev state, not a formal
coefficient population. -/
def CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivative
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (t : Icc (0 : ℝ) T) : PeriodicVectorWeightedSobolev 3 :=
  (nu : ℂ) •
      (∑ coordinate : Fin 3,
        finiteOrderVectorDerivativeToThree
          2 2 (by omega) (fun _ : Fin 2 ↦ coordinate) (tower.lift 2 t)) -
    periodicVectorWeightedLerayDivergenceConvolution
      4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t)

/-- The order-four quadratic lift has literally the projected base-path coefficient after
spending its one derivative. -/
theorem CoherentWeightedSmoothPathTower.orderFourLeraySource_coefficient_eq_base
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 3
      (periodicVectorWeightedLerayDivergenceConvolution
        4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t) component)).1 k =
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) component).1 k := by
  have hhigh := congrFun
    (vectorCoefficientAt_periodicVectorWeightedLerayDivergenceConvolution
      4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t) k) component
  have hbase := congrFun
    (vectorCoefficientAt_lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree (base t))
      (unweightedVectorThree (base t)) k) component
  change
    vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder 3
        (periodicVectorWeightedLerayDivergenceConvolution
          4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t))) k component =
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

/-- Every unweighted coefficient of the native first time jet is exactly the projected modal
momentum right-hand side. -/
theorem CoherentWeightedSmoothPathTower.weightedSobolevCoefficients_nativeProjectedTimeDerivative
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 3
      (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivative
        tower nu t component)).1 k =
      ((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          (weightedSobolevCoefficients 3 (base t component)).1 k -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base t))
          (unweightedVectorThree (base t)) component).1 k := by
  unfold CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivative
  have hsource :=
    CoherentWeightedSmoothPathTower.orderFourLeraySource_coefficient_eq_base
      tower t component k
  have hderivative : ∀ coordinate : Fin 3,
      ((((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
        (finiteOrderVectorDerivativeToThree
          2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
            (tower.lift 2 t) component k)) =
        orderedDerivativeMultiplier 2 (fun _ : Fin 2 ↦ coordinate) k *
          (weightedSobolevCoefficients 3 (base t component)).1 k := by
    intro coordinate
    exact (weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply
      2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
        (tower.lift 2 t) component k).trans (by
          rw [tower.weightedSobolevCoefficients_lift_eq_base])
  have hsymbol :
      (∑ coordinate : Fin 3,
        orderedDerivativeMultiplier 2 (fun _ : Fin 2 ↦ coordinate) k) =
        -(torusStokesEigenvalue k : ℂ) := by
    have h :=
      Soma.Holonics.Millennium.NavierStokesWeightedSmoothClassicalMomentum.sum_orderedDerivativeMultiplier_diagonalSecondWord k
    change
      (∑ coordinate : Fin 3,
        orderedDerivativeMultiplier 2 (fun _ : Fin 2 ↦ coordinate) k) =
          -(torusStokesEigenvalue k : ℂ) at h
    exact h
  have hviscous :
      (weightedSobolevCoefficients 3
        ((∑ coordinate : Fin 3,
          finiteOrderVectorDerivativeToThree
            2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
              (tower.lift 2 t)) component)).1 k =
        -(torusStokesEigenvalue k : ℂ) *
          (weightedSobolevCoefficients 3 (base t component)).1 k := by
    change ((((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
      (∑ coordinate : Fin 3,
        finiteOrderVectorDerivativeToThree
          2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
            (tower.lift 2 t) component k)) = _
    rw [Finset.mul_sum]
    simp_rw [hderivative]
    rw [← Finset.sum_mul, hsymbol]
  change
    ((((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
      ((nu : ℂ) *
          (∑ coordinate : Fin 3,
            finiteOrderVectorDerivativeToThree
              2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
                (tower.lift 2 t) component k) -
        periodicVectorWeightedLerayDivergenceConvolution
          4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t) component k)) = _
  calc
    ((((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
        ((nu : ℂ) *
            (∑ coordinate : Fin 3,
              finiteOrderVectorDerivativeToThree
                2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
                  (tower.lift 2 t) component k) -
          periodicVectorWeightedLerayDivergenceConvolution
            4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t) component k)) =
      (nu : ℂ) *
          (weightedSobolevCoefficients 3
            ((∑ coordinate : Fin 3,
              finiteOrderVectorDerivativeToThree
                2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
                  (tower.lift 2 t)) component)).1 k -
        (weightedSobolevCoefficients 3
          (periodicVectorWeightedLerayDivergenceConvolution
            4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t) component)).1 k := by
        change _ =
          (nu : ℂ) *
              ((((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
                (∑ coordinate : Fin 3,
                  finiteOrderVectorDerivativeToThree
                    2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
                      (tower.lift 2 t) component k)) -
            (((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
              periodicVectorWeightedLerayDivergenceConvolution
                4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t) component k
        ring
    _ = (nu : ℂ) *
          (-(torusStokesEigenvalue k : ℂ) *
            (weightedSobolevCoefficients 3 (base t component)).1 k) -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base t))
          (unweightedVectorThree (base t)) component).1 k := by
      rw [hviscous, hsource]
    _ = _ := by
      push_cast
      ring

/-- Bounded evaluation of one unweighted native Sobolev coefficient.  This is the separating
receiver used to commute the modal FTC identity through the Bochner integral. -/
def weightedVectorSobolevCoefficientCLM
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency) :
    PeriodicVectorWeightedSobolev order →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun state ↦
        (weightedSobolevCoefficients order (state component)).1 k
      map_add' := by
        intro left right
        change ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
            ((left + right) component k)) =
          ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
              left component k) +
            ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
              right component k)
        simp only [Pi.add_apply, lp.coeFn_add]
        ring
      map_smul' := by
        intro scalar state
        change ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
            ((scalar • state) component k)) =
          scalar * ((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
            state component k)
        simp only [Pi.smul_apply, lp.coeFn_smul, smul_eq_mul]
        ring }
    1 (fun state ↦ by
      have hcoefficient := norm_weightedSobolevCoefficients_apply_le
        order state component k
      have hinv :
          (Real.sqrt (periodicSobolevWeight order k))⁻¹ ≤ 1 := by
        exact inv_le_one_of_one_le₀
          (Real.one_le_sqrt.mpr (one_le_periodicSobolevWeight order k))
      calc
        ‖(weightedSobolevCoefficients order (state component)).1 k‖ ≤
            (Real.sqrt (periodicSobolevWeight order k))⁻¹ * ‖state‖ :=
          hcoefficient
        _ ≤ 1 * ‖state‖ :=
          mul_le_mul_of_nonneg_right hinv (norm_nonneg state))

@[simp]
theorem weightedVectorSobolevCoefficientCLM_apply
    (order : ℕ) (component : Fin 3) (k : SpatialFrequency)
    (state : PeriodicVectorWeightedSobolev order) :
    weightedVectorSobolevCoefficientCLM order component k state =
      (weightedSobolevCoefficients order (state component)).1 k :=
  rfl

/-- The complete population of bounded unweighted coefficient receivers separates native vector
Sobolev states. -/
theorem periodicVectorWeightedSobolev_eq_of_coefficients_eq
    {order : ℕ} {left right : PeriodicVectorWeightedSobolev order}
    (hcoeff : ∀ component k,
      weightedVectorSobolevCoefficientCLM order component k left =
        weightedVectorSobolevCoefficientCLM order component k right) :
    left = right := by
  funext component
  rw [← coefficientWeightedRealization_weightedSobolevCoefficients order
      (left component),
    ← coefficientWeightedRealization_weightedSobolevCoefficients order
      (right component)]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext k
  exact hcoeff component k

/-- The actual native projected first jet varies continuously on the closed addressed time
aperture. -/
def CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) :
    WeightedH3Path T where
  toFun t := CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivative
    tower nu t
  continuous_toFun := by
    have hviscous : Continuous (fun t : Icc (0 : ℝ) T ↦
        ∑ coordinate : Fin 3,
          finiteOrderVectorDerivativeToThree
            2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
              (tower.lift 2 t)) := by
      fun_prop
    have hsource : Continuous (fun t : Icc (0 : ℝ) T ↦
        periodicVectorWeightedLerayDivergenceConvolution
          4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t)) := by
      exact (((periodicVectorWeightedLerayDivergenceConvolutionContinuous
        4 (by norm_num)).continuous.comp (tower.lift 1).continuous).clm_apply
          (tower.lift 1).continuous).congr (fun _ ↦ rfl)
    change Continuous (fun t : Icc (0 : ℝ) T ↦
      (nu : ℂ) •
          (∑ coordinate : Fin 3,
            finiteOrderVectorDerivativeToThree
              2 2 (by omega) (fun _ : Fin 2 ↦ coordinate)
                (tower.lift 2 t)) -
        periodicVectorWeightedLerayDivergenceConvolution
          4 (by norm_num) (tower.lift 1 t) (tower.lift 1 t))
    exact ((continuous_const : Continuous
      (fun _ : Icc (0 : ℝ) T ↦ (nu : ℂ))).smul hviscous).sub hsource

@[simp]
theorem CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath_apply
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (t : Icc (0 : ℝ) T) :
    CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu t =
      CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivative tower nu t :=
  rfl

/-- **Strong native first-time bootstrap.**  The exact scalar modal ODE, the continuous native
projected jet, and bounded coefficient evaluation imply a genuine Banach-space derivative in
native `H³`.  The proof is coefficientwise FTC followed by separation of native states; it does
not assume strong time differentiability of the path. -/
theorem CoherentWeightedSmoothPathTower.hasDerivAt_weightedPathExtension_nativeProjectedTimeDerivative
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau ↦ weightedPathExtension hT base tau)
      (weightedPathExtension hT
        (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
          tower nu) t) t := by
  let jetPath : WeightedH3Path T :=
    CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu
  let f : ℝ → PeriodicVectorWeightedSobolev 3 :=
    fun tau ↦ weightedPathExtension hT base tau
  let g : ℝ → PeriodicVectorWeightedSobolev 3 :=
    fun tau ↦ weightedPathExtension hT jetPath tau
  have hf : Continuous f := (weightedPathExtension hT base).continuous
  have hg : Continuous g := (weightedPathExtension hT jetPath).continuous
  have hcoefficientDerivative : ∀ (component : Fin 3) (k : SpatialFrequency)
      {s : ℝ}, s ∈ Ioo (0 : ℝ) T →
      HasDerivAt
        (fun tau ↦ weightedVectorSobolevCoefficientCLM
          3 component k (f tau))
        (weightedVectorSobolevCoefficientCLM 3 component k (g s)) s := by
    intro component k s hs
    have hmodal :=
      fixedPoint_weightedMildMap_reconstructedCoefficient_hasDerivAt_projected
        nu hnu hT initial hfixed hreal component k hs
    have hfunction :
        (fun tau ↦ weightedVectorSobolevCoefficientCLM
          3 component k (f tau)) =
        (fun tau ↦ weightedReconstructedVelocityCoefficient
          hT base component k tau) := by
      funext tau
      rw [weightedVectorSobolevCoefficientCLM_apply]
      exact (weightedReconstructedVelocityCoefficient_eq_native
        hT hreal component k tau).symm
    rw [hfunction]
    convert hmodal using 1
    dsimp only [g, jetPath]
    rw [weightedVectorSobolevCoefficientCLM_apply,
      weightedPathExtension_of_mem hT
        (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
          tower nu) ⟨hs.1.le, hs.2.le⟩,
      CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath_apply,
      CoherentWeightedSmoothPathTower.weightedSobolevCoefficients_nativeProjectedTimeDerivative]
  letI : SecondCountableTopologyEither ℝ
      (PeriodicVectorWeightedSobolev 3) :=
    ⟨Or.inl inferInstance⟩
  have hmodel : HasDerivAt
      (fun y ↦ f t + ∫ s in t..y, g s)
      (g t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable t t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt).const_add (f t)
  have heventually :
      f =ᶠ[nhds t] (fun y ↦ f t + ∫ s in t..y, g s) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    apply periodicVectorWeightedSobolev_eq_of_coefficients_eq
    intro component k
    let L := weightedVectorSobolevCoefficientCLM 3 component k
    have hinside : uIcc t y ⊆ Ioo (0 : ℝ) T := by
      intro s hs
      exact ⟨(lt_min ht.1 hy.1).trans_le hs.1,
        hs.2.trans_lt (max_lt ht.2 hy.2)⟩
    have hderiv : ∀ s ∈ uIcc t y,
        HasDerivAt (fun tau ↦ L (f tau)) (L (g s)) s := by
      intro s hs
      exact hcoefficientDerivative component k (hinside hs)
    have hgintegrable : IntervalIntegrable g MeasureTheory.volume t y :=
      hg.intervalIntegrable t y
    have hcoefficientFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((L.continuous.comp hg).intervalIntegrable t y)
    change L (f y) = L (f t + ∫ s in t..y, g s)
    rw [L.map_add, ← L.intervalIntegral_comp_comm hgintegrable,
      hcoefficientFTC]
    abel
  change HasDerivAt f (g t) t
  exact hmodel.congr_of_eventuallyEq heventually

/-- The sharp next elliptic input is not pressure smoothness.  It is an actual continuous native
`H²` time derivative of the unprojected quadratic source, with the displayed Leibniz
constitutive law.  Applying `nativePressureFromH2` to this derivative would return the native
pressure time jet. -/
structure EllipticPressureFirstTimePort
    {T : ℝ} (hT : 0 ≤ T) (base : WeightedH3Path T) where
  velocityTimeDerivative : ℝ → PeriodicVectorWeightedSobolev 3
  sourceTimeDerivative : ℝ → PeriodicVectorWeightedSobolev 2
  velocityDerivativeContinuousOn :
    ContinuousOn velocityTimeDerivative (Ioo (0 : ℝ) T)
  sourceDerivativeContinuousOn :
    ContinuousOn sourceTimeDerivative (Ioo (0 : ℝ) T)
  velocityHasDerivAt : ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) T →
    HasDerivAt
      (fun tau ↦ weightedPathExtension hT base tau)
      (velocityTimeDerivative t) t
  sourceLeibniz : ∀ t ∈ Ioo (0 : ℝ) T,
    sourceTimeDerivative t =
      weightedUnprojectedDivergenceConvolution
        (velocityTimeDerivative t) (weightedPathExtension hT base t) +
      weightedUnprojectedDivergenceConvolution
        (weightedPathExtension hT base t) (velocityTimeDerivative t)

/-- Arbitrary spatial persistence plus the fixed mild equation actually supplies the sharp
elliptic first-time port.  In particular, the port is no longer an external regularity premise. -/
def CoherentWeightedSmoothPathTower.ellipticPressureFirstTimePort
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    EllipticPressureFirstTimePort hT base where
  velocityTimeDerivative := fun t ↦ weightedPathExtension hT
    (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
      tower nu) t
  sourceTimeDerivative := fun t ↦
    weightedUnprojectedDivergenceConvolution
      (weightedPathExtension hT
        (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
          tower nu) t)
      (weightedPathExtension hT base t) +
    weightedUnprojectedDivergenceConvolution
      (weightedPathExtension hT base t)
      (weightedPathExtension hT
        (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
          tower nu) t)
  velocityDerivativeContinuousOn :=
    (weightedPathExtension hT
      (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
        tower nu)).continuous.continuousOn
  sourceDerivativeContinuousOn := by
    have hvelocity : Continuous (fun t ↦ weightedPathExtension hT
        (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
          tower nu) t) :=
      (weightedPathExtension hT
        (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
          tower nu)).continuous
    have hbase : Continuous (fun t ↦ weightedPathExtension hT base t) :=
      (weightedPathExtension hT base).continuous
    have hleft : Continuous (fun t ↦
        weightedUnprojectedDivergenceConvolution
          (weightedPathExtension hT
            (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
              tower nu) t)
          (weightedPathExtension hT base t)) := by
      exact ((weightedUnprojectedDivergenceConvolutionContinuous.continuous.comp
        hvelocity).clm_apply hbase).congr (fun _ ↦ rfl)
    have hright : Continuous (fun t ↦
        weightedUnprojectedDivergenceConvolution
          (weightedPathExtension hT base t)
          (weightedPathExtension hT
            (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath
              tower nu) t)) := by
      exact ((weightedUnprojectedDivergenceConvolutionContinuous.continuous.comp
        hbase).clm_apply hvelocity).congr (fun _ ↦ rfl)
    exact (hleft.add hright).continuousOn
  velocityHasDerivAt := fun {_t} ht ↦
    CoherentWeightedSmoothPathTower.hasDerivAt_weightedPathExtension_nativeProjectedTimeDerivative
      hT tower nu hnu initial hfixed hreal ht
  sourceLeibniz := by
    intro t _ht
    rfl

/-- The concrete elliptic port immediately differentiates the native zero-gauge pressure; no
pressure regularity is assumed here. -/
theorem EllipticPressureFirstTimePort.hasDerivAt_weightedNativePressure
    {T : ℝ} {hT : 0 ≤ T} {base : WeightedH3Path T}
    (port : EllipticPressureFirstTimePort hT base)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau ↦ weightedNativePressure hT base tau)
      (nativePressureFromH2 (port.sourceTimeDerivative t)) t := by
  let B : PeriodicVectorWeightedSobolev 3 →L[ℝ]
      PeriodicVectorWeightedSobolev 3 →L[ℝ]
        PeriodicVectorWeightedSobolev 2 :=
    weightedUnprojectedDivergenceConvolutionContinuous.bilinearRestrictScalars ℝ
  have hu := port.velocityHasDerivAt ht
  have hoperator : HasDerivAt
      (fun tau ↦ B (weightedPathExtension hT base tau))
      (B (port.velocityTimeDerivative t)) t := by
    change HasDerivAt
      (B ∘ fun tau ↦ weightedPathExtension hT base tau)
      (B (port.velocityTimeDerivative t)) t
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one] using
        (B.hasFDerivAt.comp t hu.hasFDerivAt).hasDerivAt
  have hsource : HasDerivAt
      (fun tau ↦ B (weightedPathExtension hT base tau)
        (weightedPathExtension hT base tau))
      (B (port.velocityTimeDerivative t) (weightedPathExtension hT base t) +
        B (weightedPathExtension hT base t) (port.velocityTimeDerivative t)) t :=
    hoperator.clm_apply hu
  have hsource' : HasDerivAt
      (fun tau ↦ weightedUnprojectedQuadratic
        (weightedPathExtension hT base tau))
      (port.sourceTimeDerivative t) t := by
    rw [port.sourceLeibniz t ht]
    simpa only [weightedUnprojectedQuadratic, B,
      ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      weightedUnprojectedDivergenceConvolutionContinuous_apply] using hsource
  have hpressure :=
    (nativePressureFromH2.restrictScalars ℝ).hasFDerivAt.comp t
      hsource'.hasFDerivAt
  have hpressureFunction :
      (fun tau ↦ weightedNativePressure hT base tau) =
        ((nativePressureFromH2.restrictScalars ℝ) ∘
          fun tau ↦ weightedUnprojectedQuadratic
            (weightedPathExtension hT base tau)) := by
    funext tau
    simp only [weightedNativePressure, Function.comp_apply,
      weightedUnprojectedDivergenceState_eq_quadratic,
      ContinuousLinearMap.coe_restrictScalars']
  rw [hpressureFunction]
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one,
    ContinuousLinearMap.coe_restrictScalars'] using hpressure.hasDerivAt

/-- The elliptic port returns a continuously varying native pressure time jet. -/
theorem EllipticPressureFirstTimePort.continuousOn_nativePressureTimeDerivative
    {T : ℝ} {hT : 0 ≤ T} {base : WeightedH3Path T}
    (port : EllipticPressureFirstTimePort hT base) :
    ContinuousOn
      (fun t ↦ nativePressureFromH2 (port.sourceTimeDerivative t))
      (Ioo (0 : ℝ) T) :=
  nativePressureFromH2.continuous.comp_continuousOn
    port.sourceDerivativeContinuousOn

/-- Hence the actual native zero-gauge pressure path is `C¹` in interior time. -/
theorem EllipticPressureFirstTimePort.contDiffOn_one_weightedNativePressure
    {T : ℝ} {hT : 0 ≤ T} {base : WeightedH3Path T}
    (port : EllipticPressureFirstTimePort hT base) :
    ContDiffOn ℝ 1
      (fun t ↦ weightedNativePressure hT base t)
      (Ioo (0 : ℝ) T) := by
  rw [isOpen_Ioo.contDiffOn_iff]
  intro t ht
  rw [contDiffAt_one_iff]
  let D : ℝ → PeriodicWeightedSobolev 3 := fun s ↦
    nativePressureFromH2 (port.sourceTimeDerivative s)
  let D' : ℝ → (ℝ →L[ℝ] PeriodicWeightedSobolev 3) := fun s ↦
    ContinuousLinearMap.toSpanSingleton ℝ (D s)
  refine ⟨D', Ioo (0 : ℝ) T, Ioo_mem_nhds ht.1 ht.2, ?_, ?_⟩
  · have hD : ContinuousOn D (Ioo (0 : ℝ) T) := by
      exact port.continuousOn_nativePressureTimeDerivative
    have hcontinuous :=
      (ContinuousLinearMap.smulRightL ℝ ℝ
        (PeriodicWeightedSobolev 3) 1).continuous.comp_continuousOn hD
    exact hcontinuous.congr (fun _ _ ↦ rfl)
  · intro s hs
    exact (port.hasDerivAt_weightedNativePressure hs).hasFDerivAt

/-- Arbitrary spatial persistence and the actual fixed mild equation therefore derive native
interior `C¹` pressure in time, with no pressure differentiability premise. -/
theorem CoherentWeightedSmoothPathTower.contDiffOn_one_weightedNativePressure
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) :
    ContDiffOn ℝ 1
      (fun t ↦ weightedNativePressure hT base t)
      (Ioo (0 : ℝ) T) :=
  (CoherentWeightedSmoothPathTower.ellipticPressureFirstTimePort
    hT tower nu hnu initial hfixed hreal).contDiffOn_one_weightedNativePressure

section Audit

#print axioms CoherentWeightedSmoothPathTower.contDiffOn_one_joint_reconstructedVelocity
#print axioms WeightedClassicalRestartCarrier.velocityJointC1
#print axioms CoherentWeightedSmoothPathTower.hasDerivAt_weightedPathExtension_nativeProjectedTimeDerivative
#print axioms CoherentWeightedSmoothPathTower.ellipticPressureFirstTimePort
#print axioms EllipticPressureFirstTimePort.hasDerivAt_weightedNativePressure
#print axioms CoherentWeightedSmoothPathTower.contDiffOn_one_weightedNativePressure

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap
