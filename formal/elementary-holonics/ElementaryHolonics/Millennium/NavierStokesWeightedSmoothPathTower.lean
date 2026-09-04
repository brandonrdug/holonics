import ElementaryHolonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
import ElementaryHolonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum

/-!
# Coherent all-order native paths and their smooth spatial reconstruction

**[proved-derived]** A coherent path tower over one native weighted `H³` path supplies a
continuous native `H^(m+3)` lift for every finite `m`, with literal pointwise restriction back to
the same base occurrence.  Every addressed time face therefore reconstructs as one actual real
periodic `C∞` velocity.  Ordered derivative paths remain continuous in time, their torus
coefficients carry the exact Fourier multiplier word, and prepending a coordinate agrees with an
actual spatial Fréchet derivative.

For a Fourier-real fixed mild path, the tower's two summable coefficient majorants additionally
justify differentiation of the complete Fourier synthesis at every interior time.  The returned
time derivative is the exact projected modal momentum series.  Identifying its viscous and
quadratic-plus-pressure populations with physical spatial operators remains a separate
constitutive composition, so no pointwise Navier--Stokes equation is asserted here.
-/

noncomputable section

open Function Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.NavierStokesWeightedSpacetimeReconstruction

/-! ## Continuous coherent native lifts -/

/-- Continuous native paths at an arbitrary weighted Sobolev order. -/
abbrev WeightedSobolevPath (T : ℝ) (order : ℕ) :=
  C(Icc (0 : ℝ) T, PeriodicVectorWeightedSobolev order)

/-- One base `H³` path together with continuous lifts at every finite higher order.  Coherence is
an exact native restriction equality at every addressed time face, not a smoothness premise. -/
structure CoherentWeightedSmoothPathTower
    {T : ℝ} (base : WeightedH3Path T) where
  lift : ∀ m : ℕ, WeightedSobolevPath T (m + 3)
  restrict_lift : ∀ (m : ℕ) (t : Icc (0 : ℝ) T),
    periodicVectorWeightedSobolevRestrictCLM
      3 (m + 3) (by omega) (lift m t) = base t

/-- Evaluation at one addressed time returns the coherent native point tower required by the
finite-order reconstruction owner. -/
def CoherentWeightedSmoothPathTower.faceTower
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) : CompatibleNativeWeightedSobolevTower where
  base := base t
  lift := fun m ↦ tower.lift m t
  restrict_lift := fun m ↦ tower.restrict_lift m t

/-- Every unweighted coefficient of every lift is exactly the coefficient of the common base
path face. -/
theorem CoherentWeightedSmoothPathTower.weightedSobolevCoefficients_lift_eq_base
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (m : ℕ) (t : Icc (0 : ℝ) T)
    (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients (m + 3)
      (tower.lift m t component)).1 k =
      (weightedSobolevCoefficients 3 (base t component)).1 k := by
  have hrestriction := congrArg
    (fun state : PeriodicVectorWeightedSobolev 3 ↦
      (weightedSobolevCoefficients 3 (state component)).1 k)
    (tower.restrict_lift m t)
  change
    (weightedSobolevCoefficients 3
      (periodicWeightedSobolevRestrict
        3 (m + 3) (by omega) (tower.lift m t component))).1 k =
      (weightedSobolevCoefficients 3 (base t component)).1 k at hrestriction
  rw [weightedSobolevCoefficients_restrict_apply] at hrestriction
  exact hrestriction

/-! ## Continuous ordered derivative paths -/

/-- Spend one ordered word continuously along its supplied high-order native path. -/
def CoherentWeightedSmoothPathTower.finiteDerivativePath
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3) :
    WeightedH3Path T where
  toFun t := finiteOrderVectorDerivativeToThree
    m r hr word (tower.lift m t)
  continuous_toFun :=
    (finiteOrderVectorDerivativeToThree m r hr word).continuous.comp
      (tower.lift m).continuous

@[simp]
theorem CoherentWeightedSmoothPathTower.finiteDerivativePath_apply
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (t : Icc (0 : ℝ) T) :
    tower.finiteDerivativePath m r hr word t =
      finiteOrderVectorDerivativeToThree
        m r hr word (tower.lift m t) :=
  rfl

/-- Every derivative word reconstructs as one jointly continuous time--torus component field. -/
theorem CoherentWeightedSmoothPathTower.continuous_joint_finiteDerivativeComponent
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (component : Fin 3) :
    Continuous (fun z : Icc (0 : ℝ) T × SpatialTorus ↦
      reconstructedFiniteOrderTorusComplexComponent
        m r hr word (tower.lift m z.1) component z.2) := by
  simpa only [finiteDerivativePath_apply,
    reconstructedFiniteOrderTorusComplexComponent] using
      continuous_joint_reconstructedTorusComplexComponent
        (tower.finiteDerivativePath m r hr word) component

/-- Exact base-relative Fourier coefficient of every reconstructed ordered derivative path. -/
theorem CoherentWeightedSmoothPathTower.torusSpatialFourierCoeff_finiteDerivative
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (k : SpatialFrequency) :
    torusSpatialFourierCoeff
        (reconstructedFiniteOrderTorusComplexComponent
          m r hr word (tower.lift m t) component) k =
      orderedDerivativeMultiplier r word k *
        (weightedSobolevCoefficients 3 (base t component)).1 k := by
  rw [torusSpatialFourierCoeff_reconstructedFiniteOrderTorusComplexComponent,
    tower.weightedSobolevCoefficients_lift_eq_base]

/-- Prepending one coordinate to a tower word is its actual spatial partial derivative at every
addressed time face. -/
theorem CoherentWeightedSmoothPathTower.fderiv_finiteDerivative_apply_single
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (t : Icc (0 : ℝ) T) (component coordinate : Fin 3) (x : Space) :
    fderiv ℝ
        (reconstructedFiniteOrderComplexComponent
          m r (by omega) word (tower.lift m t) component) x
        (EuclideanSpace.single coordinate 1) =
      reconstructedFiniteOrderComplexComponent
        m (r + 1) hr (Fin.cons coordinate word)
          (tower.lift m t) component x :=
  fderiv_reconstructedFiniteOrderComplexComponent_apply_single
    m r hr word (tower.lift m t) component coordinate x

/-! ## The common actual smooth spatial velocity -/

/-- The actual real periodic velocity of one addressed face.  Its definition uses the common
base state; every lift is retained by `faceTower` as differentiation testimony. -/
def CoherentWeightedSmoothPathTower.reconstructedVelocity
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) : InitialVelocity :=
  reconstructedSmoothVelocity (tower.faceTower t)

/-- The tower velocity is literally the established physical reconstruction of the base face. -/
theorem CoherentWeightedSmoothPathTower.reconstructedVelocity_eq_base
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) :
    tower.reconstructedVelocity t =
      Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction.reconstructedVelocity
        (base t) :=
  rfl

/-- Every addressed face reconstructs as an actual real periodic `C∞` velocity. -/
theorem CoherentWeightedSmoothPathTower.contDiff_infty_reconstructedVelocity
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (tower.reconstructedVelocity t) :=
  contDiff_infty_reconstructedSmoothVelocity (tower.faceTower t)

/-- The common actual smooth velocity remains jointly continuous in space and addressed time. -/
theorem CoherentWeightedSmoothPathTower.continuous_joint_reconstructedVelocity
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) :
    Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      tower.reconstructedVelocity z.2 z.1) := by
  simpa only [tower.reconstructedVelocity_eq_base] using
    Soma.Holonics.Millennium.NavierStokesWeightedSpacetimeReconstruction.continuous_joint_reconstructedVelocity
      base

/-! ## Higher-order coefficient majorants for the modal time return -/

/-- The square root of an even Sobolev weight is exactly the half-order weight. -/
theorem sqrt_periodicSobolevWeight_even
    (n : ℕ) (k : SpatialFrequency) :
    Real.sqrt (periodicSobolevWeight (2 * n) k) =
      periodicSobolevWeight n k := by
  rw [periodicSobolevWeight, periodicSobolevWeight]
  rw [show (1 + torusStokesEigenvalue k) ^ (2 * n) =
      ((1 + torusStokesEigenvalue k) ^ n) ^ 2 by
    rw [← pow_mul]
    congr 1
    omega]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
  exact pow_nonneg
    (add_nonneg zero_le_one (torusStokesEigenvalue_nonneg k)) n

/-- One unweighted coefficient is bounded by the reciprocal square-root weight times the full
native vector norm. -/
theorem norm_weightedSobolevCoefficients_apply_le
    (order : ℕ) (state : PeriodicVectorWeightedSobolev order)
    (component : Fin 3) (k : SpatialFrequency) :
    ‖(weightedSobolevCoefficients order (state component)).1 k‖ ≤
      (Real.sqrt (periodicSobolevWeight order k))⁻¹ * ‖state‖ := by
  change ‖((((Real.sqrt (periodicSobolevWeight order k))⁻¹ : ℝ) : ℂ) *
      state component k)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    ((lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (state component) k).trans (norm_le_pi_norm state component))
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- The order-eight velocity lift supplies a reciprocal-`H³` majorant after multiplication by
the Stokes eigenvalue. -/
theorem stokes_mul_inv_sqrt_weight_eight_le_weight_three_inv
    (k : SpatialFrequency) :
    torusStokesEigenvalue k *
        (Real.sqrt (periodicSobolevWeight 8 k))⁻¹ ≤
      (periodicSobolevWeight 3 k)⁻¹ := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num,
    sqrt_periodicSobolevWeight_even]
  let a : ℝ := 1 + torusStokesEigenvalue k
  have ha : 0 < a := by
    dsimp [a]
    linarith [torusStokesEigenvalue_nonneg k]
  have hlambda : torusStokesEigenvalue k ≤ a := by
    dsimp [a]
    linarith
  rw [periodicSobolevWeight, periodicSobolevWeight]
  change torusStokesEigenvalue k * (a ^ 4)⁻¹ ≤ (a ^ 3)⁻¹
  calc
    torusStokesEigenvalue k * (a ^ 4)⁻¹ ≤
        a * (a ^ 4)⁻¹ :=
      mul_le_mul_of_nonneg_right hlambda (inv_nonneg.mpr (pow_nonneg ha.le 4))
    _ = (a ^ 3)⁻¹ := by
      field_simp [ne_of_gt ha]

/-- At output order six, reciprocal square-root weight is literally reciprocal `H³` weight. -/
theorem inv_sqrt_weight_six_eq_weight_three_inv
    (k : SpatialFrequency) :
    (Real.sqrt (periodicSobolevWeight 6 k))⁻¹ =
      (periodicSobolevWeight 3 k)⁻¹ := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num,
    sqrt_periodicSobolevWeight_even]

/-- The order-seven quadratic lift has exactly the same projected divergence coefficient as the
base `H³` path. -/
theorem CoherentWeightedSmoothPathTower.higherLeraySource_coefficient_eq_base
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 6
      (periodicVectorWeightedLerayDivergenceConvolution
        7 (by norm_num) (tower.lift 4 t) (tower.lift 4 t) component)).1 k =
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (base t))
        (unweightedVectorThree (base t)) component).1 k := by
  have hhigh := congrFun
    (vectorCoefficientAt_periodicVectorWeightedLerayDivergenceConvolution
      7 (by norm_num) (tower.lift 4 t) (tower.lift 4 t) k) component
  have hbase := congrFun
    (vectorCoefficientAt_lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree (base t))
      (unweightedVectorThree (base t)) k) component
  change
    vectorCoefficientAt
      (nativeVectorUnderlyingAtOrder 6
        (periodicVectorWeightedLerayDivergenceConvolution
          7 (by norm_num) (tower.lift 4 t) (tower.lift 4 t))) k component =
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

/-- The uniform native bound furnished by the continuous order-seven lift for its projected
quadratic order-six source. -/
def CoherentWeightedSmoothPathTower.higherLeraySourceUniformBound
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) : ℝ :=
  (36 * (2 : ℝ) ^ 7 * periodicH3EmbeddingConstant) *
    ‖tower.lift 4‖ ^ 2

theorem CoherentWeightedSmoothPathTower.higherLeraySourceUniformBound_nonneg
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) :
    0 ≤ tower.higherLeraySourceUniformBound := by
  unfold higherLeraySourceUniformBound
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 7))
      periodicH3EmbeddingConstant_nonneg)
    (sq_nonneg _)

/-- The Stokes-weighted base coefficient is uniformly dominated by the reciprocal `H³` weight,
using the continuous order-eight lift. -/
theorem CoherentWeightedSmoothPathTower.stokes_mul_norm_baseCoefficient_le
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (k : SpatialFrequency) :
    torusStokesEigenvalue k *
        ‖(weightedSobolevCoefficients 3 (base t component)).1 k‖ ≤
      ‖tower.lift 5‖ * (periodicSobolevWeight 3 k)⁻¹ := by
  rw [← tower.weightedSobolevCoefficients_lift_eq_base 5 t component k]
  have hcoefficient := norm_weightedSobolevCoefficients_apply_le
    8 (tower.lift 5 t) component k
  have hstate : ‖tower.lift 5 t‖ ≤ ‖tower.lift 5‖ :=
    (tower.lift 5).norm_coe_le_norm t
  calc
    torusStokesEigenvalue k *
        ‖(weightedSobolevCoefficients 8 (tower.lift 5 t component)).1 k‖ ≤
      torusStokesEigenvalue k *
        ((Real.sqrt (periodicSobolevWeight 8 k))⁻¹ *
          ‖tower.lift 5 t‖) :=
      mul_le_mul_of_nonneg_left hcoefficient (torusStokesEigenvalue_nonneg k)
    _ ≤ torusStokesEigenvalue k *
        ((Real.sqrt (periodicSobolevWeight 8 k))⁻¹ *
          ‖tower.lift 5‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hstate
          (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        (torusStokesEigenvalue_nonneg k)
    _ = (torusStokesEigenvalue k *
        (Real.sqrt (periodicSobolevWeight 8 k))⁻¹) *
          ‖tower.lift 5‖ := by ring
    _ ≤ (periodicSobolevWeight 3 k)⁻¹ * ‖tower.lift 5‖ :=
      mul_le_mul_of_nonneg_right
        (stokes_mul_inv_sqrt_weight_eight_le_weight_three_inv k)
        (norm_nonneg _)
    _ = ‖tower.lift 5‖ * (periodicSobolevWeight 3 k)⁻¹ := by ring

/-- The projected quadratic source coefficient is uniformly dominated by the same summable
reciprocal `H³` population, using the order-seven-to-six nonlinear passage. -/
theorem CoherentWeightedSmoothPathTower.norm_baseLeraySourceCoefficient_le
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (component : Fin 3) (k : SpatialFrequency) :
    ‖(lerayProjectedH3DivergenceConvolution
      (unweightedVectorThree (base t))
      (unweightedVectorThree (base t)) component).1 k‖ ≤
      tower.higherLeraySourceUniformBound *
        (periodicSobolevWeight 3 k)⁻¹ := by
  rw [← tower.higherLeraySource_coefficient_eq_base t component k]
  let source : PeriodicVectorWeightedSobolev 6 :=
    periodicVectorWeightedLerayDivergenceConvolution
      7 (by norm_num) (tower.lift 4 t) (tower.lift 4 t)
  have hcoefficient := norm_weightedSobolevCoefficients_apply_le
    6 source component k
  have hsource := norm_periodicVectorWeightedLerayDivergenceConvolution_le
    7 (by norm_num) (tower.lift 4 t) (tower.lift 4 t)
  have hstate : ‖tower.lift 4 t‖ ≤ ‖tower.lift 4‖ :=
    (tower.lift 4).norm_coe_le_norm t
  have hconstant :
      0 ≤ 36 * (2 : ℝ) ^ 7 * periodicH3EmbeddingConstant := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 7))
      periodicH3EmbeddingConstant_nonneg
  have hstatesSquare :
      ‖tower.lift 4 t‖ * ‖tower.lift 4 t‖ ≤ ‖tower.lift 4‖ ^ 2 := by
    nlinarith [norm_nonneg (tower.lift 4 t), norm_nonneg (tower.lift 4)]
  have hscaledStates :
      (36 * (2 : ℝ) ^ 7 * periodicH3EmbeddingConstant) *
          ‖tower.lift 4 t‖ * ‖tower.lift 4 t‖ ≤
        (36 * (2 : ℝ) ^ 7 * periodicH3EmbeddingConstant) *
          ‖tower.lift 4‖ ^ 2 := by
    calc
      (36 * (2 : ℝ) ^ 7 * periodicH3EmbeddingConstant) *
          ‖tower.lift 4 t‖ * ‖tower.lift 4 t‖ =
        (36 * (2 : ℝ) ^ 7 * periodicH3EmbeddingConstant) *
          (‖tower.lift 4 t‖ * ‖tower.lift 4 t‖) := by ring
      _ ≤ (36 * (2 : ℝ) ^ 7 * periodicH3EmbeddingConstant) *
          ‖tower.lift 4‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hstatesSquare hconstant
  calc
    ‖(weightedSobolevCoefficients 6 (source component)).1 k‖ ≤
        (Real.sqrt (periodicSobolevWeight 6 k))⁻¹ * ‖source‖ :=
      hcoefficient
    _ ≤ (Real.sqrt (periodicSobolevWeight 6 k))⁻¹ *
        ((36 * (2 : ℝ) ^ 7 * periodicH3EmbeddingConstant) *
          ‖tower.lift 4 t‖ * ‖tower.lift 4 t‖) := by
      exact mul_le_mul_of_nonneg_left (by simpa [source] using hsource)
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ (Real.sqrt (periodicSobolevWeight 6 k))⁻¹ *
        ((36 * (2 : ℝ) ^ 7 * periodicH3EmbeddingConstant) *
          ‖tower.lift 4‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        hscaledStates
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = tower.higherLeraySourceUniformBound *
        (periodicSobolevWeight 3 k)⁻¹ := by
      rw [inv_sqrt_weight_six_eq_weight_three_inv]
      unfold higherLeraySourceUniformBound
      ring

/-! ## Interior time differentiation of the complete Fourier sum -/

/-- One uniform coefficient majorant for the modal time derivative. -/
def CoherentWeightedSmoothPathTower.modalTimeDerivativeUniformBound
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) : ℝ :=
  (nu : ℝ) * ‖tower.lift 5‖ + tower.higherLeraySourceUniformBound

theorem CoherentWeightedSmoothPathTower.modalTimeDerivativeUniformBound_nonneg
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) :
    0 ≤ tower.modalTimeDerivativeUniformBound nu := by
  unfold modalTimeDerivativeUniformBound
  exact add_nonneg (mul_nonneg (NNReal.coe_nonneg nu) (norm_nonneg _))
    tower.higherLeraySourceUniformBound_nonneg

/-- The reciprocal-weight modal derivative majorant is summable on the complete lattice. -/
theorem CoherentWeightedSmoothPathTower.summable_modalTimeDerivativeMajorant
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) :
    Summable (fun k : SpatialFrequency ↦
      tower.modalTimeDerivativeUniformBound nu *
        (periodicSobolevWeight 3 k)⁻¹) :=
  summable_periodicSobolevWeight_three_inv.mul_left
    (tower.modalTimeDerivativeUniformBound nu)

/-- On the declared aperture, the actual reconstructed real-field coefficient is exactly the
coefficient of the common base path face. -/
theorem weightedReconstructedVelocityCoefficient_eq_base
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (k : SpatialFrequency) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    weightedReconstructedVelocityCoefficient hT base component k t =
      (weightedSobolevCoefficients 3
        (base ⟨t, ht⟩ component)).1 k := by
  rw [weightedReconstructedVelocityCoefficient_eq_native hT hreal,
    weightedPathExtension_of_mem hT base ht]

/-- The fixed-point coefficient ODE in projected form, now expressed entirely on the common base
face of the tower. -/
theorem fixedPoint_weightedMildMap_reconstructedCoefficient_hasDerivAt_projected
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) {base : WeightedH3Path T}
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (k : SpatialFrequency) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau : ℝ ↦
        weightedReconstructedVelocityCoefficient hT base component k tau)
      (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          (weightedSobolevCoefficients 3
            (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩ component)).1 k -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          component).1 k) t := by
  have hnative := fixedPoint_weightedMildMap_physicalCoefficient_hasDerivAt
    nu hnu hT initial base hfixed component k ht
  have hfunction :
      (fun tau : ℝ ↦
        weightedReconstructedVelocityCoefficient hT base component k tau) =
      (fun tau : ℝ ↦
        (weightedSobolevCoefficients 3
          (weightedPathExtension hT base tau component)).1 k) := by
    funext tau
    exact weightedReconstructedVelocityCoefficient_eq_native
      hT hreal component k tau
  rw [hfunction]
  have hextension := weightedPathExtension_of_mem hT base
    ⟨ht.1.le, ht.2.le⟩
  rw [hextension] at hnative
  exact hnative

/-- The complete modal derivative is uniformly dominated by the summable reciprocal `H³`
population throughout the interior aperture. -/
theorem CoherentWeightedSmoothPathTower.norm_modalDerivativeCoefficient_le
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (k : SpatialFrequency) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ‖(((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          weightedReconstructedVelocityCoefficient hT base component k t -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          component).1 k)‖ ≤
      tower.modalTimeDerivativeUniformBound nu *
        (periodicSobolevWeight 3 k)⁻¹ := by
  have hvelocity := tower.stokes_mul_norm_baseCoefficient_le
    ⟨t, ⟨ht.1.le, ht.2.le⟩⟩ component k
  have hsource := tower.norm_baseLeraySourceCoefficient_le
    ⟨t, ⟨ht.1.le, ht.2.le⟩⟩ component k
  rw [weightedReconstructedVelocityCoefficient_eq_base
    hT hreal component k ⟨ht.1.le, ht.2.le⟩]
  calc
    ‖(((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          (weightedSobolevCoefficients 3
            (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩ component)).1 k -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          component).1 k)‖ ≤
      ‖(((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          (weightedSobolevCoefficients 3
            (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩ component)).1 k)‖ +
        ‖(lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          component).1 k‖ := norm_sub_le _ _
    _ = (nu : ℝ) * torusStokesEigenvalue k *
          ‖(weightedSobolevCoefficients 3
            (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩ component)).1 k‖ +
        ‖(lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          (unweightedVectorThree (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
          component).1 k‖ := by
      rw [norm_mul]
      congr 2
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg nu)
          (torusStokesEigenvalue_nonneg k))]
    _ ≤ (nu : ℝ) *
          (‖tower.lift 5‖ * (periodicSobolevWeight 3 k)⁻¹) +
        tower.higherLeraySourceUniformBound *
          (periodicSobolevWeight 3 k)⁻¹ := by
      apply add_le_add
      · simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hvelocity (NNReal.coe_nonneg nu))
      · exact hsource
    _ = tower.modalTimeDerivativeUniformBound nu *
        (periodicSobolevWeight 3 k)⁻¹ := by
      unfold modalTimeDerivativeUniformBound
      ring

/-- At every real time, the complete series of actual reconstructed velocity coefficients is the
complexification of the actual real velocity component. -/
theorem tsum_weightedReconstructedVelocityCoefficient_mul_character
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (x : Space) (t : ℝ) :
    (∑' k : SpatialFrequency,
      weightedReconstructedVelocityCoefficient hT base component k t *
        euclideanFourierCharacter k x) =
      (weightedReconstructedVelocity hT base t x component : ℂ) := by
  let state := weightedPathExtension hT base t
  have hcomplex := congrFun
    (complexifySpace_reconstructedTorusReal (hreal.extension hT t)
      (euclideanToSpatialTorus x)) component
  change ((reconstructedTorusReal state (euclideanToSpatialTorus x) component : ℝ) : ℂ) =
      reconstructedTorusComplex state (euclideanToSpatialTorus x) component at hcomplex
  rw [reconstructedTorusComplex_apply] at hcomplex
  change (∑' k : SpatialFrequency,
      weightedReconstructedVelocityCoefficient hT base component k t *
        euclideanFourierCharacter k x) =
    ((reconstructedTorusReal state (euclideanToSpatialTorus x) component : ℝ) : ℂ)
  rw [hcomplex]
  rw [reconstructedTorusComplexComponent_apply]
  apply tsum_congr
  intro k
  rw [weightedReconstructedVelocityCoefficient_eq_native hT hreal,
    euclideanFourierCharacter_eq_mFourier]
  rfl

/-- **Strong interior time derivative of the reconstructed velocity component.**  The coherent
all-order path tower supplies the summable uniform majorant needed to commute the fixed-point
modal derivative through the complete Fourier sum. -/
theorem CoherentWeightedSmoothPathTower.hasDerivAt_reconstructedVelocity_component
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (component : Fin 3) (x : Space) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau : ℝ ↦
        (weightedReconstructedVelocity hT base tau x component : ℂ))
      (∑' k : SpatialFrequency,
        (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
            weightedReconstructedVelocityCoefficient
              hT base component k t -
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree
              (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
            (unweightedVectorThree
              (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩))
            component).1 k) * euclideanFourierCharacter k x) t := by
  let g : SpatialFrequency → ℝ → ℂ := fun k tau ↦
    weightedReconstructedVelocityCoefficient hT base component k tau *
      euclideanFourierCharacter k x
  let g' : SpatialFrequency → ℝ → ℂ := fun k tau ↦
    (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
        weightedReconstructedVelocityCoefficient hT base component k tau -
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree (weightedPathExtension hT base tau))
        (unweightedVectorThree (weightedPathExtension hT base tau))
        component).1 k) * euclideanFourierCharacter k x
  let u : SpatialFrequency → ℝ := fun k ↦
    tower.modalTimeDerivativeUniformBound nu *
      (periodicSobolevWeight 3 k)⁻¹
  have hu : Summable u :=
    tower.summable_modalTimeDerivativeMajorant nu
  have hg : ∀ k tau, tau ∈ Ioo (0 : ℝ) T →
      HasDerivAt (g k) (g' k tau) tau := by
    intro k tau htau
    have hcoefficient :=
      fixedPoint_weightedMildMap_reconstructedCoefficient_hasDerivAt_projected
        nu hnu hT initial hfixed hreal component k htau
    rw [← weightedReconstructedVelocityCoefficient_eq_base
      hT hreal component k ⟨htau.1.le, htau.2.le⟩] at hcoefficient
    have hproduct := hcoefficient.mul_const (euclideanFourierCharacter k x)
    simpa only [g, g', weightedPathExtension_of_mem hT base
      ⟨htau.1.le, htau.2.le⟩] using hproduct
  have hg' : ∀ k tau, tau ∈ Ioo (0 : ℝ) T → ‖g' k tau‖ ≤ u k := by
    intro k tau htau
    change ‖(((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          weightedReconstructedVelocityCoefficient hT base component k tau -
        (lerayProjectedH3DivergenceConvolution
          (unweightedVectorThree (weightedPathExtension hT base tau))
          (unweightedVectorThree (weightedPathExtension hT base tau))
          component).1 k) * euclideanFourierCharacter k x‖ ≤
      tower.modalTimeDerivativeUniformBound nu *
        (periodicSobolevWeight 3 k)⁻¹
    rw [show weightedPathExtension hT base tau =
        base ⟨tau, ⟨htau.1.le, htau.2.le⟩⟩ from
      weightedPathExtension_of_mem hT base ⟨htau.1.le, htau.2.le⟩]
    rw [norm_mul, norm_euclideanFourierCharacter, mul_one]
    exact tower.norm_modalDerivativeCoefficient_le
      hT nu hreal component k htau
  have hg0 : Summable (fun k ↦ g k t) := by
    apply Summable.of_norm
    have hnative := summable_norm_nativeUnweightedComponent
      (base ⟨t, ⟨ht.1.le, ht.2.le⟩⟩) component
    apply hnative.congr
    intro k
    rw [show g k t =
        weightedReconstructedVelocityCoefficient hT base component k t *
          euclideanFourierCharacter k x by rfl,
      norm_mul, norm_euclideanFourierCharacter, mul_one,
      weightedReconstructedVelocityCoefficient_eq_base
        hT hreal component k ⟨ht.1.le, ht.2.le⟩]
    rfl
  have hseries := hasDerivAt_tsum_of_isPreconnected
    (y₀ := t) hu isOpen_Ioo isPreconnected_Ioo hg hg' ht hg0 ht
  have hfunction :
      (fun tau : ℝ ↦ ∑' k : SpatialFrequency, g k tau) =
      (fun tau : ℝ ↦
        (weightedReconstructedVelocity hT base tau x component : ℂ)) := by
    funext tau
    exact tsum_weightedReconstructedVelocityCoefficient_mul_character
      hT hreal component x tau
  rw [hfunction] at hseries
  simpa only [g', weightedPathExtension_of_mem hT base
    ⟨ht.1.le, ht.2.le⟩] using hseries

section Audit

#print axioms CoherentWeightedSmoothPathTower.weightedSobolevCoefficients_lift_eq_base
#print axioms CoherentWeightedSmoothPathTower.continuous_joint_finiteDerivativeComponent
#print axioms CoherentWeightedSmoothPathTower.torusSpatialFourierCoeff_finiteDerivative
#print axioms CoherentWeightedSmoothPathTower.fderiv_finiteDerivative_apply_single
#print axioms CoherentWeightedSmoothPathTower.contDiff_infty_reconstructedVelocity
#print axioms CoherentWeightedSmoothPathTower.continuous_joint_reconstructedVelocity
#print axioms CoherentWeightedSmoothPathTower.hasDerivAt_reconstructedVelocity_component

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
