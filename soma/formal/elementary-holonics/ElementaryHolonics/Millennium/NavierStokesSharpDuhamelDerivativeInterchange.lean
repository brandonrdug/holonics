import ElementaryHolonics.Millennium.NavierStokesSharpDuhamelDerivativeIdentification
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Dominated spatial differentiation for the sharp Duhamel population

This module packages the first and second spatial derivatives of the exact positive-time `H2`
heat reconstruction as bounded operators.  Finite Euclidean basis expansion turns the already
proved addressed `D2` bounds into a full Hessian operator-norm majorant, so Mathlib's dominated
parametric-integral theorem applies without an assumed identification interface.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesSharpDuhamelDerivativeInterchange

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesSharpDuhamelDerivativeIdentification
open Soma.Holonics.Millennium.NavierStokesSharpDuhamelSecondDerivative
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivativeReconstruction
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelMeasurability
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Evaluation of one reconstructed retained derivative word, bundled as a bounded real-linear
map of its native weighted state. -/
def reconstructedFiniteOrderRealEvaluationCLM
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (component : Fin 3) (x : Space) :
    PeriodicVectorWeightedSobolev (m + 3) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((ContinuousMap.evalCLM ℂ (euclideanToSpatialTorus x)).restrictScalars ℝ).comp
      (((reconstructedTorusComplexComponentCLM component).restrictScalars ℝ).comp
        ((finiteOrderVectorDerivativeToThree m r hr word).restrictScalars ℝ)))

@[simp]
theorem reconstructedFiniteOrderRealEvaluationCLM_apply
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x : Space) :
    reconstructedFiniteOrderRealEvaluationCLM m r hr word component x state =
      reconstructedFiniteOrderRealComponent m r hr word state component x := by
  rfl

/-- The complete first Fréchet derivative operator of a retained real reconstruction, assembled
from its three addressed partial derivatives. -/
def reconstructedFiniteOrderRealFDerivStateCLM
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (component : Fin 3) (x : Space) :
    PeriodicVectorWeightedSobolev (m + 3) →L[ℝ] (Space →L[ℝ] ℝ) :=
  ∑ coordinate : Fin 3,
    (reconstructedFiniteOrderRealEvaluationCLM m (r + 1) hr
      (Fin.cons coordinate word) component x).smulRight
        (EuclideanSpace.proj coordinate : Space →L[ℝ] ℝ)

/-- The corresponding derivative operator for one supplied state. -/
def reconstructedFiniteOrderRealFDerivCLM
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x : Space) : Space →L[ℝ] ℝ :=
  reconstructedFiniteOrderRealFDerivStateCLM m r hr word component x state

@[simp]
theorem reconstructedFiniteOrderRealFDerivCLM_apply
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x direction : Space) :
    reconstructedFiniteOrderRealFDerivCLM m r hr word state component x direction =
      ∑ coordinate : Fin 3,
        reconstructedFiniteOrderRealComponent m (r + 1) hr
          (Fin.cons coordinate word) state component x * direction coordinate := by
  simp [reconstructedFiniteOrderRealFDerivCLM,
    reconstructedFiniteOrderRealFDerivStateCLM]

/-- The finite-basis operator is exactly the actual Fréchet derivative. -/
theorem reconstructedFiniteOrderRealFDerivCLM_eq_fderiv
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x : Space) :
    reconstructedFiniteOrderRealFDerivCLM m r hr word state component x =
      fderiv ℝ (reconstructedFiniteOrderRealComponent m r (by omega)
        word state component) x := by
  apply ContinuousLinearMap.ext
  intro direction
  have hdirection :
      direction = ∑ coordinate : Fin 3,
        direction coordinate • EuclideanSpace.single coordinate 1 := by
    simpa using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr direction).symm
  rw [reconstructedFiniteOrderRealFDerivCLM_apply]
  calc
    ∑ coordinate : Fin 3,
        reconstructedFiniteOrderRealComponent m (r + 1) hr
          (Fin.cons coordinate word) state component x * direction coordinate =
      ∑ coordinate : Fin 3, direction coordinate •
        fderiv ℝ (reconstructedFiniteOrderRealComponent m r (by omega)
          word state component) x (EuclideanSpace.single coordinate 1) := by
        apply Finset.sum_congr rfl
        intro coordinate _
        rw [fderiv_reconstructedFiniteOrderRealComponent_apply_single
          m r hr word state component coordinate x]
        simp [mul_comm]
    _ = fderiv ℝ (reconstructedFiniteOrderRealComponent m r (by omega)
          word state component) x
        (∑ coordinate : Fin 3,
          direction coordinate • EuclideanSpace.single coordinate 1) := by
      rw [map_sum]
      simp only [map_smul]
    _ = _ := congrArg
      (fderiv ℝ (reconstructedFiniteOrderRealComponent m r (by omega)
        word state component) x) hdirection.symm

/-- Exact derivative witness for the packaged first spatial operator. -/
theorem hasFDerivAt_reconstructedFiniteOrderRealComponent
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x : Space) :
    HasFDerivAt
      (reconstructedFiniteOrderRealComponent m r (by omega) word state component)
      (reconstructedFiniteOrderRealFDerivCLM m r hr word state component x) x := by
  rw [reconstructedFiniteOrderRealFDerivCLM_eq_fderiv]
  exact ((contDiff_one_reconstructedFiniteOrderRealComponent
    m r (by omega) word state component).differentiable (by norm_num) x).hasFDerivAt

/-- The Hessian operator for one supplied state. -/
def reconstructedFiniteOrderRealSecondFDerivCLM
    (m r : ℕ) (hr : r + 2 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x : Space) :
    Space →L[ℝ] (Space →L[ℝ] ℝ) :=
  ∑ first : Fin 3, ∑ second : Fin 3,
    reconstructedFiniteOrderRealComponent m (r + 2) hr
      (Fin.cons second (Fin.cons first word)) state component x •
        ((EuclideanSpace.proj second : Space →L[ℝ] ℝ).smulRight
          (EuclideanSpace.proj first : Space →L[ℝ] ℝ))

@[simp]
theorem reconstructedFiniteOrderRealSecondFDerivCLM_apply
    (m r : ℕ) (hr : r + 2 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x outer inner : Space) :
    reconstructedFiniteOrderRealSecondFDerivCLM
        m r hr word state component x outer inner =
      ∑ first : Fin 3, ∑ second : Fin 3,
        reconstructedFiniteOrderRealComponent m (r + 2) hr
          (Fin.cons second (Fin.cons first word)) state component x *
            outer second * inner first := by
  simp [reconstructedFiniteOrderRealSecondFDerivCLM,
    mul_assoc]

/-- The packaged Hessian is the genuine derivative of the packaged first derivative. -/
theorem hasFDerivAt_reconstructedFiniteOrderRealFDerivCLM
    (m r : ℕ) (hr : r + 2 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x : Space) :
    HasFDerivAt
      (fun y ↦ reconstructedFiniteOrderRealFDerivCLM
        m r (by omega) word state component y)
      (reconstructedFiniteOrderRealSecondFDerivCLM
        m r hr word state component x) x := by
  have hsum : HasFDerivAt
      (∑ first : Fin 3, fun y : Space ↦
        reconstructedFiniteOrderRealComponent m (r + 1) (by omega)
          (Fin.cons first word) state component y •
            (EuclideanSpace.proj first : Space →L[ℝ] ℝ))
      (∑ first : Fin 3,
        (reconstructedFiniteOrderRealFDerivCLM m (r + 1) (by omega)
          (Fin.cons first word) state component x).smulRight
            (EuclideanSpace.proj first : Space →L[ℝ] ℝ)) x := by
    apply HasFDerivAt.sum
    intro first _
    exact (hasFDerivAt_reconstructedFiniteOrderRealComponent
      m (r + 1) (by omega) (Fin.cons first word) state component x).smul_const
        (EuclideanSpace.proj first : Space →L[ℝ] ℝ)
  convert hsum using 1
  · funext y
    apply ContinuousLinearMap.ext
    intro direction
    simp [reconstructedFiniteOrderRealFDerivCLM_apply]
  · apply ContinuousLinearMap.ext
    intro outer
    apply ContinuousLinearMap.ext
    intro inner
    simp [reconstructedFiniteOrderRealSecondFDerivCLM_apply,
      reconstructedFiniteOrderRealFDerivCLM_apply, Finset.sum_mul, mul_assoc]

/-- Three coordinate receivers control the full first-derivative operator norm. -/
theorem norm_reconstructedFiniteOrderRealFDerivCLM_le
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x : Space) {M : ℝ} (hM : 0 ≤ M)
    (hcoordinate : ∀ coordinate : Fin 3,
      ‖reconstructedFiniteOrderRealComponent m (r + 1) hr
        (Fin.cons coordinate word) state component x‖ ≤ M) :
    ‖reconstructedFiniteOrderRealFDerivCLM
      m r hr word state component x‖ ≤ 3 * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hM)
  intro direction
  rw [reconstructedFiniteOrderRealFDerivCLM_apply]
  calc
    ‖∑ coordinate : Fin 3,
        reconstructedFiniteOrderRealComponent m (r + 1) hr
          (Fin.cons coordinate word) state component x * direction coordinate‖ ≤
      ∑ coordinate : Fin 3,
        ‖reconstructedFiniteOrderRealComponent m (r + 1) hr
          (Fin.cons coordinate word) state component x * direction coordinate‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _coordinate : Fin 3, M * ‖direction‖ := by
      apply Finset.sum_le_sum
      intro coordinate _
      rw [norm_mul]
      exact mul_le_mul (hcoordinate coordinate)
        (PiLp.norm_apply_le direction coordinate) (norm_nonneg _) hM
    _ = (3 * M) * ‖direction‖ := by simp; ring

/-- The nine addressed second derivatives control the complete Hessian operator norm. -/
theorem norm_reconstructedFiniteOrderRealSecondFDerivCLM_le
    (m r : ℕ) (hr : r + 2 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicVectorWeightedSobolev (m + 3))
    (component : Fin 3) (x : Space) {M : ℝ} (hM : 0 ≤ M)
    (hcoordinate : ∀ first second : Fin 3,
      ‖reconstructedFiniteOrderRealComponent m (r + 2) hr
        (Fin.cons second (Fin.cons first word)) state component x‖ ≤ M) :
    ‖reconstructedFiniteOrderRealSecondFDerivCLM
      m r hr word state component x‖ ≤ 9 * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hM)
  intro outer
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num) hM) (norm_nonneg outer))
  intro inner
  rw [reconstructedFiniteOrderRealSecondFDerivCLM_apply]
  calc
    ‖∑ first : Fin 3, ∑ second : Fin 3,
        reconstructedFiniteOrderRealComponent m (r + 2) hr
          (Fin.cons second (Fin.cons first word)) state component x *
            outer second * inner first‖ ≤
      ∑ first : Fin 3, ∑ second : Fin 3,
        ‖reconstructedFiniteOrderRealComponent m (r + 2) hr
          (Fin.cons second (Fin.cons first word)) state component x *
            outer second * inner first‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun first _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _first : Fin 3, ∑ _second : Fin 3,
        M * ‖outer‖ * ‖inner‖ := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      simp only [norm_mul]
      exact mul_le_mul
        (mul_le_mul (hcoordinate first second)
          (PiLp.norm_apply_le outer second) (norm_nonneg _) hM)
        (PiLp.norm_apply_le inner first) (norm_nonneg _)
        (mul_nonneg hM (norm_nonneg outer))
    _ = ((9 * M) * ‖outer‖) * ‖inner‖ := by simp; ring

/-! ## The positive-time `H2` heat specialization -/

/-- Full first spatial derivative of the exact scalar `H2 -> H5` heat reconstruction. -/
def reconstructedHeatH2FirstFDerivCLM
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component : Fin 3) (x : Space) : Space →L[ℝ] ℝ :=
  reconstructedFiniteOrderRealFDerivCLM 2 0 (by omega)
    (fun i ↦ Fin.elim0 i) (vectorHeatH2ToH5 nu dt h source) component x

/-- Full Hessian of the same exact heat reconstruction. -/
def reconstructedHeatH2SecondFDerivCLM
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component : Fin 3) (x : Space) :
    Space →L[ℝ] (Space →L[ℝ] ℝ) :=
  reconstructedFiniteOrderRealSecondFDerivCLM 2 0 (by omega)
    (fun i ↦ Fin.elim0 i) (vectorHeatH2ToH5 nu dt h source) component x

theorem hasFDerivAt_reconstructedHeatH2Component_full
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component : Fin 3) (x : Space) :
    HasFDerivAt (reconstructedHeatH2Component nu dt h source component)
      (reconstructedHeatH2FirstFDerivCLM nu dt h source component x) x := by
  exact hasFDerivAt_reconstructedFiniteOrderRealComponent
    2 0 (by omega) (fun i ↦ Fin.elim0 i)
      (vectorHeatH2ToH5 nu dt h source) component x

theorem hasFDerivAt_reconstructedHeatH2FirstFDerivCLM
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component : Fin 3) (x : Space) :
    HasFDerivAt
      (reconstructedHeatH2FirstFDerivCLM nu dt h source component)
      (reconstructedHeatH2SecondFDerivCLM nu dt h source component x) x := by
  exact hasFDerivAt_reconstructedFiniteOrderRealFDerivCLM
    2 0 (by omega) (fun i ↦ Fin.elim0 i)
      (vectorHeatH2ToH5 nu dt h source) component x

private theorem norm_reconstructedComponent_le_coefficientMass
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) (x : Space) :
    ‖reconstructedTorusComplexComponent state component (euclideanToSpatialTorus x)‖ ≤
      ∑' k : SpatialFrequency, ‖nativeUnweightedComponent state component k‖ := by
  rw [reconstructedTorusComplexComponent_apply]
  have hterms : Summable fun k : SpatialFrequency ↦
      ‖nativeUnweightedComponent state component k *
        UnitAddTorus.mFourier k (euclideanToSpatialTorus x)‖ := by
    apply (summable_norm_nativeUnweightedComponent state component).congr
    intro k
    rw [norm_mul]
    simp [UnitAddTorus.mFourier, norm_prod, Circle.norm_coe]
  exact (norm_tsum_le_tsum_norm hterms).trans_eq (by
    apply tsum_congr
    intro k
    rw [norm_mul]
    simp [UnitAddTorus.mFourier, norm_prod, Circle.norm_coe])

private theorem norm_firstCoordinateMultiplier_le_stokes
    (coordinate : Fin 3) (k : SpatialFrequency) :
    ‖orderedDerivativeMultiplier 1 (![coordinate]) k‖ ≤ torusStokesEigenvalue k := by
  have hcoordinate : |(k coordinate : ℝ)| ≤ frequencySquared k := by
    have hsquare : (k coordinate : ℝ) ^ 2 ≤ frequencySquared k := by
      unfold frequencySquared
      exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ))
        (Finset.mem_univ coordinate)
    by_cases hk : k coordinate = 0
    · rw [hk]
      norm_num
      unfold frequencySquared
      positivity
    · have habs : 1 ≤ |(k coordinate : ℝ)| := by
        exact_mod_cast (Int.one_le_abs hk)
      nlinarith [sq_abs (k coordinate : ℝ)]
  simp only [orderedDerivativeMultiplier, Fin.prod_univ_one,
    Matrix.cons_val_zero, coordinateFourierMultiplier, norm_mul,
    Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  unfold torusStokesEigenvalue
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hfrequency : 0 ≤ frequencySquared k := by
    unfold frequencySquared
    positivity
  rw [Complex.norm_ofNat, Complex.norm_intCast]
  change 2 * Real.pi * |(k coordinate : ℝ)| ≤
    (2 * Real.pi) ^ 2 * frequencySquared k
  calc
    2 * Real.pi * |(k coordinate : ℝ)| ≤
        2 * Real.pi * frequencySquared k :=
      mul_le_mul_of_nonneg_left hcoordinate (by positivity)
    _ ≤ (2 * Real.pi) ^ 2 * frequencySquared k := by
      apply mul_le_mul_of_nonneg_right _ hfrequency
      nlinarith

private theorem receiverTerm_eq_kernelNormMulH2
    (a : ℝ) (ha : 0 < a) (state : PeriodicWeightedSobolev 2)
    (k : SpatialFrequency) :
    torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) *
        ‖weightedSobolevRawCoefficients 2 state k‖ =
      ‖heatSecondDerivativeH2Kernel a ha k‖ * ‖weightedStateAbsolute 2 state k‖ := by
  have hsqrt : 0 < Real.sqrt (periodicSobolevWeight 2 k) :=
    Real.sqrt_pos.2 (periodicSobolevWeight_pos 2 k)
  have hk : 0 ≤ torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) /
      Real.sqrt (periodicSobolevWeight 2 k) :=
    div_nonneg (mul_nonneg (torusStokesEigenvalue_nonneg k) (Real.exp_pos _).le) hsqrt.le
  change torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) *
      ‖((((Real.sqrt (periodicSobolevWeight 2 k))⁻¹ : ℝ) : ℂ) * state k)‖ =
    ‖torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) /
      Real.sqrt (periodicSobolevWeight 2 k)‖ * ‖‖state k‖‖
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk,
    Real.norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt]
  field_simp

/-- Every addressed first derivative is bounded by the already sharp second-derivative
coefficient mass.  The zero mode vanishes and every nonzero first symbol is dominated by the
periodic Stokes eigenvalue. -/
theorem norm_reconstructedHeatH2FirstDerivative_le_coefficientMass
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component coordinate : Fin 3) (x : Space) :
    ‖reconstructedFiniteOrderRealComponent 2 1 (by omega) (![coordinate])
      (vectorHeatH2ToH5 nu dt h source) component x‖ ≤
      heatSecondDerivativeCoefficientMass 2 ((nu : ℝ) * (dt : ℝ))
        (source component) := by
  let derivativeState := finiteOrderVectorDerivativeToThree 2 1 (by omega)
    (![coordinate]) (vectorHeatH2ToH5 nu dt h source)
  have hcomplex := norm_reconstructedComponent_le_coefficientMass derivativeState component x
  have hreal :
      ‖reconstructedFiniteOrderRealComponent 2 1 (by omega) (![coordinate])
        (vectorHeatH2ToH5 nu dt h source) component x‖ ≤
      ‖reconstructedTorusComplexComponent derivativeState component
        (euclideanToSpatialTorus x)‖ := Complex.abs_re_le_norm _
  refine hreal.trans (hcomplex.trans ?_)
  unfold heatSecondDerivativeCoefficientMass
  have hholder : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hreceiver : Summable fun k : SpatialFrequency ↦
      torusStokesEigenvalue k * Real.exp (-((nu : ℝ) * (dt : ℝ)) *
        torusStokesEigenvalue k) *
        ‖weightedSobolevRawCoefficients 2 (source component) k‖ := by
    apply (lp.summable_mul hholder
      (heatSecondDerivativeH2Kernel ((nu : ℝ) * (dt : ℝ)) h)
      (weightedStateAbsolute 2 (source component))).congr
    intro k
    exact (receiverTerm_eq_kernelNormMulH2 ((nu : ℝ) * (dt : ℝ)) h
      (source component) k).symm
  apply Summable.tsum_le_tsum
  · intro k
    dsimp [nativeUnweightedComponent, derivativeState]
    rw [weightedSobolevCoefficients_finiteOrderDerivativeToThree_apply,
      weightedCoefficients_vectorHeatH2ToH5]
    rw [norm_mul, norm_mul, Complex.norm_real]
    simp only [heatStokesMultiplier]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change ‖orderedDerivativeMultiplier 1 (![coordinate]) k‖ *
        (Real.exp (-((nu : ℝ) * (dt : ℝ) * torusStokesEigenvalue k)) *
          ‖weightedSobolevRawCoefficients 2 (source component) k‖) ≤ _
    calc
      _ ≤ torusStokesEigenvalue k *
          (Real.exp (-((nu : ℝ) * (dt : ℝ) * torusStokesEigenvalue k)) *
            ‖weightedSobolevRawCoefficients 2 (source component) k‖) :=
        mul_le_mul_of_nonneg_right (norm_firstCoordinateMultiplier_le_stokes coordinate k)
          (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ = _ := by
        simp only [weightedSobolevRawCoefficients]
        ring_nf
  · exact summable_norm_nativeUnweightedComponent derivativeState component
  · exact hreceiver

/-- Endpoint-totalized full first derivative of the sharp scalar Duhamel integrand. -/
def sharpDuhamelFirstFDerivIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (s : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  if hs : s < t then
    reconstructedHeatH2FirstFDerivCLM nu (positiveElapsed t s hs)
      (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s)) component x
  else
    0

/-- Endpoint-totalized full Hessian of the same integrand. -/
def sharpDuhamelSecondFDerivIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (s : ℝ) (x : Space) :
    Space →L[ℝ] (Space →L[ℝ] ℝ) :=
  if hs : s < t then
    reconstructedHeatH2SecondFDerivCLM nu (positiveElapsed t s hs)
      (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s)) component x
  else
    0

/-- Every time slice has the packaged full first derivative, including the totalized endpoint. -/
theorem hasFDerivAt_sharpDuhamelScalarIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (s : ℝ) (x : Space) :
    HasFDerivAt
      (fun y ↦ sharpDuhamelScalarIntegrand nu hnu t path component s y)
      (sharpDuhamelFirstFDerivIntegrand nu hnu t path component s x) x := by
  by_cases hs : s < t
  · simp only [sharpDuhamelScalarIntegrand, sharpDuhamelFirstFDerivIntegrand, dif_pos hs]
    exact hasFDerivAt_reconstructedHeatH2Component_full nu (positiveElapsed t s hs)
      (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s)) component x
  · simp only [sharpDuhamelScalarIntegrand, sharpDuhamelFirstFDerivIntegrand, dif_neg hs]
    exact hasFDerivAt_const 0 x

/-- Every time slice's first-derivative operator has the packaged full Hessian. -/
theorem hasFDerivAt_sharpDuhamelFirstFDerivIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (s : ℝ) (x : Space) :
    HasFDerivAt
      (sharpDuhamelFirstFDerivIntegrand nu hnu t path component s)
      (sharpDuhamelSecondFDerivIntegrand nu hnu t path component s x) x := by
  by_cases hs : s < t
  · rw [show sharpDuhamelFirstFDerivIntegrand nu hnu t path component s =
        reconstructedHeatH2FirstFDerivCLM nu (positiveElapsed t s hs)
          (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s)) component by
        funext y
        simp only [sharpDuhamelFirstFDerivIntegrand, dif_pos hs] ]
    simp only [sharpDuhamelSecondFDerivIntegrand, dif_pos hs]
    exact hasFDerivAt_reconstructedHeatH2FirstFDerivCLM nu (positiveElapsed t s hs)
      (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s)) component x
  · rw [show sharpDuhamelFirstFDerivIntegrand nu hnu t path component s =
        (fun _ : Space ↦ (0 : Space →L[ℝ] ℝ)) by
        funext y
        simp only [sharpDuhamelFirstFDerivIntegrand, dif_neg hs] ]
    simp only [sharpDuhamelSecondFDerivIntegrand, dif_neg hs]
    exact hasFDerivAt_const (0 : Space →L[ℝ] ℝ) x

/-- A full first derivative costs at most three copies of the sharp `D2` coefficient mass. -/
theorem norm_reconstructedHeatH2FirstFDerivCLM_le
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component : Fin 3) (x : Space) :
    ‖reconstructedHeatH2FirstFDerivCLM nu dt h source component x‖ ≤
      3 * heatSecondDerivativeCoefficientMass 2 ((nu : ℝ) * (dt : ℝ))
        (source component) := by
  apply norm_reconstructedFiniteOrderRealFDerivCLM_le
    2 0 (by omega) (fun i ↦ Fin.elim0 i)
      (vectorHeatH2ToH5 nu dt h source) component x
  · unfold heatSecondDerivativeCoefficientMass
    exact tsum_nonneg fun k ↦ mul_nonneg
      (mul_nonneg (torusStokesEigenvalue_nonneg k) (Real.exp_pos _).le) (norm_nonneg _)
  · intro coordinate
    have hword : Fin.cons coordinate (fun i ↦ Fin.elim0 i) = (![coordinate]) := by
      funext i
      fin_cases i
      rfl
    rw [hword]
    exact norm_reconstructedHeatH2FirstDerivative_le_coefficientMass
      nu dt h source component coordinate x

/-- The full Hessian costs exactly the finite nine-entry basis factor over the sharp coefficient
mass. -/
theorem norm_reconstructedHeatH2SecondFDerivCLM_le
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component : Fin 3) (x : Space) :
    ‖reconstructedHeatH2SecondFDerivCLM nu dt h source component x‖ ≤
      9 * heatSecondDerivativeCoefficientMass 2 ((nu : ℝ) * (dt : ℝ))
        (source component) := by
  apply norm_reconstructedFiniteOrderRealSecondFDerivCLM_le
    2 0 (by omega) (fun i ↦ Fin.elim0 i)
      (vectorHeatH2ToH5 nu dt h source) component x
  · unfold heatSecondDerivativeCoefficientMass
    exact tsum_nonneg fun k ↦ mul_nonneg
      (mul_nonneg (torusStokesEigenvalue_nonneg k) (Real.exp_pos _).le) (norm_nonneg _)
  · intro first second
    have hword : Fin.cons second (Fin.cons first (fun i ↦ Fin.elim0 i)) =
        secondCoordinateWord first second := by
      funext i
      fin_cases i <;> rfl
    rw [hword]
    exact norm_reconstructedHeatH2SecondDerivative_le_coefficientMass
      nu dt h source component first second x

/-- The time-varying operator majorant; it is the sharp physical `D2` majorant with only the
finite nine-entry basis factor. -/
def sharpDuhamelSecondFDerivMajorant
    (nu : ℝ≥0) (t : ℝ) (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (s : ℝ) : ℝ :=
  9 * sharpDuhamelSecondDerivativeMajorant nu t path s

theorem norm_sharpDuhamelSecondFDerivIntegrand_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t s : ℝ) (hs : s < t)
    (hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (x : Space) :
    ‖sharpDuhamelSecondFDerivIntegrand nu hnu t path component s x‖ ≤
      sharpDuhamelSecondFDerivMajorant nu t path s := by
  rw [sharpDuhamelSecondFDerivIntegrand, dif_pos hs]
  have hbase := norm_reconstructedHeatH2SecondFDerivCLM_le
    nu (positiveElapsed t s hs) (mul_pos hnu (sub_pos.mpr hs))
      (sharpNonlinearSource (path s)) component x
  have hmass := heatSecondDerivativeCoefficientMass_from_weightedH2_le
    ((nu : ℝ) * ((positiveElapsed t s hs : ℝ≥0) : ℝ))
      (by simpa only [coe_positiveElapsed] using mul_pos hnu (sub_pos.mpr hs))
      (by simpa only [coe_positiveElapsed] using hlocal)
      (sharpNonlinearSource (path s) component)
  have hsource := norm_sharpNonlinearSource_component_le (path s) component
  have hfactor : 0 ≤ sharpHeatSecondDerivativeH2Constant *
      (2 * ((nu : ℝ) * (t - s))) ^ (-3 / 4 : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)
  calc
    _ ≤ 9 * heatSecondDerivativeCoefficientMass 2
        ((nu : ℝ) * ((positiveElapsed t s hs : ℝ≥0) : ℝ))
          (sharpNonlinearSource (path s) component) := hbase
    _ ≤ 9 * (sharpHeatSecondDerivativeH2Constant *
        (2 * ((nu : ℝ) * (t - s))) ^ (-3 / 4 : ℝ) *
          ‖sharpNonlinearSource (path s) component‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [coe_positiveElapsed] using hmass
    _ ≤ 9 * (sharpHeatSecondDerivativeH2Constant *
        (2 * ((nu : ℝ) * (t - s))) ^ (-3 / 4 : ℝ) *
          ((23328 * periodicH3EmbeddingConstant) * ‖path s‖ ^ 2)) := by
      gcongr
    _ = sharpDuhamelSecondFDerivMajorant nu t path s := by
      unfold sharpDuhamelSecondFDerivMajorant sharpDuhamelSecondDerivativeMajorant
        sharpDuhamelSecondDerivativeConstant
      have htime : 0 ≤ (nu : ℝ) * (t - s) :=
        mul_nonneg hnu.le (sub_pos.mpr hs).le
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) htime]
      ring

theorem norm_sharpDuhamelFirstFDerivIntegrand_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t s : ℝ) (hs : s < t)
    (hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (x : Space) :
    ‖sharpDuhamelFirstFDerivIntegrand nu hnu t path component s x‖ ≤
      sharpDuhamelSecondFDerivMajorant nu t path s := by
  rw [sharpDuhamelFirstFDerivIntegrand, dif_pos hs]
  have hbase := norm_reconstructedHeatH2FirstFDerivCLM_le
    nu (positiveElapsed t s hs) (mul_pos hnu (sub_pos.mpr hs))
      (sharpNonlinearSource (path s)) component x
  have hmass := heatSecondDerivativeCoefficientMass_from_weightedH2_le
    ((nu : ℝ) * ((positiveElapsed t s hs : ℝ≥0) : ℝ))
      (by simpa only [coe_positiveElapsed] using mul_pos hnu (sub_pos.mpr hs))
      (by simpa only [coe_positiveElapsed] using hlocal)
      (sharpNonlinearSource (path s) component)
  have hsource := norm_sharpNonlinearSource_component_le (path s) component
  calc
    _ ≤ 3 * heatSecondDerivativeCoefficientMass 2
        ((nu : ℝ) * ((positiveElapsed t s hs : ℝ≥0) : ℝ))
          (sharpNonlinearSource (path s) component) := hbase
    _ ≤ 9 * heatSecondDerivativeCoefficientMass 2
        ((nu : ℝ) * ((positiveElapsed t s hs : ℝ≥0) : ℝ))
          (sharpNonlinearSource (path s) component) := by
      apply mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 9)
      unfold heatSecondDerivativeCoefficientMass
      exact tsum_nonneg fun k ↦ mul_nonneg
        (mul_nonneg (torusStokesEigenvalue_nonneg k) (Real.exp_pos _).le) (norm_nonneg _)
    _ ≤ 9 * (sharpHeatSecondDerivativeH2Constant *
        (2 * ((nu : ℝ) * (t - s))) ^ (-3 / 4 : ℝ) *
          ‖sharpNonlinearSource (path s) component‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [coe_positiveElapsed] using hmass
    _ ≤ 9 * (sharpHeatSecondDerivativeH2Constant *
        (2 * ((nu : ℝ) * (t - s))) ^ (-3 / 4 : ℝ) *
          ((23328 * periodicH3EmbeddingConstant) * ‖path s‖ ^ 2)) := by
      gcongr
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _)
    _ = sharpDuhamelSecondFDerivMajorant nu t path s := by
      unfold sharpDuhamelSecondFDerivMajorant sharpDuhamelSecondDerivativeMajorant
        sharpDuhamelSecondDerivativeConstant
      have htime : 0 ≤ (nu : ℝ) * (t - s) :=
        mul_nonneg hnu.le (sub_pos.mpr hs).le
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) htime]
      ring

/-! ## Strong measurability and operator-valued time integrability -/

def sharpHeatFirstFDerivAtJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (component : Fin 3) (x : Space)
    (pair : PositiveElapsedTime × PeriodicVectorWeightedSobolev 2) : Space →L[ℝ] ℝ :=
  reconstructedFiniteOrderRealFDerivStateCLM 2 0 (by omega)
    (fun i ↦ Fin.elim0 i) component x (vectorHeatH2ToH5Joint nu hnu pair)

theorem continuous_sharpHeatFirstFDerivAtJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (component : Fin 3) (x : Space) :
    Continuous (sharpHeatFirstFDerivAtJoint nu hnu component x) :=
  (reconstructedFiniteOrderRealFDerivStateCLM 2 0 (by omega)
    (fun i ↦ Fin.elim0 i) component x).continuous.comp
      (continuous_vectorHeatH2ToH5Joint nu hnu)

private theorem continuousOn_sharpDuhamelFirstFDerivIntegrand_Ioo
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (path : ℝ → PeriodicVectorWeightedSobolev 3) (hpath : Continuous path)
    (component : Fin 3) (x : Space) :
    ContinuousOn (fun s ↦ sharpDuhamelFirstFDerivIntegrand
      nu hnu t path component s x) (Ioo (0 : ℝ) t) := by
  rw [continuousOn_iff_continuous_restrict]
  have helapsed : Continuous
      (fun s : Ioo (0 : ℝ) t ↦
        positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t)) :=
    (continuous_positiveElapsedBefore t).comp (continuous_subtype_val.subtype_mk _)
  have hsource : Continuous
      (fun s : Ioo (0 : ℝ) t ↦ sharpNonlinearSource (path s.1)) := by
    change Continuous (fun s : Ioo (0 : ℝ) t ↦ weightedLerayQuadratic (path s.1))
    exact continuous_weightedLerayQuadratic.comp (hpath.comp continuous_subtype_val)
  have hmodel : Continuous
      (fun s : Ioo (0 : ℝ) t ↦ sharpHeatFirstFDerivAtJoint nu hnu component x
        ⟨positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t),
          sharpNonlinearSource (path s.1)⟩) :=
    (continuous_sharpHeatFirstFDerivAtJoint nu hnu component x).comp
      (helapsed.prodMk hsource)
  apply hmodel.congr
  intro s
  have hdt : 0 < ((positiveElapsed t s.1 s.2.2 : ℝ≥0) : ℝ) := by
    simpa only [coe_positiveElapsed] using sub_pos.mpr s.2.2
  have helapsedEq : positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t) =
      (⟨positiveElapsed t s.1 s.2.2, hdt⟩ : PositiveElapsedTime) := by
    apply Subtype.ext
    change Real.toNNReal (t - s.1) = positiveElapsed t s.1 s.2.2
    apply NNReal.eq
    rw [Real.coe_toNNReal (t - s.1) (sub_nonneg.mpr s.2.2.le), coe_positiveElapsed]
  rw [helapsedEq]
  change _ = sharpDuhamelFirstFDerivIntegrand nu hnu t path component s.1 x
  unfold sharpHeatFirstFDerivAtJoint
  rw [sharpDuhamelFirstFDerivIntegrand, dif_pos s.2.2,
    vectorHeatH2ToH5Joint_apply nu (positiveElapsed t s.1 s.2.2) hnu hdt]
  rfl

theorem aestronglyMeasurable_sharpDuhamelFirstFDerivIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (path : ℝ → PeriodicVectorWeightedSobolev 3) (hpath : Continuous path)
    (component : Fin 3) (x : Space) :
    AEStronglyMeasurable (fun s ↦ sharpDuhamelFirstFDerivIntegrand
      nu hnu t path component s x) (volume.restrict (Ioc (0 : ℝ) t)) := by
  letI : SecondCountableTopologyEither ℝ (Space →L[ℝ] ℝ) := ⟨Or.inl (by infer_instance)⟩
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact (continuousOn_sharpDuhamelFirstFDerivIntegrand_Ioo
    nu hnu path hpath component x).aestronglyMeasurable measurableSet_Ioo

/-- Project the full Hessian onto the first addressed input while retaining the second input as
the Fréchet-derivative operator required by the scalar second differentiation. -/
def sharpDuhamelSecondDirectionalFDerivIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first : Fin 3) (s : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single first 1)).comp
    (sharpDuhamelSecondFDerivIntegrand nu hnu t path component s x)

theorem hasFDerivAt_sharpDuhamelFirstDirectionalIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first : Fin 3) (s : ℝ) (x : Space) :
    HasFDerivAt
      (fun y ↦ sharpDuhamelFirstFDerivIntegrand nu hnu t path component s y
        (EuclideanSpace.single first 1))
      (sharpDuhamelSecondDirectionalFDerivIntegrand
        nu hnu t path component first s x) x := by
  have h := (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single first 1)).hasFDerivAt.comp x
      (hasFDerivAt_sharpDuhamelFirstFDerivIntegrand
        nu hnu t path component s x)
  simpa [sharpDuhamelSecondDirectionalFDerivIntegrand, Function.comp_def] using h

def sharpHeatSecondDirectionalFDerivAtJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (component first : Fin 3) (x : Space)
    (pair : PositiveElapsedTime × PeriodicVectorWeightedSobolev 2) : Space →L[ℝ] ℝ :=
  reconstructedFiniteOrderRealFDerivStateCLM 2 1 (by omega) (![first]) component x
    (vectorHeatH2ToH5Joint nu hnu pair)

theorem continuous_sharpHeatSecondDirectionalFDerivAtJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (component first : Fin 3) (x : Space) :
    Continuous (sharpHeatSecondDirectionalFDerivAtJoint
      nu hnu component first x) :=
  (reconstructedFiniteOrderRealFDerivStateCLM 2 1 (by omega)
    (![first]) component x).continuous.comp (continuous_vectorHeatH2ToH5Joint nu hnu)

private theorem sharpDuhamelSecondDirectionalFDerivIntegrand_of_lt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first : Fin 3) {s : ℝ} (hs : s < t) (x : Space) :
    sharpDuhamelSecondDirectionalFDerivIntegrand
        nu hnu t path component first s x =
      reconstructedFiniteOrderRealFDerivCLM 2 1 (by omega) (![first])
        (vectorHeatH2ToH5 nu (positiveElapsed t s hs)
          (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s))) component x := by
  apply ContinuousLinearMap.ext
  intro outer
  simp [sharpDuhamelSecondDirectionalFDerivIntegrand,
    sharpDuhamelSecondFDerivIntegrand, hs,
    reconstructedHeatH2SecondFDerivCLM,
    reconstructedFiniteOrderRealSecondFDerivCLM_apply,
    reconstructedFiniteOrderRealFDerivCLM_apply]
  apply Finset.sum_congr rfl
  intro second _
  congr 2

private theorem continuousOn_sharpDuhamelSecondDirectionalFDerivIntegrand_Ioo
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (path : ℝ → PeriodicVectorWeightedSobolev 3) (hpath : Continuous path)
    (component first : Fin 3) (x : Space) :
    ContinuousOn (fun s ↦ sharpDuhamelSecondDirectionalFDerivIntegrand
      nu hnu t path component first s x) (Ioo (0 : ℝ) t) := by
  rw [continuousOn_iff_continuous_restrict]
  have helapsed : Continuous
      (fun s : Ioo (0 : ℝ) t ↦ positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t)) :=
    (continuous_positiveElapsedBefore t).comp (continuous_subtype_val.subtype_mk _)
  have hsource : Continuous
      (fun s : Ioo (0 : ℝ) t ↦ sharpNonlinearSource (path s.1)) := by
    change Continuous (fun s : Ioo (0 : ℝ) t ↦ weightedLerayQuadratic (path s.1))
    exact continuous_weightedLerayQuadratic.comp (hpath.comp continuous_subtype_val)
  have hmodel : Continuous
      (fun s : Ioo (0 : ℝ) t ↦ sharpHeatSecondDirectionalFDerivAtJoint
        nu hnu component first x
          ⟨positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t),
            sharpNonlinearSource (path s.1)⟩) :=
    (continuous_sharpHeatSecondDirectionalFDerivAtJoint
      nu hnu component first x).comp (helapsed.prodMk hsource)
  apply hmodel.congr
  intro s
  have hdt : 0 < ((positiveElapsed t s.1 s.2.2 : ℝ≥0) : ℝ) := by
    simpa only [coe_positiveElapsed] using sub_pos.mpr s.2.2
  have helapsedEq : positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t) =
      (⟨positiveElapsed t s.1 s.2.2, hdt⟩ : PositiveElapsedTime) := by
    apply Subtype.ext
    change Real.toNNReal (t - s.1) = positiveElapsed t s.1 s.2.2
    apply NNReal.eq
    rw [Real.coe_toNNReal (t - s.1) (sub_nonneg.mpr s.2.2.le), coe_positiveElapsed]
  rw [helapsedEq]
  unfold sharpHeatSecondDirectionalFDerivAtJoint
  rw [vectorHeatH2ToH5Joint_apply nu (positiveElapsed t s.1 s.2.2) hnu hdt]
  exact (sharpDuhamelSecondDirectionalFDerivIntegrand_of_lt
    nu hnu t path component first s.2.2 x).symm

theorem aestronglyMeasurable_sharpDuhamelSecondDirectionalFDerivIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (path : ℝ → PeriodicVectorWeightedSobolev 3) (hpath : Continuous path)
    (component first : Fin 3) (x : Space) :
    AEStronglyMeasurable (fun s ↦ sharpDuhamelSecondDirectionalFDerivIntegrand
      nu hnu t path component first s x) (volume.restrict (Ioc (0 : ℝ) t)) := by
  letI : SecondCountableTopologyEither ℝ (Space →L[ℝ] ℝ) := ⟨Or.inl (by infer_instance)⟩
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact (continuousOn_sharpDuhamelSecondDirectionalFDerivIntegrand_Ioo
    nu hnu path hpath component first x).aestronglyMeasurable measurableSet_Ioo

theorem norm_sharpDuhamelSecondDirectionalFDerivIntegrand_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t s : ℝ) (hs : s < t)
    (hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first : Fin 3) (x : Space) :
    ‖sharpDuhamelSecondDirectionalFDerivIntegrand
      nu hnu t path component first s x‖ ≤
        sharpDuhamelSecondFDerivMajorant nu t path s := by
  calc
    _ ≤ ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single first 1)‖ *
        ‖sharpDuhamelSecondFDerivIntegrand nu hnu t path component s x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖sharpDuhamelSecondFDerivIntegrand nu hnu t path component s x‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro L
      simpa using L.le_opNorm (EuclideanSpace.single first 1)
    _ ≤ _ := by
      simpa using norm_sharpDuhamelSecondFDerivIntegrand_le
        nu hnu t s hs hlocal path component x

theorem intervalIntegrable_sharpDuhamelSecondFDerivMajorant
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t) :
    IntervalIntegrable (sharpDuhamelSecondFDerivMajorant nu t
      (weightedPathExtension hT path)) volume 0 t := by
  have hbase := intervalIntegrable_sharpDuhamelSecondDerivativeMajorant
    nu hnu hT path ht htpos
  change IntervalIntegrable (fun s ↦ 9 * sharpDuhamelSecondDerivativeMajorant
    nu t (weightedPathExtension hT path) s) volume 0 t
  exact hbase.const_mul 9

theorem intervalIntegrable_sharpDuhamelFirstFDerivIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1) (component : Fin 3) (x : Space) :
    IntervalIntegrable (fun s ↦ sharpDuhamelFirstFDerivIntegrand nu hnu t
      (weightedPathExtension hT path) component s x) volume 0 t := by
  have hmajorant := intervalIntegrable_sharpDuhamelSecondFDerivMajorant
    nu hnu hT path ht htpos
  have hmeas : AEStronglyMeasurable (fun s ↦ sharpDuhamelFirstFDerivIntegrand
      nu hnu t (weightedPathExtension hT path) component s x)
      (volume.restrict (Ι (0 : ℝ) t)) := by
    rw [uIoc_of_le htpos.le]
    exact aestronglyMeasurable_sharpDuhamelFirstFDerivIntegrand
      nu hnu (weightedPathExtension hT path) (weightedPathExtension hT path).continuous
        component x
  apply hmajorant.mono_fun' hmeas
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le htpos.le] at hs
  by_cases hst : s < t
  · have hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1 := by
      have hsub : t - s ≤ t := by linarith [hs.1]
      have hmul : (nu : ℝ) * (t - s) ≤ (nu : ℝ) * t :=
        mul_le_mul_of_nonneg_left hsub hnu.le
      calc
        2 * ((nu : ℝ) * (t - s)) ≤ 2 * ((nu : ℝ) * t) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 2 * (nu : ℝ) * t := by ring
        _ ≤ 1 := hsmall
    exact norm_sharpDuhamelFirstFDerivIntegrand_le
      nu hnu t s hst hlocal (weightedPathExtension hT path) component x
  · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hst)
    subst s
    simp [sharpDuhamelFirstFDerivIntegrand,
      sharpDuhamelSecondFDerivMajorant, sharpDuhamelSecondDerivativeMajorant]

theorem intervalIntegrable_sharpDuhamelSecondDirectionalFDerivIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1)
    (component first : Fin 3) (x : Space) :
    IntervalIntegrable (fun s ↦ sharpDuhamelSecondDirectionalFDerivIntegrand
      nu hnu t (weightedPathExtension hT path) component first s x) volume 0 t := by
  have hmajorant := intervalIntegrable_sharpDuhamelSecondFDerivMajorant
    nu hnu hT path ht htpos
  have hmeas : AEStronglyMeasurable
      (fun s ↦ sharpDuhamelSecondDirectionalFDerivIntegrand
        nu hnu t (weightedPathExtension hT path) component first s x)
      (volume.restrict (Ι (0 : ℝ) t)) := by
    rw [uIoc_of_le htpos.le]
    exact aestronglyMeasurable_sharpDuhamelSecondDirectionalFDerivIntegrand
      nu hnu (weightedPathExtension hT path) (weightedPathExtension hT path).continuous
        component first x
  apply hmajorant.mono_fun' hmeas
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le htpos.le] at hs
  by_cases hst : s < t
  · have hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1 := by
      have hsub : t - s ≤ t := by linarith [hs.1]
      have hmul : (nu : ℝ) * (t - s) ≤ (nu : ℝ) * t :=
        mul_le_mul_of_nonneg_left hsub hnu.le
      calc
        2 * ((nu : ℝ) * (t - s)) ≤ 2 * ((nu : ℝ) * t) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 2 * (nu : ℝ) * t := by ring
        _ ≤ 1 := hsmall
    exact norm_sharpDuhamelSecondDirectionalFDerivIntegrand_le
      nu hnu t s hst hlocal (weightedPathExtension hT path) component first x
  · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hst)
    subst s
    simp [sharpDuhamelSecondDirectionalFDerivIntegrand,
      sharpDuhamelSecondFDerivIntegrand, sharpDuhamelSecondFDerivMajorant,
      sharpDuhamelSecondDerivativeMajorant]

/-- Scalar evaluation of the standing reconstructed `H3` velocity. -/
def reconstructedVelocityComponentEvaluationCLM (component : Fin 3) (x : Space) :
    PeriodicVectorWeightedSobolev 3 →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((ContinuousMap.evalCLM ℂ (euclideanToSpatialTorus x)).restrictScalars ℝ).comp
      ((reconstructedTorusComplexComponentCLM component).restrictScalars ℝ))

@[simp]
theorem reconstructedVelocityComponentEvaluationCLM_apply
    (component : Fin 3) (x : Space) (state : PeriodicVectorWeightedSobolev 3) :
    reconstructedVelocityComponentEvaluationCLM component x state =
      reconstructedVelocity state x component := by
  rfl

theorem intervalIntegrable_sharpDuhamelScalarIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (component : Fin 3) (x : Space) :
    IntervalIntegrable (fun s ↦ sharpDuhamelScalarIntegrand nu hnu t
      (weightedPathExtension hT path) component s x) volume 0 t := by
  let stateIntegrand := weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path)
  have hstate : IntervalIntegrable stateIntegrand volume 0 t :=
    intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT path ht
  let eval := reconstructedVelocityComponentEvaluationCLM component x
  have hmapped : IntervalIntegrable (fun s ↦ eval (stateIntegrand s)) volume 0 t :=
    ⟨eval.integrable_comp hstate.1, eval.integrable_comp hstate.2⟩
  apply (IntervalIntegrable.congr (f := fun s ↦ eval (stateIntegrand s)) (g := fun s ↦
    sharpDuhamelScalarIntegrand nu hnu t (weightedPathExtension hT path) component s x) ?_)
    hmapped
  intro s _
  exact reconstructedVelocity_weightedDuhamelIntegrand_eq_sharpScalar
    nu hnu t (weightedPathExtension hT path) component s x

/-! ## Two dominated differentiation passages -/

theorem hasFDerivAt_integral_sharpDuhamelScalarIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1) (component : Fin 3) (x : Space) :
    HasFDerivAt
      (fun y : Space ↦ ∫ s in (0 : ℝ)..t,
        sharpDuhamelScalarIntegrand nu hnu t
          (weightedPathExtension hT path) component s y)
      (∫ s in (0 : ℝ)..t, sharpDuhamelFirstFDerivIntegrand nu hnu t
        (weightedPathExtension hT path) component s x) x := by
  let majorant := sharpDuhamelSecondFDerivMajorant nu t
    (weightedPathExtension hT path)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume) (a := 0) (b := t)
    (F := fun y s ↦ sharpDuhamelScalarIntegrand nu hnu t
      (weightedPathExtension hT path) component s y)
    (F' := fun y s ↦ sharpDuhamelFirstFDerivIntegrand nu hnu t
      (weightedPathExtension hT path) component s y)
    (x₀ := x) (s := Set.univ) (bound := majorant) univ_mem
  · filter_upwards with y
    have hy := intervalIntegrable_sharpDuhamelScalarIntegrand
      nu hnu hT path ht component y
    simpa [uIoc_of_le htpos.le] using hy.aestronglyMeasurable
  · exact intervalIntegrable_sharpDuhamelScalarIntegrand
      nu hnu hT path ht component x
  · simpa [uIoc_of_le htpos.le] using
      (aestronglyMeasurable_sharpDuhamelFirstFDerivIntegrand
        nu hnu (weightedPathExtension hT path)
          (weightedPathExtension hT path).continuous component x)
  · filter_upwards with s
    intro hs y _
    rw [uIoc_of_le htpos.le] at hs
    by_cases hst : s < t
    · have hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1 := by
        have hsub : t - s ≤ t := by linarith [hs.1]
        have hmul : (nu : ℝ) * (t - s) ≤ (nu : ℝ) * t :=
          mul_le_mul_of_nonneg_left hsub hnu.le
        calc
          2 * ((nu : ℝ) * (t - s)) ≤ 2 * ((nu : ℝ) * t) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
          _ = 2 * (nu : ℝ) * t := by ring
          _ ≤ 1 := hsmall
      exact norm_sharpDuhamelFirstFDerivIntegrand_le
        nu hnu t s hst hlocal (weightedPathExtension hT path) component y
    · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hst)
      subst s
      simp [majorant, sharpDuhamelFirstFDerivIntegrand,
        sharpDuhamelSecondFDerivMajorant, sharpDuhamelSecondDerivativeMajorant]
  · exact intervalIntegrable_sharpDuhamelSecondFDerivMajorant
      nu hnu hT path ht htpos
  · filter_upwards with s
    intro _ y _
    exact hasFDerivAt_sharpDuhamelScalarIntegrand
      nu hnu t (weightedPathExtension hT path) component s y

theorem hasFDerivAt_integral_sharpDuhamelFirstDirectionalIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1)
    (component first : Fin 3) (x : Space) :
    HasFDerivAt
      (fun y : Space ↦ ∫ s in (0 : ℝ)..t,
        sharpDuhamelFirstFDerivIntegrand nu hnu t
          (weightedPathExtension hT path) component s y
            (EuclideanSpace.single first 1))
      (∫ s in (0 : ℝ)..t, sharpDuhamelSecondDirectionalFDerivIntegrand
        nu hnu t (weightedPathExtension hT path) component first s x) x := by
  let majorant := sharpDuhamelSecondFDerivMajorant nu t
    (weightedPathExtension hT path)
  let evalFirst : (Space →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single first (1 : ℝ))
  have hopInt (y : Space) : IntervalIntegrable
      (fun s ↦ sharpDuhamelFirstFDerivIntegrand nu hnu t
        (weightedPathExtension hT path) component s y) volume 0 t :=
    intervalIntegrable_sharpDuhamelFirstFDerivIntegrand
      nu hnu hT path ht htpos hsmall component y
  have hscalarInt (y : Space) : IntervalIntegrable
      (fun s ↦ sharpDuhamelFirstFDerivIntegrand nu hnu t
        (weightedPathExtension hT path) component s y
          (EuclideanSpace.single first 1)) volume 0 t :=
    ⟨evalFirst.integrable_comp (hopInt y).1, evalFirst.integrable_comp (hopInt y).2⟩
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume) (a := 0) (b := t)
    (F := fun y s ↦ sharpDuhamelFirstFDerivIntegrand nu hnu t
      (weightedPathExtension hT path) component s y
        (EuclideanSpace.single first 1))
    (F' := fun y s ↦ sharpDuhamelSecondDirectionalFDerivIntegrand
      nu hnu t (weightedPathExtension hT path) component first s y)
    (x₀ := x) (s := Set.univ) (bound := majorant) univ_mem
  · filter_upwards with y
    simpa [uIoc_of_le htpos.le] using (hscalarInt y).aestronglyMeasurable
  · exact hscalarInt x
  · simpa [uIoc_of_le htpos.le] using
      (aestronglyMeasurable_sharpDuhamelSecondDirectionalFDerivIntegrand
        nu hnu (weightedPathExtension hT path)
          (weightedPathExtension hT path).continuous component first x)
  · filter_upwards with s
    intro hs y _
    rw [uIoc_of_le htpos.le] at hs
    by_cases hst : s < t
    · have hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1 := by
        have hsub : t - s ≤ t := by linarith [hs.1]
        have hmul : (nu : ℝ) * (t - s) ≤ (nu : ℝ) * t :=
          mul_le_mul_of_nonneg_left hsub hnu.le
        calc
          2 * ((nu : ℝ) * (t - s)) ≤ 2 * ((nu : ℝ) * t) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
          _ = 2 * (nu : ℝ) * t := by ring
          _ ≤ 1 := hsmall
      exact norm_sharpDuhamelSecondDirectionalFDerivIntegrand_le
        nu hnu t s hst hlocal (weightedPathExtension hT path) component first y
    · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hst)
      subst s
      simp [majorant, sharpDuhamelSecondDirectionalFDerivIntegrand,
        sharpDuhamelSecondFDerivIntegrand, sharpDuhamelSecondFDerivMajorant,
        sharpDuhamelSecondDerivativeMajorant]
  · exact intervalIntegrable_sharpDuhamelSecondFDerivMajorant
      nu hnu hT path ht htpos
  · filter_upwards with s
    intro _ y _
    exact hasFDerivAt_sharpDuhamelFirstDirectionalIntegrand
      nu hnu t (weightedPathExtension hT path) component first s y

/-! ## Exact comparison with the standing compact second-derivative chart -/

/-- Evaluating the projected Hessian integrand in the second addressed direction is exactly the
standing compact-chart `D2` integrand.  This comparison uses only the already reconstructed heat
slice and its Fréchet derivative witnesses. -/
theorem sharpDuhamelSecondDirectionalFDerivIntegrand_apply_eq
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) (s : ℝ)
    (x : Metric.closedBall (0 : Space) 3) :
    sharpDuhamelSecondDirectionalFDerivIntegrand nu hnu t path
        component first s x.1 (EuclideanSpace.single second 1) =
      sharpDuhamelSecondDerivativeIntegrand nu hnu t path
        component first second s x := by
  by_cases hs : s < t
  · rw [sharpDuhamelSecondDerivativeIntegrand_apply_eq_iterated_fderiv_of_lt
      nu hnu t path component first second hs x]
    have hfirst :
        (fun y : Space ↦ sharpDuhamelFirstFDerivIntegrand nu hnu t path
          component s y (EuclideanSpace.single first 1)) =
        (fun y : Space ↦ fderiv ℝ
          (fun z : Space ↦ sharpDuhamelScalarIntegrand nu hnu t path component s z) y
          (EuclideanSpace.single first 1)) := by
      funext y
      exact congrArg (fun L : Space →L[ℝ] ℝ ↦ L (EuclideanSpace.single first 1))
        (hasFDerivAt_sharpDuhamelScalarIntegrand
          nu hnu t path component s y).fderiv.symm
    rw [← (hasFDerivAt_sharpDuhamelFirstDirectionalIntegrand
      nu hnu t path component first s x.1).fderiv, hfirst]
    congr 2
    funext z
    simp only [sharpDuhamelScalarIntegrand, dif_pos hs]
  · rw [sharpDuhamelSecondDerivativeIntegrand_of_not_lt
      nu hnu t path component first second hs]
    simp [sharpDuhamelSecondDirectionalFDerivIntegrand,
      sharpDuhamelSecondFDerivIntegrand, hs]

/-- Unconditional discharge of the exact exchange interface isolated by the reconstruction
square: both addressed spatial derivatives pass through the scalar Duhamel interval integral,
and the result is the standing compact-chart `D2` population. -/
theorem sharpScalarDuhamelSecondDerivativeExchange
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1)
    (component first second : Fin 3) :
    SharpScalarDuhamelSecondDerivativeExchange nu hnu hT path t
      component first second := by
  intro x
  let scalarField : Space → ℝ := fun z ↦ ∫ s in (0 : ℝ)..t,
    sharpDuhamelScalarIntegrand nu hnu t
      (weightedPathExtension hT path) component s z
  have hfirstField :
      (fun y : Space ↦ fderiv ℝ scalarField y
        (EuclideanSpace.single first 1)) =
      (fun y : Space ↦ ∫ s in (0 : ℝ)..t,
        sharpDuhamelFirstFDerivIntegrand nu hnu t
          (weightedPathExtension hT path) component s y
            (EuclideanSpace.single first 1)) := by
    funext y
    rw [(hasFDerivAt_integral_sharpDuhamelScalarIntegrand
      nu hnu hT path ht htpos hsmall component y).fderiv]
    exact ContinuousLinearMap.intervalIntegral_apply
      (intervalIntegrable_sharpDuhamelFirstFDerivIntegrand
        nu hnu hT path ht htpos hsmall component y)
      (EuclideanSpace.single first 1)
  change fderiv ℝ (fun y : Space ↦ fderiv ℝ scalarField y
      (EuclideanSpace.single first 1)) x.1
      (EuclideanSpace.single second 1) = _
  rw [hfirstField,
    (hasFDerivAt_integral_sharpDuhamelFirstDirectionalIntegrand
      nu hnu hT path ht htpos hsmall component first x.1).fderiv]
  rw [ContinuousLinearMap.intervalIntegral_apply
    (intervalIntegrable_sharpDuhamelSecondDirectionalFDerivIntegrand
      nu hnu hT path ht htpos hsmall component first x.1)
    (EuclideanSpace.single second 1)]
  apply intervalIntegral.integral_congr
  intro s _
  exact sharpDuhamelSecondDirectionalFDerivIntegrand_apply_eq
    nu hnu t (weightedPathExtension hT path) component first second s x

/-- The actual weighted Duhamel return has the sharp compact physical second-derivative chart.
This closes the previously isolated identification interface without assuming a mild solution or
an open-solution equality. -/
theorem hasSharpDuhamelSecondDerivativeIdentification
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1)
    (component first second : Fin 3) :
    HasSharpDuhamelSecondDerivativeIdentification nu hnu hT path t
      component first second := by
  intro x
  have hfield :
      (fun z : Space ↦ reconstructedVelocity
        (weightedDuhamelReturn nu hnu hT path t) z component) =
      (fun z : Space ↦ ∫ s in (0 : ℝ)..t,
        sharpDuhamelScalarIntegrand nu hnu t
          (weightedPathExtension hT path) component s z) := by
    funext z
    exact reconstructedVelocity_weightedDuhamelReturn_eq_integral_sharpScalar
      nu hnu hT path component ht z
  rw [hfield]
  exact (sharpScalarDuhamelSecondDerivativeExchange
    nu hnu hT path ht htpos hsmall component first second x).trans
      (sharpDuhamelSecondDerivativeChart_apply_eq_integral
        nu hnu hT path ht htpos hsmall component first second x).symm

/-! ## Axiom audit -/

#print axioms hasFDerivAt_integral_sharpDuhamelScalarIntegrand
#print axioms hasFDerivAt_integral_sharpDuhamelFirstDirectionalIntegrand
#print axioms sharpScalarDuhamelSecondDerivativeExchange
#print axioms hasSharpDuhamelSecondDerivativeIdentification








end Soma.Holonics.Millennium.NavierStokesSharpDuhamelDerivativeInterchange
