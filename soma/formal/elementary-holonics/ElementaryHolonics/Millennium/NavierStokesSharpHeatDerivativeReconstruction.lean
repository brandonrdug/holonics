import ElementaryHolonics.Millennium.NavierStokesSharpHeatDerivative
import ElementaryHolonics.Millennium.NavierStokesWeightedHeatScaleWord
import ElementaryHolonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction

/-!
# Reconstruction of the sharp heat second-derivative receiver

**[proved-derived]** Positive heat time lifts weighted `H3` (and weighted `H2` source) data to
native `H5` without changing the total heat time: two, respectively three, adjacent scale passages
use equal subdivisions.  The existing finite-order reconstruction owner then identifies every
addressed second derivative with its complete Fourier multiplier series.  Its compact-chart norm
is bounded by the sharp absolute Laplace-symbol coefficient mass.

This module identifies the genuine homogeneous heat slice.  It does not identify a general open
solution with that slice; the nonlinear Duhamel coefficient equation is the remaining seam.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesSharpHeatDerivativeReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHeatScaleWord
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

private theorem half_viscous
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ)) :
    0 < (nu : ℝ) * ((dt / 2 : ℝ≥0) : ℝ) := by
  push_cast
  nlinarith

private theorem third_viscous
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ)) :
    0 < (nu : ℝ) * ((dt / 3 : ℝ≥0) : ℝ) := by
  push_cast
  nlinarith

/-- One total heat time lifts vector weighted `H3` data to `H5`; the two scale crossings each use
half the time. -/
def vectorHeatH3ToH5
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3) :
    PeriodicVectorWeightedSobolev 5 :=
  periodicVectorWeightedHeatScaleWord 3 2 nu (dt / 2) (half_viscous nu dt h) state

/-- One total heat time lifts a vector weighted `H2` source to `H5`; the three scale crossings
each use one third of the time. -/
def vectorHeatH2ToH5
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2) :
    PeriodicVectorWeightedSobolev 5 :=
  periodicVectorWeightedHeatScaleWord 2 3 nu (dt / 3) (third_viscous nu dt h) source

private theorem heatMultiplier_half_sq
    (nu dt : ℝ≥0) (k : SpatialFrequency) :
    heatStokesMultiplier (nu : ℝ) ((dt / 2 : ℝ≥0) : ℝ) k ^ 2 =
      heatStokesMultiplier (nu : ℝ) (dt : ℝ) k := by
  rw [pow_two, ← heatStokesMultiplier_add]
  congr 2
  push_cast
  ring

private theorem heatMultiplier_third_cube
    (nu dt : ℝ≥0) (k : SpatialFrequency) :
    heatStokesMultiplier (nu : ℝ) ((dt / 3 : ℝ≥0) : ℝ) k ^ 3 =
      heatStokesMultiplier (nu : ℝ) (dt : ℝ) k := by
  rw [pow_succ, pow_two, ← heatStokesMultiplier_add, ← heatStokesMultiplier_add]
  congr 2
  push_cast
  ring

theorem weightedCoefficients_vectorHeatH3ToH5
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) :
    (weightedSobolevCoefficients 5 (vectorHeatH3ToH5 nu dt h state component)).1 k =
      (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) *
        (weightedSobolevCoefficients 3 (state component)).1 k := by
  have hw := weightedSobolevCoefficients_periodicVectorWeightedHeatScaleWord_apply
    3 2 nu (dt / 2) (half_viscous nu dt h) state component k
  calc
    (weightedSobolevCoefficients 5 (vectorHeatH3ToH5 nu dt h state component)).1 k =
        (heatStokesMultiplier (nu : ℝ) ((dt / 2 : ℝ≥0) : ℝ) k : ℂ) ^ 2 *
          (weightedSobolevCoefficients 3 (state component)).1 k := by
      simpa only [vectorHeatH3ToH5] using hw
    _ = (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) *
        (weightedSobolevCoefficients 3 (state component)).1 k := by
      rw [show ((heatStokesMultiplier (nu : ℝ) ((dt / 2 : ℝ≥0) : ℝ) k : ℂ) ^ 2) =
        (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) by
          exact_mod_cast heatMultiplier_half_sq nu dt k]

theorem weightedCoefficients_vectorHeatH2ToH5
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2) (component : Fin 3)
    (k : SpatialFrequency) :
    (weightedSobolevCoefficients 5 (vectorHeatH2ToH5 nu dt h source component)).1 k =
      (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) *
        (weightedSobolevCoefficients 2 (source component)).1 k := by
  have hw := weightedSobolevCoefficients_periodicVectorWeightedHeatScaleWord_apply
    2 3 nu (dt / 3) (third_viscous nu dt h) source component k
  calc
    (weightedSobolevCoefficients 5 (vectorHeatH2ToH5 nu dt h source component)).1 k =
        (heatStokesMultiplier (nu : ℝ) ((dt / 3 : ℝ≥0) : ℝ) k : ℂ) ^ 3 *
          (weightedSobolevCoefficients 2 (source component)).1 k := by
      simpa only [vectorHeatH2ToH5] using hw
    _ = (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) *
        (weightedSobolevCoefficients 2 (source component)).1 k := by
      rw [show ((heatStokesMultiplier (nu : ℝ) ((dt / 3 : ℝ≥0) : ℝ) k : ℂ) ^ 3) =
        (heatStokesMultiplier (nu : ℝ) (dt : ℝ) k : ℂ) by
          exact_mod_cast heatMultiplier_third_cube nu dt k]

/-- The addressed ordered pair used for a coordinate second derivative. -/
def secondCoordinateWord (first second : Fin 3) : Fin 2 → Fin 3 :=
  ![second, first]

/-- Actual reconstructed coordinate second derivative of the homogeneous heat slice from `H3`. -/
def reconstructedHeatH3SecondDerivative
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) : Space → ℝ :=
  reconstructedFiniteOrderRealComponent 2 2 (by omega)
    (secondCoordinateWord first second) (vectorHeatH3ToH5 nu dt h state) component

/-- The actual homogeneous heat component whose second derivative is reconstructed below. -/
def reconstructedHeatH3Component
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3) (component : Fin 3) : Space → ℝ :=
  reconstructedFiniteOrderRealComponent 2 0 (by omega) (fun i ↦ Fin.elim0 i)
    (vectorHeatH3ToH5 nu dt h state) component

/-- The reconstructed Fourier receiver is literally the iterated spatial derivative of the
homogeneous heat slice, not merely a coefficient-labelled surrogate. -/
theorem iterated_fderiv_reconstructedHeatH3Component
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space ↦
      fderiv ℝ (reconstructedHeatH3Component nu dt h state component) y
        (EuclideanSpace.single first 1)) x
        (EuclideanSpace.single second 1) =
      reconstructedHeatH3SecondDerivative nu dt h state component first second x := by
  rw [show (fun y : Space ↦
      fderiv ℝ (reconstructedHeatH3Component nu dt h state component) y
        (EuclideanSpace.single first 1)) =
      reconstructedFiniteOrderRealComponent 2 1 (by omega) (![first])
        (vectorHeatH3ToH5 nu dt h state) component by
    funext y
    exact fderiv_reconstructedFiniteOrderRealComponent_apply_single
      2 0 (by omega) (fun i ↦ Fin.elim0 i)
        (vectorHeatH3ToH5 nu dt h state) component first y]
  rw [fderiv_reconstructedFiniteOrderRealComponent_apply_single]
  rfl

/-- Actual reconstructed coordinate second derivative of the homogeneous heat slice from `H2`. -/
def reconstructedHeatH2SecondDerivative
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component first second : Fin 3) : Space → ℝ :=
  reconstructedFiniteOrderRealComponent 2 2 (by omega)
    (secondCoordinateWord first second) (vectorHeatH2ToH5 nu dt h source) component

private theorem norm_secondCoordinateMultiplier_le_stokes
    (first second : Fin 3) (k : SpatialFrequency) :
    ‖orderedDerivativeMultiplier 2 (secondCoordinateWord first second) k‖ ≤
      torusStokesEigenvalue k := by
  have hfirst : (k first : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    simp only [Fin.sum_univ_three]
    fin_cases first <;> simp at * <;> nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ),
      sq_nonneg (k 2 : ℝ)]
  have hsecond : (k second : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    simp only [Fin.sum_univ_three]
    fin_cases second <;> simp at * <;> nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ),
      sq_nonneg (k 2 : ℝ)]
  have habs : |(k first : ℝ)| * |(k second : ℝ)| ≤ frequencySquared k := by
    nlinarith [sq_abs (k first : ℝ), sq_abs (k second : ℝ),
      sq_nonneg (|(k first : ℝ)| - |(k second : ℝ)|)]
  simp only [orderedDerivativeMultiplier, secondCoordinateWord, Fin.prod_univ_two,
    coordinateFourierMultiplier, Matrix.cons_val_zero, Matrix.cons_val_one,
    norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Int.cast_abs]
  unfold torusStokesEigenvalue
  norm_num
  nlinarith [sq_nonneg (2 * Real.pi), Real.pi_pos]

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
  calc
    ‖∑' k : SpatialFrequency, nativeUnweightedComponent state component k *
        UnitAddTorus.mFourier k (euclideanToSpatialTorus x)‖ ≤
        ∑' k : SpatialFrequency,
          ‖nativeUnweightedComponent state component k *
            UnitAddTorus.mFourier k (euclideanToSpatialTorus x)‖ :=
      norm_tsum_le_tsum_norm hterms
    _ = ∑' k : SpatialFrequency, ‖nativeUnweightedComponent state component k‖ := by
      apply tsum_congr
      intro k
      rw [norm_mul]
      simp [UnitAddTorus.mFourier, norm_prod, Circle.norm_coe]

private theorem receiverTerm_eq_kernelNormMul
    (a : ℝ) (ha : 0 < a) (state : PeriodicWeightedSobolev 3)
    (k : SpatialFrequency) :
    torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) *
        ‖weightedSobolevRawCoefficients 3 state k‖ =
      ‖heatSecondDerivativeH3Kernel a ha k‖ * ‖weightedStateAbsolute 3 state k‖ := by
  have hsqrt : 0 < Real.sqrt (periodicSobolevWeight 3 k) :=
    Real.sqrt_pos.2 (periodicSobolevWeight_pos 3 k)
  have hk : 0 ≤ torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) /
      Real.sqrt (periodicSobolevWeight 3 k) :=
    div_nonneg (mul_nonneg (torusStokesEigenvalue_nonneg k) (Real.exp_pos _).le) hsqrt.le
  change torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) *
      ‖((((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) * state k)‖ =
    ‖torusStokesEigenvalue k * Real.exp (-a * torusStokesEigenvalue k) /
      Real.sqrt (periodicSobolevWeight 3 k)‖ * ‖‖state k‖‖
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk,
    Real.norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt]
  field_simp

theorem norm_reconstructedHeatH3SecondDerivative_le_coefficientMass
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) (x : Space) :
    ‖reconstructedHeatH3SecondDerivative nu dt h state component first second x‖ ≤
      heatSecondDerivativeCoefficientMass 3 ((nu : ℝ) * (dt : ℝ))
        (state component) := by
  let lifted := vectorHeatH3ToH5 nu dt h state
  let derivativeState := finiteOrderVectorDerivativeToThree 2 2 (by omega)
    (secondCoordinateWord first second) lifted
  have hcomplex := norm_reconstructedComponent_le_coefficientMass derivativeState component x
  have hreal : ‖reconstructedHeatH3SecondDerivative nu dt h state component first second x‖ ≤
      ‖reconstructedTorusComplexComponent derivativeState component
        (euclideanToSpatialTorus x)‖ := by
    exact Complex.abs_re_le_norm _
  refine hreal.trans (hcomplex.trans ?_)
  unfold heatSecondDerivativeCoefficientMass
  have hholder : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hreceiver : Summable fun k : SpatialFrequency ↦
      torusStokesEigenvalue k * Real.exp (-((nu : ℝ) * (dt : ℝ)) *
        torusStokesEigenvalue k) *
        ‖weightedSobolevRawCoefficients 3 (state component) k‖ := by
    apply (lp.summable_mul hholder
      (heatSecondDerivativeH3Kernel ((nu : ℝ) * (dt : ℝ)) h)
      (weightedStateAbsolute 3 (state component))).congr
    intro k
    exact (receiverTerm_eq_kernelNormMul ((nu : ℝ) * (dt : ℝ)) h
      (state component) k).symm
  apply Summable.tsum_le_tsum
  · intro k
    dsimp [nativeUnweightedComponent, derivativeState]
    rw [weightedSobolevCoefficients_finiteOrderDerivativeToThree_apply,
      weightedCoefficients_vectorHeatH3ToH5]
    rw [norm_mul, norm_mul, Complex.norm_real]
    simp only [heatStokesMultiplier]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change ‖orderedDerivativeMultiplier 2 (secondCoordinateWord first second) k‖ *
        (Real.exp (-((nu : ℝ) * (dt : ℝ) * torusStokesEigenvalue k)) *
          ‖weightedSobolevRawCoefficients 3 (state component) k‖) ≤ _
    have hsymbol := norm_secondCoordinateMultiplier_le_stokes first second k
    change _ ≤ torusStokesEigenvalue k *
      Real.exp (-((nu : ℝ) * (dt : ℝ)) * torusStokesEigenvalue k) *
        ‖weightedSobolevRawCoefficients 3 (state component) k‖
    calc
      _ ≤ torusStokesEigenvalue k *
          (Real.exp (-((nu : ℝ) * (dt : ℝ) * torusStokesEigenvalue k)) *
            ‖weightedSobolevRawCoefficients 3 (state component) k‖) :=
        mul_le_mul_of_nonneg_right hsymbol
          (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ = _ := by ring
  · exact summable_norm_nativeUnweightedComponent derivativeState component
  · exact hreceiver

/-- Compact radius-three receiver of one actual reconstructed coordinate second derivative. -/
def reconstructedHeatH3SecondDerivativeChart
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) :
    C(Metric.closedBall (0 : Space) 3, ℝ) :=
  ⟨fun x ↦ reconstructedHeatH3SecondDerivative nu dt h state component first second x.1,
    ((contDiff_one_reconstructedFiniteOrderRealComponent 2 2 (by omega)
      (secondCoordinateWord first second) (vectorHeatH3ToH5 nu dt h state)
      component).continuous.comp continuous_subtype_val)⟩

theorem norm_reconstructedHeatH3SecondDerivativeChart_le
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (state : PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) :
    ‖reconstructedHeatH3SecondDerivativeChart nu dt h state component first second‖ ≤
      heatSecondDerivativeCoefficientMass 3 ((nu : ℝ) * (dt : ℝ))
        (state component) := by
  apply (ContinuousMap.norm_le _ (by
    unfold heatSecondDerivativeCoefficientMass
    exact tsum_nonneg fun k ↦ mul_nonneg
      (mul_nonneg (torusStokesEigenvalue_nonneg k) (Real.exp_pos _).le)
      (norm_nonneg _))).2
  intro x
  exact norm_reconstructedHeatH3SecondDerivative_le_coefficientMass
    nu dt h state component first second x.1

theorem norm_reconstructedHeatH3SecondDerivativeChart_sharp
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (hlocal : 2 * ((nu : ℝ) * (dt : ℝ)) ≤ 1)
    (state : PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) :
    ‖reconstructedHeatH3SecondDerivativeChart nu dt h state component first second‖ ≤
      sharpHeatSecondDerivativeH3Constant *
        (2 * ((nu : ℝ) * (dt : ℝ))) ^ (-1 / 4 : ℝ) * ‖state component‖ :=
  (norm_reconstructedHeatH3SecondDerivativeChart_le
    nu dt h state component first second).trans
      (heatSecondDerivativeCoefficientMass_from_weightedH3_le
        ((nu : ℝ) * (dt : ℝ)) h hlocal (state component))

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

theorem norm_reconstructedHeatH2SecondDerivative_le_coefficientMass
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component first second : Fin 3) (x : Space) :
    ‖reconstructedHeatH2SecondDerivative nu dt h source component first second x‖ ≤
      heatSecondDerivativeCoefficientMass 2 ((nu : ℝ) * (dt : ℝ))
        (source component) := by
  let lifted := vectorHeatH2ToH5 nu dt h source
  let derivativeState := finiteOrderVectorDerivativeToThree 2 2 (by omega)
    (secondCoordinateWord first second) lifted
  have hcomplex := norm_reconstructedComponent_le_coefficientMass derivativeState component x
  have hreal : ‖reconstructedHeatH2SecondDerivative nu dt h source component first second x‖ ≤
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
    change ‖orderedDerivativeMultiplier 2 (secondCoordinateWord first second) k‖ *
        (Real.exp (-((nu : ℝ) * (dt : ℝ) * torusStokesEigenvalue k)) *
          ‖weightedSobolevRawCoefficients 2 (source component) k‖) ≤
      torusStokesEigenvalue k *
        Real.exp (-((nu : ℝ) * (dt : ℝ)) * torusStokesEigenvalue k) *
          ‖weightedSobolevRawCoefficients 2 (source component) k‖
    calc
      _ ≤ torusStokesEigenvalue k *
          (Real.exp (-((nu : ℝ) * (dt : ℝ) * torusStokesEigenvalue k)) *
            ‖weightedSobolevRawCoefficients 2 (source component) k‖) :=
        mul_le_mul_of_nonneg_right
          (norm_secondCoordinateMultiplier_le_stokes first second k)
          (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
      _ = _ := by ring
  · exact summable_norm_nativeUnweightedComponent derivativeState component
  · exact hreceiver

def reconstructedHeatH2SecondDerivativeChart
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component first second : Fin 3) :
    C(Metric.closedBall (0 : Space) 3, ℝ) :=
  ⟨fun x ↦ reconstructedHeatH2SecondDerivative nu dt h source component first second x.1,
    ((contDiff_one_reconstructedFiniteOrderRealComponent 2 2 (by omega)
      (secondCoordinateWord first second) (vectorHeatH2ToH5 nu dt h source)
      component).continuous.comp continuous_subtype_val)⟩

theorem norm_reconstructedHeatH2SecondDerivativeChart_sharp
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (hlocal : 2 * ((nu : ℝ) * (dt : ℝ)) ≤ 1)
    (source : PeriodicVectorWeightedSobolev 2)
    (component first second : Fin 3) :
    ‖reconstructedHeatH2SecondDerivativeChart nu dt h source component first second‖ ≤
      sharpHeatSecondDerivativeH2Constant *
        (2 * ((nu : ℝ) * (dt : ℝ))) ^ (-3 / 4 : ℝ) * ‖source component‖ := by
  calc
    _ ≤ heatSecondDerivativeCoefficientMass 2 ((nu : ℝ) * (dt : ℝ))
        (source component) := by
      apply (ContinuousMap.norm_le _ (by
        unfold heatSecondDerivativeCoefficientMass
        exact tsum_nonneg fun k ↦ mul_nonneg
          (mul_nonneg (torusStokesEigenvalue_nonneg k) (Real.exp_pos _).le)
          (norm_nonneg _))).2
      intro x
      exact norm_reconstructedHeatH2SecondDerivative_le_coefficientMass
        nu dt h source component first second x.1
    _ ≤ _ := heatSecondDerivativeCoefficientMass_from_weightedH2_le
      ((nu : ℝ) * (dt : ℝ)) h hlocal (source component)

/-! ## Axiom audit -/

#print axioms weightedCoefficients_vectorHeatH3ToH5
#print axioms iterated_fderiv_reconstructedHeatH3Component
#print axioms norm_reconstructedHeatH3SecondDerivativeChart_sharp
#print axioms norm_reconstructedHeatH2SecondDerivativeChart_sharp

end Soma.Holonics.Millennium.NavierStokesSharpHeatDerivativeReconstruction
