import ElementaryHolonics.Millennium.NavierStokesSharpDuhamelSecondDerivative
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Identifying the sharp Duhamel derivative chart with the standing reconstruction

This module begins at the exact coefficient comparison already proved for the sharp compact
`D2` chart.  It first closes the zeroth-order reconstruction square: the physical reconstruction
of the repository's actual weighted `H3` Bochner Duhamel return is exactly the time integral of
the same positive-time `H2 -> H5` heat slices used by the sharp chart.  The remaining operation is
then solely differentiation twice under this displayed scalar interval integral.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesSharpDuhamelDerivativeIdentification

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH2ToH3HeatSmoothing
open Soma.Holonics.Millennium.NavierStokesSharpDuhamelSecondDerivative
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivativeReconstruction
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Endpoint-totalized scalar physical heat slice underlying the sharp Duhamel chart. -/
def sharpDuhamelScalarIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (s : ℝ) (x : Space) : ℝ :=
  if hs : s < t then
    reconstructedHeatH2Component nu (positiveElapsed t s hs)
      (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s)) component x
  else
    0

theorem reconstructedVelocity_weightedDuhamelIntegrand_eq_sharpScalar_of_lt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) {s : ℝ} (hs : s < t) (x : Space) :
    reconstructedVelocity (weightedDuhamelIntegrand nu hnu t path s) x component =
      reconstructedHeatH2Component nu (positiveElapsed t s hs)
        (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s)) component x := by
  rw [weightedDuhamelIntegrand_of_lt nu hnu t path hs]
  change
    (reconstructedTorusComplexComponent
      (periodicVectorWeightedHeatTwoToThree nu (positiveElapsed t s hs)
        (mul_pos hnu (sub_pos.mpr hs)) (weightedLerayQuadratic (path s))) component
      (euclideanToSpatialTorus x)).re =
    (reconstructedTorusComplexComponent
      (finiteOrderVectorDerivativeToThree 2 0 (by omega) (fun i ↦ Fin.elim0 i)
        (vectorHeatH2ToH5 nu (positiveElapsed t s hs)
          (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s)))) component
      (euclideanToSpatialTorus x)).re
  congr 1
  rw [reconstructedTorusComplexComponent_apply,
    reconstructedTorusComplexComponent_apply]
  apply tsum_congr
  intro k
  congr 1
  change
    (weightedSobolevCoefficients 3
      (periodicWeightedHeatTwoToThree nu (positiveElapsed t s hs)
        (mul_pos hnu (sub_pos.mpr hs)) (weightedLerayQuadratic (path s) component))).1 k =
    (weightedSobolevCoefficients 3
      (finiteOrderVectorDerivativeToThree 2 0 (by omega) (fun i ↦ Fin.elim0 i)
        (vectorHeatH2ToH5 nu (positiveElapsed t s hs)
          (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s))) component)).1 k
  rw [unweighted_periodicWeightedHeatTwoToThree_apply,
    weightedSobolevCoefficients_finiteOrderVectorDerivativeToThree_apply,
    weightedCoefficients_vectorHeatH2ToH5]
  simp [orderedDerivativeMultiplier, weightedLerayQuadratic_apply,
    sharpNonlinearSource]

theorem reconstructedVelocity_weightedDuhamelIntegrand_eq_sharpScalar
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component : Fin 3) (s : ℝ) (x : Space) :
    reconstructedVelocity (weightedDuhamelIntegrand nu hnu t path s) x component =
      sharpDuhamelScalarIntegrand nu hnu t path component s x := by
  by_cases hs : s < t
  · rw [sharpDuhamelScalarIntegrand, dif_pos hs]
    exact reconstructedVelocity_weightedDuhamelIntegrand_eq_sharpScalar_of_lt
      nu hnu t path component hs x
  · rw [weightedDuhamelIntegrand_of_not_lt nu hnu t path hs,
      sharpDuhamelScalarIntegrand, dif_neg hs]
    change (reconstructedTorusComplexComponent 0 component
      (euclideanToSpatialTorus x)).re = 0
    have hz := (reconstructedTorusComplexComponentCLM component).map_zero
    have happ := congrArg
      (fun field : C(SpatialTorus, ℂ) ↦ (field (euclideanToSpatialTorus x)).re) hz
    simpa using happ

/-- Unconditional zeroth-order reconstruction square: the actual weighted Duhamel return and the
positive-time sharp heat population agree as physical scalar fields before any differentiation
under the time integral is invoked. -/
theorem reconstructedVelocity_weightedDuhamelReturn_eq_integral_sharpScalar
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (component : Fin 3)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Space) :
    reconstructedVelocity (weightedDuhamelReturn nu hnu hT path t) x component =
      ∫ s in (0 : ℝ)..t,
        sharpDuhamelScalarIntegrand nu hnu t
          (weightedPathExtension hT path) component s x := by
  let integrand := weightedDuhamelIntegrand nu hnu t (weightedPathExtension hT path)
  have hintegrable : IntervalIntegrable integrand volume 0 t :=
    intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT path ht
  have hreconstruct :=
    (reconstructedTorusComplexComponentCLM component).intervalIntegral_comp_comm hintegrable
  let reconstructed : PeriodicVectorWeightedSobolev 3 →L[ℝ] C(SpatialTorus, ℂ) :=
    (reconstructedTorusComplexComponentCLM component).restrictScalars ℝ
  let evalRe : C(SpatialTorus, ℂ) →L[ℝ] ℝ :=
    Complex.reCLM.comp
      ((ContinuousMap.evalCLM ℂ (euclideanToSpatialTorus x)).restrictScalars ℝ)
  have hmapped : IntervalIntegrable (fun s ↦ reconstructed (integrand s)) volume 0 t :=
    ⟨reconstructed.integrable_comp hintegrable.1,
      reconstructed.integrable_comp hintegrable.2⟩
  have hevalcomm := evalRe.intervalIntegral_comp_comm hmapped
  calc
    reconstructedVelocity (weightedDuhamelReturn nu hnu hT path t) x component =
        evalRe (reconstructed (weightedDuhamelReturn nu hnu hT path t)) := by rfl
    _ = evalRe (∫ s in (0 : ℝ)..t, reconstructed (integrand s)) := by
      congr 1
      exact hreconstruct.symm
    _ = ∫ s in (0 : ℝ)..t, evalRe (reconstructed (integrand s)) :=
      hevalcomm.symm
    _ = ∫ s in (0 : ℝ)..t,
        sharpDuhamelScalarIntegrand nu hnu t
          (weightedPathExtension hT path) component s x := by
      apply intervalIntegral.integral_congr
      intro s _
      exact reconstructedVelocity_weightedDuhamelIntegrand_eq_sharpScalar
        nu hnu t (weightedPathExtension hT path) component s x

/-- Evaluation of the constructed sharp compact chart commutes with its honest chart-valued
Bochner integral.  Thus its value is exactly the integral of the genuine per-slice second
derivatives, with no coefficient or reconstruction seam left. -/
theorem sharpDuhamelSecondDerivativeChart_apply_eq_integral
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1)
    (component first second : Fin 3)
    (x : Metric.closedBall (0 : Space) 3) :
    sharpDuhamelSecondDerivativeChart nu hnu hT path t component first second x =
      ∫ s in (0 : ℝ)..t,
        sharpDuhamelSecondDerivativeIntegrand nu hnu t
          (weightedPathExtension hT path) component first second s x := by
  let integrand := sharpDuhamelSecondDerivativeIntegrand nu hnu t
    (weightedPathExtension hT path) component first second
  have hintegrable : IntervalIntegrable integrand volume 0 t :=
    intervalIntegrable_sharpDuhamelSecondDerivativeIntegrand
      nu hnu hT path ht htpos hsmall component first second
  have hcommute := (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm hintegrable
  exact hcommute.symm

/-- The smallest remaining lemma after both reconstruction squares have been closed.  It contains
only dominated spatial differentiation under a scalar interval integral: no Fourier coefficient,
Sobolev carrier, mild equation, fixed-point hypothesis, or open-solution identification remains
inside the equality.  The standing repository lacks the operator-valued sharp first-derivative
majorant needed by Mathlib's parametric-integral theorem to prove this proposition directly. -/
def SharpScalarDuhamelSecondDerivativeExchange
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (t : ℝ)
    (component first second : Fin 3) : Prop :=
  ∀ x : Metric.closedBall (0 : Space) 3,
    fderiv ℝ (fun y : Space ↦
      fderiv ℝ (fun z : Space ↦
        ∫ s in (0 : ℝ)..t,
          sharpDuhamelScalarIntegrand nu hnu t
            (weightedPathExtension hT path) component s z) y
        (EuclideanSpace.single first 1)) x.1
        (EuclideanSpace.single second 1) =
      ∫ s in (0 : ℝ)..t,
        sharpDuhamelSecondDerivativeIntegrand nu hnu t
          (weightedPathExtension hT path) component first second s x

#print axioms reconstructedVelocity_weightedDuhamelReturn_eq_integral_sharpScalar
#print axioms sharpDuhamelSecondDerivativeChart_apply_eq_integral

end Soma.Holonics.Millennium.NavierStokesSharpDuhamelDerivativeIdentification
