import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The scalar heat Volterra passage carries its ordered time word

**[proved-derived]** A continuous source transported through the scalar heat kernel is not merely
an endpoint integral.  Factoring the kernel through the current time face and applying the
fundamental theorem of calculus returns the exact differential law

`V'(t) = source(t) - rate * V(t)`.

This owner is deliberately independent of Navier--Stokes.  The coefficientwise mild equation can
instantiate it with the genuine Stokes eigenvalue and the actual Leray-divergence source.
-/

noncomputable section

open MeasureTheory
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesScalarHeatVolterra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The exponentially transported ordered source history from the initial face to `t`. -/
def scalarHeatVolterra (rate : ℝ) (source : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, Real.exp (-rate * (t - s)) • source s

/-- The integrating-factor primitive whose current-time transport is the Volterra passage. -/
def scalarHeatPrimitive (rate : ℝ) (source : ℝ → E) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, Real.exp (rate * s) • source s

/-- Exact factorization through the current time face. -/
theorem scalarHeatVolterra_eq_currentTransport_primitive
    (rate : ℝ) (source : ℝ → E) (t : ℝ) :
    scalarHeatVolterra rate source t =
      Real.exp (-rate * t) • scalarHeatPrimitive rate source t := by
  rw [scalarHeatVolterra, scalarHeatPrimitive,
    ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _hs
  change Real.exp (-rate * (t - s)) • source s =
    Real.exp (-rate * t) • (Real.exp (rate * s) • source s)
  rw [← mul_smul, ← Real.exp_add]
  congr 2
  ring

/-- The integrating factor has its exact scalar derivative. -/
theorem hasDerivAt_negativeRateExp (rate t : ℝ) :
    HasDerivAt (fun τ : ℝ ↦ Real.exp (-rate * τ))
      (-rate * Real.exp (-rate * t)) t := by
  have h := ((hasDerivAt_id t).const_mul (-rate)).exp
  convert h using 1 <;> simp [Function.comp_def] <;> ring

/-- The weighted source primitive differentiates to its presented current face. -/
theorem hasDerivAt_scalarHeatPrimitive
    (rate : ℝ) {source : ℝ → E} (hsource : Continuous source) (t : ℝ) :
    HasDerivAt (scalarHeatPrimitive rate source)
      (Real.exp (rate * t) • source t) t := by
  let weightedSource : ℝ → E := fun s ↦ Real.exp (rate * s) • source s
  have hweighted : Continuous weightedSource :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).smul hsource
  change HasDerivAt
    (fun u ↦ ∫ s in (0 : ℝ)..u, Real.exp (rate * s) • source s)
    (Real.exp (rate * t) • source t) t
  simpa only [weightedSource] using
    (hweighted.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt

/-- **Exact ordered-time return.**  The scalar heat Volterra passage satisfies the inhomogeneous
heat equation at every time face. -/
theorem hasDerivAt_scalarHeatVolterra
    (rate : ℝ) {source : ℝ → E} (hsource : Continuous source) (t : ℝ) :
    HasDerivAt (scalarHeatVolterra rate source)
      (source t - rate • scalarHeatVolterra rate source t) t := by
  rw [scalarHeatVolterra_eq_currentTransport_primitive]
  have hproduct :=
    (hasDerivAt_negativeRateExp rate t).smul
      (hasDerivAt_scalarHeatPrimitive rate hsource t)
  have hproduct' :
      HasDerivAt
        (fun τ : ℝ ↦ Real.exp (-rate * τ) •
          scalarHeatPrimitive rate source τ)
        (Real.exp (-rate * t) •
            (Real.exp (rate * t) • source t) +
          (-rate * Real.exp (-rate * t)) •
            scalarHeatPrimitive rate source t) t := by
    change HasDerivAt
      (fun τ : ℝ ↦ Real.exp (-rate * τ) • scalarHeatPrimitive rate source τ)
      (Real.exp (-rate * t) • (Real.exp (rate * t) • source t) +
        (-rate * Real.exp (-rate * t)) • scalarHeatPrimitive rate source t) t at hproduct
    exact hproduct
  convert hproduct' using 1
  · funext τ
    exact scalarHeatVolterra_eq_currentTransport_primitive rate source τ
  have hexp : Real.exp (-rate * t) * Real.exp (rate * t) = 1 := by
    calc
      Real.exp (-rate * t) * Real.exp (rate * t) =
          Real.exp (-rate * t + rate * t) := (Real.exp_add _ _).symm
      _ = 1 := by rw [show -rate * t + rate * t = 0 by ring, Real.exp_zero]
  have hsourceFace :
      Real.exp (-rate * t) • (Real.exp (rate * t) • source t) = source t := by
    calc
      Real.exp (-rate * t) • (Real.exp (rate * t) • source t) =
          (Real.exp (-rate * t) * Real.exp (rate * t)) • source t := by
            rw [mul_smul]
      _ = source t := by rw [hexp, one_smul]
  change source t - rate •
      (Real.exp (-rate * t) • scalarHeatPrimitive rate source t) =
    Real.exp (-rate * t) • (Real.exp (rate * t) • source t) +
      (-rate * Real.exp (-rate * t)) • scalarHeatPrimitive rate source t
  rw [hsourceFace, sub_eq_add_neg]
  module

section Audit

#print axioms scalarHeatVolterra_eq_currentTransport_primitive
#print axioms hasDerivAt_negativeRateExp
#print axioms hasDerivAt_scalarHeatPrimitive
#print axioms hasDerivAt_scalarHeatVolterra

end Audit

end Soma.Holonics.Millennium.NavierStokesScalarHeatVolterra
