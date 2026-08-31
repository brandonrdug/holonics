import ElementaryHolonics.Millennium.NavierStokesFrozenSharpSourceBoundary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Clock-scale squeeze of the frozen sharp-source boundary

**[proved-derived; formal-checked]**  The frozen heat/curl boundary owner already identifies the
exact signed boundary action before coefficient mass is taken.  This file evaluates its named
positive-elapsed service law.  On an aperture of length `h`, the first-derivative heat clock has
budget proportional to `h^(3/4)`.  Consequently every fixed native weighted `H2` source is squeezed
to zero by the complete boundary receiver as `h → 0+`.

This is a local clock-scale statement.  Its remaining multiplier is the literal source norm, so it
does not supply the terminal-uniform, scale-critical payment required by Statement B.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundaryScale

open Soma.Holonics.Millennium.NavierStokesCriticalMildReceiver
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundary
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
open Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- The exact finite-aperture budget returned by the named first-derivative heat clock. -/
def frozenH2SourceBoundaryClockBudget (nu horizon : ℝ) : ℝ :=
  8 * sharpHeatFirstDerivativeH2Constant *
    (2 * nu) ^ (-1 / 4 : ℝ) * horizon ^ (3 / 4 : ℝ)

/-- Exact primitive of the clock exponent occurring after one spatial derivative is recovered
from an `H2` source. -/
private theorem intervalIntegral_rpow_neg_one_quarter
    {horizon : ℝ} (_hhorizon : 0 ≤ horizon) :
    (∫ elapsed in (0 : ℝ)..horizon, elapsed ^ (-1 / 4 : ℝ)) =
      (4 / 3 : ℝ) * horizon ^ (3 / 4 : ℝ) := by
  rw [integral_rpow (a := 0) (b := horizon)
    (r := (-1 / 4 : ℝ)) (Or.inl (by norm_num))]
  rw [show (-1 / 4 : ℝ) + 1 = 3 / 4 by ring,
    Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0), sub_zero]
  ring

/-- The named clock kernel has the exact `h^(3/4)` finite-aperture budget. -/
theorem intervalIntegral_clockedFirstDerivativeH2ServiceKernel_eq
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 ≤ horizon) :
    (∫ elapsed in (0 : ℝ)..horizon,
      clockedFirstDerivativeH2ServiceKernel nu elapsed) =
      (4 / 3 : ℝ) * (2 * nu) ^ (-1 / 4 : ℝ) *
        horizon ^ (3 / 4 : ℝ) := by
  have htwoNu : 0 ≤ 2 * nu := by positivity
  have hfactor : ∀ elapsed ∈ Icc (0 : ℝ) horizon,
      clockedFirstDerivativeH2ServiceKernel nu elapsed =
        (2 * nu) ^ (-1 / 4 : ℝ) * elapsed ^ (-1 / 4 : ℝ) := by
    intro elapsed helapsed
    unfold clockedFirstDerivativeH2ServiceKernel
    rw [show 2 * (nu * elapsed) = (2 * nu) * elapsed by ring,
      Real.mul_rpow htwoNu helapsed.1]
  calc
    (∫ elapsed in (0 : ℝ)..horizon,
        clockedFirstDerivativeH2ServiceKernel nu elapsed) =
        ∫ elapsed in (0 : ℝ)..horizon,
          (2 * nu) ^ (-1 / 4 : ℝ) * elapsed ^ (-1 / 4 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro elapsed helapsed
      rw [uIcc_of_le hhorizon] at helapsed
      exact hfactor elapsed helapsed
    _ = (2 * nu) ^ (-1 / 4 : ℝ) *
        ∫ elapsed in (0 : ℝ)..horizon, elapsed ^ (-1 / 4 : ℝ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (4 / 3 : ℝ) * (2 * nu) ^ (-1 / 4 : ℝ) *
        horizon ^ (3 / 4 : ℝ) := by
      rw [intervalIntegral_rpow_neg_one_quarter hhorizon]
      ring

/-- Exact evaluation of the frozen boundary service: the clock contributes `h^(3/4)` and the
source remains as the full native `H2` reconstruction payment. -/
theorem intervalIntegral_frozenH2SourceBoundaryServiceRate_eq_budget
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 ≤ horizon)
    (source : PeriodicVectorWeightedSobolev 2) :
    (∫ elapsed in (0 : ℝ)..horizon,
      frozenH2SourceBoundaryServiceRate nu source elapsed) =
      frozenH2SourceBoundaryClockBudget nu horizon * ‖source‖ := by
  unfold frozenH2SourceBoundaryServiceRate frozenH2SourceBoundaryClockBudget
  calc
    (∫ elapsed in (0 : ℝ)..horizon,
        6 * sharpHeatFirstDerivativeH2Constant *
          clockedFirstDerivativeH2ServiceKernel nu elapsed * ‖source‖) =
        ∫ elapsed in (0 : ℝ)..horizon,
          (6 * sharpHeatFirstDerivativeH2Constant * ‖source‖) *
            clockedFirstDerivativeH2ServiceKernel nu elapsed := by
      apply intervalIntegral.integral_congr
      intro elapsed _helapsed
      ring
    _ = (6 * sharpHeatFirstDerivativeH2Constant * ‖source‖) *
        ∫ elapsed in (0 : ℝ)..horizon,
          clockedFirstDerivativeH2ServiceKernel nu elapsed := by
      rw [intervalIntegral.integral_const_mul]
    _ = 8 * sharpHeatFirstDerivativeH2Constant *
        (2 * nu) ^ (-1 / 4 : ℝ) * horizon ^ (3 / 4 : ℝ) * ‖source‖ := by
      rw [intervalIntegral_clockedFirstDerivativeH2ServiceKernel_eq hnu hhorizon]
      ring

/-- Complete reconstruction-fibre squeeze at one fixed source face.  This sharpens the former
unevaluated service integral but deliberately retains its non-uniform source-norm payment. -/
theorem completeFrozenH2SourceCurlBoundaryMass_le_clockBudget
    {nu horizon : ℝ} (hnu : 0 < nu) (hhorizon : 0 < horizon)
    (hlocal : 2 * (nu * horizon) ≤ 1)
    (source : PeriodicVectorWeightedSobolev 2) :
    completeFrozenH2SourceCurlBoundaryMass nu horizon source ≤
      ENNReal.ofReal
        (frozenH2SourceBoundaryClockBudget nu horizon * ‖source‖) := by
  calc
    completeFrozenH2SourceCurlBoundaryMass nu horizon source ≤
        ENNReal.ofReal
          (∫ elapsed in (0 : ℝ)..horizon,
            frozenH2SourceBoundaryServiceRate nu source elapsed) :=
      completeFrozenH2SourceCurlBoundaryMass_le_integral_service
        hnu hhorizon hlocal source
    _ = ENNReal.ofReal
        (frozenH2SourceBoundaryClockBudget nu horizon * ‖source‖) := by
      rw [intervalIntegral_frozenH2SourceBoundaryServiceRate_eq_budget
        hnu hhorizon.le source]

/-- At the zero clock aperture the exact boundary action, and therefore its complete coefficient
mass fibre, is identically zero. -/
@[simp] theorem completeFrozenH2SourceCurlBoundaryMass_zero
    (nu : ℝ) (source : PeriodicVectorWeightedSobolev 2) :
    completeFrozenH2SourceCurlBoundaryMass nu 0 source = 0 := by
  unfold completeFrozenH2SourceCurlBoundaryMass
  simp [finiteFrozenH2SourceCurlBoundaryMass,
    frozenH2SourceCurlBoundaryAction, finiteHeatBoundaryResolventScalar,
    heatStokesMultiplier,
    Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound.complexVectorL1]

/-- The clock budget itself vanishes at the zero-aperture face for every positive viscosity. -/
theorem tendsto_frozenH2SourceBoundaryClockBudget_zero
    (nu : ℝ) :
    Tendsto (frozenH2SourceBoundaryClockBudget nu) (nhdsWithin 0 (Ici 0))
      (nhds 0) := by
  unfold frozenH2SourceBoundaryClockBudget
  have hpowerAt : Tendsto (fun horizon : ℝ ↦ horizon ^ (3 / 4 : ℝ))
      (nhds 0) (nhds 0) := by
    simpa using
      (Real.continuousAt_rpow_const 0 (3 / 4 : ℝ) (Or.inr (by norm_num))).tendsto
  have hpower : Tendsto (fun horizon : ℝ ↦ horizon ^ (3 / 4 : ℝ))
      (nhdsWithin 0 (Ici 0)) (nhds 0) :=
    hpowerAt.mono_left inf_le_left
  have hscaled := hpower.const_mul
    (8 * sharpHeatFirstDerivativeH2Constant *
      (2 * nu) ^ (-1 / 4 : ℝ))
  simpa [mul_assoc] using hscaled

/-- The complete integrated frozen-source receiver itself converges to zero on shrinking positive
clock apertures.  The source face is fixed; no terminal-uniform assertion is hidden here. -/
theorem tendsto_completeFrozenH2SourceCurlBoundaryMass_zero
    {nu : ℝ} (hnu : 0 < nu)
    (source : PeriodicVectorWeightedSobolev 2) :
    Tendsto
      (fun horizon ↦ completeFrozenH2SourceCurlBoundaryMass nu horizon source)
      (nhdsWithin 0 (Ici 0)) (nhds 0) := by
  let upper : ℝ → ℝ≥0∞ := fun horizon ↦
    ENNReal.ofReal (frozenH2SourceBoundaryClockBudget nu horizon * ‖source‖)
  have hbudgetReal : Tendsto
      (fun horizon ↦ frozenH2SourceBoundaryClockBudget nu horizon * ‖source‖)
      (nhdsWithin 0 (Ici 0)) (nhds 0) := by
    simpa using (tendsto_frozenH2SourceBoundaryClockBudget_zero nu).mul_const ‖source‖
  have hupperLimit : Tendsto upper (nhdsWithin 0 (Ici 0)) (nhds 0) := by
    simpa [upper, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hbudgetReal
  have hsmallSet : Iio ((2 * nu)⁻¹) ∈ nhdsWithin (0 : ℝ) (Ici 0) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (inv_pos.mpr (by positivity)))
  have hupper : ∀ᶠ horizon in nhdsWithin (0 : ℝ) (Ici 0),
      completeFrozenH2SourceCurlBoundaryMass nu horizon source ≤ upper horizon := by
    filter_upwards [self_mem_nhdsWithin, hsmallSet] with horizon hhorizon hsmall
    by_cases hzero : horizon = 0
    · subst horizon
      simp [upper]
    · have hpos : 0 < horizon := lt_of_le_of_ne hhorizon (Ne.symm hzero)
      have htwoNu : 0 < 2 * nu := by positivity
      have hsmall' : horizon < 1 / (2 * nu) := by
        simpa [one_div] using hsmall
      have hlocalStrict : horizon * (2 * nu) < 1 :=
        (lt_div_iff₀ htwoNu).mp hsmall'
      have hlocal : 2 * (nu * horizon) ≤ 1 := by
        nlinarith
      exact completeFrozenH2SourceCurlBoundaryMass_le_clockBudget
        hnu hpos hlocal source
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperLimit
    (Filter.Eventually.of_forall fun _ ↦ bot_le) hupper

/-- Actual-open-solution specialization: freezing the literal nonlinear source at any one strict
interior time gives a boundary population squeezed to zero by shrinking elapsed clock length. -/
theorem tendsto_openFrozenSharpSourceCurlBoundaryMass_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (targetTime : Ioo (0 : ℝ) T) :
    Tendsto
      (fun horizon ↦
        openFrozenSharpSourceCurlBoundaryMass solution targetTime horizon)
      (nhdsWithin 0 (Ici 0)) (nhds 0) := by
  exact tendsto_completeFrozenH2SourceCurlBoundaryMass_zero hnu
    (sharpNonlinearSource (openVelocityWeightedH3State solution targetTime))

section Audit

#print axioms intervalIntegral_clockedFirstDerivativeH2ServiceKernel_eq
#print axioms intervalIntegral_frozenH2SourceBoundaryServiceRate_eq_budget
#print axioms completeFrozenH2SourceCurlBoundaryMass_le_clockBudget
#print axioms completeFrozenH2SourceCurlBoundaryMass_zero
#print axioms tendsto_frozenH2SourceBoundaryClockBudget_zero
#print axioms tendsto_completeFrozenH2SourceCurlBoundaryMass_zero
#print axioms tendsto_openFrozenSharpSourceCurlBoundaryMass_zero

end Audit

end Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundaryScale
