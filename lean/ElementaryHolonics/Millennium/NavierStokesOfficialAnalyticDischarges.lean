import ElementaryHolonics.Millennium.NavierStokesOfficialBridge
import ElementaryHolonics.Millennium.NavierStokesOverlapUniqueness
import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
import ElementaryHolonics.Millennium.NavierStokesCofinalGlobalization

/-!
# Proved analytic fields of the periodic Navier--Stokes finish line

This module deposits the official fields already returned by the existing analytic owners.  It
does not package a `PeriodicStatementBFinishLine`: the cofinal construction and the unconditional
terminal derivative estimate remain separate open obligations.

Every theorem below is `[proved-derived; formal-checked]`.
-/

noncomputable section

open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesOfficialAnalyticDischarges

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCofinalGlobalization
open Soma.Holonics.Millennium.NavierStokesOfficialBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOverlapUniqueness
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus

/-- The official terminal derivative chart and the source continuation chart are the same
compact-map occurrence. -/
theorem terminalCanonicalVorticityDerivativeChart_eq_openPeriodic
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    terminalCanonicalVorticityDerivativeChart solution t =
      openPeriodicVorticityDerivativeChart solution t := by
  rfl

/-- Consequently the official terminal rate is literally the source rate consumed by the proved
critical-vorticity continuation owner. -/
theorem terminalCanonicalVorticityDerivativeRate_eq_openPeriodic
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    terminalCanonicalVorticityDerivativeRate solution =
      openPeriodicCanonicalVorticityDerivativeRate solution := by
  funext s
  by_cases hs : s ∈ Set.Ioo 0 T
  · simp only [terminalCanonicalVorticityDerivativeRate,
      openPeriodicCanonicalVorticityDerivativeRate, hs, dite_true,
      terminalCanonicalVorticityLipschitzConstant,
      openPeriodicCanonicalVorticityLipschitzConstant,
      terminalCanonicalVorticityDerivativeChart_eq_openPeriodic]
  · simp only [terminalCanonicalVorticityDerivativeRate,
      openPeriodicCanonicalVorticityDerivativeRate, hs, dite_false]

/-- The already proved BKM/Hodge/restart construction discharges the official terminal-extension
law once the rate spelling is rebased exactly. -/
theorem canonicalTerminalExtensionLaw : CanonicalTerminalExtensionLaw := by
  constructor
  intro T nu initial velocity pressure solution hnu hcontrol
  refine ⟨compatibleOpenPeriodicExtension_of_integrableCanonicalDerivativeRate
    solution hnu ?_⟩
  rw [← terminalCanonicalVorticityDerivativeRate_eq_openPeriodic solution]
  exact hcontrol

/-- Periodic energy uniqueness discharges the official positive-viscosity overlap field. -/
theorem periodicOpenUniqueness : PeriodicOpenUniqueness := by
  constructor
  intro T nu initial force velocity₁ velocity₂ pressure₁ pressure₂
    hnu solution₁ solution₂
  exact (openPeriodicOverlapUniqueness_of_nonnegativeViscosity
      (show 0 ≤ nu from hnu.le)).agreesBefore
    solution₁ solution₂ solution₁.terminal_pos le_rfl le_rfl

/-- The shared cofinal atlas globalization field is already proved, rather than postulated. -/
theorem periodicGlobalization : PeriodicGlobalizationLaw :=
  periodicGlobalizationLaw

section Audit

#print axioms terminalCanonicalVorticityDerivativeChart_eq_openPeriodic
#print axioms terminalCanonicalVorticityDerivativeRate_eq_openPeriodic
#print axioms canonicalTerminalExtensionLaw
#print axioms periodicOpenUniqueness
#print axioms periodicGlobalization

end Audit

end Soma.Holonics.Millennium.NavierStokesOfficialAnalyticDischarges
