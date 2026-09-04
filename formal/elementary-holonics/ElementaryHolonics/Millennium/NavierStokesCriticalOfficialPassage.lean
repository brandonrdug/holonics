import ElementaryHolonics.Millennium.NavierStokesCofinalConstruction
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeCompletedKernelPassage
import ElementaryHolonics.Millennium.NavierStokesOfficialAnalyticDischarges
import ElementaryHolonics.Millennium.NavierStokesPeriodicLocalExistence

/-!
# Scale-critical passage to the literal periodic Navier--Stokes receiver

The canonical derivative-rate finish line is sufficient, but it is supercritical under the
Navier--Stokes parabolic rebase.  The completed dyadic Hodge/BKM owner already continues an open
periodic solution from the scale-invariant time integral of `criticalVorticityRate`.  This file
connects that exact analytic current directly to the cofinal construction and the literal
official alternative B.

**[proved-derived; formal-checked]** The passage below is exact plumbing, not a regularity proof.
It leaves one openly displayed analytic obligation: terminal integrability of the critical
vorticity rate for every positive-viscosity official open solution.  No canonical derivative
bound is assumed or manufactured.
-/

noncomputable section

open MeasureTheory Set

namespace Soma.Holonics.Millennium.NavierStokesCriticalOfficialPassage

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCofinalConstruction
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeCompletedKernelPassage
open Soma.Holonics.Millennium.NavierStokesOfficialAnalyticDischarges
open Soma.Holonics.Millennium.NavierStokesOfficialBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOverlapUniqueness
open Soma.Holonics.Millennium.NavierStokesPeriodicLocalExistence

/-- **[project-postulate]** The scale-critical terminal obligation.  Unlike
`CanonicalTerminalControl`, this receiver is invariant under the parabolic Navier--Stokes scale.
Its unconditional inhabitation is the remaining analytic theorem on this route. -/
def CriticalVorticityTerminalControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    InitialVelocityConditionPeriodic initial →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      IntervalIntegrable (criticalVorticityRate solution) volume 0 T

/-- **[proved-derived; formal-checked]** An open periodic solution reconstructs the complete
smooth, divergence-free, periodic condition on its initial face.  Thus the cofinal extension law
does not need an extra admissibility premise. -/
theorem initialVelocityConditionPeriodic_of_openPeriodicSolution
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    InitialVelocityConditionPeriodic initial := by
  have hzero : (0 : ℝ) ∈ openTimeSlab T :=
    ⟨le_rfl, solution.terminal_pos⟩
  have hsection : (fun x ↦ velocity x 0) = initial := by
    funext x
    exact solution.initial x
  refine {
    divergenceFree := ?_
    smooth := ?_
    periodic := ?_ }
  · intro x
    rw [← hsection]
    exact solution.incompressible x 0 hzero
  · rw [← hsection]
    exact
      Soma.Holonics.Millennium.NavierStokesOverlapUniqueness.OpenPeriodicSolutionOn.velocitySpatialSmooth
        solution hzero
  · rw [← hsection]
    exact solution.velocityPeriodic 0 hzero

/-- **[proved-derived; formal-checked, conditional]** Critical terminal control supplies the
universal compatible-extension law through the completed dyadic Hodge kernel and weighted restart
owners. -/
theorem positivePeriodicCompatibleExtensionLaw_of_criticalVorticityTerminalControl
    (control : CriticalVorticityTerminalControl) :
    PositivePeriodicCompatibleExtensionLaw := by
  intro T nu initial velocity pressure hnu solution
  refine ⟨compatibleOpenPeriodicExtension_of_integrableCriticalVorticity
    solution hnu ?_⟩
  exact control hnu
    (initialVelocityConditionPeriodic_of_openPeriodicSolution solution) solution

/-- **[proved-derived; formal-checked, conditional]** The scale-critical terminal theorem is
sufficient for the literal official periodic existence receiver.  This route bypasses the
strictly stronger canonical derivative-rate field of `PeriodicStatementBFinishLine`. -/
theorem statementB_of_criticalVorticityTerminalControl
    (control : CriticalVorticityTerminalControl) : StatementB := by
  have extensionLaw : PositivePeriodicCompatibleExtensionLaw :=
    positivePeriodicCompatibleExtensionLaw_of_criticalVorticityTerminalControl control
  have cofinalConstruction := cofinalPeriodicAtlas_of_local_extension_unique
    periodicLocalExistence periodicOpenUniqueness extensionLaw
  intro nu hnu initial hinitial
  obtain ⟨atlas⟩ := cofinalConstruction nu hnu initial hinitial
  exact ⟨atlas.velocity, atlas.pressure, periodicGlobalization atlas⟩

/-- **[proved-derived; formal-checked, conditional]** The same critical theorem reaches the
repository's literal four-alternative official problem proposition. -/
theorem officialProblem_of_criticalVorticityTerminalControl
    (control : CriticalVorticityTerminalControl) : TheOfficialNavierStokesProblem :=
  Or.inr (Or.inl (statementB_of_criticalVorticityTerminalControl control))

section Audit

#print axioms initialVelocityConditionPeriodic_of_openPeriodicSolution
#print axioms positivePeriodicCompatibleExtensionLaw_of_criticalVorticityTerminalControl
#print axioms statementB_of_criticalVorticityTerminalControl
#print axioms officialProblem_of_criticalVorticityTerminalControl

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalOfficialPassage
