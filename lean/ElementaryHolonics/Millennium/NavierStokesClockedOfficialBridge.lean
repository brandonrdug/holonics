import ElementaryHolonics.Millennium.NavierStokesClockedExtensionTower
import ElementaryHolonics.Millennium.NavierStokesOfficialBridge
import ElementaryHolonics.Millennium.NavierStokesForceObstruction

/-!
# Clocked extension occupation at the official Navier--Stokes finish line

This module connects the clocked strict-extension holon to the official periodic finish line.  A
canonical terminal-control receipt occupies the exact source fibre whenever the declared terminal
extension law is available.  The future-force counterexample fires at the same receiver: its
source fibre is empty even though an accumulated interior Jacobian-control receipt is inhabited.

The source-specific analytic obstruction is named as an integrable majorant inequality for the
canonical vorticity-derivative rate.  It is sufficient for `CanonicalTerminalControl`; no claim is
made here that the Navier--Stokes equations already supply that majorant.

All introduced carriers are `[definition]`.  Every theorem is
`[proved-derived; formal-checked]` unless its statement says otherwise.
-/

noncomputable section

open scoped Interval NNReal

namespace Soma.Holonics.Millennium.NavierStokesClockedOfficialBridge

open MeasureTheory Set
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesClockedExtensionTower
open Soma.Holonics.Millennium.NavierStokesForceObstruction
open Soma.Holonics.Millennium.NavierStokesOfficialBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy

/-! ## The official solution as a clocked-extension boundary state -/

/-- [definition] Bundle one existing open solution as the exact state seen by the continuation
holon. -/
def stateOfSolution
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    OpenPeriodicState nu initial force where
  lifetime := T
  velocity := velocity
  pressure := pressure
  solution := solution

/-- A canonical terminal-control receipt occupies the exact strict-extension source fibre once
the official terminal extension law is supplied. -/
theorem canonicalTerminalControl_occupies_extensionSourceFibre
    (law : CanonicalTerminalExtensionLaw)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (control : CanonicalTerminalControl solution) :
    Nonempty (ExtensionSourceFibre (stateOfSolution solution)) := by
  apply (canExtendCompatibly_iff_extensionSourceFibre_nonempty
    (stateOfSolution solution)).mp
  exact law.extension solution hnu control

/-- The complete official finish-line certificate therefore occupies the same exact source fibre
for every admitted periodic datum. -/
theorem finishLine_occupies_extensionSourceFibre
    (finish : PeriodicStatementBFinishLine)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (hnu : 0 < nu) (hinitial : InitialVelocityConditionPeriodic initial)
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    Nonempty (ExtensionSourceFibre (stateOfSolution solution)) := by
  exact canonicalTerminalControl_occupies_extensionSourceFibre
    finish.terminalExtension solution hnu
      (finish.canonicalTerminalControl hnu hinitial solution)

/-! ## The named terminal majorant obstruction -/

/-- [open] A source-specific terminal majorant receipt.  Its substantive PDE field is the
pointwise domination of the canonical vorticity-derivative population by one terminally integrable
function.  Measurability is retained separately because an inequality alone cannot create an
integral. -/
structure CanonicalTerminalMajorantReceipt
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) where
  majorant : ℝ → ℝ
  majorant_intervalIntegrable : IntervalIntegrable majorant volume 0 T
  rate_aestronglyMeasurable : AEStronglyMeasurable
    (terminalCanonicalVorticityDerivativeRate solution) (volume.restrict (uIoc 0 T))
  dominates : ∀ᵐ s ∂(volume.restrict (uIoc 0 T)),
    ‖terminalCanonicalVorticityDerivativeRate solution s‖ ≤ majorant s

/-- An integrable terminal majorant closes the official canonical terminal-control receiver. -/
theorem CanonicalTerminalMajorantReceipt.canonicalTerminalControl
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure}
    (receipt : CanonicalTerminalMajorantReceipt solution) :
    CanonicalTerminalControl solution := by
  exact receipt.majorant_intervalIntegrable.mono_fun'
    receipt.rate_aestronglyMeasurable receipt.dominates

/-- A terminal majorant, followed by the official extension law, occupies the exact extension
fibre.  This is the shortest typed analytic-to-holonic passage in the official bridge. -/
theorem CanonicalTerminalMajorantReceipt.occupies_extensionSourceFibre
    (law : CanonicalTerminalExtensionLaw)
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure}
    (receipt : CanonicalTerminalMajorantReceipt solution) (hnu : 0 < nu) :
    Nonempty (ExtensionSourceFibre (stateOfSolution solution)) :=
  canonicalTerminalControl_occupies_extensionSourceFibre
    law solution hnu receipt.canonicalTerminalControl

/-! ## Firing receiver counterexample -/

/-- [definition] The zero interior solution for the terminal-spike force, bundled as an exact
extension-holon boundary state. -/
def terminalSpikeZeroState (T nu : ℝ) (hT : 0 < T) :
    OpenPeriodicState nu 0 (terminalSpikeForce T) :=
  stateOfSolution (zeroOpenPeriodicSolution T nu hT)

/-- [counterexample; formal-checked] The future-force obstruction returns an empty strict-extension
source fibre.  This is the firing falsifier for any purported generic clock/scale argument which
claims to manufacture continuation from interior data alone. -/
theorem terminalSpikeZeroState_extensionSourceFibre_isEmpty
    (T nu : ℝ) (hT : 0 < T) :
    IsEmpty (ExtensionSourceFibre (terminalSpikeZeroState T nu hT)) := by
  constructor
  intro carried
  apply zeroOpenPeriodicSolution_isMaximal T nu hT
  exact (canExtendCompatibly_iff_extensionSourceFibre_nonempty
    (terminalSpikeZeroState T nu hT)).mpr ⟨carried⟩

/-- [counterexample; formal-checked] An inhabited accumulated interior Jacobian-control receiver
does not force occupation of the strict-extension fibre for an arbitrary fixed future force. -/
theorem accumulatedInteriorControl_does_not_imply_extensionFibreOccupation
    (T nu : ℝ) (hT : 0 < T) (hnu : 0 ≤ nu) :
    ¬ (OpenAccumulatedJacobianControl T nu (terminalSpikeForce T) 0
          (T / 2) 0 (fun _ => 0) →
        Nonempty (ExtensionSourceFibre (terminalSpikeZeroState T nu hT))) := by
  intro implication
  obtain ⟨carried⟩ := implication (zeroAccumulatedJacobianControl T nu hT hnu)
  exact (terminalSpikeZeroState_extensionSourceFibre_isEmpty T nu hT).false carried

section Audit

#print axioms canonicalTerminalControl_occupies_extensionSourceFibre
#print axioms finishLine_occupies_extensionSourceFibre
#print axioms CanonicalTerminalMajorantReceipt.canonicalTerminalControl
#print axioms CanonicalTerminalMajorantReceipt.occupies_extensionSourceFibre
#print axioms terminalSpikeZeroState_extensionSourceFibre_isEmpty
#print axioms accumulatedInteriorControl_does_not_imply_extensionFibreOccupation

end Audit

end Soma.Holonics.Millennium.NavierStokesClockedOfficialBridge
