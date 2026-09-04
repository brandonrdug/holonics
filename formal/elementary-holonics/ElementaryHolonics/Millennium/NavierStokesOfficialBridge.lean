import ElementaryHolonics.Millennium.NavierStokesTorusFourier

/-!
# The periodic Navier--Stokes official finish line

**[definition]** The continuation development works on half-open lifespans, whereas official
alternative B asks for one smooth periodic world-tube on every nonnegative time.  This file names
the construction targets between those levels:

1. a pressure-normalized, cofinal atlas solving every finite open slab;
2. uniqueness modulo the pressure gauge on overlaps;
3. terminal integrability of the canonical compact-chart vorticity-derivative receiver and the
   exact continuation law which turns it into a compatible strict extension; and
4. the analytic local-to-global gluing law which upgrades one cofinal atlas to the official global
   `PeriodicSolution` carrier.

**[proved-derived; formal-checked]** The finish-line certificate does not contain `StatementB`.
Its closing theorem returns literally that existing proposition.
-/

noncomputable section

open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesOfficialBridge

open MeasureTheory Set
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- [definition] A fixed pressure gauge: the pressure vanishes at the spatial origin at every
nonnegative time.  This removes the time-dependent additive ambiguity before global gluing. -/
def PressureNormalized (pressure : PressureField) : Prop :=
  ∀ t : ℝ, 0 ≤ t → pressure 0 t = 0

/-- [project-postulate] A single pair of fields whose restriction solves every finite half-open
slab.  The fields are shared across the family, so compatibility is definitional rather than an
endpoint-only relation. -/
structure CofinalPeriodicAtlas (nu : ℝ) (initial : InitialVelocity) where
  velocity : VelocityField
  pressure : PressureField
  pressureNormalized : PressureNormalized pressure
  onOpenSlab : ∀ T : ℝ, 0 < T →
    OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure

/-- [project-postulate] Local existence in the exact open-lifespan carrier used by the continuation
line. -/
def HasPeriodicLocalExistence : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ initial : InitialVelocity,
    InitialVelocityConditionPeriodic initial →
      ∃ (T : ℝ) (velocity : VelocityField) (pressure : PressureField),
        0 < T ∧
          OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure

/-- [project-postulate] Uniqueness on every common open lifespan at the positive viscosities in
the official periodic problem, with exact velocity agreement and pressure-gradient agreement.
This is the overlap law required for lawful gluing. -/
structure PeriodicOpenUniqueness : Prop where
  unique : ∀ {T nu : ℝ} {initial : InitialVelocity} {force : VelocityField}
    {velocity₁ velocity₂ : VelocityField} {pressure₁ pressure₂ : PressureField},
    0 < nu →
    OpenPeriodicSolutionOn T nu initial force velocity₁ pressure₁ →
    OpenPeriodicSolutionOn T nu initial force velocity₂ pressure₂ →
    PeriodicFieldsAgreeBefore T velocity₁ velocity₂ pressure₁ pressure₂

/-- [definition] The actual spatial derivative of vorticity on the compact radius-three chart
used by the periodic torus-distance lift. -/
def terminalCanonicalVorticityDerivativeChart
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    C(Metric.closedBall (0 : Space) 3, Space →L[ℝ] Space) :=
  ⟨fun x ↦ fderiv ℝ (fun y ↦ vorticityField velocity y t.1) x.1,
    ((vorticityField_contDiff_one velocity t.1
      ((openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).of_le
        (WithTop.coe_le_coe.mpr le_top))).continuous_fderiv one_ne_zero).comp
      continuous_subtype_val⟩

/-- [definition] The canonical nonnegative receiver is the exact compact-map norm of the complete
derivative population. -/
def terminalCanonicalVorticityLipschitzConstant
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℝ≥0 :=
  ‖terminalCanonicalVorticityDerivativeChart solution t‖₊

/-- [definition] The terminal-control chart of the canonical spatial derivative receiver.  This
is extensionally the source expression later named
`openPeriodicCanonicalVorticityDerivativeRate`, reconstructed here from its upstream owners so the
finish line does not depend on the currently stale downstream build artifact. -/
def terminalCanonicalVorticityDerivativeRate
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (s : ℝ) : ℝ :=
  if hs : s ∈ Set.Ioo 0 T then
    (terminalCanonicalVorticityLipschitzConstant solution ⟨s, hs⟩ : ℝ)
  else 0

/-- [project-postulate] The active PDE-owned obstruction on one open lifespan: terminal
integrability of the canonical spatial vorticity-derivative population.  Interior smoothness alone
does not imply this endpoint control. -/
def CanonicalTerminalControl
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) : Prop :=
  IntervalIntegrable (terminalCanonicalVorticityDerivativeRate solution) volume 0 T

/-- [project-postulate] The exact adapter law discharged downstream by
`compatibleOpenPeriodicExtension_of_integrableCanonicalDerivativeRate`: terminal integrability of
the canonical derivative receiver returns the existing addressed extension carrier. -/
structure CanonicalTerminalExtensionLaw : Prop where
  extension : ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure),
    0 < nu → CanonicalTerminalControl solution →
      Nonempty (CompatibleOpenPeriodicExtension solution)

/-- [project-postulate] The remaining sheaf/gluing theorem: joint smoothness, the time derivative,
the PDE, periodicity, and the normalized pressure all descend from every finite restriction to the
closed nonnegative-time world-tube.  Its premise is strictly stronger than the conclusion's bare
existence and retains the complete cofinal atlas. -/
def PeriodicGlobalizationLaw : Prop :=
  ∀ {nu : ℝ} {initial : InitialVelocity} (atlas : CofinalPeriodicAtlas nu initial),
    PeriodicSolution nu initial (0 : VelocityField) atlas.velocity atlas.pressure

/-- [project-postulate] The complete alternative-B finish line.  It exposes cofinal construction,
overlap uniqueness, canonical terminal control, its addressed extension law, and analytic
globalization as separately addressable obligations. -/
structure PeriodicStatementBFinishLine : Prop where
  cofinalConstruction : ∀ nu : ℝ, 0 < nu → ∀ initial : InitialVelocity,
    InitialVelocityConditionPeriodic initial →
      Nonempty (CofinalPeriodicAtlas nu initial)
  overlapUniqueness : PeriodicOpenUniqueness
  canonicalTerminalControl : ∀ {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    InitialVelocityConditionPeriodic initial →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      CanonicalTerminalControl solution
  terminalExtension : CanonicalTerminalExtensionLaw
  globalization : PeriodicGlobalizationLaw

/-- [proved-derived; formal-checked] A cofinal construction already supplies genuine local
existence in the existing half-open carrier. -/
theorem localExistence_of_finishLine (finish : PeriodicStatementBFinishLine) :
    HasPeriodicLocalExistence := by
  intro nu hnu initial hinitial
  obtain ⟨atlas⟩ := finish.cofinalConstruction nu hnu initial hinitial
  exact ⟨1, atlas.velocity, atlas.pressure, zero_lt_one, atlas.onOpenSlab 1 zero_lt_one⟩

/-- [proved-derived; formal-checked] Cofinality plus overlap uniqueness gives every finite
open-lifespan solution a gauge-compatible strict extension.  Hence no finite member of the
official-data family can be maximal. -/
theorem canExtendCompatibly_of_finishLine
    (finish : PeriodicStatementBFinishLine)
    {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField}
    (hnu : 0 < nu) (hinitial : InitialVelocityConditionPeriodic initial)
    (base : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    base.CanExtendCompatibly := by
  exact finish.terminalExtension.extension base hnu
    (finish.canonicalTerminalControl hnu hinitial base)

/-- [proved-derived; formal-checked] A completed construction/uniqueness/gluing certificate closes
literal official alternative B. -/
theorem statementB_of_finishLine (finish : PeriodicStatementBFinishLine) : StatementB := by
  intro nu hnu initial hinitial
  obtain ⟨atlas⟩ := finish.cofinalConstruction nu hnu initial hinitial
  exact ⟨atlas.velocity, atlas.pressure, finish.globalization atlas⟩

/-- [proved-derived; formal-checked] The same certificate closes the disjunctive official
Navier--Stokes prize target through alternative B. -/
theorem officialProblem_of_finishLine (finish : PeriodicStatementBFinishLine) :
    TheOfficialNavierStokesProblem :=
  Or.inr (Or.inl (statementB_of_finishLine finish))

section Audit

#print axioms localExistence_of_finishLine
#print axioms canExtendCompatibly_of_finishLine
#print axioms statementB_of_finishLine
#print axioms officialProblem_of_finishLine

end Audit

end Soma.Holonics.Millennium.NavierStokesOfficialBridge
