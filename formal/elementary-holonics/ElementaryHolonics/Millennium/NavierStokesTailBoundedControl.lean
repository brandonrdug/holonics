import ElementaryHolonics.Millennium.NavierStokesTailRelevance

/-!
# A bounded tail mass on a terminal tail returns the periodic finish line

`TailRelevanceControl` asks the Jacobian tail mass to be measurable, continuous, and
interval-integrable on a terminal tail.  A constant budget needs none of that.  If the tail mass
at one radius stays below `M` on `[s, T)`, the aligned strain budget is the constant
`3² · (2π · G(N) · 3√(2E(0)) + M)`, and the periodic official alternative follows.

This is the form of the relevance control that the weighted tail energy bound will discharge.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesTailBoundedControl

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesExteriorFaceGenerator
open Soma.Holonics.Millennium.NavierStokesTailRelevance

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}

/-- The constant relevance budget at radius `N` with tail bound `M`. -/
def boundedBudget (velocity : VelocityField) (radius : ℕ) (M : ℝ) : ℝ :=
  3 ^ 2 * (2 * Real.pi * exteriorFaceMass radius *
    (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0)) + M)

theorem alignedStrain_le_boundedBudget
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) {radius : ℕ} {M : ℝ}
    (hM : tailMass solution radius t ≤ M) :
    alignedStrain velocity x t ≤
      boundedBudget velocity radius M * ‖vorticityField velocity x t‖ ^ 2 := by
  refine (alignedStrain_le_relevanceBudget solution hnu x ht radius).trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  unfold relevanceBudget boundedBudget
  linarith

/-- The aligned strain budget returned by a bounded tail mass. -/
def AlignedStrainBudget.ofTailBounded
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (radius : ℕ) {s : ℝ} (hs : 0 < s) (hsT : s < T) {M : ℝ}
    (hM : ∀ t ∈ Ioo s T, tailMass solution radius t ≤ M) :
    AlignedStrainBudget solution where
  start := s
  start_pos := hs
  start_lt := hsT
  budget := fun _ ↦ boundedBudget velocity radius M
  budget_measurable := measurable_const
  budget_continuousOn := continuousOn_const
  budget_integrable := intervalIntegrable_const
  dominates := fun x t ht ↦
    alignedStrain_le_boundedBudget solution hnu x ⟨hs.trans ht.1, ht.2⟩ (hM t ht)

/-- **The bounded relevance control.**  For every admitted positive-viscosity solution some radius
has a tail mass bounded on a terminal tail. -/
def TailBoundedControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (radius : ℕ) (s M : ℝ), 0 < s ∧ s < T ∧
        ∀ t ∈ Ioo s T, tailMass solution radius t ≤ M

theorem alignedStrainTerminalControl_of_tailBounded (h : TailBoundedControl) :
    AlignedStrainTerminalControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨radius, s, M, hs, hsT, hM⟩ := h hnu solution
  exact ⟨AlignedStrainBudget.ofTailBounded solution hnu.le radius hs hsT hM⟩

/-- **A bounded tail mass returns the periodic official alternative.** -/
theorem statementB_of_tailBounded (h : TailBoundedControl) : StatementB :=
  statementB_of_alignedStrainTerminalControl (alignedStrainTerminalControl_of_tailBounded h)

section Audit

#print axioms alignedStrain_le_boundedBudget
#print axioms statementB_of_tailBounded

end Audit

end Soma.Holonics.Millennium.NavierStokesTailBoundedControl
