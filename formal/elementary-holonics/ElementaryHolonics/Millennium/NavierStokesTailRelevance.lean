import ElementaryHolonics.Millennium.NavierStokesExteriorFaceGenerator

/-!
# Receiver-relative tail tolerance and a terminal integrability criterion

The full strain receiver is its finite addressed band plus a convergent tail. At each fixed
interior time, the tail bound tends to zero as the band grows. Thus every positive tolerance is
eventually met at that time. This is neither exact zero at a finite radius nor invisibility to
every possible receiver, and the required radius can depend on time and tolerance.

`TailRelevanceControl` is a separate terminal-time integrability hypothesis for a fixed radius,
with measurability and continuity. It returns the aligned-strain budget and the periodic official
alternative. Integrability does not say that the tail is zero or that no future receiver can
separate it. Pointwise convergence in radius does not prove that terminal control.

This is a quantitative fluid instance of relevance, with the actual unforced periodic solution
and receiver retained. The control itself is not proved in this owner.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesTailRelevance

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

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}

/-- The tail mass at cube radius `N`, read as a function of time; zero outside the open lifespan. -/
def tailMass (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (radius : ℕ) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo 0 T then
    openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩ (frequencyCube radius)
  else 0

theorem tailMass_nonneg
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (radius : ℕ) (t : ℝ) : 0 ≤ tailMass solution radius t := by
  unfold tailMass
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

/-! ## The cubes are cofinal among finite frequency populations -/

theorem tendsto_frequencyCube_atTop : Tendsto frequencyCube atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro modes
  refine ⟨modes.sup fun k => Finset.univ.sup fun c => (k c).natAbs, fun n hn k hk => ?_⟩
  rw [mem_frequencyCube_iff]
  intro c
  have h1 : (k c).natAbs ≤ n :=
    le_trans (le_trans (Finset.le_sup (f := fun c => (k c).natAbs) (Finset.mem_univ c))
      (Finset.le_sup (f := fun k => Finset.univ.sup fun c => (k c).natAbs) hk)) hn
  omega

/-! ## Tail tolerance at a fixed interior event -/

/-- At each fixed interior time, the tail bound eventually lies below every positive tolerance.
The statement supplies no exact finite cutoff or uniform terminal-time bound. -/
theorem tendsto_tailMass_atTop
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    Tendsto (fun radius => tailMass solution radius t) atTop (𝓝 0) := by
  have hentry : ∀ component coordinate : Fin 3,
      Tendsto (fun radius : ℕ =>
        ∑' frequency : {frequency : SpatialFrequency // frequency ∉ frequencyCube radius},
          ‖openPeriodicJacobianFourierMode solution ⟨t, ht⟩ frequency.1 component coordinate‖)
        atTop (𝓝 0) := by
    intro component coordinate
    exact (tendsto_tsum_compl_atTop_zero
      (fun frequency : SpatialFrequency =>
        ‖openPeriodicJacobianFourierMode solution ⟨t, ht⟩ frequency component coordinate‖)).comp
      tendsto_frequencyCube_atTop
  have harray : Tendsto (fun radius : ℕ => (fun component coordinate : Fin 3 =>
      ∑' frequency : {frequency : SpatialFrequency // frequency ∉ frequencyCube radius},
        ‖openPeriodicJacobianFourierMode solution ⟨t, ht⟩ frequency.1 component coordinate‖ :
      Fin 3 → Fin 3 → ℝ)) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro component
    rw [tendsto_pi_nhds]
    intro coordinate
    simpa using hentry component coordinate
  have hnorm := harray.norm
  rw [norm_zero] at hnorm
  refine hnorm.congr' ?_
  filter_upwards with radius
  simp [tailMass, ht, openPeriodicJacobianCoefficientTailMass]

/-! ## A separate terminal-time integrability criterion -/

/-- The relevance budget at radius `N`: the exterior face paid by the initial energy plus the
tail mass, times the interior coordinate comparison `3²`. -/
def relevanceBudget
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (radius : ℕ) (t : ℝ) : ℝ :=
  3 ^ 2 * (2 * Real.pi * exteriorFaceMass radius *
    (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0)) + tailMass solution radius t)

theorem alignedStrain_le_relevanceBudget
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) (radius : ℕ) :
    alignedStrain velocity x t ≤
      relevanceBudget solution radius t * ‖vorticityField velocity x t‖ ^ 2 := by
  have h := alignedStrain_le_exterior_add_interior solution hnu x ht radius
  simp only [relevanceBudget, tailMass, dif_pos ht]
  convert h using 1
  ring

/-- Every admitted positive-viscosity solution has a fixed cube radius with a measurable,
continuous, interval-integrable tail bound on a terminal interval. This is an additional
hypothesis, not exact invisibility or a consequence of the pointwise tail limit. -/
def TailRelevanceControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (radius : ℕ) (s : ℝ), 0 < s ∧ s < T ∧
        Measurable (tailMass solution radius) ∧
        ContinuousOn (tailMass solution radius) (Ioo s T) ∧
        IntervalIntegrable (tailMass solution radius) volume s T

/-- The aligned strain budget returned by one relevant radius. -/
def AlignedStrainBudget.ofTailRelevance
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (radius : ℕ) {s : ℝ} (hs : 0 < s) (hsT : s < T)
    (hmeas : Measurable (tailMass solution radius))
    (hcont : ContinuousOn (tailMass solution radius) (Ioo s T))
    (hint : IntervalIntegrable (tailMass solution radius) volume s T) :
    AlignedStrainBudget solution where
  start := s
  start_pos := hs
  start_lt := hsT
  budget := relevanceBudget solution radius
  budget_measurable := measurable_const.mul (measurable_const.add hmeas)
  budget_continuousOn := continuousOn_const.mul (continuousOn_const.add hcont)
  budget_integrable := by
    unfold relevanceBudget
    exact (intervalIntegrable_const.add hint).const_mul _
  dominates := fun x t ht =>
    alignedStrain_le_relevanceBudget solution hnu x ⟨hs.trans ht.1, ht.2⟩ radius

theorem alignedStrainTerminalControl_of_tailRelevance (h : TailRelevanceControl) :
    AlignedStrainTerminalControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨radius, s, hs, hsT, hmeas, hcont, hint⟩ := h hnu solution
  exact ⟨AlignedStrainBudget.ofTailRelevance solution hnu.le radius hs hsT hmeas hcont hint⟩

/-- The stated terminal integrability control returns the periodic official alternative. -/
theorem statementB_of_tailRelevance (h : TailRelevanceControl) : StatementB :=
  statementB_of_alignedStrainTerminalControl (alignedStrainTerminalControl_of_tailRelevance h)

theorem officialProblem_of_tailRelevance (h : TailRelevanceControl) :
    TheOfficialNavierStokesProblem :=
  Or.inr (Or.inl (statementB_of_tailRelevance h))

section Audit

#print axioms tendsto_frequencyCube_atTop
#print axioms tendsto_tailMass_atTop
#print axioms alignedStrain_le_relevanceBudget
#print axioms statementB_of_tailRelevance
#print axioms officialProblem_of_tailRelevance

end Audit

end Soma.Holonics.Millennium.NavierStokesTailRelevance
