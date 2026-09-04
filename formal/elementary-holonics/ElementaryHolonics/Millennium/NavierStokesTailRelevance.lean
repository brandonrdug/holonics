import ElementaryHolonics.Millennium.NavierStokesExteriorFaceGenerator

/-!
# The relevance theorem: the unaddressed tail is irrelevant at every event, and the periodic
# finish line asks only that it stay irrelevant up to the terminal time

Brandon's relevance hypothesis: a value stands only when a receiver reaches it; the population
beyond an addressed band is a potential face, not an actual one, until some receiver acquires a
separating word for it.  On the torus this is not a doctrine but an equation.  The full strain
reading at an event is exactly its finite addressed band plus its addressed convergent tail
(`openPeriodicFullStrainReading_eq_finite_add_tail`), and the exterior face is paid at `t = 0`
(`alignedStrain_le_exterior_add_interior`).

This owner proves the two halves of the relevance theorem.

* **At every event the tail is irrelevant.**  For each interior time the tail mass at cube
  radius `N` tends to zero as `N` grows: no receiver at that event separates the tail once the
  band is wide enough.  This spends only the absolute summability Sol already proved and the
  cofinality of the cubes among finite frequency populations.
* **The finish line is uniform relevance.**  If, for every admitted solution, one radius exists
  whose tail mass stays interval-integrable up to `T`, then the aligned strain budget is
  inhabited and the periodic official alternative `StatementB` follows.  The continuum
  hypothesis of the Clay posing is therefore consumed at exactly one place: the uniformity of the
  tail's irrelevance in time.  "The tail never acquires a separating word before `T`" is that
  integrability.

Nothing here inhabits the uniform control.  It is the sole remaining obligation on this route,
now stated as relevance rather than as regularity.
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

/-! ## At every event the tail is irrelevant -/

/-- **Per-event irrelevance.**  At each interior time the tail mass tends to zero as the cube
radius grows: once the addressed band is wide enough no receiver at that event separates the
tail. -/
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

/-! ## The finish line is uniform relevance -/

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

/-- **The relevance hypothesis as a control.**  For every admitted positive-viscosity solution some
cube radius has a tail mass that stays measurable, continuous, and interval-integrable on a
terminal tail.  This is "the tail never acquires a separating word before `T`". -/
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

/-- **The relevance theorem.**  Uniform irrelevance of the tail returns the periodic official
alternative. -/
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
