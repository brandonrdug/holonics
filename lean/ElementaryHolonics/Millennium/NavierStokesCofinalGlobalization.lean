import ElementaryHolonics.Millennium.NavierStokesOfficialBridge

/-!
# Globalization of a shared cofinal periodic atlas

The official bridge stores one common velocity and pressure field whose restriction solves every
positive half-open lifespan.  This file proves that the remaining local-to-global passage is not a
new PDE hypothesis: every finite time has a larger open slab, and that slab agrees locally with the
nonnegative-time carrier.  The derivative and smoothness charts therefore rebase through an exact
neighborhood equality.

Every theorem is `[proved-derived; formal-checked]`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesCofinalGlobalization

open ContDiff Filter Set
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOfficialBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan

/-- The finite half-open lifespan and the nonnegative half-line agree in a neighborhood of every
time strictly below the finite terminal face. -/
theorem openTimeSlab_eventuallyEq_Ici
    {t T : ℝ} (htT : t < T) :
    Filter.EventuallyEq (nhds t) (openTimeSlab T) (Ici (0 : ℝ)) := by
  filter_upwards [Iio_mem_nhds htT] with s hs
  apply propext
  change (0 ≤ s ∧ s < T) ↔ 0 ≤ s
  exact ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩

/-- The corresponding space--time cylinders agree locally at every point strictly before the
finite terminal face. -/
theorem openSpaceTimeSlab_eventuallyEq_univ_prod_Ici
    {z : Space × ℝ} {T : ℝ} (hzT : z.2 < T) :
    Filter.EventuallyEq (nhds z) (openSpaceTimeSlab T)
      (Set.univ ×ˢ Ici (0 : ℝ)) := by
  have hneighborhood : {w : Space × ℝ | w.2 < T} ∈ nhds z :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hzT
  filter_upwards [hneighborhood] with w hw
  apply propext
  constructor
  · rintro ⟨_, hnonneg, _⟩
    exact ⟨Set.mem_univ _, hnonneg⟩
  · rintro ⟨_, hnonneg⟩
    exact ⟨Set.mem_univ _, hnonneg, hw⟩

/-- Every shared cofinal atlas is already a global periodic solution on nonnegative time. -/
theorem cofinalPeriodicAtlas_toPeriodicSolution
    {nu : ℝ} {initial : InitialVelocity}
    (atlas : CofinalPeriodicAtlas nu initial) :
    PeriodicSolution nu initial (0 : VelocityField) atlas.velocity atlas.pressure where
  momentum x t ht := by
    let T : ℝ := t + 1
    have hT : 0 < T := by linarith
    have htT : t < T := by dsimp [T]; linarith
    have htOpen : t ∈ openTimeSlab T := ⟨ht, htT⟩
    have hmomentum := (atlas.onOpenSlab T hT).momentum x t htOpen
    rw [derivWithin_congr_set (openTimeSlab_eventuallyEq_Ici htT)] at hmomentum
    exact hmomentum
  incompressible x t ht := by
    let T : ℝ := t + 1
    have hT : 0 < T := by linarith
    have htT : t < T := by dsimp [T]; linarith
    exact (atlas.onOpenSlab T hT).incompressible x t ⟨ht, htT⟩
  initial x := by
    exact (atlas.onOpenSlab 1 zero_lt_one).initial x
  velocitySmooth := by
    intro z hz
    let T : ℝ := z.2 + 1
    have hznonneg : 0 ≤ z.2 := hz.2
    have hT : 0 < T := by dsimp [T]; linarith
    have hzT : z.2 < T := by dsimp [T]; linarith
    have hzOpen : z ∈ openSpaceTimeSlab T := ⟨Set.mem_univ _, hz.2, hzT⟩
    exact ((atlas.onOpenSlab T hT).velocitySmooth z hzOpen).congr_set
      (openSpaceTimeSlab_eventuallyEq_univ_prod_Ici hzT)
  pressureSmooth := by
    intro z hz
    let T : ℝ := z.2 + 1
    have hznonneg : 0 ≤ z.2 := hz.2
    have hT : 0 < T := by dsimp [T]; linarith
    have hzT : z.2 < T := by dsimp [T]; linarith
    have hzOpen : z ∈ openSpaceTimeSlab T := ⟨Set.mem_univ _, hz.2, hzT⟩
    exact ((atlas.onOpenSlab T hT).pressureSmooth z hzOpen).congr_set
      (openSpaceTimeSlab_eventuallyEq_univ_prod_Ici hzT)
  velocityPeriodic t ht := by
    let T : ℝ := t + 1
    have hT : 0 < T := by linarith
    have htT : t < T := by dsimp [T]; linarith
    exact (atlas.onOpenSlab T hT).velocityPeriodic t ⟨ht, htT⟩
  pressurePeriodic t ht := by
    let T : ℝ := t + 1
    have hT : 0 < T := by linarith
    have htT : t < T := by dsimp [T]; linarith
    exact (atlas.onOpenSlab T hT).pressurePeriodic t ⟨ht, htT⟩

/-- The `PeriodicGlobalizationLaw` field of the official finish line is discharged. -/
theorem periodicGlobalizationLaw : PeriodicGlobalizationLaw := by
  intro nu initial atlas
  exact cofinalPeriodicAtlas_toPeriodicSolution atlas

section Audit

#print axioms openTimeSlab_eventuallyEq_Ici
#print axioms openSpaceTimeSlab_eventuallyEq_univ_prod_Ici
#print axioms cofinalPeriodicAtlas_toPeriodicSolution
#print axioms periodicGlobalizationLaw

end Audit

end Soma.Holonics.Millennium.NavierStokesCofinalGlobalization
