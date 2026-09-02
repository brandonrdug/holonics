import ElementaryHolonics.Millennium.NavierStokesModalGronwall

/-!
# The half-radius reach: every tail mode has a decaying cost

A mode `k` with sup-norm `m = |k|_∞` lies outside the cube of radius `2 · ⌊(m−1)/2⌋`, so the
shell-step cost can be taken at that half radius.  The cost at radius `r` is paid by the tail
masses beyond `r`, which decay as `r` grows by per-event irrelevance.  Consequently the cost of
a mode decays with the mode, which is what a sum over the tail needs and what a cost uniform in
`k` cannot supply.

The Stokes eigenvalue of a mode is at least `(2π)² |k|_∞²`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesHalfRadiusReach

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
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesModalGronwall

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-- The sup-norm of an integer frequency. -/
def frequencySup (k : SpatialFrequency) : ℕ :=
  Finset.univ.sup fun coordinate ↦ (k coordinate).natAbs

theorem mem_frequencyCube_iff_frequencySup_le (radius : ℕ) (k : SpatialFrequency) :
    k ∈ frequencyCube radius ↔ frequencySup k ≤ radius := by
  rw [mem_frequencyCube_iff, frequencySup, Finset.sup_le_iff]
  constructor
  · intro h coordinate _
    have := h coordinate
    omega
  · intro h coordinate
    have := h coordinate (Finset.mem_univ _)
    omega

/-- The half radius of a mode. -/
def halfRadius (k : SpatialFrequency) : ℕ := (frequencySup k - 1) / 2

theorem not_mem_frequencyCube_two_mul_halfRadius {k : SpatialFrequency}
    (hk : 1 ≤ frequencySup k) : k ∉ frequencyCube (2 * halfRadius k) := by
  rw [mem_frequencyCube_iff_frequencySup_le, halfRadius]
  omega

theorem frequencySup_sq_le_frequencySquared (k : SpatialFrequency) :
    ((frequencySup k : ℕ) : ℝ) ^ 2 ≤ frequencySquared k := by
  obtain ⟨coordinate, _, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3))
    Finset.univ_nonempty (fun coordinate ↦ (k coordinate).natAbs)
  have hcoordinate : ((frequencySup k : ℕ) : ℝ) ^ 2 = (k coordinate : ℝ) ^ 2 := by
    rw [frequencySup, hsup, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [hcoordinate]
  unfold frequencySquared
  exact Finset.single_le_sum (f := fun j : Fin 3 ↦ (k j : ℝ) ^ 2) (fun _ _ ↦ sq_nonneg _)
    (Finset.mem_univ coordinate)

theorem torusStokesEigenvalue_ge (k : SpatialFrequency) :
    (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ 2 ≤ torusStokesEigenvalue k := by
  unfold torusStokesEigenvalue
  exact mul_le_mul_of_nonneg_left (frequencySup_sq_le_frequencySquared k) (by positivity)

/-- The shell-step cost of a mode, taken at its own half radius. -/
def halfRadiusCost (t : Ioo 0 T) (k : SpatialFrequency) : ℝ :=
  feedBound solution t (halfRadius k)

/-- **The modal Riccati inequality at the half radius.**  For every nonzero mode the drive is paid
by the tail masses beyond the mode's own half radius. -/
theorem modalEnergy_riccati_halfRadius (hnu : 0 < nu) (t : Ioo 0 T) {k : SpatialFrequency}
    (hk : 1 ≤ frequencySup k) :
    ∃ D : ℝ, HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
      D ≤ -(nu * torusStokesEigenvalue k) * modalEnergy (velocity := velocity) k t.1 +
        3 ^ 5 / nu * halfRadiusCost solution t k ^ 2 :=
  modalEnergy_riccati_amgm solution hnu t (not_mem_frequencyCube_two_mul_halfRadius hk)

section Audit

#print axioms mem_frequencyCube_iff_frequencySup_le
#print axioms torusStokesEigenvalue_ge
#print axioms modalEnergy_riccati_halfRadius

end Audit

end Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
