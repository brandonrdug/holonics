import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianTailDecay
import ElementaryHolonics.Millennium.NavierStokesFiniteFourierHeat

/-!
# Addressed spectral-clock transport outside a finite frequency cube

**[proved-derived; formal-checked]** Leaving the radius-`N` frequency cube forces one integer
coordinate to have magnitude at least `N+1`.  This module retains that escaped coordinate as an
addressed boundary-generator mode, compares the two modes through their spectral order, and then
uses only the zero/serial/order laws of a spectral clock action.

The conventional unit-torus circumference calibration and exponential chart occur only in the
separate realization proving that the standing heat multiplier satisfies this constraint object;
they are not identities of the clock or the exterior mode.  This is the spatial-frequency half of
the terminal service law.  It makes no assertion about the size or time integrability of the
nonlinear source transported by the clock action.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesHighFrequencyHeatDecay

open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The addressed boundary generator -/

/-- The first missing lattice occurrence in one addressed coordinate. -/
def exteriorBoundaryFrequency (radius : ℕ) (axis : Fin 3) : SpatialFrequency :=
  Pi.single axis (radius + 1 : ℤ)

@[simp]
theorem exteriorBoundaryFrequency_apply_same (radius : ℕ) (axis : Fin 3) :
    exteriorBoundaryFrequency radius axis axis = (radius + 1 : ℤ) := by
  simp [exteriorBoundaryFrequency]

/-- Its normalized lattice spectrum is exactly the squared boundary length. -/
theorem frequencySquared_exteriorBoundaryFrequency
    (radius : ℕ) (axis : Fin 3) :
    frequencySquared (exteriorBoundaryFrequency radius axis) =
      (radius + 1 : ℝ) ^ 2 := by
  fin_cases axis <;>
    simp [frequencySquared, exteriorBoundaryFrequency, Pi.single_apply]

/-- **[proved-derived; formal-checked]** An exterior cube mode has squared frequency at least the
square of the first missing integer radius. -/
theorem radius_add_one_sq_le_frequencySquared_of_not_mem_frequencyCube
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube radius) :
    (radius + 1 : ℝ) ^ 2 ≤ frequencySquared frequency := by
  obtain ⟨axis, haxis⟩ :=
    exists_coordinate_natAbs_gt_of_not_mem_frequencyCube radius hfrequency
  have haxis' : radius + 1 ≤ (frequency axis).natAbs := by omega
  have habs : (radius + 1 : ℝ) ≤ |(frequency axis : ℝ)| := by
    have hcast : (radius + 1 : ℝ) ≤ ((frequency axis).natAbs : ℝ) := by
      exact_mod_cast haxis'
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
  have hsquare : (radius + 1 : ℝ) ^ 2 ≤ (frequency axis : ℝ) ^ 2 := by
    have hsquareAbs := pow_le_pow_left₀ (by positivity) habs 2
    simpa only [sq_abs] using hsquareAbs
  have hterm : (frequency axis : ℝ) ^ 2 ≤ frequencySquared frequency := by
    unfold frequencySquared
    exact Finset.single_le_sum
      (fun other _hother ↦ sq_nonneg (frequency other : ℝ)) (Finset.mem_univ axis)
  exact hsquare.trans hterm

/-- **[proved-derived; formal-checked]** Every exterior occurrence spectrally dominates the
addressed boundary generator selected by one of its escaping coordinates. -/
theorem exists_boundaryGenerator_spectrum_le_of_not_mem_frequencyCube
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube radius) :
    ∃ axis : Fin 3,
      torusStokesEigenvalue (exteriorBoundaryFrequency radius axis) ≤
        torusStokesEigenvalue frequency := by
  obtain ⟨axis, haxis⟩ :=
    exists_coordinate_natAbs_gt_of_not_mem_frequencyCube radius hfrequency
  refine ⟨axis, ?_⟩
  unfold torusStokesEigenvalue
  rw [frequencySquared_exteriorBoundaryFrequency]
  exact mul_le_mul_of_nonneg_left
    (radius_add_one_sq_le_frequencySquared_of_not_mem_frequencyCube
      radius hfrequency)
    (sq_nonneg _)

/-! ## Holonic clock constraint and its standing heat realization -/

/-- A spectral clock is a nonnegative serial action whose transport decreases when the addressed
spectral cost increases.  Its laws, rather than a privileged closed-form coordinate, are the
clock object used by the exterior service passage. -/
structure SpectralClockAction where
  transport : ℝ → SpatialFrequency → ℝ
  transport_nonneg : ∀ elapsed frequency, 0 ≤ transport elapsed frequency
  zero : ∀ frequency, transport 0 frequency = 1
  serial : ∀ s t frequency,
    transport (s + t) frequency = transport s frequency * transport t frequency
  antitone_spectrum : ∀ {elapsed : ℝ}, 0 ≤ elapsed →
    ∀ {slower faster : SpatialFrequency},
      torusStokesEigenvalue slower ≤ torusStokesEigenvalue faster →
        transport elapsed faster ≤ transport elapsed slower

/-- The standing exact heat multiplier is one realization of the spectral-clock constraints.
The realization chart is deliberately separated from the constraint object above. -/
def heatSpectralClockAction (nu : ℝ) (hnu : 0 ≤ nu) : SpectralClockAction where
  transport elapsed frequency := heatStokesMultiplier nu elapsed frequency
  transport_nonneg elapsed frequency := by
    unfold heatStokesMultiplier
    exact (Real.exp_pos _).le
  zero := heatStokesMultiplier_zero_time nu
  serial := heatStokesMultiplier_add nu
  antitone_spectrum := by
    intro elapsed helapsed slower faster hspectrum
    unfold heatStokesMultiplier
    apply Real.exp_le_exp.mpr
    have hproduct : 0 ≤ nu * elapsed := mul_nonneg hnu helapsed
    nlinarith [mul_le_mul_of_nonneg_left hspectrum hproduct]

/-- **[proved-derived; formal-checked]** Exterior spectral incidence forces every lawful spectral
clock to transport the exterior mode no more strongly than one addressed boundary generator. -/
theorem exists_transport_le_boundaryGenerator
    (clock : SpectralClockAction) {elapsed : ℝ} (helapsed : 0 ≤ elapsed)
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube radius) :
    ∃ axis : Fin 3,
      clock.transport elapsed frequency ≤
        clock.transport elapsed (exteriorBoundaryFrequency radius axis) := by
  obtain ⟨axis, hspectrum⟩ :=
    exists_boundaryGenerator_spectrum_le_of_not_mem_frequencyCube radius hfrequency
  exact ⟨axis, clock.antitone_spectrum helapsed hspectrum⟩

/-- **[proved-derived; formal-checked]** The standing heat realization therefore returns the
same boundary-generator comparison without exposing a circumference or exponential coordinate. -/
theorem exists_heatTransport_le_boundaryGenerator
    {nu elapsed : ℝ} (hnu : 0 ≤ nu) (helapsed : 0 ≤ elapsed)
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube radius) :
    ∃ axis : Fin 3,
      heatStokesMultiplier nu elapsed frequency ≤
        heatStokesMultiplier nu elapsed (exteriorBoundaryFrequency radius axis) := by
  exact exists_transport_le_boundaryGenerator
    (heatSpectralClockAction nu hnu) helapsed radius hfrequency

section Audit

#print axioms radius_add_one_sq_le_frequencySquared_of_not_mem_frequencyCube
#print axioms frequencySquared_exteriorBoundaryFrequency
#print axioms exists_boundaryGenerator_spectrum_le_of_not_mem_frequencyCube
#print axioms heatSpectralClockAction
#print axioms exists_transport_le_boundaryGenerator
#print axioms exists_heatTransport_le_boundaryGenerator

end Audit

end Soma.Holonics.Millennium.NavierStokesHighFrequencyHeatDecay
