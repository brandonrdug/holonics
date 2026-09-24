import ElementaryHolonics.Millennium.NavierStokesWeightedDuhamelMeasurability
import ElementaryHolonics.Millennium.NavierStokesWeightedPathSpace

/-!
# The linear heat path on the native restart carrier

**[proved-derived]** Strong continuity of each weighted heat orbit is now transported into the
complete path carrier `C([0,T], H³)`.  The returned path begins at the exact initial coefficient
population and is a contraction in the path supremum norm.  This is the linear half of the mild
restart map; it does not introduce a nonlinear fixed point or a PDE solution.
-/

noncomputable section

open Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedLinearPath

open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelMeasurability
open Soma.Holonics.Millennium.NavierStokesWeightedHeatSemigroup
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Componentwise same-order heat transport is contractive on the native vector carrier. -/
theorem norm_periodicVectorWeightedHeat_le
    (order : ℕ) (nu t : ℝ≥0)
    (state : PeriodicVectorWeightedSobolev order) :
    ‖periodicVectorWeightedHeat order nu t state‖ ≤ ‖state‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg state)]
  intro component
  exact (norm_periodicWeightedHeat_le order nu t (state component)).trans
    (norm_le_pi_norm state component)

/-- The same-order vector heat orbit is continuous in nonnegative elapsed time. -/
theorem continuous_periodicVectorWeightedHeat_orbit
    (order : ℕ) (nu : ℝ≥0)
    (state : PeriodicVectorWeightedSobolev order) :
    Continuous (fun tau : ℝ≥0 ↦ periodicVectorWeightedHeat order nu tau state) := by
  apply continuous_pi
  intro component
  exact continuous_periodicWeightedHeat_orbit order nu (state component)

/-- The exact linear heat path on a declared nonnegative time aperture. -/
def weightedLinearHeatPath
    (nu : ℝ≥0) {T : ℝ} (_hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) : WeightedH3Path T where
  toFun := fun t ↦ periodicVectorWeightedHeat 3 nu (Real.toNNReal t.1) initial
  continuous_toFun :=
    (continuous_periodicVectorWeightedHeat_orbit 3 nu initial).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)

/-- The linear path starts at exactly the initial native coefficient population. -/
@[simp]
theorem weightedLinearHeatPath_zero
    (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) :
    weightedLinearHeatPath nu hT initial ⟨0, ⟨le_rfl, hT⟩⟩ = initial := by
  funext component
  unfold weightedLinearHeatPath
  simp only [ContinuousMap.coe_mk, Real.toNNReal_zero]
  change periodicWeightedHeat 3 nu 0 (initial component) = initial component
  have hzero := congrArg (fun operator ↦ operator (initial component))
    (periodicWeightedHeat_zero_time 3 nu)
  simpa only [ContinuousLinearMap.id_apply] using hzero

/-- The complete linear heat path occupies no more than the norm of its initial face. -/
theorem norm_weightedLinearHeatPath_le
    (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) :
    ‖weightedLinearHeatPath nu hT initial‖ ≤ ‖initial‖ := by
  apply (ContinuousMap.norm_le (weightedLinearHeatPath nu hT initial)
    (norm_nonneg initial)).2
  intro t
  exact norm_periodicVectorWeightedHeat_le 3 nu (Real.toNNReal t.1) initial

section Audit

#print axioms continuous_periodicVectorWeightedHeat_orbit
#print axioms weightedLinearHeatPath_zero
#print axioms norm_weightedLinearHeatPath_le

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
