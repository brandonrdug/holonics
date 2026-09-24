import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeScaleChain

/-!
# Positivity of the direct dyadic Hodge multiplier

**[proved-derived; formal-checked]**  At the dyadic parameters used by the Hodge scale chain,
the plateau of the next de la Vallee--Poussin low pass contains the complete support of the
previous low pass.  Consequently their direct difference is not merely bounded in absolute
value: it lies in the unit interval at every lattice frequency.

This is a multiplier fact.  It supplies the positivity required to read the one-copy
phase-sensitive storage as an energy carrier, but asserts no spacetime or terminal estimate.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity

open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- The previous dyadic low-pass support is contained in the next dyadic plateau. -/
theorem dyadicHodgeOuterCube_subset_next_parameterPlateau
    (scale : ℕ) :
    frequencyCube (dyadicHodgeOuterCutoff scale) ⊆
      frequencyCube (dyadicHodgeParameter (scale + 1) + 1) := by
  apply frequencyCube_mono
  rw [dyadicHodgeParameter_add_one, dyadicHodgeOuterCutoff_eq]
  exact Nat.sub_le _ _

/-- The next dyadic low-pass multiplier equals one on every frequency carried by the previous
low-pass support. -/
theorem tensorValleePoussinWeight_next_eq_one_of_mem_previous_outer
    (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (dyadicHodgeOuterCutoff scale)) :
    tensorValleePoussinWeight (dyadicHodgeParameter (scale + 1)) frequency = 1 := by
  exact tensorValleePoussinWeight_eq_one _
    (dyadicHodgeOuterCube_subset_next_parameterPlateau scale hfrequency)

/-- **Positive direct scale passage.**  Every direct dyadic Hodge band weight lies in `[0,1]`.
The proof retains both support faces: on the earlier support the next multiplier is exactly one;
off that support the earlier multiplier is exactly zero. -/
theorem dyadicHodgeBandWeight_mem_unitInterval
    (scale : ℕ) (frequency : SpatialFrequency) :
    0 ≤ dyadicHodgeBandWeight scale frequency ∧
      dyadicHodgeBandWeight scale frequency ≤ 1 := by
  obtain ⟨hnextNonneg, hnextOne⟩ :=
    tensorValleePoussinWeight_mem_unitInterval
      (dyadicHodgeParameter (scale + 1)) frequency
  obtain ⟨hpreviousNonneg, hpreviousOne⟩ :=
    tensorValleePoussinWeight_mem_unitInterval
      (dyadicHodgeParameter scale) frequency
  by_cases hfrequency :
      frequency ∈ frequencyCube (dyadicHodgeOuterCutoff scale)
  · have hnextExact :=
      tensorValleePoussinWeight_next_eq_one_of_mem_previous_outer
        scale hfrequency
    unfold dyadicHodgeBandWeight
    rw [hnextExact]
    constructor <;> linarith
  · have hpreviousExact :
        tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency = 0 := by
      exact tensorValleePoussinWeight_eq_zero_of_not_mem_outer
        (dyadicHodgeParameter scale) (by
          simpa only [dyadicHodgeOuterCutoff] using hfrequency)
    unfold dyadicHodgeBandWeight
    rw [hpreviousExact, sub_zero]
    exact ⟨hnextNonneg, hnextOne⟩

theorem dyadicHodgeBandWeight_nonneg
    (scale : ℕ) (frequency : SpatialFrequency) :
    0 ≤ dyadicHodgeBandWeight scale frequency :=
  (dyadicHodgeBandWeight_mem_unitInterval scale frequency).1

theorem dyadicHodgeBandWeight_le_one
    (scale : ℕ) (frequency : SpatialFrequency) :
    dyadicHodgeBandWeight scale frequency ≤ 1 :=
  (dyadicHodgeBandWeight_mem_unitInterval scale frequency).2

section Audit

#print axioms dyadicHodgeOuterCube_subset_next_parameterPlateau
#print axioms tensorValleePoussinWeight_next_eq_one_of_mem_previous_outer
#print axioms dyadicHodgeBandWeight_mem_unitInterval

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity
