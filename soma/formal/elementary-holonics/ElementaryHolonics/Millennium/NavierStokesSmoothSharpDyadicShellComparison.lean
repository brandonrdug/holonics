import ElementaryHolonics.Millennium.NavierStokesDyadicVorticityFluxReceiver

/-!
# Exact comparison of smooth dyadic Hodge bands and sharp shells

**[proved-derived; formal-checked]** The direct smooth Hodge multiplier at scale `j` has no
frequency population beyond the two consecutive sharp shells `j` and `j + 1`.  Conversely, the
scale-`0` multiplier is one on the first sharp shell, while on every later sharp shell the two
adjacent smooth multipliers add exactly to one.

These coefficient identities lift to exact finite Fourier-synthesis identities.  In particular,
an actual sharp vorticity shell is the sum of its two adjacent smooth-multiplier restrictions, and
the same identity applies to a finite localized nonlinear flux on a sharp output aperture.

**[open]** Restricting a complete smooth band back to one sharp shell is itself a sharp Fourier
projection.  This file proves no scale-uniform `L∞` norm bound for that operation.  Therefore it
does not replace the missing physical-kernel estimate, projected vorticity evolution, cofinal
nonlinear convolution identification, or terminal Carleson service law.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxReceiver
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-! ## Exact finite overlap -/

/-- The support cutoff of a dyadic low pass lies strictly below the next plateau cutoff. -/
theorem dyadicHodgeOuterCutoff_lt_nextInnerCutoff (scale : ℕ) :
    dyadicHodgeOuterCutoff scale < dyadicHodgeInnerCutoff (scale + 1) := by
  rw [dyadicHodgeOuterCutoff_eq]
  unfold dyadicHodgeInnerCutoff
  have hpositive : 0 < dyadicRadius (scale + 1) := by
    unfold dyadicRadius
    positivity
  omega

/-- A nonzero direct smooth multiplier pin belongs to exactly the two-shell aperture naturally
adjacent to its scale. -/
theorem mem_two_sharp_shells_of_dyadicHodgeBandWeight_ne_zero
    (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : dyadicHodgeBandWeight scale frequency ≠ 0) :
    frequency ∈ dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1) := by
  have hnotInner : frequency ∉ frequencyCube (dyadicHodgeInnerCutoff scale) := by
    intro hinner
    exact hfrequency (dyadicHodgeBandWeight_eq_zero_of_mem_inner scale hinner)
  have houter :
      frequency ∈ frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
    by_contra hnotOuter
    exact hfrequency
      (dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale hnotOuter)
  have houterLarge : frequency ∈ frequencyCube (dyadicRadius (scale + 2)) := by
    apply frequencyCube_mono (show dyadicHodgeOuterCutoff (scale + 1) ≤
      dyadicRadius (scale + 2) by
        rw [dyadicHodgeOuterCutoff_eq]
        simpa [Nat.add_assoc] using Nat.sub_le (dyadicRadius (scale + 2)) 1)
    exact houter
  rw [Finset.mem_union, mem_dyadicFrequencyShell_iff,
    mem_dyadicFrequencyShell_iff]
  by_cases hmiddle : frequency ∈ frequencyCube (dyadicRadius (scale + 1))
  · exact Or.inl ⟨hmiddle, by simpa [dyadicHodgeInnerCutoff] using hnotInner⟩
  · exact Or.inr ⟨by simpa [Nat.add_assoc] using houterLarge, hmiddle⟩

/-- Equivalently, every frequency outside the two adjacent sharp shells has zero smooth-band
weight. -/
theorem dyadicHodgeBandWeight_eq_zero_of_not_mem_two_sharp_shells
    (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉
      dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)) :
    dyadicHodgeBandWeight scale frequency = 0 := by
  by_contra hnonzero
  exact hfrequency
    (mem_two_sharp_shells_of_dyadicHodgeBandWeight_ne_zero scale hnonzero)

/-- **Exact finite overlap.** Synthesizing a complete smooth dyadic band on its native support
cube is identical to synthesizing it on the union of the two adjacent sharp shells.  Frequencies
added or removed by the aperture change have zero coefficient before synthesis. -/
theorem finiteFourierSynthesis_dyadicHodgeBand_eq_twoSharpShells
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coefficient : SpatialFrequency → E) (scale : ℕ) :
    finiteFourierSynthesis
        (fun frequency ↦
          (dyadicHodgeBandWeight scale frequency : ℂ) • coefficient frequency)
        (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) =
      finiteFourierSynthesis
        (fun frequency ↦
          (dyadicHodgeBandWeight scale frequency : ℂ) • coefficient frequency)
        (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)) := by
  let outer := frequencyCube (dyadicRadius (scale + 2))
  have hnative :
      frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) ⊆ outer := by
    apply frequencyCube_mono
    rw [dyadicHodgeOuterCutoff_eq]
    simpa [outer, Nat.add_assoc] using Nat.sub_le (dyadicRadius (scale + 2)) 1
  have hshells :
      dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1) ⊆ outer := by
    intro frequency hfrequency
    rw [Finset.mem_union] at hfrequency
    rcases hfrequency with hfirst | hsecond
    · rw [mem_dyadicFrequencyShell_iff] at hfirst
      exact frequencyCube_mono
        (by
          unfold dyadicRadius
          exact Nat.pow_le_pow_right (by norm_num) (by omega)) hfirst.1
    · rw [mem_dyadicFrequencyShell_iff] at hsecond
      simpa [outer, Nat.add_assoc] using hsecond.1
  have hnativeOuter :
      finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight scale frequency : ℂ) • coefficient frequency)
          (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) =
        finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight scale frequency : ℂ) • coefficient frequency)
          outer := by
    apply finiteFourierSynthesis_eq_of_subset_of_eq_zero _ hnative
    intro frequency _houter hnotNative
    rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale hnotNative]
    simp
  have hshellsOuter :
      finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight scale frequency : ℂ) • coefficient frequency)
          (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)) =
        finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight scale frequency : ℂ) • coefficient frequency)
          outer := by
    apply finiteFourierSynthesis_eq_of_subset_of_eq_zero _ hshells
    intro frequency _houter hnotShells
    rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_two_sharp_shells
      scale hnotShells]
    simp
  exact hnativeOuter.trans hshellsOuter.symm

/-! ## Partition of unity on every sharp shell -/

/-- The first direct smooth band is exactly one on the first sharp shell. -/
theorem dyadicHodgeBandWeight_eq_one_of_mem_first_sharp_shell
    {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ dyadicFrequencyShell 0) :
    dyadicHodgeBandWeight 0 frequency = 1 := by
  rw [mem_dyadicFrequencyShell_iff] at hfrequency
  have hnext : frequency ∈
      frequencyCube (dyadicHodgeParameter (0 + 1) + 1) := by
    simpa [dyadicHodgeParameter_add_one] using hfrequency.1
  have hbaseOuter : frequency ∉
      frequencyCube (dyadicHodgeOuterCutoff 0) := by
    simpa [dyadicHodgeOuterCutoff_eq, dyadicRadius] using hfrequency.2
  unfold dyadicHodgeBandWeight
  rw [tensorValleePoussinWeight_eq_one _ hnext,
    tensorValleePoussinWeight_eq_zero_of_not_mem_outer
      (dyadicHodgeParameter 0) (by
        simpa [dyadicHodgeOuterCutoff] using hbaseOuter)]
  norm_num

/-- On every noninitial sharp shell, the two adjacent smooth multiplier faces add to one. -/
theorem adjacent_dyadicHodgeBandWeights_add_eq_one_of_mem_sharp_shell
    (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ dyadicFrequencyShell (scale + 1)) :
    dyadicHodgeBandWeight scale frequency +
        dyadicHodgeBandWeight (scale + 1) frequency = 1 := by
  rw [mem_dyadicFrequencyShell_iff] at hfrequency
  have hnext : frequency ∈
      frequencyCube (dyadicHodgeParameter (scale + 2) + 1) := by
    simpa [dyadicHodgeParameter_add_one, Nat.add_assoc] using hfrequency.1
  have hbaseOuter : frequency ∉
      frequencyCube (dyadicHodgeOuterCutoff scale) := by
    intro hbase
    have hbaseInner :
        frequency ∈ frequencyCube (dyadicRadius (scale + 1)) := by
      simpa [dyadicHodgeInnerCutoff] using
        (frequencyCube_mono
          (Nat.le_of_lt (dyadicHodgeOuterCutoff_lt_nextInnerCutoff scale)) hbase)
    exact hfrequency.2 hbaseInner
  unfold dyadicHodgeBandWeight
  rw [tensorValleePoussinWeight_eq_one _ hnext,
    tensorValleePoussinWeight_eq_zero_of_not_mem_outer
      (dyadicHodgeParameter scale) (by
        simpa [dyadicHodgeOuterCutoff] using hbaseOuter)]
  ring

/-! ## Exact finite-synthesis comparison -/

/-- The first sharp shell is its scale-zero smooth-multiplier restriction, for every coefficient
population. -/
theorem finiteFourierSynthesis_firstSharpShell_eq_firstSmoothRestriction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coefficient : SpatialFrequency → E) :
    finiteFourierSynthesis coefficient (dyadicFrequencyShell 0) =
      finiteFourierSynthesis
        (fun frequency ↦
          (dyadicHodgeBandWeight 0 frequency : ℂ) • coefficient frequency)
        (dyadicFrequencyShell 0) := by
  ext q
  change (∑ frequency ∈ dyadicFrequencyShell 0,
      UnitAddTorus.mFourier frequency q • coefficient frequency) =
    ∑ frequency ∈ dyadicFrequencyShell 0,
      UnitAddTorus.mFourier frequency q •
        ((dyadicHodgeBandWeight 0 frequency : ℂ) • coefficient frequency)
  apply Finset.sum_congr rfl
  intro frequency hfrequency
  rw [dyadicHodgeBandWeight_eq_one_of_mem_first_sharp_shell hfrequency]
  simp

/-- Every later sharp shell is exactly the sum of its two adjacent smooth-multiplier
restrictions. -/
theorem finiteFourierSynthesis_sharpShell_succ_eq_adjacentSmoothRestrictions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coefficient : SpatialFrequency → E) (scale : ℕ) :
    finiteFourierSynthesis coefficient (dyadicFrequencyShell (scale + 1)) =
      finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight scale frequency : ℂ) • coefficient frequency)
          (dyadicFrequencyShell (scale + 1)) +
        finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight (scale + 1) frequency : ℂ) •
              coefficient frequency)
          (dyadicFrequencyShell (scale + 1)) := by
  ext q
  unfold finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro frequency hfrequency
  rw [← smul_add, ← add_smul]
  have hpartition :
      (dyadicHodgeBandWeight scale frequency : ℂ) +
          (dyadicHodgeBandWeight (scale + 1) frequency : ℂ) = 1 := by
    exact_mod_cast
      adjacent_dyadicHodgeBandWeights_add_eq_one_of_mem_sharp_shell
        scale hfrequency
  rw [hpartition]
  simp

/-! ## Actual-vorticity and finite-flux specializations -/

/-- The actual first sharp vorticity shell is exactly the first smooth restriction. -/
theorem openPeriodicVorticityFirstSharpShell_eq_firstSmoothRestriction
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    openPeriodicVorticityBandProjector solution t (dyadicFrequencyShell 0) =
      finiteFourierSynthesis
        (fun frequency ↦
          (dyadicHodgeBandWeight 0 frequency : ℂ) •
            openPeriodicVorticityFourierMode solution t frequency)
        (dyadicFrequencyShell 0) :=
  finiteFourierSynthesis_firstSharpShell_eq_firstSmoothRestriction _

/-- The actual later sharp vorticity shell is exactly the sum of its two adjacent smooth
restrictions. -/
theorem openPeriodicVorticitySharpShell_succ_eq_adjacentSmoothRestrictions
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicVorticityBandProjector solution t
        (dyadicFrequencyShell (scale + 1)) =
      finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight scale frequency : ℂ) •
              openPeriodicVorticityFourierMode solution t frequency)
          (dyadicFrequencyShell (scale + 1)) +
        finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight (scale + 1) frequency : ℂ) •
              openPeriodicVorticityFourierMode solution t frequency)
          (dyadicFrequencyShell (scale + 1)) :=
  finiteFourierSynthesis_sharpShell_succ_eq_adjacentSmoothRestrictions _ scale

/-- Consequently the phase-local sharp-shell receiver is bounded by the two adjacent restricted
smooth-band norms.  No scale-dependent Fourier projection constant is hidden here. -/
theorem openPeriodicVorticityDyadicShellSpatialSup_succ_le_adjacentSmoothRestrictions
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicVorticityDyadicShellSpatialSup solution t (scale + 1) ≤
      ‖finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight scale frequency : ℂ) •
              openPeriodicVorticityFourierMode solution t frequency)
          (dyadicFrequencyShell (scale + 1))‖ +
        ‖finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight (scale + 1) frequency : ℂ) •
              openPeriodicVorticityFourierMode solution t frequency)
          (dyadicFrequencyShell (scale + 1))‖ := by
  unfold openPeriodicVorticityDyadicShellSpatialSup
  rw [openPeriodicVorticitySharpShell_succ_eq_adjacentSmoothRestrictions]
  exact norm_add_le _ _

/-- The same exact sharp/smooth partition applies to a finite localized nonlinear flux on any
later sharp output aperture. -/
theorem finiteOpenVorticityFluxBand_sharpShell_succ_eq_adjacentSmoothRestrictions
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (fluxScale : ℕ)
    (advectingAperture : Finset SpatialFrequency) (shellScale : ℕ) :
    finiteOpenVorticityFluxBand solution t fluxScale advectingAperture
        (dyadicFrequencyShell (shellScale + 1)) =
      finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight shellScale frequency : ℂ) •
              finiteOpenVorticityFluxCoefficient solution t fluxScale
                advectingAperture frequency)
          (dyadicFrequencyShell (shellScale + 1)) +
        finiteFourierSynthesis
          (fun frequency ↦
            (dyadicHodgeBandWeight (shellScale + 1) frequency : ℂ) •
              finiteOpenVorticityFluxCoefficient solution t fluxScale
                advectingAperture frequency)
          (dyadicFrequencyShell (shellScale + 1)) :=
  finiteFourierSynthesis_sharpShell_succ_eq_adjacentSmoothRestrictions _ shellScale

section Audit

#print axioms mem_two_sharp_shells_of_dyadicHodgeBandWeight_ne_zero
#print axioms finiteFourierSynthesis_dyadicHodgeBand_eq_twoSharpShells
#print axioms adjacent_dyadicHodgeBandWeights_add_eq_one_of_mem_sharp_shell
#print axioms finiteFourierSynthesis_sharpShell_succ_eq_adjacentSmoothRestrictions
#print axioms openPeriodicVorticityDyadicShellSpatialSup_succ_le_adjacentSmoothRestrictions
#print axioms finiteOpenVorticityFluxBand_sharpShell_succ_eq_adjacentSmoothRestrictions

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
