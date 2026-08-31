import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeKernelVariation
import ElementaryHolonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison

/-!
# Terminal packing of phase-bearing smooth dyadic vorticity bands

**[proved-derived; formal-checked]** The same direct dyadic multiplier used by the localized
commutator is applied here to actual vorticity before Hodge ascent.  Its low passes telescope from
the existing phase-bearing low face through the smooth dyadic bands.  The complete complex
vorticity slice is that finite word plus an explicit reconstruction fibre, and the fibre vanishes
along the cofinal dyadic scale.

**[definition; formal-checked]** The terminal smooth-band population is an `ENNReal` sum after
each signed band reaches its spatial supremum receiver, followed by a time `lintegral`.  Tonelli
therefore retains divergence as `∞`.

**[proved-derived; formal-checked, conditional]** Finiteness of this robust population, together
with the already unconditional low-face integrability theorem, makes the literal critical
vorticity rate interval-integrable.  Universal finiteness would therefore yield the existing
`CriticalVorticityTerminalControl` and literal official problem receiver.

**[open]** No theorem in this file asserts that the smooth terminal packing is finite.  That is
the remaining scale-critical PDE estimate.
-/

noncomputable section

open MeasureTheory Real Set Filter
open scoped BigOperators ENNReal Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesCriticalOfficialPassage
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability
open Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-! ## Direct smooth vorticity low passes and bands -/

/-- The direct smooth dyadic low pass applied to actual vorticity before Hodge ascent. -/
def openPeriodicSmoothDyadicVorticityLowPass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (fun frequency ↦
      (tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency : ℂ) •
        openPeriodicVorticityFourierMode solution t frequency)
    (frequencyCube (dyadicHodgeOuterCutoff scale))

/-- The phase-bearing direct smooth dyadic vorticity band. -/
def openPeriodicSmoothDyadicVorticityBand
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (fun frequency ↦
      (dyadicHodgeBandWeight scale frequency : ℂ) •
        openPeriodicVorticityFourierMode solution t frequency)
    (frequencyCube (dyadicHodgeOuterCutoff (scale + 1)))

/-- The smaller low pass may be mounted in the next smooth-band aperture without changing its
value. -/
theorem openPeriodicSmoothDyadicVorticityLowPass_eq_nextAperture
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicSmoothDyadicVorticityLowPass solution t scale =
      finiteFourierSynthesis
        (fun frequency ↦
          (tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency : ℂ) •
            openPeriodicVorticityFourierMode solution t frequency)
        (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) := by
  unfold openPeriodicSmoothDyadicVorticityLowPass
  apply finiteFourierSynthesis_eq_of_subset_of_eq_zero
  · apply frequencyCube_mono
    exact dyadicHodgeOuterCutoff_mono scale
  · intro frequency _houter hinner
    rw [tensorValleePoussinWeight_eq_zero_of_not_mem_outer
      (dyadicHodgeParameter scale) (by
        simpa [dyadicHodgeOuterCutoff] using hinner)]
    simp

/-- One direct smooth scale passage. -/
theorem openPeriodicSmoothDyadicVorticityLowPass_succ
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicSmoothDyadicVorticityLowPass solution t (scale + 1) =
      openPeriodicSmoothDyadicVorticityLowPass solution t scale +
        openPeriodicSmoothDyadicVorticityBand solution t scale := by
  have hcurrent := openPeriodicSmoothDyadicVorticityLowPass_eq_nextAperture
    solution t scale
  rw [hcurrent]
  ext q component
  unfold openPeriodicSmoothDyadicVorticityLowPass
    openPeriodicSmoothDyadicVorticityBand finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  unfold dyadicHodgeBandWeight
  push_cast
  ring

/-- At scale zero the smooth low pass is exactly the already-owned phase-bearing low cube. -/
theorem openPeriodicSmoothDyadicVorticityLowPass_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    openPeriodicSmoothDyadicVorticityLowPass solution t 0 =
      openPeriodicVorticityBandProjector solution t lowFrequencyModes := by
  apply ContinuousMap.ext
  intro q
  change (∑ frequency ∈ frequencyCube (dyadicHodgeOuterCutoff 0),
      UnitAddTorus.mFourier frequency q •
        ((tensorValleePoussinWeight (dyadicHodgeParameter 0) frequency : ℂ) •
          openPeriodicVorticityFourierMode solution t frequency)) =
    ∑ frequency ∈ lowFrequencyModes,
      UnitAddTorus.mFourier frequency q •
        openPeriodicVorticityFourierMode solution t frequency
  have haperture : frequencyCube (dyadicHodgeOuterCutoff 0) = lowFrequencyModes := by
    simp [dyadicHodgeOuterCutoff_eq, dyadicRadius, lowFrequencyModes]
  rw [haperture]
  apply Finset.sum_congr rfl
  intro frequency hfrequency
  have hplateau : frequency ∈ frequencyCube (dyadicHodgeParameter 0 + 1) := by
    simpa [dyadicHodgeParameter, dyadicRadius, lowFrequencyModes] using hfrequency
  rw [tensorValleePoussinWeight_eq_one _ hplateau]
  simp

/-- The complete finite smooth word is the retained low face plus every crossed smooth band. -/
theorem openPeriodicSmoothDyadicVorticityLowPass_eq_low_add_bands
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    openPeriodicSmoothDyadicVorticityLowPass solution t depth =
      openPeriodicVorticityBandProjector solution t lowFrequencyModes +
        ∑ scale ∈ Finset.range depth,
          openPeriodicSmoothDyadicVorticityBand solution t scale := by
  induction depth with
  | zero => simp [openPeriodicSmoothDyadicVorticityLowPass_zero]
  | succ depth ih =>
      rw [openPeriodicSmoothDyadicVorticityLowPass_succ, ih,
        Finset.sum_range_succ]
      abel

/-! ## Cofinal reconstruction fibre -/

/-- The transition population between the sharp plateau cube and the outer support of one smooth
low pass. -/
def openPeriodicSmoothDyadicVorticityTransition
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (fun frequency ↦
      (tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency : ℂ) •
        openPeriodicVorticityFourierMode solution t frequency)
    (frequencyCube (dyadicHodgeOuterCutoff scale) \
      frequencyCube (dyadicRadius scale))

private theorem dyadicRadius_le_dyadicHodgeOuterCutoff (scale : ℕ) :
    dyadicRadius scale ≤ dyadicHodgeOuterCutoff scale := by
  rw [dyadicHodgeOuterCutoff_eq]
  unfold dyadicRadius
  rw [pow_succ]
  have hpositive : 1 ≤ 2 ^ scale := Nat.one_le_pow scale 2 (by norm_num)
  omega

/-- A smooth low pass is exactly its sharp plateau cube plus its retained transition population. -/
theorem openPeriodicSmoothDyadicVorticityLowPass_eq_cube_add_transition
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicSmoothDyadicVorticityLowPass solution t scale =
      openPeriodicVorticityBandProjector solution t
          (frequencyCube (dyadicRadius scale)) +
        openPeriodicSmoothDyadicVorticityTransition solution t scale := by
  have hsubset : frequencyCube (dyadicRadius scale) ⊆
      frequencyCube (dyadicHodgeOuterCutoff scale) :=
    frequencyCube_mono (dyadicRadius_le_dyadicHodgeOuterCutoff scale)
  rw [openPeriodicSmoothDyadicVorticityLowPass,
    finiteFourierSynthesis_eq_add_sdiff _ hsubset]
  congr 1
  · apply ContinuousMap.ext
    intro q
    change (∑ frequency ∈ frequencyCube (dyadicRadius scale),
        UnitAddTorus.mFourier frequency q •
          ((tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency : ℂ) •
            openPeriodicVorticityFourierMode solution t frequency)) =
      ∑ frequency ∈ frequencyCube (dyadicRadius scale),
        UnitAddTorus.mFourier frequency q •
          openPeriodicVorticityFourierMode solution t frequency
    apply Finset.sum_congr rfl
    intro frequency hfrequency
    have hplateau : frequency ∈
        frequencyCube (dyadicHodgeParameter scale + 1) := by
      simpa [dyadicHodgeParameter_add_one] using hfrequency
    rw [tensorValleePoussinWeight_eq_one _ hplateau]
    simp

/-- The exact unresolved smooth complement after a finite scale word. -/
def openPeriodicSmoothDyadicVorticityReconstructionFiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : C(SpatialTorus, ComplexVector) :=
  complexTorusVorticitySlice solution t -
    openPeriodicSmoothDyadicVorticityLowPass solution t depth

/-- Low face, ordered smooth word, and reconstruction fibre recover the complete complex
vorticity slice exactly. -/
theorem complexTorusVorticitySlice_eq_low_add_smoothBands_add_fiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    complexTorusVorticitySlice solution t =
      openPeriodicVorticityBandProjector solution t lowFrequencyModes +
        (∑ scale ∈ Finset.range depth,
          openPeriodicSmoothDyadicVorticityBand solution t scale) +
        openPeriodicSmoothDyadicVorticityReconstructionFiber solution t depth := by
  rw [← openPeriodicSmoothDyadicVorticityLowPass_eq_low_add_bands
    solution t depth]
  unfold openPeriodicSmoothDyadicVorticityReconstructionFiber
  abel

/-- Norm of the complete smooth reconstruction fibre. -/
def openPeriodicSmoothDyadicVorticityReconstructionFiberNorm
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : ℝ :=
  ‖openPeriodicSmoothDyadicVorticityReconstructionFiber solution t depth‖

theorem openPeriodicSmoothDyadicVorticityReconstructionFiberNorm_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    0 ≤ openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth :=
  norm_nonneg _

private theorem smoothTransitionAperture_subset_shell (scale : ℕ) :
    frequencyCube (dyadicHodgeOuterCutoff scale) \
        frequencyCube (dyadicRadius scale) ⊆
      dyadicFrequencyShell scale := by
  intro frequency hfrequency
  rw [Finset.mem_sdiff] at hfrequency
  rw [mem_dyadicFrequencyShell_iff]
  refine ⟨?_, hfrequency.2⟩
  apply frequencyCube_mono
    (show dyadicHodgeOuterCutoff scale ≤ dyadicRadius (scale + 1) by
      rw [dyadicHodgeOuterCutoff_eq]
      omega)
  exact hfrequency.1

/-- The transition population is paid by one already-summable sharp-shell coefficient mass. -/
theorem norm_openPeriodicSmoothDyadicVorticityTransition_le_shellCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    ‖openPeriodicSmoothDyadicVorticityTransition solution t scale‖ ≤
      openPeriodicVorticityDyadicShellCoefficientMass solution t scale := by
  apply (ContinuousMap.norm_le _
    (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution t scale)).2
  intro q
  calc
    ‖openPeriodicSmoothDyadicVorticityTransition solution t scale q‖ ≤
        ∑ frequency ∈
            (frequencyCube (dyadicHodgeOuterCutoff scale) \
              frequencyCube (dyadicRadius scale)),
          ‖(tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency : ℂ) •
            openPeriodicVorticityFourierMode solution t frequency‖ := by
      exact norm_finiteFourierSynthesis_le_sum_norm _ _ q
    _ ≤ ∑ frequency ∈
            (frequencyCube (dyadicHodgeOuterCutoff scale) \
              frequencyCube (dyadicRadius scale)),
          complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      obtain ⟨hweightNonneg, hweightOne⟩ :=
        tensorValleePoussinWeight_mem_unitInterval
          (dyadicHodgeParameter scale) frequency
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hweightNonneg]
      exact (mul_le_of_le_one_left (norm_nonneg _) hweightOne).trans
        (norm_complexVector_le_complexVectorL1 _)
    _ ≤ ∑ frequency ∈ dyadicFrequencyShell scale,
          complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (smoothTransitionAperture_subset_shell scale)
      intro frequency _hshell _htransition
      exact complexVectorL1_nonneg _
    _ = openPeriodicVorticityDyadicShellCoefficientMass solution t scale := rfl

/-- The smooth fibre is bounded by the already-vanishing sharp fibre plus one transition shell. -/
theorem openPeriodicSmoothDyadicVorticityReconstructionFiberNorm_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth ≤
      openPeriodicVorticityDyadicReconstructionFiber solution t depth +
        openPeriodicVorticityDyadicShellCoefficientMass solution t depth := by
  unfold openPeriodicSmoothDyadicVorticityReconstructionFiberNorm
    openPeriodicSmoothDyadicVorticityReconstructionFiber
  rw [openPeriodicSmoothDyadicVorticityLowPass_eq_cube_add_transition]
  rw [complexTorusVorticitySlice_eq_band_add_frequencyRemainder solution t
    (frequencyCube (dyadicRadius depth))]
  have hrebase :
      openPeriodicVorticityBandProjector solution t
            (frequencyCube (dyadicRadius depth)) +
          openPeriodicVorticityFrequencyRemainder solution t
            (frequencyCube (dyadicRadius depth)) -
        (openPeriodicVorticityBandProjector solution t
            (frequencyCube (dyadicRadius depth)) +
          openPeriodicSmoothDyadicVorticityTransition solution t depth) =
      openPeriodicVorticityFrequencyRemainder solution t
          (frequencyCube (dyadicRadius depth)) -
        openPeriodicSmoothDyadicVorticityTransition solution t depth := by
    abel
  rw [hrebase]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rfl
  · exact norm_openPeriodicSmoothDyadicVorticityTransition_le_shellCoefficientMass
      solution t depth

/-- The complete smooth reconstruction fibre disappears at the cofinal dyadic scale. -/
theorem tendsto_openPeriodicSmoothDyadicVorticityReconstructionFiberNorm_atTop
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    Tendsto (openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t)
      atTop (nhds 0) := by
  have hsharp := tendsto_openPeriodicVorticityDyadicReconstructionFiber_atTop solution t
  have hmass : Tendsto
      (openPeriodicVorticityDyadicShellCoefficientMass solution t) atTop (nhds 0) :=
    (summable_openPeriodicVorticityDyadicShellCoefficientMass solution t).tendsto_atTop_zero
  apply squeeze_zero
  · exact openPeriodicSmoothDyadicVorticityReconstructionFiberNorm_nonneg solution t
  · exact openPeriodicSmoothDyadicVorticityReconstructionFiberNorm_le solution t
  · simpa using hsharp.add hmass

/-! ## Smooth-band spatial population -/

/-- Spatial supremum of one phase-bearing smooth vorticity band. -/
def openPeriodicSmoothDyadicVorticityBandSpatialSup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : ℝ :=
  ‖openPeriodicSmoothDyadicVorticityBand solution t scale‖

theorem openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    0 ≤ openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale :=
  norm_nonneg _

/-- One direct smooth band is paid pointwise by its finite mode count and the actual vorticity
second moment.  This is the unconditional finite-scale Bernstein/enstrophy payment; no terminal
packing premise enters. -/
theorem openPeriodicSmoothDyadicVorticityBandSpatialSup_le_sqrt_card_mul_sqrt_secondMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale ≤
      Real.sqrt
          ((frequencyCube (dyadicHodgeOuterCutoff (scale + 1))).card : ℝ) *
        Real.sqrt
          (∫ x in unitCube, ‖vorticityField velocity x t.1‖ ^ 2) := by
  let modes : Finset SpatialFrequency :=
    frequencyCube (dyadicHodgeOuterCutoff (scale + 1))
  let coeff : SpatialFrequency → ComplexVector := fun frequency ↦
    (dyadicHodgeBandWeight scale frequency : ℂ) •
      openPeriodicVorticityFourierMode solution t frequency
  have hweighted :
      (∑ frequency ∈ modes, ‖coeff frequency‖ ^ 2) ≤
        ∑ frequency ∈ modes,
          ‖openPeriodicVorticityFourierMode solution t frequency‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro frequency _hfrequency
    dsimp [coeff]
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
    have hweight := abs_dyadicHodgeBandWeight_le_one scale frequency
    have hweightSq : |dyadicHodgeBandWeight scale frequency| ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hweight 2
    simpa using mul_le_mul_of_nonneg_right hweightSq
      (sq_nonneg ‖openPeriodicVorticityFourierMode solution t frequency‖)
  have hcoeff :
      (∑ frequency ∈ modes, ‖coeff frequency‖ ^ 2) ≤
        ∫ x in unitCube, ‖vorticityField velocity x t.1‖ ^ 2 := by
    rw [integral_norm_vorticityField_sq_eq_two_mul_periodicEnstrophy]
    exact hweighted.trans
      (sum_sq_openPeriodicVorticityFourierMode_le_two_enstrophy solution t modes)
  unfold openPeriodicSmoothDyadicVorticityBandSpatialSup
    openPeriodicSmoothDyadicVorticityBand
  apply (ContinuousMap.norm_le _
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
  intro q
  change ‖finiteFourierSynthesis coeff modes q‖ ≤ _
  refine (norm_finiteFourierSynthesis_le_sqrt_card_mul_sqrt_sum_sq
    coeff modes q).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcoeff)
    (Real.sqrt_nonneg _)

private theorem adjacentDyadicFrequencyShell_disjoint (scale : ℕ) :
    Disjoint (dyadicFrequencyShell scale) (dyadicFrequencyShell (scale + 1)) := by
  rw [Finset.disjoint_left]
  intro frequency hfirst hsecond
  rw [mem_dyadicFrequencyShell_iff] at hfirst hsecond
  exact hsecond.2 hfirst.1

/-- One smooth-band norm is paid by the two sharp coefficient shells in its exact support. -/
theorem openPeriodicSmoothDyadicVorticityBandSpatialSup_le_adjacentShellCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale ≤
      openPeriodicVorticityDyadicShellCoefficientMass solution t scale +
        openPeriodicVorticityDyadicShellCoefficientMass solution t (scale + 1) := by
  unfold openPeriodicSmoothDyadicVorticityBandSpatialSup
    openPeriodicSmoothDyadicVorticityBand
  rw [finiteFourierSynthesis_dyadicHodgeBand_eq_twoSharpShells]
  apply (ContinuousMap.norm_le _ (add_nonneg
    (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution t scale)
    (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution t (scale + 1)))).2
  intro q
  calc
    ‖finiteFourierSynthesis
        (fun frequency ↦ (dyadicHodgeBandWeight scale frequency : ℂ) •
          openPeriodicVorticityFourierMode solution t frequency)
        (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)) q‖ ≤
      ∑ frequency ∈
          (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
        ‖(dyadicHodgeBandWeight scale frequency : ℂ) •
          openPeriodicVorticityFourierMode solution t frequency‖ :=
      norm_finiteFourierSynthesis_le_sum_norm _ _ q
    _ ≤ ∑ frequency ∈
          (dyadicFrequencyShell scale ∪ dyadicFrequencyShell (scale + 1)),
        complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (abs_dyadicHodgeBandWeight_le_one scale frequency)).trans
        (norm_complexVector_le_complexVectorL1 _)
    _ = openPeriodicVorticityDyadicShellCoefficientMass solution t scale +
        openPeriodicVorticityDyadicShellCoefficientMass solution t (scale + 1) := by
      rw [Finset.sum_union (adjacentDyadicFrequencyShell_disjoint scale)]
      rfl

/-- Smooth-band spatial suprema are summable on every strict-interior slice. -/
theorem summable_openPeriodicSmoothDyadicVorticityBandSpatialSup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    Summable (openPeriodicSmoothDyadicVorticityBandSpatialSup solution t) := by
  have hmass := summable_openPeriodicVorticityDyadicShellCoefficientMass solution t
  have hmajorant : Summable (fun scale : ℕ ↦
      openPeriodicVorticityDyadicShellCoefficientMass solution t scale +
        openPeriodicVorticityDyadicShellCoefficientMass solution t (scale + 1)) :=
    hmass.add ((summable_nat_add_iff 1).2 hmass)
  exact Summable.of_nonneg_of_le
    (openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg solution t)
    (openPeriodicSmoothDyadicVorticityBandSpatialSup_le_adjacentShellCoefficientMass
      solution t) hmajorant

/-- Finite smooth words are bounded by the low face and the crossed smooth-band norms. -/
theorem norm_openPeriodicSmoothDyadicVorticityLowPass_le_low_add_bands
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    ‖openPeriodicSmoothDyadicVorticityLowPass solution t depth‖ ≤
      openPeriodicVorticityLowSpatialSup solution t +
        ∑ scale ∈ Finset.range depth,
          openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale := by
  rw [openPeriodicSmoothDyadicVorticityLowPass_eq_low_add_bands]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact norm_sum_le _ _

/-- Finite smooth reconstruction, including its retained fibre, controls the literal critical
vorticity rate at one depth. -/
theorem criticalVorticityRate_le_finiteSmoothWord_add_fiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    criticalVorticityRate solution t.1 ≤
      Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          (∑ scale ∈ Finset.range depth,
            openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale) +
          openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth) := by
  rw [criticalVorticityRate_eq solution t.2]
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg 3)
    (add_nonneg
      (add_nonneg (openPeriodicVorticityLowSpatialSup_nonneg solution t)
        (Finset.sum_nonneg fun scale _ ↦
          openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg solution t scale))
      (openPeriodicSmoothDyadicVorticityReconstructionFiberNorm_nonneg
        solution t depth)))).2
  intro q
  have hreal := norm_space_le_sqrt_three_mul_norm_complexifySpace
    (torusVorticityEvolution solution t q)
  have hsplit := DFunLike.congr_fun
    (show complexTorusVorticitySlice solution t =
        openPeriodicSmoothDyadicVorticityLowPass solution t depth +
          openPeriodicSmoothDyadicVorticityReconstructionFiber solution t depth by
      unfold openPeriodicSmoothDyadicVorticityReconstructionFiber
      abel) q
  have hcomplex : ‖complexTorusVorticitySlice solution t q‖ ≤
      ‖openPeriodicSmoothDyadicVorticityLowPass solution t depth‖ +
        openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (openPeriodicSmoothDyadicVorticityLowPass solution t depth).norm_coe_le_norm q
    · exact (openPeriodicSmoothDyadicVorticityReconstructionFiber
        solution t depth).norm_coe_le_norm q
  have hword := norm_openPeriodicSmoothDyadicVorticityLowPass_le_low_add_bands
    solution t depth
  calc
    ‖torusVorticityEvolution solution t q‖ ≤
        Real.sqrt 3 * ‖complexTorusVorticitySlice solution t q‖ := hreal
    _ ≤ Real.sqrt 3 *
        (‖openPeriodicSmoothDyadicVorticityLowPass solution t depth‖ +
          openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth) :=
      mul_le_mul_of_nonneg_left hcomplex (Real.sqrt_nonneg 3)
    _ ≤ Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          (∑ scale ∈ Finset.range depth,
            openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale) +
          openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 3)
      exact add_le_add hword le_rfl

/-- Low plus the complete smooth-band population controls the literal critical vorticity rate on
every strict-interior slice. -/
theorem criticalVorticityRate_le_low_add_tsum_smoothBands
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    criticalVorticityRate solution t.1 ≤
      Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          ∑' scale : ℕ,
            openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale) := by
  have hsummable := summable_openPeriodicSmoothDyadicVorticityBandSpatialSup solution t
  have hpartial : ∀ depth : ℕ,
      criticalVorticityRate solution t.1 ≤
        Real.sqrt 3 *
          (openPeriodicVorticityLowSpatialSup solution t +
            (∑ scale ∈ Finset.range depth,
              openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale) +
            openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth) :=
    criticalVorticityRate_le_finiteSmoothWord_add_fiber solution t
  have hlimit : Tendsto (fun depth : ℕ ↦
      Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          (∑ scale ∈ Finset.range depth,
            openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale) +
          openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth))
      atTop (nhds (Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          ∑' scale : ℕ,
            openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale))) := by
    have hbands := hsummable.hasSum.tendsto_sum_nat
    have hfiber :=
      tendsto_openPeriodicSmoothDyadicVorticityReconstructionFiberNorm_atTop solution t
    have hbody : Tendsto (fun depth : ℕ ↦
        openPeriodicVorticityLowSpatialSup solution t +
            (∑ scale ∈ Finset.range depth,
              openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale) +
          openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth)
        atTop (nhds
          (openPeriodicVorticityLowSpatialSup solution t +
            ∑' scale : ℕ,
              openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale)) := by
      simpa only [add_zero] using
        ((tendsto_const_nhds.add hbands).add hfiber)
    simpa only [add_zero] using tendsto_const_nhds.mul hbody
  exact ge_of_tendsto hlimit (Filter.Eventually.of_forall hpartial)

/-! ## Robust terminal smooth packing -/

/-- Real-time presentation of one smooth-band spatial supremum, extended by zero off the open
lifespan. -/
def openPeriodicSmoothDyadicVorticityBandSpatialSupRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (scale : ℕ) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0 : ℝ) T then
    openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale
  else 0

@[simp]
theorem openPeriodicSmoothDyadicVorticityBandSpatialSupRate_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (scale : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t =
      openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale := by
  simp [openPeriodicSmoothDyadicVorticityBandSpatialSupRate, ht]

theorem continuous_openPeriodicSmoothDyadicVorticityLowPass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (scale : ℕ) :
    Continuous (fun t : Ioo (0 : ℝ) T ↦
      openPeriodicSmoothDyadicVorticityLowPass solution t scale) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  unfold openPeriodicSmoothDyadicVorticityLowPass finiteFourierSynthesis
  exact continuous_finsetSum _ fun frequency _hfrequency ↦
    ((UnitAddTorus.mFourier frequency).continuous.comp continuous_snd).smul
      ((show Continuous (fun _ : (Ioo (0 : ℝ) T) × SpatialTorus ↦
          (tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency : ℂ)) from
        continuous_const).smul
        ((continuous_openPeriodicVorticityFourierMode solution frequency).comp continuous_fst))

theorem continuous_openPeriodicSmoothDyadicVorticityBandSpatialSup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (scale : ℕ) :
    Continuous (openPeriodicSmoothDyadicVorticityBandSpatialSup solution · scale) := by
  unfold openPeriodicSmoothDyadicVorticityBandSpatialSup
    openPeriodicSmoothDyadicVorticityBand
  have hband : Continuous (fun t : Ioo (0 : ℝ) T ↦
      openPeriodicSmoothDyadicVorticityLowPass solution t (scale + 1) -
        openPeriodicSmoothDyadicVorticityLowPass solution t scale) :=
    (continuous_openPeriodicSmoothDyadicVorticityLowPass solution (scale + 1)).sub
      (continuous_openPeriodicSmoothDyadicVorticityLowPass solution scale)
  apply continuous_norm.comp
  apply hband.congr
  intro t
  rw [openPeriodicSmoothDyadicVorticityLowPass_succ]
  abel

theorem continuousOn_openPeriodicSmoothDyadicVorticityBandSpatialSupRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (scale : ℕ) :
    ContinuousOn (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale)
      (Ioo (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply (continuous_openPeriodicSmoothDyadicVorticityBandSpatialSup solution scale).congr
  intro t
  simp [openPeriodicSmoothDyadicVorticityBandSpatialSupRate, t.2]

/-! ## Unconditional finite-scale enstrophy payment -/

/-- Every fixed smooth phase-bearing band is globally time-integrable on the complete open
lifespan.  The payment is the ordinary energy/enstrophy budget, with the finite Bernstein mode
count retained explicitly at this scale. -/
theorem openPeriodicSolutionOn_smoothDyadicVorticityBandSpatialSupRate_integrableOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (scale : ℕ) :
    IntegrableOn
      (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale)
      (Ioo (0 : ℝ) T) volume := by
  let moment : ℝ → ℝ := fun t ↦
    ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2
  let modeFactor : ℝ :=
    Real.sqrt
      ((frequencyCube (dyadicHodgeOuterCutoff (scale + 1))).card : ℝ)
  have hmoment : IntegrableOn moment (Ioo (0 : ℝ) T) volume :=
    (openPeriodicSolutionOn_vorticitySecondMoment_integrableOn_and_integral_le
      solution hnu).1
  have hmajorant : IntegrableOn
      (fun t ↦ modeFactor * (1 + moment t))
      (Ioo (0 : ℝ) T) volume :=
    ((integrableOn_const (s := Ioo (0 : ℝ) T) (C := (1 : ℝ))
      (measure_Ioo_lt_top.ne)).add hmoment).const_mul modeFactor
  apply Integrable.mono' hmajorant
    ((continuousOn_openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale)
      |>.aestronglyMeasurable measurableSet_Ioo)
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards with t
  intro ht
  have hmomentNonneg : 0 ≤ moment t := integral_nonneg fun x ↦ sq_nonneg _
  have hsqrt : Real.sqrt (moment t) ≤ 1 + moment t := by
    nlinarith [Real.sq_sqrt hmomentNonneg,
      Real.sqrt_nonneg (moment t), sq_nonneg (Real.sqrt (moment t) - 1)]
  rw [Real.norm_of_nonneg (by
    rw [openPeriodicSmoothDyadicVorticityBandSpatialSupRate_eq solution scale ht]
    exact openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg
      solution ⟨t, ht⟩ scale)]
  calc
    openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t ≤
        modeFactor * Real.sqrt (moment t) := by
      rw [openPeriodicSmoothDyadicVorticityBandSpatialSupRate_eq solution scale ht]
      exact
        openPeriodicSmoothDyadicVorticityBandSpatialSup_le_sqrt_card_mul_sqrt_secondMoment
          solution ⟨t, ht⟩ scale
    _ ≤ modeFactor * (1 + moment t) :=
      mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)

/-- Quantitative form of the fixed-band payment.  The mode-count loss is exactly the elementary
finite-dimensional Bernstein loss; the remaining factor is paid by lifespan plus the global
unforced energy/enstrophy budget. -/
theorem openPeriodicSolutionOn_integral_smoothDyadicVorticityBandSpatialSupRate_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (scale : ℕ) :
    (∫ t in Ioo (0 : ℝ) T,
        openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t) ≤
      Real.sqrt
          ((frequencyCube (dyadicHodgeOuterCutoff (scale + 1))).card : ℝ) *
        (T + 2 * (periodicKineticEnergy velocity 0 / nu)) := by
  let moment : ℝ → ℝ := fun t ↦
    ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2
  let modeFactor : ℝ :=
    Real.sqrt
      ((frequencyCube (dyadicHodgeOuterCutoff (scale + 1))).card : ℝ)
  have hmoment :=
    openPeriodicSolutionOn_vorticitySecondMoment_integrableOn_and_integral_le
      solution hnu
  have hconstant : IntegrableOn (fun _t : ℝ ↦ (1 : ℝ))
      (Ioo (0 : ℝ) T) volume :=
    integrableOn_const (s := Ioo (0 : ℝ) T) (C := (1 : ℝ))
      (measure_Ioo_lt_top.ne)
  have hmajorant : IntegrableOn
      (fun t ↦ modeFactor * (1 + moment t))
      (Ioo (0 : ℝ) T) volume :=
    (hconstant.add hmoment.1).const_mul modeFactor
  have hrate :=
    openPeriodicSolutionOn_smoothDyadicVorticityBandSpatialSupRate_integrableOn
      solution hnu scale
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) T,
      openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t ≤
        modeFactor * (1 + moment t) := by
    intro t ht
    have hmomentNonneg : 0 ≤ moment t := integral_nonneg fun x ↦ sq_nonneg _
    have hsqrt : Real.sqrt (moment t) ≤ 1 + moment t := by
      nlinarith [Real.sq_sqrt hmomentNonneg,
        Real.sqrt_nonneg (moment t), sq_nonneg (Real.sqrt (moment t) - 1)]
    calc
      openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t ≤
          modeFactor * Real.sqrt (moment t) := by
        rw [openPeriodicSmoothDyadicVorticityBandSpatialSupRate_eq solution scale ht]
        exact
          openPeriodicSmoothDyadicVorticityBandSpatialSup_le_sqrt_card_mul_sqrt_secondMoment
            solution ⟨t, ht⟩ scale
      _ ≤ modeFactor * (1 + moment t) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
  calc
    (∫ t in Ioo (0 : ℝ) T,
        openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t) ≤
        ∫ t in Ioo (0 : ℝ) T, modeFactor * (1 + moment t) :=
      setIntegral_mono_on hrate hmajorant measurableSet_Ioo hpoint
    _ = modeFactor *
        ((∫ _t in Ioo (0 : ℝ) T, (1 : ℝ)) +
          ∫ t in Ioo (0 : ℝ) T, moment t) := by
      rw [integral_const_mul, integral_add hconstant hmoment.1]
    _ = modeFactor *
        (T + ∫ t in Ioo (0 : ℝ) T, moment t) := by
      rw [setIntegral_one_eq_measureReal]
      simp [solution.terminal_pos.le]
    _ ≤ modeFactor *
        (T + 2 * (periodicKineticEnergy velocity 0 / nu)) :=
      mul_le_mul_of_nonneg_left (by
        simpa [moment, add_comm] using add_le_add_left hmoment.2 T)
          (Real.sqrt_nonneg _)

/-- Every finite smooth-band prefix is globally time-integrable.  Thus the existing unconditional
energy law pays any prescribed finite sequence of pantographic scale swings; only a bound uniform
under cofinal passage is absent. -/
theorem openPeriodicSolutionOn_finiteSmoothDyadicVorticityBandPrefix_integrableOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (depth : ℕ) :
    IntegrableOn
      (fun t : ℝ ↦ ∑ scale ∈ Finset.range depth,
        openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t)
      (Ioo (0 : ℝ) T) volume :=
  integrable_finsetSum (Finset.range depth) fun scale _hscale ↦
    openPeriodicSolutionOn_smoothDyadicVorticityBandSpatialSupRate_integrableOn
      solution hnu scale

/-- Quantitative finite-prefix payment.  The bound displays why the present energy owner cannot
be passed directly to the cofinal scale: it pays the sum of the finite Bernstein mode-count
factors, with no decaying scale envelope. -/
theorem openPeriodicSolutionOn_integral_finiteSmoothDyadicVorticityBandPrefix_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (depth : ℕ) :
    (∫ t in Ioo (0 : ℝ) T, ∑ scale ∈ Finset.range depth,
        openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t) ≤
      (∑ scale ∈ Finset.range depth,
          Real.sqrt
            ((frequencyCube (dyadicHodgeOuterCutoff (scale + 1))).card : ℝ)) *
        (T + 2 * (periodicKineticEnergy velocity 0 / nu)) := by
  let budget : ℝ := T + 2 * (periodicKineticEnergy velocity 0 / nu)
  have hband : ∀ scale : ℕ,
      Integrable
        (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale)
        (volume.restrict (Ioo (0 : ℝ) T)) := fun scale ↦
    openPeriodicSolutionOn_smoothDyadicVorticityBandSpatialSupRate_integrableOn
      solution hnu scale
  calc
    (∫ t in Ioo (0 : ℝ) T, ∑ scale ∈ Finset.range depth,
        openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t) =
        ∑ scale ∈ Finset.range depth,
          ∫ t in Ioo (0 : ℝ) T,
            openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t := by
      rw [integral_finsetSum (Finset.range depth) fun scale _hscale ↦ hband scale]
    _ ≤ ∑ scale ∈ Finset.range depth,
        Real.sqrt
            ((frequencyCube (dyadicHodgeOuterCutoff (scale + 1))).card : ℝ) *
          budget := by
      apply Finset.sum_le_sum
      intro scale _hscale
      exact openPeriodicSolutionOn_integral_smoothDyadicVorticityBandSpatialSupRate_le
        solution hnu scale
    _ = (∑ scale ∈ Finset.range depth,
          Real.sqrt
            ((frequencyCube (dyadicHodgeOuterCutoff (scale + 1))).card : ℝ)) *
        budget := by
      rw [Finset.sum_mul]

/-- The nonnegative extended-real smooth-band density. -/
def openPeriodicVorticityTerminalSmoothDyadicDensity
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : ℝ) : ℝ≥0∞ :=
  ∑' scale : ℕ,
    ENNReal.ofReal
      (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t)

theorem aemeasurable_openPeriodicVorticityTerminalSmoothDyadicDensity
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    AEMeasurable (openPeriodicVorticityTerminalSmoothDyadicDensity solution)
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  unfold openPeriodicVorticityTerminalSmoothDyadicDensity
  apply AEMeasurable.tsum
  intro scale
  exact ((continuousOn_openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale)
    |>.aestronglyMeasurable measurableSet_Ioo).aemeasurable.ennreal_ofReal

/-- Robust terminal spacetime packing of the actual smooth dyadic vorticity bands. -/
def openPeriodicVorticityTerminalSmoothDyadicPacking
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) T,
    openPeriodicVorticityTerminalSmoothDyadicDensity solution t ∂volume

/-- Tonelli exposes the exact individual smooth-band payments. -/
theorem openPeriodicVorticityTerminalSmoothDyadicPacking_eq_tsum_lintegral
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    openPeriodicVorticityTerminalSmoothDyadicPacking solution =
      ∑' scale : ℕ, ∫⁻ t in Ioo (0 : ℝ) T,
        ENNReal.ofReal
          (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale t) ∂volume := by
  unfold openPeriodicVorticityTerminalSmoothDyadicPacking
    openPeriodicVorticityTerminalSmoothDyadicDensity
  rw [lintegral_tsum]
  intro scale
  exact ((continuousOn_openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale)
    |>.aestronglyMeasurable measurableSet_Ioo).aemeasurable.ennreal_ofReal

/-- The exact open PDE property: finiteness of the robust smooth terminal packing. -/
structure OpenPeriodicTerminalSmoothDyadicPackingReceipt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) : Prop where
  packing_lt_top : openPeriodicVorticityTerminalSmoothDyadicPacking solution < ∞

/-- On every admitted time slice the density's real value is the actual summable smooth-band
population. -/
theorem openPeriodicVorticityTerminalSmoothDyadicDensity_toReal_eq_tsum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (openPeriodicVorticityTerminalSmoothDyadicDensity solution t).toReal =
      ∑' scale : ℕ,
        openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale := by
  have hsummable :=
    summable_openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩
  have hnonneg : ∀ scale : ℕ,
      0 ≤ openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale :=
    openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg solution ⟨t, ht⟩
  have hofReal := ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable
  have hsumNonneg : 0 ≤ ∑' scale : ℕ,
      openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale :=
    tsum_nonneg hnonneg
  calc
    (openPeriodicVorticityTerminalSmoothDyadicDensity solution t).toReal =
        (ENNReal.ofReal (∑' scale : ℕ,
          openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale)).toReal := by
      congr 1
      simpa [openPeriodicVorticityTerminalSmoothDyadicDensity,
        openPeriodicSmoothDyadicVorticityBandSpatialSupRate, ht] using hofReal.symm
    _ = ∑' scale : ℕ,
        openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale :=
      ENNReal.toReal_ofReal hsumNonneg

theorem openPeriodicVorticityTerminalSmoothDyadicDensity_toReal_integrableOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (receipt : OpenPeriodicTerminalSmoothDyadicPackingReceipt solution) :
    IntegrableOn
      (fun t : ℝ ↦
        (openPeriodicVorticityTerminalSmoothDyadicDensity solution t).toReal)
      (Ioo (0 : ℝ) T) volume := by
  apply integrable_toReal_of_lintegral_ne_top
    (aemeasurable_openPeriodicVorticityTerminalSmoothDyadicDensity solution)
  exact receipt.packing_lt_top.ne

/-! ## Literal critical and official passages -/

/-- A finite smooth terminal packing and positive viscosity make the literal critical vorticity
rate interval-integrable. -/
theorem intervalIntegrable_criticalVorticityRate_of_terminalSmoothDyadicPacking
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu)
    (receipt : OpenPeriodicTerminalSmoothDyadicPackingReceipt solution) :
    IntervalIntegrable (criticalVorticityRate solution) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le solution.terminal_pos.le]
  have hlow := openPeriodicSolutionOn_lowSpatialSupRate_integrableOn solution hnu
  have hbands :=
    openPeriodicVorticityTerminalSmoothDyadicDensity_toReal_integrableOn solution receipt
  have hmodel : IntegrableOn (fun t : ℝ ↦ Real.sqrt 3 *
      (openPeriodicVorticityLowSpatialSupRate solution t +
        (openPeriodicVorticityTerminalSmoothDyadicDensity solution t).toReal))
      (Ioo (0 : ℝ) T) volume :=
    (hlow.add hbands).const_mul (Real.sqrt 3)
  apply Integrable.mono' hmodel
    (criticalVorticityRate_measurable solution).aestronglyMeasurable.restrict
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards with t
  intro ht
  rw [Real.norm_of_nonneg (criticalVorticityRate_nonneg solution t)]
  calc
    criticalVorticityRate solution t ≤
        Real.sqrt 3 *
          (openPeriodicVorticityLowSpatialSup solution ⟨t, ht⟩ +
            ∑' scale : ℕ,
              openPeriodicSmoothDyadicVorticityBandSpatialSup solution ⟨t, ht⟩ scale) :=
      criticalVorticityRate_le_low_add_tsum_smoothBands solution ⟨t, ht⟩
    _ = Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSupRate solution t +
          (openPeriodicVorticityTerminalSmoothDyadicDensity solution t).toReal) := by
      rw [openPeriodicVorticityLowSpatialSupRate_eq solution ht,
        openPeriodicVorticityTerminalSmoothDyadicDensity_toReal_eq_tsum solution ht]

/-- Universal finiteness of the smooth terminal packing discharges the literal scale-critical
terminal-control receiver. -/
theorem criticalVorticityTerminalControl_of_terminalSmoothDyadicPacking
    (packing : ∀ {T nu : ℝ} {initial : InitialVelocity}
      {velocity : VelocityField} {pressure : PressureField},
      0 < nu →
      InitialVelocityConditionPeriodic initial →
      (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
        OpenPeriodicTerminalSmoothDyadicPackingReceipt solution) :
    CriticalVorticityTerminalControl := by
  intro T nu initial velocity pressure hnu hinitial solution
  exact intervalIntegrable_criticalVorticityRate_of_terminalSmoothDyadicPacking
    solution hnu (packing hnu hinitial solution)

/-- The same universal smooth-packing theorem reaches the repository's literal official problem
proposition through the existing critical official passage. -/
theorem officialProblem_of_terminalSmoothDyadicPacking
    (packing : ∀ {T nu : ℝ} {initial : InitialVelocity}
      {velocity : VelocityField} {pressure : PressureField},
      0 < nu →
      InitialVelocityConditionPeriodic initial →
      (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
        OpenPeriodicTerminalSmoothDyadicPackingReceipt solution) :
    TheOfficialNavierStokesProblem :=
  officialProblem_of_criticalVorticityTerminalControl
    (criticalVorticityTerminalControl_of_terminalSmoothDyadicPacking packing)

section Audit

#print axioms openPeriodicSmoothDyadicVorticityLowPass_eq_low_add_bands
#print axioms complexTorusVorticitySlice_eq_low_add_smoothBands_add_fiber
#print axioms tendsto_openPeriodicSmoothDyadicVorticityReconstructionFiberNorm_atTop
#print axioms summable_openPeriodicSmoothDyadicVorticityBandSpatialSup
#print axioms openPeriodicSmoothDyadicVorticityBandSpatialSup_le_sqrt_card_mul_sqrt_secondMoment
#print axioms openPeriodicSolutionOn_smoothDyadicVorticityBandSpatialSupRate_integrableOn
#print axioms openPeriodicSolutionOn_integral_smoothDyadicVorticityBandSpatialSupRate_le
#print axioms openPeriodicSolutionOn_finiteSmoothDyadicVorticityBandPrefix_integrableOn
#print axioms openPeriodicSolutionOn_integral_finiteSmoothDyadicVorticityBandPrefix_le
#print axioms criticalVorticityRate_le_low_add_tsum_smoothBands
#print axioms openPeriodicVorticityTerminalSmoothDyadicPacking_eq_tsum_lintegral
#print axioms intervalIntegrable_criticalVorticityRate_of_terminalSmoothDyadicPacking
#print axioms criticalVorticityTerminalControl_of_terminalSmoothDyadicPacking
#print axioms officialProblem_of_terminalSmoothDyadicPacking

end Audit

end Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking
