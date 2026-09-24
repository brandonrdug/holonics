import ElementaryHolonics.Millennium.NavierStokesCriticalOfficialPassage
import ElementaryHolonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-!
# Phase-local dyadic vorticity population and the critical terminal receiver

**[proved-derived]** This file reconstructs the actual vorticity of an admitted periodic
Navier--Stokes solution from one retained low face and its signed dyadic Fourier shells.  The
shell receiver is the spatial supremum of the signed synthesis, rather than the sum of absolute
Fourier coefficients.  Exact finite telescoping retains every phase cancellation inside a shell;
the complementary Fourier fibre vanishes cofinally.

Consequently the genuine critical vorticity rate is bounded by the `B^0_{infinity,1}`-style
population consisting of the low face plus the sum of shell spatial suprema.  Integrability of
that actual-solution population implies the literal `CriticalVorticityTerminalControl` receiver.

**[open]** The remaining PDE obligation is to prove the time-integrability of this phase-local
population uniformly up to the terminal face from the unforced Navier--Stokes equations.  The
present result proves the nontrivial reconstruction inequality and does not assume the critical
vorticity rate itself.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesCriticalOfficialPassage
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-! ## The actual signed shell population -/

/-- The retained low-frequency face of one actual vorticity slice, measured only after its
signed Fourier synthesis has reached the spatial receiver. -/
def openPeriodicVorticityLowSpatialSup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  ‖openPeriodicVorticityBandProjector solution t lowFrequencyModes‖

/-- The phase-local spatial supremum of one actual signed dyadic vorticity shell.  Cancellation
inside the shell occurs before the norm is taken. -/
def openPeriodicVorticityDyadicShellSpatialSup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (level : ℕ) : ℝ :=
  ‖openPeriodicVorticityBandProjector solution t (dyadicFrequencyShell level)‖

theorem openPeriodicVorticityLowSpatialSup_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    0 ≤ openPeriodicVorticityLowSpatialSup solution t :=
  norm_nonneg _

theorem openPeriodicVorticityDyadicShellSpatialSup_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (level : ℕ) :
    0 ≤ openPeriodicVorticityDyadicShellSpatialSup solution t level :=
  norm_nonneg _

/-- Absolute coefficient mass of one dyadic shell.  This is used only as an interior-slice
summability majorant; the phase-local receiver itself still takes the norm after signed spatial
synthesis. -/
def openPeriodicVorticityDyadicShellCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (level : ℕ) : ℝ :=
  ∑ frequency ∈ dyadicFrequencyShell level,
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency)

theorem openPeriodicVorticityDyadicShellCoefficientMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (level : ℕ) :
    0 ≤ openPeriodicVorticityDyadicShellCoefficientMass solution t level := by
  exact Finset.sum_nonneg fun frequency _ ↦ complexVectorL1_nonneg _

/-- Delaying the norm until after signed synthesis can only improve on the shell's absolute
coefficient population. -/
theorem openPeriodicVorticityDyadicShellSpatialSup_le_coefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (level : ℕ) :
    openPeriodicVorticityDyadicShellSpatialSup solution t level ≤
      openPeriodicVorticityDyadicShellCoefficientMass solution t level := by
  unfold openPeriodicVorticityDyadicShellSpatialSup
    openPeriodicVorticityDyadicShellCoefficientMass
  apply (ContinuousMap.norm_le _
    (Finset.sum_nonneg fun frequency _ ↦ complexVectorL1_nonneg _)).mpr
  intro q
  calc
    ‖openPeriodicVorticityBandProjector solution t
        (dyadicFrequencyShell level) q‖ ≤
      ∑ frequency ∈ dyadicFrequencyShell level,
        ‖openPeriodicVorticityFourierMode solution t frequency‖ :=
      norm_openPeriodicVorticityBandProjector_le_sum_norm
        solution t (dyadicFrequencyShell level) q
    _ ≤ ∑ frequency ∈ dyadicFrequencyShell level,
        complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
      apply Finset.sum_le_sum
      intro frequency _hfrequency
      exact norm_complexVector_le_complexVectorL1 _

/-- The low cube together with the first `depth` dyadic shells is exactly the addressed dyadic
cube, now read through any real coefficient mass. -/
private theorem low_add_partialDyadicShellMass_eq_cube
    (mass : SpatialFrequency → ℝ) (depth : ℕ) :
    (∑ frequency ∈ lowFrequencyModes, mass frequency) +
        (∑ level ∈ Finset.range depth,
          ∑ frequency ∈ dyadicFrequencyShell level, mass frequency) =
      ∑ frequency ∈ frequencyCube (dyadicRadius depth), mass frequency := by
  induction depth with
  | zero =>
      simp [dyadicRadius, lowFrequencyModes]
  | succ depth ih =>
      have hsubset :
          frequencyCube (dyadicRadius depth) ⊆
            frequencyCube (dyadicRadius (depth + 1)) :=
        frequencyCube_mono
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ depth))
      have hsplit := Finset.sum_sdiff (f := mass) hsubset
      calc
        (∑ frequency ∈ lowFrequencyModes, mass frequency) +
            (∑ level ∈ Finset.range (depth + 1),
              ∑ frequency ∈ dyadicFrequencyShell level, mass frequency) =
          ((∑ frequency ∈ lowFrequencyModes, mass frequency) +
              (∑ level ∈ Finset.range depth,
                ∑ frequency ∈ dyadicFrequencyShell level, mass frequency)) +
            ∑ frequency ∈ dyadicFrequencyShell depth, mass frequency := by
              rw [Finset.sum_range_succ]
              ring
        _ = (∑ frequency ∈ frequencyCube (dyadicRadius depth), mass frequency) +
            ∑ frequency ∈ dyadicFrequencyShell depth, mass frequency := by rw [ih]
        _ = ∑ frequency ∈ frequencyCube (dyadicRadius (depth + 1)),
            mass frequency := by
          simpa only [dyadicFrequencyShell, add_comm] using hsplit

/-- Interior smoothness already makes the absolute dyadic-shell masses summable.  Thus spatial
shell summability is not part of the terminal obstruction. -/
theorem summable_openPeriodicVorticityDyadicShellCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    Summable (openPeriodicVorticityDyadicShellCoefficientMass solution t) := by
  let mass : SpatialFrequency → ℝ := fun frequency ↦
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency)
  have hmass : Summable mass :=
    summable_complexVectorL1_openPeriodicVorticityFourierMode solution t
  apply summable_of_sum_range_le
    (fun level ↦ openPeriodicVorticityDyadicShellCoefficientMass_nonneg
      solution t level)
  intro depth
  calc
    (∑ level ∈ Finset.range depth,
        openPeriodicVorticityDyadicShellCoefficientMass solution t level) ≤
      (∑ frequency ∈ lowFrequencyModes, mass frequency) +
        (∑ level ∈ Finset.range depth,
          ∑ frequency ∈ dyadicFrequencyShell level, mass frequency) := by
      unfold openPeriodicVorticityDyadicShellCoefficientMass mass
      exact le_add_of_nonneg_left
        (Finset.sum_nonneg fun frequency _ ↦ complexVectorL1_nonneg _)
    _ = ∑ frequency ∈ frequencyCube (dyadicRadius depth), mass frequency :=
      low_add_partialDyadicShellMass_eq_cube mass depth
    _ ≤ ∑' frequency : SpatialFrequency, mass frequency :=
      hmass.sum_le_tsum _ (fun frequency _ ↦ complexVectorL1_nonneg _)

/-- Every strict-interior actual vorticity slice has summable signed-shell spatial suprema. -/
theorem summable_openPeriodicVorticityDyadicShellSpatialSup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    Summable (openPeriodicVorticityDyadicShellSpatialSup solution t) :=
  Summable.of_nonneg_of_le
    (openPeriodicVorticityDyadicShellSpatialSup_nonneg solution t)
    (openPeriodicVorticityDyadicShellSpatialSup_le_coefficientMass solution t)
    (summable_openPeriodicVorticityDyadicShellCoefficientMass solution t)

/-! ## Exact finite telescoping and the retained reconstruction fibre -/

/-- One dyadic enlargement is exactly the previous cube plus the newly crossed signed shell. -/
theorem openPeriodicVorticityDyadicCube_succ
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (level : ℕ) :
    openPeriodicVorticityBandProjector solution t
        (frequencyCube (dyadicRadius (level + 1))) =
      openPeriodicVorticityBandProjector solution t
          (frequencyCube (dyadicRadius level)) +
        openPeriodicVorticityBandProjector solution t
          (dyadicFrequencyShell level) := by
  exact finiteFourierSynthesis_eq_add_sdiff
    (openPeriodicVorticityFourierMode solution t)
    (frequencyCube_mono (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ level)))

/-- The complete finite dyadic cube is the low face plus every crossed shell, with exact phase
and frequency lineage retained. -/
theorem openPeriodicVorticityDyadicCube_eq_low_add_shells
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    openPeriodicVorticityBandProjector solution t
        (frequencyCube (dyadicRadius depth)) =
      openPeriodicVorticityBandProjector solution t lowFrequencyModes +
        (∑ level ∈ Finset.range depth,
          openPeriodicVorticityBandProjector solution t
            (dyadicFrequencyShell level)) := by
  induction depth with
  | zero =>
      simp [dyadicRadius, lowFrequencyModes]
  | succ depth ih =>
      rw [openPeriodicVorticityDyadicCube_succ solution t depth, ih]
      simp only [Finset.sum_range_succ]
      abel

/-- The exact unresolved complement after a dyadic aperture. -/
def openPeriodicVorticityDyadicReconstructionFiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : ℝ :=
  ‖openPeriodicVorticityFrequencyRemainder solution t
    (frequencyCube (dyadicRadius depth))‖

theorem openPeriodicVorticityDyadicReconstructionFiber_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    0 ≤ openPeriodicVorticityDyadicReconstructionFiber solution t depth :=
  norm_nonneg _

private def openPeriodicVorticityDyadicH3TailService
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : ℝ :=
  6 * ((2 * Real.pi) *
    Real.sqrt (jacobianTailScale (dyadicRadius depth) * jacobianTailLatticeMass) *
      ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖)

private theorem openPeriodicVorticityDyadicReconstructionFiber_le_service
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    openPeriodicVorticityDyadicReconstructionFiber solution t depth ≤
      openPeriodicVorticityDyadicH3TailService solution t depth := by
  unfold openPeriodicVorticityDyadicReconstructionFiber
  apply (ContinuousMap.norm_le _ (by
    unfold openPeriodicVorticityDyadicH3TailService
    positivity)).mpr
  intro q
  exact norm_openPeriodicVorticityFrequencyRemainder_frequencyCube_le_H3Tail
    solution t (dyadicRadius depth) q

private theorem tendsto_dyadicRadius_atTop :
    Tendsto dyadicRadius atTop atTop := by
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)

private theorem tendsto_openPeriodicVorticityDyadicH3TailService_atTop
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    Tendsto (openPeriodicVorticityDyadicH3TailService solution t) atTop (nhds 0) := by
  let response : ℝ → ℝ := fun scale ↦
    6 * ((2 * Real.pi) * Real.sqrt (scale * jacobianTailLatticeMass) *
      ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖)
  have hresponse : Continuous response := by
    dsimp [response]
    fun_prop
  have hscale : Tendsto (jacobianTailScale ∘ dyadicRadius) atTop (nhds 0) :=
    tendsto_jacobianTailScale_atTop.comp tendsto_dyadicRadius_atTop
  have htransport := hresponse.continuousAt.tendsto.comp hscale
  change Tendsto (response ∘ (jacobianTailScale ∘ dyadicRadius)) atTop (nhds 0)
  simpa [response, Function.comp_def] using htransport

/-- The complete reconstruction fibre disappears along the cofinal dyadic aperture. -/
theorem tendsto_openPeriodicVorticityDyadicReconstructionFiber_atTop
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    Tendsto (openPeriodicVorticityDyadicReconstructionFiber solution t)
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact openPeriodicVorticityDyadicReconstructionFiber_nonneg solution t
  · exact openPeriodicVorticityDyadicReconstructionFiber_le_service solution t
  · exact tendsto_openPeriodicVorticityDyadicH3TailService_atTop solution t

/-! ## The phase-local `B^0_{infinity,1}`-style receiver -/

/-- Low face plus the complete sum of actual signed-shell spatial suprema. -/
def openPeriodicVorticityPhaseLocalDiniPopulationOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  Real.sqrt 3 *
    (openPeriodicVorticityLowSpatialSup solution t +
      ∑' level : ℕ, openPeriodicVorticityDyadicShellSpatialSup solution t level)

/-- The finite cube population is bounded by the low face plus the exact spatial-sup mass of all
shells crossed so far. -/
theorem norm_openPeriodicVorticityDyadicCube_le_low_add_shells
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    ‖openPeriodicVorticityBandProjector solution t
        (frequencyCube (dyadicRadius depth))‖ ≤
      openPeriodicVorticityLowSpatialSup solution t +
        (∑ level ∈ Finset.range depth,
          openPeriodicVorticityDyadicShellSpatialSup solution t level) := by
  rw [openPeriodicVorticityDyadicCube_eq_low_add_shells solution t depth]
  calc
    ‖openPeriodicVorticityBandProjector solution t lowFrequencyModes +
        ∑ level ∈ Finset.range depth,
          openPeriodicVorticityBandProjector solution t
            (dyadicFrequencyShell level)‖ ≤
      ‖openPeriodicVorticityBandProjector solution t lowFrequencyModes‖ +
        ‖∑ level ∈ Finset.range depth,
          openPeriodicVorticityBandProjector solution t
            (dyadicFrequencyShell level)‖ := norm_add_le _ _
    _ ≤ openPeriodicVorticityLowSpatialSup solution t +
        (∑ level ∈ Finset.range depth,
          openPeriodicVorticityDyadicShellSpatialSup solution t level) := by
      have hshell :
          ‖∑ level ∈ Finset.range depth,
              openPeriodicVorticityBandProjector solution t
                (dyadicFrequencyShell level)‖ ≤
            ∑ level ∈ Finset.range depth,
              ‖openPeriodicVorticityBandProjector solution t
                (dyadicFrequencyShell level)‖ :=
        norm_sum_le _ _
      unfold openPeriodicVorticityLowSpatialSup
        openPeriodicVorticityDyadicShellSpatialSup
      exact add_le_add_right hshell _

/-- **Actual reconstruction inequality.**  The automatically summable signed-shell spatial
suprema on one strict-interior slice control the literal critical vorticity rate.  This is not a
wrapper around that rate: the proof passes through exact finite shell telescoping and a vanishing
cofinal Fourier reconstruction fibre. -/
theorem criticalVorticityRate_le_phaseLocalDiniPopulationOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    criticalVorticityRate solution t.1 ≤
      openPeriodicVorticityPhaseLocalDiniPopulationOn solution t := by
  have hsummable : Summable
      (openPeriodicVorticityDyadicShellSpatialSup solution t) :=
    summable_openPeriodicVorticityDyadicShellSpatialSup solution t
  have hpartial : ∀ depth : ℕ,
      criticalVorticityRate solution t.1 ≤
        Real.sqrt 3 *
          (openPeriodicVorticityLowSpatialSup solution t +
            (∑ level ∈ Finset.range depth,
              openPeriodicVorticityDyadicShellSpatialSup solution t level) +
            openPeriodicVorticityDyadicReconstructionFiber solution t depth) := by
    intro depth
    rw [criticalVorticityRate_eq solution t.2]
    have hreceiverNonneg : 0 ≤ Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          (∑ level ∈ Finset.range depth,
            openPeriodicVorticityDyadicShellSpatialSup solution t level) +
          openPeriodicVorticityDyadicReconstructionFiber solution t depth) := by
      apply mul_nonneg (Real.sqrt_nonneg 3)
      exact add_nonneg
        (add_nonneg (openPeriodicVorticityLowSpatialSup_nonneg solution t)
          (Finset.sum_nonneg fun level _ ↦
            openPeriodicVorticityDyadicShellSpatialSup_nonneg solution t level))
        (openPeriodicVorticityDyadicReconstructionFiber_nonneg solution t depth)
    apply (ContinuousMap.norm_le _ hreceiverNonneg).mpr
    intro q
    have hreal := norm_space_le_sqrt_three_mul_norm_complexifySpace
      (torusVorticityEvolution solution t q)
    have hsplit := DFunLike.congr_fun
      (complexTorusVorticitySlice_eq_band_add_frequencyRemainder solution t
        (frequencyCube (dyadicRadius depth))) q
    have hcomplex : ‖complexTorusVorticitySlice solution t q‖ ≤
        ‖openPeriodicVorticityBandProjector solution t
          (frequencyCube (dyadicRadius depth))‖ +
        openPeriodicVorticityDyadicReconstructionFiber solution t depth := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (openPeriodicVorticityBandProjector solution t
          (frequencyCube (dyadicRadius depth))).norm_coe_le_norm q
      · exact (openPeriodicVorticityFrequencyRemainder solution t
          (frequencyCube (dyadicRadius depth))).norm_coe_le_norm q
    have hcube := norm_openPeriodicVorticityDyadicCube_le_low_add_shells
      solution t depth
    calc
      ‖torusVorticityEvolution solution t q‖ ≤
          Real.sqrt 3 * ‖complexTorusVorticitySlice solution t q‖ := hreal
      _ ≤ Real.sqrt 3 *
          (‖openPeriodicVorticityBandProjector solution t
              (frequencyCube (dyadicRadius depth))‖ +
            openPeriodicVorticityDyadicReconstructionFiber solution t depth) :=
        mul_le_mul_of_nonneg_left hcomplex (Real.sqrt_nonneg 3)
      _ ≤ Real.sqrt 3 *
          (openPeriodicVorticityLowSpatialSup solution t +
            (∑ level ∈ Finset.range depth,
              openPeriodicVorticityDyadicShellSpatialSup solution t level) +
            openPeriodicVorticityDyadicReconstructionFiber solution t depth) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 3)
        exact add_le_add_left hcube
          (openPeriodicVorticityDyadicReconstructionFiber solution t depth)
  have hlimit : Tendsto (fun depth : ℕ ↦
      Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          (∑ level ∈ Finset.range depth,
            openPeriodicVorticityDyadicShellSpatialSup solution t level) +
          openPeriodicVorticityDyadicReconstructionFiber solution t depth))
      atTop (nhds (openPeriodicVorticityPhaseLocalDiniPopulationOn solution t)) := by
    have hshell := hsummable.hasSum.tendsto_sum_nat
    have hfiber := tendsto_openPeriodicVorticityDyadicReconstructionFiber_atTop solution t
    unfold openPeriodicVorticityPhaseLocalDiniPopulationOn
    have hbody : Tendsto (fun depth : ℕ ↦
        openPeriodicVorticityLowSpatialSup solution t +
            (∑ level ∈ Finset.range depth,
              openPeriodicVorticityDyadicShellSpatialSup solution t level) +
          openPeriodicVorticityDyadicReconstructionFiber solution t depth)
        atTop (nhds
          (openPeriodicVorticityLowSpatialSup solution t +
            ∑' level : ℕ,
              openPeriodicVorticityDyadicShellSpatialSup solution t level)) := by
      simpa only [add_zero] using
        ((tendsto_const_nhds.add hshell).add hfiber)
    exact tendsto_const_nhds.mul hbody
  exact ge_of_tendsto hlimit (Filter.Eventually.of_forall hpartial)

/-- Real-domain presentation for time integration.  It is zero outside the open lifespan and
does not assign a terminal trace. -/
def openPeriodicVorticityPhaseLocalDiniPopulation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) : ℝ :=
  if hs : s ∈ Ioo 0 T then
    openPeriodicVorticityPhaseLocalDiniPopulationOn solution ⟨s, hs⟩
  else 0

/-- The exact pointwise bridge on the real time chart. -/
theorem criticalVorticityRate_le_phaseLocalDiniPopulation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) :
    criticalVorticityRate solution s ≤
      openPeriodicVorticityPhaseLocalDiniPopulation solution s := by
  by_cases hs : s ∈ Ioo 0 T
  · rw [openPeriodicVorticityPhaseLocalDiniPopulation]
    simp only [hs, dite_true]
    exact criticalVorticityRate_le_phaseLocalDiniPopulationOn solution ⟨s, hs⟩
  · simp [criticalVorticityRate, openPeriodicVorticityPhaseLocalDiniPopulation, hs]

/-- The exact actual-solution phase-local terminal obligation.  Per-slice spatial-scale
summability is proved above; the sole remaining field is integrability of the resulting population
across the open lifespan. -/
structure OpenPeriodicPhaseLocalDiniReceipt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) : Prop where
  populationIntervalIntegrable :
    IntervalIntegrable (openPeriodicVorticityPhaseLocalDiniPopulation solution)
      volume 0 T

/-- A phase-local receipt supplies terminal integrability of the literal critical vorticity
rate. -/
theorem intervalIntegrable_criticalVorticityRate_of_phaseLocalDiniReceipt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (receipt : OpenPeriodicPhaseLocalDiniReceipt solution) :
    IntervalIntegrable (criticalVorticityRate solution) volume 0 T := by
  apply receipt.populationIntervalIntegrable.mono_fun'
  · exact (criticalVorticityRate_measurable solution).aestronglyMeasurable.restrict
  · filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (criticalVorticityRate_nonneg solution s)]
    exact criticalVorticityRate_le_phaseLocalDiniPopulation solution s

/-- Universal time-integrability of the actual phase-local population discharges the literal
scale-critical terminal receiver. -/
theorem criticalVorticityTerminalControl_of_phaseLocalDini
    (control : ∀ {T nu : ℝ} {initial : InitialVelocity}
      {velocity : VelocityField} {pressure : PressureField},
      0 < nu →
      InitialVelocityConditionPeriodic initial →
      (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
        OpenPeriodicPhaseLocalDiniReceipt solution) :
    CriticalVorticityTerminalControl := by
  intro T nu initial velocity pressure hnu hinitial solution
  exact intervalIntegrable_criticalVorticityRate_of_phaseLocalDiniReceipt
    solution (control hnu hinitial solution)

section Audit

#print axioms openPeriodicVorticityDyadicCube_eq_low_add_shells
#print axioms summable_openPeriodicVorticityDyadicShellSpatialSup
#print axioms tendsto_openPeriodicVorticityDyadicReconstructionFiber_atTop
#print axioms criticalVorticityRate_le_phaseLocalDiniPopulationOn
#print axioms intervalIntegrable_criticalVorticityRate_of_phaseLocalDiniReceipt
#print axioms criticalVorticityTerminalControl_of_phaseLocalDini

end Audit

end Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
