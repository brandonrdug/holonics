import ElementaryHolonics.Millennium.NavierStokesClockWeightedSpatialBandPacking

/-!
# Compact-time and scale-matched clock packing

**[proved-derived; formal-checked]** The clock-weighted spatial prefix has a genuine compact-time
`L¹` passage.  Hölder on the restricted Lebesgue interval proves

`(∫ P) ^ 2 ≤ (b - a) * ∫ P ^ 2`,

and the existing scale--time ledger therefore pays this compact-time receiver by the same one-copy
linear boundary-work term.

**[proved-derived; formal-checked]** There is also a diagonal, scale-matched terminal-window
receiver.  Shell `j` is integrated only over its reciprocal parabolic clock window
`[b - 4⁻ʲ, b]`.  Localized Bernstein followed by time Cauchy--Schwarz pays its `L¹` square by
`card_j / 16ʲ` times the clocked coefficient mass in that same window.  The density sum is the
already proved depth-uniform `1024`, and the matched windows sit inside `[a,b]` when
`a ≤ b - 1`; hence the signed scale--time ledger pays the entire matched finite word.

**[open]** The diagonal receiver is not the unweighted terminal receiver.  For a finite word, the
exact missing scale--time population is the sum of each shell's earlier interval
`[a, b - 4⁻ʲ]`.  It is retained below as the off-diagonal reconstruction fibre and an exact
rectangle decomposition is proved.  No estimate removes that fibre here.  The endpoint clock-weight
defect and cofinal frequency complement from the imported owner also remain distinct retained
fibres; no terminal regularity conclusion is asserted.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesClockWeightedCompactTimePacking

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesClockWeightedSpatialBandPacking
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger
open Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

set_option maxHeartbeats 2400000

/-! ## The genuine compact-time Cauchy--Schwarz passage -/

/-- Cauchy--Schwarz on an ordered compact real interval, stated in the exact squared form used by
the scale--time ledger. -/
theorem intervalIntegral_sq_integral_le_length_mul_integral_sq
    {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b) (hf : Continuous f)
    (hnonneg : ∀ x, 0 ≤ f x) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  have hf_ae : AEStronglyMeasurable f μ := hf.aestronglyMeasurable.restrict
  have hf2int : Integrable (fun x ↦ f x ^ 2) μ :=
    ((hf.pow 2).intervalIntegrable a b).1
  have hfLp : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hf_ae).2 hf2int
  have honeLp : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 μ := memLp_const 1
  have hfLp' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    convert hfLp using 1
    norm_num
  have honeLp' : MemLp (fun _ : ℝ ↦ (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    convert honeLp using 1
    norm_num
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two (ae_of_all μ hnonneg)
    (ae_of_all μ fun _ : ℝ ↦ (by norm_num : 0 ≤ (1 : ℝ))) hfLp' honeLp'
  simp only [mul_one, one_rpow, integral_const, one_div] at hholder
  dsimp [μ] at hholder
  have hmeasure : (volume.restrict (Ioc a b)).real univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hmeasure, mul_one] at hholder
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hleft : 0 ≤ ∫ x, f x ∂μ :=
    integral_nonneg_of_ae (ae_of_all μ hnonneg)
  have hright : 0 ≤ ∫ x, f x ^ 2 ∂μ :=
    integral_nonneg_of_ae (ae_of_all μ fun x ↦ sq_nonneg (f x))
  have hholder' : ∫ x, f x ∂μ ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (b - a) := by
    dsimp [μ]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [Real.rpow_two, one_div] using hholder
  calc
    (∫ x, f x ∂μ) ^ 2 ≤
        (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (b - a)) ^ 2 :=
      pow_le_pow_left₀ hleft hholder' 2
    _ = (b - a) * ∫ x, f x ^ 2 ∂μ := by
      rw [mul_pow, Real.sq_sqrt hright, Real.sq_sqrt (sub_nonneg.mpr hab)]
      ring

theorem openPeriodicSolutionOn_clockWeightedSpatialPrefix_L1_sq_le_length_mul_L2
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    (∫ time in a..b,
      compactOpenSmoothDyadicClockWeightedSpatialPrefix
        solution ha hab hbT depth time) ^ 2 ≤
      (b - a) * ∫ time in a..b,
        compactOpenSmoothDyadicClockWeightedSpatialPrefix
          solution ha hab hbT depth time ^ 2 := by
  exact intervalIntegral_sq_integral_le_length_mul_integral_sq hab
    (continuous_compactOpenSmoothDyadicClockWeightedSpatialPrefix
      solution ha hab hbT depth)
    (fun time ↦ openSmoothDyadicClockWeightedSpatialPrefix_nonneg solution
      (compactInteriorTime ha hab hbT time) depth)

/-- The compact-time `L¹` clock-weighted prefix is paid by the exact cumulative linear
boundary-work receiver already returned by the scale--time ledger. -/
theorem openPeriodicSolutionOn_clockWeightedSpatialPrefix_L1_sq_le_linearBoundaryWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu) (depth : ℕ) :
    nu * (∫ time in a..b,
      compactOpenSmoothDyadicClockWeightedSpatialPrefix
        solution ha hab hbT depth time) ^ 2 ≤
      1024 * (b - a) * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|) := by
  have hcs := openPeriodicSolutionOn_clockWeightedSpatialPrefix_L1_sq_le_length_mul_L2
    solution ha hab hbT depth
  have hledger :=
    openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_linearBoundaryWork
      solution ha hab hbT hnu depth
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab
  calc
    nu * (∫ time in a..b,
        compactOpenSmoothDyadicClockWeightedSpatialPrefix
          solution ha hab hbT depth time) ^ 2 ≤
      nu * ((b - a) * ∫ time in a..b,
        compactOpenSmoothDyadicClockWeightedSpatialPrefix
          solution ha hab hbT depth time ^ 2) :=
      mul_le_mul_of_nonneg_left hcs hnu.le
    _ = (b - a) * (nu * ∫ time in a..b,
        compactOpenSmoothDyadicClockWeightedSpatialPrefix
          solution ha hab hbT depth time ^ 2) := by ring
    _ ≤ (b - a) * (1024 * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|)) :=
      mul_le_mul_of_nonneg_left hledger hlength
    _ = 1024 * (b - a) * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|) := by ring

/-! ## Reciprocal shell clocks and the diagonal terminal windows -/

/-- The reciprocal parabolic clock of shell `j`. -/
def smoothDyadicReciprocalShellClock (scale : ℕ) : ℝ :=
  ((4 : ℝ) ^ scale)⁻¹

/-- The left endpoint of the terminal window whose length is shell `j`'s reciprocal clock. -/
def smoothDyadicTerminalWindowStart (terminal : ℝ) (scale : ℕ) : ℝ :=
  terminal - smoothDyadicReciprocalShellClock scale

theorem smoothDyadicReciprocalShellClock_pos (scale : ℕ) :
    0 < smoothDyadicReciprocalShellClock scale := by
  unfold smoothDyadicReciprocalShellClock
  positivity

theorem smoothDyadicReciprocalShellClock_le_one (scale : ℕ) :
    smoothDyadicReciprocalShellClock scale ≤ 1 := by
  unfold smoothDyadicReciprocalShellClock
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4))

theorem smoothDyadicTerminalWindowStart_le (terminal : ℝ) (scale : ℕ) :
    smoothDyadicTerminalWindowStart terminal scale ≤ terminal := by
  unfold smoothDyadicTerminalWindowStart
  linarith [smoothDyadicReciprocalShellClock_pos scale]

theorem leftEndpoint_le_smoothDyadicTerminalWindowStart
    {a terminal : ℝ} (ha : a ≤ terminal - 1) (scale : ℕ) :
    a ≤ smoothDyadicTerminalWindowStart terminal scale := by
  unfold smoothDyadicTerminalWindowStart
  linarith [smoothDyadicReciprocalShellClock_le_one scale]

/-- The spatial supremum of one smooth vorticity band after compact-time interiorization. -/
def compactOpenSmoothDyadicVorticityBandSpatialSup
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (time : ℝ) : ℝ :=
  openPeriodicSmoothDyadicVorticityBandSpatialSup
    solution (compactInteriorTime ha hab hbT time) scale

theorem continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    Continuous (compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale) :=
  (continuous_openPeriodicSmoothDyadicVorticityBandSpatialSup solution scale).comp
    (continuous_compactInteriorTime ha hab hbT)

theorem compactOpenSmoothDyadicVorticityBandSpatialSup_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (time : ℝ) :
    0 ≤ compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale time :=
  openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg solution
    (compactInteriorTime ha hab hbT time) scale

theorem compactOpenSmoothDyadicVorticityBandSpatialSup_sq_le_card_mul_coefficientMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) (time : ℝ) :
    compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale time ^ 2 ≤
      ((smoothDyadicBandNativeAperture scale).card : ℝ) *
        compactOpenSmoothDyadicBandCoefficientMass
          solution ha hab hbT scale time := by
  have hmass := openSmoothDyadicBandCoefficientMass_nonneg solution
    (compactInteriorTime ha hab hbT time) scale
  have hspatial := openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg solution
    (compactInteriorTime ha hab hbT time) scale
  have hcard : 0 ≤ ((smoothDyadicBandNativeAperture scale).card : ℝ) := by positivity
  have hbernstein :=
    openPeriodicSmoothDyadicVorticityBandSpatialSup_le_sqrt_card_mul_sqrt_coefficientMass
      solution (compactInteriorTime ha hab hbT time) scale
  have hsquare := pow_le_pow_left₀ hspatial hbernstein 2
  rw [mul_pow, Real.sq_sqrt hcard, Real.sq_sqrt hmass] at hsquare
  simpa [compactOpenSmoothDyadicVorticityBandSpatialSup,
    compactOpenSmoothDyadicBandCoefficientMass] using hsquare

/-- Shell `j`'s spatial `L¹` mass in its own final reciprocal-clock window. -/
def compactOpenSmoothDyadicMatchedTerminalBandL1
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) : ℝ :=
  ∫ time in smoothDyadicTerminalWindowStart b scale..b,
    compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale time

/-- Shell `j`'s `4ʲ M_j` clock mass in the same final reciprocal-clock window. -/
def compactOpenSmoothDyadicMatchedTerminalBandClockMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) : ℝ :=
  ∫ time in smoothDyadicTerminalWindowStart b scale..b,
    (4 : ℝ) ^ scale *
      compactOpenSmoothDyadicBandCoefficientMass
        solution ha hab hbT scale time

theorem compactOpenSmoothDyadicMatchedTerminalBandL1_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    0 ≤ compactOpenSmoothDyadicMatchedTerminalBandL1
      solution ha hab hbT scale := by
  unfold compactOpenSmoothDyadicMatchedTerminalBandL1
  exact intervalIntegral.integral_nonneg
    (smoothDyadicTerminalWindowStart_le b scale) fun time _htime ↦
      compactOpenSmoothDyadicVorticityBandSpatialSup_nonneg
        solution ha hab hbT scale time

theorem compactOpenSmoothDyadicMatchedTerminalBandClockMass_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    0 ≤ compactOpenSmoothDyadicMatchedTerminalBandClockMass
      solution ha hab hbT scale := by
  unfold compactOpenSmoothDyadicMatchedTerminalBandClockMass
  exact intervalIntegral.integral_nonneg
    (smoothDyadicTerminalWindowStart_le b scale) fun time _htime ↦
      mul_nonneg (by positivity)
        (openSmoothDyadicBandCoefficientMass_nonneg solution
          (compactInteriorTime ha hab hbT time) scale)

/-- The exact one-shell scale-matched estimate.  Its density is `card_j / 16ʲ`; no full
enstrophy population enters. -/
theorem compactOpenSmoothDyadicMatchedTerminalBandL1_sq_le_density_mul_clockMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    compactOpenSmoothDyadicMatchedTerminalBandL1
        solution ha hab hbT scale ^ 2 ≤
      (((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale) *
        compactOpenSmoothDyadicMatchedTerminalBandClockMass
          solution ha hab hbT scale := by
  let start := smoothDyadicTerminalWindowStart b scale
  let spatial := compactOpenSmoothDyadicVorticityBandSpatialSup
    solution ha hab hbT scale
  let mass := compactOpenSmoothDyadicBandCoefficientMass
    solution ha hab hbT scale
  have hstart : start ≤ b := smoothDyadicTerminalWindowStart_le b scale
  have hcs : (∫ time in start..b, spatial time) ^ 2 ≤
      (b - start) * ∫ time in start..b, spatial time ^ 2 :=
    intervalIntegral_sq_integral_le_length_mul_integral_sq hstart
      (continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale)
      (fun time ↦ compactOpenSmoothDyadicVorticityBandSpatialSup_nonneg
        solution ha hab hbT scale time)
  have hspatialInt : IntervalIntegrable (fun time ↦ spatial time ^ 2) volume start b :=
    ((continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale).pow 2).intervalIntegrable _ _
  have hmassInt : IntervalIntegrable
      (fun time ↦ ((smoothDyadicBandNativeAperture scale).card : ℝ) * mass time)
      volume start b :=
    ((continuous_compactOpenSmoothDyadicBandCoefficientMass
      solution ha hab hbT scale).const_mul
        ((smoothDyadicBandNativeAperture scale).card : ℝ)).intervalIntegrable _ _
  have hmono : (∫ time in start..b, spatial time ^ 2) ≤
      ∫ time in start..b,
        ((smoothDyadicBandNativeAperture scale).card : ℝ) * mass time := by
    exact intervalIntegral.integral_mono_on hstart hspatialInt hmassInt
      (fun time _htime ↦
        compactOpenSmoothDyadicVorticityBandSpatialSup_sq_le_card_mul_coefficientMass
          solution ha hab hbT scale time)
  have hmono' : (∫ time in start..b, spatial time ^ 2) ≤
      ((smoothDyadicBandNativeAperture scale).card : ℝ) *
        ∫ time in start..b, mass time := by
    simpa only [intervalIntegral.integral_const_mul] using hmono
  have hlength : 0 ≤ b - start := sub_nonneg.mpr hstart
  have h4 : (0 : ℝ) < (4 : ℝ) ^ scale := by positivity
  have h16 : (16 : ℝ) ^ scale = ((4 : ℝ) ^ scale) ^ 2 := by
    rw [show (16 : ℝ) = (4 : ℝ) * 4 by norm_num, mul_pow, pow_two]
  unfold compactOpenSmoothDyadicMatchedTerminalBandL1
    compactOpenSmoothDyadicMatchedTerminalBandClockMass
  change (∫ time in start..b, spatial time) ^ 2 ≤ _
  rw [intervalIntegral.integral_const_mul]
  calc
    (∫ time in start..b, spatial time) ^ 2 ≤
        (b - start) * ∫ time in start..b, spatial time ^ 2 := hcs
    _ ≤ (b - start) *
        (((smoothDyadicBandNativeAperture scale).card : ℝ) *
          ∫ time in start..b, mass time) :=
      mul_le_mul_of_nonneg_left hmono' hlength
    _ = (((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale) *
        ((4 : ℝ) ^ scale * ∫ time in start..b, mass time) := by
      dsimp [start, smoothDyadicTerminalWindowStart, smoothDyadicReciprocalShellClock]
      rw [h16]
      field_simp [ne_of_gt h4]
      ring

/-- The finite diagonal word of terminal-window spatial `L¹` masses. -/
def compactOpenSmoothDyadicMatchedTerminalL1Prefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactOpenSmoothDyadicMatchedTerminalBandL1 solution ha hab hbT scale

/-- The finite diagonal word of clocked coefficient masses over the same matched windows. -/
def compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactOpenSmoothDyadicMatchedTerminalBandClockMass solution ha hab hbT scale

theorem compactOpenSmoothDyadicMatchedTerminalClockMassPrefix_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    0 ≤ compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
      solution ha hab hbT depth := by
  unfold compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
  exact Finset.sum_nonneg fun scale _hscale ↦
    compactOpenSmoothDyadicMatchedTerminalBandClockMass_nonneg
      solution ha hab hbT scale

theorem compactOpenSmoothDyadicMatchedTerminalL1Prefix_sq_le_density_mul_clockMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactOpenSmoothDyadicMatchedTerminalL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      smoothDyadicClockDensityPrefix depth *
        compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
          solution ha hab hbT depth := by
  unfold compactOpenSmoothDyadicMatchedTerminalL1Prefix
    compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
    smoothDyadicClockDensityPrefix
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro scale _hscale
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · intro scale _hscale
    exact compactOpenSmoothDyadicMatchedTerminalBandClockMass_nonneg
      solution ha hab hbT scale
  · intro scale _hscale
    exact compactOpenSmoothDyadicMatchedTerminalBandL1_sq_le_density_mul_clockMass
      solution ha hab hbT scale

theorem compactOpenSmoothDyadicMatchedTerminalL1Prefix_sq_le_uniformClockMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactOpenSmoothDyadicMatchedTerminalL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      1024 * compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
        solution ha hab hbT depth := by
  exact (compactOpenSmoothDyadicMatchedTerminalL1Prefix_sq_le_density_mul_clockMass
    solution ha hab hbT depth).trans
      (mul_le_mul_of_nonneg_right (smoothDyadicClockDensityPrefix_le depth)
        (compactOpenSmoothDyadicMatchedTerminalClockMassPrefix_nonneg
          solution ha hab hbT depth))

/-- If the compact interval contains a unit terminal window, then every reciprocal shell window is
inside it, and the matched clock word is bounded by the common-rectangle scale--time ledger. -/
theorem compactOpenSmoothDyadicMatchedTerminalClockMassPrefix_le_fullClockIntegral
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (habUnit : a ≤ b - 1) (depth : ℕ) :
    compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
        solution ha hab hbT depth ≤
      ∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time := by
  have hscale : ∀ scale ∈ Finset.range depth,
      compactOpenSmoothDyadicMatchedTerminalBandClockMass
          solution ha hab hbT scale ≤
        ∫ time in a..b, (4 : ℝ) ^ scale *
          compactOpenSmoothDyadicBandCoefficientMass
            solution ha hab hbT scale time := by
    intro scale _hscale
    unfold compactOpenSmoothDyadicMatchedTerminalBandClockMass
    exact intervalIntegral.integral_mono_interval
      (leftEndpoint_le_smoothDyadicTerminalWindowStart habUnit scale)
      (smoothDyadicTerminalWindowStart_le b scale) le_rfl
      (ae_of_all _ fun time ↦ mul_nonneg (by positivity)
        (openSmoothDyadicBandCoefficientMass_nonneg solution
          (compactInteriorTime ha hab hbT time) scale))
      ((compactOpenSmoothDyadicBandCoefficientMass_intervalIntegrable
        solution ha hab hbT scale).const_mul ((4 : ℝ) ^ scale))
  have hsum := Finset.sum_le_sum hscale
  unfold compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
    compactOpenSmoothDyadicPrefixClockedCoefficientMass
  rw [intervalIntegral.integral_finsetSum (fun scale _hscale ↦
    (compactOpenSmoothDyadicBandCoefficientMass_intervalIntegrable
      solution ha hab hbT scale).const_mul ((4 : ℝ) ^ scale))]
  exact hsum

/-- The scale-matched terminal-window `L¹` word is paid without a factor depending on the number
of shells.  This is a diagonal scale--time statement, not the unweighted terminal receiver. -/
theorem openPeriodicSolutionOn_matchedTerminalL1Prefix_sq_le_linearBoundaryWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (habUnit : a ≤ b - 1)
    (hnu : 0 < nu) (depth : ℕ) :
    nu * compactOpenSmoothDyadicMatchedTerminalL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      1024 * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|) := by
  have hpacking := compactOpenSmoothDyadicMatchedTerminalL1Prefix_sq_le_uniformClockMass
    solution ha hab hbT depth
  have hwindow := compactOpenSmoothDyadicMatchedTerminalClockMassPrefix_le_fullClockIntegral
    solution ha hab hbT habUnit depth
  have hledger :=
    openPeriodicSolutionOn_integral_prefixClockedCoefficientMass_le_linearBoundaryWork
      solution ha hab hbT hnu depth
  calc
    nu * compactOpenSmoothDyadicMatchedTerminalL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      nu * (1024 * compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
        solution ha hab hbT depth) :=
      mul_le_mul_of_nonneg_left hpacking hnu.le
    _ = 1024 * (nu * compactOpenSmoothDyadicMatchedTerminalClockMassPrefix
        solution ha hab hbT depth) := by ring
    _ ≤ 1024 * (nu * ∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hwindow hnu.le) (by norm_num)
    _ ≤ 1024 * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|) :=
      mul_le_mul_of_nonneg_left hledger (by norm_num)

/-! ## The exact unmatched/off-diagonal scale--time fibre -/

/-- The common compact-time, finite-scale unweighted rectangle.  This is retained for exact
reconstruction and is not asserted to be uniformly bounded in depth. -/
def compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    ∫ time in a..b, compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale time

/-- The exact earlier-time population excluded by the diagonal terminal-window receiver.  Its
shell-time cells lie off the matched diagonal `length = 4⁻j`. -/
def compactOpenSmoothDyadicOffDiagonalScaleTimeReconstructionFiber
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    ∫ time in a..smoothDyadicTerminalWindowStart b scale,
      compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale time

theorem compactOpenSmoothDyadicOffDiagonalScaleTimeReconstructionFiber_nonneg
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (habUnit : a ≤ b - 1)
    (depth : ℕ) :
    0 ≤ compactOpenSmoothDyadicOffDiagonalScaleTimeReconstructionFiber
      solution ha hab hbT depth := by
  unfold compactOpenSmoothDyadicOffDiagonalScaleTimeReconstructionFiber
  exact Finset.sum_nonneg fun scale _hscale ↦
    intervalIntegral.integral_nonneg
      (leftEndpoint_le_smoothDyadicTerminalWindowStart habUnit scale)
      (fun time _htime ↦
        compactOpenSmoothDyadicVorticityBandSpatialSup_nonneg
          solution ha hab hbT scale time)

/-- Exact reconstruction of the finite unweighted scale--time rectangle as the matched diagonal
plus its earlier, off-diagonal fibre.  The equality records the obstruction; it does not estimate
or discard it. -/
theorem compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_eq_offDiagonal_add_matched
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution ha hab hbT depth =
      compactOpenSmoothDyadicOffDiagonalScaleTimeReconstructionFiber
          solution ha hab hbT depth +
        compactOpenSmoothDyadicMatchedTerminalL1Prefix
          solution ha hab hbT depth := by
  unfold compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
    compactOpenSmoothDyadicOffDiagonalScaleTimeReconstructionFiber
    compactOpenSmoothDyadicMatchedTerminalL1Prefix
    compactOpenSmoothDyadicMatchedTerminalBandL1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro scale _hscale
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale).intervalIntegrable _ _)
    ((continuous_compactOpenSmoothDyadicVorticityBandSpatialSup
      solution ha hab hbT scale).intervalIntegrable _ _)).symm

section Audit

#print axioms intervalIntegral_sq_integral_le_length_mul_integral_sq
#print axioms openPeriodicSolutionOn_clockWeightedSpatialPrefix_L1_sq_le_linearBoundaryWork
#print axioms compactOpenSmoothDyadicMatchedTerminalBandL1_sq_le_density_mul_clockMass
#print axioms compactOpenSmoothDyadicMatchedTerminalL1Prefix_sq_le_uniformClockMass
#print axioms openPeriodicSolutionOn_matchedTerminalL1Prefix_sq_le_linearBoundaryWork
#print axioms compactOpenSmoothDyadicFiniteScaleTimeRectangleL1_eq_offDiagonal_add_matched

end Audit

end Soma.Holonics.Millennium.NavierStokesClockWeightedCompactTimePacking
