import ElementaryHolonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence

/-!
# Compact endpoint exhaustion for the literal smooth terminal packing

**[proved-derived; formal-checked]**  This file performs the measure-theoretic passage which is
needed after a real compact scale--time estimate has been obtained.  A single finite real bound,
uniform simultaneously in the left endpoint `a -> 0`, the right endpoint `b -> T`, and the finite
scale depth, bounds the literal `ENNReal` terminal packing.  The passage uses an explicit nested
compact exhaustion and Tonelli; it never turns an infinite value into a real number.

The premise is deliberately the complete unweighted scale--time rectangle.  The adaptive clock
theorems currently pay its matched diagonal, while their earlier-history reconstruction fibre is
retained.  Consequently this file does not claim that the premise follows from the present energy
or cofinal-work estimates.
-/

noncomputable section

open Filter MeasureTheory Real Set Topology
open scoped BigOperators ENNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesTerminalCompactEndpointExhaustion

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
open Soma.Holonics.Millennium.NavierStokesClockWeightedCompactTimePacking
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

set_option maxHeartbeats 2400000

/-! ## A concrete compact exhaustion of the open lifespan -/

/-- Positive distance from either endpoint in the `n`th compact exhaustion window. -/
def smoothTerminalExhaustionRadius (T : ℝ) (n : ℕ) : ℝ :=
  (T / 2) * (1 / ((n : ℝ) + 1))

/-- The left endpoint approaches zero from inside the lifespan. -/
def smoothTerminalExhaustionLeft (T : ℝ) (n : ℕ) : ℝ :=
  smoothTerminalExhaustionRadius T n

/-- The right endpoint approaches `T` from inside the lifespan. -/
def smoothTerminalExhaustionRight (T : ℝ) (n : ℕ) : ℝ :=
  T - smoothTerminalExhaustionRadius T n

theorem smoothTerminalExhaustionRadius_pos
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 < smoothTerminalExhaustionRadius T n := by
  unfold smoothTerminalExhaustionRadius
  exact mul_pos (div_pos hT (by norm_num)) (by positivity)

theorem smoothTerminalExhaustionRadius_le_half
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    smoothTerminalExhaustionRadius T n ≤ T / 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hinv : 1 / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).2 hden
  unfold smoothTerminalExhaustionRadius
  calc
    T / 2 * (1 / ((n : ℝ) + 1)) ≤ T / 2 * 1 :=
      mul_le_mul_of_nonneg_left hinv (div_nonneg hT.le (by norm_num))
    _ = T / 2 := mul_one _

theorem smoothTerminalExhaustionLeft_pos
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 < smoothTerminalExhaustionLeft T n :=
  smoothTerminalExhaustionRadius_pos hT n

theorem smoothTerminalExhaustionLeft_le_right
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    smoothTerminalExhaustionLeft T n ≤ smoothTerminalExhaustionRight T n := by
  unfold smoothTerminalExhaustionLeft smoothTerminalExhaustionRight
  linarith [smoothTerminalExhaustionRadius_le_half hT n]

theorem smoothTerminalExhaustionRight_lt
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    smoothTerminalExhaustionRight T n < T := by
  unfold smoothTerminalExhaustionRight
  linarith [smoothTerminalExhaustionRadius_pos hT n]

theorem tendsto_smoothTerminalExhaustionLeft
    (T : ℝ) :
    Tendsto (smoothTerminalExhaustionLeft T) atTop (nhds 0) := by
  change Tendsto (fun n : ℕ ↦ (T / 2) * (1 / ((n : ℝ) + 1))) atTop (nhds 0)
  have hreciprocal :
      Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hconstant : Tendsto (fun _ : ℕ ↦ T / 2) atTop (nhds (T / 2)) :=
    tendsto_const_nhds
  simpa using hconstant.mul hreciprocal

theorem tendsto_smoothTerminalExhaustionRight
    (T : ℝ) :
    Tendsto (smoothTerminalExhaustionRight T) atTop (nhds T) := by
  change Tendsto (fun n : ℕ ↦ T - smoothTerminalExhaustionLeft T n) atTop (nhds T)
  have hconstant : Tendsto (fun _ : ℕ ↦ T) atTop (nhds T) := tendsto_const_nhds
  simpa using hconstant.sub (tendsto_smoothTerminalExhaustionLeft T)

/-! ## Exact real/extended-real presentation on one compact rectangle -/

theorem compactOpenSmoothDyadicVorticityBandSpatialSup_eq_rate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ)
    {time : ℝ} (htime : time ∈ Icc a b) :
    compactOpenSmoothDyadicVorticityBandSpatialSup
        solution ha hab hbT scale time =
      openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time := by
  have hfull : time ∈ Ioo (0 : ℝ) T :=
    ⟨ha.trans_le htime.1, htime.2.trans_lt hbT⟩
  rw [openPeriodicSmoothDyadicVorticityBandSpatialSupRate_eq solution scale hfull]
  unfold compactOpenSmoothDyadicVorticityBandSpatialSup
  congr 1
  apply Subtype.ext
  exact compactInteriorTime_eq ha hab hbT htime

/-- On a compact interior interval, one band's `ENNReal` integral is exactly the `ofReal`
presentation of the ordinary interval integral used by the compact clock construction. -/
theorem lintegral_smoothBandRate_eq_ofReal_compactBandIntegral
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (scale : ℕ) :
    (∫⁻ time in Ioo a b,
        ENNReal.ofReal
          (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time)
        ∂volume) =
      ENNReal.ofReal
        (∫ time in a..b,
          compactOpenSmoothDyadicVorticityBandSpatialSup
            solution ha hab hbT scale time) := by
  have hsubset : Ioo a b ⊆ Ioo (0 : ℝ) T := by
    intro time htime
    exact ⟨ha.trans htime.1, htime.2.trans hbT⟩
  have hintegrable : IntegrableOn
      (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale)
      (Ioo a b) volume :=
    (openPeriodicSolutionOn_smoothDyadicVorticityBandSpatialSupRate_integrableOn
      solution hnu scale).mono_set hsubset
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo a b)]
      openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale := by
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards with time
    intro htime
    rw [openPeriodicSmoothDyadicVorticityBandSpatialSupRate_eq
      solution scale (hsubset htime)]
    exact openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg
      solution ⟨time, hsubset htime⟩ scale
  rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnonneg]
  congr 1
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro time htime
  exact (compactOpenSmoothDyadicVorticityBandSpatialSup_eq_rate
    solution ha hab hbT scale ⟨htime.1.le, htime.2.le⟩).symm

/-- Finite Tonelli on a compact rectangle agrees exactly with the real compact rectangle owner. -/
theorem lintegral_finiteSmoothBandPrefix_eq_ofReal_compactRectangle
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    (∫⁻ time in Ioo a b,
        ∑ scale ∈ Finset.range depth,
          ENNReal.ofReal
            (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time)
        ∂volume) =
      ENNReal.ofReal
        (compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
          solution ha hab hbT depth) := by
  rw [lintegral_finsetSum']
  · unfold compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro scale hscale
      exact lintegral_smoothBandRate_eq_ofReal_compactBandIntegral
        solution hnu ha hab hbT scale
    · intro scale hscale
      exact intervalIntegral.integral_nonneg hab fun time _htime ↦
        compactOpenSmoothDyadicVorticityBandSpatialSup_nonneg
          solution ha hab hbT scale time
  · intro scale hscale
    exact (((continuousOn_openPeriodicSmoothDyadicVorticityBandSpatialSupRate
      solution scale).aestronglyMeasurable measurableSet_Ioo).aemeasurable
        |>.ennreal_ofReal).mono_measure (Measure.restrict_mono hsubset le_rfl)
    where
      hsubset : Ioo a b ⊆ Ioo (0 : ℝ) T := by
        intro time htime
        exact ⟨ha.trans htime.1, htime.2.trans hbT⟩

/-- Every compact finite-depth rectangle is a genuine subpopulation of the literal terminal
packing.  Thus uniform compact exhaustion is not merely sufficient: any finite terminal bound
must pay these same rectangles. -/
theorem ofReal_compactRectangle_le_terminalSmoothDyadicPacking
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    ENNReal.ofReal
        (compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
          solution ha hab hbT depth) ≤
      openPeriodicVorticityTerminalSmoothDyadicPacking solution := by
  rw [← lintegral_finiteSmoothBandPrefix_eq_ofReal_compactRectangle
    solution hnu ha hab hbT depth]
  have hsubset : Ioo a b ⊆ Ioo (0 : ℝ) T := by
    intro time htime
    exact ⟨ha.trans htime.1, htime.2.trans hbT⟩
  calc
    (∫⁻ time in Ioo a b,
        ∑ scale ∈ Finset.range depth,
          ENNReal.ofReal
            (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time)
        ∂volume) ≤
      ∫⁻ time in Ioo (0 : ℝ) T,
        ∑ scale ∈ Finset.range depth,
          ENNReal.ofReal
            (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time)
        ∂volume := by
      exact lintegral_mono'
        (Measure.restrict_mono hsubset le_rfl) (fun _time ↦ le_rfl)
    _ = ∑ scale ∈ Finset.range depth,
        ∫⁻ time in Ioo (0 : ℝ) T,
          ENNReal.ofReal
            (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time)
          ∂volume := by
      rw [lintegral_finsetSum']
      intro scale _hscale
      exact (((continuousOn_openPeriodicSmoothDyadicVorticityBandSpatialSupRate
        solution scale).aestronglyMeasurable measurableSet_Ioo).aemeasurable).ennreal_ofReal
    _ ≤ ∑' scale : ℕ,
        ∫⁻ time in Ioo (0 : ℝ) T,
          ENNReal.ofReal
            (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time)
          ∂volume := by
      exact ENNReal.summable.sum_le_tsum (Finset.range depth)
        (fun _scale _hscale ↦ bot_le)
    _ = openPeriodicVorticityTerminalSmoothDyadicPacking solution :=
      (openPeriodicVorticityTerminalSmoothDyadicPacking_eq_tsum_lintegral solution).symm

/-! ## Uniform endpoint/depth exhaustion -/

/-- **Compact-to-terminal exhaustion.**  The displayed hypothesis is the exact uniformity that
the terminal receiver needs: the same finite real `bound` pays every interior endpoint pair and
every finite scale depth. -/
theorem openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformExhaustionRectangle
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (bound : ℝ)
    (uniformExhaustion : ∀ (n depth : ℕ),
      compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution
          (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
          (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
          (smoothTerminalExhaustionRight_lt solution.terminal_pos n)
          depth ≤ bound) :
    openPeriodicVorticityTerminalSmoothDyadicPacking solution ≤
      ENNReal.ofReal bound := by
  rw [openPeriodicVorticityTerminalSmoothDyadicPacking_eq_tsum_lintegral]
  apply ENNReal.tsum_le_of_sum_range_le
  intro depth
  let left : ℕ → ℝ := smoothTerminalExhaustionLeft T
  let right : ℕ → ℝ := smoothTerminalExhaustionRight T
  let bandWord : ℝ → ENNReal := fun time ↦
    ∑ scale ∈ Finset.range depth,
      ENNReal.ofReal
        (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time)
  have hbandWordMeasurable : AEMeasurable bandWord
      (volume.restrict (Ioo (0 : ℝ) T)) := by
    unfold bandWord
    exact Finset.aemeasurable_fun_sum (Finset.range depth) fun scale _hscale ↦
      (((continuousOn_openPeriodicSmoothDyadicVorticityBandSpatialSupRate
        solution scale).aestronglyMeasurable measurableSet_Ioo).aemeasurable).ennreal_ofReal
  have hcover : AECover (volume.restrict (Ioo (0 : ℝ) T)) atTop
      (fun n ↦ Ioo (left n) (right n)) := by
    exact aecover_Ioo_of_Ioo
      (tendsto_smoothTerminalExhaustionLeft T)
      (tendsto_smoothTerminalExhaustionRight T)
  have hlimit := hcover.lintegral_tendsto_of_nat hbandWordMeasurable
  have hcompactBound : ∀ n : ℕ,
      (∫⁻ time in Ioo (left n) (right n), bandWord time
        ∂(volume.restrict (Ioo (0 : ℝ) T))) ≤ ENNReal.ofReal bound := by
    intro n
    have hleft : 0 < left n := smoothTerminalExhaustionLeft_pos solution.terminal_pos n
    have hlr : left n ≤ right n :=
      smoothTerminalExhaustionLeft_le_right solution.terminal_pos n
    have hright : right n < T :=
      smoothTerminalExhaustionRight_lt solution.terminal_pos n
    have hsub : Ioo (left n) (right n) ⊆ Ioo (0 : ℝ) T := by
      intro time htime
      exact ⟨hleft.trans htime.1, htime.2.trans hright⟩
    rw [Measure.restrict_restrict_of_subset hsub]
    change (∫⁻ time in Ioo (left n) (right n),
      ∑ scale ∈ Finset.range depth,
        ENNReal.ofReal
          (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time)
      ∂volume) ≤ ENNReal.ofReal bound
    rw [lintegral_finiteSmoothBandPrefix_eq_ofReal_compactRectangle
      solution hnu hleft hlr hright depth]
    exact ENNReal.ofReal_le_ofReal
      (uniformExhaustion n depth)
  have hfullPrefix :
      (∫⁻ time, bandWord time ∂(volume.restrict (Ioo (0 : ℝ) T))) ≤
        ENNReal.ofReal bound :=
    le_of_tendsto hlimit (Filter.Eventually.of_forall hcompactBound)
  change (∫⁻ time in Ioo (0 : ℝ) T,
    ∑ scale ∈ Finset.range depth,
      ENNReal.ofReal
        (openPeriodicSmoothDyadicVorticityBandSpatialSupRate solution scale time)
    ∂volume) ≤ ENNReal.ofReal bound at hfullPrefix
  rw [lintegral_finsetSum'] at hfullPrefix
  · exact hfullPrefix
  · intro scale hscale
    exact (((continuousOn_openPeriodicSmoothDyadicVorticityBandSpatialSupRate
      solution scale).aestronglyMeasurable measurableSet_Ioo).aemeasurable).ennreal_ofReal

/-- Requiring one bound on every compact interior interval is a convenient stronger presentation
of the exact cofinal-exhaustion premise above. -/
theorem openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformCompactRectangle
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (bound : ℝ)
    (uniformCompact : ∀ (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
      (depth : ℕ),
      compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution ha hab hbT depth ≤ bound) :
    openPeriodicVorticityTerminalSmoothDyadicPacking solution ≤
      ENNReal.ofReal bound := by
  apply openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformExhaustionRectangle
    solution hnu bound
  intro n depth
  exact uniformCompact
    (smoothTerminalExhaustionLeft T n)
    (smoothTerminalExhaustionRight T n)
    (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
    (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
    (smoothTerminalExhaustionRight_lt solution.terminal_pos n)
    depth

/-- The same exact uniform real premise constructs the literal terminal-packing receipt. -/
theorem openPeriodicTerminalSmoothDyadicPackingReceipt_of_uniformCompactRectangle
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (bound : ℝ)
    (uniformCompact : ∀ (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
      (depth : ℕ),
      compactOpenSmoothDyadicFiniteScaleTimeRectangleL1
        solution ha hab hbT depth ≤ bound) :
    OpenPeriodicTerminalSmoothDyadicPackingReceipt solution := by
  refine ⟨lt_of_le_of_lt
    (openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformCompactRectangle
      solution hnu bound uniformCompact) ENNReal.ofReal_lt_top⟩

section Audit

#print axioms lintegral_smoothBandRate_eq_ofReal_compactBandIntegral
#print axioms lintegral_finiteSmoothBandPrefix_eq_ofReal_compactRectangle
#print axioms ofReal_compactRectangle_le_terminalSmoothDyadicPacking
#print axioms openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformExhaustionRectangle
#print axioms openPeriodicVorticityTerminalSmoothDyadicPacking_le_of_uniformCompactRectangle
#print axioms openPeriodicTerminalSmoothDyadicPackingReceipt_of_uniformCompactRectangle

end Audit

end Soma.Holonics.Millennium.NavierStokesTerminalCompactEndpointExhaustion
