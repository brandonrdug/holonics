import ElementaryHolonics.Millennium.NavierStokesDirectionBalancedTime
import ElementaryHolonics.Millennium.NavierStokesVorticitySuperlevelPacking

/-!
# Dyadic amplitude packing crossed with the Hodge tail

The pointwise Markov estimate for one vorticity superlevel loses the nesting between amplitude
levels.  This module retains that nesting.  The dyadic squared-amplitude populations have a
geometric layer-cake bound, so their complete population is summable on every compact spacetime
cell.  Crossing that population with the already summable inverse-fourth-root Hodge tail gives an
unconditional two-scale summable receiver.

**[proved-derived; formal-checked]** This is a packing theorem, not a terminal regularity theorem.
It does not dominate the scale-summed direction current or `criticalVorticityRate`: a spacetime
`L²` population can still have tall, narrow spikes whose time-indexed spatial supremum is not
integrable.  Closing that reconstruction passage remains a separate analytic obligation.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPackedHodgeTerminalSummability

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDirectionBalancedTime
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticitySuperlevelPacking

/-! ## The geometric layer-cake inequality -/

/-- [definition] The dyadic amplitude population based at a nonnegative level. -/
def dyadicAmplitudeLevel (base : ℝ) (amplitude : ℕ) : ℝ :=
  base * (2 : ℝ) ^ amplitude

theorem dyadicAmplitudeLevel_nonneg {base : ℝ} (hbase : 0 ≤ base) (amplitude : ℕ) :
    0 ≤ dyadicAmplitudeLevel base amplitude := by
  unfold dyadicAmplitudeLevel
  positivity

private theorem sum_range_dyadicAmplitudeLevel_sq_le
    {base : ℝ} (hbase : 0 ≤ base) (amplitude : ℕ) :
    (∑ level ∈ Finset.range (amplitude + 1), dyadicAmplitudeLevel base level ^ 2) ≤
      (4 / 3 : ℝ) * dyadicAmplitudeLevel base amplitude ^ 2 := by
  induction amplitude with
  | zero =>
      simp [dyadicAmplitudeLevel]
      nlinarith [sq_nonneg base]
  | succ amplitude ih =>
      rw [Finset.sum_range_succ]
      have hlevel : 0 ≤ dyadicAmplitudeLevel base amplitude :=
        dyadicAmplitudeLevel_nonneg hbase amplitude
      have hnext :
          dyadicAmplitudeLevel base (amplitude + 1) =
            2 * dyadicAmplitudeLevel base amplitude := by
        simp [dyadicAmplitudeLevel, pow_succ]
        ring
      rw [hnext]
      nlinarith

private theorem sum_range_dyadicAmplitudeIndicator_le
    {base value : ℝ} (hbase : 0 ≤ base) (_hvalue : 0 ≤ value) (count : ℕ) :
    (∑ amplitude ∈ Finset.range count,
        if dyadicAmplitudeLevel base amplitude ≤ value then
          dyadicAmplitudeLevel base amplitude ^ 2 else 0) ≤
      (4 / 3 : ℝ) * value ^ 2 := by
  induction count with
  | zero =>
      simp
      exact sq_nonneg value
  | succ count ih =>
      rw [Finset.sum_range_succ]
      by_cases hactive : dyadicAmplitudeLevel base count ≤ value
      · rw [if_pos hactive]
        calc
          (∑ amplitude ∈ Finset.range count,
              if dyadicAmplitudeLevel base amplitude ≤ value then
                dyadicAmplitudeLevel base amplitude ^ 2 else 0) +
                dyadicAmplitudeLevel base count ^ 2 ≤
              (∑ amplitude ∈ Finset.range count,
                dyadicAmplitudeLevel base amplitude ^ 2) +
                dyadicAmplitudeLevel base count ^ 2 := by
              gcongr with amplitude hamplitude
              split <;> simp_all only [le_refl, sq_nonneg]
          _ = ∑ amplitude ∈ Finset.range (count + 1),
                dyadicAmplitudeLevel base amplitude ^ 2 := by
              rw [Finset.sum_range_succ]
          _ ≤ (4 / 3 : ℝ) * dyadicAmplitudeLevel base count ^ 2 :=
              sum_range_dyadicAmplitudeLevel_sq_le hbase count
          _ ≤ (4 / 3 : ℝ) * value ^ 2 := by
              have hlevel := dyadicAmplitudeLevel_nonneg hbase count
              gcongr
      · simpa [hactive] using ih

/-! ## Actual spacetime vorticity population -/

/-- [definition] The squared dyadic level multiplied by the actual occupied spacetime volume. -/
def periodicSpacetimeDyadicAmplitudeMass
    (velocity : VelocityField) (source target base : ℝ) (amplitude : ℕ) : ℝ :=
  dyadicAmplitudeLevel base amplitude ^ 2 *
    periodicSpacetimeVorticityAmplitudeSuperlevelMeasure velocity source target
      (dyadicAmplitudeLevel base amplitude)

theorem periodicSpacetimeDyadicAmplitudeMass_nonneg
    (velocity : VelocityField) (source target : ℝ) {base : ℝ} (_hbase : 0 ≤ base)
    (amplitude : ℕ) :
    0 ≤ periodicSpacetimeDyadicAmplitudeMass velocity source target base amplitude := by
  unfold periodicSpacetimeDyadicAmplitudeMass
  exact mul_nonneg (sq_nonneg _) measureReal_nonneg

/-- **[proved-derived] Geometric layer cake on one actual compact spacetime cell.**  Unlike
applying Markov independently at each level, this retains the nested superlevel populations and
therefore has no factor equal to the number of amplitude scales. -/
theorem sum_range_periodicSpacetimeDyadicAmplitudeMass_le_secondMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {source target base : ℝ} (hsource : 0 < source) (htarget : target < T)
    (hbase : 0 ≤ base) (count : ℕ) :
    (∑ amplitude ∈ Finset.range count,
        periodicSpacetimeDyadicAmplitudeMass velocity source target base amplitude) ≤
      (4 / 3 : ℝ) *
        periodicSpacetimeVorticitySecondMoment velocity source target := by
  let μ : Measure (Space × ℝ) :=
    ((volume : Measure Space).prod volume).restrict
      (periodicSpacetimeCell source target)
  let vorticitySq : Space × ℝ → ℝ := fun z ↦
    ‖vorticityField velocity z.1 z.2‖ ^ 2
  let amplitudeIntegrand : ℕ → Space × ℝ → ℝ := fun amplitude z ↦
    if dyadicAmplitudeLevel base amplitude ≤
        ‖vorticityField velocity z.1 z.2‖ then
      dyadicAmplitudeLevel base amplitude ^ 2 else 0
  have hvorticityIntegrable : Integrable vorticitySq μ := by
    change Integrable (fun z : Space × ℝ ↦
      ‖vorticityField velocity z.1 z.2‖ ^ 2)
        (((volume : Measure Space).prod volume).restrict
          (periodicSpacetimeCell source target))
    exact integrableOn_norm_vorticity_sq_spacetimeCell solution hsource htarget
  have hlevelNonneg (amplitude : ℕ) :
      0 ≤ dyadicAmplitudeLevel base amplitude :=
    dyadicAmplitudeLevel_nonneg hbase amplitude
  have hsuperlevelNullMeasurable (amplitude : ℕ) :
      NullMeasurableSet
        {z : Space × ℝ | dyadicAmplitudeLevel base amplitude ≤
          ‖vorticityField velocity z.1 z.2‖} μ := by
    have hsets :
        {z : Space × ℝ | dyadicAmplitudeLevel base amplitude ≤
            ‖vorticityField velocity z.1 z.2‖} =
          {z : Space × ℝ | dyadicAmplitudeLevel base amplitude ^ 2 ≤
            vorticitySq z} := by
      ext z
      exact (sq_le_sq₀ (hlevelNonneg amplitude) (norm_nonneg _)).symm
    rw [hsets]
    exact nullMeasurableSet_le aemeasurable_const
      hvorticityIntegrable.aestronglyMeasurable.aemeasurable
  have hamplitudeIntegrable (amplitude : ℕ) :
      Integrable (amplitudeIntegrand amplitude) μ := by
    refine Integrable.mono hvorticityIntegrable ?_ ?_
    · let superlevel : Set (Space × ℝ) :=
        {z : Space × ℝ | dyadicAmplitudeLevel base amplitude ≤
          ‖vorticityField velocity z.1 z.2‖}
      have hfun : amplitudeIntegrand amplitude =
          superlevel.indicator
            (fun _ : Space × ℝ ↦ dyadicAmplitudeLevel base amplitude ^ 2) := by
        funext z
        simp [amplitudeIntegrand, superlevel, Set.indicator]
      rw [hfun]
      exact aestronglyMeasurable_const.indicator₀
        (hsuperlevelNullMeasurable amplitude)
    · filter_upwards with z
      unfold amplitudeIntegrand vorticitySq
      by_cases hactive : dyadicAmplitudeLevel base amplitude ≤
          ‖vorticityField velocity z.1 z.2‖
      · rw [if_pos hactive]
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
          (sq_le_sq₀ (hlevelNonneg amplitude) (norm_nonneg _) |>.2 hactive)
      · simp [hactive]
  have hintegral_eq_mass (amplitude : ℕ) :
      (∫ z, amplitudeIntegrand amplitude z ∂μ) =
        periodicSpacetimeDyadicAmplitudeMass velocity source target base amplitude := by
    let superlevel : Set (Space × ℝ) :=
      {z : Space × ℝ | dyadicAmplitudeLevel base amplitude ≤
        ‖vorticityField velocity z.1 z.2‖}
    have hfun : amplitudeIntegrand amplitude =
        superlevel.indicator
          (fun _ : Space × ℝ ↦ dyadicAmplitudeLevel base amplitude ^ 2) := by
      funext z
      simp [amplitudeIntegrand, superlevel, Set.indicator]
    rw [hfun, integral_indicator₀ (hsuperlevelNullMeasurable amplitude)]
    simp only [MeasureTheory.integral_const, smul_eq_mul]
    unfold periodicSpacetimeDyadicAmplitudeMass
      periodicSpacetimeVorticityAmplitudeSuperlevelMeasure
    simp only [μ, measureReal_restrict_apply_univ, mul_comm]
  calc
    (∑ amplitude ∈ Finset.range count,
        periodicSpacetimeDyadicAmplitudeMass velocity source target base amplitude) =
        ∫ z, ∑ amplitude ∈ Finset.range count,
          amplitudeIntegrand amplitude z ∂μ := by
      rw [integral_finsetSum (Finset.range count)
        (fun amplitude _hamplitude ↦ hamplitudeIntegrable amplitude)]
      exact Finset.sum_congr rfl fun amplitude _hamplitude ↦
        (hintegral_eq_mass amplitude).symm
    _ ≤ ∫ z, (4 / 3 : ℝ) * vorticitySq z ∂μ := by
      apply integral_mono
      · exact integrable_finsetSum (Finset.range count)
          (fun amplitude _hamplitude ↦ hamplitudeIntegrable amplitude)
      · exact hvorticityIntegrable.const_mul (4 / 3 : ℝ)
      · intro z
        exact sum_range_dyadicAmplitudeIndicator_le hbase (norm_nonneg _) count
    _ = (4 / 3 : ℝ) *
        periodicSpacetimeVorticitySecondMoment velocity source target := by
      rw [integral_const_mul]
      rfl

/-- The complete dyadic amplitude packing population is summable on every compact interior
spacetime cell. -/
theorem summable_periodicSpacetimeDyadicAmplitudeMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {source target base : ℝ} (hsource : 0 < source) (htarget : target < T)
    (hbase : 0 ≤ base) :
    Summable (periodicSpacetimeDyadicAmplitudeMass velocity source target base) := by
  apply summable_of_sum_range_le
  · exact periodicSpacetimeDyadicAmplitudeMass_nonneg velocity source target hbase
  · exact sum_range_periodicSpacetimeDyadicAmplitudeMass_le_secondMoment
      solution hsource htarget hbase

/-- The sharp geometric layer-cake bound for the complete dyadic amplitude population. -/
theorem tsum_periodicSpacetimeDyadicAmplitudeMass_le_secondMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {source target base : ℝ} (hsource : 0 < source) (htarget : target < T)
    (hbase : 0 ≤ base) :
    (∑' amplitude : ℕ,
        periodicSpacetimeDyadicAmplitudeMass velocity source target base amplitude) ≤
      (4 / 3 : ℝ) *
        periodicSpacetimeVorticitySecondMoment velocity source target := by
  apply Real.tsum_le_of_sum_range_le
  · exact periodicSpacetimeDyadicAmplitudeMass_nonneg velocity source target hbase
  · exact sum_range_periodicSpacetimeDyadicAmplitudeMass_le_secondMoment
      solution hsource htarget hbase

/-! ## Tensor product with the actual Hodge tail -/

/-- [definition] The two-scale packing receiver: inverse-fourth-root Hodge scale crossed with
dyadic squared-amplitude occupancy. -/
def packedHodgeAmplitudeCellMass
    (velocity : VelocityField) (source target base : ℝ)
    (index : ℕ × ℕ) : ℝ :=
  inverseFourthRootDyadicTailWeight index.1 *
    periodicSpacetimeDyadicAmplitudeMass velocity source target base index.2

theorem packedHodgeAmplitudeCellMass_nonneg
    (velocity : VelocityField) (source target : ℝ) {base : ℝ} (hbase : 0 ≤ base)
    (index : ℕ × ℕ) :
    0 ≤ packedHodgeAmplitudeCellMass velocity source target base index := by
  exact mul_nonneg (inverseFourthRootDyadicTailWeight_nonneg index.1)
    (periodicSpacetimeDyadicAmplitudeMass_nonneg
      velocity source target hbase index.2)

/-- **[proved-derived; formal-checked] Unconditional double-scale summability.** -/
theorem summable_packedHodgeAmplitudeCellMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {source target base : ℝ} (hsource : 0 < source) (htarget : target < T)
    (hbase : 0 ≤ base) :
    Summable (packedHodgeAmplitudeCellMass velocity source target base) := by
  unfold packedHodgeAmplitudeCellMass
  exact summable_inverseFourthRootDyadicTailWeight.mul_of_nonneg
    (summable_periodicSpacetimeDyadicAmplitudeMass
      solution hsource htarget hbase)
    inverseFourthRootDyadicTailWeight_nonneg
    (periodicSpacetimeDyadicAmplitudeMass_nonneg velocity source target hbase)

/-- The complete two-scale population is bounded by the Hodge tail mass times the exact
spacetime vorticity second moment. -/
theorem tsum_packedHodgeAmplitudeCellMass_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {source target base : ℝ} (hsource : 0 < source) (htarget : target < T)
    (hbase : 0 ≤ base) :
    (∑' index : ℕ × ℕ,
        packedHodgeAmplitudeCellMass velocity source target base index) ≤
      inverseFourthRootDyadicTailMass *
        ((4 / 3 : ℝ) *
          periodicSpacetimeVorticitySecondMoment velocity source target) := by
  have hamplitude := summable_periodicSpacetimeDyadicAmplitudeMass
    solution hsource htarget hbase
  have hproduct := summable_packedHodgeAmplitudeCellMass
    solution hsource htarget hbase
  calc
    (∑' index : ℕ × ℕ,
        packedHodgeAmplitudeCellMass velocity source target base index) =
        inverseFourthRootDyadicTailMass *
          ∑' amplitude : ℕ,
            periodicSpacetimeDyadicAmplitudeMass
              velocity source target base amplitude := by
      simpa [packedHodgeAmplitudeCellMass, inverseFourthRootDyadicTailMass] using
        (summable_inverseFourthRootDyadicTailWeight.tsum_mul_tsum
          hamplitude hproduct).symm
    _ ≤ inverseFourthRootDyadicTailMass *
        ((4 / 3 : ℝ) *
          periodicSpacetimeVorticitySecondMoment velocity source target) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_periodicSpacetimeDyadicAmplitudeMass_le_secondMoment
          solution hsource htarget hbase)
        inverseFourthRootDyadicTailMass_nonneg

/-! ## Reconstruction boundary

The preceding tensor product is deliberately not identified with the physical Hodge stretching
word.  The exact Young square in `NavierStokesDissipationHodgeInteraction` returns the quartic
population `∫ |ω|⁴`.  Its dyadic layer-cake chart carries `level⁴ * measure(superlevel)`, which is
`level²` times the packing term proved here.  The Hodge weight has an independent scale index, and
no proved owner relates that index to the amplitude index.  Consequently the summable Hodge tail
cannot pay the missing growing `level²` factor.
-/

section Audit

#print axioms sum_range_periodicSpacetimeDyadicAmplitudeMass_le_secondMoment
#print axioms summable_periodicSpacetimeDyadicAmplitudeMass
#print axioms tsum_periodicSpacetimeDyadicAmplitudeMass_le_secondMoment
#print axioms summable_packedHodgeAmplitudeCellMass
#print axioms tsum_packedHodgeAmplitudeCellMass_le

end Audit

end Soma.Holonics.Millennium.NavierStokesPackedHodgeTerminalSummability
