import ElementaryHolonics.Millennium.HolonicTerminalCurrent
import ElementaryHolonics.Millennium.NavierStokesCriticalVorticityRate
import Mathlib.Topology.Order.Monotone

/-!
# The critical-vorticity accumulation as a terminal holonic current

This file attaches the generic terminal-current calculus to the genuine periodic three-torus
vorticity receiver.  The accumulated mass is clipped below its addressed base time, so it is a
single monotone receiver on the complete incoming terminal filter.

An `OpenAccumulatedCriticalVorticityBudget` makes this receiver bounded above.  Monotonicity plus
that exact bound returns a unique finite terminal accumulated mass, hence a null terminal current.
This closes the scalar accumulation face.  It does **not** reconstruct a terminal velocity field:
that stronger passage still requires a source-specific law transporting this scalar return through
the high-order state carrier and the restart/gluing owner.
-/

noncomputable section

open Filter MeasureTheory Real Set
open scoped BigOperators Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesTerminalCurrent

open Soma.Holonics.Millennium.HolonicTerminalCurrent
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate

/-- [definition] Accumulated genuine critical-vorticity mass from the addressed base.  Times below
`base` are sent to the same base occurrence; this changes no incoming-terminal germ when
`base < terminal`. -/
def accumulatedCriticalVorticityMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (base : ℝ) (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (time : ℝ) : ℝ :=
  ∫ s in base..max base time, criticalVorticityRate solution s

/-- [proved-derived; formal-checked] On an addressed interval above the base, the oriented
accumulation current is exactly the integral of the genuine critical rate across that interval. -/
theorem intervalCurrent_accumulatedCriticalVorticityMass_eq
    {T base nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (hbase : 0 < base) {source target : ℝ}
    (hsource : base ≤ source) (hst : source ≤ target) (htT : target < T) :
    intervalCurrent (accumulatedCriticalVorticityMass base solution) source target =
      ∫ time in source..target, criticalVorticityRate solution time := by
  have hcontinuousBaseSource : ContinuousOn (criticalVorticityRate solution) (Icc base source) :=
    (continuousOn_criticalVorticityRate_tail solution hbase).mono (by
      intro time htime
      exact ⟨htime.1, lt_of_le_of_lt (htime.2.trans hst) htT⟩)
  have hcontinuousSourceTarget : ContinuousOn (criticalVorticityRate solution) (Icc source target) :=
    (continuousOn_criticalVorticityRate_tail solution hbase).mono (by
      intro time htime
      exact ⟨hsource.trans htime.1, lt_of_le_of_lt htime.2 htT⟩)
  have hbaseSource : IntervalIntegrable (criticalVorticityRate solution) volume base source :=
    hcontinuousBaseSource.intervalIntegrable_of_Icc hsource
  have hsourceTarget : IntervalIntegrable (criticalVorticityRate solution) volume source target :=
    hcontinuousSourceTarget.intervalIntegrable_of_Icc hst
  change (∫ time in base..max base target, criticalVorticityRate solution time) -
      (∫ time in base..max base source, criticalVorticityRate solution time) = _
  rw [max_eq_right hsource, max_eq_right (hsource.trans hst)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hbaseSource hsourceTarget]
  ring

/-- [proved-derived; formal-checked] Every finite sampling of the accumulated critical current
glues to its one exterior returned difference. -/
theorem finitePartition_accumulatedCriticalVorticityMass_eq_exterior
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (base : ℝ) (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (time : ℕ → ℝ) (pieces : ℕ) :
    (∑ piece ∈ Finset.range pieces,
      intervalCurrent (accumulatedCriticalVorticityMass base solution)
        (time piece) (time (piece + 1))) =
      intervalCurrent (accumulatedCriticalVorticityMass base solution)
        (time 0) (time pieces) :=
  finitePartitionCurrent_eq_exterior _ _ _

/-- [proved-derived; formal-checked] Nonnegativity of the genuine critical rate makes its
accumulation monotone throughout the incoming terminal carrier. -/
theorem monotoneOn_accumulatedCriticalVorticityMass
    {T base nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (hbase : 0 < base) (hbaseT : base < T) :
    MonotoneOn (accumulatedCriticalVorticityMass base solution) (Iio T) := by
  intro source hsourceT target htargetT hst
  have hmaxTargetT : max base target < T := max_lt hbaseT htargetT
  have hcontinuous : ContinuousOn (criticalVorticityRate solution) (Icc base (max base target)) :=
    (continuousOn_criticalVorticityRate_tail solution hbase).mono (by
      intro time htime
      exact ⟨htime.1, lt_of_le_of_lt htime.2 hmaxTargetT⟩)
  have hintegrable : IntervalIntegrable (criticalVorticityRate solution) volume
      base (max base target) :=
    hcontinuous.intervalIntegrable_of_Icc (le_max_left _ _)
  unfold accumulatedCriticalVorticityMass
  exact intervalIntegral.integral_mono_interval
    le_rfl (le_max_left _ _) (max_le_max_left base hst)
    (Eventually.of_forall fun time ↦ criticalVorticityRate_nonneg solution time)
    hintegrable

/-- [proved-derived; formal-checked] The declared open critical-vorticity budget bounds the whole
incoming image of the clipped accumulation receiver. -/
theorem bddAbove_accumulatedCriticalVorticityMass_image
    {T base M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (hbaseT : base < T)
    (budget : OpenAccumulatedCriticalVorticityBudget (a := base) solution M) :
    BddAbove (accumulatedCriticalVorticityMass base solution '' Iio T) := by
  refine ⟨M, ?_⟩
  rintro mass ⟨time, htimeT, rfl⟩
  by_cases htime : base ≤ time
  · simpa [accumulatedCriticalVorticityMass, max_eq_right htime] using
      budget.accumulated_le time ⟨htime, htimeT⟩
  · have hM : 0 ≤ M := by
      simpa using budget.accumulated_le base ⟨le_rfl, hbaseT⟩
    simpa [accumulatedCriticalVorticityMass, max_eq_left (le_of_not_ge htime)] using hM

/-- [proved-derived; formal-checked] A finite open critical-vorticity budget returns a concrete
terminal accumulated mass from the incoming side. -/
theorem exists_terminalAccumulatedCriticalVorticityMass
    {T base M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (hbase : 0 < base) (hbaseT : base < T)
    (budget : OpenAccumulatedCriticalVorticityBudget (a := base) solution M) :
    ∃ terminalMass,
      Tendsto (accumulatedCriticalVorticityMass base solution)
        (incomingTerminalFilter T) (nhds terminalMass) := by
  refine ⟨sSup (accumulatedCriticalVorticityMass base solution '' Iio T), ?_⟩
  exact (monotoneOn_accumulatedCriticalVorticityMass solution hbase hbaseT).tendsto_nhdsLT
    (bddAbove_accumulatedCriticalVorticityMass_image hbaseT budget)

/-- [proved-derived; formal-checked] Therefore the accumulated critical-vorticity carrier lies in
the terminal null cone.  This is the exact terminal-concentration statement supplied by the
existing budget. -/
theorem hasNullTerminalCurrentAt_accumulatedCriticalVorticityMass
    {T base M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (hbase : 0 < base) (hbaseT : base < T)
    (budget : OpenAccumulatedCriticalVorticityBudget (a := base) solution M) :
    HasNullTerminalCurrentAt T (accumulatedCriticalVorticityMass base solution) := by
  rcases exists_terminalAccumulatedCriticalVorticityMass hbase hbaseT budget with
    ⟨terminalMass, returned⟩
  exact hasNullTerminalCurrentAt_of_tendsto returned

/-- [proved-derived; formal-checked] The terminal accumulated mass is unique, not merely selected. -/
theorem existsUnique_terminalAccumulatedCriticalVorticityMass
    {T base M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (hbase : 0 < base) (hbaseT : base < T)
    (budget : OpenAccumulatedCriticalVorticityBudget (a := base) solution M) :
    ∃! terminalMass,
      Tendsto (accumulatedCriticalVorticityMass base solution)
        (incomingTerminalFilter T) (nhds terminalMass) :=
  hasNullTerminalCurrentAt_iff_existsUnique_terminalTrace.mp
    (hasNullTerminalCurrentAt_accumulatedCriticalVorticityMass hbase hbaseT budget)

section Audit

#print axioms intervalCurrent_accumulatedCriticalVorticityMass_eq
#print axioms finitePartition_accumulatedCriticalVorticityMass_eq_exterior
#print axioms exists_terminalAccumulatedCriticalVorticityMass
#print axioms hasNullTerminalCurrentAt_accumulatedCriticalVorticityMass
#print axioms existsUnique_terminalAccumulatedCriticalVorticityMass

end Audit

end Soma.Holonics.Millennium.NavierStokesTerminalCurrent
