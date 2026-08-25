import ElementaryHolonics.Millennium.HolonicDifferenceCalculus
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Terminal current: exact partition gluing and receiver reconstruction

For a receiver-valued state `state`, the current across an addressed time interval is the oriented
difference `state target - state source`.  A finite time partition glues exactly because all
internal faces cancel.  Near a terminal face `T`, the null-current condition is the Cauchy
condition on the left-neighbourhood filter: every sufficiently late pair of receiver occurrences
has arbitrarily small returned difference.

In a complete separated receiver, terminal nullity reconstructs one unique terminal value.  This
is the exact local-to-global law; it does not assert that a particular physical current is null.
That attachment must be proved from its constitutive law.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Soma.Holonics.Millennium.HolonicTerminalCurrent

/-! ## Oriented interval current and finite gluing -/

variable {G : Type*} [AddCommGroup G]

/-- [definition] The receiver difference transported across one addressed interval. -/
def intervalCurrent (state : ℝ → G) (source target : ℝ) : G :=
  state target - state source

/-- [proved-derived; formal-checked] Reversal changes only the orientation of the current. -/
theorem intervalCurrent_reverse (state : ℝ → G) (source target : ℝ) :
    intervalCurrent state target source = -intervalCurrent state source target := by
  simp [intervalCurrent]

/-- [proved-derived; formal-checked] Currents through two adjacent intervals glue exactly. -/
theorem intervalCurrent_glue (state : ℝ → G) (a b c : ℝ) :
    intervalCurrent state a b + intervalCurrent state b c = intervalCurrent state a c := by
  simp [intervalCurrent]

/-- [proved-derived; formal-checked] Every internal face of a finite addressed time partition
cancels.  No ordering or equal-spacing assumption on `time` is needed for this algebraic law. -/
theorem finitePartitionCurrent_eq_exterior
    (state : ℝ → G) (time : ℕ → ℝ) (pieces : ℕ) :
    (∑ piece ∈ Finset.range pieces,
      intervalCurrent state (time piece) (time (piece + 1))) =
      intervalCurrent state (time 0) (time pieces) := by
  simpa [intervalCurrent] using
    (Soma.Holonics.finite_telescoping (fun piece ↦ state (time piece)) pieces)

/-! ## Terminal null cone and reconstruction -/

/-- [definition] The incoming time filter at `terminal`; it contains only occurrences strictly
before the terminal face. -/
def incomingTerminalFilter (terminal : ℝ) : Filter ℝ :=
  nhdsWithin terminal (Iio terminal)

/-- [definition] A state lies in the terminal null cone when its receiver differences vanish on
the incoming terminal filter, expressed exactly as the Cauchy condition. -/
def HasNullTerminalCurrentAt {X : Type*} [UniformSpace X]
    (terminal : ℝ) (state : ℝ → X) : Prop :=
  Cauchy ((incomingTerminalFilter terminal).map state)

/-- [proved-derived; formal-checked] For a normed additive receiver, terminal nullity says exactly
that every sufficiently late pair of incoming occurrences carries an arbitrarily small oriented
interval current.  The sign/orientation is retained inside `intervalCurrent`; the norm is only the
declared nullity receiver. -/
theorem hasNullTerminalCurrentAt_iff_eventually_intervalCurrent
    {X : Type*} [NormedAddCommGroup X] {terminal : ℝ} {state : ℝ → X} :
    HasNullTerminalCurrentAt terminal state ↔
      ∀ ε > 0, ∃ tail ∈ incomingTerminalFilter terminal,
        ∀ source ∈ tail, ∀ target ∈ tail,
          ‖intervalCurrent state source target‖ < ε := by
  constructor
  · intro nullCurrent ε hε
    rcases (Metric.cauchy_iff.mp nullCurrent).2 ε hε with ⟨values, hvalues, hclose⟩
    refine ⟨state ⁻¹' values, hvalues, ?_⟩
    intro source hsource target htarget
    simpa [intervalCurrent, dist_eq_norm, norm_sub_rev] using
      hclose (state source) hsource (state target) htarget
  · intro vanishes
    letI : NeBot (incomingTerminalFilter terminal) := by
      exact nhdsWithin_Iio_neBot le_rfl
    apply Metric.cauchy_iff.mpr
    constructor
    · infer_instance
    · intro ε hε
      rcases vanishes ε hε with ⟨tail, htail, hclose⟩
      refine ⟨state '' tail, ?_, ?_⟩
      · change state ⁻¹' (state '' tail) ∈ incomingTerminalFilter terminal
        filter_upwards [htail] with time htime
        exact ⟨time, htime, rfl⟩
      · rintro _ ⟨source, hsource, rfl⟩ _ ⟨target, htarget, rfl⟩
        simpa [intervalCurrent, dist_eq_norm, norm_sub_rev] using
          hclose source hsource target htarget

/-- [proved-derived; formal-checked] A returned terminal trace forces terminal-current nullity. -/
theorem hasNullTerminalCurrentAt_of_tendsto
    {X : Type*} [UniformSpace X] {terminal : ℝ} {state : ℝ → X} {trace : X}
    (returned : Tendsto state (incomingTerminalFilter terminal) (nhds trace)) :
    HasNullTerminalCurrentAt terminal state := by
  letI : NeBot (incomingTerminalFilter terminal) := by
    exact nhdsWithin_Iio_neBot le_rfl
  exact cauchy_nhds.mono returned

/-- [proved-derived; formal-checked] In a complete receiver, terminal-current nullity reconstructs
a terminal trace. -/
theorem exists_terminalTrace_of_hasNullTerminalCurrentAt
    {X : Type*} [UniformSpace X] [CompleteSpace X]
    {terminal : ℝ} {state : ℝ → X}
    (nullCurrent : HasNullTerminalCurrentAt terminal state) :
    ∃ trace, Tendsto state (incomingTerminalFilter terminal) (nhds trace) := by
  letI : NeBot (incomingTerminalFilter terminal) := by
    exact nhdsWithin_Iio_neBot le_rfl
  exact cauchy_map_iff_exists_tendsto.mp nullCurrent

/-- [proved-derived; formal-checked] A separated receiver assigns at most one value to the
incoming terminal current. -/
theorem terminalTrace_unique
    {X : Type*} [UniformSpace X] [T2Space X]
    {terminal : ℝ} {state : ℝ → X} {left right : X}
    (leftReturned : Tendsto state (incomingTerminalFilter terminal) (nhds left))
    (rightReturned : Tendsto state (incomingTerminalFilter terminal) (nhds right)) :
    left = right := by
  letI : NeBot (incomingTerminalFilter terminal) := by
    exact nhdsWithin_Iio_neBot le_rfl
  exact tendsto_nhds_unique leftReturned rightReturned

/-- [proved-derived; formal-checked] In a complete separated receiver, nullity is equivalent to
existence of one unique terminal trace. -/
theorem hasNullTerminalCurrentAt_iff_existsUnique_terminalTrace
    {X : Type*} [UniformSpace X] [CompleteSpace X] [T2Space X]
    {terminal : ℝ} {state : ℝ → X} :
    HasNullTerminalCurrentAt terminal state ↔
      ∃! trace, Tendsto state (incomingTerminalFilter terminal) (nhds trace) := by
  constructor
  · intro nullCurrent
    rcases exists_terminalTrace_of_hasNullTerminalCurrentAt nullCurrent with ⟨trace, returned⟩
    exact ⟨trace, returned, fun other otherReturned ↦
      terminalTrace_unique otherReturned returned⟩
  · rintro ⟨trace, returned, _unique⟩
    exact hasNullTerminalCurrentAt_of_tendsto returned

section Audit

#print axioms intervalCurrent_reverse
#print axioms intervalCurrent_glue
#print axioms finitePartitionCurrent_eq_exterior
#print axioms hasNullTerminalCurrentAt_iff_eventually_intervalCurrent
#print axioms exists_terminalTrace_of_hasNullTerminalCurrentAt
#print axioms hasNullTerminalCurrentAt_iff_existsUnique_terminalTrace

end Audit

end Soma.Holonics.Millennium.HolonicTerminalCurrent
