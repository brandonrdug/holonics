import Holonics.Foundation.Standing.Law
import Mathlib.Tactic

/-!
# A fold over updates is sufficient for its own future, and is no retention of the contact material

[definition] This module proves only that the result of a left fold over an update list is
sufficient for that same fold's future: `Machine.run := List.foldl step`, and the `StandingLaw`
instance takes the update list itself as its source type. Every theorem follows from the fold's
definition. It contains no pair, phase or receiver of the Holonic objects.

It is not the standing of the pair machine's contact material. That binding is a `StandingLaw`
whose source is the machine's own chart and whose `retain` is the declared quotient, with the
source fibre's separator as its defect ([the retention contract](../../../docs/ELEMENTARY_OBJECTS.md#the-retention-contract)).
The row `compression.fold-tautology-not-standing` of the atlas is this module's: a fold over an
update list is the tape the retention law refuses, and its sufficiency is a tautology of the fold.

Ported on November 19 from the pre-reset tree (`13f8c734`,
`formal/elementary-holonics/ElementaryHolonics/Transport/ContactAmplitudeState.lean`), whose
theorems the atlas row graded `formal-checked` while no target of the package built them; the
statements and proofs are the same, read against the live `StandingLaw` and `transportWord`.
-/

namespace Holonics.Foundation.FoldStanding

open Holonics.Foundation.Chronology
open Holonics.Foundation.Standing

variable {Update State Generator Face Parameter : Type*}

/-- A machine that folds its updates into one state, with a receiver's action and a parameter read. -/
structure Machine (Update State Generator Face Parameter : Type*) where
  initial : State
  step : Update → State → State
  action : Generator → State → Face
  parameter : State → Parameter

namespace Machine

variable (M : Machine Update State Generator Face Parameter)

/-- The left fold of the updates from the initial state. -/
def run (updates : List Update) : State :=
  updates.foldl (fun state update => M.step update state) M.initial

/-- One update's transport. -/
def transport (update : Update) (state : State) : State := M.step update state

/-- A receiver's face of a state. -/
def observe (receiver : Generator) (state : State) : Face := M.action receiver state

/-- The retained state: the fold itself. -/
def retained (updates : List Update) : State := M.run updates

/-- [proved-derived; formal-checked] One more update is one more step of the fold. -/
theorem run_append_one (updates : List Update) (update : Update) :
    M.run (updates ++ [update]) = M.step update (M.run updates) := by
  simp [run, List.foldl_append]

/-- [proved-derived; formal-checked] A transport word on the folded state is the fold of the
updates followed by the word, read in the word's own order (right to left). -/
theorem run_transportWord_state (updates : List Update) (word : List Update) :
    transportWord M.step word (M.run updates) = M.run (updates ++ word.reverse) := by
  induction word with
  | nil => simp [run]
  | cons update word ih =>
      simp only [transportWord_cons, List.reverse_cons]
      rw [ih, ← M.run_append_one]
      simp [List.append_assoc]

/-- [proved-derived; formal-checked] Appending a word to the history, letter by letter, appends
its reverse. -/
theorem transportWord_append_history (updates word : List Update) :
    transportWord (fun update history => history ++ [update]) word updates =
      updates ++ word.reverse := by
  induction word with
  | nil => simp
  | cons update word ih =>
      simp only [transportWord_cons, List.reverse_cons]
      rw [ih]
      simp [List.append_assoc]

/-- [proved-derived; formal-checked] Equal folded states give every future face alike. -/
theorem same_current_is_future_equivalent {left right : List Update}
    (h : M.retained left = M.retained right) (receiver : Generator) (word : List Update) :
    M.observe receiver (transportWord M.transport word (M.retained left)) =
      M.observe receiver (transportWord M.transport word (M.retained right)) := by
  rw [h]

/-- [proved-derived; formal-checked] Equal folded states give the same parameter. -/
theorem same_current_has_same_parameter {left right : List Update}
    (h : M.retained left = M.retained right) :
    M.parameter (M.retained left) = M.parameter (M.retained right) := by
  rw [h]

/-- [proved-derived; formal-checked] The fold, with the update list as its source, is a
`StandingLaw`: its sufficiency holds by the fold's definition alone. -/
def completedStanding : StandingLaw Update Generator (List Update) State Face where
  transport := fun update history => history ++ [update]
  observe := fun receiver history => M.observe receiver (M.retained history)
  retain := M.retained
  reopen := fun receiver word state => M.observe receiver (transportWord M.step word state)
  sufficient := by
    intro receiver word history
    simpa only [Machine.retained, transportWord_append_history] using
      congrArg (M.observe receiver) (M.run_transportWord_state history word)

/-- [proved-derived; formal-checked] A completed fold needs no history: equal folded states agree
on the parameter and on every future face. -/
theorem completed_updates_need_no_history {left right : List Update}
    (h : M.retained left = M.retained right) :
    M.parameter (M.retained left) = M.parameter (M.retained right) ∧
      ∀ receiver word,
        M.observe receiver (transportWord M.transport word (M.retained left)) =
          M.observe receiver (transportWord M.transport word (M.retained right)) := by
  refine ⟨M.same_current_has_same_parameter h, ?_⟩
  intro receiver word
  exact M.same_current_is_future_equivalent h receiver word

end Machine

end Holonics.Foundation.FoldStanding
