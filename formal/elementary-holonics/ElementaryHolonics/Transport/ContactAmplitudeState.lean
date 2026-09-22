import ElementaryHolonics.Foundation.Standing
import ElementaryHolonics.Foundation.ReceiverHistoryCompression
import ElementaryHolonics.Transport.ContactFactorScale
import Mathlib.Tactic

/-!
# Sufficient state for completed contact-amplitude updates

Completed update sequences are identified by the full current state they produce. This is a
state quotient, not a causal-history archive: the next deterministic action, receiver face and
parameter update are functions of that state. Live producing comparisons are deliberately a
separate operand and are not identified by this quotient.
-/

namespace Soma.Holonics.Transport.ContactAmplitudeState

open Soma.Holonics
open Soma.Holonics.Foundation
open Soma.Holonics.Foundation.Standing
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Transport.ContactFactorScale

variable {Update State Generator Face Parameter : Type*}

structure Machine where
  initial : State
  step : Update → State → State
  action : Generator → State → Face
  parameter : State → Parameter

namespace Machine

variable (M : Machine (Update := Update) (State := State) (Generator := Generator)
  (Face := Face) (Parameter := Parameter))

def run (updates : List Update) : State :=
  updates.foldl (fun state update => M.step update state) M.initial

def transport (update : Update) (state : State) : State := M.step update state

def observe (receiver : Generator) (state : State) : Face := M.action receiver state

def retained (updates : List Update) : State := M.run updates

theorem run_append_one (updates : List Update) (update : Update) :
    M.run (updates ++ [update]) = M.step update (M.run updates) := by
  simp [run, List.foldl_append]

theorem run_transportWord_state (updates : List Update) (word : List Update) :
    transportWord M.step word (M.run updates) = M.run (updates ++ word.reverse) := by
  induction word with
  | nil => simp [run]
  | cons update word ih =>
      simp only [transportWord_cons, List.reverse_cons]
      rw [ih, ← M.run_append_one]
      simp [List.append_assoc]

theorem transportWord_append (updates word : List Update) :
    transportWord (fun update history => history ++ [update]) word updates =
      updates ++ word.reverse := by
  induction word with
  | nil => simp
  | cons update word ih =>
      simp only [transportWord_cons, List.reverse_cons]
      rw [ih]
      simp [List.append_assoc]

theorem same_current_is_future_equivalent {left right : List Update}
    (h : M.retained left = M.retained right) (receiver : Generator) (word : List Update) :
    M.observe receiver
        (transportWord M.transport word (M.retained left)) =
      M.observe receiver
        (transportWord M.transport word (M.retained right)) := by
  rw [h]

theorem same_current_has_same_parameter {left right : List Update}
    (h : M.retained left = M.retained right) :
    M.parameter (M.retained left) = M.parameter (M.retained right) := by
  rw [h]

def completedStanding : StandingLaw Update Generator (List Update) State Face where
  transport := fun update history => history ++ [update]
  observe := fun receiver history => M.observe receiver (M.retained history)
  retain := M.retained
  reopen := fun receiver word state => M.observe receiver (transportWord M.step word state)
  sufficient := by
    intro receiver word history
    simpa only [Machine.retained, transportWord_append] using
      congrArg (M.observe receiver) (M.run_transportWord_state history word)

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

def realizedOperator {m n : Type*} (template : Mat m n) (rho : ℚ) : Mat m n :=
  amplitude rho template

theorem realizedOperator_depends_only_on_current
    {m n : Type*} (template : Mat m n) {rhoLeft rhoRight : ℚ}
    (h : rhoLeft = rhoRight) :
    realizedOperator template rhoLeft = realizedOperator template rhoRight := by
  rw [h]

theorem positive_realizedOperator_scale
    {rho alpha : ℚ}
    (hRho : 0 < rho) (hAlpha : 0 < alpha) :
    0 < alpha * rho :=
  positive_amplitude_proposal hRho hAlpha

end Soma.Holonics.Transport.ContactAmplitudeState
