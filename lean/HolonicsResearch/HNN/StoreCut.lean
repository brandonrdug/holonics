import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# What a region is handed: a store's state at a cut is sufficient for what stands before it

The record `research/records/2026-11-25_A_REGIONS_FIRST_PLACE_EMPTIES_EVERY_STORE_SO_NO_COMPARED_PLACE_ASKS_A_STORE_FOR_WHAT_STANDS_FAR_BEFORE_IT_A_CUT_COSTS_HER_FORTY_NATS_AND_CONSECUTIVE_STRETCHES_CUT_ONLY_IN_THEIR_SHARP_HEARING_ARE_WHERE_A_STORE_IS_ASKED.md`
(atlas `store.state-at-cut-sufficient`) reads the engine's regions: a region begins with every store
at rest, so a place just past a region's first reads as if nothing stood before it. This file states
what a store run along a strand hands across a cut, on any store of that kind.

A strand is `x : ℕ → α`, a symbol a place. A store run along it holds a state `run step s x t` before
place `t`: the state `s` before the first place, moved by `step` at each place (a ring's moment
`m ↦ U m + E u`, a carry circle's charge `Q ↦ κ b + γ Q`, a level's count of closed epochs). A face is
read through the store's state and a band of the `w` places before it, heard one by one.

[proved-derived; formal-checked] What is proved.

1. **The hand-off law** (`run_from_cut`): a store run from a cut with the state it held there reads
   every later place as the whole strand's run does. A region handed its stores' states at its first
   place is the strand continued.
2. **A store's state at a cut is sufficient for what stands before it** (`state_at_cut_sufficient`):
   two strands that agree from the cut on and whose stores hold one state at the cut hold one state at
   every later place. What stands before a cut reaches the places after it through that state alone.
3. **A face a band past the cut reads nothing before the cut but the state** (`face_past_band`): where a
   face reads the store's state and the `w` places before it, at a place `w` or more past the cut it is
   the same on both strands.
4. **A store emptied at a cut hands nothing on** (`emptied_at_cut`): where the run begins anew at the cut from a state that does not
   depend on what stood before, two strands that agree from the cut on hold one state at every later place. What stands before the
   cut is then in the kernel of every later face, so a quotient sufficient for those faces keeps none of it: the engine's regions
   today, each beginning with every store at rest.
5. **A banded strand costs its band a place** (`banded_pairs_le`, `whole_pairs`): a place that hears
   the `min t w` places before it one by one costs at most `N w` pairs over `N` places, where every
   place heard by every later one costs `N (N − 1) / 2`.

Scope. The state at a cut is a quotient of what stands before it, sufficient for the faces a band past
the cut reads (the retention law at a cut, `Holonics.Foundation.Standing`); a band of places is a part
of the passage kept whole, and is no retention. Not proved here: that a store of the engine keeps what
a face needs (that is read, store by store, by the engine's `ruler_cut`), nor any bound on what a
state of a given width can hold. The ring's moment is the instance proved in
`Holonics.Transport.SourceMoment` (`moment_append_one`).

The computational object is the helical pair interaction along a strand: a pair heard one by one
inside the band, and every pair past it met through a store's state. Of the winding guide's six
general objects this touches the helix (a ring's moment is a strand on it), the tube (a span continued
along its clock) and the tower thread (the level's epochs are a store on the coarser clock); the pair,
faces and placement and the cell holonomy stay attached.

Consumers: the atlas row `store.state-at-cut-sufficient` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.StoreCut

open Finset

variable {α σ β : Type*}

/-- A store run along a strand: its state before place `t`, from the state `s` before place `0`. -/
def run (step : σ → α → σ) (s : σ) (x : ℕ → α) : ℕ → σ
  | 0 => s
  | t + 1 => step (run step s x t) (x t)

@[simp] theorem run_zero (step : σ → α → σ) (s : σ) (x : ℕ → α) : run step s x 0 = s := rfl

theorem run_succ (step : σ → α → σ) (s : σ) (x : ℕ → α) (t : ℕ) :
    run step s x (t + 1) = step (run step s x t) (x t) := rfl

/-- **The hand-off law.** A store run from a cut with the state it held there reads every later
place as the whole strand's run does. -/
theorem run_from_cut (step : σ → α → σ) (s : σ) (x : ℕ → α) (c k : ℕ) :
    run step (run step s x c) (fun i => x (c + i)) k = run step s x (c + k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [run_succ, ih, ← Nat.add_assoc, run_succ]

/-- **A store's state at a cut is sufficient for what stands before it.** Two strands that agree from
place `c` on and whose stores hold one state at `c` hold one state at every later place. -/
theorem state_at_cut_sufficient (step : σ → α → σ) (s s' : σ) (x y : ℕ → α) (c : ℕ)
    (hstate : run step s x c = run step s' y c) (hafter : ∀ i, c ≤ i → x i = y i) (k : ℕ) :
    run step s x (c + k) = run step s' y (c + k) := by
  induction k with
  | zero => exact hstate
  | succ k ih =>
    rw [← Nat.add_assoc, run_succ, run_succ, ih, hafter (c + k) (Nat.le_add_right c k)]

/-- **A store emptied at a cut hands nothing on.** Where the run begins anew at the cut from a state `s₀` that does not depend on what
stood before, two strands that agree from the cut on hold one state at every later place: what stands before the cut is in the
kernel of every later face, and a quotient sufficient for those faces keeps none of it. -/
theorem emptied_at_cut (step : σ → α → σ) (s₀ : σ) (x y : ℕ → α) (c : ℕ)
    (hafter : ∀ i, c ≤ i → x i = y i) (k : ℕ) :
    run step s₀ (fun i => x (c + i)) k = run step s₀ (fun i => y (c + i)) k := by
  have h : (fun i => x (c + i)) = fun i => y (c + i) := funext fun i => hafter _ (Nat.le_add_right c i)
  rw [h]

/-- **A face a band past the cut reads nothing before the cut but the state.** `R` reads the store's
state and the `w` places before the place (`hR`: nothing past the band). -/
theorem face_past_band (step : σ → α → σ) (w : ℕ) (R : σ → (ℕ → α) → β)
    (hR : ∀ q u v, (∀ i, i < w → u i = v i) → R q u = R q v) (s s' : σ) (x y : ℕ → α) (c : ℕ)
    (hstate : run step s x c = run step s' y c) (hafter : ∀ i, c ≤ i → x i = y i) (k : ℕ)
    (hk : w ≤ k) :
    R (run step s x (c + k)) (fun i => x (c + k - 1 - i)) =
      R (run step s' y (c + k)) (fun i => y (c + k - 1 - i)) := by
  rw [state_at_cut_sufficient step s s' x y c hstate hafter k]
  exact hR _ _ _ (fun i hi => hafter _ (by omega))

/-- **A banded strand costs its band a place**: over `N` places, a place hearing the `min t w` places
before it one by one costs at most `N w` pairs. -/
theorem banded_pairs_le (N w : ℕ) : ∑ t ∈ range N, min t w ≤ N * w := by
  calc ∑ t ∈ range N, min t w ≤ ∑ _t ∈ range N, w := sum_le_sum (fun t _ => Nat.min_le_right t w)
    _ = N * w := by simp

/-- Every place heard by every later one: `2 Σ_(t<N) t = N (N − 1)`. -/
theorem whole_pairs (N : ℕ) : (∑ t ∈ range N, t) * 2 = N * (N - 1) :=
  Finset.sum_range_id_mul_two N

/-- A band never costs more than the whole strand heard one by one. -/
theorem banded_le_whole (N w : ℕ) : ∑ t ∈ range N, min t w ≤ ∑ t ∈ range N, t :=
  sum_le_sum (fun t _ => Nat.min_le_left t w)

end Holonics.HNN.StoreCut
