import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# A region read one-sided continues by a site: its kept states stand, and a reply costs one forward

The record `research/records/2026-11-24_A_LAPS_CARD_TIME_WAS_ITS_READS_THE_HELD_READ_RAN_ONE_FORWARD_FOUR_TIMES_A_ONE_SIDED_REGION_CONTINUES_BY_A_SITE_AND_A_READ_IS_SIZED_BY_THE_SCATTER_BETWEEN_LAPS.md`
(§4, atlas `tower.one-sided-region-continues-by-a-site`) reads the engine's writer (`athena`'s
`write-next`): at every place it writes it rebuilds its whole region and runs the whole forward to
read one face. Under a known stream (atlas `tower.region-known-stream`, `tower.region-strand`,
`tower.level-before`) a site's state is a function of the symbols up to its own place. This file
states what follows on any tick of that kind.

A passage is `x : ℕ → α`, a symbol a place; a tick `F` gives every site a state from the passage's
states, and a forward is `F` iterated. `OneSided F` says that the state `F` gives site `t` is fixed by
the states of the sites up to `t`.

[proved-derived; formal-checked] What is proved.

1. **One-sided ticks compose** (`OneSided.comp`, `OneSided.iterate`): a tick after a one-sided tick is
   one-sided, so a forward of any count of ticks is.
2. **The kept states stand** (`kept_states_stand`): two passages that agree up to place `n` hold the
   same state at every site up to `n` after every count of ticks. A passage continued past `n` moves no
   state kept at its first `n` sites, at any tick: the states of the sites that stand are a retention
   sufficient for every continuation, which is the retention law read on a passage's own order.
3. **A face read one-sided stands** (`face_stands`): a one-sided reading of the forward at a place up
   to `n` is the same on both passages, so a face read once is never read again.
4. **A continued reply costs one forward of the finished region** (`continued_pairs`): with a forward of
   `m` sites counted as `m²` pairs (every site with every site, as the card stages a region), a site
   joining `m` sites pairs with each of them both ways and with itself, `2m + 1` pairs, and
   `m² + Σ_(k<R) (2(m + k) + 1) = (m + R)²`.
5. **A replayed reply costs at least `R` forwards of the prompt** (`replayed_pairs_ge`,
   `continued_le_replayed`): reading the forward anew at each of `R` places costs
   `Σ_(k<R) (m + k + 1)² ≥ R (m + 1)²`, and the continued count never exceeds it.

Not proved here: that the engine's built tick is one-sided in this sense in every part (its still
heads, crowds, circles and the level's hand-on are stated so in their atlas rows and are read on the
card by the bits of a continued forward against a replayed one).

The computational object is the helical pair interaction along a strand: a site's contacts reach only
the sites that have arrived. Of the winding guide's six general objects this touches the helix (a
passage's order) and the tube (a span continued along its clock); the pair, faces and placement, the
cell holonomy and the tower thread stay attached.

Consumers: the atlas row `tower.one-sided-region-continues-by-a-site` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ContinuedRegion

open Finset

variable {α β γ : Type*}

/-- A tick is one-sided: the state it gives site `t` is fixed by the states of the sites up to `t`. -/
def OneSided (F : (ℕ → α) → ℕ → β) : Prop :=
  ∀ x y : ℕ → α, ∀ t : ℕ, (∀ i, i ≤ t → x i = y i) → F x t = F y t

/-- A tick after a one-sided tick is one-sided. -/
theorem OneSided.comp {F : (ℕ → α) → ℕ → β} {G : (ℕ → β) → ℕ → γ}
    (hF : OneSided F) (hG : OneSided G) : OneSided (fun x => G (F x)) := by
  intro x y t h
  apply hG
  intro i hi
  exact hF x y i (fun j hj => h j (le_trans hj hi))

/-- A forward of any count of one-sided ticks is one-sided. -/
theorem OneSided.iterate {F : (ℕ → α) → ℕ → α} (hF : OneSided F) (k : ℕ) :
    OneSided (F^[k]) := by
  induction k with
  | zero =>
    intro x y t h
    simpa using h t le_rfl
  | succ k ih =>
    intro x y t h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (F x) (F y) t (fun i hi => hF x y i (fun j hj => h j (le_trans hj hi)))

/-- **The kept states stand.** Two passages that agree up to place `n` hold the same state at every
site up to `n` after every count of ticks: continuing a passage moves no state kept at the sites that
stand. -/
theorem kept_states_stand {F : (ℕ → α) → ℕ → α} (hF : OneSided F) (x y : ℕ → α) (n : ℕ)
    (h : ∀ i, i ≤ n → x i = y i) (k t : ℕ) (ht : t ≤ n) : F^[k] x t = F^[k] y t :=
  hF.iterate k x y t (fun i hi => h i (le_trans hi ht))

/-- **A face read one-sided stands.** A one-sided reading of the forward at a place up to `n` is the
same on two passages that agree up to `n`. -/
theorem face_stands {F : (ℕ → α) → ℕ → α} {R : (ℕ → α) → ℕ → γ} (hF : OneSided F)
    (hR : OneSided R) (x y : ℕ → α) (n : ℕ) (h : ∀ i, i ≤ n → x i = y i) (k t : ℕ)
    (ht : t ≤ n) : R (F^[k] x) t = R (F^[k] y) t :=
  ((hF.iterate k).comp hR) x y t (fun i hi => h i (le_trans hi ht))

/-- **A continued reply costs one forward of the finished region.** A site joining `m + k` sites adds
`2 (m + k) + 1` pairs, and `R` such sites after `m` bring the count to `(m + R)²`. -/
theorem continued_pairs (m R : ℕ) :
    m ^ 2 + ∑ k ∈ range R, (2 * (m + k) + 1) = (m + R) ^ 2 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ, ← add_assoc, ih]
    ring

/-- **A replayed reply costs at least `R` forwards of the prompt with its first place.** -/
theorem replayed_pairs_ge (m R : ℕ) :
    R * (m + 1) ^ 2 ≤ ∑ k ∈ range R, (m + k + 1) ^ 2 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ, Nat.succ_mul]
    have h : (m + 1) ^ 2 ≤ (m + R + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact Nat.add_le_add ih h

/-- The continued count never exceeds the replayed one: each place's `2 (m + k) + 1` new pairs are
among the `(m + k + 1)²` a forward read anew counts there. -/
theorem continued_le_replayed (m R : ℕ) :
    ∑ k ∈ range R, (2 * (m + k) + 1) ≤ ∑ k ∈ range R, (m + k + 1) ^ 2 := by
  apply sum_le_sum
  intro k _
  nlinarith [Nat.zero_le (m + k)]

end Holonics.HNN.ContinuedRegion
