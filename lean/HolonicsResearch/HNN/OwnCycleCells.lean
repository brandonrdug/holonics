import Mathlib

/-!
# A cell of whole periods counts its source's pulses once, a frame's count beats, and counts cross a join one for one

Atlas: `aeon.own-cycle-cell-counts-once`, `pair.count-crosses-a-join-one-for-one`. Record:
`research/records/2026-11-26_A_READER_HOLDS_A_STREAM_AS_NESTED_CYCLES_IT_LOCATES_…`.

The owners that stand in the tree, named where each is used: the count of one cycle's ticks against another's, kept by every
re-timing (`aeon.count-survives-every-retiming`), a level's sites as the landmarks of its news (`code.site-isolation-landmark`),
a crossing's answer at the sum and the difference of two rates (`pair.crossing-sum-and-difference`) and the second invariant of
one sign that sends a cascade to the coarse grain (`fluid.one-signed-invariant-bounds-fine-grain`). This module holds the two
finite statements those rows do not.

1. **A cell cut on a source's own periods counts once; a frame's count beats** (`pulses_eq`, `whole_periods_count_once`,
   `frame_count_two_values`, `frame_count_beats`). A source pulses at the multiples of its period `P`. A cell of `m` whole periods
   holds `m` pulses wherever it starts. A frame of `F` places holds `F / P` pulses or one more, by where it starts, and where
   `P` does not divide `F` both counts occur: a reader that cuts by frames is handed a count that moves while the source does
   nothing.
2. **Counts cross a join one for one, and power in the ratio of the rates** (`counts_close_the_power`, `slow_share`,
   `depth_share`). Where three members with `ω₃ = ω₁ + ω₂` exchange counts one for one, their powers `ω N` close, so the count is
   a second kept quantity beside the power; the slow member's share of what the fast one hands down is its rate over the fast
   one's; and through `L` levels of one stride the share is the stride's inverse to the power `L`. A slow level is read by its
   count, in its own unit: as a share of the fast level's power it is small by construction.
-/

namespace Holonics.HNN.OwnCycleCells

open Finset

/-- The pulses of a source of period `P` in the cell `(a, b]`: the multiples of `P` there. -/
def pulses (P a b : ℕ) : ℕ := ((Ioc a b).filter (P ∣ ·)).card

/-- The pulses in `(a, b]` are the difference of the two quotients. -/
theorem pulses_eq (P a b : ℕ) (hab : a ≤ b) : pulses P a b = b / P - a / P := by
  unfold pulses
  have hb := Nat.Ioc_filter_dvd_card_eq_div b P
  have ha := Nat.Ioc_filter_dvd_card_eq_div a P
  have hu : Ioc 0 b = Ioc 0 a ∪ Ioc a b := (Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab).symm
  have hd : Disjoint ((Ioc 0 a).filter (P ∣ ·)) ((Ioc a b).filter (P ∣ ·)) :=
    disjoint_filter_filter (Ioc_disjoint_Ioc_of_le le_rfl)
  rw [hu, filter_union, card_union_of_disjoint hd, ha] at hb
  omega

/-- A cell of `m` whole periods holds exactly `m` pulses, wherever it starts. -/
theorem whole_periods_count_once (P a m : ℕ) (hP : 0 < P) : pulses P a (a + m * P) = m := by
  rw [pulses_eq P a (a + m * P) (Nat.le_add_right a _), Nat.add_mul_div_right a m hP]
  omega

/-- A frame of `F` places holds `F / P` pulses or one more, by where it starts. -/
theorem frame_count_two_values (P a F : ℕ) (hP : 0 < P) :
    pulses P a (a + F) = F / P + if P ≤ a % P + F % P then 1 else 0 := by
  rw [pulses_eq P a (a + F) (Nat.le_add_right a F), Nat.add_div hP, Nat.add_assoc,
    Nat.add_sub_cancel_left]

/-- Where the period does not divide the frame, both counts occur: the frame's count beats under a source that does nothing. -/
theorem frame_count_beats (P F : ℕ) (hP : 0 < P) (hF : ¬ P ∣ F) :
    pulses P 0 F = F / P ∧ pulses P (P - F % P) (P - F % P + F) = F / P + 1 := by
  constructor
  · rw [pulses_eq P 0 F (Nat.zero_le F)]
    simp
  · have h1 : F % P < P := Nat.mod_lt F hP
    have h2 : 0 < F % P := Nat.pos_of_ne_zero (fun h => hF (Nat.dvd_of_mod_eq_zero h))
    have h3 : (P - F % P) % P = P - F % P := Nat.mod_eq_of_lt (by omega)
    have h4 : P ≤ P - F % P + F % P := by omega
    rw [frame_count_two_values P (P - F % P) F hP, h3, if_pos h4]

/-- Where counts are exchanged one for one across a join of rates `ω₃ = ω₁ + ω₂`, the powers `ω N` close (Manley and Rowe). -/
theorem counts_close_the_power {ω₁ ω₂ ω₃ N₁ N₂ N₃ : ℝ} (hω : ω₃ = ω₁ + ω₂)
    (h₁ : N₁ + N₃ = 0) (h₂ : N₂ + N₃ = 0) : ω₁ * N₁ + ω₂ * N₂ + ω₃ * N₃ = 0 := by
  have e₁ : N₁ = -N₃ := by linarith
  have e₂ : N₂ = -N₃ := by linarith
  rw [hω, e₁, e₂]
  ring

/-- The slow member's share of the power the fast one hands down is its rate over the fast one's. -/
theorem slow_share {ω₂ ω₃ n : ℝ} (hn : n ≠ 0) : (ω₂ * n) / (ω₃ * n) = ω₂ / ω₃ :=
  mul_div_mul_right ω₂ ω₃ hn

/-- Through `L` levels of one stride `κ`, a level's share of the first level's power is the stride's inverse to the power `L`. -/
theorem depth_share (κ : ℝ) (L : ℕ) : (1 / κ) ^ L = 1 / κ ^ L :=
  one_div_pow κ L

end Holonics.HNN.OwnCycleCells
