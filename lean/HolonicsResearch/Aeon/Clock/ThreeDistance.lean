import Mathlib
import Holonics.Aeon.Clock.CarryWord

/-!
# Three distances: the gaps a clock's first readings cut on its circle

[definition] Source: §5 of
`research/records/2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS.md`
(the atlas row `rotation.three-distance`), the closing `[open]` paragraph of
`Holonics/Aeon/Clock/CarryWord` (the three-distance theorem of Sós, Świerczkowski and Surányi,
1958), the row `aeon.three-distance-open`, and the fifths' gaps in the ratio chart of
`research/records/2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md`
(`rotation.fifth-gap-recursion`, whose scope left every `N` to Lean).

A rate-`α` clock read at the unit clock's first `n + 1` sections leaves the open phases
`{iα}`, `0 ≤ i ≤ n`, on the circle. The **forward arc** from the reading `i` to the reading `j`
depends on `i − j` alone; write it `d (i − j)`, a value in `(0, L]` with `L` the whole turn (the
whole turn where the two readings coincide). The **gap after** the reading `i` is the least
forward arc from it, `gap d n i = min_(j ≤ n) d (i − j)`.

[proved-derived; formal-checked] What is proved.

1. **The shift argument on an order alone** (`Arcs`, `gap_succ`, `gap_mem`). Let `d : ℤ → G` take
   values in a linear order with a composition `comb`, and suppose: `d 0` is greatest; an arc that
   holds a shorter one from the same start is their composition, and its other part is shorter too
   (`split`); and a point inside a part is inside the whole (`between`). Then the gap after `i + 1`
   is the gap after `i`, or the gap after the last reading, or the composition of the gap after the
   first reading with the gap after the last. So every gap is one of

   `gap d n 0`,  `gap d n n`,  `comb (gap d n 0) (gap d n n)`

   (`gap_mem`), and the gaps take at most three values (`card_gaps_le_three`). The gap after the
   last reading is the gap before the first (`gap_last`). No hypothesis asks the readings to be
   distinct: coincident readings are a whole turn apart in `d`.
2. **Two bridges.** In an ordered commutative ring, arcs in `(0, L]` that add up to the arc of the
   sum or to it plus `L` satisfy `Arcs` with `comb = +` (`arcs_of_add`). In an ordered field, ratios
   in `(1, L]` that multiply to the ratio of the sum or to it times `L` satisfy `Arcs` with
   `comb = ·` (`arcs_of_mul`).
3. **A real rate, every `α` and every `n`** (`three_distance`, `card_gaps_le_three_real`). With
   `fwd α k = 1 − fract (kα)` the gaps of `{iα}`, `i ≤ n`, are the gap after the first reading, the
   gap after the last, or their sum, so where three lengths occur the largest is the sum of the
   other two (`three_distance_largest`). `fwd α (i − j)` is the arc from `{iα}` forward to `{jα}`
   (`fwd_eq_of_lt`, `fwd_eq_of_le`), and it is read on the owner's objects:
   `fwd α k = 1 − openPhase (helixReading α 0 k)` (`fwd_eq_openPhase`). Irrationality is not used.
4. **A finite ring** (`three_distance_ring`, `card_gaps_le_three_ring`). On `ℤ/q` with any step `p`
   the arcs `ringFwd q p k = q − (kp mod q)` give the same statement in integers; the residue is
   `ZMod q`'s (`ringFwd_eq_val`). Coprimality is not used: it only says the first `q` readings are
   distinct.
5. **The ratio chart over factored integers, every `n`** (`three_ratios`,
   `card_gaps_le_three_ratio`). For naturals `a ≥ 1`, `b ≥ 2` the reading `k` is the reduced power
   `a^k / b^e` in `[1, b)`, `e = Int.log b (a^k)` (`reduced`, `reduced_mem`), and the ratio from it
   forward to the origin is `ratioFwd a b k = b^(e + 1) / a^k = b / reduced` in `(1, b]`
   (`ratioFwd_eq`). The neighbour ratios of the first `n + 1` reduced powers take at most three
   values, and the third is the product of the other two. No logarithm of a real number enters:
   `Int.log` is the integer `e` with `b^e ≤ a^k < b^(e + 1)`, and where `e` is given the ratio is
   read with no search (`ratioFwd_of_bounds`). The fifths in the octave are `a = 3`, `b = 2`:
   among five fifths the ratio after the first is `3² : 2³` and after the last `2⁵ : 3³`
   (`fifths_five`), and among twelve the two are the apotome `3⁷ : 2¹¹` and the leimma `2⁸ : 3⁵`
   of `Mathematics/Comma`, with the tone `9 : 8` their product (`fifths_twelve`).

**Limits.** The lengths are not identified with the continued fraction's residues
(`δ_n = |q_n α − p_n|`, and the counts `N = c q_n + q_(n−1) + r` of each length): the statement
here is the three values and their sum. That exactly three, two or one occur at a given `n` is not
decided here. Sturmian factor complexity `n + 1` (Morse–Hedlund 1940) is the sibling module
`Aeon/Clock/SturmianComplexity`.

**Part of the line served.** Navigators: a rate clock; terrain: the unit clock's sections;
landmarks: the nearest readings on each side of the origin, whose arcs are the two short gaps;
kernel and cokernel: none stated here.

The computational object is the helical pair interaction: the unit clock and the rate-`α` clock on
the torus of their joint motion, read on the rate clock's circle. Of the six objects of the winding
guide this module touches the helix (circle + carry: an arc is an open phase's complement), the
pair (the finite ring is the lock's address) and faces and placement (the readings' places on the
circle); cell holonomy, the tube and the tower thread stay attached and are not used here.

Consumers: `Holonics/Aeon/Clock/CarryWord` (its closing paragraph), the atlas rows
`rotation.three-distance`, `aeon.three-distance-open` and `rotation.fifth-gap-recursion`.

No `sorry`, no `axiom`, no `native_decide`.
-/

set_option linter.dupNamespace false

namespace Holonics.Aeon.Clock.ThreeDistance

open Finset

/-! ## 1. The shift argument on an order alone -/

section Core

variable {G : Type*} [LinearOrder G]

/-- [definition] **The gap after the reading `i`** among the readings `0, …, n`: the least forward
arc `d (i − j)` from it, the reading itself counted at the whole turn `d 0`. -/
def gap (d : ℤ → G) (n : ℕ) (i : ℤ) : G :=
  (range (n + 1)).inf' nonempty_range_add_one (fun j : ℕ => d (i - j))

/-- [definition] **The gap before the first reading**: the least forward arc `d k` from a reading
`k ≤ n` to the origin. -/
def pre (d : ℤ → G) (n : ℕ) : G :=
  (range (n + 1)).inf' nonempty_range_add_one (fun k : ℕ => d k)

/-- [proved-derived; formal-checked] The gap after `i` is at most each forward arc from `i`. -/
theorem gap_le (d : ℤ → G) {n j : ℕ} (hj : j ≤ n) (i : ℤ) : gap d n i ≤ d (i - j) :=
  inf'_le (f := fun j : ℕ => d (i - j)) (mem_range.mpr (Nat.lt_succ_of_le hj))

/-- [proved-derived; formal-checked] The gap after `i` is attained at a reading. -/
theorem exists_gap_eq (d : ℤ → G) (n : ℕ) (i : ℤ) : ∃ j : ℕ, j ≤ n ∧ gap d n i = d (i - j) := by
  obtain ⟨j, hj, h⟩ := exists_mem_eq_inf' nonempty_range_add_one (fun j : ℕ => d (i - j))
  exact ⟨j, Nat.lt_succ_iff.mp (mem_range.mp hj), h⟩

/-- [proved-derived; formal-checked] The gap before the origin is at most each arc to it. -/
theorem pre_le (d : ℤ → G) {n k : ℕ} (hk : k ≤ n) : pre d n ≤ d k :=
  inf'_le (f := fun k : ℕ => d k) (mem_range.mpr (Nat.lt_succ_of_le hk))

/-- [proved-derived; formal-checked] The gap before the origin is attained at a reading. -/
theorem exists_pre_eq (d : ℤ → G) (n : ℕ) : ∃ k : ℕ, k ≤ n ∧ pre d n = d k := by
  obtain ⟨k, hk, h⟩ := exists_mem_eq_inf' nonempty_range_add_one (fun k : ℕ => d (k : ℤ))
  exact ⟨k, Nat.lt_succ_iff.mp (mem_range.mp hk), h⟩

/-- [proved-derived; formal-checked] **The gap after the last reading is the gap before the
first**: the reflection `j ↦ n − j` of the readings carries one family of arcs to the other. -/
theorem gap_last (d : ℤ → G) (n : ℕ) : gap d n n = pre d n := by
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk, hpk⟩ := exists_pre_eq d n
    have h := gap_le d (j := n - k) (Nat.sub_le n k) (n : ℤ)
    have e : (n : ℤ) - ((n - k : ℕ) : ℤ) = k := by omega
    rw [e] at h
    rw [hpk]
    exact h
  · obtain ⟨j, hj, hgj⟩ := exists_gap_eq d n n
    have h := pre_le d (n := n) (k := n - j) (Nat.sub_le n j)
    have e : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
    rw [e] at h
    rw [hgj]
    exact h

/-- [definition] **What the shift argument asks of the forward arcs** `d (i − j)` and their
composition `comb`: the whole turn `d 0` is greatest; an arc `d (a + b)` holding the shorter arc
`d a` from the same start is `comb (d a) (d b)`, and its other part is shorter too; and a point
inside a part of an arc is inside the arc. -/
structure Arcs (d : ℤ → G) (comb : G → G → G) : Prop where
  /-- The whole turn is the greatest arc. -/
  le_zero : ∀ k, d k ≤ d 0
  /-- An arc that holds a shorter one from its start is the composition of its two parts. -/
  split : ∀ a b, d a < d (a + b) → d (a + b) = comb (d a) (d b) ∧ d b < d (a + b)
  /-- A point inside the second part of an arc is inside the arc. -/
  between : ∀ u v w, d u < d (u + w) → d v < d w → d (u + v) < d (u + w)

variable {d : ℤ → G} {comb : G → G → G}

/-- [proved-derived; formal-checked] **The shift**: the gap after `i + 1`, moved back one tick, is
the gap after `i`, unless it ends at the origin (then it is the gap before the first reading) or
the moved arc holds the last reading (then it is the gap after the first reading composed with the
gap before it). -/
theorem gap_succ (h : Arcs d comb) {n i : ℕ} (hi : i + 1 ≤ n) :
    gap d n ((i : ℤ) + 1) = gap d n i ∨ gap d n ((i : ℤ) + 1) = pre d n ∨
      gap d n ((i : ℤ) + 1) = comb (gap d n 0) (pre d n) := by
  obtain ⟨j, hj, hgj⟩ := exists_gap_eq d n ((i : ℤ) + 1)
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · -- the gap ends at the origin
    right; left
    have hg : gap d n ((i : ℤ) + 1) = d ((i : ℤ) + 1) := by simpa using hgj
    obtain ⟨k, hk, hpk⟩ := exists_pre_eq d n
    refine le_antisymm ?_ ?_
    · by_contra hlt
      rw [not_le, hpk, hg] at hlt
      have e : (k : ℤ) + ((i : ℤ) + 1 - k) = (i : ℤ) + 1 := by ring
      have hs := (h.split k ((i : ℤ) + 1 - k) (by rw [e]; exact hlt)).2
      rw [e] at hs
      have hle := gap_le d hk ((i : ℤ) + 1)
      rw [hg] at hle
      exact absurd hs (not_lt.mpr hle)
    · have h1 := pre_le d (n := n) (k := i + 1) hi
      have e : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
      rw [e] at h1
      rw [hg]
      exact h1
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hgj' : gap d n ((i : ℤ) + 1) = d ((i : ℤ) - j') := by
      rw [hgj]
      congr 1
      push_cast
      ring
    have hle : gap d n i ≤ gap d n ((i : ℤ) + 1) := by
      rw [hgj']
      exact gap_le d (by omega) (i : ℤ)
    rcases hle.eq_or_lt with heq | hlt
    · left
      exact heq.symm
    · right; right
      obtain ⟨k, hk, hgk⟩ := exists_gap_eq d n (i : ℤ)
      have hkn : k = n := by
        by_contra hne
        have hk1 : k + 1 ≤ n := by omega
        have h1 := gap_le d hk1 ((i : ℤ) + 1)
        have e : ((i : ℤ) + 1 - ((k + 1 : ℕ) : ℤ)) = (i : ℤ) - k := by push_cast; ring
        rw [e, ← hgk] at h1
        exact absurd hlt (not_lt.mpr h1)
      rw [hkn] at hgk
      obtain ⟨u, hu⟩ : ∃ u : ℤ, u = (i : ℤ) - n := ⟨_, rfl⟩
      obtain ⟨w, hw⟩ : ∃ w : ℤ, w = (n : ℤ) - j' := ⟨_, rfl⟩
      have huw : u + w = (i : ℤ) - j' := by omega
      have hgu : gap d n i = d u := by rw [hgk, hu]
      have hlt' : d u < d (u + w) := by
        rw [huw, ← hgj', ← hgu]
        exact hlt
      have hsplit := (h.split u w hlt').1
      have hA : d u = gap d n 0 := by
        refine le_antisymm ?_ ?_
        · by_contra hlt2
          rw [not_le] at hlt2
          obtain ⟨m, hm, hgm⟩ := exists_gap_eq d n 0
          rw [hgm] at hlt2
          have e : (0 : ℤ) - m + (u + m) = u := by ring
          have hs := (h.split ((0 : ℤ) - m) (u + m) (by rw [e]; exact hlt2)).2
          rw [e] at hs
          have hle2 := gap_le d (j := n - m) (Nat.sub_le n m) (i : ℤ)
          have e2 : (i : ℤ) - ((n - m : ℕ) : ℤ) = u + m := by omega
          rw [e2, hgu] at hle2
          exact absurd hs (not_lt.mpr hle2)
        · have h1 := gap_le d (j := n - i) (Nat.sub_le n i) (0 : ℤ)
          have e : (0 : ℤ) - ((n - i : ℕ) : ℤ) = u := by omega
          rw [e] at h1
          exact h1
      have hB : d w = pre d n := by
        refine le_antisymm ?_ ?_
        · by_contra hlt2
          rw [not_le] at hlt2
          obtain ⟨m, hm, hpm⟩ := exists_pre_eq d n
          rw [hpm] at hlt2
          have hb := h.between u m w hlt' hlt2
          rcases Nat.eq_zero_or_pos m with rfl | hmpos
          · exact absurd hlt2 (not_lt.mpr (by simpa using h.le_zero w))
          · have hle2 := gap_le d (n := n) (j := n - m + 1) (by omega) ((i : ℤ) + 1)
            have e : (i : ℤ) + 1 - ((n - m + 1 : ℕ) : ℤ) = u + m := by omega
            rw [e, hgj', ← huw] at hle2
            exact absurd hb (not_lt.mpr hle2)
        · have h1 := pre_le d (n := n) (k := n - j') (Nat.sub_le n j')
          have e : ((n - j' : ℕ) : ℤ) = w := by omega
          rw [e] at h1
          exact h1
      rw [hgj', ← huw, hsplit, hA, hB]

/-- [proved-derived; formal-checked] **Three distances on an order alone.** Every gap among the
readings `0, …, n` is the gap after the first reading, the gap after the last reading, or their
composition. -/
theorem gap_mem (h : Arcs d comb) (n : ℕ) {i : ℕ} (hi : i ≤ n) :
    gap d n i = gap d n 0 ∨ gap d n i = gap d n n ∨
      gap d n i = comb (gap d n 0) (gap d n n) := by
  rw [gap_last]
  induction i with
  | zero => left; simp
  | succ i ih =>
    have e : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [e]
    rcases gap_succ h hi with h1 | h1 | h1
    · rw [h1]
      exact ih (by omega)
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

/-- [proved-derived; formal-checked] **At most three gap values.** -/
theorem card_gaps_le_three (h : Arcs d comb) (n : ℕ) :
    ((range (n + 1)).image (fun i : ℕ => gap d n i)).card ≤ 3 := by
  refine (card_le_card (?_ : _ ⊆ ({gap d n 0, gap d n n, comb (gap d n 0) (gap d n n)} :
    Finset G))).trans card_le_three
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  have h1 := gap_mem h n (Nat.lt_succ_iff.mp (mem_range.mp hi))
  simpa using h1

end Core

/-! ## 2. The two bridges: arcs that add, ratios that multiply -/

section Bridges

/-- [proved-derived; formal-checked] **Arcs that add.** Arcs in `(0, L]` whose sum is the arc of
the sum, or that arc and one whole turn, satisfy the shift argument's hypotheses with `+`. -/
theorem arcs_of_add {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    {d : ℤ → K} {L : K} (hpos : ∀ k, 0 < d k) (hle : ∀ k, d k ≤ L)
    (hadd : ∀ a b, d a + d b = d (a + b) ∨ d a + d b = d (a + b) + L) :
    Arcs d (fun x y => x + y) where
  le_zero k := by
    have h0 : d 0 = L := by
      have hp := hpos 0
      rcases hadd 0 0 with h | h
      · rw [add_zero] at h
        linarith
      · rw [add_zero] at h
        linarith
    rw [h0]
    exact hle k
  split a b hlt := by
    have ha := hpos a
    have hb := hle b
    rcases hadd a b with h | h
    · exact ⟨by show d (a + b) = d a + d b; linarith, by linarith⟩
    · exfalso
      linarith
  between u v w h1 h2 := by
    have hw := hle w
    have hL : 0 < L := lt_of_lt_of_le (hpos 0) (hle 0)
    have huw : d (u + w) = d u + d w := by
      rcases hadd u w with h | h
      · linarith
      · exfalso
        linarith
    rcases hadd u v with h | h <;> linarith

/-- [proved-derived; formal-checked] **Ratios that multiply.** Ratios in `(1, L]` whose product is
the ratio of the sum, or that ratio times the whole turn's ratio `L`, satisfy the shift argument's
hypotheses with `·`. -/
theorem arcs_of_mul {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d : ℤ → K} {L : K} (hone : ∀ k, 1 < d k) (hle : ∀ k, d k ≤ L)
    (hmul : ∀ a b, d a * d b = d (a + b) ∨ d a * d b = d (a + b) * L) :
    Arcs d (fun x y => x * y) where
  le_zero k := by
    have h0 : d 0 = L := by
      have hp := hone 0
      rcases hmul 0 0 with h | h
      · rw [add_zero] at h
        nlinarith
      · rw [add_zero] at h
        exact mul_left_cancel₀ (by linarith : d 0 ≠ 0) h
    rw [h0]
    exact hle k
  split a b hlt := by
    have ha := hone a
    have hb := hone b
    rcases hmul a b with h | h
    · refine ⟨h.symm, ?_⟩
      rw [← h]
      nlinarith
    · exfalso
      have h1 : d a * d b < d (a + b) * L :=
        mul_lt_mul hlt (hle b) (by linarith) (by linarith [hone (a + b)])
      linarith
  between u v w h1 h2 := by
    have hu := hone u
    have hL : 1 < L := lt_of_lt_of_le (hone 0) (hle 0)
    have huw : d (u + w) = d u * d w := by
      rcases hmul u w with h | h
      · exact h.symm
      · exfalso
        have h3 : d u * d w < d (u + w) * L :=
          mul_lt_mul h1 (hle w) (by linarith [hone w]) (by linarith [hone (u + w)])
        linarith
    have hlt : d u * d v < d u * d w := mul_lt_mul_of_pos_left h2 (by linarith)
    rcases hmul u v with h | h
    · rw [← h, huw]
      exact hlt
    · have h3 : d (u + v) * L < d (u + w) := by
        rw [← h, huw]
        exact hlt
      have h4 : d (u + v) < d (u + v) * L := by nlinarith [hone (u + v)]
      linarith

end Bridges

/-! ## 3. A real rate: every `α`, every `n` -/

section Real

/-- [definition] **The forward arc** from the reading `{kα}` to the origin, in `(0, 1]`: the whole
turn where the reading is the origin. `fwd α (i − j)` is the arc from `{iα}` forward to `{jα}`. -/
noncomputable def fwd (α : ℝ) (k : ℤ) : ℝ := 1 - Int.fract ((k : ℝ) * α)

/-- [proved-derived; formal-checked] An arc is positive. -/
theorem fwd_pos (α : ℝ) (k : ℤ) : 0 < fwd α k := by
  have := Int.fract_lt_one ((k : ℝ) * α)
  unfold fwd
  linarith

/-- [proved-derived; formal-checked] An arc is at most the whole turn. -/
theorem fwd_le_one (α : ℝ) (k : ℤ) : fwd α k ≤ 1 := by
  have := Int.fract_nonneg ((k : ℝ) * α)
  unfold fwd
  linarith

/-- [proved-derived; formal-checked] **Arcs add up to the arc of the sum, or to it and a whole
turn.** -/
theorem fwd_add (α : ℝ) (a b : ℤ) :
    fwd α a + fwd α b = fwd α (a + b) ∨ fwd α a + fwd α b = fwd α (a + b) + 1 := by
  unfold fwd
  have e : (((a + b : ℤ) : ℝ)) * α = (a : ℝ) * α + (b : ℝ) * α := by push_cast; ring
  rw [e]
  obtain ⟨z, hz⟩ := Int.fract_add ((a : ℝ) * α) ((b : ℝ) * α)
  have h1 := Int.fract_nonneg ((a : ℝ) * α)
  have h2 := Int.fract_lt_one ((a : ℝ) * α)
  have h3 := Int.fract_nonneg ((b : ℝ) * α)
  have h4 := Int.fract_lt_one ((b : ℝ) * α)
  have h5 := Int.fract_nonneg ((a : ℝ) * α + (b : ℝ) * α)
  have h6 := Int.fract_lt_one ((a : ℝ) * α + (b : ℝ) * α)
  have hz1 : ((-2 : ℤ) : ℝ) < (z : ℝ) := by push_cast; linarith
  have hz2 : (z : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
  have hz1' : (-2 : ℤ) < z := by exact_mod_cast hz1
  have hz2' : z < 1 := by exact_mod_cast hz2
  have hz3 : z = -1 ∨ z = 0 := by omega
  rcases hz3 with rfl | rfl
  · left
    push_cast at hz
    linarith
  · right
    push_cast at hz
    linarith

/-- [proved-derived; formal-checked] The real rate's arcs satisfy the shift argument's hypotheses
with `+`. -/
theorem arcs_fwd (α : ℝ) : Arcs (fwd α) (fun x y => x + y) :=
  arcs_of_add (fwd_pos α) (fwd_le_one α) (fwd_add α)

/-- [proved-derived; formal-checked] `fwd α (i − j)` is the arc from `{iα}` forward to `{jα}` where
`{jα}` lies ahead on the unit interval. -/
theorem fwd_eq_of_lt {α : ℝ} {i j : ℤ}
    (h : Int.fract ((i : ℝ) * α) < Int.fract ((j : ℝ) * α)) :
    fwd α (i - j) = Int.fract ((j : ℝ) * α) - Int.fract ((i : ℝ) * α) := by
  have h1 := Int.fract_nonneg ((i : ℝ) * α)
  have h2 := Int.fract_lt_one ((j : ℝ) * α)
  have key : Int.fract (((i - j : ℤ) : ℝ) * α) =
      Int.fract ((i : ℝ) * α) - Int.fract ((j : ℝ) * α) + 1 := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⌊(i : ℝ) * α⌋ - ⌊(j : ℝ) * α⌋ - 1, ?_⟩
    simp only [Int.fract]
    push_cast
    ring
  unfold fwd
  rw [key]
  ring

/-- [proved-derived; formal-checked] `fwd α (i − j)` is the arc from `{iα}` forward to `{jα}`
through the section where `{jα}` lies behind, and the whole turn where the two coincide. -/
theorem fwd_eq_of_le {α : ℝ} {i j : ℤ}
    (h : Int.fract ((j : ℝ) * α) ≤ Int.fract ((i : ℝ) * α)) :
    fwd α (i - j) = 1 + Int.fract ((j : ℝ) * α) - Int.fract ((i : ℝ) * α) := by
  have h1 := Int.fract_lt_one ((i : ℝ) * α)
  have h2 := Int.fract_nonneg ((j : ℝ) * α)
  have key : Int.fract (((i - j : ℤ) : ℝ) * α) =
      Int.fract ((i : ℝ) * α) - Int.fract ((j : ℝ) * α) := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, ⌊(i : ℝ) * α⌋ - ⌊(j : ℝ) * α⌋, ?_⟩
    simp only [Int.fract]
    push_cast
    ring
  unfold fwd
  rw [key]
  ring

/-- [proved-derived; formal-checked] **The arc on the owner's objects**: the complement of the
open phase of the rate clock's reading from phase `0` (`CarryWord.helixReading`,
`Winding.openPhase`). -/
theorem fwd_eq_openPhase (α : ℝ) (k : ℤ) :
    fwd α k = 1 - Winding.openPhase (CarryWord.helixReading α 0 k) := by
  simp [fwd, CarryWord.helixReading_eq, Winding.openPhase]

/-- [proved-derived; formal-checked] **The three-distance theorem, every rate and every count.**
Among the readings `{iα}`, `0 ≤ i ≤ n`, every gap is the gap after the first reading, the gap
after the last, or their sum. -/
theorem three_distance (α : ℝ) (n : ℕ) {i : ℕ} (hi : i ≤ n) :
    gap (fwd α) n i = gap (fwd α) n 0 ∨ gap (fwd α) n i = gap (fwd α) n n ∨
      gap (fwd α) n i = gap (fwd α) n 0 + gap (fwd α) n n :=
  gap_mem (arcs_fwd α) n hi

/-- [proved-derived; formal-checked] The gaps of a real rate take at most three lengths. -/
theorem card_gaps_le_three_real (α : ℝ) (n : ℕ) :
    ((range (n + 1)).image (fun i : ℕ => gap (fwd α) n i)).card ≤ 3 :=
  card_gaps_le_three (arcs_fwd α) n

/-- [proved-derived; formal-checked] A gap is positive. -/
theorem gap_fwd_pos (α : ℝ) (n : ℕ) (i : ℤ) : 0 < gap (fwd α) n i := by
  obtain ⟨j, -, h⟩ := exists_gap_eq (fwd α) n i
  rw [h]
  exact fwd_pos α _

/-- [proved-derived; formal-checked] **Where three lengths occur, the largest is the sum of the
other two**: a gap that is neither the first reading's nor the last reading's exceeds both and is
their sum. -/
theorem three_distance_largest (α : ℝ) (n : ℕ) {i : ℕ} (hi : i ≤ n)
    (h0 : gap (fwd α) n i ≠ gap (fwd α) n 0) (hn : gap (fwd α) n i ≠ gap (fwd α) n n) :
    gap (fwd α) n i = gap (fwd α) n 0 + gap (fwd α) n n ∧
      gap (fwd α) n 0 < gap (fwd α) n i ∧ gap (fwd α) n n < gap (fwd α) n i := by
  have hA := gap_fwd_pos α n 0
  have hB := gap_fwd_pos α n n
  rcases three_distance α n hi with h | h | h
  · exact absurd h h0
  · exact absurd h hn
  · exact ⟨h, by linarith, by linarith⟩

end Real

/-! ## 4. A finite ring -/

section Ring

/-- [definition] **The forward arc on `ℤ/q`** from the reading `kp` to the origin, counted in
steps of the ring, in `(0, q]`. -/
def ringFwd (q p : ℤ) (k : ℤ) : ℤ := q - (k * p) % q

/-- [proved-derived; formal-checked] A ring arc is positive. -/
theorem ringFwd_pos {q : ℤ} (hq : 0 < q) (p k : ℤ) : 0 < ringFwd q p k := by
  have := Int.emod_lt_of_pos (k * p) hq
  unfold ringFwd
  omega

/-- [proved-derived; formal-checked] A ring arc is at most the ring. -/
theorem ringFwd_le {q : ℤ} (hq : 0 < q) (p k : ℤ) : ringFwd q p k ≤ q := by
  have := Int.emod_nonneg (k * p) hq.ne'
  unfold ringFwd
  omega

/-- [proved-derived; formal-checked] Ring arcs add up to the arc of the sum, or to it and the
whole ring. -/
theorem ringFwd_add {q : ℤ} (hq : 0 < q) (p a b : ℤ) :
    ringFwd q p a + ringFwd q p b = ringFwd q p (a + b) ∨
      ringFwd q p a + ringFwd q p b = ringFwd q p (a + b) + q := by
  unfold ringFwd
  have e : (a + b) * p = a * p + b * p := by ring
  have h1 := Int.emod_nonneg (a * p) hq.ne'
  have h2 := Int.emod_lt_of_pos (a * p) hq
  have h3 := Int.emod_nonneg (b * p) hq.ne'
  have h4 := Int.emod_lt_of_pos (b * p) hq
  rw [e, Int.add_emod]
  by_cases h : (a * p) % q + (b * p) % q < q
  · right
    rw [Int.emod_eq_of_lt (by omega) h]
    omega
  · left
    have hs : ((a * p) % q + (b * p) % q) % q = (a * p) % q + (b * p) % q - q := by
      rw [Int.emod_eq_sub_self_emod (a := (a * p) % q + (b * p) % q) (b := q)]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hs]
    omega

/-- [proved-derived; formal-checked] The ring's arcs satisfy the shift argument's hypotheses. -/
theorem arcs_ringFwd {q : ℤ} (hq : 0 < q) (p : ℤ) : Arcs (ringFwd q p) (fun x y => x + y) :=
  arcs_of_add (ringFwd_pos hq p) (ringFwd_le hq p) (ringFwd_add hq p)

/-- [proved-derived; formal-checked] The arc is read on `ZMod q`: the ring's size less the
residue of `kp`. -/
theorem ringFwd_eq_val (q : ℕ) [NeZero q] (p k : ℤ) :
    ringFwd q p k = (q : ℤ) - (((k * p : ℤ) : ZMod q).val : ℤ) := by
  rw [ZMod.val_intCast]
  rfl

/-- [proved-derived; formal-checked] **Three distances on a finite ring.** Among the readings
`ip mod q`, `0 ≤ i ≤ n`, every gap is the gap after the first reading, the gap after the last, or
their sum; any step `p` and any count `n`. -/
theorem three_distance_ring {q : ℤ} (hq : 0 < q) (p : ℤ) (n : ℕ) {i : ℕ} (hi : i ≤ n) :
    gap (ringFwd q p) n i = gap (ringFwd q p) n 0 ∨
      gap (ringFwd q p) n i = gap (ringFwd q p) n n ∨
      gap (ringFwd q p) n i = gap (ringFwd q p) n 0 + gap (ringFwd q p) n n :=
  gap_mem (arcs_ringFwd hq p) n hi

/-- [proved-derived; formal-checked] The gaps on a finite ring take at most three lengths. -/
theorem card_gaps_le_three_ring {q : ℤ} (hq : 0 < q) (p : ℤ) (n : ℕ) :
    ((range (n + 1)).image (fun i : ℕ => gap (ringFwd q p) n i)).card ≤ 3 :=
  card_gaps_le_three (arcs_ringFwd hq p) n

end Ring

/-! ## 5. The ratio chart over factored integers -/

section Ratio

variable {a b : ℕ}

/-- [definition] **The reduced power**: `a^k` brought into `[1, b)` by the power of `b` below it,
`a^k / b^e` with `e = Int.log b (a^k)` (the fifth `3^k : 2^e` in the octave is `a = 3`, `b = 2`). -/
def reduced (a b : ℕ) (k : ℤ) : ℚ := (a : ℚ) ^ k / (b : ℚ) ^ Int.log b ((a : ℚ) ^ k)

/-- [definition] **The forward ratio** from the reduced power `k` to the origin `1`, through the
closing ratio `b`: `b^(e + 1) / a^k`, in `(1, b]`. -/
def ratioFwd (a b : ℕ) (k : ℤ) : ℚ := (b : ℚ) ^ (Int.log b ((a : ℚ) ^ k) + 1) / (a : ℚ) ^ k

/-- [proved-derived; formal-checked] The reduced power lies in `[1, b)`. -/
theorem reduced_mem (hb : 1 < b) (ha : 0 < a) (k : ℤ) :
    1 ≤ reduced a b k ∧ reduced a b k < b := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hx : (0 : ℚ) < (a : ℚ) ^ k := zpow_pos ha' k
  have hp : (0 : ℚ) < (b : ℚ) ^ Int.log b ((a : ℚ) ^ k) := zpow_pos hb' _
  have h1 := Int.zpow_log_le_self hb hx
  have h2 := Int.lt_zpow_succ_log_self hb ((a : ℚ) ^ k)
  rw [zpow_add_one₀ hb'.ne'] at h2
  unfold reduced
  exact ⟨(one_le_div hp).mpr h1, (div_lt_iff₀ hp).mpr (by linarith [mul_comm (b : ℚ) ((b : ℚ) ^ Int.log b ((a : ℚ) ^ k))])⟩

/-- [proved-derived; formal-checked] The forward ratio is the closing ratio over the reduced
power. -/
theorem ratioFwd_eq (hb : 1 < b) (ha : 0 < a) (k : ℤ) :
    ratioFwd a b k = b / reduced a b k := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hx : (0 : ℚ) < (a : ℚ) ^ k := zpow_pos ha' k
  have hp : (0 : ℚ) < (b : ℚ) ^ Int.log b ((a : ℚ) ^ k) := zpow_pos hb' _
  unfold ratioFwd reduced
  rw [zpow_add_one₀ hb'.ne']
  field_simp

/-- [proved-derived; formal-checked] A forward ratio exceeds one. -/
theorem one_lt_ratioFwd (hb : 1 < b) (ha : 0 < a) (k : ℤ) : 1 < ratioFwd a b k := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hx : (0 : ℚ) < (a : ℚ) ^ k := zpow_pos ha' k
  unfold ratioFwd
  exact (one_lt_div hx).mpr (Int.lt_zpow_succ_log_self hb _)

/-- [proved-derived; formal-checked] A forward ratio is at most the closing ratio. -/
theorem ratioFwd_le (hb : 1 < b) (ha : 0 < a) (k : ℤ) : ratioFwd a b k ≤ b := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hx : (0 : ℚ) < (a : ℚ) ^ k := zpow_pos ha' k
  have h1 := Int.zpow_log_le_self hb hx
  unfold ratioFwd
  rw [div_le_iff₀ hx, zpow_add_one₀ hb'.ne', mul_comm]
  exact mul_le_mul_of_nonneg_left h1 hb'.le

/-- [proved-derived; formal-checked] **Forward ratios multiply to the ratio of the sum, or to it
times the closing ratio**: the integer `e` of a product is the sum of the two, or one more. -/
theorem ratioFwd_mul (hb : 1 < b) (ha : 0 < a) (k l : ℤ) :
    ratioFwd a b k * ratioFwd a b l = ratioFwd a b (k + l) ∨
      ratioFwd a b k * ratioFwd a b l = ratioFwd a b (k + l) * b := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hxy : (a : ℚ) ^ (k + l) = (a : ℚ) ^ k * (a : ℚ) ^ l := zpow_add₀ ha'.ne' k l
  obtain ⟨x, hx0⟩ : ∃ x : ℚ, x = (a : ℚ) ^ k := ⟨_, rfl⟩
  obtain ⟨y, hy0⟩ : ∃ y : ℚ, y = (a : ℚ) ^ l := ⟨_, rfl⟩
  have hx : 0 < x := hx0 ▸ zpow_pos ha' k
  have hy : 0 < y := hy0 ▸ zpow_pos ha' l
  have h1 : Int.log b x + Int.log b y ≤ Int.log b (x * y) := by
    rw [← Int.zpow_le_iff_le_log hb (mul_pos hx hy), zpow_add₀ hb'.ne']
    exact mul_le_mul (Int.zpow_log_le_self hb hx) (Int.zpow_log_le_self hb hy)
      (zpow_nonneg hb'.le _) hx.le
  have h2 : Int.log b (x * y) < Int.log b x + Int.log b y + 2 := by
    rw [← Int.lt_zpow_iff_log_lt hb (mul_pos hx hy)]
    have e : (b : ℚ) ^ (Int.log b x + Int.log b y + 2) =
        (b : ℚ) ^ (Int.log b x + 1) * (b : ℚ) ^ (Int.log b y + 1) := by
      rw [← zpow_add₀ hb'.ne']
      congr 1
      ring
    rw [e]
    exact mul_lt_mul'' (Int.lt_zpow_succ_log_self hb x) (Int.lt_zpow_succ_log_self hb y)
      hx.le hy.le
  have h3 : Int.log b (x * y) = Int.log b x + Int.log b y + 1 ∨
      Int.log b (x * y) = Int.log b x + Int.log b y := by omega
  have e1 : (b : ℚ) ^ (Int.log b x + 1) = (b : ℚ) ^ Int.log b x * b := zpow_add_one₀ hb'.ne' _
  have e2 : (b : ℚ) ^ (Int.log b y + 1) = (b : ℚ) ^ Int.log b y * b := zpow_add_one₀ hb'.ne' _
  have e3 : (b : ℚ) ^ (Int.log b x + Int.log b y + 1) =
      (b : ℚ) ^ Int.log b x * (b : ℚ) ^ Int.log b y * b := by
    rw [zpow_add_one₀ hb'.ne', zpow_add₀ hb'.ne']
  have e4 : (b : ℚ) ^ (Int.log b x + Int.log b y + 1 + 1) =
      (b : ℚ) ^ Int.log b x * (b : ℚ) ^ Int.log b y * b * b := by
    rw [zpow_add_one₀ hb'.ne', e3]
  unfold ratioFwd
  rw [hxy, ← hx0, ← hy0]
  rcases h3 with h | h
  · left
    rw [h, e1, e2, e4]
    field_simp
  · right
    rw [h, e1, e2, e3]
    field_simp

/-- [proved-derived; formal-checked] The ratio chart's forward ratios satisfy the shift argument's
hypotheses with `·`. -/
theorem arcs_ratioFwd (hb : 1 < b) (ha : 0 < a) : Arcs (ratioFwd a b) (fun x y => x * y) :=
  arcs_of_mul (L := (b : ℚ)) (one_lt_ratioFwd hb ha) (ratioFwd_le hb ha) (ratioFwd_mul hb ha)

/-- [proved-derived; formal-checked] **Three ratios in the ratio chart, every count.** Among the
reduced powers `a^i / b^(e_i)`, `0 ≤ i ≤ n`, every neighbour ratio is the ratio after the first
reading, the ratio after the last, or their product. -/
theorem three_ratios (hb : 1 < b) (ha : 0 < a) (n : ℕ) {i : ℕ} (hi : i ≤ n) :
    gap (ratioFwd a b) n i = gap (ratioFwd a b) n 0 ∨
      gap (ratioFwd a b) n i = gap (ratioFwd a b) n n ∨
      gap (ratioFwd a b) n i = gap (ratioFwd a b) n 0 * gap (ratioFwd a b) n n :=
  gap_mem (arcs_ratioFwd hb ha) n hi

/-- [proved-derived; formal-checked] The neighbour ratios take at most three values. -/
theorem card_gaps_le_three_ratio (hb : 1 < b) (ha : 0 < a) (n : ℕ) :
    ((range (n + 1)).image (fun i : ℕ => gap (ratioFwd a b) n i)).card ≤ 3 :=
  card_gaps_le_three (arcs_ratioFwd hb ha) n

/-- [proved-derived; formal-checked] **The chart over factored integers**: where the integer `e`
is given with `b^e ≤ a^k < b^(e + 1)`, the forward ratio is `b^(e + 1) : a^k`, with no search for
`e`. -/
theorem ratioFwd_of_bounds (hb : 1 < b) (ha : 0 < a) {k e : ℤ}
    (h1 : (b : ℚ) ^ e ≤ (a : ℚ) ^ k) (h2 : (a : ℚ) ^ k < (b : ℚ) ^ (e + 1)) :
    ratioFwd a b k = (b : ℚ) ^ (e + 1) / (a : ℚ) ^ k := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hx : (0 : ℚ) < (a : ℚ) ^ k := zpow_pos ha' k
  have hle : e ≤ Int.log b ((a : ℚ) ^ k) := (Int.zpow_le_iff_le_log hb hx).mp h1
  have hlt : Int.log b ((a : ℚ) ^ k) < e + 1 := (Int.lt_zpow_iff_log_lt hb hx).mp h2
  have he : Int.log b ((a : ℚ) ^ k) = e := by omega
  unfold ratioFwd
  rw [he]

/-- [proved-derived; formal-checked] **Five fifths in the octave** (the row
`rotation.fifth-gap-recursion` at `N = 5`): the neighbour ratio after the first fifth is the tone
`3² : 2³` and the ratio after the last is `2⁵ : 3³`. -/
theorem fifths_five :
    gap (ratioFwd 3 2) 4 0 = 9 / 8 ∧ gap (ratioFwd 3 2) 4 4 = 32 / 27 := by
  have v : ∀ (k e : ℤ), ((2 : ℕ) : ℚ) ^ e ≤ ((3 : ℕ) : ℚ) ^ k →
      ((3 : ℕ) : ℚ) ^ k < ((2 : ℕ) : ℚ) ^ (e + 1) →
      ratioFwd 3 2 k = ((2 : ℕ) : ℚ) ^ (e + 1) / ((3 : ℕ) : ℚ) ^ k :=
    fun k e h1 h2 => ratioFwd_of_bounds (by norm_num) (by norm_num) h1 h2
  have r0 : ratioFwd 3 2 0 = 2 := by rw [v 0 0 (by norm_num) (by norm_num)]; norm_num
  have r1 : ratioFwd 3 2 1 = 4 / 3 := by rw [v 1 1 (by norm_num) (by norm_num)]; norm_num
  have r2 : ratioFwd 3 2 2 = 16 / 9 := by rw [v 2 3 (by norm_num) (by norm_num)]; norm_num
  have r3 : ratioFwd 3 2 3 = 32 / 27 := by rw [v 3 4 (by norm_num) (by norm_num)]; norm_num
  have r4 : ratioFwd 3 2 4 = 128 / 81 := by rw [v 4 6 (by norm_num) (by norm_num)]; norm_num
  have m1 : ratioFwd 3 2 (-1) = 3 / 2 := by
    rw [v (-1) (-2) (by norm_num) (by norm_num)]; norm_num
  have m2 : ratioFwd 3 2 (-2) = 9 / 8 := by
    rw [v (-2) (-4) (by norm_num) (by norm_num)]; norm_num
  have m3 : ratioFwd 3 2 (-3) = 27 / 16 := by
    rw [v (-3) (-5) (by norm_num) (by norm_num)]; norm_num
  have m4 : ratioFwd 3 2 (-4) = 81 / 64 := by
    rw [v (-4) (-7) (by norm_num) (by norm_num)]; norm_num
  constructor
  · refine le_antisymm ?_ ?_
    · have h := gap_le (ratioFwd 3 2) (n := 4) (j := 2) (by norm_num) 0
      norm_num [m2] at h
      exact h
    · unfold gap
      refine Finset.le_inf' _ _ ?_
      intro j hj
      rw [mem_range] at hj
      interval_cases j <;> norm_num [r0, m1, m2, m3, m4]
  · refine le_antisymm ?_ ?_
    · have h := gap_le (ratioFwd 3 2) (n := 4) (j := 1) (by norm_num) 4
      norm_num [r3] at h
      exact h
    · unfold gap
      refine Finset.le_inf' _ _ ?_
      intro j hj
      rw [mem_range] at hj
      interval_cases j <;> norm_num [r0, r1, r2, r3, r4]

/-- [proved-derived; formal-checked] **Twelve fifths in the octave** (the row
`rotation.fifth-gap-recursion` at `N = 12`): the neighbour ratio after the first fifth is the
apotome `3⁷ : 2¹¹` and the ratio after the last is the leimma `2⁸ : 3⁵`, the two ratios whose
quotient `Mathematics/Comma.apotome_div_leimma` reads as the comma; their product, the third value
`three_ratios` allows, is the tone `9 : 8`. -/
theorem fifths_twelve :
    gap (ratioFwd 3 2) 11 0 = 3 ^ 7 / 2 ^ 11 ∧ gap (ratioFwd 3 2) 11 11 = 2 ^ 8 / 3 ^ 5 ∧
      ((3 : ℚ) ^ 7 / 2 ^ 11) * (2 ^ 8 / 3 ^ 5) = 9 / 8 := by
  have v : ∀ (k e : ℤ), ((2 : ℕ) : ℚ) ^ e ≤ ((3 : ℕ) : ℚ) ^ k →
      ((3 : ℕ) : ℚ) ^ k < ((2 : ℕ) : ℚ) ^ (e + 1) →
      ratioFwd 3 2 k = ((2 : ℕ) : ℚ) ^ (e + 1) / ((3 : ℕ) : ℚ) ^ k :=
    fun k e h1 h2 => ratioFwd_of_bounds (by norm_num) (by norm_num) h1 h2
  have p0 : ratioFwd 3 2 0 = 2 := by
    rw [v 0 0 (by norm_num) (by norm_num)]; norm_num
  have p1 : ratioFwd 3 2 1 = 4 / 3 := by
    rw [v 1 1 (by norm_num) (by norm_num)]; norm_num
  have p2 : ratioFwd 3 2 2 = 16 / 9 := by
    rw [v 2 3 (by norm_num) (by norm_num)]; norm_num
  have p3 : ratioFwd 3 2 3 = 32 / 27 := by
    rw [v 3 4 (by norm_num) (by norm_num)]; norm_num
  have p4 : ratioFwd 3 2 4 = 128 / 81 := by
    rw [v 4 6 (by norm_num) (by norm_num)]; norm_num
  have p5 : ratioFwd 3 2 5 = 256 / 243 := by
    rw [v 5 7 (by norm_num) (by norm_num)]; norm_num
  have p6 : ratioFwd 3 2 6 = 1024 / 729 := by
    rw [v 6 9 (by norm_num) (by norm_num)]; norm_num
  have p7 : ratioFwd 3 2 7 = 4096 / 2187 := by
    rw [v 7 11 (by norm_num) (by norm_num)]; norm_num
  have p8 : ratioFwd 3 2 8 = 8192 / 6561 := by
    rw [v 8 12 (by norm_num) (by norm_num)]; norm_num
  have p9 : ratioFwd 3 2 9 = 32768 / 19683 := by
    rw [v 9 14 (by norm_num) (by norm_num)]; norm_num
  have p10 : ratioFwd 3 2 10 = 65536 / 59049 := by
    rw [v 10 15 (by norm_num) (by norm_num)]; norm_num
  have p11 : ratioFwd 3 2 11 = 262144 / 177147 := by
    rw [v 11 17 (by norm_num) (by norm_num)]; norm_num
  have q1 : ratioFwd 3 2 (-1) = 3 / 2 := by
    rw [v (-1) (-2) (by norm_num) (by norm_num)]; norm_num
  have q2 : ratioFwd 3 2 (-2) = 9 / 8 := by
    rw [v (-2) (-4) (by norm_num) (by norm_num)]; norm_num
  have q3 : ratioFwd 3 2 (-3) = 27 / 16 := by
    rw [v (-3) (-5) (by norm_num) (by norm_num)]; norm_num
  have q4 : ratioFwd 3 2 (-4) = 81 / 64 := by
    rw [v (-4) (-7) (by norm_num) (by norm_num)]; norm_num
  have q5 : ratioFwd 3 2 (-5) = 243 / 128 := by
    rw [v (-5) (-8) (by norm_num) (by norm_num)]; norm_num
  have q6 : ratioFwd 3 2 (-6) = 729 / 512 := by
    rw [v (-6) (-10) (by norm_num) (by norm_num)]; norm_num
  have q7 : ratioFwd 3 2 (-7) = 2187 / 2048 := by
    rw [v (-7) (-12) (by norm_num) (by norm_num)]; norm_num
  have q8 : ratioFwd 3 2 (-8) = 6561 / 4096 := by
    rw [v (-8) (-13) (by norm_num) (by norm_num)]; norm_num
  have q9 : ratioFwd 3 2 (-9) = 19683 / 16384 := by
    rw [v (-9) (-15) (by norm_num) (by norm_num)]; norm_num
  have q10 : ratioFwd 3 2 (-10) = 59049 / 32768 := by
    rw [v (-10) (-16) (by norm_num) (by norm_num)]; norm_num
  have q11 : ratioFwd 3 2 (-11) = 177147 / 131072 := by
    rw [v (-11) (-18) (by norm_num) (by norm_num)]; norm_num
  refine ⟨?_, ?_, by norm_num⟩
  · refine le_antisymm ?_ ?_
    · have h := gap_le (ratioFwd 3 2) (n := 11) (j := 7) (by norm_num) 0
      norm_num [q7] at h
      norm_num
      exact h
    · unfold gap
      refine Finset.le_inf' _ _ ?_
      intro j hj
      rw [mem_range] at hj
      interval_cases j <;> norm_num [p0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11]
  · refine le_antisymm ?_ ?_
    · have h := gap_le (ratioFwd 3 2) (n := 11) (j := 6) (by norm_num) 11
      norm_num [p5] at h
      norm_num
      exact h
    · unfold gap
      refine Finset.le_inf' _ _ ?_
      intro j hj
      rw [mem_range] at hj
      interval_cases j <;> norm_num [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]

end Ratio

end Holonics.Aeon.Clock.ThreeDistance
