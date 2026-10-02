import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# HNN.CarriedCuts: the carried states along one step's direction

[proved-derived; formal-checked] A step carries `W + ηD` onto the locus's lattice `uℤ`
(`hnn::constitution::carried_entry`): each entry moves by `q u`, where `q` is the coarse
coordinate, nearest with ties upward, of the fine point, itself nearest with ties upward, of its
update `η d` plus its carried remainder `r`. The two roundings compose to
`q(η) = ⌊(r + η d)/u + c⌋` with `c = 1/2 + 2^(−k−1)`, `2^(−k)` the fine lattice's ratio to the
coarse, `k ≥ 1` (`HNN/LatticeDeposit.quot_fine_eq_floor`, `step_coordinate_eq_floor`). So
along the direction each coordinate is constant in `η` except at its **cuts**, the step sizes
where `(r + η d)/u + c` passes an integer: an arithmetic progression of spacing `u/|d|`. Every
reading, commitment and code length of the successor is a function of the carried state, so all of
them are constant between consecutive cuts of the union over entries and change only at a cut:
the carried path's candidate states are indexed by its cuts, not by `η`.

- **An entry changes exactly at a cut** (`coordinate_changes_iff`).
- **The count of cuts is a Weyl law**: one entry moves by `|η′ − η||d|/u` coordinates up to less
  than one (`coordinate_moves_lt`, `coordinate_moves_gt`), and the whole map by
  `|η′ − η|/u · ‖d‖₁` up to less than its number of entries `n` (`moves_sum_lt`, `moves_sum_gt`).
- **A margin survives every carried state it can pay for**: if each coordinate moved changes a
  station's margin by at most `κ`, the margin stays positive at every step size with
  `κ(η/u · ‖d‖₁ + n) ≤ μ₀` (`margin_survives_moves`); entry by entry, with a rate `w_i` per
  coordinate of entry `i`, at every step size with `η/u · Σ w_i|d_i| + Σ w_i < μ₀`
  (`margin_survives_weighted`).

The record: `research/records/2026-10-02_THE_STEPS_CANDIDATE_STATES_ARE_THE_CUTS_OF_THE_CARRIED_PATH_AND_THEIR_COUNT_IS_A_WEYL_LAW.md`.
-/

namespace Holonics.HNN.CarriedCuts

/-- **An integer reading changes exactly when an integer lies between its two arguments**: for
`a ≤ b`, `⌊a⌋ ≠ ⌊b⌋ ↔ ∃ k : ℤ, a < k ≤ b`. -/
theorem floor_ne_iff {a b : ℝ} (hab : a ≤ b) : ⌊a⌋ ≠ ⌊b⌋ ↔ ∃ k : ℤ, a < k ∧ (k : ℝ) ≤ b := by
  constructor
  · intro hne
    have hlt : ⌊a⌋ < ⌊b⌋ := lt_of_le_of_ne (Int.floor_mono hab) hne
    refine ⟨⌊b⌋, ?_, Int.floor_le b⟩
    have h1 := Int.lt_floor_add_one a
    have h2 : ((⌊a⌋ : ℤ) : ℝ) + 1 ≤ ((⌊b⌋ : ℤ) : ℝ) := by exact_mod_cast hlt
    linarith
  · rintro ⟨k, hk1, hk2⟩
    have h1 : ⌊a⌋ < k := Int.floor_lt.mpr hk1
    have h2 : k ≤ ⌊b⌋ := Int.le_floor.mpr hk2
    omega

/-- **An integer reading moves by its argument's change up to less than one**:
`|⌊b⌋ − ⌊a⌋| < |b − a| + 1`. -/
theorem floor_sub_abs_lt (a b : ℝ) : |((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ)| < |b - a| + 1 := by
  have ha := Int.floor_le a
  have ha' := Int.lt_floor_add_one a
  have hb := Int.floor_le b
  have hb' := Int.lt_floor_add_one b
  push_cast
  rw [abs_lt]
  constructor <;> cases abs_cases (b - a) <;> linarith

/-- **and by at least its argument's change less one**: `|b − a| − 1 < |⌊b⌋ − ⌊a⌋|`. -/
theorem floor_sub_abs_gt (a b : ℝ) : |b - a| - 1 < |((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ)| := by
  have ha := Int.floor_le a
  have ha' := Int.lt_floor_add_one a
  have hb := Int.floor_le b
  have hb' := Int.lt_floor_add_one b
  push_cast
  cases abs_cases (b - a) <;>
    cases abs_cases (((⌊b⌋ : ℤ) : ℝ) - ((⌊a⌋ : ℤ) : ℝ)) <;> linarith

/-- The coordinate an entry carries at step `η`: `⌊(r + η d)/u + c⌋`, with `r` its carried
remainder, `d` the direction's entry, `u` the lattice's unit and `c` the rounding's offset. -/
noncomputable def coordinate (r d u c η : ℝ) : ℤ := ⌊(r + η * d) / u + c⌋

/-- [proved-derived; formal-checked] **An entry changes exactly at a cut**: for `d ≥ 0`, `u > 0`
and `η ≤ η′`, the carried coordinates differ iff some integer `k` has
`(r + η d)/u + c < k ≤ (r + η′ d)/u + c`, a step size of the progression of spacing `u/d`. -/
theorem coordinate_changes_iff {r d u c η η' : ℝ} (hd : 0 ≤ d) (hu : 0 < u) (h : η ≤ η') :
    coordinate r d u c η ≠ coordinate r d u c η' ↔
      ∃ k : ℤ, (r + η * d) / u + c < k ∧ (k : ℝ) ≤ (r + η' * d) / u + c := by
  unfold coordinate
  apply floor_ne_iff
  have : r + η * d ≤ r + η' * d := by nlinarith
  have := div_le_div_of_nonneg_right this hu.le
  linarith

/-- The argument's change along the direction: `(r + η′d)/u − (r + ηd)/u = (η′ − η)d/u`. -/
theorem argument_sub (r d u c η η' : ℝ) (hu : u ≠ 0) :
    ((r + η' * d) / u + c) - ((r + η * d) / u + c) = (η' - η) * d / u := by
  field_simp
  ring

/-- [proved-derived; formal-checked] **One entry moves by `|η′ − η||d|/u` coordinates, up to less
than one**. -/
theorem coordinate_moves_lt (r d c η η' : ℝ) {u : ℝ} (hu : 0 < u) :
    |((coordinate r d u c η' - coordinate r d u c η : ℤ) : ℝ)| < |η' - η| * |d| / u + 1 := by
  have h := floor_sub_abs_lt ((r + η * d) / u + c) ((r + η' * d) / u + c)
  rw [argument_sub r d u c η η' hu.ne', abs_div, abs_mul, abs_of_pos hu] at h
  exact h

/-- [proved-derived; formal-checked] **and by at least `|η′ − η||d|/u` less one**. -/
theorem coordinate_moves_gt (r d c η η' : ℝ) {u : ℝ} (hu : 0 < u) :
    |η' - η| * |d| / u - 1 < |((coordinate r d u c η' - coordinate r d u c η : ℤ) : ℝ)| := by
  have h := floor_sub_abs_gt ((r + η * d) / u + c) ((r + η' * d) / u + c)
  rw [argument_sub r d u c η η' hu.ne', abs_div, abs_mul, abs_of_pos hu] at h
  exact h

variable {ι : Type*}

/-- The coordinates the whole map moves between two step sizes: `Σ_i |q_i(η′) − q_i(η)|`, the
number of single-entry unit moves the carried path takes (each cut moves one entry one
coordinate; coincident cuts move several). -/
noncomputable def moves (s : Finset ι) (r d c : ι → ℝ) (u η η' : ℝ) : ℝ :=
  ∑ i ∈ s, |((coordinate (r i) (d i) u (c i) η' - coordinate (r i) (d i) u (c i) η : ℤ) : ℝ)|

/-- [proved-derived; formal-checked] **The Weyl law of the carried path, from above**: the map
moves by less than `|η′ − η|/u · ‖d‖₁ + n` coordinates, `n` its entries. -/
theorem moves_sum_lt (s : Finset ι) (hs : s.Nonempty) (r d c : ι → ℝ) {u : ℝ} (hu : 0 < u)
    (η η' : ℝ) :
    moves s r d c u η η' < |η' - η| / u * (∑ i ∈ s, |d i|) + s.card := by
  unfold moves
  have h := Finset.sum_lt_sum_of_nonempty hs fun i _ => by
    have := coordinate_moves_lt (r i) (d i) (c i) η η' hu
    rw [mul_div_right_comm] at this
    exact this
  have e : ∑ i ∈ s, (|η' - η| / u * |d i| + 1) = |η' - η| / u * (∑ i ∈ s, |d i|) + s.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
  linarith

/-- [proved-derived; formal-checked] **and from below**: by more than `|η′ − η|/u · ‖d‖₁ − n`. -/
theorem moves_sum_gt (s : Finset ι) (hs : s.Nonempty) (r d c : ι → ℝ) {u : ℝ} (hu : 0 < u)
    (η η' : ℝ) :
    |η' - η| / u * (∑ i ∈ s, |d i|) - s.card < moves s r d c u η η' := by
  unfold moves
  have h := Finset.sum_lt_sum_of_nonempty hs fun i _ => by
    have := coordinate_moves_gt (r i) (d i) (c i) η η' hu
    rw [mul_div_right_comm] at this
    exact this
  have e : ∑ i ∈ s, (|η' - η| / u * |d i| - 1) = |η' - η| / u * (∑ i ∈ s, |d i|) - s.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
  linarith

/-- [proved-derived; formal-checked] **A margin survives every carried state it can pay for**: if a
station's margin `μ` changes by at most `κ ≥ 0` per coordinate moved, `|μ η − μ 0| ≤ κ · moves`,
then `μ η > 0` at every step size with `κ(η/u · ‖d‖₁ + n) ≤ μ 0`. So the flip-free stretch of the
direction is set by the smallest margin over its rate per coordinate, counted on the cuts. -/
theorem margin_survives_moves (s : Finset ι) (hs : s.Nonempty) (r d cs : ι → ℝ) {u : ℝ}
    (hu : 0 < u) {μ : ℝ → ℝ} {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (hμ : |μ η - μ 0| ≤ κ * moves s r d cs u 0 η)
    (hpay : κ * (η / u * (∑ i ∈ s, |d i|) + s.card) ≤ μ 0) (hμ0 : 0 < μ 0) : 0 < μ η := by
  have hlt := moves_sum_lt s hs r d cs hu 0 η
  rw [sub_zero, abs_of_nonneg hη] at hlt
  have := (abs_le.mp hμ).1
  rcases hκ.lt_or_eq with hκ' | hκ'
  · have hstrict : κ * moves s r d cs u 0 η < κ * (η / u * (∑ i ∈ s, |d i|) + s.card) :=
      mul_lt_mul_of_pos_left hlt hκ'
    linarith
  · subst hκ'
    simp at hμ
    linarith

/-- [proved-derived; formal-checked] **Each entry moves a weight by at most its rate times its
own change**: for nonnegative per-entry rates `w i`, the weighted moves
`Σ w_i |q_i(η′) − q_i(η)|` are at most `|η′ − η|/u · Σ w_i|d_i| + Σ w_i`. -/
theorem weighted_moves_le (s : Finset ι) (r d c w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) {u : ℝ}
    (hu : 0 < u) (η η' : ℝ) :
    ∑ i ∈ s, w i *
        |((coordinate (r i) (d i) u (c i) η' - coordinate (r i) (d i) u (c i) η : ℤ) : ℝ)|
      ≤ |η' - η| / u * (∑ i ∈ s, w i * |d i|) + ∑ i ∈ s, w i := by
  have h : ∀ i ∈ s, w i * |((coordinate (r i) (d i) u (c i) η' -
      coordinate (r i) (d i) u (c i) η : ℤ) : ℝ)| ≤ |η' - η| / u * (w i * |d i|) + w i := by
    intro i hi
    have hlt := coordinate_moves_lt (r i) (d i) (c i) η η' hu
    have e : |η' - η| / u * (w i * |d i|) + w i = w i * (|η' - η| * |d i| / u + 1) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hlt.le (hw i hi)
  calc _ ≤ ∑ i ∈ s, (|η' - η| / u * (w i * |d i|) + w i) := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- [proved-derived; formal-checked] **A margin survives every carried state it can pay for, entry
by entry**: if a pair's margin `μ` changes by at most `w_i` per coordinate entry `i` moves,
`|μ η − μ 0| ≤ Σ w_i |q_i(η) − q_i(0)|`, then `μ η > 0` at every step size with
`η/u · Σ w_i|d_i| + Σ w_i < μ 0`. An entry the margin does not read has `w_i = 0` and charges
nothing; at first order `w_i = u|∂μ/∂E_i|`, so the condition reads
`η Σ |∂μ/∂E_i||d_i| + u Σ |∂μ/∂E_i| < μ 0`: the margin's directional rate plus one rounding per
entry it reads. -/
theorem margin_survives_weighted (s : Finset ι) (r d cs w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    {u : ℝ} (hu : 0 < u) {μ : ℝ → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hμ : |μ η - μ 0| ≤ ∑ i ∈ s, w i *
      |((coordinate (r i) (d i) u (cs i) η - coordinate (r i) (d i) u (cs i) 0 : ℤ) : ℝ)|)
    (hpay : η / u * (∑ i ∈ s, w i * |d i|) + ∑ i ∈ s, w i < μ 0) : 0 < μ η := by
  have hle := weighted_moves_le s r d cs w hw hu 0 η
  rw [sub_zero, abs_of_nonneg hη] at hle
  have := (abs_le.mp hμ).1
  linarith

end Holonics.HNN.CarriedCuts

section Audit
open Holonics.HNN.CarriedCuts
#print axioms floor_ne_iff
#print axioms coordinate_changes_iff
#print axioms coordinate_moves_lt
#print axioms coordinate_moves_gt
#print axioms moves_sum_lt
#print axioms moves_sum_gt
#print axioms margin_survives_moves
#print axioms weighted_moves_le
#print axioms margin_survives_weighted
end Audit
