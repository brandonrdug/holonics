import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# A fading medium carries by a cycle with a hand and keeps what a common turn leaves: a count, or a pair of opposite hands

Atlas: `swing.retraced-stroke-moves-nothing`, `swing.three-states-least-hand`, `pair.common-turn-leaves-opposite-hands`,
`radix.floored-shift-push-pop`, `code.nesting-depth-is-index`, `receiver.order-in-the-skew-half`,
`fluid.one-signed-invariant-bounds-fine-grain`, `key.chosen-query-halves`, `hodge.class-singlet-of-its-circle`,
`tower.level-is-difference-tone`, `key.loop-closes-a-sleeping-link`, `ratio.unit-is-a-loop-that-nearly-closes`,
`ratio.common-stretch-is-a-shift-of-the-log-axis`, `ratio.mutual-loss-is-a-two-reader-comma`,
`constitution.one-sided-response-is-fixed-by-its-face`, `receiver.size-is-one-readers-gauge-anothers-state`. Record:
`research/records/2026-11-23_A_FADING_MEDIUM_CARRIES_BY_A_CYCLE_WITH_A_HAND_…`.

The law's owners stand in the tree, named where each is used: the helix as a circle and its carry (`winding.mixed-radix-odometer`),
a helix's two signs and its hand (`helical.two-signs-hand`), compose against compare (`key.mirror-separates-finding-from-checking`),
a reciprocal boundary that cannot orient a passage (`junction.reciprocal-unoriented`), the index of a floored shift's symbol
(`cell.toeplitz-index`), complex Euler's indefinite exchange (`fluid.complex-euler`) and a state added to its own reversal
(`key.half-line-circle-contraction`). This module holds the finite statements those rows do not.

1. **A retraced stroke moves nothing, and a loop moves what it encloses** (`retraced_stroke_moves_nothing`, `loop_moves_its_area`,
   `reversed_loop_moves_back`, `sweep_scale_free`). `sweep p q` is what a straight stroke from shape `p` to shape `q` moves under
   the area's own potential. Out and back cancel; a loop through three shapes moves its signed area; the loop run the other way
   moves the opposite; and nothing in the statement holds a rate, so the amount is the same at any speed.
2. **Two states only retrace; three are the least that go around** (`two_state_cycle_is_its_reverse`,
   `three_state_cycle_has_a_hand`).
3. **A common turn leaves a pair of opposite hands and nothing linear** (`common_turn_cancels`, `same_hand_doubles_the_turn`,
   `linear_read_keeps_the_turn`, `paired_hands_singlet`, `unpaired_hand_turns`). Turn two members by one unit `z`: the product of
   one with the other's conjugate is unchanged, the plain product carries the turn twice, and every linear read carries it once.
   `p` of one hand against `p` of the other is a singlet of the circle, and one hand alone is not.
4. **A shift with a floor: push then pop is the identity, pop then push loses the floor** (`pop_push`, `push_pop`,
   `push_pop_loses_the_floor`, `push_injective`, `pop_kills_the_floor`).
5. **Nesting depth is an index** (`bmul_assoc`, `depth_bmul`, `open_then_close`, `close_then_open`). The words of one bracket pair
   in their reduced form, `a` closers then `b` openers, with the product that cancels an opener against the closer after it: the
   product is associative, the depth `b − a` adds, an opener then its closer is the empty word, and a closer then an opener is not.
6. **Order lives in the skew half of a response** (`order_reads_the_skew_half`, `reciprocal_port_is_order_blind`). At a two-port
   with response `[[a, b], [c, d]]`, an act `x` answered at `y` less the act `y` answered at `x` is `(b − c)` times their oriented
   area: a reciprocal port (`b = c`) returns the same for both orders.
7. **A second invariant of one sign bounds what reaches the fine grain; one of two signs bounds nothing**
   (`triad_split`, `middle_feeds_both_ends`, `fine_grain_share_bounded`, `two_signed_invariant_bounds_nothing`). A triad that keeps
   the sum of its members' changes and their sum weighted by `w₁ < w₂ < w₃`: what the middle member loses goes to both ends in
   the ratio `(w₃ − w₂) : (w₂ − w₁)`. With every weight and every member nonnegative, the members at weight `c` or more hold at
   most the weighted total over `c`. With weights of both signs the weighted total can vanish while a member at the top holds all.
8. **A chosen query halves the keys that stand** (`chosen_query_halves`).
9. **A chain of relative moves, a link asleep, and a loop that closes it** (`chain_regauge`, `asleep_link_keeps_the_far_part`,
   `place_tells_the_link`, `touch_recovers_link`). A part's place is the product of the relative moves between it and the trunk.
   A change of the frames inside the chain leaves the product as it was. With one link unknown the far part is still read against
   itself, its place varies one for one with the unknown link, and one closed loop through the link returns it.
10. **A unit is a loop that nearly closes, and its comma has no first part** (`comma_accumulates`, `loop_start_conjugates`,
   `loop_has_no_first`). A unit that misses its closure by a comma misses by `n` commas in `n` laps, which is a helix. Read from
   another of its parts the loop's remainder is a conjugate of the same remainder, and in a loop every member stands before every
   other. That a helix of fifths closes on no octave, with its commas as ratios of factored integers, is `Mathematics/Comma`'s.
11. **A common stretch is a shift, and mutual loss is a two-reader comma** (`common_stretch_leaves_ratio`,
   `stretch_shifts_log_axis`, `stretches_add`, `mutual_loss_two_way`, `mutual_loss_symm`, `mutual_loss_nonneg`,
   `mutual_loss_pos`). A stretch common to two rates leaves their ratio, moves both by one shift on the logarithmic axis, and
   stretches along a chain add there. `(p − q)(log p − log q)` is the sum of what each of two readers pays to read the other's
   share with its own, the same from either side, never negative, and positive wherever they differ.
12. **A response one-sided in time is fixed by its face** (`face_add_under`, `face_even`, `under_odd`, `one_sided_under_is_face`,
   `one_sided_under_before`, `one_sided_from_face`, `fade_over_turn_is_unit_free`). A response is its part even in time, the face,
   and its part odd in time, the underside. Where nothing answers before the act, the underside is the face after the act and
   the face's negative before it, so the face alone gives the response: twice the face after the act. The ratio of a medium's fade
   to its turn is the same in every unit, so it is no gauge.
13. **A size is a gauge to one reader and a state to another** (`ratio_reader_takes_no_step_along_size`,
   `ratio_reader_step_is_one_over_size`). A reader of a part as a ratio to its own power returns a covector with no component
   along the part, as large as one over the part's size: it holds no balance on the size. A second reader of the same part
   added to a state reads the size, and is the only one that sizes it (`receiver.size-is-one-readers-gauge-anothers-state`).
-/

namespace Holonics

namespace HandedCycle

open BigOperators

/-! ### 1. A retraced stroke and a loop -/

/-- What a straight stroke from shape `p` to shape `q` moves under the potential of the area form. -/
noncomputable def sweep (p q : ℝ × ℝ) : ℝ := (p.1 * q.2 - p.2 * q.1) / 2

/-- A stroke out and back along the same shapes moves nothing. -/
theorem retraced_stroke_moves_nothing (p q : ℝ × ℝ) : sweep p q + sweep q p = 0 := by
  unfold sweep; ring

/-- A loop through three shapes moves its signed area. -/
theorem loop_moves_its_area (p q r : ℝ × ℝ) :
    sweep p q + sweep q r + sweep r p = ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) / 2 := by
  unfold sweep; ring

/-- The loop run the other way moves the opposite amount: the hand of the cycle is the sign of what it carries. -/
theorem reversed_loop_moves_back (p q r : ℝ × ℝ) :
    sweep p r + sweep r q + sweep q p = -(sweep p q + sweep q r + sweep r p) := by
  unfold sweep; ring

/-- Shapes scaled by `c` move `c²` times as much: the amount is the loop's, and no rate enters it. -/
theorem sweep_scale_free (c : ℝ) (p q : ℝ × ℝ) : sweep (c * p.1, c * p.2) (c * q.1, c * q.2) = c ^ 2 * sweep p q := by
  unfold sweep; ring

/-! ### 2. The least cycle with a hand -/

/-- A cycle through two states is its own reverse. -/
theorem two_state_cycle_is_its_reverse : (fun i : Fin 2 => i + 1) = (fun i : Fin 2 => i - 1) := by
  funext i; fin_cases i <;> rfl

/-- A cycle through three states is not its own reverse. -/
theorem three_state_cycle_has_a_hand : (fun i : Fin 3 => i + 1) ≠ (fun i : Fin 3 => i - 1) := by
  intro h
  have h0 := congrFun h 0
  revert h0
  decide

/-! ### 3. What a common turn leaves -/

/-- Two members turned by one unit `z`: the product of one with the other's conjugate is unchanged. -/
theorem common_turn_cancels (z a b : ℂ) (hz : Complex.normSq z = 1) :
    (starRingEnd ℂ) (z * a) * (z * b) = (starRingEnd ℂ) a * b := by
  have h : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, hz]; simp
  rw [map_mul]
  calc (starRingEnd ℂ) z * (starRingEnd ℂ) a * (z * b)
      = ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) a * b) := by ring
    _ = (starRingEnd ℂ) a * b := by rw [h, one_mul]

/-- The plain product of two members of one hand carries the common turn twice. -/
theorem same_hand_doubles_the_turn (z a b : ℂ) : (z * a) * (z * b) = z ^ 2 * (a * b) := by ring

/-- Every linear read of members turned by `z` is the read of the members, turned by `z`: no linear read removes a common turn. -/
theorem linear_read_keeps_the_turn {ι : Type*} (s : Finset ι) (c h : ι → ℂ) (z : ℂ) :
    ∑ i ∈ s, c i * (z * h i) = z * ∑ i ∈ s, c i * h i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `p` of one hand against `p` of the other is a singlet of the circle. -/
theorem paired_hands_singlet (z : ℂ) (hz : Complex.normSq z = 1) (p : ℕ) : z ^ p * (starRingEnd ℂ) z ^ p = 1 := by
  rw [← mul_pow, Complex.mul_conj, hz]; simp

/-- One hand alone turns: the quarter turn to the first power, against none of the other hand, is not one. -/
theorem unpaired_hand_turns : Complex.I ^ 1 * (starRingEnd ℂ) Complex.I ^ 0 ≠ 1 := by
  simp only [pow_one, pow_zero, mul_one]
  intro h
  have := congrArg Complex.re h
  simp at this

/-! ### 4. A shift with a floor -/

variable {α : Type*} [Zero α]

/-- Push: every place moves one up and the floor is left empty. -/
def push (f : ℕ → α) : ℕ → α
  | 0 => 0
  | n + 1 => f n

/-- Pop: every place moves one down and the floor's content leaves. -/
def pop (f : ℕ → α) : ℕ → α := fun n => f (n + 1)

/-- Push then pop is the identity. -/
theorem pop_push (f : ℕ → α) : pop (push f) = f := rfl

/-- Pop then push keeps every place but the floor, which it empties. -/
theorem push_pop (f : ℕ → α) (n : ℕ) : push (pop f) n = if n = 0 then 0 else f n := by
  cases n <;> simp [push, pop]

/-- Pop then push is not the identity: a store with content at its floor loses it. -/
theorem push_pop_loses_the_floor : ∃ f : ℕ → ℤ, push (pop f) ≠ f := by
  refine ⟨fun _ => 1, fun h => ?_⟩
  have := congrFun h 0
  simp [push] at this

/-- Push loses nothing. -/
theorem push_injective : Function.Injective (push : (ℕ → α) → ℕ → α) := by
  intro f g h
  funext n
  exact congrFun h (n + 1)

omit [Zero α] in
/-- Pop forgets what stood at the floor: two stores that differ only there pop to the same store. -/
theorem pop_kills_the_floor (f g : ℕ → α) (h : ∀ n, f (n + 1) = g (n + 1)) : pop f = pop g := by
  funext n; exact h n

/-! ### 5. Nesting depth is an index -/

/-- Reduced words of one bracket pair, `(a, b)` for `a` closers then `b` openers; the product cancels an opener against the closer
after it. -/
def bmul (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 + y.1 - min x.2 y.1, y.2 + x.2 - min x.2 y.1)

/-- The depth a reduced word leaves: its openers less its closers. -/
def depth (x : ℕ × ℕ) : ℤ := (x.2 : ℤ) - x.1

theorem bmul_assoc (x y z : ℕ × ℕ) : bmul (bmul x y) z = bmul x (bmul y z) := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  obtain ⟨e, f⟩ := z
  simp only [bmul, Prod.mk.injEq]
  constructor <;> omega

/-- The depth adds: it is the one count the product keeps of each factor. -/
theorem depth_bmul (x y : ℕ × ℕ) : depth (bmul x y) = depth x + depth y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [bmul, depth]
  omega

/-- An opener then its closer is the empty word. -/
theorem open_then_close : bmul (0, 1) (1, 0) = (0, 0) := by decide

/-- A closer then an opener is not: the two orders differ, at depth zero both. -/
theorem close_then_open : bmul (1, 0) (0, 1) = (1, 1) ∧ depth (1, 1) = 0 ∧ ((1, 1) : ℕ × ℕ) ≠ (0, 0) := by decide

/-! ### 6. Order lives in the skew half -/

/-- At a two-port with response `[[a, b], [c, d]]`: the act `x` answered at `y`, less the act `y` answered at `x`, is `b − c`
times the oriented area of the two acts. -/
theorem order_reads_the_skew_half (a b c d x₁ x₂ y₁ y₂ : ℝ) :
    (x₁ * (a * y₁ + b * y₂) + x₂ * (c * y₁ + d * y₂)) - (y₁ * (a * x₁ + b * x₂) + y₂ * (c * x₁ + d * x₂))
      = (b - c) * (x₁ * y₂ - x₂ * y₁) := by ring

/-- A reciprocal port returns the same for both orders of two acts. -/
theorem reciprocal_port_is_order_blind (a b d x₁ x₂ y₁ y₂ : ℝ) :
    x₁ * (a * y₁ + b * y₂) + x₂ * (b * y₁ + d * y₂) = y₁ * (a * x₁ + b * x₂) + y₂ * (b * x₁ + d * x₂) := by ring

/-! ### 7. A second invariant of one sign -/

/-- A triad that keeps the sum of its members' changes and their weighted sum: the ends' changes are fixed by the middle's. -/
theorem triad_split (w₁ w₂ w₃ d₁ d₂ d₃ : ℝ) (hE : d₁ + d₂ + d₃ = 0) (hZ : w₁ * d₁ + w₂ * d₂ + w₃ * d₃ = 0) :
    (w₃ - w₁) * d₁ = -(w₃ - w₂) * d₂ ∧ (w₃ - w₁) * d₃ = -(w₂ - w₁) * d₂ := by
  constructor
  · linear_combination w₃ * hE - hZ
  · linear_combination hZ - w₁ * hE

/-- With the weights in order, what the middle member loses goes to both ends: no transfer runs to the fine end alone. -/
theorem middle_feeds_both_ends (w₁ w₂ w₃ d₁ d₂ d₃ : ℝ) (h12 : w₁ < w₂) (h23 : w₂ < w₃) (hd : d₂ < 0)
    (hE : d₁ + d₂ + d₃ = 0) (hZ : w₁ * d₁ + w₂ * d₂ + w₃ * d₃ = 0) : 0 < d₁ ∧ 0 < d₃ := by
  obtain ⟨h1, h3⟩ := triad_split w₁ w₂ w₃ d₁ d₂ d₃ hE hZ
  have h13 : 0 < w₃ - w₁ := by linarith
  constructor
  · by_contra hcon
    have hle : d₁ ≤ 0 := not_lt.mp hcon
    have hpos : 0 < (w₃ - w₁) * d₁ := by
      rw [h1]; nlinarith [mul_pos (sub_pos.mpr h23) (neg_pos.mpr hd)]
    nlinarith [mul_nonneg h13.le (neg_nonneg.mpr hle)]
  · by_contra hcon
    have hle : d₃ ≤ 0 := not_lt.mp hcon
    have hpos : 0 < (w₃ - w₁) * d₃ := by
      rw [h3]; nlinarith [mul_pos (sub_pos.mpr h12) (neg_pos.mpr hd)]
    nlinarith [mul_nonneg h13.le (neg_nonneg.mpr hle)]

/-- Members and weights nonnegative: the members at weight `c` or more hold at most the weighted total over `c`. -/
theorem fine_grain_share_bounded {ι : Type*} (s : Finset ι) (e w : ι → ℝ) (c : ℝ)
    (he : ∀ i ∈ s, 0 ≤ e i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    c * ∑ i ∈ s.filter (fun i => c ≤ w i), e i ≤ ∑ i ∈ s, w i * e i := by
  classical
  rw [Finset.mul_sum]
  calc ∑ i ∈ s.filter (fun i => c ≤ w i), c * e i
      ≤ ∑ i ∈ s.filter (fun i => c ≤ w i), w i * e i := by
        apply Finset.sum_le_sum
        intro i hi
        have hmem := Finset.mem_filter.mp hi
        exact mul_le_mul_of_nonneg_right hmem.2 (he i hmem.1)
    _ ≤ ∑ i ∈ s, w i * e i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i hi _
        exact mul_nonneg (hw i hi) (he i hi)

/-- Weights of both signs: the weighted total vanishes while the member at the top weight holds a whole unit. -/
theorem two_signed_invariant_bounds_nothing :
    ∃ e₁ e₂ w₁ w₂ : ℝ, 0 ≤ e₁ ∧ 0 ≤ e₂ ∧ w₁ * e₁ + w₂ * e₂ = 0 ∧ 1 ≤ w₂ ∧ e₂ = 1 :=
  ⟨1, 1, -1, 1, by norm_num, by norm_num, by norm_num, le_refl 1, rfl⟩

/-! ### 8. A chosen query -/

/-- Among the keys that stand, a query can be chosen that half of them answer one way. -/
theorem chosen_query_halves {κ : Type*} (S : Finset κ) : ∃ A ⊆ S, A.card = S.card / 2 :=
  Finset.exists_subset_card_eq (Nat.div_le_self _ _)

/-! ### 9. A chain of relative moves -/

/-- A change of the frame at a joint inside a chain leaves the chain's product as it was. -/
theorem chain_regauge {G : Type*} [Group G] (a b g : G) : (a * g) * (g⁻¹ * b) = a * b := by group

/-- A link `x` asleep between the near chain `a` and the far chain `b`: the far part `c` is still read against itself, whatever
the sleeping link is. -/
theorem asleep_link_keeps_the_far_part {G : Type*} [Group G] (a x b c : G) :
    (a * x * b)⁻¹ * (a * x * b * c) = c := by group

/-- The far part's place varies one for one with the sleeping link: while the link is unknown the place is unknown by that factor
and by no more. -/
theorem place_tells_the_link {G : Type*} [Group G] (a b x y : G) (h : a * x * b = a * y * b) : x = y :=
  mul_left_cancel (mul_right_cancel h)

/-- One closed loop through the sleeping link, the far part touched at a place `t` that is known, returns the link. -/
theorem touch_recovers_link {G : Type*} [Group G] (a x b t : G) (h : a * x * b = t) : x = a⁻¹ * t * b⁻¹ := by
  subst h; group

/-! ### 10. A unit, its comma and its parts -/

/-- A unit that misses its closure by a comma `κ` misses by `n` commas in `n` laps: a helix, and no circle. -/
theorem comma_accumulates {M : Type*} [CommMonoid M] (u κ : M) (n : ℕ) : (u * κ) ^ n = u ^ n * κ ^ n := mul_pow u κ n

/-- A loop of two parts read from the other part: its remainder is a conjugate of the same remainder, so the loop has no first
part and its class is no part's own. -/
theorem loop_start_conjugates {G : Type*} [Group G] (a b : G) : b * a = a⁻¹ * (a * b) * a := by group

/-- In a loop every member stands before every other: from any member some count of steps reaches any member. -/
theorem loop_has_no_first (n : ℕ) [NeZero n] (i j : Fin n) : ∃ k : Fin n, i + k = j := ⟨j - i, by abel⟩

/-! ### 11. A common stretch, and mutual loss -/

/-- A stretch common to two rates leaves their ratio: a spectrum moved by a common factor keeps its intervals. -/
theorem common_stretch_leaves_ratio (c a b : ℝ) (hc : c ≠ 0) : (c * a) / (c * b) = a / b := mul_div_mul_left a b hc

/-- On the logarithmic axis a common stretch is one shift, and every difference stands. -/
theorem stretch_shifts_log_axis (c a b : ℝ) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    Real.log (c * a) - Real.log (c * b) = Real.log a - Real.log b := by
  rw [Real.log_mul hc.ne' ha.ne', Real.log_mul hc.ne' hb.ne']; ring

/-- Stretches along a chain add on the logarithmic axis. -/
theorem stretches_add (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Real.log (a * b) = Real.log a + Real.log b :=
  Real.log_mul ha.ne' hb.ne'

/-- Mutual loss at one symbol is the sum of the two directed parts: what `p`'s reader pays to read with `q`'s share, and what
`q`'s reader pays to read with `p`'s. -/
theorem mutual_loss_two_way (p q : ℝ) :
    (p - q) * (Real.log p - Real.log q) = p * (Real.log p - Real.log q) + q * (Real.log q - Real.log p) := by ring

/-- It is the same from either reader's side. -/
theorem mutual_loss_symm (p q : ℝ) :
    (p - q) * (Real.log p - Real.log q) = (q - p) * (Real.log q - Real.log p) := by ring

/-- It is never negative, at every symbol. -/
theorem mutual_loss_nonneg (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : 0 ≤ (p - q) * (Real.log p - Real.log q) := by
  rcases le_total p q with h | h
  · have hl := Real.log_le_log hp h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hl)]
  · have hl := Real.log_le_log hq h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hl)]

/-- It is positive wherever the two shares differ: only a perfect copy pays nothing. -/
theorem mutual_loss_pos (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (h : p ≠ q) : 0 < (p - q) * (Real.log p - Real.log q) := by
  rcases lt_or_gt_of_ne h with h | h
  · have hl := Real.log_lt_log hp h
    nlinarith [mul_pos (sub_pos.mpr h) (sub_pos.mpr hl)]
  · have hl := Real.log_lt_log hq h
    nlinarith [mul_pos (sub_pos.mpr h) (sub_pos.mpr hl)]

/-! ### 12. A face and its underside -/

/-- The part of a response that is even in time: its face. -/
noncomputable def facePart (f : ℝ → ℝ) (t : ℝ) : ℝ := (f t + f (-t)) / 2

/-- The part of a response that is odd in time: the face's underside. -/
noncomputable def underPart (f : ℝ → ℝ) (t : ℝ) : ℝ := (f t - f (-t)) / 2

/-- A response is its face and its underside. -/
theorem face_add_under (f : ℝ → ℝ) (t : ℝ) : facePart f t + underPart f t = f t := by
  unfold facePart underPart; ring

/-- The face reads the same under a reversal of time. -/
theorem face_even (f : ℝ → ℝ) (t : ℝ) : facePart f (-t) = facePart f t := by
  unfold facePart; rw [neg_neg]; ring

/-- The underside changes sign under a reversal of time. -/
theorem under_odd (f : ℝ → ℝ) (t : ℝ) : underPart f (-t) = -underPart f t := by
  unfold underPart; rw [neg_neg]; ring

/-- Where nothing answers before the act, the underside is the face after the act. -/
theorem one_sided_under_is_face (f : ℝ → ℝ) (h : ∀ t, t < 0 → f t = 0) (t : ℝ) (ht : 0 < t) :
    underPart f t = facePart f t := by
  unfold underPart facePart; rw [h (-t) (by linarith)]; ring

/-- And the face's negative before it: the underside is the face times the sign of time. -/
theorem one_sided_under_before (f : ℝ → ℝ) (h : ∀ t, t < 0 → f t = 0) (t : ℝ) (ht : t < 0) :
    underPart f t = -facePart f t := by
  unfold underPart facePart; rw [h t ht]; ring

/-- So the face alone gives a one-sided response: twice the face after the act. -/
theorem one_sided_from_face (f : ℝ → ℝ) (h : ∀ t, t < 0 → f t = 0) (t : ℝ) (ht : 0 < t) :
    f t = 2 * facePart f t := by
  unfold facePart; rw [h (-t) (by linarith)]; ring

/-- The ratio of a medium's fade to its turn is the same in every unit of length or of time: a number of this kind is no gauge. -/
theorem fade_over_turn_is_unit_free (c fade turn : ℝ) (hc : c ≠ 0) : (c * fade) / (c * turn) = fade / turn :=
  mul_div_mul_left fade turn hc

/-! ### 13. A size is a gauge to one reader and a state to another -/

/-- A reader that reads a part as a ratio to its own power returns a covector with no component along the part: with `r` the
ratio (of unit power) and `g` the covector on it, the covector on the part is `g − r ⟨r, g⟩` over the part's size, and its pairing
with `r` is zero. Such a reader takes no step along the part's size and holds no balance on it. -/
theorem ratio_reader_takes_no_step_along_size {n : ℕ} (r g : Fin n → ℝ) (h : ∑ i, r i * r i = 1) :
    ∑ i, r i * (g i - r i * ∑ j, r j * g j) = 0 := by
  have step : ∀ i, r i * (g i - r i * ∑ j, r j * g j) = r i * g i - (r i * r i) * ∑ j, r j * g j := by
    intro i; ring
  simp only [step, Finset.sum_sub_distrib, ← Finset.sum_mul, h, one_mul, sub_self]

/-- And the step it does take is as large as one over the size: at `c` times the size the covector is `1/c` of itself. -/
theorem ratio_reader_step_is_one_over_size (g s c : ℝ) (hs : s ≠ 0) (hc : c ≠ 0) : g / (c * s) = (g / s) / c := by
  field_simp

end HandedCycle

end Holonics
