import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# A chain of links is an address, two links about two anchors fail to commute by their anchors' displacement, reach is bought by depth, a cut bounds what crosses it, and a draw is weighed by what its return did

Atlas: `swing.two-anchors-fail-to-commute`, `radix.place-is-a-link`, `tower.reach-is-bought-by-depth`,
`receiver.answer-sized-to-its-cut`, `holarchy.flow-out-of-a-cut`, `receipt.draw-weighed-by-its-return`,
`receiver.own-anchor-has-no-own-address`. Record:
`research/records/2026-11-23_A_QUESTION_IS_THE_STROKE_OUT_OF_A_LOOP_ITS_ANSWER_CLOSES_…`.

Most of the law has its owners, named where each is used: a pantograph about one anchor and its serial composition
(`swing.pantograph`, `Geometry/HolonicPantographicSwingJets`), the gyrogroup's parallelogram (`frame.gyroparallelogram`), a push and a
pop with their floor (`HNN/HandedCycle`: `pop_push`, `push_pop_loses_the_floor`), a chosen query that halves (`chosen_query_halves`),
a loop that moves its area and a retraced stroke that moves nothing (`loop_moves_its_area`, `retraced_stroke_moves_nothing`), a
probe that reads its loop and an act that is not answered (`HNN/AnsweredAct`: `probe_reads_loop`, `unanswered_act_conditional`),
the leader's growth and deposit (`heat.leader-breakdown`), max flow and min cut (`holarchy.pocket-min-cut`), and the cost of
navigating between states (`key.slow-modes-landmarks`, the record of November 10). This module holds the statements those rows do
not.

1. **A link, and two links about two anchors** (`link_fixes_anchor`, `link_comp_same_anchor`, `links_fail_to_commute`,
   `links_commute_iff`, `link_comp_anchor`, `two_half_turns_translate`). A link is the pantograph about an anchor `a` with a scale
   `u`: `x ↦ a + u (x − a)`. Links about one anchor multiply their scales and commute. Links about two anchors `a`, `b` with scales
   `u`, `v`, taken in the two orders, differ by `(1 − u)(1 − v)(a − b)` at every point: a displacement that names no point, zero
   only where a link is idle or the anchors are one. Their composite is one link, its scale the product and its anchor a weighed
   mean of the two anchors, or a pure displacement where the scales multiply to one (two half-turns: twice the anchors'
   displacement). This is the affine chart of the parallelogram that does not close, and for links near idle, `u = 1 − ε` and
   `v = 1 − δ`, the defect is the product `ε δ` of the two strokes times the anchors' displacement: an area.
2. **A place of a positional address is a link, and a chain's reach is the product of its scales** (`place_is_a_link`, `nest`,
   `nest_reach`, `chain_addresses_count`). The place `x ↦ d + b x` is the link of scale `b` about the anchor `d / (1 − b)`: a
   digit and a radix are an anchor and a scale. Through a chain of places a displacement at the innermost end arrives at the
   outermost multiplied by the product of the scales, and a chain of `k` joints whose ranges are `b i` holds `∏ b i` addresses.
   The linkage is the address: no radix stands beside the digits.
3. **Reach is bought by depth** (`words_reach_at_most`, `route_is_two_half_routes`). Words of `t` moves over `d` kinds of move
   reach at most `d ^ t` states, so a limb whose moves reach `n` states has depth at least `log n / log d`: the counting floor
   under every diameter. A route of `2 m` moves is two routes of `m` moves that meet.
4. **An answer is sized to the cut its question opened** (`answer_needs_its_length`, `answer_of_its_length_exists`,
   `short_answer_merges_two_cases`). An answer that tells `n` cases apart through a channel of `b` symbols has length `L` with
   `n ≤ b ^ L`; an answer of that length exists; and a shorter one gives two cases the same word. What stands in an answer beyond
   the cases its asker left open tells no case apart.
5. **A cut bounds what crosses it** (`net_flow_out_of_cut`, `flow_out_of_cut_le_capacity`, `source_flow_le_any_cut`). On a finite
   network the net flow out of a set of vertices is the net flow across its boundary, the flows inside cancelling in pairs; with
   flows between zero and the capacities it is at most the capacity of the boundary; and where every vertex of the set but a
   source conserves its flow, what leaves the source is at most the capacity of every cut around it. The area of the least cut is
   the channel's capacity (the half of max flow and min cut that needs no construction).
6. **The first person is an anchor** (`own_anchor_reads_zero`, `name_from_another_anchor`, `anchor_read_through_another_link`).
   A point's address from an anchor is its displacement from it. An anchor's address in its own frame is zero, which no symbol
   holds; from another anchor the same point's address is its own-frame address plus the displacement of the two anchors, and
   read through another's link it is that displacement times the link's scale. A name is an address from another's anchor.
7. **A draw is weighed by what its return did** (`draw_term_mean`, `baseline_moves_nothing`, `news_stands_where_the_fall_is_nothing`).
   A face `p` over acts, each act `i` with a return `L i`. The term `(L i − mean)(1[i = j] − p j)` at the face's locus `j`,
   averaged over the face's own draws, is `p j (L j − mean)`: the face moves toward the acts whose return stands above its mean
   and away from those below, with no comparison of any act with a target. A constant added to every return moves nothing. Where
   the return is the fall of an answer's code across its deposit, an answer already held and an answer no deposit moves both
   return nothing, while the answer's news still stands at the second: a draw weighed by news alone is held by noise, and one
   weighed by the fall is released there.
-/

namespace Holonics.HNN.ReachAndCapacity

open Finset

/-! ### 1. A link, and two links about two anchors -/

/-- A link: the pantograph about the anchor `a` with the scale `u`. -/
def link {R : Type*} [CommRing R] (a u x : R) : R := a + u * (x - a)

/-- A link keeps its anchor. -/
theorem link_fixes_anchor {R : Type*} [CommRing R] (a u : R) : link a u a = a := by
  simp [link]

/-- Links about one anchor multiply their scales. -/
theorem link_comp_same_anchor {R : Type*} [CommRing R] (a u v x : R) :
    link a u (link a v x) = link a (u * v) x := by
  simp only [link]; ring

/-- Two links about two anchors, taken in the two orders, differ at every point by one displacement: the product of what each
scale lacks of one, times the displacement of the anchors. -/
theorem links_fail_to_commute {R : Type*} [CommRing R] (a b u v x : R) :
    link a u (link b v x) - link b v (link a u x) = (1 - u) * (1 - v) * (a - b) := by
  simp only [link]; ring

/-- Two links commute at every point only where one of them is idle or their anchors are one. -/
theorem links_commute_iff {K : Type*} [Field K] (a b u v : K) :
    (∀ x, link a u (link b v x) = link b v (link a u x)) ↔ u = 1 ∨ v = 1 ∨ a = b := by
  constructor
  · intro h
    have h0 := links_fail_to_commute a b u v 0
    rw [h 0, sub_self] at h0
    rcases mul_eq_zero.mp h0.symm with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inl (sub_eq_zero.mp h2).symm
      · exact Or.inr (Or.inl (sub_eq_zero.mp h2).symm)
    · exact Or.inr (Or.inr (sub_eq_zero.mp h1))
  · rintro (rfl | rfl | rfl) x <;> simp only [link] <;> ring

/-- Two links compose into one link: its scale the product, its anchor a weighed mean of the two anchors. -/
theorem link_comp_anchor {K : Type*} [Field K] (a b u v x : K) (h : 1 - u * v ≠ 0) :
    link a u (link b v x) = link (((1 - u) * a + u * (1 - v) * b) / (1 - u * v)) (u * v) x := by
  simp only [link]
  field_simp
  ring

/-- Two half-turns about two anchors leave a displacement by twice the anchors' own. -/
theorem two_half_turns_translate {R : Type*} [CommRing R] (a b x : R) :
    link a (-1) (link b (-1) x) = x + 2 * (a - b) := by
  simp only [link]; ring

/-! ### 2. A place of a positional address is a link -/

/-- The place `x ↦ d + b x` is the link of scale `b` about the anchor `d / (1 − b)`. -/
theorem place_is_a_link {K : Type*} [Field K] (d b x : K) (h : 1 - b ≠ 0) :
    d + b * x = link (d / (1 - b)) b x := by
  simp only [link]
  field_simp
  ring

/-- A chain of places, the outermost first: each a digit and a radix. -/
def nest {R : Type*} [CommRing R] : List (R × R) → R → R
  | [], x => x
  | p :: l, x => p.1 + p.2 * nest l x

/-- A displacement at the innermost end of a chain arrives at the outermost multiplied by the product of the scales. -/
theorem nest_reach {R : Type*} [CommRing R] (l : List (R × R)) (x y : R) :
    nest l x - nest l y = (l.map Prod.snd).prod * (x - y) := by
  induction l with
  | nil => simp [nest]
  | cons p l ih =>
    simp only [nest, List.map_cons, List.prod_cons]
    linear_combination p.2 * ih

/-- A chain of `k` joints whose ranges are `b i` holds the product of the ranges in addresses. -/
theorem chain_addresses_count {k : ℕ} (b : Fin k → ℕ) :
    Fintype.card ((i : Fin k) → Fin (b i)) = ∏ i, b i := by
  simp [Fintype.card_pi]

/-! ### 3. Reach is bought by depth -/

/-- Words of `t` moves over `d` kinds of move reach at most `d ^ t` states. -/
theorem words_reach_at_most {S : Type*} [Fintype S] (d t : ℕ) (f : (Fin t → Fin d) → S)
    (hf : Function.Surjective f) : Fintype.card S ≤ d ^ t := by
  calc Fintype.card S ≤ Fintype.card (Fin t → Fin d) := Fintype.card_le_of_surjective f hf
    _ = d ^ t := by simp

/-- A route of `2 m` moves is two routes of `m` moves that meet. -/
theorem route_is_two_half_routes {M : Type*} [Monoid M] (A : M) (m : ℕ) : A ^ (2 * m) = A ^ m * A ^ m := by
  rw [two_mul, pow_add]

/-! ### 4. An answer is sized to the cut its question opened -/

/-- An answer that tells the cases apart through `L` places of `b` symbols: the cases number at most `b ^ L`. -/
theorem answer_needs_its_length {C : Type*} [Fintype C] (b L : ℕ) (f : C → (Fin L → Fin b))
    (hf : Function.Injective f) : Fintype.card C ≤ b ^ L := by
  calc Fintype.card C ≤ Fintype.card (Fin L → Fin b) := Fintype.card_le_of_injective f hf
    _ = b ^ L := by simp

/-- An answer of that length exists. -/
theorem answer_of_its_length_exists (b L : ℕ) :
    ∃ f : Fin (b ^ L) → (Fin L → Fin b), Function.Injective f :=
  ⟨finFunctionFinEquiv.symm, finFunctionFinEquiv.symm.injective⟩

/-- A shorter answer gives two cases the same word. -/
theorem short_answer_merges_two_cases {C : Type*} [Fintype C] (b L : ℕ) (f : C → (Fin L → Fin b))
    (h : b ^ L < Fintype.card C) : ∃ x y, x ≠ y ∧ f x = f y := by
  have hlt : Fintype.card (Fin L → Fin b) < Fintype.card C := by simpa using h
  exact Fintype.exists_ne_map_eq_of_card_lt f hlt

/-! ### 5. A cut bounds what crosses it -/

/-- The net flow out of a set of vertices is the net flow across its boundary: the flows inside cancel in pairs. -/
theorem net_flow_out_of_cut {V : Type*} [Fintype V] [DecidableEq V] (f : V → V → ℝ) (S : Finset V) :
    ∑ v ∈ S, (∑ w, f v w - ∑ w, f w v) = ∑ v ∈ S, ∑ w ∈ Sᶜ, (f v w - f w v) := by
  have inner : ∑ v ∈ S, ∑ w ∈ S, f v w = ∑ v ∈ S, ∑ w ∈ S, f w v := Finset.sum_comm
  calc ∑ v ∈ S, (∑ w, f v w - ∑ w, f w v)
      = ∑ v ∈ S, ((∑ w ∈ S, f v w + ∑ w ∈ Sᶜ, f v w) - (∑ w ∈ S, f w v + ∑ w ∈ Sᶜ, f w v)) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        have h1 : ∑ w ∈ S, f v w + ∑ w ∈ Sᶜ, f v w = ∑ w, f v w := Finset.sum_add_sum_compl S _
        have h2 : ∑ w ∈ S, f w v + ∑ w ∈ Sᶜ, f w v = ∑ w, f w v := Finset.sum_add_sum_compl S _
        rw [h1, h2]
    _ = (∑ v ∈ S, ∑ w ∈ S, f v w - ∑ v ∈ S, ∑ w ∈ S, f w v) + ∑ v ∈ S, ∑ w ∈ Sᶜ, (f v w - f w v) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        ring
    _ = ∑ v ∈ S, ∑ w ∈ Sᶜ, (f v w - f w v) := by rw [inner, sub_self, zero_add]

/-- With flows between zero and the capacities, the net flow out of a set is at most the capacity of its boundary. -/
theorem flow_out_of_cut_le_capacity {V : Type*} [Fintype V] [DecidableEq V] (f c : V → V → ℝ) (S : Finset V)
    (h0 : ∀ v w, 0 ≤ f v w) (hc : ∀ v w, f v w ≤ c v w) :
    ∑ v ∈ S, (∑ w, f v w - ∑ w, f w v) ≤ ∑ v ∈ S, ∑ w ∈ Sᶜ, c v w := by
  rw [net_flow_out_of_cut]
  refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => ?_
  linarith [h0 w v, hc v w]

/-- Where every vertex of a set but a source conserves its flow, what leaves the source is at most the capacity of the set's
boundary: no loop carries more than the least cut it threads. -/
theorem source_flow_le_any_cut {V : Type*} [Fintype V] [DecidableEq V] (f c : V → V → ℝ) (S : Finset V) (s : V)
    (hs : s ∈ S) (h0 : ∀ v w, 0 ≤ f v w) (hc : ∀ v w, f v w ≤ c v w)
    (hcons : ∀ v ∈ S, v ≠ s → ∑ w, f v w - ∑ w, f w v = 0) :
    ∑ w, f s w - ∑ w, f w s ≤ ∑ v ∈ S, ∑ w ∈ Sᶜ, c v w := by
  have h := flow_out_of_cut_le_capacity f c S h0 hc
  rwa [Finset.sum_eq_single_of_mem s hs hcons] at h

/-! ### 6. The first person is an anchor -/

/-- A point's address from an anchor is zero only at the anchor. -/
theorem own_anchor_reads_zero {R : Type*} [AddGroup R] (a x : R) : x - a = 0 ↔ x = a := sub_eq_zero

/-- A point's address from another anchor is its address from one's own plus the displacement of the two anchors. -/
theorem name_from_another_anchor {R : Type*} [AddCommGroup R] (a b x : R) : x - b = (x - a) + (a - b) := by
  abel

/-- An anchor read through another's link stands at the anchors' displacement times that link's scale. -/
theorem anchor_read_through_another_link {R : Type*} [CommRing R] (a b v : R) : link b v a - b = v * (a - b) := by
  simp only [link]; ring

/-! ### 7. A draw is weighed by what its return did -/

/-- The term `(L i − mean)(1[i = j] − p j)` at a face's locus `j`, averaged over the face's own draws, is the face's share at
`j` times how far that act's return stands above the mean. -/
theorem draw_term_mean {ι : Type*} [Fintype ι] [DecidableEq ι] (p L : ι → ℝ) (hp : ∑ i, p i = 1) (j : ι) :
    ∑ i, p i * (L i - ∑ k, p k * L k) * ((if i = j then 1 else 0) - p j) = p j * (L j - ∑ k, p k * L k) := by
  obtain ⟨m, hm⟩ : ∃ m, m = ∑ k, p k * L k := ⟨_, rfl⟩
  rw [← hm]
  have h1 : ∑ i, p i * (L i - m) * (if i = j then 1 else 0) = p j * (L j - m) := by simp
  have h2 : ∑ i, p i * (L i - m) = 0 := by
    have h3 : ∑ i, p i * (L i - m) = ∑ i, p i * L i - m * ∑ i, p i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h3, hp, mul_one, ← hm, sub_self]
  calc ∑ i, p i * (L i - m) * ((if i = j then 1 else 0) - p j)
      = ∑ i, p i * (L i - m) * (if i = j then 1 else 0) - (∑ i, p i * (L i - m)) * p j := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = p j * (L j - m) := by rw [h1, h2, zero_mul, sub_zero]

/-- A constant added to every return moves nothing. -/
theorem baseline_moves_nothing {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (hp : ∑ i, p i = 1) (b : ℝ) (j : ι) :
    ∑ i, p i * b * ((if i = j then 1 else 0) - p j) = 0 := by
  have h1 : ∑ i, p i * b * (if i = j then 1 else 0) = p j * b := by simp
  calc ∑ i, p i * b * ((if i = j then 1 else 0) - p j)
      = ∑ i, p i * b * (if i = j then 1 else 0) - (∑ i, p i) * (b * p j) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 0 := by rw [h1, hp]; ring

/-- An answer no deposit moves stands at the same code before and after: its news stands, and its fall is nothing. -/
theorem news_stands_where_the_fall_is_nothing (c : ℝ) (hc : 0 < c) : 0 < c ∧ c - c = 0 :=
  ⟨hc, sub_self c⟩

end Holonics.HNN.ReachAndCapacity
