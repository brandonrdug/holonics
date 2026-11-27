import Mathlib

/-!
# A cell of whole periods counts its source's pulses once, a frame's count beats, counts cross a join one for one, a moved site turns the face, a push costs where the face is open, agreement costs its span, a ring is heard over its skin, a chain held two ways costs the cheaper and a bit, holding it whole is a new presentation of one ring, a carried key pairs as a conjunction, a charge is its news, and a nested store's depths are read on the graded pieces of its flag

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
3. **A moved site turns the strand face** (`moved_site_turns_rings`, `moved_site_inside_epoch_turns`). The strand face counts each
   place's ring phase from its epoch's site on the fine rings of periods 2, 3 and 4. A site moved by `δ` places leaves all three
   rings unturned exactly when 12 divides `δ`, so inside an epoch shorter than twelve places every moved site turns some ring:
   one word cut at two sites lands on two faces (atlas `tower.word-is-an-adopted-strand-cut-only-at-its-ends`).
4. **A push costs where the face is open** (`two_way_push_variance`, `two_way_push_variance_le`). On a face that gives `p` and
   `1 − p` to two symbols, a push of `a` and `b` on their logits has variance `p (1 − p) (a − b)²` under the face, the
   second-order cost of a push that carries no news: nothing on a pinned face (`p` at 0 or 1), at most `(a − b)²/4`, reached at
   an even face (atlas `code.handed-row-enters-at-its-capacity-price`).
5. **Agreement along a line costs its span, and a copy inside is free** (`span_insert_inside`, `span_le_insert`). Places on a
   line that share one bit cost the distance between the outermost two: a place added between them leaves it, and a place added
   anywhere never lowers it. A word's ends pay and its inside is free (atlas `tower.word-is-an-adopted-strand-cut-only-at-its-ends`).
6. **A ring is heard over its skin, and its phase returns only where the skin has spent it** (`skin_heard_iff`,
   `skin_at_period`, `coprime_rings_alias_iff`, `her_rings_alias`). A ring of period `P` with the skin `e^(−2π d/P)`, one e-fold
   a radian of turn, keeps at least `e^(−1)` of a place exactly within `P/(2π)` places, and at a lag of one whole period, where its
   phase first returns, it keeps `e^(−2π)`, about 0.0019. Places share every phase of coprime rings exactly at a multiple of
   their product, so her rings (powers of two to 4,096 and of three to 6,561) repeat only after 26,873,856 places. Her rings
   address a place by its age, within about a radian of turn, never by a phase that returns; a recurrence past the skins of her
   coarsest rings (about 650 and 1,040 places), or across a reset of her state, is heard only by what carries it farther (atlas
   `tower.level-hands-down-its-slow-store`).
7. **A chain held whole and by its pieces costs the cheaper path and a bit** (`two_paths_code_le`). A reader that gives the two
   paths equal weight codes the chain at `−log₂ ((p + q)/2)`, at most `−log₂ p + 1` for either path's `p`: a fluent reader and a
   newcomer are one reader holding both (atlas `tower.chain-becomes-a-part-held-beside-its-pieces`).
8. **Holding a chain whole is a new presentation of one ring, and its splits are a fibre** (`adjoin_part_same_ring`,
   `regarding_two_splits`, `regarding_splits_differ`). Adjoining a generator `t` with its defining relation `t = r` leaves the
   ring as it was, `R[t]/(t − r) ≅ R`: the fluent reader's `t` and the newcomer's `r` name one element, and the relation is the
   decoder they share. The product map from parts to words is not injective: `re·gard·ing` and `re·gar·ding` are two distinct
   lists of parts over the one word `regarding`, two points of its fibre.
9. **A carried key pairs as a conjunction** (`carry_pairing_le`, `carry_pairing_full_iff`). Two carries on the circles of `s`,
   with phase differences `θ j`, pair as `Σ_j cos θ_j`, at most the number of circles and equal to it exactly when they agree on
   every circle. A key that is the product of a prefix's moves is matched whole or not at all, where the sum of their logs, the
   additive face, pairs bilinearly and gives partial credit to every shared term: a bag.
10. **A charge is its news** (`delta_charge_contracts`, `delta_charge_zero_at_read`). The delta step `x + η (m − x)` moves an
    address's read toward its letter by `(1 − η)` of its distance, and an address that already reads its letter takes no charge,
    so a heavy address saturates where a summed charge grows with every word that shares it.
11. **A nested store is a flag, and a depth's worth is its slope on its graded piece** (`flag_increments_telescope`,
    `flag_slopes_tail_sums`). The address of length `k + 1` fixes the address of length `k`, so the reads `x_0, …, x_(n−1)` at the
    depths sit on a flag. Their graded pieces `x_k − x_(k−1)` (with `x_(−1) = 0`) telescope back to the deepest read, and a read
    `Σ_k a_k x_k` is the same read `Σ_k b_k (x_k − x_(k−1))` with `b_k = Σ_(j ≥ k) a_j`: the slope on the news depth `k` adds over
    depth `k − 1` is the tail sum of the slopes from `k` down. A fit on the reads themselves trades neighbours; the tail sums are
    the same fit read in the flag's own coordinates.
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

/-- A unit's unsaid share is read in its own unit: its places coded at a common scale `c` (twice over, or at another grain of
nats) leave the share of the unit the join left unsaid where it was. -/
theorem unsaid_share_scale_free {R Z c : ℝ} (hc : c ≠ 0) : (c * R) / (c * Z) = R / Z :=
  mul_div_mul_left R Z hc

/-- A site moved by `δ` places leaves the fine rings of periods 2, 3 and 4 unturned exactly when twelve divides `δ`. -/
theorem moved_site_turns_rings (δ : ℤ) : (2 ∣ δ ∧ 3 ∣ δ ∧ 4 ∣ δ) ↔ 12 ∣ δ := by
  omega

/-- Inside an epoch shorter than twelve places, every moved site turns at least one of the three rings. -/
theorem moved_site_inside_epoch_turns (δ : ℤ) (h0 : 0 < δ) (h12 : δ < 12) : ¬ (2 ∣ δ ∧ 3 ∣ δ ∧ 4 ∣ δ) := by
  omega

/-- On a two-way face `(p, 1 − p)`, a push `(a, b)` on the logits has variance `p (1 − p) (a − b)²` under the face. -/
theorem two_way_push_variance (p a b : ℝ) :
    p * a ^ 2 + (1 - p) * b ^ 2 - (p * a + (1 - p) * b) ^ 2 = p * (1 - p) * (a - b) ^ 2 := by
  ring

/-- That variance is at most a quarter of the push's spread, reached at an even face, and nothing on a pinned one. -/
theorem two_way_push_variance_le (p a b : ℝ) : p * (1 - p) * (a - b) ^ 2 ≤ (a - b) ^ 2 / 4 := by
  nlinarith [sq_nonneg (p - 1 / 2), sq_nonneg (a - b), mul_nonneg (sq_nonneg (p - 1 / 2)) (sq_nonneg (a - b))]

/-- A place added inside the span of places on a line leaves the span: a copy inside is free. -/
theorem span_insert_inside (s : Finset ℝ) (h : s.Nonempty) (x : ℝ) (hlo : s.min' h ≤ x) (hhi : x ≤ s.max' h) :
    (insert x s).max' (s.insert_nonempty x) - (insert x s).min' (s.insert_nonempty x) = s.max' h - s.min' h := by
  rw [Finset.max'_insert x s h, Finset.min'_insert x s h, max_eq_right hhi, min_eq_right hlo]

/-- A place added anywhere never lowers the span of places on a line. -/
theorem span_le_insert (s : Finset ℝ) (h : s.Nonempty) (x : ℝ) :
    s.max' h - s.min' h ≤ (insert x s).max' (s.insert_nonempty x) - (insert x s).min' (s.insert_nonempty x) := by
  rw [Finset.max'_insert x s h, Finset.min'_insert x s h]
  have h1 := le_max_right x (s.max' h)
  have h2 := min_le_right x (s.min' h)
  linarith

/-- Two places at lag `d` share their phase on coprime rings of periods `m` and `n` exactly when `m n` divides `d`. -/
theorem coprime_rings_alias_iff {m n d : ℕ} (hmn : Nat.Coprime m n) :
    (m ∣ d ∧ n ∣ d) ↔ m * n ∣ d :=
  ⟨fun ⟨hm, hn⟩ => hmn.mul_dvd_of_dvd_of_dvd hm hn,
   fun h => ⟨(Dvd.intro n rfl).trans h, (Dvd.intro_left m rfl).trans h⟩⟩

/-- Her coarsest rings, of 4,096 and 6,561 places, share their phase only at a multiple of 26,873,856 places, and every finer
ring of hers divides one of them. -/
theorem her_rings_alias (d : ℕ) : (4096 ∣ d ∧ 6561 ∣ d) ↔ 26873856 ∣ d :=
  coprime_rings_alias_iff (m := 4096) (n := 6561) (by norm_num)

/-- A ring of period `P` with skin `e^(−2π d/P)` keeps at least `e^(−1)` of a place exactly within `P/(2π)` places. -/
theorem skin_heard_iff (P d : ℝ) (hP : 0 < P) :
    Real.exp (-1) ≤ Real.exp (-(2 * Real.pi * d / P)) ↔ d ≤ P / (2 * Real.pi) := by
  rw [Real.exp_le_exp, neg_le_neg_iff, div_le_one hP, le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- At a lag of one whole period, where the ring's phase first returns, its skin keeps `e^(−2π)`. -/
theorem skin_at_period (P : ℝ) (hP : P ≠ 0) :
    Real.exp (-(2 * Real.pi * P / P)) = Real.exp (-(2 * Real.pi)) := by
  rw [mul_div_assoc, div_self hP, mul_one]

/-- A chain held two ways with equal weight, whole (`p`) and by its pieces (`q`), costs at most either path's code and one bit. -/
theorem two_paths_code_le (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    -Real.logb 2 ((p + q) / 2) ≤ -Real.logb 2 p + 1 := by
  have h1 : p / 2 ≤ (p + q) / 2 := by linarith
  have h2 : Real.logb 2 (p / 2) ≤ Real.logb 2 ((p + q) / 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
  have h3 : Real.logb 2 (p / 2) = Real.logb 2 p - 1 := by
    rw [Real.logb_div hp.ne' two_ne_zero, Real.logb_self_eq_one (by norm_num)]
  linarith

/-- Adjoining a generator with its defining relation, `R[t]/(t − r)`, leaves the ring as it was. -/
noncomputable def adjoin_part_same_ring {R : Type*} [CommRing R] (r : R) :
    (Polynomial R ⧸ Ideal.span {Polynomial.X - Polynomial.C r}) ≃ₐ[R] R :=
  Polynomial.quotientSpanXSubCAlgEquiv r

/-- Two splits of one word: `re·gard·ing` and `re·gar·ding` compose to the same string. -/
theorem regarding_two_splits : ("re" ++ "gard" ++ "ing") = ("re" ++ "gar" ++ "ding") := by decide

/-- The two splits are distinct lists of parts: the product map from parts to words has two points over `regarding`. -/
theorem regarding_splits_differ : ["re", "gard", "ing"] ≠ ["re", "gar", "ding"] := by decide

/-- Two carries on the circles of `s` pair at most at the number of circles. -/
theorem carry_pairing_le {ι : Type*} (s : Finset ι) (θ : ι → ℝ) :
    (∑ j ∈ s, Real.cos (θ j)) ≤ (s.card : ℝ) := by
  have hc : (s.card : ℝ) = ∑ j ∈ s, (1 : ℝ) := by simp
  rw [hc]
  exact Finset.sum_le_sum fun j _ => Real.cos_le_one _

/-- Two carries pair fully exactly when they agree on every circle: the carried key is a conjunction. -/
theorem carry_pairing_full_iff {ι : Type*} (s : Finset ι) (θ : ι → ℝ) :
    (∑ j ∈ s, Real.cos (θ j)) = (s.card : ℝ) ↔ ∀ j ∈ s, Real.cos (θ j) = 1 := by
  have h : ∀ j ∈ s, Real.cos (θ j) ≤ 1 := fun j _ => Real.cos_le_one _
  have hc : (s.card : ℝ) = ∑ j ∈ s, (1 : ℝ) := by simp
  rw [hc]
  exact Finset.sum_eq_sum_iff_of_le h

/-- The delta step moves an address's read toward its letter by `(1 − η)` of its distance. -/
theorem delta_charge_contracts (x m η : ℝ) : x + η * (m - x) - m = (1 - η) * (x - m) := by
  ring

/-- An address that already reads its letter takes no charge. -/
theorem delta_charge_zero_at_read (x m η : ℝ) (h : x = m) : η * (m - x) = 0 := by
  simp [h]

/-- The graded pieces of a flag of reads telescope back to the deepest read. -/
theorem flag_increments_telescope (r : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (r k - if k = 0 then 0 else r (k - 1)) = r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp

/-- A read on the depths of a flag is the same read on its graded pieces, each piece weighed by the tail sum of the slopes from
its depth down (Abel summation). -/
theorem flag_slopes_tail_sums (a r : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, a k * r k =
      ∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico k n, a j) * (r k - if k = 0 then 0 else r (k - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ k ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.Ico k (n + 1), a j) * (r k - if k = 0 then 0 else r (k - 1)) =
        ∑ k ∈ Finset.range (n + 1),
          ((∑ j ∈ Finset.Ico k n, a j) * (r k - if k = 0 then 0 else r (k - 1)) +
            a n * (r k - if k = 0 then 0 else r (k - 1))) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.sum_Ico_succ_top (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), add_mul]
    rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, flag_increments_telescope,
      Finset.sum_range_succ (fun k => (∑ j ∈ Finset.Ico k n, a j) * (r k - if k = 0 then 0 else r (k - 1))),
      Finset.Ico_self, Finset.sum_empty, zero_mul, add_zero, ← ih, Finset.sum_range_succ]

end Holonics.HNN.OwnCycleCells
