import Holonics.Compression.Landmark.Context.Merge
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Set.Finite.List

/-!
# The founded units' price is the change of the complete code, and the parse bounds the lattice's code

[proved-derived; formal-checked] The source is the record of October 23 on units founded by code length
(`research/records/2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY.md`;
atlas `hnn.founded-units`, `receiver.merge-segmentation-mass`) and its Rust owner `holonics_engine::units`
(`crates/engine/src/units.rs`). Units above the byte are founded from a passage: a pair `(a, b)` of adjacent units
becomes one unit `z` exactly when the complete code, the founding list's description plus the passage's order-one KT
code in the units, falls.

What is proved.

1. **The KT mass in Γ** (`ktSeq_eq_gamma`). The sequential Krichevsky–Trofimov mass of a word `y` over an alphabet of
   size `A > 0`, each symbol paid `(n_c + ½)/(t + A/2)` at its arrival (`ktSeq`, `ktSeq_snoc`), is
   `Π_c [Γ(n_c + ½)/Γ(½)] / [Γ(n + A/2)/Γ(A/2)]`; so, with `L(k) = log₂ Γ(k/2)` (`L`),
   `−log₂ KT(y) = L(2n + A) − L(A) − Σ_c [L(2n_c + 1) − L(1)]` (`neg_logb_ktSeq`), and the table's recurrence
   `L(k + 2) = L(k) + log₂ k − 1` is Γ's (`L_add_two`). A count of zero adds nothing (`ctxCode_zero`,
   `cellCredit_zero`), so the Rust's sums over the cells and contexts it holds are the sums over every symbol.
2. **The order-one KT code** (`neg_logb_orderOneMass`). With `succs s w` the units that follow `s` in `w` (`succs`),
   the order-one mass `W(w) = Π_s KT(succs s w)` (`orderOneMass`) has
   `−log₂ W = Σ_s [L(2n_s + A) − L(A)] − Σ_(s,c) [L(2n_sc + 1) − L(1)]` (`orderOneCode`), `n_s` the context's count and
   `n_sc` the adjacent count of `(s, c)` (`ctxCount`, `cellCount`).
3. **The price is the change of the complete code** (`price_eq_change`). The Rust's price, read from the count tables
   before and after a merge (`price`: the cells' credit change, the growth of every context's code from `A` to
   `A + 1` units, the changed contexts' moves at `A + 1`, and the founded unit's description `2 log₂ A + 1`,
   `describe`), equals `K′ − K` for the complete code `K = description + order-one code` (`completeUnitsCode`) with
   `A → A + 1` and the description grown by `2 log₂ A + 1`; `merge_price_eq_change` is the case `w′ = merge (a, b) → z`
   over its occurrences left to right without overlap (`mergeStep`).
4. **The join to `merge_cost_mass_iff`** (`price_neg_iff_mass`): with the description a mass `P = 2^(−description)`,
   the price is negative exactly when `P·W(w) < P′·W′(w′)`, `Merge.merge_cost_mass_iff` read on the units; the
   founded unit's description mass is `1/(2A²)` (`describe_mass`), so a merge is accepted exactly when the order-one
   mass grows by more than `2A²` (`price_neg_iff_ratio`).
5. **The parse decodes** (`decode_mergeStep`, `decode_parse`, `decode_parse_self`): a merge whose unit decodes to its
   pair's pieces leaves the decoded bytes unchanged, so replaying the founded merges in order reads the passage back
   whole. The Rust's pieces, `D(z_i) = D(a_i) D(b_i)` with `z_i = B + i` (`piece`, `triples`), meet that law for every
   merge of units standing at its founding (`piece_merge`, `founded_decode_parse`).
6. **The parse bounds the lattice's code** (`lattice_code_le_parse`). The segmentations of a source into units with
   nonempty pieces are finitely many (`fibre_finite`); the lattice's code `−log₂ Σ_(D w = x) P(w)` (`latticeCode`) is
   at most `−log₂ P(parse x)` for every nonnegative law with `P(parse x) > 0`, through
   `Merge.segmentation_code_le` (`latticeMass_eq_sourceMass`, `lattice_code_le`); it equals it exactly when no other
   segmentation carries mass (`lattice_code_eq_iff`).

What stands beside it. The Rust prices on the grain `2^(−32)` bits with a table enclosure (a price inside it is
refused as undecided) and computes the count changes incrementally from the taken occurrences (`changes`); the Lean
reads the after-counts as the merged word's own, and the incremental read's agreement with them is the Rust test
`each_price_is_the_change_of_the_order_one_code` on one passage, not a theorem here. The founding's proposal order,
its refusals at a count and its end are the realization's. The first symbol of a passage is not coded (the Rust reads
windows), and neither is the founding list's final stop bit. The order-one receiver is the declared price, not the
tower that reads the units.

The computational object is the helical pair interaction read on a passage's adjacent pairs: a founded unit is a pair
contact composed into one move, and its price is read from the cells the contact changes. Of the winding guide's six
general objects this touches the pair (the adjacent counts), faces and placement (the KT faces at each context) and
the tower thread (a unit restricts to its pair's pieces); the helix, the cell holonomy and the tube stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.FoundedUnitsPrice

open Finset Real
open Holonics.Compression.Landmark.Context.Merge (completeCode merge_cost_mass_iff sourceMass
  segmentation_code_le)

/-! ## 1. The KT mass in Γ -/

section KT

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The sequential KT mass read newest first: each symbol paid `(n_c + ½)/(t + A/2)` on the word before it. -/
noncomputable def ktRev (A : ℝ) : List α → ℝ
  | [] => 1
  | c :: r => ktRev A r * (((r.count c : ℕ) : ℝ) + 1 / 2) / (((r.length : ℕ) : ℝ) + A / 2)

/-- The sequential KT mass of a word, its symbols paid in arrival order. -/
noncomputable def ktSeq (A : ℝ) (y : List α) : ℝ := ktRev A y.reverse

omit [Fintype α] in
theorem ktSeq_nil (A : ℝ) : ktSeq A ([] : List α) = 1 := rfl

omit [Fintype α] in
theorem ktSeq_snoc (A : ℝ) (y : List α) (c : α) :
    ktSeq A (y ++ [c]) = ktSeq A y * (((y.count c : ℕ) : ℝ) + 1 / 2) / (((y.length : ℕ) : ℝ) + A / 2) := by
  simp [ktSeq, ktRev, List.count_reverse]

/-- `Γ(n + ½)/Γ(½)`, a symbol's KT numerator after `n` arrivals. -/
noncomputable def gammaHalf (n : ℕ) : ℝ := Gamma ((n : ℝ) + 1 / 2) / Gamma (1 / 2)

theorem gammaHalf_succ (n : ℕ) : gammaHalf (n + 1) = gammaHalf n * ((n : ℝ) + 1 / 2) := by
  unfold gammaHalf
  push_cast
  rw [show (n : ℝ) + 1 + 1 / 2 = ((n : ℝ) + 1 / 2) + 1 by ring, Gamma_add_one (by positivity)]
  ring

theorem gammaHalf_pos (n : ℕ) : 0 < gammaHalf n :=
  div_pos (Gamma_pos_of_pos (by positivity)) (Gamma_pos_of_pos (by norm_num))

/-- Statement 1: the sequential KT mass is `Π_c [Γ(n_c + ½)/Γ(½)] / [Γ(n + A/2)/Γ(A/2)]`. -/
theorem ktSeq_eq_gamma {A : ℝ} (hA : 0 < A) (y : List α) :
    ktSeq A y = (∏ c, gammaHalf (y.count c)) / (Gamma ((y.length : ℝ) + A / 2) / Gamma (A / 2)) := by
  induction y using List.reverseRecOn with
  | nil =>
    have h : Gamma (A / 2) ≠ 0 := (Gamma_pos_of_pos (by positivity)).ne'
    simp only [ktSeq_nil, gammaHalf, List.count_nil, List.length_nil, Nat.cast_zero, zero_add, div_self h,
      div_one]
    rw [div_self (Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne', Finset.prod_const_one]
  | append_singleton y d ih =>
    rw [ktSeq_snoc, ih]
    have hprod : ∏ c, gammaHalf ((y ++ [d]).count c)
        = (∏ c, gammaHalf (y.count c)) * (((y.count d : ℕ) : ℝ) + 1 / 2) := by
      have hc : ∀ c, gammaHalf ((y ++ [d]).count c)
          = gammaHalf (y.count c) * (if d = c then (((y.count d : ℕ) : ℝ) + 1 / 2) else 1) := by
        intro c
        rw [List.count_append]
        by_cases h : d = c
        · subst h
          simp [gammaHalf_succ]
        · have : [d].count c = 0 := by simpa [List.count_singleton] using h
          rw [this, Nat.add_zero, if_neg h, mul_one]
      rw [Finset.prod_congr rfl (fun c _ => hc c), Finset.prod_mul_distrib, Finset.prod_ite_eq]
      simp
    have hlen : Gamma ((((y ++ [d]).length : ℕ) : ℝ) + A / 2)
        = (((y.length : ℕ) : ℝ) + A / 2) * Gamma (((y.length : ℕ) : ℝ) + A / 2) := by
      rw [List.length_append, List.length_singleton]
      push_cast
      rw [show (y.length : ℝ) + 1 + A / 2 = ((y.length : ℝ) + A / 2) + 1 by ring, Gamma_add_one (by positivity)]
    rw [hprod, hlen]
    have h1 : 0 < Gamma (((y.length : ℕ) : ℝ) + A / 2) := Gamma_pos_of_pos (by positivity)
    have h2 : 0 < Gamma (A / 2) := Gamma_pos_of_pos (by positivity)
    have h3 : (0 : ℝ) < ((y.length : ℕ) : ℝ) + A / 2 := by positivity
    field_simp

theorem ktSeq_pos {A : ℝ} (hA : 0 < A) (y : List α) : 0 < ktSeq A y := by
  rw [ktSeq_eq_gamma hA]
  exact div_pos (Finset.prod_pos fun c _ => gammaHalf_pos _)
    (div_pos (Gamma_pos_of_pos (by positivity)) (Gamma_pos_of_pos (by positivity)))

/-- The code's table: `L(k) = log₂ Γ(k/2)`. -/
noncomputable def L (k : ℕ) : ℝ := logb 2 (Gamma ((k : ℝ) / 2))

/-- The table's recurrence is Γ's: `L(k + 2) = L(k) + log₂ k − 1`. -/
theorem L_add_two {k : ℕ} (hk : 0 < k) : L (k + 2) = L k + logb 2 k - 1 := by
  unfold L
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  push_cast
  rw [show ((k : ℝ) + 2) / 2 = (k : ℝ) / 2 + 1 by ring, Gamma_add_one (by positivity),
    logb_mul (by positivity) (Gamma_pos_of_pos (by positivity)).ne', logb_div hk'.ne' (by norm_num),
    logb_self_eq_one (by norm_num)]
  ring

/-- A context's code `L(2n + A) − L(A)`. -/
noncomputable def ctxCode (A n : ℕ) : ℝ := L (2 * n + A) - L A

/-- A cell's credit `L(2n + 1) − L(1)`. -/
noncomputable def cellCredit (n : ℕ) : ℝ := L (2 * n + 1) - L 1

@[simp] theorem ctxCode_zero (A : ℕ) : ctxCode A 0 = 0 := by simp [ctxCode]

@[simp] theorem cellCredit_zero : cellCredit 0 = 0 := by simp [cellCredit]

/-- Statement 1 in bits: `−log₂ KT(y) = L(2n + A) − L(A) − Σ_c [L(2n_c + 1) − L(1)]`. -/
theorem neg_logb_ktSeq {A : ℕ} (hA : 0 < A) (y : List α) :
    -logb 2 (ktSeq (A : ℝ) y) = ctxCode A y.length - ∑ c, cellCredit (y.count c) := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  rw [ktSeq_eq_gamma hA']
  have hP : ∀ c ∈ (univ : Finset α), gammaHalf (y.count c) ≠ 0 := fun c _ => (gammaHalf_pos _).ne'
  have h1 : 0 < Gamma ((y.length : ℝ) + (A : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Gamma ((A : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
  have h12 : (0 : ℝ) < Gamma (1 / 2) := Gamma_pos_of_pos (by norm_num)
  rw [logb_div (Finset.prod_pos fun c _ => gammaHalf_pos _).ne' (div_pos h1 h2).ne', logb_prod _ _ hP,
    logb_div h1.ne' h2.ne']
  unfold ctxCode cellCredit L gammaHalf
  have hsum : ∑ c, logb 2 (Gamma (((y.count c : ℕ) : ℝ) + 1 / 2) / Gamma (1 / 2))
      = ∑ c, (logb 2 (Gamma ((((2 * y.count c + 1 : ℕ)) : ℝ) / 2)) - logb 2 (Gamma (((1 : ℕ) : ℝ) / 2))) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [logb_div (Gamma_pos_of_pos (by positivity)).ne' h12.ne']
    push_cast
    congr 3
    ring
  rw [hsum]
  push_cast
  rw [show (2 * (y.length : ℝ) + A) / 2 = (y.length : ℝ) + A / 2 by ring]
  ring

end KT

/-! ## 2. The order-one KT code -/

section OrderOne

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The units that follow `s` in `w`, in order. -/
def succs (s : α) : List α → List α
  | x :: y :: r => (if x = s then [y] else []) ++ succs s (y :: r)
  | _ => []

/-- A context's count: how often `s` is followed. -/
def ctxCount (w : List α) (s : α) : ℕ := (succs s w).length

/-- A cell's count: how often `s` is followed by `c`. -/
def cellCount (w : List α) (s c : α) : ℕ := (succs s w).count c

/-- The order-one KT mass: each context's successors coded by KT over `A` units. -/
noncomputable def orderOneMass (A : ℝ) (w : List α) : ℝ := ∏ s, ktSeq A (succs s w)

/-- The order-one KT code the Rust reads from its count tables. -/
noncomputable def orderOneCode (A : ℕ) (w : List α) : ℝ :=
  ∑ s, ctxCode A (ctxCount w s) - ∑ s, ∑ c, cellCredit (cellCount w s c)

theorem orderOneMass_pos {A : ℝ} (hA : 0 < A) (w : List α) : 0 < orderOneMass A w :=
  Finset.prod_pos fun _ _ => ktSeq_pos hA _

/-- Statement 2: `−log₂ W = Σ_s [L(2n_s + A) − L(A)] − Σ_(s,c) [L(2n_sc + 1) − L(1)]`. -/
theorem neg_logb_orderOneMass {A : ℕ} (hA : 0 < A) (w : List α) :
    -logb 2 (orderOneMass (A : ℝ) w) = orderOneCode A w := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  rw [orderOneMass, logb_prod _ _ fun s _ => (ktSeq_pos hA' _).ne', ← Finset.sum_neg_distrib, orderOneCode,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => neg_logb_ktSeq hA _

end OrderOne

/-! ## 3. The price is the change of the complete code -/

section Price

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A founded unit's description: its ordered pair of the `A` units standing, and one bit for "another unit". -/
noncomputable def describe (A : ℕ) : ℝ := 2 * logb 2 A + 1

/-- The complete code: the founding list's description plus the order-one code in the units. -/
noncomputable def completeUnitsCode (desc : ℝ) (A : ℕ) (w : List α) : ℝ := desc + orderOneCode A w

/-- The Rust's price, read from the count tables before (`w`, `A` units) and after (`w′`, `A + 1` units): the cells'
credit change, the growth of every context's code, the changed contexts' moves and the description. -/
noncomputable def price (A : ℕ) (w w' : List α) : ℝ :=
  -(∑ s, ∑ c, (cellCredit (cellCount w' s c) - cellCredit (cellCount w s c)))
    + ∑ s, (ctxCode (A + 1) (ctxCount w s) - ctxCode A (ctxCount w s))
    + ∑ s, (ctxCode (A + 1) (ctxCount w' s) - ctxCode (A + 1) (ctxCount w s))
    + describe A

/-- Statement 3: the price is `K′ − K`. -/
theorem price_eq_change (A : ℕ) (desc : ℝ) (w w' : List α) :
    price A w w' = completeUnitsCode (desc + describe A) (A + 1) w' - completeUnitsCode desc A w := by
  unfold price completeUnitsCode orderOneCode
  simp only [Finset.sum_sub_distrib]
  ring

/-- A merge `(a, b) → z` over its occurrences taken left to right without overlap. -/
def mergeStep (a b z : α) : List α → List α
  | x :: y :: r => if x = a ∧ y = b then z :: mergeStep a b z r else x :: mergeStep a b z (y :: r)
  | l => l

theorem merge_price_eq_change (A : ℕ) (desc : ℝ) (a b z : α) (w : List α) :
    price A w (mergeStep a b z w)
      = completeUnitsCode (desc + describe A) (A + 1) (mergeStep a b z w) - completeUnitsCode desc A w :=
  price_eq_change A desc w _

/-- The founded unit's description mass is `1/(2A²)`. -/
theorem describe_mass {A : ℕ} (hA : 0 < A) : (2 : ℝ) ^ (-describe A) = 1 / (2 * (A : ℝ) ^ 2) := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  rw [describe, neg_add, rpow_add (by norm_num), show -(2 * logb 2 (A : ℝ)) = logb 2 (A : ℝ) * (-2) by ring,
    rpow_mul (by norm_num), rpow_logb (by norm_num) (by norm_num) hA', rpow_neg hA'.le, rpow_neg (by norm_num),
    rpow_one, rpow_two]
  field_simp

theorem completeUnitsCode_eq {A : ℕ} (hA : 0 < A) (desc : ℝ) (w : List α) :
    completeUnitsCode desc A w = completeCode (-logb 2 ((2 : ℝ) ^ (-desc))) (orderOneMass (A : ℝ) w) := by
  rw [completeUnitsCode, completeCode, logb_rpow (by norm_num) (by norm_num), ← neg_logb_orderOneMass hA]
  ring

/-- Statement 4: the price is negative exactly when `P·W(w) < P′·W′(w′)`, `merge_cost_mass_iff` on the units. -/
theorem price_neg_iff_mass {A : ℕ} (hA : 0 < A) (desc : ℝ) (w w' : List α) :
    price A w w' < 0 ↔
      (2 : ℝ) ^ (-desc) * orderOneMass (A : ℝ) w
        < (2 : ℝ) ^ (-(desc + describe A)) * orderOneMass ((A + 1 : ℕ) : ℝ) w' := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  rw [price_eq_change A desc, sub_neg, completeUnitsCode_eq (Nat.succ_pos A), completeUnitsCode_eq hA]
  exact merge_cost_mass_iff (by positivity) (by positivity) (orderOneMass_pos hA' w)
    (orderOneMass_pos (by positivity) w')

/-- A merge is accepted exactly when the order-one mass grows by more than `2A²`. -/
theorem price_neg_iff_ratio {A : ℕ} (hA : 0 < A) (desc : ℝ) (w w' : List α) :
    price A w w' < 0 ↔ 2 * (A : ℝ) ^ 2 * orderOneMass (A : ℝ) w < orderOneMass ((A + 1 : ℕ) : ℝ) w' := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  rw [price_neg_iff_mass hA desc w w', neg_add, rpow_add (by norm_num), describe_mass hA]
  have hP : (0 : ℝ) < (2 : ℝ) ^ (-desc) := by positivity
  have hA2 : (0 : ℝ) < 2 * (A : ℝ) ^ 2 := by positivity
  constructor
  · intro h
    have h' : (2 : ℝ) ^ (-desc) * (2 * (A : ℝ) ^ 2 * orderOneMass (A : ℝ) w)
        < (2 : ℝ) ^ (-desc) * orderOneMass ((A + 1 : ℕ) : ℝ) w' := by
      have := mul_lt_mul_of_pos_left h hA2
      calc (2 : ℝ) ^ (-desc) * (2 * (A : ℝ) ^ 2 * orderOneMass (A : ℝ) w)
          = 2 * (A : ℝ) ^ 2 * ((2 : ℝ) ^ (-desc) * orderOneMass (A : ℝ) w) := by ring
        _ < 2 * (A : ℝ) ^ 2 * ((2 : ℝ) ^ (-desc) * (1 / (2 * (A : ℝ) ^ 2)) * orderOneMass ((A + 1 : ℕ) : ℝ) w') :=
          this
        _ = (2 : ℝ) ^ (-desc) * orderOneMass ((A + 1 : ℕ) : ℝ) w' := by field_simp
    exact lt_of_mul_lt_mul_left h' hP.le
  · intro h
    have := mul_lt_mul_of_pos_left h (show (0 : ℝ) < (2 : ℝ) ^ (-desc) * (1 / (2 * (A : ℝ) ^ 2)) by positivity)
    calc (2 : ℝ) ^ (-desc) * orderOneMass (A : ℝ) w
        = (2 : ℝ) ^ (-desc) * (1 / (2 * (A : ℝ) ^ 2)) * (2 * (A : ℝ) ^ 2 * orderOneMass (A : ℝ) w) := by
          field_simp
      _ < _ := this

end Price

/-! ## 4. The parse decodes -/

section Parse

variable {α β : Type*} [DecidableEq α]

/-- Statement 5: a merge whose unit decodes to its pair's pieces leaves the decoded word unchanged. -/
theorem decode_mergeStep (piece : α → List β) {a b z : α} (hz : piece z = piece a ++ piece b) (w : List α) :
    (mergeStep a b z w).flatMap piece = w.flatMap piece := by
  fun_induction mergeStep a b z w with
  | case1 x y r h ih =>
    obtain ⟨rfl, rfl⟩ := h
    simp [ih, hz]
  | case2 x y r h ih => simp [ih]
  | case3 l h => rfl

/-- The founded merges replayed in order, each a triple `(a, b, z)`. -/
def parse (merges : List (α × α × α)) (w : List α) : List α :=
  merges.foldl (fun w m => mergeStep m.1 m.2.1 m.2.2 w) w

theorem decode_parse (piece : α → List β) (merges : List (α × α × α))
    (hm : ∀ m ∈ merges, piece m.2.2 = piece m.1 ++ piece m.2.1) (w : List α) :
    (parse merges w).flatMap piece = w.flatMap piece := by
  induction merges generalizing w with
  | nil => rfl
  | cons m ms ih =>
    simp only [parse, List.foldl_cons] at ih ⊢
    rw [ih (fun m' hm' => hm m' (List.mem_cons_of_mem _ hm')) _,
      decode_mergeStep piece (hm m List.mem_cons_self)]

/-- Replaying the merges reads a passage back whole when every byte decodes to itself. -/
theorem decode_parse_self (piece : α → List α) (merges : List (α × α × α))
    (hm : ∀ m ∈ merges, piece m.2.2 = piece m.1 ++ piece m.2.1) (x : List α) (hx : ∀ c ∈ x, piece c = [c]) :
    (parse merges x).flatMap piece = x := by
  rw [decode_parse piece merges hm]
  induction x with
  | nil => rfl
  | cons c r ih =>
    rw [List.flatMap_cons, hx c List.mem_cons_self, ih fun c' h => hx c' (List.mem_cons_of_mem _ h)]
    rfl

/-- The Rust's pieces: a byte `u < B` decodes to itself, the unit `B + i` to its merge's two pieces. -/
def piece (B : ℕ) (ms : List (ℕ × ℕ)) (u : ℕ) : List ℕ :=
  if u < B then [u] else
    match ms[u - B]? with
    | some ab => if _hab : ab.1 < u ∧ ab.2 < u then piece B ms ab.1 ++ piece B ms ab.2 else []
    | none => []
termination_by u
decreasing_by
  · exact _hab.1
  · exact _hab.2

/-- The merges as triples, the `i`-th founding the unit `B + i`. -/
def triples (B : ℕ) (ms : List (ℕ × ℕ)) : List (ℕ × ℕ × ℕ) := ms.mapIdx fun i ab => (ab.1, ab.2, B + i)

/-- Each merge reads units standing at its founding. -/
def Standing (B : ℕ) (ms : List (ℕ × ℕ)) : Prop := ∀ i (h : i < ms.length), ms[i].1 < B + i ∧ ms[i].2 < B + i

theorem piece_merge {B : ℕ} {ms : List (ℕ × ℕ)} (hs : Standing B ms) (i : ℕ) (h : i < ms.length) :
    piece B ms (B + i) = piece B ms ms[i].1 ++ piece B ms ms[i].2 := by
  rw [piece]
  have hB : ¬ B + i < B := by omega
  rw [if_neg hB]
  split
  · next ab hab =>
    have hi : B + i - B = i := by omega
    rw [hi, List.getElem?_eq_getElem h, Option.some.injEq] at hab
    subst hab
    rw [dif_pos (hs i h)]
  · next hn =>
    have hi : B + i - B = i := by omega
    rw [hi, List.getElem?_eq_getElem h] at hn
    exact absurd hn (by simp)

theorem triples_merge {B : ℕ} {ms : List (ℕ × ℕ)} (hs : Standing B ms) :
    ∀ m ∈ triples B ms, piece B ms m.2.2 = piece B ms m.1 ++ piece B ms m.2.1 := by
  intro m hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  have hi' : i < ms.length := by simpa [triples] using hi
  simp only [triples, List.getElem_mapIdx]
  exact piece_merge hs i hi'

/-- The founded units' parse decodes: `decode(parse(x)) = x` for every passage of bytes. -/
theorem founded_decode_parse {B : ℕ} {ms : List (ℕ × ℕ)} (hs : Standing B ms) (x : List ℕ) (hx : ∀ c ∈ x, c < B) :
    (parse (triples B ms) x).flatMap (piece B ms) = x :=
  decode_parse_self (piece B ms) (triples B ms) (triples_merge hs) x fun c hc => by
    rw [piece, if_pos (hx c hc)]

end Parse

/-! ## 5. The parse bounds the lattice's code -/

section Lattice

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/-- The segmentations of a source into units with nonempty pieces are finitely many. -/
theorem fibre_finite [Finite α] (piece : α → List β) (hne : ∀ u, piece u ≠ []) (x : List β) :
    {w : List α | w.flatMap piece = x}.Finite := by
  refine (List.finite_length_le α x.length).subset fun w hw => ?_
  simp only [Set.mem_ofPred_eq] at hw ⊢
  rw [← hw]
  clear hw
  induction w with
  | nil => simp
  | cons u r ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := List.length_pos_iff.2 (hne u)
    omega

/-- The lattice's mass over a finite set of segmentations: the mass of those that decode to the source. -/
def latticeMass (piece : α → List β) (P : List α → ℚ) (S : Finset (List α)) (x : List β) : ℚ :=
  ∑ w ∈ S.filter (fun w => w.flatMap piece = x), P w

omit [DecidableEq α] in
/-- The lattice's mass is `Merge.sourceMass` of the decoder on the segmentations. -/
theorem latticeMass_eq_sourceMass (piece : α → List β) (P : List α → ℚ) (S : Finset (List α)) (x : List β) :
    latticeMass piece P S x = sourceMass (fun w : S => (w : List α).flatMap piece) (fun w => P w) x := by
  unfold latticeMass sourceMass Holonics.Compression.Landmark.Context.Evolution.speciesWeight
  rw [Finset.sum_filter, Finset.sum_filter]
  exact (Finset.sum_coe_sort S (fun w => if w.flatMap piece = x then P w else 0)).symm

omit [DecidableEq α] in
/-- The lattice codes a source at most as any one of its segmentations: `Merge.segmentation_code_le`. -/
theorem lattice_code_le (piece : α → List β) {P : List α → ℚ} (hP : ∀ w, 0 ≤ P w) {S : Finset (List α)}
    {z : List α} (hzS : z ∈ S) (hz : 0 < P z) :
    -logb 2 (latticeMass piece P S (z.flatMap piece) : ℝ) ≤ -logb 2 (P z : ℝ) := by
  rw [latticeMass_eq_sourceMass]
  exact segmentation_code_le (fun w : S => (w : List α).flatMap piece) (fun w => hP w) ⟨z, hzS⟩ hz

/-- The lattice's code over every segmentation of a source. -/
noncomputable def latticeCode [Finite α] (piece : α → List β) (hne : ∀ u, piece u ≠ []) (P : List α → ℚ)
    (x : List β) : ℝ :=
  -logb 2 (latticeMass piece P (fibre_finite piece hne x).toFinset x : ℝ)

/-- Statement 6: the greedy parse's code bounds the lattice's code from above. -/
theorem lattice_code_le_parse [Finite α] (piece : α → List α) (hne : ∀ u, piece u ≠ [])
    (merges : List (α × α × α)) (hm : ∀ m ∈ merges, piece m.2.2 = piece m.1 ++ piece m.2.1) (x : List α)
    (hx : ∀ c ∈ x, piece c = [c]) {P : List α → ℚ} (hP : ∀ w, 0 ≤ P w) (hpos : 0 < P (parse merges x)) :
    latticeCode piece hne P x ≤ -logb 2 (P (parse merges x) : ℝ) := by
  have hdec := decode_parse_self piece merges hm x hx
  have hmem : parse merges x ∈ (fibre_finite piece hne x).toFinset := by simpa using hdec
  have := lattice_code_le piece hP hmem hpos
  rwa [hdec] at this

/-- The lattice's code equals one segmentation's exactly when no other segmentation carries mass. -/
theorem lattice_code_eq_iff (piece : α → List β) {P : List α → ℚ} (hP : ∀ w, 0 ≤ P w) {S : Finset (List α)}
    {z : List α} (hzS : z ∈ S) (hz : 0 < P z) :
    -logb 2 (latticeMass piece P S (z.flatMap piece) : ℝ) = -logb 2 (P z : ℝ) ↔
      ∀ w ∈ S, w.flatMap piece = z.flatMap piece → w ≠ z → P w = 0 := by
  set T := S.filter (fun w => w.flatMap piece = z.flatMap piece)
  have hzT : z ∈ T := Finset.mem_filter.2 ⟨hzS, rfl⟩
  have hsplit : latticeMass piece P S (z.flatMap piece) = P z + ∑ w ∈ T.erase z, P w := by
    rw [latticeMass, ← Finset.add_sum_erase _ _ hzT]
  have hrest : 0 ≤ ∑ w ∈ T.erase z, P w := Finset.sum_nonneg fun w _ => hP w
  have hpos : (0 : ℝ) < (latticeMass piece P S (z.flatMap piece) : ℝ) := by
    rw [hsplit]; push_cast; exact_mod_cast add_pos_of_pos_of_nonneg hz hrest
  have hzr : (0 : ℝ) < (P z : ℝ) := by exact_mod_cast hz
  rw [neg_inj]
  constructor
  · intro h w hwS hw hne
    have heq := logb_injOn_pos (b := 2) (by norm_num) (Set.mem_Ioi.2 hpos) (Set.mem_Ioi.2 hzr) h
    rw [hsplit] at heq
    have heq' : P z + ∑ w ∈ T.erase z, P w = P z := by exact_mod_cast heq
    have h0 : ∑ w ∈ T.erase z, P w = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hP w).1 h0 w
      (Finset.mem_erase.2 ⟨hne, Finset.mem_filter.2 ⟨hwS, hw⟩⟩)
  · intro h
    have h0 : ∑ w ∈ T.erase z, P w = 0 := Finset.sum_eq_zero fun w hw => by
      obtain ⟨hne, hwT⟩ := Finset.mem_erase.1 hw
      exact h w (Finset.mem_filter.1 hwT).1 (Finset.mem_filter.1 hwT).2 hne
    rw [hsplit, h0, add_zero]

end Lattice

end Holonics.HNN.FoundedUnitsPrice
