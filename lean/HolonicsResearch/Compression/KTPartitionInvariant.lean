import Mathlib
import Holonics.Compression.Landmark.Context.Tree

/-!
# A KT code split by a phase its context already carries is the node's code, face by face

Source: comment c6249536068 of #62, item 2 (`kt_code_partition_invariant`), on the founding law of
#398 (`hnn::founding::FoundingLaw::receive` at `d5ed4adc1`, its test
`a_class_carried_phase_leaves_the_split_and_node_kt_codes_identical`; atlas
`code.kt-partition-invariant`). A candidate ring of period `ℓ` splits the founding law's node: the
node counts each arriving class `y_k` at the cell `(k mod g, a_k)`, `g = gcd(ℓ, L)` with `L` the
cell clock and `a_k = y_(k − offset)` the context, and the split counts it at `(k mod ℓ, a_k)`.
Each law emits at a cell the Krichevsky–Trofimov face `q = (2N_y + 1)/(2n + |A|)` of that cell's
earlier arrivals, and its code is the product of its faces. The box: when the context determines
`k mod ℓ`, the split code equals the node code cell by cell.

## What is proved

* **The face is the KT face in the founding law's integer form.** `Context/Tree.ktFace` of a count
  table at the arriving class is `(2N_y + 1)/(2n + |A|)` (`ktProb_eq_odd`, `cellFace_eq`), the face
  `FoundingLaw::receive` appends to its code.
* **Two keyings that agree on the passage emit the same faces.** For any two keyings `s`, `t` of the
  counted cells `[o, n)`, if each earlier cell shares the arriving cell's `s`-key exactly when it
  shares its `t`-key, the two count tables at the arriving cell are equal
  (`cellCounts_eq_of_agree`), so are the faces (`cellFace_eq_of_agree`) and the codes
  (`keyedCode_eq_of_agree`). The split is a quotient of the passage's cells, and a code reads only
  which earlier cells meet the arriving one, never the names of the cells.
* **The box (`kt_code_partition_invariant`).** With `g ∣ ℓ` (so `g = gcd(ℓ, L)` among others), if
  two counted cells with the same context and the same node phase have the same split phase (in
  particular, if the context alone determines `k mod ℓ`, `kt_code_partition_invariant_of_context`),
  the split cell `(k mod ℓ, a_k)` and the node cell `(k mod g, a_k)` partition the passage alike
  (`split_node_agree`), so the split code equals the node code face by face. Its surplus over the
  node's code is then zero, and no description cost founds the ring
  (`surplus_zero_of_context_determines`).
* **The Rust fixture.** The test's stream `y_k = 2(k mod 2) + ⌊k/2⌋ mod 2` at offset one, period two
  and cell clock one has a context whose high digit is the previous cell's phase, so it determines
  `k mod 2` (`fixture_context_determines_phase`), and the split and node codes agree at every length,
  not only the test's 512 cells (`fixture_codes_equal`).
* **Without the hypothesis the codes part** (`phase_not_carried_parts_faces`): on the alternating
  stream with a constant context the split by period two and the node at clock one emit `3/4` and
  `1/2` at the third cell.

## Limits

* The keyings are given; the founding law's search over a family of periods, its maximum-likelihood
  node code and the universal-inference bound of item 1 stand beside this (box "Founding" of #410).
* Faces and codes are read in `ℚ`, the faces' own field; the Rust carries the code as a bounded
  product with its dyadic exponent, and the equality of carriers is the equality of these products.

The computational object is the helical pair interaction at the declared offset: a class `y_k` paired
with the class `offset` cells back. Of the winding guide's six objects this touches the helix (the
phase `k mod ℓ` of a candidate ring and `k mod g` of its node), the pair (the context `a_k`), and
faces and placement (the KT face each cell emits); cell holonomy, the tube and the tower thread stay
attached through `Context/Tree`.

Consumers: `Context/Tree`'s KT face (`ktFace`, `RegionCounts.ktProb`), the founding law's split and
node codes (`hnn::founding::FoundingLaw::{receive, read}` at `d5ed4adc1`), and the atlas row
`code.kt-partition-invariant`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.KTPartitionInvariant

open Holonics.Compression.Landmark.Context.Tree
open Holonics.HNN.RegionCounts (ktProb)

/-! ## 1. The face in the founding law's integer form -/

/-- [proved-derived; formal-checked] **The KT probability in odd form**:
`(n_c + 1/2)/(n + k/2) = (2n_c + 1)/(2n + k)`, the face the founding law appends. -/
theorem ktProb_eq_odd (nc n k : ℕ) : ktProb nc n k = (2 * nc + 1 : ℚ) / (2 * n + k) := by
  unfold ktProb
  rw [show (2 * nc + 1 : ℚ) = 2 * (nc + 1 / 2) by ring,
    show (2 * n + k : ℚ) = 2 * (n + k / 2) by ring, mul_div_mul_left _ _ two_ne_zero]

/-! ## 2. Keyed KT codes -/

section Keyed

variable {A : Type*} [Fintype A] [DecidableEq A] {S T : Type*} [DecidableEq S] [DecidableEq T]

/-- [definition] **A cell's count table**: for the arriving cell `k`, how many counted cells
`j ∈ [o, k)` share its key `s k` and carry class `c`. -/
def cellCounts (s : ℕ → S) (y : ℕ → A) (o k : ℕ) : A → ℕ :=
  fun c => ((Finset.Ico o k).filter fun j => s j = s k ∧ y j = c).card

/-- [definition] **The face a keyed law emits at cell `k`**: the KT face of its cell's count table
at the arriving class. -/
def cellFace (s : ℕ → S) (y : ℕ → A) (o k : ℕ) : ℚ := ktFace (cellCounts s y o k) (y k)

/-- [definition] **A keyed sequential KT code**: the product of the faces over the counted cells
`[o, n)`, the law's likelihood of the passage. -/
def keyedCode (s : ℕ → S) (y : ℕ → A) (o n : ℕ) : ℚ := ∏ k ∈ Finset.Ico o n, cellFace s y o k

/-- [proved-derived; formal-checked] A cell's count table sums to the earlier cells sharing its
key. -/
theorem sum_cellCounts (s : ℕ → S) (y : ℕ → A) (o k : ℕ) :
    ∑ c, cellCounts s y o k c = ((Finset.Ico o k).filter fun j => s j = s k).card := by
  classical
  unfold cellCounts
  rw [← Finset.card_biUnion]
  · congr 1
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨c, hj, hs, -⟩
      exact ⟨hj, hs⟩
    · rintro ⟨hj, hs⟩
      exact ⟨y j, hj, hs, rfl⟩
  · intro c _ c' _ hcc'
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    rintro j - ⟨-, hj⟩ ⟨-, hj'⟩
    exact hcc' (hj.symm.trans hj')

/-- [proved-derived; formal-checked] **The emitted face is `(2N_y + 1)/(2n + |A|)`**, with `N_y` the
earlier arrivals of the class at the cell and `n` all earlier arrivals at the cell: the face
`FoundingLaw::receive` appends to its code. -/
theorem cellFace_eq (s : ℕ → S) (y : ℕ → A) (o k : ℕ) :
    cellFace s y o k =
      (2 * (cellCounts s y o k (y k) : ℚ) + 1) /
        (2 * (((Finset.Ico o k).filter fun j => s j = s k).card : ℚ) + Fintype.card A) := by
  rw [cellFace, ktFace, ktProb_eq_odd, sum_cellCounts]

omit [Fintype A] in
/-- [proved-derived; formal-checked] **Two keyings that agree on the earlier cells have one count
table** at the arriving cell. -/
theorem cellCounts_eq_of_agree {s : ℕ → S} {t : ℕ → T} (y : ℕ → A) {o k : ℕ}
    (h : ∀ j ∈ Finset.Ico o k, (s j = s k ↔ t j = t k)) :
    cellCounts s y o k = cellCounts t y o k := by
  funext c
  unfold cellCounts
  congr 1
  exact Finset.filter_congr fun j hj => by rw [h j hj]

/-- [proved-derived; formal-checked] Two keyings that agree on the earlier cells emit one face. -/
theorem cellFace_eq_of_agree {s : ℕ → S} {t : ℕ → T} (y : ℕ → A) {o k : ℕ}
    (h : ∀ j ∈ Finset.Ico o k, (s j = s k ↔ t j = t k)) :
    cellFace s y o k = cellFace t y o k := by
  rw [cellFace, cellFace, cellCounts_eq_of_agree y h]

/-- [proved-derived; formal-checked] **Two keyings that partition the passage alike have one code**:
if at every counted cell the earlier cells sharing its `s`-key are those sharing its `t`-key, the
two sequential KT codes are equal. -/
theorem keyedCode_eq_of_agree {s : ℕ → S} {t : ℕ → T} (y : ℕ → A) {o n : ℕ}
    (h : ∀ k ∈ Finset.Ico o n, ∀ j ∈ Finset.Ico o k, (s j = s k ↔ t j = t k)) :
    keyedCode s y o n = keyedCode t y o n :=
  Finset.prod_congr rfl fun k hk => cellFace_eq_of_agree y (h k hk)

end Keyed

/-! ## 3. The split and the node -/

section SplitNode

variable {A : Type*} [Fintype A] [DecidableEq A] {C : Type*} [DecidableEq C]

/-- [definition] **The split cell** of a candidate ring of period `ℓ`: the phase `k mod ℓ` and the
context `a_k`. -/
def splitCell (ℓ : ℕ) (a : ℕ → C) (k : ℕ) : ℕ × C := (k % ℓ, a k)

/-- [definition] **The node cell** at `g = gcd(ℓ, L)`: the phase `k mod g` and the context. -/
def nodeCell (g : ℕ) (a : ℕ → C) (k : ℕ) : ℕ × C := (k % g, a k)

omit [DecidableEq C] in
/-- [proved-derived; formal-checked] **The split refines the node**: with `g ∣ ℓ`, two cells in one
split cell are in one node cell. -/
theorem node_of_split {g ℓ : ℕ} (hg : g ∣ ℓ) (a : ℕ → C) {j k : ℕ}
    (h : splitCell ℓ a j = splitCell ℓ a k) : nodeCell g a j = nodeCell g a k := by
  simp only [splitCell, nodeCell, Prod.mk.injEq] at h ⊢
  refine ⟨?_, h.2⟩
  rw [← Nat.mod_mod_of_dvd j hg, ← Nat.mod_mod_of_dvd k hg, h.1]

omit [DecidableEq C] in
/-- [proved-derived; formal-checked] **The split and the node partition alike** where two cells of
one context and one node phase share their split phase. -/
theorem split_node_agree {g ℓ : ℕ} (hg : g ∣ ℓ) (a : ℕ → C) {j k : ℕ}
    (hdet : a j = a k → j % g = k % g → j % ℓ = k % ℓ) :
    splitCell ℓ a j = splitCell ℓ a k ↔ nodeCell g a j = nodeCell g a k := by
  refine ⟨node_of_split hg a, fun h => ?_⟩
  simp only [splitCell, nodeCell, Prod.mk.injEq] at h ⊢
  exact ⟨hdet h.2 h.1, h.2⟩

/-- [proved-derived; formal-checked] **`kt_code_partition_invariant`.** Let `g ∣ ℓ` (the node
`g = gcd(ℓ, L)` of a candidate period `ℓ` on the cell clock `L`). If on the counted cells `[o, n)`
two cells of one context and one node phase share their phase modulo `ℓ`, the split law and the
node law emit the same KT face `(2N_y + 1)/(2n + |A|)` at every cell, and their codes are equal. -/
theorem kt_code_partition_invariant {g ℓ : ℕ} (hg : g ∣ ℓ) (a : ℕ → C) (y : ℕ → A) {o n : ℕ}
    (hdet : ∀ j ∈ Finset.Ico o n, ∀ k ∈ Finset.Ico o n,
      a j = a k → j % g = k % g → j % ℓ = k % ℓ) :
    (∀ k ∈ Finset.Ico o n, cellFace (splitCell ℓ a) y o k = cellFace (nodeCell g a) y o k) ∧
      keyedCode (splitCell ℓ a) y o n = keyedCode (nodeCell g a) y o n := by
  have hagree : ∀ k ∈ Finset.Ico o n, ∀ j ∈ Finset.Ico o k,
      (splitCell ℓ a j = splitCell ℓ a k ↔ nodeCell g a j = nodeCell g a k) := by
    intro k hk j hj
    have hj' : j ∈ Finset.Ico o n := by
      simp only [Finset.mem_Ico] at hj hk ⊢; omega
    exact split_node_agree hg a (hdet j hj' k hk)
  exact ⟨fun k hk => cellFace_eq_of_agree y (hagree k hk), keyedCode_eq_of_agree y hagree⟩

/-- [proved-derived; formal-checked] **The box's reading**: a context that determines `k mod ℓ` on
the counted cells leaves the split code equal to the node code, face by face, at `g = gcd(ℓ, L)`. -/
theorem kt_code_partition_invariant_of_context (ℓ L : ℕ) (a : ℕ → C) (y : ℕ → A) {o n : ℕ}
    (hdet : ∀ j ∈ Finset.Ico o n, ∀ k ∈ Finset.Ico o n, a j = a k → j % ℓ = k % ℓ) :
    (∀ k ∈ Finset.Ico o n,
        cellFace (splitCell ℓ a) y o k = cellFace (nodeCell (Nat.gcd ℓ L) a) y o k) ∧
      keyedCode (splitCell ℓ a) y o n = keyedCode (nodeCell (Nat.gcd ℓ L) a) y o n :=
  kt_code_partition_invariant (Nat.gcd_dvd_left ℓ L) a y fun j hj k hk h _ => hdet j hj k hk h

/-- [proved-derived; formal-checked] **Nothing to found.** Under the box's hypothesis the split's
code-length surplus over the node, `log₂(Q_split/Q_node)`, is zero, so no positive description cost
is paid out of it. -/
theorem surplus_zero_of_context_determines (ℓ L : ℕ) (a : ℕ → C) (y : ℕ → A) {o n : ℕ}
    (hdet : ∀ j ∈ Finset.Ico o n, ∀ k ∈ Finset.Ico o n, a j = a k → j % ℓ = k % ℓ) :
    Real.logb 2 ((keyedCode (splitCell ℓ a) y o n : ℝ) /
      (keyedCode (nodeCell (Nat.gcd ℓ L) a) y o n : ℝ)) = 0 := by
  rw [(kt_code_partition_invariant_of_context ℓ L a y hdet).2]
  by_cases h0 : (keyedCode (nodeCell (Nat.gcd ℓ L) a) y o n : ℝ) = 0
  · rw [h0, div_zero, Real.logb_zero]
  · rw [div_self h0, Real.logb_one]

end SplitNode

/-! ## 4. The Rust fixture and a phase the context does not carry -/

section Fixture

/-- [definition] The test stream `y_k = 2(k mod 2) + ⌊k/2⌋ mod 2` over four classes. -/
def fixture (k : ℕ) : Fin 4 := ⟨(k % 2) * 2 + (k / 2) % 2, by omega⟩

/-- [definition] Its context at offset one, `a_k = y_(k−1)`. -/
def fixtureContext (k : ℕ) : Fin 4 := fixture (k - 1)

/-- [proved-derived; formal-checked] **The fixture's context carries the phase**: the previous
class's high digit is the previous cell's phase, so on the counted cells `k ≥ 1` the context
determines `k mod 2`. -/
theorem fixture_context_determines_phase {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k)
    (h : fixtureContext j = fixtureContext k) : j % 2 = k % 2 := by
  have h' := congrArg Fin.val h
  simp only [fixtureContext, fixture] at h'
  omega

/-- [proved-derived; formal-checked] **The Rust test's equality at every length**: at offset one,
period two and cell clock one (node `gcd(2, 1) = 1`) the split and node codes of the fixture are
equal face by face. -/
theorem fixture_codes_equal (n : ℕ) :
    (∀ k ∈ Finset.Ico 1 n, cellFace (splitCell 2 fixtureContext) fixture 1 k =
        cellFace (nodeCell (Nat.gcd 2 1) fixtureContext) fixture 1 k) ∧
      keyedCode (splitCell 2 fixtureContext) fixture 1 n =
        keyedCode (nodeCell (Nat.gcd 2 1) fixtureContext) fixture 1 n :=
  kt_code_partition_invariant_of_context 2 1 fixtureContext fixture fun _ hj _ hk h =>
    fixture_context_determines_phase (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hk).1 h

/-- [definition] The alternating stream over two classes. -/
def alternating (k : ℕ) : Fin 2 := ⟨k % 2, Nat.mod_lt _ (by norm_num)⟩

/-- [proved-derived; formal-checked] **A phase the context does not carry parts the codes**: with a
constant context the split by period two emits `3/4` at the third cell of the alternating stream,
where the node at clock one emits `1/2`. -/
theorem phase_not_carried_parts_faces :
    cellFace (splitCell 2 fun _ => ()) alternating 0 2 = 3 / 4 ∧
      cellFace (nodeCell (Nat.gcd 2 1) fun _ => ()) alternating 0 2 = 1 / 2 := by
  have hs : ((Finset.Ico 0 2).filter fun j => splitCell 2 (fun _ => ()) j =
      splitCell 2 (fun _ => ()) 2).card = 1 := by decide
  have hn : ((Finset.Ico 0 2).filter fun j => nodeCell (Nat.gcd 2 1) (fun _ => ()) j =
      nodeCell (Nat.gcd 2 1) (fun _ => ()) 2).card = 2 := by decide
  have cs : cellCounts (splitCell 2 fun _ => ()) alternating 0 2 (alternating 2) = 1 := by decide
  have cn : cellCounts (nodeCell (Nat.gcd 2 1) fun _ => ()) alternating 0 2 (alternating 2) = 1 := by
    decide
  rw [cellFace_eq, cellFace_eq, hs, hn, cs, cn]
  norm_num

end Fixture

end Holonics.Compression.KTPartitionInvariant
