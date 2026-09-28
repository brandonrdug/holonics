import Holonics.Compression.Landmark.Context.Evolution

/-!
# Merges: species of cells, priced by their code-length pair

[definition; agent-inferred] The merge law of campaign 5 (`research/records/2026-09-25_THE_
COMPRESSION_IS_OF_LANDMARKS_A_TREE_COCYCLE_AND_MERGES_PRICED_BY_THEIR_CODE_LENGTH_PAIR.md`, §5;
`docs/plans/THE_REBUILD.md`, campaign 5; Rust `receiver::population::merge`). A **merge** is a map
`σ : C → S` of cells onto merged cells: of symbols onto a coarser alphabet (a tokenizer's pair
`c ↦ ab` read backwards, a word's letters onto the word), or of the cells of a partition onto its
blocks (the hazard's last-byte classes; a thin port's cells onto another port's). Two eggs are one
species when every admitted future receiver reads them alike (`Evolution.species_collapse_code`);
a merge is the same quotient applied to cells, and it is either a **release** (no admitted face
changes) or **priced** (the faces change and the complete description must fall).

* `expand_merge`, `expansion_sum`, `mergedFace_isPrior` [proved-derived; formal-checked]: **a
  merged cell's face reconstructs its members' faces by the declared expansion**. The merged face
  is the push-forward `Q(s) = Σ_(σ c = s) q(c)` (`Evolution.speciesWeight`), a face wherever `q`
  is, and the expansion `e(c) = q(c)/Q(σ c)` is a face on every fibre of positive mass, with
  `q(c) = Q(σ c)·e(c)` for every member (a member of a massless fibre reads zero on both sides).
* `merge_cost_iff`, `merge_cost_nat`, `merge_cost_mass_iff` [proved-derived; formal-checked]:
  **the code-length pair**. With the complete descriptions `K = ℓ − log₂ W_G(z)` and
  `K′ = ℓ′ − log₂ W_(G′)(z′)` and `d = ℓ′ − ℓ`, the merge lowers the code exactly when
  `W_(G′)(z′)/W_G(z) > 2^d`; for a whole `d` and rational likelihoods `a/b`, `a′/b′` it is the
  integer comparison `a·b′·2^d < a′·b`; and when both descriptions are masses (`ℓ = −log₂ P`), it is
  `P·W < P′·W′`, one comparison of positive rationals.
* `restaurant_found`, `restaurant_join`, `restaurant_step_sum`, `restaurant_merge_ratio`
  [proved-derived; formal-checked]: **the description of a partition** (agent-inferred, the charge
  the Rust owner uses). The restaurant mass at `α = ½`, `P(π) = α^k ∏_B (|B| − 1)! / ∏_(j<N)(j + α)`
  over `N` cells in `k` blocks, is KT's one-per-two for partitions: seating the next cell founds a
  block with face `α/(N + α)` or joins a block of `m` with face `m/(N + α)`, the seatings'
  faces sum to one at every step, and the mass is their product (`restaurant_found`,
  `restaurant_join`). [proved-standard] (Ewens 1972; Pitman) Summed over the set partitions of `N`
  cells the mass is one, so `−log₂ P(π)` is a prefix code of the partition. **A merge of blocks of
  `a` and `b` cells multiplies it by `2·(a + b − 1)!/((a − 1)!(b − 1)!)`**, never below `2`: a
  merge that leaves the likelihood unchanged always shortens the description.
* `segmentation_mass`, `parse_given_sum`, `parse_code`, `segmentation_code_le` [proved-derived;
  formal-checked]: **one source, several alphabets.** For a decoder `D : Z → X` of symbol words
  (segmentations) and a law `P` on them, the source mass `P_G(x) = Σ_(D z = x) P(z)` is a
  probability law (the same push-forward); the parse given its source is a face on its fibre; a
  transmitted parse pays `−log₂ P(z) = −log₂ P_G(x) − log₂ P(z | x)`, once; and the lattice codes a
  source at most as any one of its parses (the byte path is the lossless fallback).
* `square_iff_no_separator`, `encoding_square_or_separator`, `merged_square_of_compatible`
  [proved-derived; formal-checked]: **`D E = ρ` and `E_next T = U E` on the merged encoding, or a
  separator.** For an encoding `E`, its successor chart `E_next`, an action `T`, a reading `ρ` and a
  merge `σ`, a decoder `D′` and a transport `U′` with `D′ (σ E x) = ρ x` and
  `σ (E_next (T x)) = U′ (σ E x)` exist exactly when no **separator** exists: a pair of cells the
  merged encoding identifies whose readings, or whose successors' merged encodings, differ. When the
  unmerged square holds and the decoder and transport respect the merge, the merged square holds.
  The one-reading form is `Holon/Restriction.descent_total` (a reading descends through a
  restriction or a merged pair separates it); this is its pair form, the reading and the successor's
  merged encoding read together, with the decoder and the transport it returns.
* `release_merge_iff_future_equivalent`, `release_merge_code` [proved-derived; formal-checked]:
  **a merge is a lawful release exactly when its merged cells are future-equivalent.** A release
  keeps one face per merged cell, from which every member's face is read at every admitted tick
  (`∃ g, f k t = g (σ k) t` for `t < h`); that holds exactly when members of one merged cell agree at
  every admitted tick. Then the merged mixture at the summed weights codes every passage within the
  admitted future exactly as the unmerged one (`Evolution.species_collapse_code` with the merged
  face in place of a representative). [correction, Sol] A merge that stops shortening the code is not
  thereby releasable: release needs this equivalence, which the code-length pair does not test.
* `equal_present_faces_do_not_merge` [counterexample; formal-checked] (U2; GPT-6 Astra's review of
  September 28): **equal present faces do not make a merge of tree contexts lawful.** At depth one,
  after one arrival of class `0` at `[0]` and one at `[1]`, the two contexts read every class alike
  (`4/5` and `1/5`); after one further arrival of class `1` at `[0]` they read `9/16` and `11/16`. A
  merge stores the two contexts in one register, which reads them alike after every word, so no
  lawful `Foundation/Standing.StandingLaw` of the tree under arrivals reads them through one register.
  Equal code on validation cells is agreement along the words those cells are, and fails the same
  way. The merges and releases of the tree that are future-sufficient are derived in the tree's
  owner (`compression::landmark::context`, "Which merges and releases are future-sufficient").
* `coarsening_within_margin_iff` [proved-derived; formal-checked] (U2): **the charged coarsening
  law.** A declared coarser receiver (a shallower depth, a founding rule, a merge of contexts) is not
  a retention of the finer one; it is priced against it. With both complete descriptions masses, the
  coarser code lies within a margin of `m` bits of the finer exactly when `P·W ≤ 2^m·P′·W′`
  (`merge_cost_mass_iff` at the margin `m`).

The computational object is the helical pair interaction read as the receiver's cells and their
merges. Of the winding guide's six general objects this module touches **faces and placement**
(the merged face and its expansion, the partition's cells), the **tower thread** (a merge is a
coarsening: members restrict to their merged cell) and, through the admitted future, the **helix**
(a key's clock read over the admitted ticks); the pair, the cell holonomy and the tube stay attached
through the families' owners.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.Merge

open Finset
open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.LocalWeighing
open Holonics.Compression.Landmark.Context.Population
open Holonics.Compression.Landmark.Context.Evolution

/-! ## 1. The merged face and its expansion -/

section Expansion

variable {C S : Type*} [Fintype C] [Fintype S] [DecidableEq C] [DecidableEq S]

/-- [definition] **The declared expansion** of a merged cell: each member's share of its merged
cell's face, `e(c) = q(c)/Q(σ c)`, `Q = speciesWeight σ q` the push-forward. -/
def expansion (σ : C → S) (q : C → ℚ) (c : C) : ℚ := q c / speciesWeight σ q (σ c)

/-- [proved-derived; formal-checked] **The merged face is a face** wherever the members' is. -/
theorem mergedFace_isPrior (σ : C → S) {q : C → ℚ} (hq : IsPrior q) :
    IsPrior (speciesWeight σ q) :=
  speciesWeight_isPrior σ hq

omit [Fintype S] [DecidableEq C] in
/-- [proved-derived; formal-checked] **The expansion is a face on every fibre of positive mass.** -/
theorem expansion_sum (σ : C → S) (q : C → ℚ) (s : S) (hs : speciesWeight σ q s ≠ 0) :
    ∑ c ∈ univ.filter (fun c => σ c = s), expansion σ q c = 1 := by
  have : ∀ c ∈ univ.filter (fun c => σ c = s), expansion σ q c = q c / speciesWeight σ q s := by
    intro c hc
    rw [expansion, (mem_filter.1 hc).2]
  rw [sum_congr rfl this, ← sum_div]
  exact div_self hs

omit [Fintype S] [DecidableEq C] in
/-- [proved-derived; formal-checked] **`expand_merge`: a merged cell's face reconstructs its
members' faces by the declared expansion**, `q(c) = Q(σ c)·e(c)`, for a nonnegative face. -/
theorem expand_merge (σ : C → S) {q : C → ℚ} (hq : ∀ c, 0 ≤ q c) (c : C) :
    q c = speciesWeight σ q (σ c) * expansion σ q c := by
  by_cases h : speciesWeight σ q (σ c) = 0
  · have hle : q c ≤ speciesWeight σ q (σ c) :=
      single_le_sum (f := q) (fun k _ => hq k) (mem_filter.2 ⟨mem_univ c, rfl⟩)
    have hc : q c = 0 := le_antisymm (by rw [h] at hle; exact hle) (hq c)
    rw [h, zero_mul, hc]
  · rw [expansion, mul_div_cancel₀ _ h]

end Expansion

/-! ## 2. The code-length pair -/

section Cost

/-- [definition] **The complete description** of a decoder of `ℓ` bits and its word of
likelihood `W`: `K = ℓ − log₂ W`. -/
def completeCode (ℓ W : ℝ) : ℝ := ℓ - Real.logb 2 W

/-- [proved-derived; formal-checked] **`merge_cost_iff`: a merge lowers the code exactly when its
likelihood ratio passes its description charge**, `K′ < K ↔ W·2^(ℓ′ − ℓ) < W′`. -/
theorem merge_cost_iff {ℓ ℓ' W W' : ℝ} (hW : 0 < W) (hW' : 0 < W') :
    completeCode ℓ' W' < completeCode ℓ W ↔ W * (2 : ℝ) ^ (ℓ' - ℓ) < W' := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (ℓ' - ℓ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [← Real.logb_lt_logb_iff (b := 2) (by norm_num) (mul_pos hW h2) hW',
    Real.logb_mul hW.ne' h2.ne', Real.logb_rpow (by norm_num) (by norm_num)]
  unfold completeCode
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **The integer comparison**: for a whole charge `d` and rational
likelihoods `a/b`, `a′/b′` with positive denominators, `W·2^d < W′ ↔ a·b′·2^d < a′·b`. -/
theorem merge_cost_nat {a b a' b' : ℕ} (hb : 0 < b) (hb' : 0 < b') (d : ℕ) :
    (a : ℚ) / b * 2 ^ d < (a' : ℚ) / b' ↔ a * b' * 2 ^ d < a' * b := by
  have hb0 : (0 : ℚ) < b := by exact_mod_cast hb
  have hb0' : (0 : ℚ) < b' := by exact_mod_cast hb'
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ hb0 hb0']
  have : ((a : ℚ) * 2 ^ d * b' < a' * b) ↔ ((a * b' * 2 ^ d : ℕ) : ℚ) < ((a' * b : ℕ) : ℚ) := by
    push_cast
    constructor <;> intro h <;> linarith
  rw [this]
  exact_mod_cast Iff.rfl

/-- [proved-derived; formal-checked] **Descriptions that are masses**: with `ℓ = −log₂ P` and
`ℓ′ = −log₂ P′`, the merge lowers the complete code exactly when `P·W < P′·W′`. -/
theorem merge_cost_mass_iff {P P' W W' : ℝ} (hP : 0 < P) (hP' : 0 < P') (hW : 0 < W)
    (hW' : 0 < W') :
    completeCode (-Real.logb 2 P') W' < completeCode (-Real.logb 2 P) W ↔ P * W < P' * W' := by
  rw [← Real.logb_lt_logb_iff (b := 2) (by norm_num) (mul_pos hP hW) (mul_pos hP' hW'),
    Real.logb_mul hP.ne' hW.ne', Real.logb_mul hP'.ne' hW'.ne']
  unfold completeCode
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **`coarsening_within_margin_iff`: a coarsening is within a margin
of `m` bits exactly when `P·W ≤ 2^m·P′·W′`.** The charged coarsening law (module header): the coarser
complete code `K′ = −log₂ P′ − log₂ W′` lies within `m` bits of the finer `K = −log₂ P − log₂ W`. -/
theorem coarsening_within_margin_iff {P P' W W' m : ℝ} (hP : 0 < P) (hP' : 0 < P') (hW : 0 < W)
    (hW' : 0 < W') :
    completeCode (-Real.logb 2 P') W' ≤ completeCode (-Real.logb 2 P) W + m ↔
      P * W ≤ (2 : ℝ) ^ m * (P' * W') := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := Real.rpow_pos_of_pos (by norm_num) _
  rw [← Real.logb_le_logb (b := 2) (by norm_num) (mul_pos hP hW) (mul_pos h2 (mul_pos hP' hW')),
    Real.logb_mul hP.ne' hW.ne', Real.logb_mul h2.ne' (mul_pos hP' hW').ne',
    Real.logb_mul hP'.ne' hW'.ne', Real.logb_rpow (by norm_num) (by norm_num)]
  unfold completeCode
  constructor <;> intro h <;> linarith

end Cost

/-! ## 3. The description of a partition: the restaurant mass at `α = ½` -/

section Restaurant

/-- [definition] **The restaurant mass at `α = ½`** of a partition whose blocks hold `s` cells:
`α^k ∏_B (|B| − 1)! / ∏_(j<N) (j + α)`, `k` the blocks and `N = Σ s` the cells. -/
def restaurantMass (s : List ℕ) : ℚ :=
  (1 / 2 : ℚ) ^ s.length * (s.map fun m => ((m - 1).factorial : ℚ)).prod /
    ∏ j ∈ range s.sum, ((j : ℚ) + 1 / 2)

theorem restaurant_den_pos (N : ℕ) : 0 < ∏ j ∈ range N, ((j : ℚ) + 1 / 2) :=
  prod_pos fun j _ => by positivity

/-- [proved-derived; formal-checked] **Founding a block**: a new cell seated alone multiplies the
mass by `α/(N + α)`. -/
theorem restaurant_found (s : List ℕ) :
    restaurantMass (1 :: s) = restaurantMass s * ((1 / 2) / ((s.sum : ℚ) + 1 / 2)) := by
  have hD := restaurant_den_pos s.sum
  have hN : (0 : ℚ) < (s.sum : ℚ) + 1 / 2 := by positivity
  simp only [restaurantMass, List.length_cons, List.map_cons, List.prod_cons, List.sum_cons]
  rw [add_comm 1 s.sum, prod_range_succ]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul, pow_succ]
  field_simp

/-- [proved-derived; formal-checked] **Joining a block of `m ≥ 1`**: the cell seated there
multiplies the mass by `m/(N + α)`, `N` the cells seated before it. -/
theorem restaurant_join (m : ℕ) (hm : 1 ≤ m) (s : List ℕ) :
    restaurantMass ((m + 1) :: s) =
      restaurantMass (m :: s) * ((m : ℚ) / ((m : ℚ) + s.sum + 1 / 2)) := by
  have hD := restaurant_den_pos (m + s.sum)
  have hN : (0 : ℚ) < (m : ℚ) + s.sum + 1 / 2 := by positivity
  simp only [restaurantMass, List.length_cons, List.map_cons, List.prod_cons, List.sum_cons]
  rw [show m + 1 + s.sum = (m + s.sum) + 1 by omega, prod_range_succ]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

/-- [proved-derived; formal-checked] **The seatings are a face at every step**: over blocks holding
`N = Σ s` cells, the joins' faces `m/(N + α)` and the founding's `α/(N + α)` sum to one. -/
theorem restaurant_step_sum (s : List ℕ) :
    (s.map fun m : ℕ => (m : ℚ) / ((s.sum : ℚ) + 1 / 2)).sum + (1 / 2) / ((s.sum : ℚ) + 1 / 2) = 1 := by
  have hN : (0 : ℚ) < (s.sum : ℚ) + 1 / 2 := by positivity
  have hlist : ∀ (l : List ℕ) (N : ℚ), (l.map fun m : ℕ => (m : ℚ) / N).sum = (l.sum : ℚ) / N := by
    intro l N
    induction l with
    | nil => simp
    | cons x l ih => rw [List.map_cons, List.sum_cons, ih, List.sum_cons, Nat.cast_add, add_div]
  have hmap := hlist s ((s.sum : ℚ) + 1 / 2)
  rw [hmap, ← add_div, div_self hN.ne']

/-- [proved-derived; formal-checked] **`restaurant_merge_ratio`: a merge of blocks of `a` and `b`
cells multiplies the description's mass by `2·(a + b − 1)!/((a − 1)!(b − 1)!)`.** -/
theorem restaurant_merge_ratio {a b : ℕ} (_ha : 1 ≤ a) (_hb : 1 ≤ b) (s : List ℕ) :
    restaurantMass ((a + b) :: s) =
      restaurantMass (a :: b :: s) *
        (2 * ((a + b - 1).factorial : ℚ) / (((a - 1).factorial : ℚ) * ((b - 1).factorial : ℚ))) := by
  have hD := restaurant_den_pos (a + b + s.sum)
  have hfa : (0 : ℚ) < ((a - 1).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  have hfb : (0 : ℚ) < ((b - 1).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  simp only [restaurantMass, List.length_cons, List.map_cons, List.prod_cons, List.sum_cons]
  rw [show a + (b + s.sum) = a + b + s.sum by omega, pow_succ, pow_succ]
  field_simp
  ring

/-- The merge ratio is at least `2`: a merge that keeps the likelihood shortens the description. -/
theorem restaurant_merge_ratio_ge_two {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (2 : ℚ) ≤ 2 * ((a + b - 1).factorial : ℚ) / (((a - 1).factorial : ℚ) * ((b - 1).factorial : ℚ)) := by
  have hfa : (0 : ℚ) < ((a - 1).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  have hfb : (0 : ℚ) < ((b - 1).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  rw [le_div_iff₀ (mul_pos hfa hfb)]
  have hle : (a - 1).factorial * (b - 1).factorial ≤ (a + b - 1).factorial := by
    calc (a - 1).factorial * (b - 1).factorial ≤ (a - 1 + (b - 1)).factorial :=
          Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
      _ ≤ (a + b - 1).factorial := Nat.factorial_le (by omega)
  have : ((a - 1).factorial : ℚ) * (b - 1).factorial ≤ (a + b - 1).factorial := by
    exact_mod_cast hle
  linarith

end Restaurant

/-! ## 4. One source, several alphabets: the segmentation lattice -/

section Segmentation

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- [definition] **The source mass** of a decoder `D` under a law `P` on its words:
`P_G(x) = Σ_(D z = x) P(z)`. -/
def sourceMass (D : Z → X) (P : Z → ℚ) (x : X) : ℚ := speciesWeight D P x

/-- [definition] **The parse given its source**, `P(z | D z) = P(z)/P_G(D z)`. -/
def parseGiven (D : Z → X) (P : Z → ℚ) (z : Z) : ℚ := P z / sourceMass D P (D z)

/-- [proved-derived; formal-checked] **`segmentation_mass`: the mass over segmentations is a
probability law** on the sources. -/
theorem segmentation_mass (D : Z → X) {P : Z → ℚ} (hP : IsPrior P) : IsPrior (sourceMass D P) :=
  speciesWeight_isPrior D hP

omit [Fintype X] [DecidableEq Z] in
/-- [proved-derived; formal-checked] **The parse given its source is a face** on the source's
segmentations. -/
theorem parse_given_sum (D : Z → X) (P : Z → ℚ) (x : X) (hx : sourceMass D P x ≠ 0) :
    ∑ z ∈ univ.filter (fun z => D z = x), parseGiven D P z = 1 :=
  expansion_sum D P x hx

omit [Fintype X] [DecidableEq Z] in
theorem sourceMass_ge (D : Z → X) {P : Z → ℚ} (hP : ∀ z, 0 ≤ P z) (z : Z) :
    P z ≤ sourceMass D P (D z) := by
  unfold sourceMass speciesWeight
  exact single_le_sum (f := P) (fun k _ => hP k) (mem_filter.2 ⟨mem_univ z, rfl⟩)

omit [Fintype X] [DecidableEq Z] in
/-- [proved-derived; formal-checked] **A transmitted parse pays its source once**:
`−log₂ P(z) = −log₂ P_G(D z) − log₂ P(z | D z)`. -/
theorem parse_code (D : Z → X) {P : Z → ℚ} (hP : ∀ z, 0 ≤ P z) (z : Z) (hz : 0 < P z) :
    -Real.logb 2 (P z : ℝ) =
      -Real.logb 2 (sourceMass D P (D z) : ℝ) - Real.logb 2 (parseGiven D P z : ℝ) := by
  have hx : 0 < sourceMass D P (D z) := lt_of_lt_of_le hz (sourceMass_ge D hP z)
  have hxr : (0 : ℝ) < (sourceMass D P (D z) : ℝ) := by exact_mod_cast hx
  have hzr : (0 : ℝ) < (P z : ℝ) := by exact_mod_cast hz
  rw [parseGiven, Rat.cast_div, Real.logb_div hzr.ne' hxr.ne']
  ring

omit [Fintype X] [DecidableEq Z] in
/-- [proved-derived; formal-checked] **The lattice codes a source at most as any one of its
parses**: `−log₂ P_G(D z) ≤ −log₂ P(z)` (the byte path is the lossless fallback). -/
theorem segmentation_code_le (D : Z → X) {P : Z → ℚ} (hP : ∀ z, 0 ≤ P z) (z : Z) (hz : 0 < P z) :
    -Real.logb 2 (sourceMass D P (D z) : ℝ) ≤ -Real.logb 2 (P z : ℝ) := by
  have hzr : (0 : ℝ) < (P z : ℝ) := by exact_mod_cast hz
  have hle : (P z : ℝ) ≤ (sourceMass D P (D z) : ℝ) := Rat.cast_le.2 (sourceMass_ge D hP z)
  exact neg_logb_le_of_le hzr hle

end Segmentation

/-! ## 5. The encoding square on the merged encoding, or a separator -/

section Square

variable {X Y Y' R : Type*}

/-- [definition] **The merged square**: a decoder `D′` and a transport `U′` on the merged encoding
with `D′ (σ (E x)) = ρ x` (`D E = ρ`) and `σ (E_next (T x)) = U′ (σ (E x))` (`E_next T = U E`). -/
def MergedSquare (E Enext : X → Y) (σ : Y → Y') (ρ : X → R) (T : X → X) : Prop :=
  ∃ (D' : Y' → R) (U' : Y' → Y'), (∀ x, D' (σ (E x)) = ρ x) ∧ ∀ x, σ (Enext (T x)) = U' (σ (E x))

/-- [definition] **A separator**: two cells the merged encoding identifies whose readings, or whose
successors' merged encodings, differ. -/
def Separator (E Enext : X → Y) (σ : Y → Y') (ρ : X → R) (T : X → X) (x x' : X) : Prop :=
  σ (E x) = σ (E x') ∧ (ρ x ≠ ρ x' ∨ σ (Enext (T x)) ≠ σ (Enext (T x')))

/-- [proved-derived; formal-checked] **The merged square holds exactly when no separator
exists.** -/
theorem square_iff_no_separator [Nonempty R] (E Enext : X → Y) (σ : Y → Y') (ρ : X → R)
    (T : X → X) :
    MergedSquare E Enext σ ρ T ↔ ¬ ∃ x x', Separator E Enext σ ρ T x x' := by
  classical
  constructor
  · rintro ⟨D', U', hD, hU⟩ ⟨x, x', hσ, hsep⟩
    rcases hsep with h | h
    · exact h (by rw [← hD x, ← hD x', hσ])
    · exact h (by rw [hU x, hU x', hσ])
  · intro hno
    have hagree : ∀ x x', σ (E x) = σ (E x') →
        ρ x = ρ x' ∧ σ (Enext (T x)) = σ (Enext (T x')) := by
      intro x x' hσ
      by_contra h
      rw [not_and_or] at h
      exact hno ⟨x, x', hσ, h⟩
    refine ⟨fun y => if h : ∃ x, σ (E x) = y then ρ h.choose else Classical.arbitrary R,
      fun y => if h : ∃ x, σ (E x) = y then σ (Enext (T h.choose)) else y, ?_, ?_⟩
    · intro x
      have h : ∃ x', σ (E x') = σ (E x) := ⟨x, rfl⟩
      simp only [dif_pos h]
      exact (hagree _ _ h.choose_spec).1
    · intro x
      have h : ∃ x', σ (E x') = σ (E x) := ⟨x, rfl⟩
      simp only [dif_pos h]
      exact ((hagree _ _ h.choose_spec).2).symm

/-- [proved-derived; formal-checked] **`encoding_square_or_separator`: `D E = ρ` and
`E_next T = U E` hold on the merged encoding, or a separator is returned.** -/
theorem encoding_square_or_separator [Nonempty R] (E Enext : X → Y) (σ : Y → Y') (ρ : X → R)
    (T : X → X) :
    MergedSquare E Enext σ ρ T ∨ ∃ x x', Separator E Enext σ ρ T x x' := by
  by_cases h : ∃ x x', Separator E Enext σ ρ T x x'
  · exact Or.inr h
  · exact Or.inl ((square_iff_no_separator E Enext σ ρ T).2 h)

/-- [proved-derived; formal-checked] **A merge the decoder and the transport respect keeps the
square**: from `D (E x) = ρ x`, `E_next (T x) = U (E x)`, `D = D′ ∘ σ` and `σ ∘ U = U′ ∘ σ`. -/
theorem merged_square_of_compatible {E Enext : X → Y} {σ : Y → Y'} {ρ : X → R} {T : X → X}
    {D : Y → R} {U : Y → Y} (hD : ∀ x, D (E x) = ρ x) (hU : ∀ x, Enext (T x) = U (E x))
    (D' : Y' → R) (U' : Y' → Y') (hDσ : ∀ y, D y = D' (σ y)) (hUσ : ∀ y, σ (U y) = U' (σ y)) :
    MergedSquare E Enext σ ρ T :=
  ⟨D', U', fun x => by rw [← hDσ, hD], fun x => by rw [hU, hUσ]⟩

end Square

/-! ## 6. Release: a merge that changes no admitted face -/

section Release

variable {κ S : Type*} [Fintype κ] [Fintype S] [DecidableEq κ] [DecidableEq S]

/-- [definition] **Future-equivalent cells**: members of one merged cell agree at every admitted
tick `t < h`. -/
def FutureEquivalent (σ : κ → S) (f : κ → ℕ → ℚ) (h : ℕ) : Prop :=
  ∀ k k', σ k = σ k' → ∀ t < h, f k t = f k' t

/-- [definition] **A lawful release**: one face per merged cell from which every member's face is
read at every admitted tick. -/
def LawfulRelease (σ : κ → S) (f : κ → ℕ → ℚ) (h : ℕ) : Prop :=
  ∃ g : S → ℕ → ℚ, ∀ k, ∀ t < h, f k t = g (σ k) t

omit [Fintype S] [DecidableEq κ] in
/-- [proved-derived; formal-checked] **`release_merge_iff_future_equivalent`: a merge is a lawful
release exactly when its merged cells are future-equivalent for the admitted receivers.** -/
theorem release_merge_iff_future_equivalent (σ : κ → S) (f : κ → ℕ → ℚ) (h : ℕ) :
    LawfulRelease σ f h ↔ FutureEquivalent σ f h := by
  classical
  constructor
  · rintro ⟨g, hg⟩ k k' hσ t ht
    rw [hg k t ht, hg k' t ht, hσ]
  · intro heq
    refine ⟨fun s t => if hs : ∃ k, σ k = s then f hs.choose t else 0, fun k t ht => ?_⟩
    have hs : ∃ k', σ k' = σ k := ⟨k, rfl⟩
    simp only [dif_pos hs]
    exact heq k hs.choose hs.choose_spec.symm t ht

omit [Fintype κ] [Fintype S] [DecidableEq κ] [DecidableEq S] in
/-- Over the admitted future a member's likelihood is its merged cell's. -/
theorem release_likelihood (σ : κ → S) {f : κ → ℕ → ℚ} {h : ℕ} (g : S → ℕ → ℚ)
    (hg : ∀ k, ∀ t < h, f k t = g (σ k) t) {n : ℕ} (hn : n ≤ h) (k : κ) :
    seqLik (f k) n = seqLik (g (σ k)) n :=
  prod_congr rfl fun t ht => hg k t (lt_of_lt_of_le (mem_range.1 ht) hn)

omit [DecidableEq κ] in
theorem release_mixture (σ : κ → S) (w : κ → ℚ) {f : κ → ℕ → ℚ} {h : ℕ} (g : S → ℕ → ℚ)
    (hg : ∀ k, ∀ t < h, f k t = g (σ k) t) {n : ℕ} (hn : n ≤ h) :
    ∑ k, w k * seqLik (f k) n = ∑ s, speciesWeight σ w s * seqLik (g s) n := by
  rw [← sum_fiberwise univ σ (fun k => w k * seqLik (f k) n)]
  refine sum_congr rfl fun s _ => ?_
  unfold speciesWeight
  rw [sum_mul]
  refine sum_congr rfl fun k hk => ?_
  rw [release_likelihood σ g hg hn k, (mem_filter.1 hk).2]

/-- [proved-derived; formal-checked] **`release_merge_code`: a lawful release changes no code for
the admitted future.** The merged mixture at the summed weights, each merged cell reading its one
face, codes every passage within the admitted future exactly as the unmerged mixture. -/
theorem release_merge_code (σ : κ → S) (w : κ → ℚ) {f : κ → ℕ → ℚ} {h : ℕ} (g : S → ℕ → ℚ)
    (hg : ∀ k, ∀ t < h, f k t = g (σ k) t) {n : ℕ} (hn : n ≤ h) :
    ∏ t ∈ range n, fwdMix w f idKernel t =
      ∏ t ∈ range n, fwdMix (speciesWeight σ w) g idKernel t := by
  refine prod_congr rfl fun t ht => ?_
  have ht' : t < h := lt_of_lt_of_le (mem_range.1 ht) hn
  unfold fwdMix
  simp only [fwd_id]
  have hnum : ∑ k, w k * seqLik (f k) t * f k t =
      ∑ s, speciesWeight σ w s * seqLik (g s) t * g s t := by
    have := release_mixture σ w g hg (n := t + 1) ht'
    simpa only [seqLik_succ, mul_assoc] using this
  rw [hnum, release_mixture σ w g hg ht'.le]

end Release

/-! ## 7. The tree's contexts: equal present faces do not merge -/

section TreeContexts

open Holonics.Foundation.Standing (StandingLaw)
open Holonics.Foundation.Chronology (transportWord)

/-- [definition] **The fixture**: at depth one over `Fin 2` letters and classes, one arrival of class
`0` at the address `[0]` and one at `[1]`. -/
def twoContexts : TreeStanding (Fin 2) (Fin 2) := arrive (arrive emptyStanding [0] 0) [1] 0

/-- [definition] The fixture after one further arrival of class `1` at `[0]`. -/
def parted : TreeStanding (Fin 2) (Fin 2) := arrival ([0], 1) twoContexts

theorem ktMass_fin_two (n : Fin 2 → ℕ) :
    ktMass n = (∏ j ∈ range (n 0), ((j : ℚ) + 1 / 2)) *
        (∏ j ∈ range (n 1), ((j : ℚ) + 1 / 2)) / ∏ j ∈ range (n 0 + n 1), ((j : ℚ) + 1) := by
  simp [ktMass, Fin.prod_univ_two, Fin.sum_univ_two]

/-- The root face at depth one: the root's KT face and the context's, mixed by the stop weight. -/
theorem rootRead_depth_one (N : TreeStanding (Fin 2) (Fin 2)) (b c : Fin 2) :
    rootRead 1 ([b], c) N =
      ktMass (N []) / (ktMass (N []) + ktMass (N [0]) * ktMass (N [1])) * ktFace (N []) c +
        (1 - ktMass (N []) / (ktMass (N []) + ktMass (N [0]) * ktMass (N [1]))) *
          ktFace (N [b]) c := by
  simp only [rootRead, face]
  rw [pathFace_step _ _ Nat.zero_lt_one, pathFace_deepest]
  simp [kAt, lamAt, splitMass, treeWeight, Fin.prod_univ_two]

theorem twoContexts_counts :
    (twoContexts [] 0 = 2 ∧ twoContexts [] 1 = 0) ∧
      (twoContexts [0] 0 = 1 ∧ twoContexts [0] 1 = 0) ∧
        (twoContexts [1] 0 = 1 ∧ twoContexts [1] 1 = 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

theorem parted_counts :
    (parted [] 0 = 2 ∧ parted [] 1 = 1) ∧
      (parted [0] 0 = 1 ∧ parted [0] 1 = 1) ∧
        (parted [1] 0 = 1 ∧ parted [1] 1 = 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

/-- The two contexts read every class alike now, `4/5` for class `0`. -/
theorem twoContexts_faces :
    (∀ c, rootRead 1 ([0], c) twoContexts = rootRead 1 ([1], c) twoContexts) ∧
      rootRead 1 ([0], 0) twoContexts = 4 / 5 := by
  have same : twoContexts [0] = twoContexts [1] := by
    funext c
    fin_cases c <;> decide
  refine ⟨fun c => by rw [rootRead_depth_one, rootRead_depth_one, same], ?_⟩
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, ⟨c0, c1⟩⟩ := twoContexts_counts
  rw [rootRead_depth_one, ktMass_fin_two, ktMass_fin_two, ktMass_fin_two]
  simp only [ktFace, Holonics.HNN.RegionCounts.ktProb, Fin.sum_univ_two, a0, a1, b0, b1, c0, c1]
  norm_num [prod_range_succ]

/-- After the parting arrival they read `9/16` and `11/16`. -/
theorem parted_faces :
    rootRead 1 ([0], 0) parted = 9 / 16 ∧ rootRead 1 ([1], 0) parted = 11 / 16 := by
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, ⟨c0, c1⟩⟩ := parted_counts
  constructor <;>
  · rw [rootRead_depth_one, ktMass_fin_two, ktMass_fin_two, ktMass_fin_two]
    simp only [ktFace, Holonics.HNN.RegionCounts.ktProb, Fin.sum_univ_two, a0, a1, b0, b1, c0, c1]
    norm_num [prod_range_succ]

/-- [counterexample; formal-checked] **`equal_present_faces_do_not_merge`** (module header). The
contexts `[0]` and `[1]` read every class alike now; after the arrival of class `1` at `[0]` they
read `9/16` and `11/16`; so every lawful standing of the tree under arrivals reopens the two
contexts differently after that word, and no register shared by both is a standing. -/
theorem equal_present_faces_do_not_merge :
    (∀ c, rootRead 1 ([0], c) twoContexts = rootRead 1 ([1], c) twoContexts) ∧
      rootRead 1 ([0], 0) (arrival ([0], 1) twoContexts) = 9 / 16 ∧
        rootRead 1 ([1], 0) (arrival ([0], 1) twoContexts) = 11 / 16 ∧
          ∀ {R : Type} (L : StandingLaw (List (Fin 2) × Fin 2) (List (Fin 2) × Fin 2)
              (TreeStanding (Fin 2) (Fin 2)) R ℚ),
            L.transport = arrival → L.observe = rootRead 1 →
              L.reopen ([0], 0) [([0], 1)] (L.retain twoContexts) ≠
                L.reopen ([1], 0) [([0], 1)] (L.retain twoContexts) := by
  obtain ⟨h0, h1⟩ := parted_faces
  refine ⟨twoContexts_faces.1, h0, h1, fun L ht ho => ?_⟩
  rw [L.sufficient, L.sufficient]
  simp only [transportWord, ht, ho]
  change rootRead 1 ([0], 0) parted ≠ rootRead 1 ([1], 0) parted
  rw [h0, h1]
  norm_num

end TreeContexts

section Audit

#print axioms expand_merge
#print axioms expansion_sum
#print axioms mergedFace_isPrior
#print axioms merge_cost_iff
#print axioms merge_cost_nat
#print axioms merge_cost_mass_iff
#print axioms restaurant_found
#print axioms restaurant_join
#print axioms restaurant_step_sum
#print axioms restaurant_merge_ratio
#print axioms restaurant_merge_ratio_ge_two
#print axioms segmentation_mass
#print axioms parse_given_sum
#print axioms parse_code
#print axioms segmentation_code_le
#print axioms square_iff_no_separator
#print axioms encoding_square_or_separator
#print axioms merged_square_of_compatible
#print axioms release_merge_iff_future_equivalent
#print axioms release_merge_code
#print axioms coarsening_within_margin_iff
#print axioms twoContexts_faces
#print axioms parted_faces
#print axioms equal_present_faces_do_not_merge

end Audit

end Holonics.Compression.Landmark.Context.Merge
