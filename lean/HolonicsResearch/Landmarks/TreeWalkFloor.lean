import Mathlib
import HolonicsResearch.Landmarks.IharaBass
import HolonicsResearch.Landmarks.RegularComplexZeros

/-!
# The tree-walk floor: a regular complex holds at every cell the covering tree's closed walks, so its other modes cannot all stay below `2√q`

Source record: `research/records/2026-11-18_HARD_LEFSCHETZ_HOLDS_ON_A_FLAT_TORUS_LETTER_BY_LETTER_A_COVERS_CLOSED_WALKS_FALL_INTO_THEIR_HOLONOMY_CLASSES_AT_THE_HALF_AND_THE_COVERING_TREES_RETURNS_SET_THE_FLOOR_AT_THE_HALF.md`,
§5, the sequel to `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md`,
§4.2, which names this construction: the floor at `2√q` from the covering tree.

[proved-standard; formal-checked] `Landmarks/IharaBass` holds a finite complex of contacts as darts
(`src`, `tgt`), with the start and end incidences `S`, `T`, the reversal `J`, the dart operator
`B = hashimoto` and the cell operator `A = S Tᵀ`; `Landmarks/RegularComplexZeros` holds the modes
`λ_i = eigen a b i` of `A`.  This module counts, at every cell of a complex with `q + 1` darts at
every cell, the closed walks that the covering tree forces, and reads the count against the modes.
Write `n = |V|` and `C_k` for Catalan's number.

What is proved.

* **W1, the walks without backtracking** (`nbWalk`, `adjacency_mul_nbWalk`): with `N_0 = 1` and
  `N_(j+1) = S Bʲ Tᵀ`, the three-term recursion `A N_j = N_(j+1) + w_j N_(j−1)`, where the weight of
  a step back is `w_0 = 0`, `w_1 = q + 1`, `w_j = q` beyond (`weight`).  It rests on `B = Tᵀ S − J`
  (`hashimoto_eq`), `T Tᵀ = q + 1` (`end_mul_end_transpose`) and `T B = q S`
  (`end_mul_hashimoto`).
* **W2, the tree counts** (`treeCount`, `adjacency_pow_eq_sum`, `nbWalk_nonneg`,
  `treeCount_le_adjacency_pow_diag`): `Aᵐ = Σ_(j ≤ m) treeCount q m j · N_j`, where
  `treeCount q m j` counts the walks of `m` steps on the covering tree from its root that end at
  depth `j`, each step back weighted by its `w`; every `N_j` is entrywise nonnegative and
  `N_0 = 1`, so `(Aᵐ)_vv ≥ treeCount q m 0` at every cell `v`.
* **W3, Catalan's count** (`ballot`, `pow_mul_ballot_le_treeCount`, `ballot_eq_form`,
  `ballot_zero_right`, `four_pow_le_catalan`): the ballot numbers count the paths of `i` steps back
  that stay at or above the root and end at depth `j`; every step back weighs at least `q`, so
  `q^i · ballot i j ≤ treeCount q (2i + j) j`; the ballot theorem
  `ballot i j = C(2i + j, i) − C(2i + j, i − 1)` holds in `ℤ`, so `ballot k 0 = C_k`; and
  `4^k ≤ (2k + 1)(k + 1) C_k`.
* **W4, the floor** (`catalan_mul_pow_le_adjacency_pow_diag`, `trace_adjacency_pow`,
  `card_mul_catalan_le_trace`, `floor`, `floor_div`, `floor_half`): every cell has at least
  `C_k q^k` closed walks of `2k` darts, `(A^(2k))_vv ≥ C_k q^k`; with `tr Aˡ = Σ_i λ_iˡ`,
  `tr A^(2k) ≥ n C_k q^k`.  If the count `q + 1` is the mode at `i₀` and every other mode has
  `|λ_i| ≤ μ`, then `n C_k q^k ≤ (q + 1)^(2k) + (n − 1) μ^(2k)`, so on two or more cells
  `μ^(2k) ≥ (n C_k q^k − (q + 1)^(2k)) / (n − 1)`, and once `2 (q + 1)^(2k) ≤ n C_k q^k`,
  `μ^(2k) ≥ C_k q^k / 2`.
* **W5, Alon–Boppana in finite form** (`exists_catalan_floor_gt`, `alon_boppana`): for every `μ`
  with `μ² < 4q` there is a size `N` such that every complex with `q + 1` darts at every cell and
  at least `N` cells has a mode other than the count with `|λ_i| > μ`.  The `k` is the one at which
  `k² (μ²/4q)^k < 1/12` (`tendsto_pow_const_mul_const_pow_of_abs_lt_one`), and `N = 2 (q + 1)^(2k)`.

The reading: the covering tree is the complex unwound, and its closed walks are Dyck words of steps
out and back, `C_k` of them for `2k` steps with at least `q` ways for each step back.  Every cell of
the finite complex holds all of them, because the walks without backtracking are counts and the
first of them is the identity.  The trace spends those returns over the modes: the count `q + 1`
takes `(q + 1)^(2k)` of them, a fixed amount, and the rest must be spread over the other `n − 1`
modes, which then cannot all be below `(C_k q^k / 2)^(1/2k)`, a number that reaches `2√q` as `k`
grows.  The half `2√q` is the spectral radius of the tree's own walk.

The route is algebraic: the expansion of `Aᵐ` in the walks without backtracking replaces an
injection of the tree's words into the complex's walks, so no list of walks is built.

## What this does not state

* No diameter or test-function form of Alon–Boppana: neither the bound
  `λ₂ ≥ 2√q − (2√q − 1)/⌊D/2⌋` in the diameter `D`, nor a rate in `n`.  The attributions (Alon,
  1986; Nilli, 1991) are from training, not read from a source in this tree.
* The signed second mode: the floor bounds `|λ_i|` over the modes other than the count, so on a
  complex with two sides the mode `−(q + 1)` is among them and the statement is spent on it.  The
  same argument with that mode erased as well bounds the rest; it is not written here.
* A root form `μ ≥ (C_k q^k / 2)^(1/2k)` and the limit `2√q` itself: the module states the even
  powers and the existence of `N` for each `μ` below `2√q`.

The computational object is the helical pair interaction read as a census of returns: a closed walk
is a closed strand through pair contacts, and the covering tree is that strand's helix unwound, on
which every return is a word of steps out and back.  Of the winding guide's six general objects this
touches the pair (the darts and their non-reversing contacts, `N_j`) and the cell holonomy (the
modes of the cell operator, through the trace); the helix, faces and placement, the tube and the
tower thread stay attached.

Consumers: the atlas row `trace.tree-walk-floor` (beside `trace.ihara-zeta` and the tempered rows
that `Landmarks/RegularComplexZeros` and `Landmarks/PrimeCycleHalf` serve, whose hypothesis
`λ_i² ≤ 4q` this floor shows cannot be bettered in the large), and its source record.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix Finset

namespace Holonics.Landmarks.TreeWalkFloor

open Holonics.Landmarks.IharaBass
open Holonics.Landmarks.RegularComplexZeros

/-! ## W1. The non-backtracking walks of every length -/

section Walks

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (a b : E → V)

/-- [definition] The non-backtracking walk matrices: `N 0 = 1` and `N (j + 1) = S Bʲ Tᵀ`, whose
entry `(v, w)` counts the walks of `j + 1` darts from `v` to `w` that never take a dart straight
back. -/
noncomputable def nbWalk : ℕ → Matrix V V ℝ
  | 0 => 1
  | j + 1 => startMatrix ℝ a b * hashimoto ℝ a b ^ j * (endMatrix ℝ a b)ᵀ

/-- [definition] The weight of a step back toward the root of the covering tree: none from the
root, `q + 1` from its neighbours (every dart of the root returns there), `q` farther out. -/
def weight (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => q + 1
  | _ + 2 => q

omit [Fintype E] in
/-- [proved-derived; formal-checked] `B = Tᵀ S − J`. -/
theorem hashimoto_eq :
    hashimoto ℝ a b = (endMatrix ℝ a b)ᵀ * startMatrix ℝ a b - reversal ℝ E := by
  rw [endMatrix_transpose_mul_startMatrix, add_sub_cancel_right]

omit [Fintype V] in
/-- [proved-derived; formal-checked] On a complex with `q + 1` darts at every cell,
`T Tᵀ = q + 1`. -/
theorem end_mul_end_transpose {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1) :
    endMatrix ℝ a b * (endMatrix ℝ a b)ᵀ = ((q : ℝ) + 1) • (1 : Matrix V V ℝ) := by
  rw [← degree_eq_end, degree_eq_smul_one_of_regular ℝ a b hreg]

/-- [proved-derived; formal-checked] **The darts in, then on without turning back, are `q` times
the darts out**: `T B = q S` on a complex with `q + 1` darts at every cell. -/
theorem end_mul_hashimoto {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1) :
    endMatrix ℝ a b * hashimoto ℝ a b = (q : ℝ) • startMatrix ℝ a b := by
  rw [hashimoto_eq, Matrix.mul_sub, ← Matrix.mul_assoc, end_mul_end_transpose a b hreg,
    endMatrix_mul_reversal, Matrix.smul_mul, Matrix.one_mul, add_smul, one_smul,
    add_sub_cancel_right]

/-- [proved-derived; formal-checked] **The three-term recursion.**  `A N_j = N_(j+1) + w_j N_(j−1)`:
a walk without backtracking followed by one more dart either goes on (`N_(j+1)`) or turns straight
back, which a cell's `q + 1` darts allow in `w_j` ways. -/
theorem adjacency_mul_nbWalk {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1) (j : ℕ) :
    adjacency ℝ a b * nbWalk a b j =
      nbWalk a b (j + 1) + (weight q j : ℝ) • nbWalk a b (j - 1) := by
  have hA : adjacency ℝ a b = startMatrix ℝ a b * (endMatrix ℝ a b)ᵀ := rfl
  have hTS : (endMatrix ℝ a b)ᵀ * startMatrix ℝ a b = hashimoto ℝ a b + reversal ℝ E :=
    endMatrix_transpose_mul_startMatrix ℝ a b
  set S := startMatrix ℝ a b
  set T := endMatrix ℝ a b
  set B := hashimoto ℝ a b
  set J := reversal ℝ E
  have hSJ : S * J = T := startMatrix_mul_reversal ℝ a b
  match j with
  | 0 =>
    simp only [nbWalk, weight, Nat.cast_zero, zero_smul, add_zero, pow_zero, Matrix.mul_one,
      hA]
    rfl
  | 1 =>
    show S * Tᵀ * (S * B ^ 0 * Tᵀ) = S * B ^ 1 * Tᵀ + ((q + 1 : ℕ) : ℝ) • (1 : Matrix V V ℝ)
    calc S * Tᵀ * (S * B ^ 0 * Tᵀ) = S * (Tᵀ * S) * Tᵀ := by
          simp only [pow_zero, Matrix.mul_one, Matrix.mul_assoc]
      _ = S * B * Tᵀ + (S * J) * Tᵀ := by
          rw [hTS, Matrix.mul_add, Matrix.add_mul]
      _ = S * B ^ 1 * Tᵀ + ((q + 1 : ℕ) : ℝ) • (1 : Matrix V V ℝ) := by
          rw [hSJ, end_mul_end_transpose a b hreg, pow_one]
          push_cast
          rfl
  | k + 2 =>
    show S * Tᵀ * (S * B ^ (k + 1) * Tᵀ) = S * B ^ (k + 2) * Tᵀ + (q : ℝ) • (S * B ^ k * Tᵀ)
    calc S * Tᵀ * (S * B ^ (k + 1) * Tᵀ) = S * ((Tᵀ * S) * B ^ (k + 1)) * Tᵀ := by
          simp only [Matrix.mul_assoc]
      _ = S * (B * B ^ (k + 1)) * Tᵀ + (S * J) * (B * B ^ k) * Tᵀ := by
          rw [hTS]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, pow_succ']
      _ = S * B ^ (k + 2) * Tᵀ + (T * B) * B ^ k * Tᵀ := by
          rw [← pow_succ', hSJ]
          simp only [Matrix.mul_assoc]
      _ = S * B ^ (k + 2) * Tᵀ + (q : ℝ) • (S * B ^ k * Tᵀ) := by
          rw [end_mul_hashimoto a b hreg, Matrix.smul_mul, Matrix.smul_mul]

end Walks

/-! ## W2. The walks on the covering tree, by depth -/

/-- [definition] **The tree counts.**  `treeCount q m j` counts, with the weights of the steps back,
the walks of `m` steps on the covering tree from its root that end at depth `j`: the last step
either went out from depth `j − 1` or came back from depth `j + 1`, which a cell's darts allow in
`weight q (j + 1)` ways. -/
def treeCount (q : ℕ) : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | m + 1, j =>
    (if j = 0 then 0 else treeCount q m (j - 1)) + weight q (j + 1) * treeCount q m (j + 1)

/-- [proved-derived; formal-checked] No walk of `m` steps reaches past depth `m`. -/
theorem treeCount_eq_zero_of_lt (q : ℕ) : ∀ {m j : ℕ}, m < j → treeCount q m j = 0
  | 0, j, h => by simp [treeCount, Nat.pos_iff_ne_zero.mp h]
  | m + 1, j, h => by
    have h1 : j ≠ 0 := by omega
    simp only [treeCount, if_neg h1, treeCount_eq_zero_of_lt q (by omega : m < j - 1),
      treeCount_eq_zero_of_lt q (by omega : m < j + 1), mul_zero, add_zero]

/-- [proved-derived; formal-checked] One walk of `m` steps reaches depth `m`: straight out. -/
theorem treeCount_self (q : ℕ) : ∀ m : ℕ, treeCount q m m = 1
  | 0 => by simp [treeCount]
  | m + 1 => by
    simp only [treeCount, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, treeCount_self q m,
      treeCount_eq_zero_of_lt q (by omega : m < m + 1 + 1), mul_zero, add_zero]

/-- [proved-derived; formal-checked] A walk at the root came back from depth one, in `q + 1`
ways. -/
theorem treeCount_succ_zero (q m : ℕ) : treeCount q (m + 1) 0 = (q + 1) * treeCount q m 1 := by
  simp [treeCount, weight]

/-- [proved-derived; formal-checked] Away from the root a step back has `q` ways. -/
theorem treeCount_succ_succ (q m j : ℕ) :
    treeCount q (m + 1) (j + 1) = treeCount q m j + q * treeCount q m (j + 2) := by
  simp [treeCount, weight]

section Expansion

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (a b : E → V)

/-- [proved-derived; formal-checked] **The cell operator's powers expand in the walks without
backtracking, with the tree counts as coefficients**:
`Aᵐ = Σ_(j ≤ m) treeCount q m j · N_j` on a complex with `q + 1` darts at every cell. -/
theorem adjacency_pow_eq_sum {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1) (m : ℕ) :
    adjacency ℝ a b ^ m = ∑ j ∈ range (m + 1), (treeCount q m j : ℝ) • nbWalk a b j := by
  induction m with
  | zero => simp [treeCount, nbWalk]
  | succ m ih =>
    have e1 : treeCount q m (m + 1) = 0 := treeCount_eq_zero_of_lt q (by omega)
    have e2 : treeCount q m (m + 1 + 1) = 0 := treeCount_eq_zero_of_lt q (by omega)
    rw [pow_succ', ih, Finset.mul_sum]
    simp only [Matrix.mul_smul, adjacency_mul_nbWalk a b hreg, smul_add, Finset.sum_add_distrib,
      smul_smul]
    have hsplit : ∀ j, (treeCount q (m + 1) j : ℝ) • nbWalk a b j =
        ((if j = 0 then 0 else treeCount q m (j - 1) : ℕ) : ℝ) • nbWalk a b j +
        ((weight q (j + 1) * treeCount q m (j + 1) : ℕ) : ℝ) • nbWalk a b j := by
      intro j
      rw [← add_smul, ← Nat.cast_add]
      rfl
    simp only [hsplit, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_range_succ' _ (m + 1)]
      simp
    · have hL : ∑ j ∈ range (m + 1), ((treeCount q m j : ℝ) * (weight q j : ℝ)) • nbWalk a b (j - 1)
          = ∑ i ∈ range m, ((weight q (i + 1) * treeCount q m (i + 1) : ℕ) : ℝ) • nbWalk a b i := by
        rw [Finset.sum_range_succ']
        simp only [weight, Nat.cast_zero, mul_zero, zero_smul, add_zero, Nat.add_sub_cancel]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        rw [mul_comm]
      have hR : ∑ j ∈ range (m + 1 + 1),
            ((weight q (j + 1) * treeCount q m (j + 1) : ℕ) : ℝ) • nbWalk a b j
          = ∑ i ∈ range m, ((weight q (i + 1) * treeCount q m (i + 1) : ℕ) : ℝ) • nbWalk a b i := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        simp [e1, e2]
      rw [hL, hR]

/-- [proved-standard; formal-checked] A product of entrywise nonnegative matrices is entrywise
nonnegative. -/
theorem mul_entry_nonneg {ι κ ρ : Type*} [Fintype κ] {M : Matrix ι κ ℝ} {N : Matrix κ ρ ℝ}
    (hM : ∀ i k, 0 ≤ M i k) (hN : ∀ k l, 0 ≤ N k l) (i : ι) (l : ρ) : 0 ≤ (M * N) i l := by
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hM i k) (hN k l)

omit [Fintype V] in
/-- [proved-derived; formal-checked] The walks without backtracking are counts: every entry of
`N_j` is nonnegative. -/
theorem nbWalk_nonneg (j : ℕ) (v w : V) : 0 ≤ nbWalk a b j v w := by
  have hS : ∀ v d, 0 ≤ startMatrix ℝ a b v d := fun v d => by
    rw [startMatrix_apply]; split_ifs <;> norm_num
  have hT : ∀ d w, 0 ≤ (endMatrix ℝ a b)ᵀ d w := fun d w => by
    rw [Matrix.transpose_apply]; simp only [endMatrix, Matrix.of_apply]; split_ifs <;> norm_num
  have hB : ∀ d f, 0 ≤ hashimoto ℝ a b d f := fun d f => by
    simp only [hashimoto, Matrix.of_apply]; split_ifs <;> norm_num
  have hBp : ∀ n, ∀ d f, 0 ≤ (hashimoto ℝ a b ^ n) d f := by
    intro n
    induction n with
    | zero => intro d f; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    | succ n ih => intro d f; rw [pow_succ]; exact mul_entry_nonneg ih hB d f
  cases j with
  | zero =>
    show 0 ≤ (1 : Matrix V V ℝ) v w
    rw [Matrix.one_apply]; split_ifs <;> norm_num
  | succ j => exact mul_entry_nonneg (mul_entry_nonneg hS (hBp j)) hT v w

/-- [proved-derived; formal-checked] **The closed walks at a cell are at least the tree's closed
walks at its root**: `(Aᵐ)_vv ≥ treeCount q m 0`. -/
theorem treeCount_le_adjacency_pow_diag {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1)
    (m : ℕ) (v : V) : (treeCount q m 0 : ℝ) ≤ (adjacency ℝ a b ^ m) v v := by
  rw [adjacency_pow_eq_sum a b hreg m, Matrix.sum_apply]
  have h0 : (0 : ℕ) ∈ range (m + 1) := Finset.mem_range.mpr (Nat.succ_pos m)
  calc (treeCount q m 0 : ℝ) = ((treeCount q m 0 : ℝ) • nbWalk a b 0) v v := by
        simp [nbWalk]
    _ ≤ ∑ j ∈ range (m + 1), ((treeCount q m j : ℝ) • nbWalk a b j) v v :=
        Finset.single_le_sum (f := fun j => ((treeCount q m j : ℝ) • nbWalk a b j) v v)
          (fun j _ => by
            rw [Matrix.smul_apply, smul_eq_mul]
            exact mul_nonneg (Nat.cast_nonneg _) (nbWalk_nonneg a b j v v)) h0

end Expansion

/-! ## W3. The ballot numbers and Catalan's count -/

/-- [definition] **The ballot numbers**: `ballot i j` counts the paths of `i` steps back and
`i + j` steps out that never go below the root and end at depth `j`. -/
def ballot : ℕ → ℕ → ℕ
  | 0, _ => 1
  | i + 1, 0 => ballot i 1
  | i + 1, j + 1 => ballot (i + 1) j + ballot i (j + 2)
termination_by i j => (i, j)

/-- [proved-derived; formal-checked] With no step back there is one path. -/
theorem ballot_zero (j : ℕ) : ballot 0 j = 1 := by rw [ballot]

/-- [proved-derived; formal-checked] A path at the root came back from depth one. -/
theorem ballot_succ_zero (i : ℕ) : ballot (i + 1) 0 = ballot i 1 := by rw [ballot]

/-- [proved-derived; formal-checked] Away from the root the last step went out or came back. -/
theorem ballot_succ_succ (i j : ℕ) :
    ballot (i + 1) (j + 1) = ballot (i + 1) j + ballot i (j + 2) := by rw [ballot]

/-- [proved-derived; formal-checked] **Each step back weighs at least `q`**:
`q^i · ballot i j ≤ treeCount q (2i + j) j`. -/
theorem pow_mul_ballot_le_treeCount (q : ℕ) :
    ∀ i j : ℕ, q ^ i * ballot i j ≤ treeCount q (2 * i + j) j
  | 0, j => by simp [ballot_zero, treeCount_self]
  | i + 1, 0 => by
    have h := pow_mul_ballot_le_treeCount q i 1
    rw [show 2 * (i + 1) + 0 = (2 * i + 1) + 1 by ring, treeCount_succ_zero, ballot_succ_zero,
      pow_succ]
    calc q ^ i * q * ballot i 1 = q * (q ^ i * ballot i 1) := by ring
      _ ≤ (q + 1) * treeCount q (2 * i + 1) 1 := Nat.mul_le_mul (Nat.le_succ q) h
  | i + 1, j + 1 => by
    have h1 := pow_mul_ballot_le_treeCount q (i + 1) j
    have h2 := pow_mul_ballot_le_treeCount q i (j + 2)
    rw [show 2 * (i + 1) + (j + 1) = (2 * (i + 1) + j) + 1 by ring, treeCount_succ_succ,
      ballot_succ_succ]
    rw [show 2 * (i + 1) + j = 2 * i + (j + 2) by ring] at h1 ⊢
    calc q ^ (i + 1) * (ballot (i + 1) j + ballot i (j + 2))
        = q ^ (i + 1) * ballot (i + 1) j + q * (q ^ i * ballot i (j + 2)) := by ring
      _ ≤ treeCount q (2 * i + (j + 2)) j + q * treeCount q (2 * i + (j + 2)) (j + 2) :=
          Nat.add_le_add h1 (Nat.mul_le_mul_left q h2)
termination_by i j => (i, j)

/-- [definition] The ballot numbers' closed form, read in `ℤ`:
`C(2i + j, i) − C(2i + j, i − 1)` for `i ≥ 1`. -/
def ballotForm : ℕ → ℕ → ℤ
  | 0, _ => 1
  | i + 1, j => ((2 * i + 2 + j).choose (i + 1) : ℤ) - ((2 * i + 2 + j).choose i : ℤ)

/-- [proved-standard; formal-checked] **The ballot theorem's count**:
`ballot i j = C(2i + j, i) − C(2i + j, i − 1)`. -/
theorem ballot_eq_form : ∀ i j : ℕ, (ballot i j : ℤ) = ballotForm i j
  | 0, j => by simp [ballot_zero, ballotForm]
  | i + 1, 0 => by
    rw [ballot_succ_zero, ballot_eq_form i 1]
    cases i with
    | zero => norm_num [ballotForm]
    | succ i' =>
      show ((2 * i' + 2 + 1).choose (i' + 1) : ℤ) - ((2 * i' + 2 + 1).choose i' : ℤ)
        = ((2 * (i' + 1) + 2 + 0).choose (i' + 1 + 1) : ℤ) -
          ((2 * (i' + 1) + 2 + 0).choose (i' + 1) : ℤ)
      have hs := Nat.choose_symm_half (i' + 1)
      rw [show 2 * (i' + 1) + 1 = 2 * i' + 2 + 1 by ring] at hs
      rw [show 2 * (i' + 1) + 2 + 0 = (2 * i' + 2 + 1) + 1 by ring,
        Nat.choose_succ_succ (2 * i' + 2 + 1) (i' + 1), Nat.choose_succ_succ (2 * i' + 2 + 1) i',
        hs]
      push_cast
      ring
  | i + 1, j + 1 => by
    rw [ballot_succ_succ, Nat.cast_add, ballot_eq_form (i + 1) j, ballot_eq_form i (j + 2)]
    cases i with
    | zero =>
      show ((2 * 0 + 2 + j).choose (0 + 1) : ℤ) - ((2 * 0 + 2 + j).choose 0 : ℤ) + 1
        = ((2 * 0 + 2 + (j + 1)).choose (0 + 1) : ℤ) - ((2 * 0 + 2 + (j + 1)).choose 0 : ℤ)
      simp only [zero_add, mul_zero, Nat.choose_one_right, Nat.choose_zero_right]
      push_cast
      ring
    | succ i' =>
      show ((2 * (i' + 1) + 2 + j).choose (i' + 1 + 1) : ℤ) -
          ((2 * (i' + 1) + 2 + j).choose (i' + 1) : ℤ) +
          (((2 * i' + 2 + (j + 2)).choose (i' + 1) : ℤ) - ((2 * i' + 2 + (j + 2)).choose i' : ℤ))
        = ((2 * (i' + 1) + 2 + (j + 1)).choose (i' + 1 + 1) : ℤ) -
          ((2 * (i' + 1) + 2 + (j + 1)).choose (i' + 1) : ℤ)
      rw [show 2 * (i' + 1) + 2 + j = 2 * i' + 4 + j by ring,
        show 2 * i' + 2 + (j + 2) = 2 * i' + 4 + j by ring,
        show 2 * (i' + 1) + 2 + (j + 1) = (2 * i' + 4 + j) + 1 by ring,
        Nat.choose_succ_succ (2 * i' + 4 + j) (i' + 1), Nat.choose_succ_succ (2 * i' + 4 + j) i']
      push_cast
      ring
termination_by i j => (i, j)

/-- [proved-standard; formal-checked] **The closed paths are Catalan's**: `ballot k 0 = C_k`. -/
theorem ballot_zero_right (k : ℕ) : ballot k 0 = catalan k := by
  rcases k with _ | k
  · simp [ballot_zero]
  · have h := ballot_eq_form (k + 1) 0
    rw [show ballotForm (k + 1) 0 = ((2 * k + 2 + 0).choose (k + 1) : ℤ) -
        ((2 * k + 2 + 0).choose k : ℤ) from rfl,
      show 2 * k + 2 + 0 = 2 * (k + 1) by ring] at h
    have hZ := succ_mul_catalan_eq_centralBinom (k + 1)
    rw [Nat.centralBinom_eq_two_mul_choose] at hZ
    have hXY := Nat.choose_succ_right_eq (2 * (k + 1)) k
    rw [show 2 * (k + 1) - k = k + 2 by omega] at hXY
    have hZ' : ((k : ℤ) + 1 + 1) * (catalan (k + 1) : ℤ) = ((2 * (k + 1)).choose (k + 1) : ℤ) := by
      exact_mod_cast hZ
    have hXY' : ((2 * (k + 1)).choose (k + 1) : ℤ) * ((k : ℤ) + 1) =
        ((2 * (k + 1)).choose k : ℤ) * ((k : ℤ) + 2) := by exact_mod_cast hXY
    have key : ((k : ℤ) + 2) * (ballot (k + 1) 0 : ℤ) = ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) := by
      rw [h]
      linear_combination (-1 : ℤ) * hZ' + hXY'
    exact_mod_cast mul_left_cancel₀ (by positivity : ((k : ℤ) + 2) ≠ 0) key

/-- [proved-standard; formal-checked] Catalan's numbers grow like `4^k` up to a square:
`4^k ≤ (2k + 1)(k + 1) C_k`. -/
theorem four_pow_le_catalan (k : ℕ) : 4 ^ k ≤ (2 * k + 1) * (k + 1) * catalan k := by
  have h1 := Nat.four_pow_le_two_mul_add_one_mul_central_binom k
  have h2 := succ_mul_catalan_eq_centralBinom k
  rw [Nat.centralBinom_eq_two_mul_choose] at h2
  rw [mul_assoc, h2]
  exact h1

/-- [proved-standard; formal-checked] Catalan's numbers are positive. -/
theorem catalan_pos' (k : ℕ) : 0 < catalan k := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have := four_pow_le_catalan k
  rw [h, mul_zero] at this
  exact absurd this (Nat.not_le.mpr (by positivity))

/-! ## W4. The floor -/

section Floor

open Polynomial

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (a b : E → V)

/-- [proved-derived; formal-checked] **At every cell, at least `C_k q^k` closed walks of `2k`
darts**: `(A^(2k))_vv ≥ C_k q^k`. -/
theorem catalan_mul_pow_le_adjacency_pow_diag {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1)
    (k : ℕ) (v : V) : (catalan k : ℝ) * (q : ℝ) ^ k ≤ (adjacency ℝ a b ^ (2 * k)) v v := by
  have h := pow_mul_ballot_le_treeCount q k 0
  rw [ballot_zero_right, add_zero] at h
  calc (catalan k : ℝ) * (q : ℝ) ^ k = ((q ^ k * catalan k : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (treeCount q (2 * k) 0 : ℝ) := by exact_mod_cast h
    _ ≤ _ := treeCount_le_adjacency_pow_diag a b hreg (2 * k) v

/-- [proved-standard; formal-checked] **The trace at the modes**: `tr Aˡ = Σ_i λ_iˡ`. -/
theorem trace_adjacency_pow (l : ℕ) :
    (adjacency ℝ a b ^ l).trace = ∑ i, (eigen a b i) ^ l := by
  apply Complex.ofReal_injective
  have h1 : (((adjacency ℝ a b ^ l).trace : ℝ) : ℂ) = (adjacency ℂ a b ^ l).trace := by
    rw [← adjacency_map a b (algebraMap ℝ ℂ), ← Matrix.map_pow]
    simp [Matrix.trace]
  rw [h1, trace_pow_eq_sum_roots_charpoly, adjacency_charpoly_complex]
  change psum l _ = _
  rw [psum_prod l _ _ (fun i _ => X_sub_C_ne_zero _)]
  push_cast
  simp [psum_X_sub_C]

/-- [proved-derived; formal-checked] **The trace floor**: `tr A^(2k) ≥ n C_k q^k`. -/
theorem card_mul_catalan_le_trace {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1)
    (k : ℕ) :
    (Fintype.card V : ℝ) * ((catalan k : ℝ) * (q : ℝ) ^ k) ≤ (adjacency ℝ a b ^ (2 * k)).trace := by
  show _ ≤ ∑ v, (adjacency ℝ a b ^ (2 * k)) v v
  calc (Fintype.card V : ℝ) * ((catalan k : ℝ) * (q : ℝ) ^ k)
      = ∑ _v : V, (catalan k : ℝ) * (q : ℝ) ^ k := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ v, (adjacency ℝ a b ^ (2 * k)) v v :=
        Finset.sum_le_sum fun v _ => catalan_mul_pow_le_adjacency_pow_diag a b hreg k v

/-- [proved-derived; formal-checked] **The floor with the modes**: if the count `q + 1` is the mode
at `i₀` and every other mode has `|λ_i| ≤ μ`, then `n C_k q^k ≤ (q + 1)^(2k) + (n − 1) μ^(2k)`. -/
theorem floor {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1)
    (k : ℕ) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1) {μ : ℝ}
    (hμ : ∀ i, i ≠ i₀ → |eigen a b i| ≤ μ) :
    (Fintype.card V : ℝ) * ((catalan k : ℝ) * (q : ℝ) ^ k) ≤
      ((q : ℝ) + 1) ^ (2 * k) + ((Fintype.card V : ℝ) - 1) * μ ^ (2 * k) := by
  have ht := card_mul_catalan_le_trace a b hreg k
  rw [trace_adjacency_pow, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), h0] at ht
  refine ht.trans (add_le_add le_rfl ?_)
  have hcard : ((Finset.univ.erase i₀).card : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
      Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨i₀⟩), Nat.cast_one]
  rw [← hcard, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun i hi => ?_
  have hi' : i ≠ i₀ := Finset.ne_of_mem_erase hi
  rw [← (even_two_mul k).pow_abs (eigen a b i)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hμ i hi') _

/-- [proved-derived; formal-checked] **The floor solved for the other modes**: on at least two
cells, `μ^(2k) ≥ (n C_k q^k − (q + 1)^(2k)) / (n − 1)`. -/
theorem floor_div {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1)
    (k : ℕ) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1) {μ : ℝ}
    (hμ : ∀ i, i ≠ i₀ → |eigen a b i| ≤ μ) (hV : 2 ≤ Fintype.card V) :
    ((Fintype.card V : ℝ) * ((catalan k : ℝ) * (q : ℝ) ^ k) - ((q : ℝ) + 1) ^ (2 * k)) /
      ((Fintype.card V : ℝ) - 1) ≤ μ ^ (2 * k) := by
  have hf := floor a b hreg k h0 hμ
  have hpos : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hV
    linarith
  rw [div_le_iff₀ hpos]
  linarith

/-- [proved-derived; formal-checked] **Half the tree's count, once the complex is large**: if
`2 (q + 1)^(2k) ≤ n C_k q^k`, then `μ^(2k) ≥ C_k q^k / 2`. -/
theorem floor_half {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1)
    (k : ℕ) {i₀ : V} (h0 : eigen a b i₀ = (q : ℝ) + 1) {μ : ℝ}
    (hμ : ∀ i, i ≠ i₀ → |eigen a b i| ≤ μ)
    (hn : 2 * ((q : ℝ) + 1) ^ (2 * k) ≤ (Fintype.card V : ℝ) * ((catalan k : ℝ) * (q : ℝ) ^ k)) :
    (catalan k : ℝ) * (q : ℝ) ^ k / 2 ≤ μ ^ (2 * k) := by
  have hf := floor a b hreg k h0 hμ
  have hM : 0 ≤ μ ^ (2 * k) := by
    rw [pow_mul]; exact pow_nonneg (sq_nonneg μ) k
  have hn1 : (1 : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i₀⟩
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hcon.le)]

end Floor

/-! ## W5. Alon–Boppana -/

/-- [proved-derived; formal-checked] Below `4q` the Catalan count wins: if `μ² < 4q`, some `k` has
`2 μ^(2k) < C_k q^k`. -/
theorem exists_catalan_floor_gt {q : ℕ} {μ : ℝ} (hμ : μ ^ 2 < 4 * q) :
    ∃ k : ℕ, 2 * μ ^ (2 * k) < (catalan k : ℝ) * (q : ℝ) ^ k := by
  have hq : (0 : ℝ) < q := by nlinarith [sq_nonneg μ]
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = μ ^ 2 / (4 * q) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ div_nonneg (sq_nonneg μ) (by positivity)
  have hx1 : x < 1 := hx ▸ (div_lt_one (by positivity)).mpr hμ
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
    (show |x| < 1 by rw [abs_of_nonneg hx0]; exact hx1)
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 12 by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N + 1, ?_⟩
  have hk : ((N + 1 : ℕ) : ℝ) ^ 2 * x ^ (N + 1) < 1 / 12 := hN (N + 1) (by omega)
  have hcat : (4 : ℝ) ^ (N + 1) ≤
      (2 * ((N + 1 : ℕ) : ℝ) + 1) * (((N + 1 : ℕ) : ℝ) + 1) * catalan (N + 1) := by
    exact_mod_cast four_pow_le_catalan (N + 1)
  have hk1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N + 1 by omega)
  have hμk : μ ^ (2 * (N + 1)) = (4 : ℝ) ^ (N + 1) * (q : ℝ) ^ (N + 1) * x ^ (N + 1) := by
    have hc : 4 * (q : ℝ) * x = μ ^ 2 := by rw [hx]; field_simp
    rw [pow_mul, ← hc, mul_pow, mul_pow]
  set K : ℝ := ((N + 1 : ℕ) : ℝ) with hK
  have hpoly : (2 * K + 1) * (K + 1) ≤ 6 * K ^ 2 := by nlinarith
  have hQ : 0 < (q : ℝ) ^ (N + 1) := pow_pos hq _
  have hD : 0 < (2 * K + 1) * (K + 1) := by positivity
  rw [hμk]
  have hW : 0 ≤ (4 : ℝ) ^ (N + 1) * (q : ℝ) ^ (N + 1) * x ^ (N + 1) := by positivity
  have hP : 0 < (4 : ℝ) ^ (N + 1) * (q : ℝ) ^ (N + 1) := by positivity
  have h1 : 2 * ((4 : ℝ) ^ (N + 1) * (q : ℝ) ^ (N + 1) * x ^ (N + 1)) * ((2 * K + 1) * (K + 1)) ≤
      12 * (K ^ 2 * x ^ (N + 1)) * ((4 : ℝ) ^ (N + 1) * (q : ℝ) ^ (N + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hpoly hW]
  have h2 : 12 * (K ^ 2 * x ^ (N + 1)) * ((4 : ℝ) ^ (N + 1) * (q : ℝ) ^ (N + 1)) <
      (4 : ℝ) ^ (N + 1) * (q : ℝ) ^ (N + 1) := by
    nlinarith [mul_lt_mul_of_pos_right hk hP]
  have h3 : (4 : ℝ) ^ (N + 1) * (q : ℝ) ^ (N + 1) ≤
      (catalan (N + 1) : ℝ) * (q : ℝ) ^ (N + 1) * ((2 * K + 1) * (K + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_right hcat hQ.le]
  exact lt_of_mul_lt_mul_right (by linarith) hD.le

/-- [proved-standard; formal-checked] **Alon–Boppana, finite form.**  For every `μ` with `μ² < 4q`
there is a size past which every complex with `q + 1` darts at every cell has a mode other than the
count with `|λ_i| > μ`. -/
theorem alon_boppana {q : ℕ} {μ : ℝ} (hμ : μ ^ 2 < 4 * q) :
    ∃ N : ℕ, ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (a b : E → V), (∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1) →
      N ≤ Fintype.card V → ∀ i₀ : V, eigen a b i₀ = (q : ℝ) + 1 →
      ∃ i, i ≠ i₀ ∧ μ < |eigen a b i| := by
  obtain ⟨k, hk⟩ := exists_catalan_floor_gt hμ
  refine ⟨2 * (q + 1) ^ (2 * k), ?_⟩
  intro V E _ _ _ _ a b hreg hN i₀ h0
  by_contra hne
  have hcon : ∀ i, i ≠ i₀ → |eigen a b i| ≤ μ := fun i hi => le_of_not_gt fun h => hne ⟨i, hi, h⟩
  have hq1 : 1 ≤ q := by
    have : (0 : ℝ) < q := by nlinarith [sq_nonneg μ]
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ (catalan k : ℝ) * (q : ℝ) ^ k :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast catalan_pos' k)
      (one_le_pow₀ (by exact_mod_cast hq1))
  have h2 : 2 * ((q : ℝ) + 1) ^ (2 * k) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hN
  have hn : 2 * ((q : ℝ) + 1) ^ (2 * k) ≤
      (Fintype.card V : ℝ) * ((catalan k : ℝ) * (q : ℝ) ^ k) :=
    h2.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) h1)
  have := floor_half a b hreg k h0 hcon hn
  linarith

/-! ## Audit -/

section Audit

#print axioms hashimoto_eq
#print axioms end_mul_end_transpose
#print axioms end_mul_hashimoto
#print axioms adjacency_mul_nbWalk
#print axioms treeCount_eq_zero_of_lt
#print axioms treeCount_self
#print axioms treeCount_succ_zero
#print axioms treeCount_succ_succ
#print axioms adjacency_pow_eq_sum
#print axioms mul_entry_nonneg
#print axioms nbWalk_nonneg
#print axioms treeCount_le_adjacency_pow_diag
#print axioms ballot_zero
#print axioms ballot_succ_zero
#print axioms ballot_succ_succ
#print axioms pow_mul_ballot_le_treeCount
#print axioms ballot_eq_form
#print axioms ballot_zero_right
#print axioms four_pow_le_catalan
#print axioms catalan_pos'
#print axioms catalan_mul_pow_le_adjacency_pow_diag
#print axioms trace_adjacency_pow
#print axioms card_mul_catalan_le_trace
#print axioms floor
#print axioms floor_div
#print axioms floor_half
#print axioms exists_catalan_floor_gt
#print axioms alon_boppana

end Audit

end Holonics.Landmarks.TreeWalkFloor
