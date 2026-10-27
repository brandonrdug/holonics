import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# The torus's two twists compose into every kind of move

The record `research/records/2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`
(§6 and §13(e)) owes to #410 the braid words in `SL(2, ℤ)` and the cat map's Lucas fixed points.
`T = [[1,1],[0,1]]` and `L = [[1,0],[−1,1]]` are the torus's two Dehn twists, each a pure carry (a
shear).

[proved-standard; formal-checked] What is proved.

1. **The braid relation** (`braid`): `T L T = L T L`.
2. **The quarter turn** (`quarter_turn`, `quarter_turn_sq`): `T L T = [[0,1],[−1,0]]`, which squares to `−1`.
3. **A turn of order six** (`turn_eq`, `trace_turn`, `turn_cube`, `orderOf_turn`):
   `T L = [[0,1],[−1,1]]`, trace `1`, `(T L)³ = −1`, so `T L` has order `6`.
4. **The cat map is a boost** (`L_mul_Linv`, `cat_eq`, `trace_cat`, `det_cat`, `det_sub_one_fin_two`):
   `T L⁻¹ = [[2,1],[1,1]] = A`, trace `3`, determinant `1`.
5. **Its fixed-point counts are the Lucas numbers less two** (`cat_pow`, `det_cat_pow_sub_one`,
   `abs_det_cat_pow_sub_one`, `cat_counts`): `A^(k+1) = [[F_(2k+3), F_(2k+2)], [F_(2k+2), F_(2k+1)]]`
   with `F` the Fibonacci numbers, so `det(A^(k+1) − 1) = 2 − L_(2k+2)` with
   `L_(2k+2) = F_(2k+1) + F_(2k+3)` the Lucas number, and `|det(Aᵏ − 1)| = L_(2k) − 2`:
   1, 5, 16, 45, 121 for `k = 1, …, 5`.
6. **Two boosts compose into a shear** (`A_mul_Ainv`, `B_mul_Binv`, `boost_commutator`,
   `trace_boost_commutator`): with
   `B = [[1,1],[1,2]]`, `A B A⁻¹ B⁻¹ = [[−7,6],[−6,5]]`, trace `−2`.

The index law that turns item 5's determinant into the count, that an automorphism `M` of the
torus `ℝ²/ℤ²` with `det(M − 1) ≠ 0` has exactly `|det(M − 1)|` fixed points, is
`Geometry/TorusIndex` (`card_fixed`, `cat_fixed_points`).

Consumers: the atlas row `motion.torus-twists-every-kind` and `Geometry/TorusIndex`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.TorusBraid

open Matrix

/-- [definition] The Dehn twist `T = [[1,1],[0,1]]`. -/
def T : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

/-- [definition] The Dehn twist `L = [[1,0],[−1,1]]`. -/
def L : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; -1, 1]

/-- [definition] `L⁻¹ = [[1,0],[1,1]]`. -/
def Linv : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]

/-- [definition] The cat map `A = [[2,1],[1,1]]`. -/
def A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]

/-- [definition] `A⁻¹ = [[1,−1],[−1,2]]`. -/
def Ainv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; -1, 2]

/-- [definition] The second boost `B = [[1,1],[1,2]]`. -/
def B : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 2]

/-- [definition] `B⁻¹ = [[2,−1],[−1,1]]`. -/
def Binv : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -1, 1]

/-- [proved-standard; formal-checked] **The braid relation** `T L T = L T L`. -/
theorem braid : T * L * T = L * T * L := by
  simp [T, L]

/-- [proved-standard; formal-checked] **The quarter turn** `T L T = [[0,1],[−1,0]]`. -/
theorem quarter_turn : T * L * T = !![0, 1; -1, 0] := by
  simp [T, L]

/-- [proved-standard; formal-checked] The quarter turn squares to `−1`. -/
theorem quarter_turn_sq : (T * L * T) * (T * L * T) = -1 := by
  rw [quarter_turn]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] `T L = [[0,1],[−1,1]]`. -/
theorem turn_eq : T * L = !![0, 1; -1, 1] := by
  simp [T, L]

/-- [proved-standard; formal-checked] `T L` has trace `1`. -/
theorem trace_turn : (T * L).trace = 1 := by
  rw [turn_eq, Matrix.trace_fin_two_of]
  norm_num

/-- [proved-standard; formal-checked] **`(T L)³ = −1`.** -/
theorem turn_cube : (T * L) ^ 3 = -1 := by
  rw [turn_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **`T L` is a turn of order six.** -/
theorem orderOf_turn : orderOf (T * L) = 6 := by
  have h6 : (T * L) ^ 6 = 1 := by
    rw [show 6 = 3 * 2 from rfl, pow_mul, turn_cube]
    simp
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨h6, fun m hm hm0 h => ?_⟩
  rw [turn_eq] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  interval_cases m <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01

/-- [proved-standard; formal-checked] `L L⁻¹ = 1`. -/
theorem L_mul_Linv : L * Linv = 1 := by
  rw [Matrix.one_fin_two]
  simp [L, Linv]

/-- [proved-standard; formal-checked] **The cat map is `T L⁻¹`.** -/
theorem cat_eq : T * Linv = A := by
  simp [T, Linv, A]

/-- [proved-standard; formal-checked] The cat map has trace `3`: a boost. -/
theorem trace_cat : A.trace = 3 := by
  rw [A, Matrix.trace_fin_two_of]
  norm_num

/-- [proved-standard; formal-checked] The cat map has determinant `1`. -/
theorem det_cat : A.det = 1 := by
  rw [A, Matrix.det_fin_two_of]
  norm_num

/-- [proved-standard; formal-checked] **The cat map's powers are Fibonacci:**
`A^(k+1) = [[F_(2k+3), F_(2k+2)], [F_(2k+2), F_(2k+1)]]`. -/
theorem cat_pow (k : ℕ) :
    A ^ (k + 1) = !![(Nat.fib (2 * k + 3) : ℤ), Nat.fib (2 * k + 2);
      Nat.fib (2 * k + 2), Nat.fib (2 * k + 1)] := by
  induction k with
  | zero =>
    rw [pow_one, A]
    have h3 : Nat.fib 3 = 2 := rfl
    simp [h3]
  | succ k ih =>
    have h3 : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := Nat.fib_add_two
    have h4 : Nat.fib (2 * (k + 1) + 2) = Nat.fib (2 * k + 2) + Nat.fib (2 * k + 3) := by
      rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by ring, Nat.fib_add_two]
    have h5 : Nat.fib (2 * (k + 1) + 3) = Nat.fib (2 * k + 3) + Nat.fib (2 * (k + 1) + 2) := by
      rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 2 by ring, Nat.fib_add_two,
        show 2 * k + 3 + 1 = 2 * (k + 1) + 2 by ring]
    have h1 : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
    rw [pow_succ, ih, A, Matrix.mul_fin_two, h5, h4, h1, h3]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals (try simp)
    all_goals ring

/-- [proved-standard; formal-checked] For a `2 × 2` matrix, `det(M − 1) = det M − tr M + 1`. -/
theorem det_sub_one_fin_two (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (M - 1).det = M.det - M.trace + 1 := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp [Matrix.sub_apply]
  ring

/-- [proved-standard; formal-checked] **`det(A^(k+1) − 1) = 2 − L_(2k+2)`** with
`L_(2k+2) = F_(2k+1) + F_(2k+3)`. -/
theorem det_cat_pow_sub_one (k : ℕ) :
    (A ^ (k + 1) - 1).det = 2 - ((Nat.fib (2 * k + 1) : ℤ) + Nat.fib (2 * k + 3)) := by
  rw [det_sub_one_fin_two, Matrix.det_pow, det_cat, one_pow, cat_pow, Matrix.trace_fin_two_of]
  ring

/-- [proved-standard; formal-checked] **`|det(A^(k+1) − 1)| = L_(2k+2) − 2`**, the number of the
cat map's fixed points on the torus by the index law (`TorusIndex.cat_fixed_points`). -/
theorem abs_det_cat_pow_sub_one (k : ℕ) :
    |(A ^ (k + 1) - 1).det| = ((Nat.fib (2 * k + 1) : ℤ) + Nat.fib (2 * k + 3)) - 2 := by
  rw [det_cat_pow_sub_one, abs_sub_comm]
  have h3 : (2 : ℤ) ≤ Nat.fib (2 * k + 3) := by
    have hmono : Nat.fib 3 ≤ Nat.fib (2 * k + 3) := Nat.fib_mono (by omega)
    have h : Nat.fib 3 = 2 := rfl
    rw [h] at hmono
    exact_mod_cast hmono
  have h1 : (0 : ℤ) ≤ Nat.fib (2 * k + 1) := Nat.cast_nonneg _
  exact abs_of_nonneg (by linarith)

/-- [proved-standard; formal-checked] **The counts for `k = 1, …, 5`:** 1, 5, 16, 45, 121. -/
theorem cat_counts :
    (List.range 5).map (fun k => Nat.fib (2 * k + 1) + Nat.fib (2 * k + 3) - 2) =
      [1, 5, 16, 45, 121] := by
  decide

/-- [proved-standard; formal-checked] `A A⁻¹ = 1` and `B B⁻¹ = 1`. -/
theorem A_mul_Ainv : A * Ainv = 1 := by
  rw [Matrix.one_fin_two]
  simp [A, Ainv]

theorem B_mul_Binv : B * Binv = 1 := by
  rw [Matrix.one_fin_two]
  simp [B, Binv]

/-- [proved-standard; formal-checked] **Two boosts compose into a shear:**
`A B A⁻¹ B⁻¹ = [[−7,6],[−6,5]]`. -/
theorem boost_commutator : A * B * Ainv * Binv = !![-7, 6; -6, 5] := by
  simp [A, B, Ainv, Binv]

/-- [proved-standard; formal-checked] The commutator has trace `−2`: a shear. -/
theorem trace_boost_commutator : (A * B * Ainv * Binv).trace = -2 := by
  rw [boost_commutator, Matrix.trace_fin_two_of]
  norm_num

end Holonics.Geometry.TorusBraid
