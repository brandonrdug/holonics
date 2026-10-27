import Mathlib.NumberTheory.Niven
import Holonics.Geometry.Turn
import Holonics.HNN.FloquetPassage
import Holonics.Compression.Landmark.SiteKind
import HolonicsResearch.Geometry.TorusIndex

/-!
# A turn holding a lattice has order 1, 2, 3, 4 or 6, and its `2 cos` is one of Niven's values

#410 owes the crystallographic restriction: a turn holding a lattice has order 1, 2, 3, 4 or 6.
Niven's values (the atlas row `winding.niven-star-values`: `2 cos(2πm/n)` is rational exactly at
those orders, with values `2, −2, −1, 0, 1`) were checked only in Rust history, and
`Geometry/Turn` proves the first refused value, `2 cos(π/5) = φ`. This file proves the restriction,
joins it to Niven's theorem (Mathlib's `niven` and `irrational_cos_rat_mul_pi`), and reads the
fifth turn's refusal through `Geometry/Turn`.

A real linear map `R` of the plane **holds a lattice** (`HoldsLattice`) when a basis `P` (its
columns) reads it as an integer matrix: `R P = P N` with `N` integral. Then `R` maps the lattice
`P ℤ²` into itself, and `N` is `R` read in that lattice's coordinates.

[proved-standard; formal-checked] What is proved.

1. **A returning integer move has order 1, 2, 3, 4 or 6** (`sq_trace_det`, `trace_sq_le`,
   `pow_one_add`, `eq_one_of_trace_two`, `cube_of_trace_neg_one`, `sq_of_trace_zero`,
   `cube_of_trace_one`, `pow_four_or_pow_six`, `orderOf_lattice`). Its determinant is a unit, `±1`.
   At determinant 1 a returning move has `tr² ≤ 4`, since a boost's closed-word counts grow
   (`SiteKind.boost_counts_grow`), and Cayley–Hamilton `M² = (tr M) M − 1` closes each of the
   five traces: trace 0 gives `M² = −1`, trace 1 gives `M³ = −1`, trace −1 gives `M³ = 1`, and trace
   `±2` gives a shear `±(1 + D)` with `D² = 0`, which returns only when `D = 0`. At determinant −1,
   `M²` has determinant 1 and trace `tr² + 2`, so `tr M = 0` and `M² = 1`. So `M⁴ = 1` or `M⁶ = 1`.
2. **The return, the trace and the determinant move with the lattice**
   (`pow_eq_one_iff_of_holds`, `orderOf_eq_of_holds`, `trace_eq_of_holds`, `det_eq_of_holds`,
   `holds_pow`): a map holding a lattice returns exactly when its integer reading returns, and has
   that reading's trace and determinant.
3. **The crystallographic restriction** (`orderOf_of_holds`, `two_cos_of_holds`,
   `two_cos_mem_of_holds`, `crystallographic_restriction`): a finite-order map holding a lattice
   has order 1, 2, 3, 4 or 6; a turn `Rot(θ)` holding a lattice has `2 cos θ ∈ {−2, −1, 0, 1, 2}`
   and, with no finite order assumed, order 1, 2, 3, 4 or 6.
4. **Every one of those orders occurs** (`quarter_turn_holds`, `sixth_turn_holds`,
   `third_turn_holds`, `half_turn_holds`, `whole_turn_holds`, the five `orderOf_…_turn`, and
   `lattice_turn_orders`): the quarter turn holds the square lattice `ℤ²`, and the sixth turn holds
   the hexagonal lattice, read there as the torus braid's `T L` (`TorusBraid.orderOf_turn`); its
   powers give the third, half and whole turns. So the orders of lattice turns are exactly
   `{1, 2, 3, 4, 6}`.
5. **Niven's values** (`niven_values`, `two_cos_rat_iff`, `no_lattice_of_den`,
   `fifth_turn_holds_no_lattice`): for rational `r`, a rational `2 cos(rπ)` is one of
   `2, 1, 0, −1, −2` (Mathlib's `niven`), and `2 cos(rπ)` is rational exactly when `den r ≤ 3`. The
   converse is item 4's lattices, since `2 cos(rπ)` is then a lattice turn's integer trace. A turn by
   `rπ` with `den r > 3` holds no lattice (Mathlib's `irrational_cos_rat_mul_pi`). The fifth turn is
   the first refusal: `2 cos(π/5) = φ` (`Turn.theGoldenRatioIsTwiceACosineOfTheFifthTurn`) lies
   strictly between 1 and 2.

The atlas row states Niven's set as `2cos(2πm/n) ∈ ℚ ⇔ n/gcd(m,n) ∈ {1,2,3,4,6}`. Here `r = 2m/n`;
the elementary reduction `den(2m/n) ≤ 3 ⇔ n/gcd(m,n) ∈ {1,2,3,4,6}` is not formalized.

The computational object is the helical pair interaction read on a lattice. A turn holding the
lattice is a pairing whose winding returns to the lattice after one, two, three, four or six moves,
and its trace is the pair's `2 cos`. Of the winding guide's six general objects this touches the
helix (the turn and its powers) and the cell holonomy (the lattice it holds); the pair, faces and
placement, the tube and the tower thread stay attached.

Consumers: the atlas rows `winding.crystallographic-restriction` and `winding.niven-star-values`,
and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Geometry.Crystallographic

open Real
open Holonics.Geometry.TorusIndex (toReal det_toReal)
open Holonics.Compression.Landmark

/-! ## 1. A returning integer move -/

/-- [proved-standard; formal-checked] Cayley–Hamilton for a two-by-two integer move:
`M² = (tr M) M − (det M) 1`. -/
theorem sq_trace_det (M : Matrix (Fin 2) (Fin 2) ℤ) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] <;>
    simp <;> ring

/-- [proved-standard; formal-checked] A returning move of determinant 1 is no boost: `tr² ≤ 4`. -/
theorem trace_sq_le (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) {m : ℕ} (hm : 0 < m)
    (h : M ^ m = 1) : M.trace ^ 2 ≤ 4 := by
  by_contra hc
  have hgrow := SiteKind.boost_counts_grow M.trace (not_le.mp hc) m
  have htr := SiteKind.trace_pow_eq M m
  rw [h, hdet, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat] at htr
  rw [← htr, abs_of_pos (by norm_num : (0 : ℤ) < 2)] at hgrow
  omega

/-- [proved-standard; formal-checked] A shear `1 + D` with `D² = 0` moves by
`(1 + D)ᵏ = 1 + k D`. -/
theorem pow_one_add {D : Matrix (Fin 2) (Fin 2) ℤ} (hD : D * D = 0) (k : ℕ) :
    (1 + D) ^ k = 1 + (k : ℤ) • D := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, hD, smul_zero, add_zero,
      Nat.cast_succ, add_smul, one_smul]
    abel

/-- [proved-standard; formal-checked] A returning move of determinant 1 and trace 2 is the
identity: a shear returns only when it does not shear. -/
theorem eq_one_of_trace_two (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (htr : M.trace = 2) {m : ℕ} (hm : 0 < m) (h : M ^ m = 1) : M = 1 := by
  have hch := sq_trace_det M
  rw [htr, hdet, one_smul] at hch
  have hD : (M - 1) * (M - 1) = 0 := by
    have e : (M - 1) * (M - 1) = M ^ 2 - (2 : ℤ) • M + 1 := by
      rw [sq, two_smul]
      noncomm_ring
    rw [e, hch]
    abel
  have e1 : (1 : Matrix (Fin 2) (Fin 2) ℤ) + (M - 1) = M := by abel
  have hpow := pow_one_add hD m
  rw [e1, h] at hpow
  have hz : (m : ℤ) • (M - 1) = 0 := by
    calc (m : ℤ) • (M - 1) = (1 + (m : ℤ) • (M - 1)) - 1 := by abel
      _ = 0 := by rw [← hpow, sub_self]
  ext i j
  have hij := congrFun (congrFun hz i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hij
  rcases mul_eq_zero.mp hij with h0 | h1
  · omega
  · exact sub_eq_zero.mp (by simpa only [Matrix.sub_apply] using h1)

/-- [proved-standard; formal-checked] Trace −1 at determinant 1: `M³ = 1`. -/
theorem cube_of_trace_neg_one (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (ht : M.trace = -1) : M ^ 3 = 1 := by
  have hch := sq_trace_det M
  rw [ht, hdet, one_smul, neg_one_smul] at hch
  calc M ^ 3 = M * M ^ 2 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ']
    _ = M * (-M - 1) := by rw [hch]
    _ = -(M ^ 2) - M := by noncomm_ring
    _ = 1 := by rw [hch]; abel

/-- [proved-standard; formal-checked] Trace 0 at determinant 1: `M² = −1`. -/
theorem sq_of_trace_zero (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (ht : M.trace = 0) : M ^ 2 = -1 := by
  have hch := sq_trace_det M
  rw [ht, hdet, zero_smul, one_smul, zero_sub] at hch
  exact hch

/-- [proved-standard; formal-checked] Trace 1 at determinant 1: `M³ = −1`. -/
theorem cube_of_trace_one (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (ht : M.trace = 1) : M ^ 3 = -1 := by
  have hch := sq_trace_det M
  rw [ht, hdet, one_smul, one_smul] at hch
  calc M ^ 3 = M * M ^ 2 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ']
    _ = M * (M - 1) := by rw [hch]
    _ = M ^ 2 - M := by noncomm_ring
    _ = -1 := by rw [hch]; abel

/-- [proved-standard; formal-checked] **A returning integer move satisfies `M⁴ = 1` or
`M⁶ = 1`.** -/
theorem pow_four_or_pow_six (M : Matrix (Fin 2) (Fin 2) ℤ) {m : ℕ} (hm : 0 < m)
    (h : M ^ m = 1) : M ^ 4 = 1 ∨ M ^ 6 = 1 := by
  have hunit : IsUnit M.det :=
    IsUnit.of_pow_eq_one (by rw [← Matrix.det_pow, h, Matrix.det_one]) hm.ne'
  rcases Int.isUnit_iff.mp hunit with hdet | hdet
  · have hsq := trace_sq_le M hdet hm h
    have hlo : -2 ≤ M.trace := by nlinarith
    have hhi : M.trace ≤ 2 := by nlinarith
    have hcases : M.trace = -2 ∨ M.trace = -1 ∨ M.trace = 0 ∨ M.trace = 1 ∨ M.trace = 2 := by
      omega
    rcases hcases with ht | ht | ht | ht | ht
    · left
      have hneg : -M = 1 := by
        refine eq_one_of_trace_two (-M) ?_ ?_ (m := 2 * m) (by omega) ?_
        · simp [Matrix.det_neg, hdet]
        · simp [Matrix.trace_neg, ht]
        · rw [pow_mul, neg_sq, ← pow_mul, mul_comm, pow_mul, h, one_pow]
      have hM : M = -1 := neg_eq_iff_eq_neg.mp hneg
      rw [hM, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow]
    · right
      rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, cube_of_trace_neg_one M hdet ht, one_pow]
    · left
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_of_trace_zero M hdet ht, neg_one_sq]
    · right
      rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, cube_of_trace_one M hdet ht, neg_one_sq]
    · left
      rw [eq_one_of_trace_two M hdet ht hm h, one_pow]
  · have hch := sq_trace_det M
    rw [hdet, neg_one_smul, sub_neg_eq_add] at hch
    have hdet2 : (M ^ 2).det = 1 := by
      rw [Matrix.det_pow, hdet]
      norm_num
    have htr2 : (M ^ 2).trace = M.trace ^ 2 + 2 := by
      rw [hch, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
        smul_eq_mul]
      push_cast
      ring
    have hsq := trace_sq_le (M ^ 2) hdet2 hm (by rw [← pow_mul, mul_comm, pow_mul, h, one_pow])
    rw [htr2] at hsq
    have ht0 : M.trace = 0 := by
      have h2 : M.trace ^ 2 = 0 := by nlinarith [sq_nonneg M.trace, sq_nonneg (M.trace ^ 2)]
      exact (pow_eq_zero_iff two_ne_zero).mp h2
    rw [ht0, zero_smul, zero_add] at hch
    left
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hch, one_pow]

/-- [proved-standard; formal-checked] **An integer move of finite order has order 1, 2, 3, 4
or 6.** -/
theorem orderOf_lattice (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : IsOfFinOrder M) :
    orderOf M = 1 ∨ orderOf M = 2 ∨ orderOf M = 3 ∨ orderOf M = 4 ∨ orderOf M = 6 := by
  have hpos := hM.orderOf_pos
  have hdvd : orderOf M ∣ 4 ∨ orderOf M ∣ 6 :=
    (pow_four_or_pow_six M hpos (pow_orderOf_eq_one M)).imp orderOf_dvd_of_pow_eq_one
      orderOf_dvd_of_pow_eq_one
  obtain ⟨o, ho⟩ : ∃ o, orderOf M = o := ⟨_, rfl⟩
  rw [ho] at hpos hdvd ⊢
  have hle : o ≤ 6 := by
    rcases hdvd with h | h
    · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) h
  interval_cases o <;> omega

/-! ## 2. The return, the trace and the determinant move with the lattice -/

/-- [definition] A real linear map of the plane **holds a lattice** when a basis `P` (its columns)
reads it as an integer matrix `N`: `R P = P N`. Then `R` maps the lattice `P ℤ²` into itself. -/
def HoldsLattice (R : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℝ, IsUnit P.det ∧
    ∃ N : Matrix (Fin 2) (Fin 2) ℤ, R * P = P * toReal N

theorem toReal_pow (N : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ) : toReal (N ^ k) = toReal N ^ k := by
  have e : ∀ M : Matrix (Fin 2) (Fin 2) ℤ, toReal M = (Int.castRingHom ℝ).mapMatrix M :=
    fun M => by
      ext i j
      simp [toReal]
  rw [e, e, map_pow]

theorem toReal_one : toReal (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
  Matrix.map_one _ Int.cast_zero Int.cast_one

theorem toReal_injective : Function.Injective (toReal : Matrix (Fin 2) (Fin 2) ℤ → _) :=
  Matrix.map_injective Int.cast_injective

/-- [proved-standard; formal-checked] **A map holding a lattice returns exactly when its integer
reading returns.** -/
theorem pow_eq_one_iff_of_holds {R P : Matrix (Fin 2) (Fin 2) ℝ} (hP : IsUnit P.det)
    {N : Matrix (Fin 2) (Fin 2) ℤ} (h : R * P = P * toReal N) (k : ℕ) :
    R ^ k = 1 ↔ N ^ k = 1 := by
  have hs : SemiconjBy P (toReal N) R := h.symm
  have hk : P * toReal (N ^ k) = R ^ k * P := by
    rw [toReal_pow]
    exact hs.pow_right k
  constructor
  · intro hR
    rw [hR, one_mul] at hk
    apply toReal_injective
    rw [toReal_one]
    calc toReal (N ^ k) = P⁻¹ * (P * toReal (N ^ k)) := by
          rw [← mul_assoc, Matrix.nonsing_inv_mul P hP, one_mul]
      _ = 1 := by rw [hk, Matrix.nonsing_inv_mul P hP]
  · intro hN
    rw [hN, toReal_one, mul_one] at hk
    calc R ^ k = R ^ k * P * P⁻¹ := by rw [mul_assoc, Matrix.mul_nonsing_inv P hP, mul_one]
      _ = 1 := by rw [← hk, Matrix.mul_nonsing_inv P hP]

/-- [proved-standard; formal-checked] A map holding a lattice has its integer reading's order. -/
theorem orderOf_eq_of_holds {R P : Matrix (Fin 2) (Fin 2) ℝ} (hP : IsUnit P.det)
    {N : Matrix (Fin 2) (Fin 2) ℤ} (h : R * P = P * toReal N) : orderOf R = orderOf N :=
  orderOf_eq_orderOf_iff.mpr (pow_eq_one_iff_of_holds hP h)

/-- [proved-standard; formal-checked] A map holding a lattice has its integer reading's trace. -/
theorem trace_eq_of_holds {R P : Matrix (Fin 2) (Fin 2) ℝ} (hP : IsUnit P.det)
    {N : Matrix (Fin 2) (Fin 2) ℤ} (h : R * P = P * toReal N) : R.trace = (N.trace : ℝ) := by
  have hN : toReal N = P⁻¹ * (R * P) := by
    rw [h, ← mul_assoc, Matrix.nonsing_inv_mul P hP, one_mul]
  have htr : (toReal N).trace = R.trace := by
    rw [hN, Matrix.trace_mul_comm, mul_assoc, Matrix.mul_nonsing_inv P hP, mul_one]
  rw [← htr, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [toReal]

/-- [proved-standard; formal-checked] A map holding a lattice has its integer reading's
determinant. -/
theorem det_eq_of_holds {R P : Matrix (Fin 2) (Fin 2) ℝ} (hP : IsUnit P.det)
    {N : Matrix (Fin 2) (Fin 2) ℤ} (h : R * P = P * toReal N) : R.det = (N.det : ℝ) := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, det_toReal, mul_comm P.det] at hd
  exact mul_right_cancel₀ hP.ne_zero hd

/-- [proved-standard; formal-checked] The powers of a map holding a lattice hold it. -/
theorem holds_pow {R : Matrix (Fin 2) (Fin 2) ℝ} (h : HoldsLattice R) (k : ℕ) :
    HoldsLattice (R ^ k) := by
  obtain ⟨P, hP, N, hN⟩ := h
  refine ⟨P, hP, N ^ k, ?_⟩
  have hs : SemiconjBy P (toReal N) R := hN.symm
  rw [toReal_pow]
  exact Eq.symm (hs.pow_right k)

/-! ## 3. The crystallographic restriction -/

/-- [proved-standard; formal-checked] **A finite-order map holding a lattice has order 1, 2, 3, 4
or 6.** -/
theorem orderOf_of_holds {R : Matrix (Fin 2) (Fin 2) ℝ} (h : HoldsLattice R)
    (hfin : IsOfFinOrder R) :
    orderOf R = 1 ∨ orderOf R = 2 ∨ orderOf R = 3 ∨ orderOf R = 4 ∨ orderOf R = 6 := by
  obtain ⟨P, hP, N, hN⟩ := h
  rw [orderOf_eq_of_holds hP hN]
  apply orderOf_lattice
  rw [← orderOf_pos_iff, ← orderOf_eq_of_holds hP hN]
  exact hfin.orderOf_pos

/-- [definition] The turn by `θ`, `Rot(θ) = [[cos θ, −sin θ], [sin θ, cos θ]]`
(`HNN/FloquetPassage.rotation`). -/
def turn (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Holonics.HNN.FloquetPassage.rotation (Real.cos θ) (Real.sin θ)

theorem trace_turn (θ : ℝ) : (turn θ).trace = 2 * Real.cos θ := by
  rw [turn, Holonics.HNN.FloquetPassage.rotation, Matrix.trace_fin_two_of]
  ring

theorem det_turn (θ : ℝ) : (turn θ).det = 1 := by
  rw [turn, Holonics.HNN.FloquetPassage.rotation, Matrix.det_fin_two_of]
  linear_combination Real.cos_sq_add_sin_sq θ

theorem turn_zero : turn 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [turn, Holonics.HNN.FloquetPassage.rotation]

theorem turn_add (a b : ℝ) : turn a * turn b = turn (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [turn, Holonics.HNN.FloquetPassage.rotation, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add] <;>
    ring

theorem turn_pow (θ : ℝ) (k : ℕ) : turn θ ^ k = turn (k * θ) := by
  induction k with
  | zero => simp [turn_zero]
  | succ k ih => rw [pow_succ, ih, turn_add, Nat.cast_succ, add_mul, one_mul]

/-- [proved-standard; formal-checked] **A turn holding a lattice has an integer `2 cos`**, one of
`−2, −1, 0, 1, 2`. -/
theorem two_cos_of_holds {θ : ℝ} (h : HoldsLattice (turn θ)) :
    ∃ t : ℤ, 2 * Real.cos θ = t ∧ (t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2) := by
  obtain ⟨P, hP, N, hN⟩ := h
  have ht : 2 * Real.cos θ = (N.trace : ℝ) := by rw [← trace_turn, trace_eq_of_holds hP hN]
  refine ⟨N.trace, ht, ?_⟩
  have hlo : (-2 : ℝ) ≤ N.trace := by linarith [Real.neg_one_le_cos θ]
  have hhi : (N.trace : ℝ) ≤ 2 := by linarith [Real.cos_le_one θ]
  have hlo' : -2 ≤ N.trace := by exact_mod_cast hlo
  have hhi' : N.trace ≤ 2 := by exact_mod_cast hhi
  omega

/-- [proved-standard; formal-checked] The same, as a set of values. -/
theorem two_cos_mem_of_holds {θ : ℝ} (h : HoldsLattice (turn θ)) :
    2 * Real.cos θ ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
  obtain ⟨t, ht, hv⟩ := two_cos_of_holds h
  rw [ht]
  rcases hv with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- [proved-standard; formal-checked] **The crystallographic restriction**: a turn holding a lattice
has order 1, 2, 3, 4 or 6. No finite order is assumed: the lattice forces it. -/
theorem crystallographic_restriction {θ : ℝ} (h : HoldsLattice (turn θ)) :
    orderOf (turn θ) = 1 ∨ orderOf (turn θ) = 2 ∨ orderOf (turn θ) = 3 ∨
      orderOf (turn θ) = 4 ∨ orderOf (turn θ) = 6 := by
  apply orderOf_of_holds h
  obtain ⟨P, hP, N, hN⟩ := h
  have ht : 2 * Real.cos θ = (N.trace : ℝ) := by rw [← trace_turn, trace_eq_of_holds hP hN]
  have hdet : N.det = 1 := by
    have := det_eq_of_holds hP hN
    rw [det_turn] at this
    exact_mod_cast this.symm
  obtain ⟨t, htc, hv⟩ := two_cos_of_holds ⟨P, hP, N, hN⟩
  have htr : N.trace = t := by exact_mod_cast ht.symm.trans htc
  rw [isOfFinOrder_iff_pow_eq_one]
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · have hc : Real.cos θ = -1 := by
      push_cast at htc
      linarith
    have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inr hc)
    have hR : turn θ = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [turn, Holonics.HNN.FloquetPassage.rotation, hc, hs]
    exact ⟨2, by norm_num, by rw [hR, neg_one_sq]⟩
  · exact ⟨3, by norm_num, (pow_eq_one_iff_of_holds hP hN 3).mpr
      (cube_of_trace_neg_one N hdet htr)⟩
  · exact ⟨4, by norm_num, (pow_eq_one_iff_of_holds hP hN 4).mpr (by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_of_trace_zero N hdet htr, neg_one_sq])⟩
  · exact ⟨6, by norm_num, (pow_eq_one_iff_of_holds hP hN 6).mpr (by
      rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, cube_of_trace_one N hdet htr, neg_one_sq])⟩
  · have hc : Real.cos θ = 1 := by
      push_cast at htc
      linarith
    have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl hc)
    have hR : turn θ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [turn, Holonics.HNN.FloquetPassage.rotation, hc, hs]
    exact ⟨1, by norm_num, by rw [hR, one_pow]⟩

/-! ## 4. Every one of those orders occurs -/

/-- [proved-standard; formal-checked] The quarter turn holds the square lattice `ℤ²`, read there
as `[[0, −1], [1, 0]]`. -/
theorem quarter_turn_eq : turn (π / 2) * 1 = 1 * toReal !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [turn, Holonics.HNN.FloquetPassage.rotation, toReal]

theorem quarter_turn_holds : HoldsLattice (turn (π / 2)) :=
  ⟨1, by simp, _, quarter_turn_eq⟩

theorem orderOf_quarter_turn : orderOf (turn (π / 2)) = 4 := by
  rw [orderOf_eq_of_holds (by simp) quarter_turn_eq]
  have h2 : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, neg_one_sq], fun m hm hm0 h => ?_⟩
  have h00 := congrFun (congrFun h 0) 0
  interval_cases m <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- [proved-standard; formal-checked] The sixth turn holds the hexagonal lattice spanned by
`(1, 0)` and `(−1/2, −√3/2)`, read there as the torus braid's `T L = [[0, 1], [−1, 1]]`. -/
theorem sixth_turn_eq :
    turn (π / 3) * !![1, -1 / 2; 0, -(Real.sqrt 3 / 2)] =
      !![1, -1 / 2; 0, -(Real.sqrt 3 / 2)] * toReal !![0, 1; -1, 1] := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [turn, Holonics.HNN.FloquetPassage.rotation, toReal, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cos_pi_div_three, Real.sin_pi_div_three] <;>
    nlinarith [h3]

theorem isUnit_hexagonal :
    IsUnit (!![1, -1 / 2; 0, -(Real.sqrt 3 / 2)] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.det_fin_two_of, isUnit_iff_ne_zero]
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  linarith

theorem sixth_turn_holds : HoldsLattice (turn (π / 3)) :=
  ⟨_, isUnit_hexagonal, _, sixth_turn_eq⟩

theorem orderOf_sixth_turn : orderOf (turn (π / 3)) = 6 := by
  rw [orderOf_eq_of_holds isUnit_hexagonal sixth_turn_eq, ← TorusBraid.turn_eq,
    TorusBraid.orderOf_turn]

theorem third_turn_holds : HoldsLattice (turn (2 * π / 3)) := by
  have h := holds_pow sixth_turn_holds 2
  rwa [turn_pow, show ((2 : ℕ) : ℝ) * (π / 3) = 2 * π / 3 by push_cast; ring] at h

theorem orderOf_third_turn : orderOf (turn (2 * π / 3)) = 3 := by
  have h := orderOf_pow' (turn (π / 3)) (by norm_num : (2 : ℕ) ≠ 0)
  rw [orderOf_sixth_turn, turn_pow] at h
  rw [show 2 * π / 3 = ((2 : ℕ) : ℝ) * (π / 3) by push_cast; ring]
  exact h.trans (by norm_num)

theorem half_turn_holds : HoldsLattice (turn π) := by
  have h := holds_pow sixth_turn_holds 3
  rwa [turn_pow, show ((3 : ℕ) : ℝ) * (π / 3) = π by push_cast; ring] at h

theorem orderOf_half_turn : orderOf (turn π) = 2 := by
  have h := orderOf_pow' (turn (π / 3)) (by norm_num : (3 : ℕ) ≠ 0)
  rw [orderOf_sixth_turn, turn_pow] at h
  rw [show π = ((3 : ℕ) : ℝ) * (π / 3) by push_cast; ring]
  exact h.trans (by norm_num)

theorem whole_turn_holds : HoldsLattice (turn 0) := by
  rw [turn_zero]
  exact ⟨1, by simp, 1, by rw [toReal_one]⟩

theorem orderOf_whole_turn : orderOf (turn 0) = 1 := by
  rw [turn_zero, orderOf_one]

/-- [proved-standard; formal-checked] **The orders of lattice turns are exactly
`{1, 2, 3, 4, 6}`.** -/
theorem lattice_turn_orders (d : ℕ) :
    (∃ θ : ℝ, HoldsLattice (turn θ) ∧ orderOf (turn θ) = d) ↔
      d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 := by
  constructor
  · rintro ⟨θ, h, rfl⟩
    exact crystallographic_restriction h
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, whole_turn_holds, orderOf_whole_turn⟩, ⟨π, half_turn_holds, orderOf_half_turn⟩,
      ⟨2 * π / 3, third_turn_holds, orderOf_third_turn⟩,
      ⟨π / 2, quarter_turn_holds, orderOf_quarter_turn⟩,
      ⟨π / 3, sixth_turn_holds, orderOf_sixth_turn⟩]

/-! ## 5. Niven's values -/

/-- [proved-standard; formal-checked] **Niven's values**: for rational `r`, a rational
`2 cos(rπ)` is one of `−2, −1, 0, 1, 2` (Mathlib's `niven`). -/
theorem niven_values (r : ℚ) (hq : ∃ q : ℚ, 2 * Real.cos (r * π) = q) :
    2 * Real.cos (r * π) ∈ ({-2, -1, 0, 1, 2} : Set ℝ) := by
  obtain ⟨q, hq⟩ := hq
  have h := niven (θ := r * π) ⟨r, rfl⟩ ⟨q / 2, by push_cast; linarith⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with h | h | h | h | h <;> rw [h] <;> norm_num

/-- [proved-standard; formal-checked] **`2 cos(rπ)` is rational exactly when `den r ≤ 3`.** One
direction is Mathlib's `irrational_cos_rat_mul_pi`; the other is the lattice: for `den r ≤ 3` the
turn by `rπ` is a power of the half, quarter or sixth turn, so its `2 cos` is an integer trace. -/
theorem two_cos_rat_iff (r : ℚ) : (∃ q : ℚ, 2 * Real.cos (r * π) = q) ↔ r.den ≤ 3 := by
  constructor
  · rintro ⟨q, hq⟩
    by_contra hden
    exact (irrational_cos_rat_mul_pi (not_le.mp hden)).ne_rat (q / 2) (by push_cast; linarith)
  · intro hden
    have hbase : HoldsLattice (turn (π / r.den)) := by
      have hd : r.den = 1 ∨ r.den = 2 ∨ r.den = 3 := by
        have := r.den_pos
        omega
      rcases hd with hd | hd | hd <;> rw [hd]
      · simpa using half_turn_holds
      · simpa using quarter_turn_holds
      · simpa using sixth_turn_holds
    have hθ := holds_pow hbase r.num.natAbs
    rw [turn_pow] at hθ
    obtain ⟨t, ht, -⟩ := two_cos_of_holds hθ
    have hcos : Real.cos ((r.num.natAbs : ℕ) * (π / r.den)) = Real.cos (r * π) := by
      rw [← Real.cos_abs ((r : ℝ) * π)]
      congr 1
      rw [abs_mul, abs_of_pos Real.pi_pos, Rat.cast_def, abs_div, Nat.abs_cast, Nat.cast_natAbs,
        Int.cast_abs]
      ring
    refine ⟨(t : ℚ), ?_⟩
    rw [← hcos, ht, Rat.cast_intCast]

/-- [proved-standard; formal-checked] **A turn by `rπ` with `den r > 3` holds no lattice.** -/
theorem no_lattice_of_den (r : ℚ) (hr : 3 < r.den) : ¬ HoldsLattice (turn (r * π)) := by
  intro h
  obtain ⟨t, ht, -⟩ := two_cos_of_holds h
  exact absurd ((two_cos_rat_iff r).mp ⟨(t : ℚ), by rw [ht, Rat.cast_intCast]⟩) (not_le.mpr hr)

/-- [proved-standard; formal-checked] **The fifth turn is the first refusal**: `2 cos(π/5) = φ`
(`Geometry/Turn`) lies strictly between 1 and 2, so the fifth turn holds no lattice. -/
theorem fifth_turn_holds_no_lattice : ¬ HoldsLattice (turn (π / 5)) := by
  intro h
  obtain ⟨t, ht, hv⟩ := two_cos_of_holds h
  rw [Turn.theGoldenRatioIsTwiceACosineOfTheFifthTurn] at ht
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hlo : 1 < Real.sqrt 5 := by nlinarith
  have hhi : Real.sqrt 5 < 3 := by nlinarith
  rcases hv with rfl | rfl | rfl | rfl | rfl <;> push_cast at ht <;> linarith

end Holonics.Geometry.Crystallographic
