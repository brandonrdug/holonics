import Mathlib

/-!
# The carry chain: its stationary law is Eulerian and its spectrum is `1, b⁻¹, …, b^(−(n−1))`

Source: the owed rest of #410's box "Association is evaluation, and a number is a word at a level of the base's tower
(#404)", from the record
`2026-10-23_ASSOCIATION_IS_EVALUATION_A_NUMBER_IS_A_WORD_OF_TURNING_DIGITS_AT_A_LEVEL_OF_THE_BASES_TOWER` §4
(atlas `radix.carry-chain-eulerian`; receipt `carries.py`): adding `n` numbers of uniform independent digits in base
`b`, the carry from place to place is a Markov chain on `{0, …, n − 1}` whose long-run law is the Eulerian numbers in
every base and whose relaxation is `1/b` per place. `Mathematics/LevelLaws` holds the two-summand propagate count and
`b^(−m)` for an unread carry (`card_propagate`, `unread_carry_prob`); this file proves the chain's law and spectrum.

The chain: carry `c` in and digits `d ∈ [0, b)ⁿ` give the carry `⌊(c + Σ d)/b⌋` out (`carryOut`); `N(i, j)` counts the
words that carry `i` to `j` (`count`), and `P(i, j) = N(i, j)/bⁿ` (`trans`). The Eulerian numbers are the record's
`A(n, j) = Σ_(r ≤ j) (−1)^r C(n + 1, r) (j + 1 − r)ⁿ` (`eulerian`).

[proved-derived; formal-checked] What is proved, for `n ≥ 1` summands and a base `b ≥ 1` (the record's `b ≥ 2` is not
needed).

1. **The chain** (`carryOut_lt`, `sum_count`, `trans_row_sum`): a carry `c < n` in leaves a carry `< n` out, and from
   every carry the counts sum to `bⁿ`, so `P` is stochastic on the carries `0, …, n − 1`. A function of the carry out
   summed against the counts is its sum over the words of digits (`sum_count_smul`).
2. **The box** (`box`, `iterate_box`, `fwdDiff_box`, `iterate_fwdDiff_box_of_le`): summing one digit over its `b`
   values is the box `Σ_(d<b) g(y + d h)`, `n` digits are `n` boxes, and a unit step across a box is the step over the
   whole box, `Δ_h ∘ box = Δ_(b h)`, so `k ≤ n` unit differences of `n` boxes are `n − k` boxes of `k` differences over
   the whole box. This one identity carries both results below: the chain is a box read through `⌊·/b⌋`, and `⌊·/b⌋`
   turns a step of `b` into a step of one (`iterate_fwdDiff_div`).
3. **The spectrum** (`countMat_mul_binMat`, `countMat_charpoly`, `trans_mul_binMatQ`, `trans_charpoly`): read in the
   binomial basis `C(c, k)` of the functions of the carry, the count matrix is upper triangular, `N V = V T` with
   `T(k, k) = b^(n−k)`, because `Δ^(k+1)` of the image of `C(·, k)` vanishes for `k < n` and `Δ^k` of it is `b^(n−k)`
   (`binImage_top`, `binImage_lead`, through Newton's formula, `newton`). So the characteristic polynomial of `N` is
   `Π_(k<n) (X − b^(n−k))` and that of `P` is `Π_(k<n) (X − b^(−k))`: the eigenvalues are `1, b⁻¹, …, b^(−(n−1))`.
   The basis does not depend on `b`.
4. **The stationary law** (`stationary_count`, `stationary_law`): `Σ_i A(n, i) N(i, j) = bⁿ A(n, j)` for every carry
   `j`, so `π_j = A(n, j)/n!` satisfies `π P = π`. The proof reads `A(n, ·)` as the `(n+1)`-st backward difference of
   `σ(x) = (x⁺)ⁿ` (`eul`, `eulerian_eq_eul`); the boxes of the chain, run backward, turn `n` of those differences into
   differences over the whole box (`iterate_box_eul`), the window of `b` values a carry out reads telescopes
   (`window_sum`), and `σ(b x) = bⁿ σ(x)` (`posPow_mul`, `iterate_negDiff_scale`) returns the factor `bⁿ`.
5. **The law is normalized and lives on the carries** (`sum_eulerian`, `eulerian_eq_zero_of_le`, `eul_eq_zero_of_neg`):
   `Σ_(j<n) A(n, j) = n!`, and `A(n, j) = 0` for `j ≥ n` (and the backward difference vanishes below `0`). The record's
   check: `A(3, ·) = 1, 4, 1` and `π = 1/6, 2/3, 1/6` (`eulerian_three`, `stationary_three`).
6. **The law is a probability law that charges every carry** (`eulerian_succ_succ`, `eulerian_nonneg`,
   `eulerian_pos`, `stationary_prob`, `stationary_pos`): Leibniz's rule for the backward difference of `y f(y)`
   (`iterate_negDiff_mul_self`) and `σ_(n+1)(x) = x σ_n(x)` (`posPow_succ`) give the recurrence
   `a_(n+1)(t) = (t + 1) a_n(t) + (n + 1 − t) a_n(t − 1)` on ℤ (`eul_succ`), so
   `A(n + 1, j + 1) = (j + 2) A(n, j + 1) + (n − j) A(n, j)` with `A(n, 0) = 1` (`eulerian_zero_right`). The
   coefficient `n − j` is negative only where `A(n, j) = 0` (`eulerian_eq_zero_of_lt`), so by induction `A(n, j) ≥ 0`
   for every `n` and `j`, and `A(n, j) > 0` for `j < n`: `π` is nonnegative, sums to `1` and is positive on every
   carry.

The computational object is the helical pair interaction's carry: each place is a pair contact between the summands'
digits, and the carry it passes on is the remainder held across the contact, its uncertainty shrinking by `b` a place.
Of the winding guide's six general objects this touches the helix (the carry as the winding's whole part) and the
tower thread (the carry passed from place to place); the pair, faces and placement, the cell holonomy and the tube
stay attached.

What stands beside it: `Mathematics/LevelLaws` (`card_propagate`, `card_unread_carry`, `unread_carry_prob`) and the
adder's bracketing (atlas `radix.adder-bracketing`). Left out: the reading of `A(n, j)` as the count of permutations
of `n` with `j` descents, the reading of the chain as the descents of a `b`-riffle shuffle, the right and left
eigenvectors beyond the triangular basis, and the convergence `Pᵐ → π` that the spectrum gives for `b ≥ 2`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.CarryChainEulerian

open Finset Function fwdDiff Matrix Polynomial

/-! ## 0. The box of one digit and its differences -/

section Box

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G]

/-- [definition] The box of `b` steps of length `h`, `(box b h g)(y) = Σ_(d<b) g(y + d • h)`: one digit summed over its
`b` values. -/
def box (b : ℕ) (h : M) (g : M → G) : M → G := fun y => ∑ d ∈ range b, g (y + d • h)

/-- A step across the box is the difference over the whole box: `Δ_h (box g) = Δ_(b h) g`. -/
theorem fwdDiff_box (b : ℕ) (h : M) (g : M → G) : Δ_[h] (box b h g) = Δ_[b • h] g := by
  funext y
  simp only [fwdDiff, box, ← Finset.sum_sub_distrib]
  have : ∀ d : ℕ, g (y + h + d • h) = g (y + (d + 1) • h) := fun d => by
    rw [succ_nsmul]; congr 1; abel
  simp only [this]
  rw [Finset.sum_range_sub (fun d => g (y + d • h)) b, zero_smul, add_zero]

/-- A difference of any step passes through the box. -/
theorem fwdDiff_comm_box (b : ℕ) (h h' : M) (g : M → G) : Δ_[h'] (box b h g) = box b h (Δ_[h'] g) := by
  funext y
  simp only [fwdDiff, box, ← Finset.sum_sub_distrib, add_right_comm y h']

theorem commute_fwdDiff_box (b : ℕ) (h h' : M) :
    Function.Commute (fwdDiff h' : (M → G) → M → G) (box b h) := fun g => fwdDiff_comm_box b h h' g

theorem commute_fwdDiff (h h' : M) :
    Function.Commute (fwdDiff h' : (M → G) → M → G) (fwdDiff h) := fun g => by
  funext y
  simp only [fwdDiff, add_right_comm y h' h]
  abel

theorem iterate_box_const (b k : ℕ) (h : M) (c : G) :
    (box b h)^[k] (fun _ => c) = fun _ => (b ^ k) • c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih]
    funext y
    simp [box, smul_smul, pow_succ']

/-- The iterated box is the sum over the words of `n` digits. -/
theorem iterate_box (b n : ℕ) (h : M) (g : M → G) (y : M) :
    (box b h)^[n] g y = ∑ d : Fin n → Fin b, g (y + (∑ k, (d k : ℕ)) • h) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', box]
    simp only [ih]
    rw [← Fin.sum_univ_eq_sum_range (fun x => ∑ d : Fin n → Fin b, g (y + x • h + (∑ k, (d k : ℕ)) • h)),
      ← (Fin.consEquiv fun _ : Fin (n + 1) => Fin b).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_smul]
    congr 1
    abel

/-- `n` differences of `n` boxes are `n` differences over the whole box. -/
theorem iterate_fwdDiff_box (b k : ℕ) (h : M) (g : M → G) :
    (Δ_[h])^[k] ((box b h)^[k] g) = (Δ_[b • h])^[k] g := by
  have hc := commute_fwdDiff_box (G := G) b h h
  have hcomp : fwdDiff h ∘ box b h = (fwdDiff (b • h) : (M → G) → M → G) := funext (fwdDiff_box b h)
  rw [← Function.comp_apply (f := (fwdDiff h)^[k]), ← hc.comp_iterate, hcomp]

/-- The same, read with the boxes outside. -/
theorem iterate_box_fwdDiff (b k : ℕ) (h : M) (g : M → G) :
    (box b h)^[k] ((Δ_[h])^[k] g) = (Δ_[b • h])^[k] g := by
  rw [← ((commute_fwdDiff_box (G := G) b h h).iterate_iterate k k) g, iterate_fwdDiff_box]

/-- With more boxes than differences: `Δ_h^k (boxⁿ g) = box^(n−k) (Δ_(b h)^k g)`. -/
theorem iterate_fwdDiff_box_of_le (b : ℕ) {k n : ℕ} (hk : k ≤ n) (h : M) (g : M → G) :
    (Δ_[h])^[k] ((box b h)^[n] g) = (box b h)^[n - k] ((Δ_[b • h])^[k] g) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, add_comm, Function.iterate_add_apply,
    ((commute_fwdDiff_box (G := G) b h h).iterate_iterate k m) _, iterate_fwdDiff_box]

end Box

/-! ## 1. The chain -/

section Chain

variable {n b : ℕ}

/-- [definition] The carry out of one place: carry `c` in and digits `d`, out `⌊(c + Σ d)/b⌋`. -/
def carryOut (b c : ℕ) {n : ℕ} (d : Fin n → Fin b) : ℕ := (c + ∑ k, (d k : ℕ)) / b

/-- [definition] The count `N(i, j)` of the words of `n` digits that carry `i` in to `j` out. -/
def count (n b i j : ℕ) : ℕ := #{d : Fin n → Fin b | carryOut b i d = j}

/-- [definition] The transition matrix of the carry chain, `P(i, j) = N(i, j)/bⁿ`, on the carries `0, …, n − 1`. -/
noncomputable def trans (n b : ℕ) : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => (count n b i j : ℚ) / b ^ n

/-- **The carry stays below the count of summands**: a carry `c < n` in leaves a carry `< n` out. -/
theorem carryOut_lt (hb : 0 < b) {c : ℕ} (hc : c < n) (d : Fin n → Fin b) : carryOut b c d < n := by
  have hs : ∑ k, (d k : ℕ) ≤ n * (b - 1) := by
    calc ∑ k, (d k : ℕ) ≤ ∑ _k : Fin n, (b - 1) := Finset.sum_le_sum fun k _ => by have := (d k).isLt; omega
      _ = n * (b - 1) := by simp
  have hnb : n * (b - 1) + n = n * b := by
    rcases b with _ | b
    · omega
    · simp [Nat.mul_succ]
  rw [carryOut, Nat.div_lt_iff_lt_mul hb]
  omega

/-- A function of the carry out, summed against the counts, is its sum over the words. -/
theorem sum_count_smul {R : Type*} [AddCommMonoid R] (hb : 0 < b) {i : ℕ} (hi : i < n) (f : ℕ → R) :
    ∑ j ∈ range n, count n b i j • f j = ∑ d : Fin n → Fin b, f (carryOut b i d) := by
  rw [← Finset.sum_fiberwise_of_maps_to' (s := univ) (t := range n) (g := fun d => carryOut b i d)
    (fun d _ => Finset.mem_range.2 (carryOut_lt hb hi d)) f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, count]

/-- **The chain is stochastic**: from every carry the counts sum to `bⁿ`. -/
theorem sum_count (hb : 0 < b) {i : ℕ} (hi : i < n) : ∑ j ∈ range n, count n b i j = b ^ n := by
  have := sum_count_smul hb hi (fun _ => (1 : ℕ))
  simp only [smul_eq_mul, mul_one] at this
  rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    smul_eq_mul, mul_one]

theorem trans_row_sum (hb : 0 < b) (i : Fin n) : ∑ j, trans n b i j = 1 := by
  have hb' : (b : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hb.ne')
  simp only [trans, Matrix.of_apply, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun j => (count n b i j : ℚ)), ← Nat.cast_sum, sum_count hb i.isLt]
  push_cast
  exact div_self hb'

end Chain

/-! ## 2. The spectrum -/

section Spectrum

variable {n b : ℕ}

/-- [definition] The binomial read of the carry out, `y ↦ C(⌊y/b⌋, k)`. -/
def binRead (b k : ℕ) : ℕ → ℤ := fun y => ((y / b).choose k : ℤ)

/-- [definition] `g_k = boxⁿ (binRead k)`: the count matrix applied to the binomial `C(·, k)` of the carry. -/
def binImage (n b k : ℕ) : ℕ → ℤ := (box b (1 : ℕ))^[n] (binRead b k)

theorem binImage_apply (i : ℕ) : binImage n b k i = ∑ d : Fin n → Fin b, ((carryOut b i d).choose k : ℤ) := by
  rw [binImage, iterate_box]
  simp [binRead, carryOut]

/-- A difference over the whole box of a read through `⌊·/b⌋` is a unit difference of the read. -/
theorem iterate_fwdDiff_div (hb : 0 < b) (m : ℕ) (q : ℕ → ℤ) (y : ℕ) :
    (Δ_[b])^[m] (fun y => q (y / b)) y = (Δ_[1])^[m] q (y / b) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [smul_eq_mul, mul_one, Nat.add_mul_div_right _ _ hb]

theorem iterate_fwdDiff_choose_self (k : ℕ) : (Δ_[1])^[k] (fun x : ℕ => (x.choose k : ℤ)) = fun _ => 1 := by
  simpa using fwdDiff_iter_choose 0 k

theorem iterate_fwdDiff_choose_succ (k : ℕ) :
    (Δ_[1])^[k + 1] (fun x : ℕ => (x.choose k : ℤ)) = 0 := by
  rw [iterate_succ_apply', iterate_fwdDiff_choose_self, fwdDiff_const]
  rfl

theorem iterate_fwdDiff_zero {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M) (m : ℕ) :
    (Δ_[h])^[m] (0 : M → G) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [iterate_succ_apply', ih]; funext y; simp [fwdDiff]

/-- **The top difference vanishes**: `Δ^(k+1) g_k = 0` for `k < n`, so `g_k` is a polynomial of degree `≤ k`. -/
theorem binImage_top (hb : 0 < b) {k : ℕ} (hk : k < n) : (Δ_[1])^[k + 1] (binImage n b k) = 0 := by
  rw [binImage, iterate_fwdDiff_box_of_le b hk]
  have : (Δ_[b • (1 : ℕ)])^[k + 1] (binRead b k) = 0 := by
    funext y
    rw [smul_eq_mul, mul_one]
    have := iterate_fwdDiff_div hb (k + 1) (fun x : ℕ => (x.choose k : ℤ)) y
    rw [iterate_fwdDiff_choose_succ] at this
    exact this
  rw [this]
  have h0 := iterate_box_const (G := ℤ) b (n - (k + 1)) (1 : ℕ) 0
  simp only [smul_zero] at h0
  exact h0

/-- **The leading difference**: `Δ^k g_k = b^(n−k)`, the leading coefficient in the binomial basis. -/
theorem binImage_lead (hb : 0 < b) {k : ℕ} (hk : k ≤ n) :
    (Δ_[1])^[k] (binImage n b k) = fun _ => (b : ℤ) ^ (n - k) := by
  rw [binImage, iterate_fwdDiff_box_of_le b hk]
  have : (Δ_[b • (1 : ℕ)])^[k] (binRead b k) = fun _ => 1 := by
    funext y
    rw [smul_eq_mul, mul_one]
    have := iterate_fwdDiff_div hb k (fun x : ℕ => (x.choose k : ℤ)) y
    rw [iterate_fwdDiff_choose_self] at this
    exact this
  rw [this, iterate_box_const]
  funext y
  simp

/-- **Newton's formula** for a function whose `(k+1)`-st difference vanishes. -/
theorem newton {g : ℕ → ℤ} {k : ℕ} (hg : (Δ_[1])^[k + 1] g = 0) (y : ℕ) :
    g y = ∑ l ∈ range (k + 1), (y.choose l : ℤ) * (Δ_[1])^[l] g 0 := by
  have hN := shift_eq_sum_fwdDiff_iter (1 : ℕ) g y 0
  rw [smul_eq_mul, mul_one, zero_add] at hN
  rw [hN]
  have hz : ∀ l, k + 1 ≤ l → (Δ_[1])^[l] g 0 = 0 := fun l hl => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hl
    rw [add_comm, Function.iterate_add_apply, hg, iterate_fwdDiff_zero]
    rfl
  have h1 : ∑ l ∈ range (y + 1), y.choose l • (Δ_[1])^[l] g 0 =
      ∑ l ∈ range (y + k + 2), (y.choose l : ℤ) * (Δ_[1])^[l] g 0 := by
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : y + 1 ≤ y + k + 2))]
    · exact Finset.sum_congr rfl fun l _ => nsmul_eq_mul _ _
    · intro l hl hl'
      simp only [Finset.mem_range] at hl hl'
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have h2 : ∑ l ∈ range (k + 1), (y.choose l : ℤ) * (Δ_[1])^[l] g 0 =
      ∑ l ∈ range (y + k + 2), (y.choose l : ℤ) * (Δ_[1])^[l] g 0 := by
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : k + 1 ≤ y + k + 2))]
    intro l hl hl'
    simp only [Finset.mem_range] at hl hl'
    rw [hz l (by omega), mul_zero]
  rw [h1, h2]

/-- [definition] The count matrix `N` over ℤ, on the carries `0, …, n − 1`. -/
def countMat (n b : ℕ) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (count n b i j : ℤ)

/-- [definition] The binomial basis `V(i, k) = C(i, k)` of the functions of the carry. -/
def binMat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i k => ((i : ℕ).choose k : ℤ)

/-- [definition] The count matrix read in the binomial basis: `T(l, k) = Δ^l g_k (0)` for `l ≤ k`. -/
def triMat (n b : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun l k => if l ≤ k then (Δ_[1])^[l] (binImage n b k) 0 else 0

theorem binMat_lower (n : ℕ) : (binMat n).IsLowerTriangular := fun i k hik => by
  simp only [binMat, Matrix.of_apply]
  rw [Nat.choose_eq_zero_of_lt (show (i : ℕ) < k from hik), Nat.cast_zero]

theorem binMat_det (n : ℕ) : (binMat n).det = 1 := by
  rw [det_of_isLowerTriangular _ (binMat_lower n)]
  simp [binMat]

theorem triMat_upper (n b : ℕ) : (triMat n b).IsUpperTriangular := fun l k hkl => by
  simp only [triMat, Matrix.of_apply, id] at hkl ⊢
  exact if_neg (not_le.2 hkl)

theorem triMat_diag (hb : 0 < b) (k : Fin n) : triMat n b k k = (b : ℤ) ^ (n - k) := by
  simp only [triMat, Matrix.of_apply, le_refl, if_true]
  rw [binImage_lead hb k.isLt.le]

/-- **The count matrix is triangular in the binomial basis**: `N V = V T`, with `T` upper triangular. -/
theorem countMat_mul_binMat (hb : 0 < b) : countMat n b * binMat n = binMat n * triMat n b := by
  ext i k
  simp only [Matrix.mul_apply, countMat, binMat, triMat, Matrix.of_apply]
  have hL : ∑ j : Fin n, (count n b i j : ℤ) * ((j : ℕ).choose k : ℤ) = binImage n b k i := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (count n b i j : ℤ) * ((j.choose k : ℕ) : ℤ)), binImage_apply]
    have := sum_count_smul (R := ℤ) hb i.isLt (fun j => (j.choose k : ℤ))
    simpa [nsmul_eq_mul] using this
  rw [hL, newton (binImage_top hb k.isLt) i]
  simp_rw [Fin.le_iff_val_le_val]
  rw [Fin.sum_univ_eq_sum_range (fun l => ((i : ℕ).choose l : ℤ) *
    (if l ≤ (k : ℕ) then (Δ_[1])^[l] (binImage n b k) 0 else 0))]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_range]
  have := k.isLt
  omega

/-- **The spectrum of the count matrix**: its characteristic polynomial is `Π_(k<n) (X − b^(n−k))`. -/
theorem countMat_charpoly (hb : 0 < b) :
    (countMat n b).charpoly = ∏ k : Fin n, (X - C ((b : ℤ) ^ (n - k))) := by
  have hu : IsUnit (binMat n).det := by rw [binMat_det]; exact isUnit_one
  set U := nonsingInvUnit (binMat n) hu
  have hconj : countMat n b = U.val * triMat n b * U.val⁻¹ := by
    have hU : U.val = binMat n := rfl
    rw [hU, ← countMat_mul_binMat hb, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
  rw [hconj, charpoly_units_conj, charpoly_of_isUpperTriangular _ (triMat_upper n b)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [triMat_diag hb]

/-- [definition] The binomial basis over ℚ. -/
def binMatQ (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := (binMat n).map (Int.castRingHom ℚ)

/-- [definition] The transition matrix read in the binomial basis, `b^(−n) T`. -/
noncomputable def triMatQ (n b : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  ((b : ℚ) ^ n)⁻¹ • (triMat n b).map (Int.castRingHom ℚ)

theorem trans_eq_smul : trans n b = ((b : ℚ) ^ n)⁻¹ • (countMat n b).map (Int.castRingHom ℚ) := by
  ext i j
  simp [trans, countMat, div_eq_inv_mul]

/-- **The transition matrix is triangular in the binomial basis**: `P V = V (b^(−n) T)`. -/
theorem trans_mul_binMatQ (hb : 0 < b) : trans n b * binMatQ n = binMatQ n * triMatQ n b := by
  rw [trans_eq_smul, binMatQ, triMatQ, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul,
    countMat_mul_binMat hb]

/-- **The spectrum of the carry chain**: the characteristic polynomial of `P` is `Π_(k<n) (X − b^(−k))`, so its
eigenvalues are `1, b⁻¹, …, b^(−(n−1))`. -/
theorem trans_charpoly (hb : 0 < b) :
    (trans n b).charpoly = ∏ k : Fin n, (X - C (((b : ℚ) ^ (k : ℕ))⁻¹)) := by
  have hdet : (binMatQ n).det = 1 := by
    rw [binMatQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det, binMat_det, map_one]
  have hu : IsUnit (binMatQ n).det := by rw [hdet]; exact isUnit_one
  set U := nonsingInvUnit (binMatQ n) hu
  have hconj : trans n b = U.val * triMatQ n b * U.val⁻¹ := by
    have hU : U.val = binMatQ n := rfl
    rw [hU, ← trans_mul_binMatQ hb, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
  have hup : (triMatQ n b).IsUpperTriangular := fun l k hkl => by
    simp [triMatQ, triMat_upper n b hkl]
  rw [hconj, charpoly_units_conj, charpoly_of_isUpperTriangular _ hup]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [triMatQ, Matrix.smul_apply, Matrix.map_apply, triMat_diag hb, smul_eq_mul, eq_intCast, Int.cast_pow,
    Int.cast_natCast]
  congr 2
  have hk : (b : ℚ) ^ n = (b : ℚ) ^ (n - (k : ℕ)) * (b : ℚ) ^ (k : ℕ) := by
    rw [← pow_add, Nat.sub_add_cancel k.isLt.le]
  rw [hk]
  field_simp

end Spectrum

/-! ## 3. The stationary law -/

section Stationary

variable {n b : ℕ}

/-- [definition] The Eulerian numbers, `A(n, j) = Σ_(r ≤ j) (−1)^r C(n + 1, r) (j + 1 − r)ⁿ`. -/
def eulerian (n j : ℕ) : ℤ :=
  ∑ r ∈ range (j + 1), (-1) ^ r * ((n + 1).choose r : ℤ) * ((j + 1 - r : ℕ) : ℤ) ^ n

theorem eulerian_three : eulerian 3 0 = 1 ∧ eulerian 3 1 = 4 ∧ eulerian 3 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [eulerian, Finset.sum_range_succ, Nat.choose]

/-- [definition] The power of the positive part, `σ(x) = (x⁺)ⁿ` on ℤ. -/
def posPow (n : ℕ) : ℤ → ℤ := fun x => (x.toNat : ℤ) ^ n

/-- [definition] The Eulerian numbers read on all of ℤ as the `(n+1)`-st backward difference of `σ`:
`a(t) = (−1)^(n+1) Δ_(−1)^(n+1) σ (t + 1)`. -/
def eul (n : ℕ) : ℤ → ℤ := fun t => (-1) ^ (n + 1) * (Δ_[(-1 : ℤ)])^[n + 1] (posPow n) (t + 1)

theorem posPow_of_nonneg {x : ℤ} (hx : 0 ≤ x) : posPow n x = x ^ n := by
  rw [posPow, Int.toNat_of_nonneg hx]

theorem posPow_of_nonpos (hn : 1 ≤ n) {x : ℤ} (hx : x ≤ 0) : posPow n x = 0 := by
  rw [posPow, Int.toNat_eq_zero.2 hx, Nat.cast_zero, zero_pow (by omega)]

theorem posPow_mul (c : ℕ) (x : ℤ) : posPow n ((c : ℤ) * x) = (c : ℤ) ^ n * posPow n x := by
  have : ((c : ℤ) * x).toNat = c * x.toNat := by
    rcases le_or_gt 0 x with hx | hx
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hx
      rw [← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
    · rw [Int.toNat_eq_zero.2 (by nlinarith [(Nat.cast_nonneg c : (0 : ℤ) ≤ c)]), Int.toNat_eq_zero.2 hx.le,
        mul_zero]
  rw [posPow, posPow, this, Nat.cast_mul, mul_pow]

/-- The backward difference expanded: `Δ_(−1)^k f (y) = Σ_r (−1)^(k−r) C(k, r) f(y − r)`. -/
theorem iterate_negDiff (f : ℤ → ℤ) (k : ℕ) (y : ℤ) :
    (Δ_[(-1 : ℤ)])^[k] f y = ∑ r ∈ range (k + 1), (-1) ^ (k - r) * (k.choose r : ℤ) * f (y - r) := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_eq_mul, nsmul_eq_mul, mul_neg_one, ← sub_eq_add_neg]

/-- A backward difference is a forward difference of the reflection. -/
theorem iterate_negDiff_reflect (f : ℤ → ℤ) (k : ℕ) (x : ℤ) :
    (Δ_[(-1 : ℤ)])^[k] f x = (Δ_[(1 : ℤ)])^[k] (fun y => f (-y)) (-x) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 2
  simp only [nsmul_eq_mul, mul_neg_one, mul_one]
  ring

/-- The backward differences of a power. -/
theorem iterate_negDiff_pow (k m : ℕ) (x : ℤ) :
    (Δ_[(-1 : ℤ)])^[k] (fun y : ℤ => y ^ m) x = (-1) ^ m * (Δ_[(1 : ℤ)])^[k] (fun y : ℤ => y ^ m) (-x) := by
  rw [iterate_negDiff_reflect]
  have : (fun y : ℤ => (-y) ^ m) = ((-1 : ℤ) ^ m) • (fun y : ℤ => y ^ m) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    exact neg_pow y m
  rw [this, fwdDiff_iter_const_smul]
  rfl

/-- Two functions equal on `x − k, …, x` have the same `k`-th backward difference at `x`. -/
theorem iterate_negDiff_congr {f g : ℤ → ℤ} {k : ℕ} {x : ℤ} (h : ∀ r ≤ k, f (x - r) = g (x - r)) :
    (Δ_[(-1 : ℤ)])^[k] f x = (Δ_[(-1 : ℤ)])^[k] g x := by
  rw [iterate_negDiff, iterate_negDiff]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [h r (by simp only [Finset.mem_range] at hr; omega)]

theorem neg_one_pow_mul_sub {k r : ℕ} (hr : r ≤ k) : ((-1 : ℤ)) ^ k * (-1) ^ (k - r) = (-1) ^ r := by
  rw [← pow_add]
  have : k + (k - r) = r + 2 * (k - r) := by omega
  rw [this, pow_add, pow_mul]
  norm_num

theorem eul_eq_sum (t : ℤ) :
    eul n t = ∑ r ∈ range (n + 2), (-1) ^ r * ((n + 1).choose r : ℤ) * posPow n (t + 1 - r) := by
  rw [eul, iterate_negDiff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp only [Finset.mem_range] at hr
  rw [← mul_assoc, ← mul_assoc, neg_one_pow_mul_sub (by omega)]

/-- **The explicit Eulerian numbers are the backward difference**: `A(n, j) = a(j)`. -/
theorem eulerian_eq_eul (hn : 1 ≤ n) (j : ℕ) : eulerian n j = eul n j := by
  rw [eul_eq_sum, eulerian]
  have hp : ∀ r : ℕ, posPow n ((j : ℤ) + 1 - r) = ((j + 1 - r : ℕ) : ℤ) ^ n := fun r => by
    rw [posPow]
    congr 2
    omega
  simp only [hp]
  set F : ℕ → ℤ := fun r => (-1) ^ r * ((n + 1).choose r : ℤ) * ((j + 1 - r : ℕ) : ℤ) ^ n
  have h1 : ∑ r ∈ range (j + 1), F r = ∑ r ∈ range (n + j + 2), F r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    simp only [Finset.mem_range] at hr hr'
    simp only [F, show j + 1 - r = 0 by omega, Nat.cast_zero, zero_pow (show n ≠ 0 by omega), mul_zero]
  have h2 : ∑ r ∈ range (n + 2), F r = ∑ r ∈ range (n + j + 2), F r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    simp only [Finset.mem_range] at hr hr'
    simp only [F, Nat.choose_eq_zero_of_lt (show n + 1 < r by omega), Nat.cast_zero, mul_zero, zero_mul]
  exact h1.trans h2.symm

theorem eul_eq_zero_of_neg (hn : 1 ≤ n) {t : ℤ} (ht : t < 0) : eul n t = 0 := by
  rw [eul_eq_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [posPow_of_nonpos hn (by omega), mul_zero]

/-- **The Eulerian numbers vanish from `n` on**: the stationary law lives on the carries `0, …, n − 1`. -/
theorem eul_eq_zero_of_ge {t : ℤ} (ht : (n : ℤ) ≤ t) : eul n t = 0 := by
  have hc : (Δ_[(-1 : ℤ)])^[n + 1] (posPow n) (t + 1) = (Δ_[(-1 : ℤ)])^[n + 1] (fun y : ℤ => y ^ n) (t + 1) :=
    iterate_negDiff_congr fun r hr => posPow_of_nonneg (by omega)
  rw [eul, hc, iterate_negDiff_pow, fwdDiff_iter_pow_eq_zero_of_lt (by omega)]
  simp

theorem eulerian_eq_zero_of_le (hn : 1 ≤ n) {j : ℕ} (hj : n ≤ j) : eulerian n j = 0 := by
  rw [eulerian_eq_eul hn]
  exact eul_eq_zero_of_ge (by exact_mod_cast hj)

/-- An integer reads its Eulerian number from the carries `0, …, n − 1`. -/
theorem eul_eq_sum_ite (hn : 1 ≤ n) (t : ℤ) :
    eul n t = ∑ i ∈ range n, if (i : ℤ) = t then eul n i else 0 := by
  by_cases h : 0 ≤ t ∧ t < n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
    simp only [Nat.cast_inj]
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_range.2 (by exact_mod_cast h.2))]
  · rw [Finset.sum_eq_zero fun i hi => if_neg fun hit => h ⟨by omega, by simp only [Finset.mem_range] at hi; omega⟩]
    rcases not_and_or.1 h with h' | h'
    · exact eul_eq_zero_of_neg hn (by omega)
    · exact eul_eq_zero_of_ge (by omega)

theorem div_eq_iff_mem (hb : 0 < b) (x j : ℕ) : x / b = j ↔ x ∈ Ico (j * b) ((j + 1) * b) := by
  rw [Finset.mem_Ico, ← Nat.le_div_iff_mul_le hb, ← Nat.div_lt_iff_lt_mul hb]
  omega

/-- One word of digits, read against the Eulerian numbers, is a window of `b` values. -/
theorem window_sum (hn : 1 ≤ n) (hb : 0 < b) (j S : ℕ) :
    ∑ i ∈ range n, (if (i + S) / b = j then eul n i else 0) =
      ∑ y ∈ Ico (j * b) ((j + 1) * b), eul n ((y : ℤ) - S) := by
  simp only [fun y : ℕ => eul_eq_sum_ite hn ((y : ℤ) - S)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : ∀ y : ℕ, ((i : ℤ) = (y : ℤ) - S) ↔ (i + S = y) := fun y => by omega
  simp only [hc]
  rw [Finset.sum_ite_eq]
  exact if_congr (div_eq_iff_mem hb _ _) rfl rfl

/-- The Eulerian numbers summed over the box of `b` steps back is a backward difference. -/
theorem iterate_box_eul (b : ℕ) (z : ℤ) :
    (box b (-1 : ℤ))^[n] (eul n) z =
      (-1) ^ (n + 1) * ((Δ_[b • (-1 : ℤ)])^[n] (posPow n) z - (Δ_[b • (-1 : ℤ)])^[n] (posPow n) (z + 1)) := by
  have h1 : (box b (-1 : ℤ))^[n] (eul n) z =
      (-1) ^ (n + 1) * (box b (-1 : ℤ))^[n] ((Δ_[(-1 : ℤ)])^[n + 1] (posPow n)) (z + 1) := by
    rw [iterate_box, iterate_box, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eul, add_right_comm]
  rw [h1, iterate_succ_apply, iterate_box_fwdDiff,
    ((commute_fwdDiff (G := ℤ) (-1 : ℤ) (b • (-1 : ℤ))).iterate_left n) (posPow n)]
  simp only [fwdDiff]
  rw [add_neg_cancel_right]

/-- A difference over the whole box, read at a multiple of `b`, is a unit difference of the scaled read. -/
theorem iterate_negDiff_scale (b k : ℕ) (f : ℤ → ℤ) (x : ℤ) :
    (Δ_[b • (-1 : ℤ)])^[k] f ((b : ℤ) * x) = (Δ_[(-1 : ℤ)])^[k] (fun y => f ((b : ℤ) * y)) x := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 2
  simp only [nsmul_eq_mul]
  ring

/-- **The stationary law**: `Σ_i A(n, i) N(i, j) = bⁿ A(n, j)` for every carry out `j`. -/
theorem stationary_count (hn : 1 ≤ n) (hb : 0 < b) (j : ℕ) :
    ∑ i ∈ range n, eulerian n i * count n b i j = (b : ℤ) ^ n * eulerian n j := by
  simp only [eulerian_eq_eul hn]
  simp only [count, Finset.natCast_card_filter, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  have hw : ∀ d : Fin n → Fin b, ∑ i ∈ range n, (if carryOut b i d = j then eul n i else 0) =
      ∑ y ∈ Ico (j * b) ((j + 1) * b), eul n ((y : ℤ) - ((∑ k, (d k : ℕ) : ℕ) : ℤ)) := fun d =>
    window_sum hn hb j _
  simp only [hw]
  rw [Finset.sum_comm]
  have hbox : ∀ y : ℕ, ∑ d : Fin n → Fin b, eul n ((y : ℤ) - ((∑ k, (d k : ℕ) : ℕ) : ℤ)) =
      (box b (-1 : ℤ))^[n] (eul n) y := fun y => by
    rw [iterate_box]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [nsmul_eq_mul, mul_neg_one, ← sub_eq_add_neg]
  simp only [hbox, iterate_box_eul]
  rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
  set G : ℤ → ℤ := (Δ_[b • (-1 : ℤ)])^[n] (posPow n)
  have htel := Finset.sum_range_sub' (fun k : ℕ => G ((j * b + k : ℕ) : ℤ)) ((j + 1) * b - j * b)
  have hcast : ∀ k : ℕ, G (((j * b + k : ℕ) : ℤ) + 1) = G ((j * b + (k + 1) : ℕ) : ℤ) := fun k => by
    push_cast; ring_nf
  simp only [hcast]
  rw [htel]
  have hw : j * b + ((j + 1) * b - j * b) = (j + 1) * b := by
    have : j * b ≤ (j + 1) * b := Nat.mul_le_mul_right b (Nat.le_succ j)
    omega
  rw [hw, add_zero]
  have hscale : ∀ x : ℤ, G ((b : ℤ) * x) = (b : ℤ) ^ n * (Δ_[(-1 : ℤ)])^[n] (posPow n) x := fun x => by
    simp only [G, iterate_negDiff_scale, posPow_mul]
    have : (fun y => (b : ℤ) ^ n * posPow n y) = ((b : ℤ) ^ n) • posPow n := rfl
    rw [this, fwdDiff_iter_const_smul]
    rfl
  have e1 : (((j * b : ℕ)) : ℤ) = (b : ℤ) * j := by push_cast; ring
  have e2 : ((((j + 1) * b : ℕ)) : ℤ) = (b : ℤ) * (j + 1) := by push_cast; ring
  rw [e1, e2, hscale, hscale, eul, iterate_succ_apply']
  simp only [fwdDiff]
  rw [add_neg_cancel_right]
  ring

/-- **The stationary law of the carry chain**: `π_j = A(n, j)/n!` is fixed by `P`, `π P = π`. -/
theorem stationary_law (hn : 1 ≤ n) (hb : 0 < b) :
    (fun i : Fin n => (eulerian n i : ℚ) / n.factorial) ᵥ* trans n b =
      fun j : Fin n => (eulerian n j : ℚ) / n.factorial := by
  funext j
  have key : ∑ i ∈ range n, (eulerian n i : ℚ) * count n b i j = (b : ℚ) ^ n * eulerian n j := by
    exact_mod_cast stationary_count hn hb j
  have hb' : (b : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hb.ne')
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  simp only [vecMul, dotProduct, trans, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun i => (eulerian n i : ℚ) / n.factorial * ((count n b i j : ℚ) / b ^ n))]
  calc ∑ i ∈ range n, (eulerian n i : ℚ) / n.factorial * ((count n b i j : ℚ) / b ^ n)
      = (∑ i ∈ range n, (eulerian n i : ℚ) * count n b i j) / (n.factorial * b ^ n) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
    _ = (eulerian n j : ℚ) / n.factorial := by
        rw [key]
        field_simp

/-- **The Eulerian numbers sum to `n!`**, so `π` is normalized. -/
theorem sum_eulerian (hn : 1 ≤ n) : ∑ j ∈ range n, eulerian n j = n.factorial := by
  set F : ℤ → ℤ := (Δ_[(-1 : ℤ)])^[n] (posPow n)
  have he : ∀ j : ℕ, eulerian n j = (-1) ^ (n + 1) * (F j - F (j + 1)) := fun j => by
    rw [eulerian_eq_eul hn, eul, iterate_succ_apply']
    simp only [fwdDiff, F]
    rw [add_neg_cancel_right]
  simp only [he, ← Finset.mul_sum]
  have htel := Finset.sum_range_sub' (fun k : ℕ => F k) n
  simp only [Nat.cast_add, Nat.cast_one] at htel
  rw [htel]
  have h0 : F 0 = 0 := by
    simp only [F, iterate_negDiff]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [posPow_of_nonpos hn (by omega), mul_zero]
  have hN : F n = (-1) ^ n * n.factorial := by
    have hc : F n = (Δ_[(-1 : ℤ)])^[n] (fun y : ℤ => y ^ n) n :=
      iterate_negDiff_congr fun r hr => posPow_of_nonneg (by omega)
    rw [hc, iterate_negDiff_pow, fwdDiff_iter_eq_factorial]
    simp
  rw [Nat.cast_zero, h0, hN]
  have hsq : ((-1 : ℤ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [pow_succ]
  linear_combination (n.factorial : ℤ) * hsq

/-- At the carry `0` the law reads `A(n, 0) = 1`. -/
theorem eulerian_zero_right (n : ℕ) : eulerian n 0 = 1 := by
  simp [eulerian]

/-- With no summand the law sits on the carry `0`: `A(0, j + 1) = 0`. -/
theorem eulerian_zero_succ (j : ℕ) : eulerian 0 (j + 1) = 0 := by
  rw [eulerian, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [Finset.sum_eq_zero fun r _ => by rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]]
  norm_num

/-- The law lives on the carries below `n`, for every `n`: `A(n, j) = 0` for `j > n`. -/
theorem eulerian_eq_zero_of_lt {n j : ℕ} (hj : n < j) : eulerian n j = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    exact eulerian_zero_succ j
  · exact eulerian_eq_zero_of_le hn hj.le

theorem posPow_succ (hn : 1 ≤ n) (x : ℤ) : posPow (n + 1) x = x * posPow n x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [posPow_of_nonneg hx, posPow_of_nonneg hx, pow_succ, mul_comm]
  · rw [posPow_of_nonpos (by omega) hx.le, posPow_of_nonpos hn hx.le, mul_zero]

/-- Leibniz's rule for the backward difference of `y f(y)`:
`Δ_(−1)^(k+1) (y f) (x) = x Δ_(−1)^(k+1) f (x) − (k + 1) Δ_(−1)^k f (x − 1)`. -/
theorem iterate_negDiff_mul_self (f : ℤ → ℤ) (k : ℕ) (x : ℤ) :
    (Δ_[(-1 : ℤ)])^[k + 1] (fun y => y * f y) x =
      x * (Δ_[(-1 : ℤ)])^[k + 1] f x - ((k : ℤ) + 1) * (Δ_[(-1 : ℤ)])^[k] f (x - 1) := by
  induction k generalizing x with
  | zero =>
    simp only [zero_add, iterate_one, iterate_zero, id, fwdDiff, Nat.cast_zero, ← sub_eq_add_neg]
    ring
  | succ k ih =>
    have hA : (Δ_[(-1 : ℤ)])^[k + 1] f (x - 1) =
        (Δ_[(-1 : ℤ)])^[k] f (x - 1 - 1) - (Δ_[(-1 : ℤ)])^[k] f (x - 1) := by
      rw [iterate_succ_apply']
      simp only [fwdDiff, ← sub_eq_add_neg]
    rw [iterate_succ_apply', iterate_succ_apply' _ (k + 1) f]
    simp only [fwdDiff, ← sub_eq_add_neg]
    rw [ih, ih]
    push_cast
    linear_combination ((k : ℤ) + 1) * hA

/-- **The Eulerian recurrence on ℤ**: `a_(n+1)(t) = (t + 1) a_n(t) + (n + 1 − t) a_n(t − 1)`. -/
theorem eul_succ (hn : 1 ≤ n) (t : ℤ) :
    eul (n + 1) t = (t + 1) * eul n t + ((n : ℤ) + 1 - t) * eul n (t - 1) := by
  have hf : posPow (n + 1) = fun y => y * posPow n y := funext (posPow_succ hn)
  have hA : (Δ_[(-1 : ℤ)])^[n + 1 + 1] (posPow n) (t + 1) =
      (Δ_[(-1 : ℤ)])^[n + 1] (posPow n) (t + 1 - 1) - (Δ_[(-1 : ℤ)])^[n + 1] (posPow n) (t + 1) := by
    rw [iterate_succ_apply']
    simp only [fwdDiff, ← sub_eq_add_neg]
  simp only [eul]
  rw [hf, iterate_negDiff_mul_self, hA, sub_add_cancel, add_sub_cancel_right]
  push_cast
  ring

/-- **The Eulerian recurrence**, `A(n + 1, j + 1) = (j + 2) A(n, j + 1) + (n − j) A(n, j)`; with
`A(n + 1, 0) = A(n, 0) = 1` (`eulerian_zero_right`) it is `A(n+1, j) = (j+1) A(n, j) + (n+1−j) A(n, j−1)` read with
`A(n, −1) = 0`. -/
theorem eulerian_succ_succ (n j : ℕ) :
    eulerian (n + 1) (j + 1) = ((j : ℤ) + 2) * eulerian n (j + 1) + ((n : ℤ) - j) * eulerian n j := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [eulerian_eq_zero_of_le le_rfl (by omega), eulerian_zero_succ]
    cases j with
    | zero => simp
    | succ j => rw [eulerian_zero_succ]; ring
  · rw [eulerian_eq_eul hn, eulerian_eq_eul hn, eulerian_eq_eul (by omega), eul_succ hn]
    push_cast
    rw [add_sub_cancel_right]
    ring

/-- **The Eulerian numbers are nonnegative**, so `π` is a law. -/
theorem eulerian_nonneg (n j : ℕ) : 0 ≤ eulerian n j := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => rw [eulerian_zero_right]; norm_num
    | succ j => rw [eulerian_zero_succ]
  | succ n ih =>
    cases j with
    | zero => rw [eulerian_zero_right]; norm_num
    | succ j =>
      rw [eulerian_succ_succ]
      have h1 : 0 ≤ ((j : ℤ) + 2) * eulerian n (j + 1) := mul_nonneg (by positivity) (ih (j + 1))
      by_cases hjn : j ≤ n
      · exact add_nonneg h1 (mul_nonneg (by omega) (ih j))
      · rw [eulerian_eq_zero_of_lt (by omega : n < j), mul_zero, add_zero]
        exact h1

/-- **The Eulerian numbers are positive on the carries**: `A(n, j) > 0` for `j < n`. -/
theorem eulerian_pos {n j : ℕ} (hj : j < n) : 0 < eulerian n j := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => rw [eulerian_zero_right]; norm_num
    | succ j =>
      rw [eulerian_succ_succ]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (eulerian_nonneg n (j + 1)))
        (mul_pos (by omega) (ih (by omega)))

/-- **The stationary law is a probability law**: `π_j = A(n, j)/n!` is nonnegative and sums to `1`. -/
theorem stationary_prob (hn : 1 ≤ n) :
    (∀ j : Fin n, 0 ≤ (eulerian n j : ℚ) / n.factorial) ∧ ∑ j : Fin n, (eulerian n j : ℚ) / n.factorial = 1 := by
  refine ⟨fun j => div_nonneg (by exact_mod_cast eulerian_nonneg n j) (by positivity), ?_⟩
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun j => (eulerian n j : ℚ)), div_eq_one_iff_eq (by positivity)]
  exact_mod_cast sum_eulerian hn

/-- **Every carry is charged**: `π_j > 0` for every carry `j < n`. -/
theorem stationary_pos (j : Fin n) : 0 < (eulerian n j : ℚ) / n.factorial :=
  div_pos (by exact_mod_cast eulerian_pos j.2) (by positivity)

/-- The law for three summands: `1/6, 2/3, 1/6`. -/
theorem stationary_three : (eulerian 3 0 : ℚ) / Nat.factorial 3 = 1 / 6 ∧ (eulerian 3 1 : ℚ) / Nat.factorial 3 = 2 / 3 ∧
    (eulerian 3 2 : ℚ) / Nat.factorial 3 = 1 / 6 := by
  obtain ⟨h0, h1, h2⟩ := eulerian_three
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [h0, h1, h2, Nat.factorial]

end Stationary

end Holonics.Mathematics.CarryChainEulerian
