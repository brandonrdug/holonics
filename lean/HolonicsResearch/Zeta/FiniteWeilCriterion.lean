import Mathlib

/-!
# The finite Weil criterion: the form is positive exactly when the reversal fixes every mode

[proved-derived; formal-checked] A finite family of modes that is closed under a reversal carries a
Hermitian form, the family's Weil form. It is positive semidefinite exactly when the reversal fixes
every mode. Read in a chart, "fixed by the reversal" is "on the circle" or "on the line", and read on
the family's counts the form is a Toeplitz form, so the criterion is a statement about the counts
alone.

## What is proved

* **W1, the abstract form.** `ι` a finite index of modes, `σ` an involution of it (the reversal),
  `m i > 0` multiplicities with `m (σ i) = m i`, and
  `weil m σ f = ∑ i, m i * f i * conj (f (σ i))`.
  * `weil_im`: the form is real.
  * `weil_nonneg_iff`: `(∀ f, 0 ≤ (weil m σ f).re) ↔ ∀ i, σ i = i`.
  * `weil_test`, `weilB_test_test`: on a two-cycle `{i, σ i}` the test
    `test σ i = Pi.single i 1 − Pi.single (σ i) 1` reads `−2 m i`, and the tests of two distinct
    two-cycles are orthogonal for the form. So each mode the reversal moves gives one negative
    direction, and these directions do not see each other. `weil_eq_sum_normSq_of_fixed`: when the
    reversal fixes every mode the form is `∑ m i ‖f i‖²`.
* **W2, interpolation** (`exists_polynomial_eval_eq`): on distinct modes every test is a polynomial
  of degree under the count of modes (Lagrange).
* **The chart lemma** (`chart_criterion`): for any map `R` of the plane with `z (σ i) = R (z i)` on
  distinct modes `z`, the form on polynomial tests,
  `∑ i, m i * p (z i) * conj (p (R (z i)))`, is nonnegative for every `p` exactly when `R` fixes
  every mode.
* **W3, the circle chart** (`circle_criterion`): `R w = 1 / conj w`, modes nonzero: the form is
  nonnegative on every polynomial iff `‖z i‖ = 1` for every mode.
* **W4, the line chart** (`line_criterion`): `R w = 1 − conj w`: the form is nonnegative on every
  polynomial iff `(z i).re = 1/2` for every mode.
* **W5, the form in the counts.** With `counts m z l = ∑ i, m i * z i ^ l` for `l : ℤ` and the
  test `testPoly x = ∑ k, C (x k) * X ^ k`:
  * `weil_testPoly_eq_toeplitz`: the circle chart's form on `testPoly x` is
    `∑ j k, x j * conj (x k) * counts m z (j − k)`.
  * `toeplitz_criterion`: the counts form a positive-definite sequence (every such finite form is
    nonnegative) iff every mode is on the circle; `toeplitz_criterion_card`: the forms of size the
    count of modes suffice.
  * `counts_neg`: `counts m z (−l) = conj (counts m z l)`, from the closure under the reversal.
* **W6, the smallest family off the circle.** For real `r`, the pair `{r, 1/r}` has
  `counts l = r^l + r^(−l)` (`pair_counts`), the pair is closed under the circle's reversal
  (`pair_reversal`), and the test `(1, −1)` reads `4 − 2 (r + 1/r)` (`pair_toeplitz`), which is
  negative for `r > 1` (`pair_toeplitz_neg`).

## Reading

[interpretation] For a finite complex with `q + 1` contacts a cell the modes are the nontrivial
`α / √q` of its dart operator (`Landmarks/IharaBass`, `Landmarks/RegularGraphNormForm`), the
reversal is the functional equation `u ↦ 1/(q u)`, and the counts `c l` are the remainders of the
counts of closed walks without backtracking over `q^(l/2)`. W5 then says: the complex is tempered
(every nontrivial mode on `|α|² = q`) exactly when its counts' remainders form a positive-definite
sequence. For the integers the modes are the zeros, the reversal is `s ↦ 1 − conj s`, the tests are
Mellin transforms, and W4 is the finite form of Weil's criterion (Weil 1952; from training, named
here only as the reading).

## What this does not state

Nothing here states the criterion for an unending family of modes: no convergence, no class of
test functions, no explicit formula, nothing about `ζ`. The identification of a complex's counts
with `counts` (through `det (1 − u B)`) is not made in this file. The full inertia of the form (that
its negative index is exactly the number of two-cycles of the reversal) is not stated; `weil_test`
and `weilB_test_test` give the negative directions and their orthogonality, and
`weil_eq_sum_normSq_of_fixed` the positive part when there are none.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace Holonics.Zeta.FiniteWeilCriterion

open Polynomial
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## W1. The abstract form -/

/-- [definition] The Weil pairing of two tests on a family of modes with reversal `σ` and
multiplicities `m`. -/
def weilB (m : ι → ℝ) (σ : ι → ι) (f g : ι → ℂ) : ℂ :=
  ∑ i, (m i : ℂ) * f i * conj (g (σ i))

/-- [definition] The Weil form: `∑ i, m i * f i * conj (f (σ i))`. -/
def weil (m : ι → ℝ) (σ : ι → ι) (f : ι → ℂ) : ℂ :=
  ∑ i, (m i : ℂ) * f i * conj (f (σ i))

omit [DecidableEq ι] in
theorem weil_eq_weilB (m : ι → ℝ) (σ : ι → ι) (f : ι → ℂ) : weil m σ f = weilB m σ f f := rfl

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] The form is its own conjugate. -/
theorem conj_weil {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i) (hmσ : ∀ i, m (σ i) = m i)
    (f : ι → ℂ) : conj (weil m σ f) = weil m σ f := by
  unfold weil
  rw [map_sum]
  have hinv : Function.Involutive σ := hσ
  refine Fintype.sum_equiv (hinv.toPerm σ) _ _ fun i => ?_
  simp only [Function.Involutive.coe_toPerm, map_mul, Complex.conj_ofReal, Complex.conj_conj, hσ,
    hmσ]
  ring

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **W1 (a).** The Weil form is real. -/
theorem weil_im {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i) (hmσ : ∀ i, m (σ i) = m i)
    (f : ι → ℂ) : (weil m σ f).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_weil hσ hmσ f)

theorem weilB_single_left (m : ι → ℝ) (σ : ι → ι) (i : ι) (a : ℂ) (g : ι → ℂ) :
    weilB m σ (Pi.single i a) g = (m i : ℂ) * a * conj (g (σ i)) := by
  unfold weilB
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [DecidableEq ι] in
theorem weilB_sub_left (m : ι → ℝ) (σ : ι → ι) (f f' g : ι → ℂ) :
    weilB m σ (f - f') g = weilB m σ f g - weilB m σ f' g := by
  unfold weilB
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.sub_apply]
  ring

/-- [definition] The test of a mode against its image under the reversal. -/
def test (σ : ι → ι) (i : ι) : ι → ℂ := Pi.single i 1 - Pi.single (σ i) 1

omit [Fintype ι] in
theorem test_apply_self {σ : ι → ι} {i : ι} (h : σ i ≠ i) : test σ i i = 1 := by
  unfold test
  rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h.symm, sub_zero]

omit [Fintype ι] in
theorem test_apply_image {σ : ι → ι} {i : ι} (h : σ i ≠ i) : test σ i (σ i) = -1 := by
  unfold test
  rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h, zero_sub]

omit [Fintype ι] in
theorem test_apply_of_ne {σ : ι → ι} {i k : ι} (hk : k ≠ i) (hk' : k ≠ σ i) : test σ i k = 0 := by
  unfold test
  rw [Pi.sub_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk', sub_zero]

theorem weilB_test_left {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i)
    (hmσ : ∀ i, m (σ i) = m i) (i : ι) (g : ι → ℂ) :
    weilB m σ (test σ i) g = (m i : ℂ) * (conj (g (σ i)) - conj (g i)) := by
  unfold test
  rw [weilB_sub_left, weilB_single_left, weilB_single_left, hσ, hmσ]
  ring

/-- [proved-derived; formal-checked] **W1 (c), the value.** On a mode the reversal moves, the test
of the mode against its image reads `−2 m i`. -/
theorem weil_test {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i) (hmσ : ∀ i, m (σ i) = m i)
    {i : ι} (h : σ i ≠ i) : weil m σ (test σ i) = -(2 * (m i : ℂ)) := by
  rw [weil_eq_weilB, weilB_test_left hσ hmσ, test_apply_image h, test_apply_self h, map_neg,
    map_one]
  ring

/-- [proved-derived; formal-checked] **W1 (c), orthogonality.** The tests of two distinct two-cycles
of the reversal do not see each other. -/
theorem weilB_test_test {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i)
    (hmσ : ∀ i, m (σ i) = m i) {i j : ι} (hji : j ≠ i) (hjσ : j ≠ σ i) :
    weilB m σ (test σ i) (test σ j) = 0 := by
  rw [weilB_test_left hσ hmσ]
  have h1 : test σ j (σ i) = 0 := by
    refine test_apply_of_ne (fun h => hjσ h.symm) (fun h => hji ?_)
    calc j = σ (σ j) := (hσ j).symm
      _ = σ (σ i) := by rw [h]
      _ = i := hσ i
  have h2 : test σ j i = 0 := by
    refine test_apply_of_ne (fun h => hji h.symm) (fun h => hjσ ?_)
    rw [h, hσ]
  rw [h1, h2, map_zero, sub_zero, mul_zero]

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] When the reversal fixes every mode the form is a sum of
squares. -/
theorem weil_eq_sum_normSq_of_fixed {m : ι → ℝ} {σ : ι → ι} (hfix : ∀ i, σ i = i) (f : ι → ℂ) :
    weil m σ f = ((∑ i, m i * Complex.normSq (f i) : ℝ) : ℂ) := by
  unfold weil
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfix i, mul_assoc, Complex.mul_conj, Complex.ofReal_mul]

/-- [proved-derived; formal-checked] **W1 (b).** The Weil form is nonnegative on every test exactly
when the reversal fixes every mode. -/
theorem weil_nonneg_iff {m : ι → ℝ} {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i) (hm : ∀ i, 0 < m i)
    (hmσ : ∀ i, m (σ i) = m i) : (∀ f, 0 ≤ (weil m σ f).re) ↔ ∀ i, σ i = i := by
  constructor
  · intro h i
    by_contra hi
    have h0 := h (test σ i)
    rw [weil_test hσ hmσ hi] at h0
    have hre : (-(2 * (m i : ℂ))).re = -(2 * m i) := by simp
    rw [hre] at h0
    linarith [hm i]
  · intro hfix f
    rw [weil_eq_sum_normSq_of_fixed hfix, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (Complex.normSq_nonneg _)

/-! ## W2. Interpolation -/

/-- [proved-standard; formal-checked] **W2.** On distinct modes every test is a polynomial of degree
under the count of modes (Lagrange). -/
theorem exists_polynomial_eval_eq {z : ι → ℂ} (hz : Function.Injective z) (f : ι → ℂ) :
    ∃ p : Polynomial ℂ, p.degree < (Fintype.card ι : WithBot ℕ) ∧ ∀ i, p.eval (z i) = f i := by
  refine ⟨Lagrange.interpolate Finset.univ z f, ?_, fun i => ?_⟩
  · have h := Lagrange.degree_interpolate_lt (r := f) (hz.injOn (s := ↑(Finset.univ : Finset ι)))
    simpa using h
  · exact Lagrange.eval_interpolate_at_node (r := f) (hz.injOn) (Finset.mem_univ i)

/-! ## The chart lemma, and W3, W4 -/

/-- [proved-derived; formal-checked] **The chart lemma.** For modes `z` that are distinct and a map
`R` of the plane that realizes the reversal on them, the form on polynomial tests is nonnegative
exactly when `R` fixes every mode. -/
theorem chart_criterion {m : ι → ℝ} {σ : ι → ι} {z : ι → ℂ} (R : ℂ → ℂ)
    (hz : Function.Injective z) (hσ : ∀ i, σ (σ i) = i) (hm : ∀ i, 0 < m i)
    (hmσ : ∀ i, m (σ i) = m i) (hσz : ∀ i, z (σ i) = R (z i)) :
    (∀ p : Polynomial ℂ,
        0 ≤ (∑ i, (m i : ℂ) * p.eval (z i) * conj (p.eval (R (z i)))).re)
      ↔ ∀ i, R (z i) = z i := by
  have key : ∀ p : Polynomial ℂ, ∑ i, (m i : ℂ) * p.eval (z i) * conj (p.eval (R (z i)))
      = weil m σ (fun i => p.eval (z i)) := by
    intro p
    simp only [weil, hσz]
  have hfix : (∀ i, σ i = i) ↔ ∀ i, R (z i) = z i := by
    refine forall_congr' fun i => ?_
    rw [← hσz i]
    exact ⟨fun h => by rw [h], fun h => hz h⟩
  rw [← hfix, ← weil_nonneg_iff hσ hm hmσ]
  constructor
  · intro h f
    obtain ⟨p, -, hp⟩ := exists_polynomial_eval_eq hz f
    have h0 := h p
    rw [key p] at h0
    have hf : (fun i => p.eval (z i)) = f := funext hp
    rwa [hf] at h0
  · intro h p
    rw [key p]
    exact h _

omit [Fintype ι] [DecidableEq ι] in
theorem involutive_of_circle {σ : ι → ι} {z : ι → ℂ} (hz : Function.Injective z)
    (hσz : ∀ i, z (σ i) = 1 / conj (z i)) (i : ι) : σ (σ i) = i := by
  apply hz
  rw [hσz, hσz]
  simp

theorem inv_conj_eq_self_iff {w : ℂ} (hw : w ≠ 0) : 1 / conj w = w ↔ ‖w‖ = 1 := by
  have hc : conj w ≠ 0 := (_root_.map_ne_zero _).mpr hw
  rw [div_eq_iff hc, Complex.mul_conj]
  constructor
  · intro h
    have h1 : Complex.normSq w = 1 := by exact_mod_cast h.symm
    rw [Complex.normSq_eq_norm_sq] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) two_ne_zero).mp h1
  · intro h
    rw [Complex.normSq_eq_norm_sq, h]
    norm_num

/-- [proved-derived; formal-checked] **W3, the circle chart.** For distinct nonzero modes closed
under `w ↦ 1 / conj w`, the form is nonnegative on every polynomial test exactly when every mode is
on the unit circle. -/
theorem circle_criterion {m : ι → ℝ} {σ : ι → ι} {z : ι → ℂ} (hz : Function.Injective z)
    (hz0 : ∀ i, z i ≠ 0) (hm : ∀ i, 0 < m i) (hmσ : ∀ i, m (σ i) = m i)
    (hσz : ∀ i, z (σ i) = 1 / conj (z i)) :
    (∀ p : Polynomial ℂ,
        0 ≤ (∑ i, (m i : ℂ) * p.eval (z i) * conj (p.eval (1 / conj (z i)))).re)
      ↔ ∀ i, ‖z i‖ = 1 :=
  (chart_criterion (fun w => 1 / conj w) hz (involutive_of_circle hz hσz) hm hmσ hσz).trans
    (forall_congr' fun i => inv_conj_eq_self_iff (hz0 i))

omit [Fintype ι] [DecidableEq ι] in
theorem involutive_of_line {σ : ι → ι} {z : ι → ℂ} (hz : Function.Injective z)
    (hσz : ∀ i, z (σ i) = 1 - conj (z i)) (i : ι) : σ (σ i) = i := by
  apply hz
  rw [hσz, hσz]
  simp

theorem one_sub_conj_eq_self_iff (w : ℂ) : 1 - conj w = w ↔ w.re = 1 / 2 := by
  constructor
  · intro h
    have h1 := congrArg Complex.re h
    simp at h1
    linarith
  · intro h
    apply Complex.ext
    · simp
      linarith
    · simp

/-- [proved-derived; formal-checked] **W4, the line chart.** For distinct modes closed under
`s ↦ 1 − conj s`, the form is nonnegative on every polynomial test exactly when every mode has real
part one half. -/
theorem line_criterion {m : ι → ℝ} {σ : ι → ι} {z : ι → ℂ} (hz : Function.Injective z)
    (hm : ∀ i, 0 < m i) (hmσ : ∀ i, m (σ i) = m i) (hσz : ∀ i, z (σ i) = 1 - conj (z i)) :
    (∀ p : Polynomial ℂ,
        0 ≤ (∑ i, (m i : ℂ) * p.eval (z i) * conj (p.eval (1 - conj (z i)))).re)
      ↔ ∀ i, (z i).re = 1 / 2 :=
  (chart_criterion (fun w => 1 - conj w) hz (involutive_of_line hz hσz) hm hmσ hσz).trans
    (forall_congr' fun i => one_sub_conj_eq_self_iff (z i))

/-! ## W5. The form in the counts -/

/-- [definition] The counts of a family of modes: its power sums, at every integer. -/
def counts (m : ι → ℝ) (z : ι → ℂ) (l : ℤ) : ℂ := ∑ i, (m i : ℂ) * z i ^ l

/-- [definition] The polynomial test with coefficients `x`. -/
def testPoly {n : ℕ} (x : Fin n → ℂ) : Polynomial ℂ := ∑ k : Fin n, C (x k) * X ^ (k : ℕ)

theorem eval_testPoly {n : ℕ} (x : Fin n → ℂ) (w : ℂ) :
    (testPoly x).eval w = ∑ k : Fin n, x k * w ^ (k : ℕ) := by
  simp [testPoly, Polynomial.eval_finsetSum]

theorem testPoly_coeff (p : Polynomial ℂ) {n : ℕ} (h : p.natDegree < n) :
    testPoly (fun k : Fin n => p.coeff k) = p := by
  simp only [testPoly]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i) n]
  exact (p.as_sum_range_C_mul_X_pow' h).symm

theorem testPoly_coeff_of_degree_lt (p : Polynomial ℂ) {n : ℕ} (h : p.degree < (n : WithBot ℕ)) :
    testPoly (fun k : Fin n => p.coeff k) = p := by
  by_cases hp : p = 0
  · subst hp
    simp [testPoly]
  · exact testPoly_coeff p ((Polynomial.natDegree_lt_iff_degree_lt hp).mpr h)

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **W5, the identity.** The circle chart's form on a polynomial
test is the Toeplitz form of the counts. -/
theorem weil_testPoly_eq_toeplitz (m : ι → ℝ) {n : ℕ} (x : Fin n → ℂ) {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0) :
    ∑ i, (m i : ℂ) * (testPoly x).eval (z i) * conj ((testPoly x).eval (1 / conj (z i)))
      = ∑ j : Fin n, ∑ k : Fin n, x j * conj (x k) * counts m z ((j : ℤ) - (k : ℤ)) := by
  simp only [eval_testPoly, counts, map_sum, map_mul, map_pow, map_div₀, map_one,
    Complex.conj_conj]
  calc ∑ i, (m i : ℂ) * (∑ j : Fin n, x j * z i ^ (j : ℕ))
          * (∑ k : Fin n, conj (x k) * (1 / z i) ^ (k : ℕ))
      = ∑ i, ∑ j : Fin n, ∑ k : Fin n,
          x j * conj (x k) * ((m i : ℂ) * z i ^ ((j : ℤ) - (k : ℤ))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hzi := hz0 i
        rw [zpow_sub₀ hzi, zpow_natCast, zpow_natCast, one_div, inv_pow, div_eq_mul_inv]
        ring
    _ = ∑ j : Fin n, ∑ k : Fin n, x j * conj (x k) * ∑ i, (m i : ℂ) * z i ^ ((j : ℤ) - (k : ℤ)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]

/-- [proved-derived; formal-checked] **W5, the criterion on the counts.** The counts of a family
closed under the circle's reversal form a positive-definite sequence exactly when every mode is on
the unit circle. -/
theorem toeplitz_criterion {m : ι → ℝ} {σ : ι → ι} {z : ι → ℂ} (hz : Function.Injective z)
    (hz0 : ∀ i, z i ≠ 0) (hm : ∀ i, 0 < m i) (hmσ : ∀ i, m (σ i) = m i)
    (hσz : ∀ i, z (σ i) = 1 / conj (z i)) :
    (∀ (n : ℕ) (x : Fin n → ℂ),
        0 ≤ (∑ j : Fin n, ∑ k : Fin n, x j * conj (x k) * counts m z ((j : ℤ) - (k : ℤ))).re)
      ↔ ∀ i, ‖z i‖ = 1 := by
  refine Iff.trans ?_ (circle_criterion hz hz0 hm hmσ hσz)
  constructor
  · intro h p
    have h0 := h (p.natDegree + 1) (fun k => p.coeff k)
    rw [← weil_testPoly_eq_toeplitz m _ hz0, testPoly_coeff p (Nat.lt_succ_self _)] at h0
    exact h0
  · intro h n x
    rw [← weil_testPoly_eq_toeplitz m _ hz0]
    exact h _

/-- [proved-derived; formal-checked] **W5, the size that suffices.** The Toeplitz forms of size the
count of modes already decide. -/
theorem toeplitz_criterion_card {m : ι → ℝ} {σ : ι → ι} {z : ι → ℂ} (hz : Function.Injective z)
    (hz0 : ∀ i, z i ≠ 0) (hm : ∀ i, 0 < m i) (hmσ : ∀ i, m (σ i) = m i)
    (hσz : ∀ i, z (σ i) = 1 / conj (z i)) :
    (∀ x : Fin (Fintype.card ι) → ℂ,
        0 ≤ (∑ j : Fin (Fintype.card ι), ∑ k : Fin (Fintype.card ι),
          x j * conj (x k) * counts m z ((j : ℤ) - (k : ℤ))).re)
      ↔ ∀ i, ‖z i‖ = 1 := by
  constructor
  · intro h
    have hσ := involutive_of_circle hz hσz
    have hfix : ∀ i, σ i = i := by
      rw [← weil_nonneg_iff hσ hm hmσ]
      intro f
      obtain ⟨p, hdeg, hp⟩ := exists_polynomial_eval_eq hz f
      have h0 := h (fun k => p.coeff k)
      rw [← weil_testPoly_eq_toeplitz m _ hz0, testPoly_coeff_of_degree_lt p hdeg] at h0
      have key : ∑ i, (m i : ℂ) * p.eval (z i) * conj (p.eval (1 / conj (z i)))
          = weil m σ f := by
        unfold weil
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hp i, ← hσz i, hp (σ i)]
      rwa [key] at h0
    intro i
    have h1 := hσz i
    rw [hfix i] at h1
    exact (inv_conj_eq_self_iff (hz0 i)).mp h1.symm
  · intro h x
    exact (toeplitz_criterion hz hz0 hm hmσ hσz).mpr h _ x

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] The counts at `−l` are the conjugates of the counts at `l`. -/
theorem counts_neg {m : ι → ℝ} {σ : ι → ι} {z : ι → ℂ} (hσ : ∀ i, σ (σ i) = i)
    (hmσ : ∀ i, m (σ i) = m i) (hσz : ∀ i, z (σ i) = 1 / conj (z i)) (l : ℤ) :
    counts m z (-l) = conj (counts m z l) := by
  unfold counts
  rw [map_sum]
  have hinv : Function.Involutive σ := hσ
  refine Fintype.sum_equiv (hinv.toPerm σ) _ _ fun i => ?_
  simp only [Function.Involutive.coe_toPerm, map_mul, Complex.conj_ofReal, map_zpow₀, hσz, hmσ,
    map_div₀, map_one, Complex.conj_conj]
  rw [one_div, inv_zpow, zpow_neg]

/-! ## W6. The smallest family off the circle -/

/-- [proved-derived; formal-checked] The pair `{r, 1/r}` is closed under the circle's reversal. -/
theorem pair_reversal (r : ℝ) (i : Fin 2) :
    (![(r : ℂ), (r : ℂ)⁻¹] : Fin 2 → ℂ) (Fin.rev i)
      = 1 / conj ((![(r : ℂ), (r : ℂ)⁻¹] : Fin 2 → ℂ) i) := by
  fin_cases i <;> simp

/-- [proved-derived; formal-checked] The counts of the pair `{r, 1/r}`. -/
theorem pair_counts (r : ℝ) (l : ℤ) :
    counts (fun _ : Fin 2 => (1 : ℝ)) ![(r : ℂ), (r : ℂ)⁻¹] l = (r : ℂ) ^ l + (r : ℂ) ^ (-l) := by
  simp [counts, Fin.sum_univ_two, zpow_neg]

/-- [proved-derived; formal-checked] On the pair `{r, 1/r}` the test `(1, −1)` reads
`4 − 2 (r + 1/r)`. -/
theorem pair_toeplitz (r : ℝ) :
    (∑ j : Fin 2, ∑ k : Fin 2, (![1, -1] : Fin 2 → ℂ) j * conj ((![1, -1] : Fin 2 → ℂ) k)
        * counts (fun _ : Fin 2 => (1 : ℝ)) ![(r : ℂ), (r : ℂ)⁻¹] ((j : ℤ) - (k : ℤ))).re
      = 4 - 2 * (r + 1 / r) := by
  have h : (∑ j : Fin 2, ∑ k : Fin 2, (![1, -1] : Fin 2 → ℂ) j * conj ((![1, -1] : Fin 2 → ℂ) k)
        * counts (fun _ : Fin 2 => (1 : ℝ)) ![(r : ℂ), (r : ℂ)⁻¹] ((j : ℤ) - (k : ℤ)))
      = ((4 - 2 * (r + 1 / r) : ℝ) : ℂ) := by
    simp only [pair_counts, Fin.sum_univ_two]
    simp
    ring
  rw [h, Complex.ofReal_re]

/-- [proved-derived; formal-checked] **W6.** For `r > 1` that reading is negative: a pair off the
circle is seen by a form of size two. -/
theorem pair_toeplitz_neg {r : ℝ} (hr : 1 < r) : 4 - 2 * (r + 1 / r) < 0 := by
  have hr0 : 0 < r := by linarith
  have h : r + 1 / r - 2 = (r - 1) ^ 2 / r := by
    field_simp
    ring
  have hpos : 0 < (r - 1) ^ 2 / r := div_pos (pow_pos (by linarith) 2) hr0
  linarith

section Audit

#print axioms weil_im
#print axioms weil_test
#print axioms weilB_test_test
#print axioms weil_eq_sum_normSq_of_fixed
#print axioms weil_nonneg_iff
#print axioms exists_polynomial_eval_eq
#print axioms chart_criterion
#print axioms circle_criterion
#print axioms line_criterion
#print axioms weil_testPoly_eq_toeplitz
#print axioms toeplitz_criterion
#print axioms toeplitz_criterion_card
#print axioms counts_neg
#print axioms pair_reversal
#print axioms pair_counts
#print axioms pair_toeplitz
#print axioms pair_toeplitz_neg

end Audit

end Holonics.Zeta.FiniteWeilCriterion
