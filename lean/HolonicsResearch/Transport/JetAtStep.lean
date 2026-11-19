import Holonics.Transport.JetStaircase
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-!
# Differences to jets at any rational step: an upper triangular change of basis with diagonal `1/(k! hᵏ)`

`Transport/JetStaircase` states the passage between difference data and jet data on the lattice of
step one, in the Newton chart `C(n, k)`. The retired Rust owner `to_jet`
([history](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/jet_staircase.rs))
read it at a declared step `h` from a declared base `x₀`: Newton's forward formula with the falling factorial expanded
by its integer recurrence, then the coefficient of `tⁱ` divided by `hⁱ` to reach `(x − x₀)ⁱ`. This module states that
change of basis for every nonzero rational step.

1. **Sampling at step `h` is the staircase's own difference.** `delta_iterate_sample`: the ladder's `Δ` (which is
   `Foundation/HigherDifferenceTransport`'s `difference`) iterated on the samples `m ↦ g(x₀ + m h)` is Mathlib's
   step-`h` difference `Δ_[h]` iterated on `g`, read at the node. No second difference operator is founded.
2. **The map.** `newton r a = Σ_{k ≤ r} (a_k / k!) · (t)_k`, with `(t)_k` the falling factorial
   (`descPochhammer`), reads `JetStaircase.ofCoefficients` at every node (`newton_eval_natCast`), and
   `toJetAtStep h r a = newton r a ∘ (u / h)` is the jet in `u = x − x₀`.
3. **Its matrix.** `coeff_toJetAtStep`: coefficient `i` of the jet is `Σ_k entry h i k · a_k` with
   `entry h i k = [tⁱ](t)_k / (k! hⁱ)`, the Rust's `falling` row divided as it divides. The matrix is upper triangular
   in the difference index (`entry_eq_zero_of_lt`, `coeff_toJetAtStep_triangular`) with diagonal `1/(k! hᵏ)`
   (`entry_diag`), as the Rust's docstring says.
4. **Both round trips.** For a polynomial `p` of degree at most `r`, the jet of its step-`h` differences at `x₀` is its
   Taylor expansion at `x₀` (`toJetAtStep_differences`), by the Gregory–Newton formula and the vanishing of differences
   above the degree (`differences_eq_zero_of_lt`). For any differences `a`, the jet read back on the nodes returns
   `a_k` for every `k ≤ r` (`differences_toJetAtStep`), through the staircase's own change of basis
   (`JetStaircase.coefficient_eq_iteratedDelta_at_zero`). So the jet determines exactly the first `r + 1` differences
   (`toJetAtStep_eq_iff`), and at step one from the base zero it is the staircase's Newton jet
   (`toJetAtStep_one_eval`).

Scope: the step is a nonzero rational and the base any rational. The Rust's refusals (an order past its ceiling or past
the sample count) are bounds of the realization and are not stated; a sample of `r + 1` nodes is what `differences` up
to order `r` reads (`fwdDiff_iter_eq_sum_shift`).

Truth status: `[proved-derived] [formal-checked]` for every theorem below.
-/

namespace Holonics.Transport.JetAtStep

open Polynomial Finset
open scoped fwdDiff Nat

/-! ## 1. Sampling at step `h` -/

/-- **The staircase's difference on the samples is the step-`h` difference.** For every `g`, iterating the ladder's
`Δ` on `m ↦ g(x₀ + m h)` and reading node `n` is iterating `Δ_[h]` on `g` and reading `x₀ + n h`. -/
theorem delta_iterate_sample (x₀ h : ℚ) :
    ∀ (k : ℕ) (g : ℚ → ℚ) (n : ℕ),
      JetStaircase.Delta^[k] (fun m : ℕ => g (x₀ + m * h)) n = (Δ_[h]^[k] g) (x₀ + n * h) := by
  intro k
  induction k with
  | zero => intro g n; rfl
  | succ k ih =>
      intro g n
      have hstep : JetStaircase.Delta (fun m : ℕ => g (x₀ + m * h))
          = fun m : ℕ => (Δ_[h] g) (x₀ + m * h) := by
        funext m
        simp only [JetStaircase.Delta, fwdDiff]
        rw [show x₀ + ((m + 1 : ℕ) : ℚ) * h = x₀ + m * h + h by push_cast; ring]
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep]
      exact ih _ n

/-- The difference column at step `h` from the base `x₀`: `D_k = Δ_hᵏ f (x₀)`. -/
def differences (h x₀ : ℚ) (f : ℚ → ℚ) (k : ℕ) : ℚ := (Δ_[h]^[k] f) x₀

/-- The column is the staircase's own iterated difference of the samples, read at node zero. -/
theorem differences_eq_staircase (h x₀ : ℚ) (f : ℚ → ℚ) (k : ℕ) :
    differences h x₀ f k = JetStaircase.Delta^[k] (fun m : ℕ => f (x₀ + m * h)) 0 := by
  rw [delta_iterate_sample]
  simp [differences]

/-! ## 2. The Newton polynomial and the jet -/

/-- Newton's forward polynomial in the step variable `t`: `Σ_{k ≤ r} (a_k / k!) · t(t − 1)⋯(t − k + 1)`. -/
noncomputable def newton (r : ℕ) (a : ℕ → ℚ) : ℚ[X] :=
  ∑ k ∈ range (r + 1), C (a k / (k ! : ℚ)) * descPochhammer ℚ k

/-- **At every node the Newton polynomial is the staircase's Newton jet**: `(n)_k / k! = C(n, k)`. -/
theorem newton_eval_natCast (r : ℕ) (a : ℕ → ℚ) (n : ℕ) :
    (newton r a).eval (n : ℚ) = JetStaircase.ofCoefficients r a n := by
  simp only [newton, eval_finsetSum, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    JetStaircase.ofCoefficients, JetStaircase.binom]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  have hk : (k ! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  push_cast
  field_simp

theorem natDegree_newton_le (r : ℕ) (a : ℕ → ℚ) : (newton r a).natDegree ≤ r := by
  unfold newton
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [descPochhammer_natDegree]
  exact Nat.lt_succ_iff.mp (mem_range.mp hk)

/-- **Differences to a jet at step `h`**: the jet in `u = x − x₀` is the Newton polynomial read at `t = u / h`. -/
noncomputable def toJetAtStep (h : ℚ) (r : ℕ) (a : ℕ → ℚ) : ℚ[X] := (newton r a).comp (C h⁻¹ * X)

theorem natDegree_toJetAtStep_le (h : ℚ) (r : ℕ) (a : ℕ → ℚ) : (toJetAtStep h r a).natDegree ≤ r := by
  refine natDegree_comp_le.trans ?_
  have hlin : (C h⁻¹ * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
  calc (newton r a).natDegree * (C h⁻¹ * X).natDegree ≤ r * 1 :=
        Nat.mul_le_mul (natDegree_newton_le r a) hlin
    _ = r := mul_one r

/-! ## 3. The matrix: upper triangular with diagonal `1/(k! hᵏ)` -/

/-- The matrix entry from difference `k` to jet coefficient `i`: `[tⁱ](t)_k / (k! hⁱ)`. -/
noncomputable def entry (h : ℚ) (i k : ℕ) : ℚ :=
  (descPochhammer ℚ k).coeff i / ((k ! : ℚ) * h ^ i)

/-- **The jet's coefficients are the matrix applied to the differences.** -/
theorem coeff_toJetAtStep (h : ℚ) (r : ℕ) (a : ℕ → ℚ) (i : ℕ) :
    (toJetAtStep h r a).coeff i = ∑ k ∈ range (r + 1), entry h i k * a k := by
  rw [toJetAtStep, comp_C_mul_X_coeff, newton, finsetSum_coeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul, entry]
  ring

/-- **Upper triangular**: a difference of lower index never reaches a higher jet coefficient. -/
theorem entry_eq_zero_of_lt (h : ℚ) {i k : ℕ} (hki : k < i) : entry h i k = 0 := by
  rw [entry, coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; exact hki), zero_div]

/-- **The diagonal is `1/(k! hᵏ)`**: the falling factorial is monic. -/
theorem entry_diag (h : ℚ) (k : ℕ) : entry h k k = 1 / ((k ! : ℚ) * h ^ k) := by
  have hm := monic_descPochhammer ℚ k
  rw [Monic, leadingCoeff, descPochhammer_natDegree] at hm
  rw [entry, hm]

/-- Coefficient `i` of the jet reads only the differences of index `i` and above. -/
theorem coeff_toJetAtStep_triangular (h : ℚ) (r : ℕ) (a b : ℕ → ℚ) (i : ℕ)
    (hab : ∀ k, i ≤ k → k ≤ r → a k = b k) :
    (toJetAtStep h r a).coeff i = (toJetAtStep h r b).coeff i := by
  rw [coeff_toJetAtStep, coeff_toJetAtStep]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hik : i ≤ k
  · rw [hab k hik (Nat.lt_succ_iff.mp (mem_range.mp hk))]
  · rw [entry_eq_zero_of_lt h (by omega), zero_mul, zero_mul]

/-- The top coefficient of the jet is `a_r / (r! hʳ)`. -/
theorem coeff_toJetAtStep_top (h : ℚ) (r : ℕ) (a : ℕ → ℚ) :
    (toJetAtStep h r a).coeff r = a r / ((r ! : ℚ) * h ^ r) := by
  rw [coeff_toJetAtStep, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, entry_diag]
  · ring
  · intro k hk
    rw [entry_eq_zero_of_lt h (mem_range.mp hk), zero_mul]

/-! ## 4. The round trips -/

theorem natDegree_comp_affine_le (p : ℚ[X]) (x₀ h : ℚ) :
    (p.comp (C x₀ + C h * X)).natDegree ≤ p.natDegree := by
  refine natDegree_comp_le.trans ?_
  have hlin : (C x₀ + C h * X).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
  calc p.natDegree * (C x₀ + C h * X).natDegree ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hlin
    _ = p.natDegree := mul_one _

/-- **Differences above the degree vanish at every step.** -/
theorem differences_eq_zero_of_lt (h x₀ : ℚ) (p : ℚ[X]) {k : ℕ} (hk : p.natDegree < k) :
    differences h x₀ p.eval k = 0 := by
  set q := p.comp (C x₀ + C h * X) with hq
  have hsamp : (fun m : ℕ => p.eval (x₀ + m * h)) = fun m : ℕ => q.eval ((0 : ℚ) + m * 1) := by
    funext m
    simp only [hq, eval_comp, eval_add, eval_C, eval_mul, eval_X]
    congr 1
    ring
  rw [differences_eq_staircase, hsamp, delta_iterate_sample 0 1 k q.eval 0,
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt ((natDegree_comp_affine_le p x₀ h).trans_lt hk)]
  rfl

/-- **The Newton polynomial of a polynomial's differences is the polynomial read in step units**: for `p` of degree at
most `r`, `newton r (Δ_hᵏ p(x₀))_k = p(x₀ + h t)`. Gregory–Newton at every node, and two polynomials that agree on the
naturals are one. -/
theorem newton_differences (h x₀ : ℚ) (p : ℚ[X]) {r : ℕ} (hp : p.natDegree ≤ r) :
    newton r (differences h x₀ p.eval) = p.comp (C x₀ + C h * X) := by
  apply eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.range (Nat.cast : ℕ → ℚ)) ?_
    (Set.infinite_range_of_injective Nat.cast_injective)
  rintro _ ⟨n, rfl⟩
  simp only [Set.mem_ofPred_eq]
  rw [newton_eval_natCast, eval_comp]
  simp only [eval_add, eval_C, eval_mul, eval_X]
  rw [show x₀ + h * n = x₀ + n • h by rw [nsmul_eq_mul]; ring, shift_eq_sum_fwdDiff_iter h p.eval n x₀]
  simp only [JetStaircase.ofCoefficients, JetStaircase.binom, nsmul_eq_mul]
  have h1 : ∑ k ∈ range (r + 1), differences h x₀ p.eval k * (n.choose k : ℚ)
      = ∑ k ∈ range (n + r + 1), differences h x₀ p.eval k * (n.choose k : ℚ) := by
    refine Finset.sum_subset (range_subset_range.mpr (by omega)) fun k _ hk => ?_
    rw [differences_eq_zero_of_lt h x₀ p (by simp only [mem_range] at hk; omega), zero_mul]
  have h2 : ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (Δ_[h]^[k] p.eval) x₀
      = ∑ k ∈ range (n + r + 1), (n.choose k : ℚ) * (Δ_[h]^[k] p.eval) x₀ := by
    refine Finset.sum_subset (range_subset_range.mpr (by omega)) fun k _ hk => ?_
    rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hk; omega), Nat.cast_zero, zero_mul]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Jets to differences to jets is the identity**: for a polynomial `p` of degree at most `r` and any nonzero
step, the jet of its step-`h` differences at `x₀` is its Taylor expansion at `x₀`. -/
theorem toJetAtStep_differences (h x₀ : ℚ) (hh : h ≠ 0) (p : ℚ[X]) {r : ℕ} (hp : p.natDegree ≤ r) :
    toJetAtStep h r (differences h x₀ p.eval) = taylor x₀ p := by
  rw [toJetAtStep, newton_differences h x₀ p hp, comp_assoc, taylor_apply]
  congr 1
  simp only [add_comp, C_comp, mul_comp, X_comp]
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hh, C_1, one_mul, add_comm]

/-- **Differences to jets to differences is the identity on the first `r + 1`**: the jet, read back at `u = x − x₀`,
has step-`h` differences `a_k` at `x₀` for every `k ≤ r`. -/
theorem differences_toJetAtStep (h x₀ : ℚ) (hh : h ≠ 0) (r : ℕ) (a : ℕ → ℚ) {k : ℕ} (hk : k ≤ r) :
    differences h x₀ ((toJetAtStep h r a).comp (X - C x₀)).eval k = a k := by
  rw [differences_eq_staircase]
  have hsamp : (fun m : ℕ => ((toJetAtStep h r a).comp (X - C x₀)).eval (x₀ + m * h))
      = JetStaircase.ofCoefficients r a := by
    funext m
    rw [← newton_eval_natCast, eval_comp, toJetAtStep, eval_comp]
    simp only [eval_sub, eval_X, eval_C, eval_mul]
    rw [add_sub_cancel_left, mul_comm, mul_assoc, mul_inv_cancel₀ hh, mul_one]
  rw [hsamp]
  exact JetStaircase.coefficient_eq_iteratedDelta_at_zero r a k hk

/-- **The jet holds exactly the first `r + 1` differences.** -/
theorem toJetAtStep_eq_iff (h : ℚ) (hh : h ≠ 0) (r : ℕ) (a b : ℕ → ℚ) :
    toJetAtStep h r a = toJetAtStep h r b ↔ ∀ k ≤ r, a k = b k := by
  constructor
  · intro hab k hk
    rw [← differences_toJetAtStep h 0 hh r a hk, ← differences_toJetAtStep h 0 hh r b hk, hab]
  · intro hab
    rw [toJetAtStep, toJetAtStep, newton, newton]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hab k (Nat.lt_succ_iff.mp (mem_range.mp hk))]

/-- **At step one from the base zero the jet is the staircase's Newton jet** at every node. -/
theorem toJetAtStep_one_eval (r : ℕ) (a : ℕ → ℚ) (n : ℕ) :
    (toJetAtStep 1 r a).eval (n : ℚ) = JetStaircase.ofCoefficients r a n := by
  rw [toJetAtStep, inv_one, C_1, one_mul, comp_X, newton_eval_natCast]

end Holonics.Transport.JetAtStep
