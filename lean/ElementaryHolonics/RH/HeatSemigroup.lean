import ElementaryHolonics.RH.ForwardPreservation

/-!
# The semigroup of the backward heat flow, and monotonicity of the pair count

On polynomials `e^{−sD²} e^{−tD²} p = e^{−(s+t)D²} p`, by the Cauchy product of the exponential
coefficients `Σ_{j+k=l} (−s)^j/j! · (−t)^k/k! = (−(s+t))^l/l!`.  Hence for `0 ≤ t ≤ t′` the
non-real root count of `e^{−t′D²} p` is at most that of `e^{−tD²} p`: along the flow the pair
population is non-increasing.  This is the exact sense in which the Riemann hypothesis, at the
polynomial face of its flow, is a statement about the face `t = 0` alone.
-/

open Polynomial Finset
open Soma.Holonics.RH.PolyaStep
open Soma.Holonics.RH.PairDescent
open Soma.Holonics.RH.ForwardPreservation

namespace Soma.Holonics.RH.HeatSemigroup

/-- The flow truncated at any bound of the degree. -/
theorem heatR_eq_sum_of_le {p : ℝ[X]} {m : ℕ} (hm : p.natDegree ≤ m) (t : ℝ) :
    heatR t p = ∑ k ∈ range (m + 1), ((-t) ^ k / (k.factorial : ℝ)) • derivative^[2 * k] p := by
  unfold heatR
  simp only [C_mul']
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hm))
  intro k _ hk'
  have hk'' : p.natDegree + 1 ≤ k := by simpa [Finset.mem_range] using hk'
  rw [iterate_derivative_eq_zero (by omega : p.natDegree < 2 * k), smul_zero]

/-- The Cauchy product of the exponential coefficients. -/
theorem scalar_cauchy (s t : ℝ) (l : ℕ) :
    ∑ j ∈ range (l + 1), ((-s) ^ j / (j.factorial : ℝ)) * ((-t) ^ (l - j) / ((l - j).factorial : ℝ)) =
      (-(s + t)) ^ l / (l.factorial : ℝ) := by
  have h := add_pow (-s) (-t) l
  rw [show (-s + -t) = -(s + t) by ring] at h
  rw [h, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : j ≤ l)
  have hfac' : ((l.choose j : ℕ) : ℝ) * (j.factorial : ℝ) * ((l - j).factorial : ℝ) =
      (l.factorial : ℝ) := by exact_mod_cast hfac
  have hj0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hlj0 : ((l - j).factorial : ℝ) ≠ 0 := by exact_mod_cast (l - j).factorial_ne_zero
  have hl0 : (l.factorial : ℝ) ≠ 0 := by exact_mod_cast l.factorial_ne_zero
  have hC : ((l.choose j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega : j ≤ l)).ne'
  rw [← hfac']
  field_simp

/-- The semigroup: `e^{−sD²} e^{−tD²} = e^{−(s+t)D²}` on polynomials. -/
theorem heatR_heatR (s t : ℝ) (p : ℝ[X]) : heatR s (heatR t p) = heatR (s + t) p := by
  set f : ℕ → ℕ → ℝ[X] := fun j k =>
    (((-s) ^ j / (j.factorial : ℝ)) * ((-t) ^ k / (k.factorial : ℝ))) • derivative^[2 * (j + k)] p
    with hf
  have hvan : ∀ j k, p.natDegree < j + k → f j k = 0 := by
    intro j k hjk
    simp only [hf]
    rw [iterate_derivative_eq_zero (by omega : p.natDegree < 2 * (j + k)), smul_zero]
  have h1 : heatR s (heatR t p) =
      ∑ j ∈ range (p.natDegree + 1), ∑ k ∈ range (p.natDegree + 1), f j k := by
    rw [heatR_eq_sum_of_le (natDegree_heatR_le t p), heatR_eq_sum_of_le le_rfl]
    apply Finset.sum_congr rfl
    intro j _
    rw [iterate_derivative_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [iterate_derivative_smul, smul_smul, ← Function.iterate_add_apply, ← mul_add]
  have h2 : ∀ j ∈ range (p.natDegree + 1),
      ∑ k ∈ range (p.natDegree + 1), f j k = ∑ k ∈ range (p.natDegree + 1 - j), f j k := by
    intro j hj
    rw [Finset.mem_range] at hj
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.sub_le _ _))
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    exact hvan j k (by omega)
  rw [h1, Finset.sum_congr rfl h2, ← Finset.sum_range_diag_flip, heatR_eq_sum_of_le le_rfl]
  apply Finset.sum_congr rfl
  intro l _
  have h3 : ∀ k ∈ range (l + 1), f k (l - k) =
      (((-s) ^ k / (k.factorial : ℝ)) * ((-t) ^ (l - k) / ((l - k).factorial : ℝ))) •
        derivative^[2 * l] p := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [hf]
    rw [Nat.add_sub_cancel' (by omega : k ≤ l)]
  rw [Finset.sum_congr rfl h3, ← Finset.sum_smul, scalar_cauchy]

theorem heatR_zero (p : ℝ[X]) : heatR 0 p = p := by
  unfold heatR
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

/-- The flow is a group: `e^{tD²}` inverts `e^{−tD²}` on polynomials. -/
theorem heatR_neg_heatR (t : ℝ) (p : ℝ[X]) : heatR (-t) (heatR t p) = p := by
  rw [heatR_heatR, neg_add_cancel, heatR_zero]

theorem heatR_injective (t : ℝ) : Function.Injective (heatR t) := fun p q h => by
  rw [← heatR_neg_heatR t p, h, heatR_neg_heatR]

/-- Monotonicity of the pair count along the flow. -/
theorem nonreal_heatR_antitone {t t' : ℝ} (h : t ≤ t') (p : ℝ[X]) :
    nonreal (heatR t' p) ≤ nonreal (heatR t p) := by
  have : heatR t' p = heatR (t' - t) (heatR t p) := by rw [heatR_heatR, sub_add_cancel]
  rw [this]
  exact nonreal_heatR_le (sub_nonneg.mpr h) _

/-- Once the population is empty it stays empty: real-rootedness is absorbing. -/
theorem nonreal_heatR_eq_zero_of_le {t t' : ℝ} (h : t ≤ t') {p : ℝ[X]}
    (h0 : nonreal (heatR t p) = 0) : nonreal (heatR t' p) = 0 :=
  Nat.le_zero.mp (h0 ▸ nonreal_heatR_antitone h p)

end Soma.Holonics.RH.HeatSemigroup
