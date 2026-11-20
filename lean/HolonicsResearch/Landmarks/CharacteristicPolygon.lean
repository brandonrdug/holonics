import HolonicsResearch.Landmarks.SmithMinors
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The characteristic polygon lies on or above the polygon of the grains

Atlas: `coupling.characteristic-polygon-above-grains`. Record:
`research/records/2026-11-20_A_LATTICE_AN_APERTURE_AND_A_DILATION_ARE_ONE_LENS_…` (§5).

A square matrix over a commutative ring is read two ways. Its grains, the invariant factors `d₁ ∣ d₂ ∣ …` of its
Smith form, are read from its minors: `d₁ ⋯ d_k` is the common divisor of the `k × k` minors, and the two-sided
unimodular class keeps that divisor (`Landmarks/SmithMinors.dvd_minors_unimodular_iff`). Its long-run rates, the
eigenvalues, are read from its characteristic polynomial, which conjugation alone keeps. At a prime `p` each reading
draws a polygon over `0, 1, …, n`: the grains' polygon through the heights `v_p(d₁ ⋯ d_k)`, and the characteristic
polygon, the lower convex hull of the heights `v_p(c_k)` of the coefficients.

1. **Every characteristic height is on or above the grains' height**
   (`dvd_charpoly_coeff_of_dvd_minors`, `pow_dvd_charpoly_coeff`): whatever divides every `k × k` minor divides the
   coefficient `c_k`, since `c_k` is a signed sum of principal `k × k` minors.
2. **The two polygons share their ends** (`charpoly_coeff_card`, `dvd_charpoly_coeff_zero_iff`): `c₀ = 1`, and
   `c_n` is the determinant up to sign, the one `n × n` minor.
3. **Two specimens with the grains `1, 2`** (`mixed`, `sorted`, `mixed_eq_swap_mul_sorted`): a swap of the two
   places joins them, so they have the same minors' divisors (`dvd_minors_mixed_iff_sorted`). `sorted` keeps one
   place and doubles the other at every tick, with characteristic polynomial `X² − 3X + 2`: its polygon is the
   grains' (slopes `0, 1` at the prime two). `mixed` doubles both places every two ticks (`mixed_mul_mixed`), with
   characteristic polynomial `X² − 2` (`mixed_charpoly`): its middle height is that of `0`, so its polygon is the
   straight line of slope one half, above the grains' at the middle. The slopes `½, ½` are the even mix of `0, 1`.

Limits. The polygons, their convexity and the valuation are not stated: the module holds the divisibility that puts
each characteristic height on or above the grains'. The theorems this is the integer form of are named in the
record from training and are not stated: that the Newton polygon of a crystal's Frobenius lies on or above its Hodge
polygon with the same ends (Mazur 1972, Katz 1979), the group form (Rapoport and Richartz 1996), and, over the
reals, that the products of the largest eigenvalue moduli are bounded by the products of the largest singular values
(Weyl 1949).
-/

open Matrix Polynomial

namespace Holonics.Landmarks.CharacteristicPolygon

open Holonics.Landmarks.SmithMinors

/-! ## 1. A characteristic height is on or above the grains' height -/

section Height

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

omit [Fintype n] in
/-- [proved-standard; formal-checked] A principal minor over a set of `k` places is a `k × k` minor in the sense of
`Landmarks/SmithMinors`: a determinant of `M` read through two maps from `Fin k`. -/
theorem principal_minor_eq (M : Matrix n n R) {k : ℕ} {s : Finset n} (hs : s.card = k) :
    ∃ f : Fin k → n, (M.submatrix (Subtype.val : s → n) (Subtype.val : s → n)).det = (M.submatrix f f).det := by
  have hcard : Fintype.card s = k := by rw [Fintype.card_coe, hs]
  let e : s ≃ Fin k := Fintype.equivFinOfCardEq hcard
  refine ⟨fun i => ((e.symm i : s) : n), ?_⟩
  rw [← Matrix.det_submatrix_equiv_self e.symm
    (M.submatrix (Subtype.val : s → n) (Subtype.val : s → n)), Matrix.submatrix_submatrix]
  rfl

/-- [proved-standard; formal-checked] **Whatever divides every `k × k` minor divides the characteristic coefficient
`c_k`**: the coefficient of `X^(n − k)` is a signed sum of the principal `k × k` minors. -/
theorem dvd_charpoly_coeff_of_dvd_minors (M : Matrix n n R) (k : ℕ) (hk : k ≤ Fintype.card n) (c : R)
    (h : ∀ f g : Fin k → n, c ∣ (M.submatrix f g).det) :
    c ∣ M.charpoly.coeff (Fintype.card n - k) := by
  rw [Matrix.charpoly_coeff_eq_sum_minors M k hk]
  refine Dvd.dvd.mul_left (Finset.dvd_sum fun s hs => ?_) _
  obtain ⟨f, hf⟩ := principal_minor_eq M (Finset.mem_powersetCard.mp hs).2
  rw [hf]
  exact h f f

/-- [proved-standard; formal-checked] The same at a prime's power: where `p ^ a` divides every `k × k` minor, the
characteristic height at `k` is at least `a`. -/
theorem pow_dvd_charpoly_coeff (M : Matrix n n R) (k : ℕ) (hk : k ≤ Fintype.card n) (p : R) (a : ℕ)
    (h : ∀ f g : Fin k → n, p ^ a ∣ (M.submatrix f g).det) :
    p ^ a ∣ M.charpoly.coeff (Fintype.card n - k) :=
  dvd_charpoly_coeff_of_dvd_minors M k hk (p ^ a) h

/-! ## 2. The two polygons share their ends -/

/-- [proved-standard; formal-checked] The first end: the leading coefficient is one. -/
theorem charpoly_coeff_card [Nontrivial R] (M : Matrix n n R) : M.charpoly.coeff (Fintype.card n) = 1 := by
  have h := (Matrix.charpoly_monic M).coeff_natDegree
  rwa [Matrix.charpoly_natDegree_eq_dim] at h

/-- [proved-standard; formal-checked] The last end: the constant coefficient is the determinant up to sign, the one
`n × n` minor, so the same things divide both. -/
theorem dvd_charpoly_coeff_zero_iff (M : Matrix n n R) (c : R) : c ∣ M.charpoly.coeff 0 ↔ c ∣ M.det := by
  rw [Matrix.det_eq_sign_charpoly_coeff M]
  exact ((isUnit_one.neg.pow (Fintype.card n)).dvd_mul_left).symm

end Height

/-! ## 3. Two specimens with the grains one and two -/

/-- The specimen that swaps its two places and doubles one of them. -/
def mixed : Matrix (Fin 2) (Fin 2) ℤ := !![0, 2; 1, 0]

/-- The specimen that keeps one place and doubles the other. -/
def sorted : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 2]

/-- The swap of the two places. -/
def swap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- [proved-standard; formal-checked] The swap is unimodular. -/
theorem isUnit_det_swap : IsUnit swap.det := by
  have h : swap.det = -1 := by simp [swap, Matrix.det_fin_two]
  rw [h]
  exact isUnit_one.neg

/-- [proved-standard; formal-checked] The two specimens are joined by the swap. -/
theorem mixed_eq_swap_mul_sorted : mixed = swap * sorted := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mixed, swap, sorted, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **The two specimens have the same grains**: the same things divide the
`k × k` minors of each, for every `k`. -/
theorem dvd_minors_mixed_iff_sorted (k : ℕ) (c : ℤ) :
    (∀ f g : Fin k → Fin 2, c ∣ (mixed.submatrix f g).det) ↔
      ∀ f g : Fin k → Fin 2, c ∣ (sorted.submatrix f g).det := by
  rw [mixed_eq_swap_mul_sorted]
  constructor
  · intro h f g
    have hinv : sorted = swap * (swap * sorted) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swap, sorted, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hinv]
    exact dvd_minor_mul_left swap (swap * sorted) c h f g
  · intro h f g
    exact dvd_minor_mul_left swap sorted c h f g

/-- [proved-standard; formal-checked] **Two ticks of the mixed specimen double both places.** -/
theorem mixed_mul_mixed : mixed * mixed = 2 • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mixed, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] The mixed specimen's characteristic polynomial is `X² − 2`: its middle
coefficient is zero, so its polygon at the prime two is the straight line of slope one half. -/
theorem mixed_charpoly : mixed.charpoly = X ^ 2 - C 2 := by
  rw [Matrix.charpoly_fin_two]
  simp [mixed, Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

/-- [proved-standard; formal-checked] The sorted specimen's characteristic polynomial is `X² − 3X + 2`: its middle
coefficient is a unit at the prime two, so its polygon is the grains', with slopes zero and one. -/
theorem sorted_charpoly : sorted.charpoly = X ^ 2 - C 3 * X + C 2 := by
  rw [Matrix.charpoly_fin_two]
  simp [sorted, Matrix.trace_fin_two, Matrix.det_fin_two]

/-- [counterexample; formal-checked] **The same grains do not fix the rates**: the two specimens have the same
divisors of their minors and different characteristic middle coefficients, zero against minus three. -/
theorem same_grains_different_rates :
    (∀ (k : ℕ) (c : ℤ), (∀ f g : Fin k → Fin 2, c ∣ (mixed.submatrix f g).det) ↔
        ∀ f g : Fin k → Fin 2, c ∣ (sorted.submatrix f g).det) ∧
      mixed.charpoly.coeff 1 = 0 ∧ sorted.charpoly.coeff 1 = -3 := by
  refine ⟨dvd_minors_mixed_iff_sorted, ?_, ?_⟩
  · rw [mixed_charpoly]
    simp [Polynomial.coeff_X_pow]
  · rw [sorted_charpoly]
    simp [Polynomial.coeff_X_pow]

end Holonics.Landmarks.CharacteristicPolygon
