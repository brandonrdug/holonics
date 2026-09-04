import ElementaryHolonics.Mathematics.JacobiEulerDerivative

/-!
# A finite diagonal receiver for the differentiated Jacobi body

The Jacobi kernel retains an outer power coordinate `q^n` and an oriented
Laurent coordinate `T^m`.  The exact substitution face `T = -q` sends an
occurrence to diagonal degree `n + m` and multiplies it by the parity of the
orientation.  This file constructs that operation without an analytic
evaluation: each requested degree is read through its complete finite root
population.

On the differentiated Jacobi source, the coefficient support is

`n = |m|²`,

so a diagonal occurrence at degree `d` obeys `m² + m = d`.  At
`d = k(k+1)` there are exactly two occurrences, `m = k` and `m = -k-1`.
Their oppositely oriented currents add to Jacobi's exact weight
`(-1)^k(2k+1)`.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.JacobiFiniteDiagonalReceiver

open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel
open Soma.Holonics.Mathematics.JacobiEulerDerivative

/-- The complete finite population of orientations reaching diagonal degree
`d` from the differentiated Jacobi source.  The interval is a presentation
bound; `diagonalRoot_mem_box` proves that it excludes no root. -/
def diagonalRootPopulation (d : ℕ) : Finset ℤ :=
  (Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1)).filter fun m =>
    m ^ 2 + m = (d : ℤ)

def diagonalOrientationWeight (m : ℤ) : ℤ :=
  (-1 : ℤ) ^ m.natAbs * m

/-- The returned signed current at one diagonal degree. -/
def diagonalRootCurrent (d : ℕ) : ℤ :=
  ∑ m ∈ diagonalRootPopulation d, diagonalOrientationWeight m

/-- The exact finite coefficient face of the formal substitution `T = -q`
at diagonal degree `d`.  Each occurrence retains its Laurent orientation;
the outer exponent is reconstructed as `d-m`.  Negative reconstructed outer
degrees are refused rather than coerced to degree zero. -/
def finiteDiagonalReceiver (d : ℕ) (F : BivariateSeries) : ℤ :=
  ∑ m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1),
    if 0 ≤ (d : ℤ) - m then
      (-1 : ℤ) ^ m.natAbs *
        (AddMonoidAlgebra.coeff
          (PowerSeries.coeff (((d : ℤ) - m).toNat) F)) m
    else 0

/-- Exact coefficient support of the Jacobi source before differentiation. -/
theorem coeff_coeff_rhs (n : ℕ) (m : ℤ) :
    (AddMonoidAlgebra.coeff (PowerSeries.coeff n rhs)) m =
      if n = m.natAbs ^ 2 then 1 else 0 := by
  letI : UniformSpace (LaurentPolynomial ℤ) := ⊥
  letI : TopologicalSpace (ℤ →₀ ℤ) := ⊥
  letI := piTop
  unfold rhs
  rw [(summable_rhs_terms).map_tsum (PowerSeries.coeff n)
    (PowerSeries.WithPiTopology.continuous_coeff _ n)]
  let coeffTerm : ℤ → LaurentPolynomial ℤ := fun i =>
      PowerSeries.coeff n
        (PowerSeries.C (LaurentPolynomial.T i) * q ^ i.natAbs ^ 2)
  have hsummable : Summable coeffTerm :=
    (summable_rhs_terms).map (PowerSeries.coeff n)
      (PowerSeries.WithPiTopology.continuous_coeff _ n)
  let coeffAt : LaurentPolynomial ℤ →+ ℤ :=
    { toFun := fun f => (AddMonoidAlgebra.coeff (R := ℤ) (M := ℤ) f) m
      map_zero' := by
        change (AddMonoidAlgebra.coeff (R := ℤ) (M := ℤ)
            (0 : LaurentPolynomial ℤ)) m = 0
        simp
      map_add' := by
        intro f g
        change (AddMonoidAlgebra.coeff (R := ℤ) (M := ℤ) (f + g)) m =
          (AddMonoidAlgebra.coeff (R := ℤ) (M := ℤ) f) m +
            (AddMonoidAlgebra.coeff (R := ℤ) (M := ℤ) g) m
        simp }
  change coeffAt (∑' i : ℤ, coeffTerm i) = _
  have hmap : coeffAt (∑' i : ℤ, coeffTerm i) =
      ∑' i : ℤ, coeffAt (coeffTerm i) := by
    exact hsummable.map_tsum coeffAt
      continuous_of_discreteTopology
  rw [hmap]
  unfold coeffTerm
  simp only [PowerSeries.coeff_C_mul_X_pow]
  rw [tsum_eq_single m]
  · by_cases hnm : n = m.natAbs ^ 2
    · simp only [if_pos hnm]
      dsimp [coeffAt]
      change (Finsupp.single m 1) m = 1
      simp
    · simp only [if_neg hnm]
      simp [coeffAt]
  · intro b hb
    by_cases hnb : n = b.natAbs ^ 2
    · simp only [if_pos hnb]
      dsimp [coeffAt]
      change (Finsupp.single b 1) m = 0
      exact Finsupp.single_eq_of_ne (Ne.symm hb)
    · simp only [if_neg hnb]
      simp [coeffAt]

/-- Euler differentiation returns the signed orientation on precisely the
square-supported coefficient and returns zero elsewhere. -/
theorem coeff_coeff_euler_rhs (n : ℕ) (m : ℤ) :
    (AddMonoidAlgebra.coeff
      (PowerSeries.coeff n (bivariateEulerDerivative rhs))) m =
      if n = m.natAbs ^ 2 then m else 0 := by
  rw [coeff_bivariateEulerDerivative, coeff_laurentEulerDerivative,
    coeff_coeff_rhs]
  split_ifs <;> ring

private theorem natAbs_square_cast (m : ℤ) :
    ((m.natAbs ^ 2 : ℕ) : ℤ) = m ^ 2 := by
  simp

/-- Reconstructing the outer exponent on a nonnegative diagonal passage is
equivalent to the integer root equation carried by that occurrence. -/
theorem diagonal_outer_eq_square_iff (d : ℕ) (m : ℤ)
    (hnonneg : 0 ≤ (d : ℤ) - m) :
    ((d : ℤ) - m).toNat = m.natAbs ^ 2 ↔
      m ^ 2 + m = (d : ℤ) := by
  constructor
  · intro h
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) h
    change (((d : ℤ) - m).toNat : ℤ) =
      ((m.natAbs ^ 2 : ℕ) : ℤ) at hcast
    rw [Int.toNat_of_nonneg hnonneg, natAbs_square_cast] at hcast
    linarith
  · intro h
    apply Int.ofNat_injective
    simp only [Int.ofNat_eq_natCast]
    rw [Int.toNat_of_nonneg hnonneg, natAbs_square_cast]
    linarith

/-- The finite diagonal receiver reads precisely the complete root current of
the differentiated Jacobi source. -/
theorem finiteDiagonalReceiver_euler_rhs (d : ℕ) :
    finiteDiagonalReceiver d (bivariateEulerDerivative rhs) =
      diagonalRootCurrent d := by
  rw [finiteDiagonalReceiver, diagonalRootCurrent, diagonalRootPopulation,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  rw [coeff_coeff_euler_rhs]
  by_cases hnonneg : 0 ≤ (d : ℤ) - m
  · rw [if_pos hnonneg]
    by_cases hroot : m ^ 2 + m = (d : ℤ)
    · rw [if_pos hroot,
        if_pos ((diagonal_outer_eq_square_iff d m hnonneg).mpr hroot)]
      rfl
    · rw [if_neg hroot,
        if_neg (not_congr (diagonal_outer_eq_square_iff d m hnonneg) |>.mpr hroot)]
      ring
  · rw [if_neg hnonneg]
    have hnotroot : m ^ 2 + m ≠ (d : ℤ) := by
      intro hroot
      apply hnonneg
      have hsquare : 0 ≤ m ^ 2 := sq_nonneg m
      linarith
    rw [if_neg hnotroot]

/-- The checked Jacobi equality commutes with every finite diagonal receiver. -/
theorem jacobi_euler_finiteDiagonalReceiver (d : ℕ) :
    finiteDiagonalReceiver d (bivariateEulerDerivative lhs) =
      finiteDiagonalReceiver d (bivariateEulerDerivative rhs) := by
  exact congrArg (finiteDiagonalReceiver d)
    jacobi_triple_product_euler_derivative

/-- **THE PRODUCT SIDE RETURNS THE COMPLETE DIAGONAL ROOT CURRENT.** -/
theorem finiteDiagonalReceiver_euler_lhs (d : ℕ) :
    finiteDiagonalReceiver d (bivariateEulerDerivative lhs) =
      diagonalRootCurrent d := by
  rw [jacobi_euler_finiteDiagonalReceiver,
    finiteDiagonalReceiver_euler_rhs]

/-- The integer quadratic furnishing the diagonal has exactly the reflected
pair of roots. -/
theorem triangular_diagonal_roots (m : ℤ) (k : ℕ) :
    m ^ 2 + m = (k : ℤ) ^ 2 + k ↔
      m = (k : ℤ) ∨ m = -(k : ℤ) - 1 := by
  constructor
  · intro h
    have hfactor : (m - (k : ℤ)) * (m + (k : ℤ) + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hleft | hright
    · left
      linarith
    · right
      linarith
  · rintro (rfl | rfl) <;> ring

private theorem diagonalRoot_mem_box {d : ℕ} {m : ℤ}
    (hroot : m ^ 2 + m = (d : ℤ)) :
    m ∈ Finset.Icc (-((d : ℤ) + 1)) ((d : ℤ) + 1) := by
  rw [Finset.mem_Icc]
  constructor
  · by_cases hm : 0 ≤ m
    · omega
    · have hm' : m ≤ -1 := by omega
      have hnonneg : 0 ≤ (-m - 1) ^ 2 := sq_nonneg (-m - 1)
      nlinarith
  · by_cases hm : m ≤ 0
    · have hd : 0 ≤ (d : ℤ) := by positivity
      linarith
    · have hm' : 1 ≤ m := by omega
      have hnonneg : 0 ≤ (m - 1) ^ 2 := sq_nonneg (m - 1)
      nlinarith

/-- At triangular diagonal degree the complete population is the two
reflection-related orientations and nothing else. -/
theorem diagonalRootPopulation_triangular (k : ℕ) :
    diagonalRootPopulation (k ^ 2 + k) =
      {(k : ℤ), -(k : ℤ) - 1} := by
  ext m
  simp only [diagonalRootPopulation, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact (triangular_diagonal_roots m k).mp (by
      simpa only [Nat.cast_add, Nat.cast_pow] using h.2)
  · intro h
    refine ⟨?_, ?_⟩
    · apply diagonalRoot_mem_box
      rcases h with rfl | rfl <;> push_cast <;> ring
    · rcases h with rfl | rfl <;> push_cast <;> ring

/-- **THE TWO DIAGONAL OCCURRENCES RETURN JACOBI'S WEIGHT.** -/
theorem diagonalRootCurrent_triangular (k : ℕ) :
    diagonalRootCurrent (k ^ 2 + k) =
      (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) := by
  rw [diagonalRootCurrent, diagonalRootPopulation_triangular]
  have hdistinct : (k : ℤ) ≠ -(k : ℤ) - 1 := by omega
  rw [Finset.sum_insert]
  · simp only [Finset.sum_singleton]
    change diagonalOrientationWeight (k : ℤ) +
        diagonalOrientationWeight (-(k : ℤ) - 1) = _
    simp only [diagonalOrientationWeight]
    have hnatAbsPositive : (k : ℤ).natAbs = k := by simp
    have hnegative : -(k : ℤ) - 1 = Int.negSucc k := by
      omega
    have hnatAbsNegative : (-(k : ℤ) - 1).natAbs = k + 1 := by
      rw [hnegative]
      exact rfl
    rw [hnatAbsPositive, hnatAbsNegative, pow_succ]
    ring
  · simpa only [Finset.mem_singleton] using hdistinct

/-- The differentiated Jacobi product itself returns the exact signed
triangular current on every diagonal.  This is the closed source-to-receiver
square needed by the subsequent Tunnell exponent regrading. -/
theorem finiteDiagonalReceiver_euler_lhs_triangular (k : ℕ) :
    finiteDiagonalReceiver (k ^ 2 + k) (bivariateEulerDerivative lhs) =
      (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) := by
  rw [finiteDiagonalReceiver_euler_lhs, diagonalRootCurrent_triangular]

#print axioms coeff_coeff_rhs
#print axioms coeff_coeff_euler_rhs
#print axioms finiteDiagonalReceiver_euler_rhs
#print axioms jacobi_euler_finiteDiagonalReceiver
#print axioms finiteDiagonalReceiver_euler_lhs
#print axioms triangular_diagonal_roots
#print axioms diagonalRootPopulation_triangular
#print axioms diagonalRootCurrent_triangular
#print axioms finiteDiagonalReceiver_euler_lhs_triangular

end Soma.Holonics.Mathematics.JacobiFiniteDiagonalReceiver
