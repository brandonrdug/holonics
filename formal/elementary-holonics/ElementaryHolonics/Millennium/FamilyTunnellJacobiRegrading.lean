import ElementaryHolonics.Millennium.FamilyTunnellJacobiOrientation

/-!
# Exact Jacobi regrading of the Tunnell orientation current

The ordinary Jacobi triangular index does not introduce a new population.  It
is the natural-number chart of the integer orientation parameter retained in
`FamilyTunnellJacobiOrientation`:

`t : ℤ  ↔  k = Equiv.intEquivNat t : ℕ`.

Under that chart, both the signed coordinate and its square return exactly

`4t+1 = (-1)^k(2k+1)` and `(4t+1)^2 = 1 + 8 T_k`.

This file proves those identities, constructs the induced equivalence on every
finite coefficient population, and returns equality of the complete formal
power series.  It is the exact substitution passage from the quarter-residue
theta current to Jacobi's triangular identity.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiRegrading

open Finset
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor
open Soma.Holonics.Millennium.FamilyTunnellJacobiOrientation

/-- The triangular exponent `T_k = k(k+1)/2`. -/
def triangularIndex (k : ℕ) : ℕ := (k ^ 2 + k) / 2

theorem two_mul_triangularIndex (k : ℕ) :
    2 * triangularIndex k = k ^ 2 + k := by
  unfold triangularIndex
  rw [Nat.two_mul_div_two_of_even]
  have hfactor : k ^ 2 + k = k * (k + 1) := by ring
  rw [hfactor]
  exact Nat.even_mul_succ_self k

@[simp] theorem orientationIndex_ofNat (n : ℕ) :
    Equiv.intEquivNat (Int.ofNat n) = 2 * n := by
  change Equiv.natSumNatEquivNat (Sum.inl n) = 2 * n
  rw [Equiv.natSumNatEquivNat_apply]
  rfl

@[simp] theorem orientationIndex_negSucc (n : ℕ) :
    Equiv.intEquivNat (Int.negSucc n) = 2 * n + 1 := by
  change Equiv.natSumNatEquivNat (Sum.inr n) = 2 * n + 1
  rw [Equiv.natSumNatEquivNat_apply]
  rfl

/-- The sign in Jacobi's identity is precisely the orientation of the
quarter-residue coordinate. -/
theorem orientedCoordinate_eq_jacobiWeight (t : ℤ) :
    4 * t + 1 = (-1 : ℤ) ^ (Equiv.intEquivNat t) *
      (2 * (Equiv.intEquivNat t : ℤ) + 1) := by
  cases t with
  | ofNat n =>
      rw [orientationIndex_ofNat]
      push_cast
      rw [show (-1 : ℤ) ^ (2 * n) = 1 by simp [pow_mul]]
      simp
      ring
  | negSucc n =>
      rw [orientationIndex_negSucc]
      push_cast
      rw [show (-1 : ℤ) ^ (2 * n + 1) = -1 by
        simp [pow_succ, pow_mul]]
      simp [Int.negSucc_eq]
      ring

/-- Squaring the oriented coordinate is exactly the affine eight-fold
regrading of the triangular index. -/
theorem orientedSquare_eq_shiftedTriangular (t : ℤ) :
    (4 * t + 1) ^ 2 =
      1 + 8 * (triangularIndex (Equiv.intEquivNat t) : ℤ) := by
  cases t with
  | ofNat n =>
      rw [orientationIndex_ofNat]
      have h := two_mul_triangularIndex (2 * n)
      push_cast at h ⊢
      simp
      nlinarith
  | negSucc n =>
      rw [orientationIndex_negSucc]
      have h := two_mul_triangularIndex (2 * n + 1)
      push_cast at h ⊢
      simp [Int.negSucc_eq]
      nlinarith

/-- The Jacobi indices contributing to the already shifted square coefficient
`n`.  The range is only a finite presentation; the next lemmas prove it omits
no occurrence. -/
def shiftedTriangularPopulation (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun k =>
    1 + 8 * triangularIndex k = n

private theorem triangularIndex_ge_index {k : ℕ} (hk : 0 < k) :
    k ≤ triangularIndex k := by
  have htwo := two_mul_triangularIndex k
  have hsq : k ≤ k ^ 2 := by
    nlinarith
  nlinarith

private theorem shifted_index_mem_range {n k : ℕ}
    (hshift : 1 + 8 * triangularIndex k = n) :
    k ∈ Finset.range (n + 1) := by
  rw [Finset.mem_range]
  by_cases hk : k = 0
  · subst k
    omega
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hle := triangularIndex_ge_index hkpos
    omega

private theorem coordinate_mem_square_box {n : ℕ} {x : ℤ}
    (hsquare : x ^ 2 = (n : ℤ)) :
    x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  simp only [Finset.mem_Icc]
  constructor
  · by_cases hx : 0 ≤ x
    · have hn : 0 ≤ (n : ℤ) := by positivity
      linarith
    · have hxneg : x ≤ -1 := by omega
      have hprod : 0 ≤ (-x) * (-x - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  · by_cases hx : x ≤ 0
    · have hn : 0 ≤ (n : ℤ) := by positivity
      linarith
    · have hxpos : 1 ≤ x := by omega
      have hprod : 0 ≤ x * (x - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith

private theorem orientation_to_shifted_mem {n : ℕ} {t : ℤ}
    (ht : t ∈ jacobiOrientationPopulation n) :
    Equiv.intEquivNat t ∈ shiftedTriangularPopulation n := by
  rcases Finset.mem_image.mp ht with ⟨x, hx, hxt⟩
  have hxSquare := (Finset.mem_filter.mp hx).2.1
  have hxReconstruct : 4 * (x / 4) + 1 = x := by
    have hxResidueZMod := (Finset.mem_filter.mp hx).2.2
    have hxResidue : x % 4 = 1 :=
      (intCast_zmod_four_eq_one_iff_emod x).mp (by simpa using hxResidueZMod)
    have hdivision : x % 4 + 4 * (x / 4) = x :=
      Int.emod_add_mul_ediv x 4
    omega
  rw [shiftedTriangularPopulation, Finset.mem_filter]
  have hcoordinate : 4 * t + 1 = x := by
    rw [← hxt]
    exact hxReconstruct
  have hsquare := orientedSquare_eq_shiftedTriangular t
  rw [hcoordinate] at hsquare
  have hshiftZ :
      1 + 8 * (triangularIndex (Equiv.intEquivNat t) : ℤ) = (n : ℤ) :=
    hsquare.symm.trans hxSquare
  have hshiftN :
      1 + 8 * triangularIndex (Equiv.intEquivNat t) = n := by
    exact_mod_cast hshiftZ
  constructor
  · exact shifted_index_mem_range hshiftN
  · exact hshiftN

private theorem shifted_to_orientation_mem {n k : ℕ}
    (hk : k ∈ shiftedTriangularPopulation n) :
    Equiv.intEquivNat.symm k ∈ jacobiOrientationPopulation n := by
  have hshift := (Finset.mem_filter.mp hk).2
  let t : ℤ := Equiv.intEquivNat.symm k
  let x : ℤ := 4 * t + 1
  have hindex : Equiv.intEquivNat t = k := by
    exact Equiv.apply_symm_apply Equiv.intEquivNat k
  have hsquare : x ^ 2 = (n : ℤ) := by
    rw [show x = 4 * t + 1 by rfl, orientedSquare_eq_shiftedTriangular,
      hindex]
    exact_mod_cast hshift
  have hxQuarter : x ∈ quarterSquarePopulation 1 n := by
    rw [quarterSquarePopulation, Finset.mem_filter]
    refine ⟨coordinate_mem_square_box hsquare, hsquare, ?_⟩
    apply (intCast_zmod_four_eq_one_iff_emod x).mpr
    rw [show x = 4 * t + 1 by rfl]
    omega
  rw [jacobiOrientationPopulation, Finset.mem_image]
  refine ⟨x, hxQuarter, ?_⟩
  change x / 4 = t
  rw [show x = 4 * t + 1 by rfl]
  omega

/-- Complete coefficient-population equivalence induced by `ℤ ≃ ℕ`. -/
def jacobiOrientationEquivShiftedTriangular (n : ℕ) :
    {t // t ∈ jacobiOrientationPopulation n} ≃
      {k // k ∈ shiftedTriangularPopulation n} where
  toFun t := ⟨Equiv.intEquivNat t.1, orientation_to_shifted_mem t.2⟩
  invFun k := ⟨Equiv.intEquivNat.symm k.1, shifted_to_orientation_mem k.2⟩
  left_inv t := by
    apply Subtype.ext
    exact Equiv.symm_apply_apply Equiv.intEquivNat t.1
  right_inv k := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply Equiv.intEquivNat k.1

def jacobiTriangularWeight (k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1)

/-- Jacobi's triangular series already transported to the Tunnell square
exponent chart `n = 1 + 8 T_k`. -/
def shiftedJacobiTriangularTheta : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ k ∈ shiftedTriangularPopulation n, jacobiTriangularWeight k

@[simp] theorem coeff_shiftedJacobiTriangularTheta (n : ℕ) :
    PowerSeries.coeff n shiftedJacobiTriangularTheta =
      ∑ k ∈ shiftedTriangularPopulation n, jacobiTriangularWeight k := by
  simp [shiftedJacobiTriangularTheta]

theorem sum_orientation_eq_shiftedTriangular (n : ℕ) :
    (∑ t ∈ jacobiOrientationPopulation n, (4 * t + 1)) =
      ∑ k ∈ shiftedTriangularPopulation n, jacobiTriangularWeight k := by
  refine Finset.sum_bij
    (i := fun t (_ : t ∈ jacobiOrientationPopulation n) =>
      Equiv.intEquivNat t) ?_ ?_ ?_ ?_
  · intro t ht
    exact orientation_to_shifted_mem ht
  · intro t₁ ht₁ t₂ ht₂ h
    exact Equiv.intEquivNat.injective h
  · intro k hk
    refine ⟨Equiv.intEquivNat.symm k, shifted_to_orientation_mem hk, ?_⟩
    exact Equiv.apply_symm_apply Equiv.intEquivNat k
  · intro t ht
    exact orientedCoordinate_eq_jacobiWeight t

/-- **EXACT JACOBI REGRADING.**  The oriented quarter-residue theta current is
the affine eight-fold triangular Jacobi stream, coefficient by coefficient and
with a complete equivalence of occurrences. -/
theorem jacobiOrientedTheta_eq_shiftedJacobiTriangularTheta :
    jacobiOrientedTheta = shiftedJacobiTriangularTheta := by
  apply PowerSeries.ext
  intro n
  simp [sum_orientation_eq_shiftedTriangular]

theorem weightedQuarterSquareTheta_eq_shiftedJacobiTriangularTheta :
    weightedQuarterSquareTheta 1 = shiftedJacobiTriangularTheta := by
  rw [← jacobiOrientedTheta_eq_weightedQuarterSquareTheta,
    jacobiOrientedTheta_eq_shiftedJacobiTriangularTheta]

#print axioms orientedCoordinate_eq_jacobiWeight
#print axioms orientedSquare_eq_shiftedTriangular
#print axioms jacobiOrientationEquivShiftedTriangular
#print axioms weightedQuarterSquareTheta_eq_shiftedJacobiTriangularTheta

end Soma.Holonics.Millennium.FamilyTunnellJacobiRegrading
