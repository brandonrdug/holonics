import ElementaryHolonics.Millennium.FamilyTunnellProjectiveNeighbors

/-!
# Exact projective zeros of a binary quadratic form

This file constructs the missing finite incidence theorem used by ternary
`p`-neighbor intersections.  For

`F(x,y)=A x²+Bxy+C y²`

over an odd prime field, its projective zero population has signed cardinal

`1+χ(B²-4AC)`.

The proof retains the affine chart `(1,t)` and its infinity chart `(0,1)`.  When
`C≠0`, completing the square is implemented as the exact swing
`t ↦ 2Ct+B`; when `C=0`, the linear and double-root cases are proved directly.
No finite-geometry or conic package is assumed.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyProjectiveBinaryQuadratic

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- Affine roots `(1,t)`. -/
def binaryAffineZeros (A B C : ZMod p) : Finset (ZMod p) :=
  univ.filter fun t => A + B * t + C * t ^ 2 = 0

/-- The infinity direction `(0,1)` occurs exactly when `C=0`. -/
def binaryInfinityZeros (C : ZMod p) : Finset Unit :=
  if C = 0 then {()} else ∅

/-- The two disjoint projective charts. -/
def binaryProjectiveZeros (A B C : ZMod p) : Finset (ZMod p ⊕ Unit) :=
  (binaryAffineZeros A B C).disjSum (binaryInfinityZeros C)

/-- The discriminant receiver of the homogeneous binary form. -/
def binaryDiscriminant (A B C : ZMod p) : ZMod p := B ^ 2 - 4 * A * C

private def completeSquareForward (B C t : ZMod p) : ZMod p :=
  2 * C * t + B

private def completeSquareInverse (B C u : ZMod p) : ZMod p :=
  (u - B) / (2 * C)

private theorem binaryAffineZeros_card_eq_squareRoots (hp2 : p ≠ 2)
    (A B : ZMod p) {C : ZMod p} (hC : C ≠ 0) :
    (binaryAffineZeros A B C).card =
      (univ.filter fun u : ZMod p => u ^ 2 = binaryDiscriminant A B C).card := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hchar
  have h2C : (2 : ZMod p) * C ≠ 0 := mul_ne_zero h2 hC
  refine Finset.card_nbij'
    (completeSquareForward B C) (completeSquareInverse B C) ?_ ?_ ?_ ?_
  · intro t ht
    have ht' : A + B * t + C * t ^ 2 = 0 := by
      simpa [binaryAffineZeros] using ht
    rw [Finset.mem_coe, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, completeSquareForward,
      binaryDiscriminant]
    linear_combination 4 * C * ht'
  · intro u hu
    have hu' : u ^ 2 = B ^ 2 - 4 * A * C := by
      have h := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      simpa [binaryDiscriminant] using h
    rw [Finset.mem_coe]
    simp only [binaryAffineZeros, Finset.mem_filter, Finset.mem_univ, true_and,
      completeSquareInverse]
    field_simp
    linear_combination hu'
  · intro t ht
    dsimp [completeSquareForward, completeSquareInverse]
    field_simp
    ring
  · intro u hu
    dsimp [completeSquareForward, completeSquareInverse]
    field_simp
    ring

private theorem binaryAffineZeros_eq_singleton_of_C_zero {A B : ZMod p}
    (hB : B ≠ 0) :
    binaryAffineZeros A B 0 = {-A / B} := by
  ext t
  simp only [binaryAffineZeros, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor <;> intro h
  · field_simp
    linear_combination h
  · rw [h]
    field_simp
    ring

private theorem binaryAffineZeros_eq_empty_of_BC_zero {A : ZMod p}
    (hA : A ≠ 0) : binaryAffineZeros A 0 0 = ∅ := by
  ext t
  simp [binaryAffineZeros, hA]

/-- **PROJECTIVE BINARY-QUADRATIC ROOT COUNT.**

The result is stated in `ℤ` so the quadratic character remains typed and no
subtraction is truncated in `ℕ`. -/
theorem binaryProjectiveZeros_card_cast (hp2 : p ≠ 2)
    {A B C : ZMod p} (hnonzero : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ((binaryProjectiveZeros A B C).card : ℤ) =
      quadraticChar (ZMod p) (binaryDiscriminant A B C) + 1 := by
  classical
  by_cases hC : C = 0
  · subst C
    by_cases hB : B = 0
    · subst B
      have hA : A ≠ 0 := by simpa using hnonzero
      rw [binaryProjectiveZeros, binaryAffineZeros_eq_empty_of_BC_zero hA]
      simp [binaryInfinityZeros, binaryDiscriminant, quadraticChar_zero]
    · rw [binaryProjectiveZeros, binaryAffineZeros_eq_singleton_of_C_zero hB]
      have hquad : quadraticChar (ZMod p) (B ^ 2) = 1 :=
        quadraticChar_sq_one' hB
      simp [binaryInfinityZeros, binaryDiscriminant, hquad]
  · have hchar : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      exact hp2
    have hroot := quadraticChar_card_sqrts hchar (binaryDiscriminant A B C)
    have hcard := binaryAffineZeros_card_eq_squareRoots (p := p) hp2 A B hC
    rw [binaryProjectiveZeros, Finset.card_disjSum, hcard]
    have hinfinity : binaryInfinityZeros C = ∅ := by simp [binaryInfinityZeros, hC]
    simp only [hinfinity, Finset.card_empty, Nat.add_zero]
    simpa [Set.toFinset_setOf] using hroot

#print axioms binaryProjectiveZeros_card_cast

end Soma.Holonics.Millennium.FamilyProjectiveBinaryQuadratic
