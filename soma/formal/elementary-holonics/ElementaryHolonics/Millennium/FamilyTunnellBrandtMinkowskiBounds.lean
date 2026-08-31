import ElementaryHolonics.Millennium.FamilyTunnellBrandtGenusInvariants

/-!
# An exact Minkowski bound for the Jones--Pall source lattice

The Brandt source `Q₁ = 2x² + y² + 32z²` is positive definite.  Before a
destination classifier can enumerate determinant-`64` forms, every bounded
norm slice must first be reduced to a finite coefficient box.  This owner
supplies that exact coefficient-wise bound; it uses no real approximation or
enumeration oracle.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtMinkowskiBounds

open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellNormOneReturn

/-! The diagonal Gram entries are retained separately in the conclusion. -/

theorem brandtFirst_minkowski_square_bounds
    (m : IntTriple) {B : ℤ}
    (hQ : brandtFirstQuadratic m ≤ B) :
    2 * m.1 ^ 2 ≤ B ∧
      m.2.1 ^ 2 ≤ B ∧
        32 * m.2.2 ^ 2 ≤ B := by
  unfold brandtFirstQuadratic at hQ
  have hx : 0 ≤ m.1 ^ 2 := sq_nonneg m.1
  have hy : 0 ≤ m.2.1 ^ 2 := sq_nonneg m.2.1
  have hz : 0 ≤ m.2.2 ^ 2 := sq_nonneg m.2.2
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem brandtFirst_minkowski_level_one_box
    (m : IntTriple) (hQ : brandtFirstQuadratic m = 1) :
    -1 ≤ m.1 ∧ m.1 ≤ 1 ∧
      -1 ≤ m.2.1 ∧ m.2.1 ≤ 1 ∧
      -1 ≤ m.2.2 ∧ m.2.2 ≤ 1 := by
  have hbounds := brandtFirst_minkowski_square_bounds (B := (1 : ℤ)) m
    (by simpa [hQ])
  rcases hbounds with ⟨hx, hy, hz⟩
  have hx' : m.1 ^ 2 ≤ 1 := by nlinarith
  have hy' : m.2.1 ^ 2 ≤ 1 := by nlinarith
  have hz' : m.2.2 ^ 2 ≤ 1 := by nlinarith
  constructor
  · nlinarith [sq_nonneg m.1]
  constructor
  · nlinarith [sq_nonneg m.1]
  constructor
  · nlinarith [sq_nonneg m.2.1]
  constructor
  · nlinarith [sq_nonneg m.2.1]
  constructor
  · nlinarith [sq_nonneg m.2.2]
  · nlinarith [sq_nonneg m.2.2]

/-! The finite box is tight enough to recover the exact norm-one fibre. -/

theorem brandtFirst_minkowski_level_one_classification
    (m : IntTriple) :
    brandtFirstQuadratic m = 1 ↔
      m = (0, 1, 0) ∨ m = (0, -1, 0) := by
  exact Soma.Holonics.Millennium.FamilyTunnellNormOneReturn.brandtFirstQuadratic_eq_one_iff m

/-! ## The completed-square chart for the second class -/

theorem brandtSecond_minkowski_square_bounds
    (m : IntTriple) {B : ℤ}
    (hQ : brandtSecondQuadratic m ≤ B) :
    2 * m.1 ^ 2 ≤ B ∧
      (2 * m.2.1 + m.2.2) ^ 2 ≤ B ∧
        8 * m.2.2 ^ 2 ≤ B := by
  rw [brandtSecondQuadratic_completedSquare] at hQ
  have hx : 0 ≤ m.1 ^ 2 := sq_nonneg m.1
  have hyz : 0 ≤ (2 * m.2.1 + m.2.2) ^ 2 :=
    sq_nonneg (2 * m.2.1 + m.2.2)
  have hz : 0 ≤ m.2.2 ^ 2 := sq_nonneg m.2.2
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem brandtSecond_minkowski_level_one_box
    (m : IntTriple) (hQ : brandtSecondQuadratic m = 1) :
    -1 ≤ m.1 ∧ m.1 ≤ 1 ∧
      -1 ≤ 2 * m.2.1 + m.2.2 ∧ 2 * m.2.1 + m.2.2 ≤ 1 ∧
      -1 ≤ m.2.2 ∧ m.2.2 ≤ 1 := by
  have hbounds := brandtSecond_minkowski_square_bounds (B := (1 : ℤ)) m
    (by simpa [hQ])
  rcases hbounds with ⟨hx, hyz, hz⟩
  have hx' : m.1 ^ 2 ≤ 1 := by nlinarith
  have hyz' : (2 * m.2.1 + m.2.2) ^ 2 ≤ 1 := by nlinarith
  have hz' : m.2.2 ^ 2 ≤ 1 := by nlinarith
  constructor
  · nlinarith [sq_nonneg m.1]
  constructor
  · nlinarith [sq_nonneg m.1]
  constructor
  · nlinarith [sq_nonneg (2 * m.2.1 + m.2.2)]
  constructor
  · nlinarith [sq_nonneg (2 * m.2.1 + m.2.2)]
  constructor
  · nlinarith [sq_nonneg m.2.2]
  · nlinarith [sq_nonneg m.2.2]

theorem brandtSecond_minkowski_level_one_classification
    (m : IntTriple) :
    brandtSecondQuadratic m = 1 ↔ False := by
  constructor
  · exact brandtSecondQuadratic_ne_one m
  · intro h
    exact False.elim h

#print axioms brandtFirst_minkowski_square_bounds
#print axioms brandtFirst_minkowski_level_one_box
#print axioms brandtFirst_minkowski_level_one_classification
#print axioms brandtSecond_minkowski_square_bounds
#print axioms brandtSecond_minkowski_level_one_box
#print axioms brandtSecond_minkowski_level_one_classification

end Soma.Holonics.Millennium.FamilyTunnellBrandtMinkowskiBounds
