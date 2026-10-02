import HolonicsResearch.Foundation.IwasawaPolynomial
import HolonicsResearch.Geometry.CyclicGrover.IntegralCoefficientCover

/-! Refs #62. Actual named finite Iwasawa polynomial consumers. -/
namespace Holonics.Epime.GroverTower
open Matrix Polynomial

theorem charpoly_is_existing_groupRingPoly (n : ℕ) :
    (operatorOver n : Matrix (Dart n) (Dart n) ℤ_[3]).charpoly =
      (Holonics.Foundation.IwasawaTower.groupRingPoly 3 (n+1))^2 := by
  rw [operatorOver_charpoly]
  rfl

theorem charpoly_difference_chart_is_existing_omegaPoly (n : ℕ) :
    ((operatorOver n : Matrix (Dart n) (Dart n) ℤ_[3]).charpoly).comp (X+1) =
      (Holonics.Foundation.IwasawaTower.omegaPoly 3 (n+1))^2 := by
  rw [charpoly_is_existing_groupRingPoly, Polynomial.pow_comp,
    ← Holonics.Foundation.IwasawaTower.omegaPoly_eq_groupRingPoly_comp]

/-- Integer nonvanishing does not imply invertibility after an arbitrary coefficient map. -/
theorem characteristic_three_determinant_zero (n : ℕ) :
    (Matrix.scalar (Dart n) (4:ZMod 3) - operatorOver n).det = 0 := by
  rw [operatorOver_chart, GroverCycle.grover_determinant]
  have h4 : (4:ZMod 3) = 1 := by decide
  simp [h4]

end Holonics.Epime.GroverTower

#print axioms Holonics.Epime.GroverTower.charpoly_is_existing_groupRingPoly
#print axioms Holonics.Epime.GroverTower.charpoly_difference_chart_is_existing_omegaPoly
#print axioms Holonics.Epime.GroverTower.characteristic_three_determinant_zero
