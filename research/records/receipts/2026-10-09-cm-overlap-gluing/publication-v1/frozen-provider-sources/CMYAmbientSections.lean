import CMYDirectDenominator

/-! A structurally different route to the actual Y action: sections on the
actual Proj basic open, avoiding full Scheme-composite normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def yAmbientAppLE : Γ(CMProjectiveAmbient, Proj.basicOpen CMGrading yCoordinate) ⟶
    Γ(CMProjectiveAmbient, Proj.basicOpen CMGrading yCoordinate) :=
  (Proj.map gradedIota irrelevant_le_map_iota).appLE
    (Proj.basicOpen CMGrading yCoordinate) (Proj.basicOpen CMGrading yCoordinate) (by
      change Proj.basicOpen CMGrading yCoordinate ≤ Proj.basicOpen CMGrading (gradedIota yCoordinate)
      exact Proj.basicOpen_mono CMGrading _ _ ⟨_, yCoordinate_actual_phase_inverse⟩)

theorem yAmbientSections_square :
    Proj.awayToSection CMGrading yCoordinate ≫ yAmbientAppLE =
      CommRingCat.ofHom yDirectAwayIota ≫ Proj.awayToSection CMGrading yCoordinate := by
  have hraw := Proj.awayToSection_comp_appLE gradedIota irrelevant_le_map_iota
    (coordinate_degree_one 1)
  change Proj.awayToSection CMGrading yCoordinate ≫
    (Proj.map gradedIota irrelevant_le_map_iota).app (Proj.basicOpen CMGrading yCoordinate) =
    CommRingCat.ofHom (Away.map gradedIota yCoordinate) ≫
      Proj.awayToSection CMGrading (gradedIota yCoordinate) at hraw
  have hunit := Proj.awayMap_awayToSection CMGrading
    (chartConstant_degree_zero (-Complex.I)) yCoordinate_actual_phase_inverse
  unfold yAmbientAppLE Scheme.Hom.appLE
  rw [← Category.assoc, hraw]
  rw [Category.assoc, ← hunit]
  rfl

#print axioms yAmbientSections_square
end Holonics.Hodge.CMGraphSource
