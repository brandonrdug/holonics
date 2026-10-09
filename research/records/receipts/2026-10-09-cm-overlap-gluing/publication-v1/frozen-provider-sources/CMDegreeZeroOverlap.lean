import CMYChartLocalization

/-!
This owner concerns degree-zero homogeneous localization, not the full
localization CubicOverlap. It identifies the actual intersection of the
two ambient projective charts and their localization maps.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open HomogeneousLocalization AlgebraicGeometry CategoryTheory
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev yzCoordinate : HomogeneousRing := zCoordinate * yCoordinate
abbrev YZDegreeZeroAway := Away CMGrading yzCoordinate
def zToDegreeZeroOverlap : ZChartAway →+* YZDegreeZeroAway :=
  awayMap CMGrading (coordinate_degree_one 1) rfl
def yToDegreeZeroOverlap : YChartAway →+* YZDegreeZeroAway :=
  awayMap CMGrading (coordinate_degree_one 2) (mul_comm _ _)

instance zOverlapAlgebra : Algebra ZChartAway YZDegreeZeroAway :=
  zToDegreeZeroOverlap.toAlgebra

theorem degreeZeroOverlap_isLocalization_z :
    IsLocalization.Away (zRatio 1) YZDegreeZeroAway := by
  simpa only [Away.isLocalizationElem, zRatio, pow_one] using
    Away.isLocalization_mul (coordinate_degree_one 2)
    (coordinate_degree_one 1) rfl (by norm_num)

def degreeZeroOverlapEquivZLocalization :
    YZDegreeZeroAway ≃ₐ[ZChartAway] Localization.Away (zRatio 1) := by
  letI := degreeZeroOverlap_isLocalization_z
  exact IsLocalization.algEquiv (.powers (zRatio 1)) _ _

def yOverlapRatio : YChartAway :=
  Away.mk CMGrading (coordinate_degree_one 1) 1 zCoordinate
    (by simpa using coordinate_degree_one 2)

theorem degreeZeroOverlap_isLocalization_y :
    letI := yToDegreeZeroOverlap.toAlgebra
    IsLocalization.Away yOverlapRatio YZDegreeZeroAway := by
  simpa only [Away.isLocalizationElem, yOverlapRatio, pow_one] using
    Away.isLocalization_mul (coordinate_degree_one 1)
    (coordinate_degree_one 2) (mul_comm _ _) (by norm_num)

def ambientYZChartIntersectionIso :
    Limits.pullback (Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num))
      (Proj.awayι CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num)) ≅
        Spec (.of YZDegreeZeroAway) :=
  Proj.pullbackAwayιIso CMGrading (coordinate_degree_one 2) (by norm_num)
    (coordinate_degree_one 1) (by norm_num) rfl

theorem ambientYZChartIntersection_projection_z :
    ambientYZChartIntersectionIso.inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom zToDegreeZeroOverlap) :=
  Proj.pullbackAwayιIso_inv_fst CMGrading (coordinate_degree_one 2) (by norm_num)
    (coordinate_degree_one 1) (by norm_num) rfl

theorem ambientYZChartIntersection_projection_y :
    ambientYZChartIntersectionIso.inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom yToDegreeZeroOverlap) :=
  Proj.pullbackAwayιIso_inv_snd CMGrading (coordinate_degree_one 2) (by norm_num)
    (coordinate_degree_one 1) (by norm_num) rfl

#print axioms degreeZeroOverlap_isLocalization_z
#print axioms degreeZeroOverlapEquivZLocalization
#print axioms degreeZeroOverlap_isLocalization_y
#print axioms ambientYZChartIntersectionIso
#print axioms ambientYZChartIntersection_projection_z
#print axioms ambientYZChartIntersection_projection_y
end Holonics.Hodge.CMGraphSource
