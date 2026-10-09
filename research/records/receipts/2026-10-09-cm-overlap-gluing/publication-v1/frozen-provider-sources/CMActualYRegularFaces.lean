import CMYAmbientCoordinates
import CMYAmbientRegular
import CMAmbientAwayIdeals

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

abbrev yGraphPAmbientOpen : Spec (.of (Localization.Away yGraphP)) ⟶ CMActualAmbientProduct :=
  ambientAwayOpen yProductChartInclusion yGraphP
theorem yGraphPActual_regular_equation :
    cmConcreteComplexGraph.ker.comap yGraphPAmbientOpen = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {algebraMap YProductRing (Localization.Away yGraphP) yGraphBEquation}).map
        (Scheme.ΓSpecIso (.of (Localization.Away yGraphP))).inv.hom) ∧
    IsRegular (algebraMap YProductRing (Localization.Away yGraphP) yGraphBEquation) := by
  constructor
  · dsimp only [yGraphPAmbientOpen, ambientAwayOpen]
    rw [Scheme.IdealSheafData.comap_comp, yActualGraph_ideal_coordinates, specOpen_coordinateIdeal_comap]
    change Scheme.IdealSheafData.ofIdealTop
      ((yGraphIdeal.map (algebraMap YProductRing (Localization.Away yGraphP))).map
        (Scheme.ΓSpecIso (.of (Localization.Away yGraphP))).inv.hom) = _
    rw [yGraphIdeal_P_face]
  · exact yGraphB_P_regular

abbrev yGraphQAmbientOpen : Spec (.of (Localization.Away yGraphQ)) ⟶ CMActualAmbientProduct :=
  ambientAwayOpen yProductChartInclusion yGraphQ
theorem yGraphQActual_regular_equation :
    cmConcreteComplexGraph.ker.comap yGraphQAmbientOpen = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {algebraMap YProductRing (Localization.Away yGraphQ) yGraphAEquation}).map
        (Scheme.ΓSpecIso (.of (Localization.Away yGraphQ))).inv.hom) ∧
    IsRegular (algebraMap YProductRing (Localization.Away yGraphQ) yGraphAEquation) := by
  constructor
  · dsimp only [yGraphQAmbientOpen, ambientAwayOpen]
    rw [Scheme.IdealSheafData.comap_comp, yActualGraph_ideal_coordinates, specOpen_coordinateIdeal_comap]
    change Scheme.IdealSheafData.ofIdealTop
      ((yGraphIdeal.map (algebraMap YProductRing (Localization.Away yGraphQ))).map
        (Scheme.ΓSpecIso (.of (Localization.Away yGraphQ))).inv.hom) = _
    rw [yGraphIdeal_Q_face]
  · exact yGraphA_Q_regular

abbrev yDiagonalPAmbientOpen : Spec (.of (Localization.Away yDiagonalP)) ⟶ CMActualAmbientProduct :=
  ambientAwayOpen yProductChartInclusion yDiagonalP
theorem yDiagonalPActual_regular_equation :
    cmComplexDiagonal.ker.comap yDiagonalPAmbientOpen = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {algebraMap YProductRing (Localization.Away yDiagonalP) yDiagonalBEquation}).map
        (Scheme.ΓSpecIso (.of (Localization.Away yDiagonalP))).inv.hom) ∧
    IsRegular (algebraMap YProductRing (Localization.Away yDiagonalP) yDiagonalBEquation) := by
  constructor
  · dsimp only [yDiagonalPAmbientOpen, ambientAwayOpen]
    rw [Scheme.IdealSheafData.comap_comp, yActualDiagonal_ideal_coordinates, specOpen_coordinateIdeal_comap]
    change Scheme.IdealSheafData.ofIdealTop
      ((yDiagonalIdeal.map (algebraMap YProductRing (Localization.Away yDiagonalP))).map
        (Scheme.ΓSpecIso (.of (Localization.Away yDiagonalP))).inv.hom) = _
    rw [yDiagonalIdeal_P_face]
  · exact yDiagonalB_P_regular

abbrev yDiagonalQAmbientOpen : Spec (.of (Localization.Away yDiagonalQ)) ⟶ CMActualAmbientProduct :=
  ambientAwayOpen yProductChartInclusion yDiagonalQ
theorem yDiagonalQActual_regular_equation :
    cmComplexDiagonal.ker.comap yDiagonalQAmbientOpen = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {algebraMap YProductRing (Localization.Away yDiagonalQ) yDiagonalAEquation}).map
        (Scheme.ΓSpecIso (.of (Localization.Away yDiagonalQ))).inv.hom) ∧
    IsRegular (algebraMap YProductRing (Localization.Away yDiagonalQ) yDiagonalAEquation) := by
  constructor
  · dsimp only [yDiagonalQAmbientOpen, ambientAwayOpen]
    rw [Scheme.IdealSheafData.comap_comp, yActualDiagonal_ideal_coordinates, specOpen_coordinateIdeal_comap]
    change Scheme.IdealSheafData.ofIdealTop
      ((yDiagonalIdeal.map (algebraMap YProductRing (Localization.Away yDiagonalQ))).map
        (Scheme.ΓSpecIso (.of (Localization.Away yDiagonalQ))).inv.hom) = _
    rw [yDiagonalIdeal_Q_face]
  · exact yDiagonalA_Q_regular

#print axioms yGraphPActual_regular_equation
#print axioms yGraphQActual_regular_equation
#print axioms yDiagonalPActual_regular_equation
#print axioms yDiagonalQActual_regular_equation
end Holonics.Hodge.CMGraphSource
