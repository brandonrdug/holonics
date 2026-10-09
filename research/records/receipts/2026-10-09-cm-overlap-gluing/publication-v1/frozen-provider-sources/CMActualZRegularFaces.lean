import CMZAmbientCoordinates
import CMZDiagonalFaces
import CMAmbientAwayIdeals

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

abbrev zGraphFactorAmbientOpen : Spec (.of (Localization.Away graphCubicFactor)) ⟶ CMActualAmbientProduct :=
  ambientAwayOpen zProductChartInclusion graphCubicFactor
theorem zGraphFactorActual_regular_equation :
    cmConcreteComplexGraph.ker.comap zGraphFactorAmbientOpen = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {algebraMap ProductRing (Localization.Away graphCubicFactor) graphVEquation}).map
        (Scheme.ΓSpecIso (.of (Localization.Away graphCubicFactor))).inv.hom) ∧
    IsRegular (algebraMap ProductRing (Localization.Away graphCubicFactor) graphVEquation) := by
  constructor
  · dsimp only [zGraphFactorAmbientOpen, ambientAwayOpen]
    rw [Scheme.IdealSheafData.comap_comp, zActualGraph_ideal_coordinates, specOpen_coordinateIdeal_comap]
    change Scheme.IdealSheafData.ofIdealTop
      ((graphIdeal.map (algebraMap ProductRing (Localization.Away graphCubicFactor))).map
        (Scheme.ΓSpecIso (.of (Localization.Away graphCubicFactor))).inv.hom) = _
    rw [graphIdeal_on_cubic_factor_face]
  · exact graphVEquation_regular_on_factor_face

abbrev zGraphVSumAmbientOpen : Spec (.of (Localization.Away graphVSum)) ⟶ CMActualAmbientProduct :=
  ambientAwayOpen zProductChartInclusion graphVSum
theorem zGraphVSumActual_regular_equation :
    cmConcreteComplexGraph.ker.comap zGraphVSumAmbientOpen = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {algebraMap ProductRing (Localization.Away graphVSum) graphXEquation}).map
        (Scheme.ΓSpecIso (.of (Localization.Away graphVSum))).inv.hom) ∧
    IsRegular (algebraMap ProductRing (Localization.Away graphVSum) graphXEquation) := by
  constructor
  · dsimp only [zGraphVSumAmbientOpen, ambientAwayOpen]
    rw [Scheme.IdealSheafData.comap_comp, zActualGraph_ideal_coordinates, specOpen_coordinateIdeal_comap]
    change Scheme.IdealSheafData.ofIdealTop
      ((graphIdeal.map (algebraMap ProductRing (Localization.Away graphVSum))).map
        (Scheme.ΓSpecIso (.of (Localization.Away graphVSum))).inv.hom) = _
    rw [graphIdeal_on_vsum_face]
  · exact graphXEquation_regular_on_vsum_face

abbrev zDiagonalFactorAmbientOpen : Spec (.of (Localization.Away diagonalCubicFactor)) ⟶ CMActualAmbientProduct :=
  ambientAwayOpen zProductChartInclusion diagonalCubicFactor
theorem zDiagonalFactorActual_regular_equation :
    cmComplexDiagonal.ker.comap zDiagonalFactorAmbientOpen = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {algebraMap ProductRing (Localization.Away diagonalCubicFactor) diagonalVEquation}).map
        (Scheme.ΓSpecIso (.of (Localization.Away diagonalCubicFactor))).inv.hom) ∧
    IsRegular (algebraMap ProductRing (Localization.Away diagonalCubicFactor) diagonalVEquation) := by
  constructor
  · dsimp only [zDiagonalFactorAmbientOpen, ambientAwayOpen]
    rw [Scheme.IdealSheafData.comap_comp, zActualDiagonal_ideal_coordinates, specOpen_coordinateIdeal_comap]
    change Scheme.IdealSheafData.ofIdealTop
      ((diagonalIdeal.map (algebraMap ProductRing (Localization.Away diagonalCubicFactor))).map
        (Scheme.ΓSpecIso (.of (Localization.Away diagonalCubicFactor))).inv.hom) = _
    rw [diagonalIdeal_on_factor_face]
  · exact diagonalVEquation_regular_on_factor_face

abbrev zDiagonalVSumAmbientOpen : Spec (.of (Localization.Away diagonalVSum)) ⟶ CMActualAmbientProduct :=
  ambientAwayOpen zProductChartInclusion diagonalVSum
theorem zDiagonalVSumActual_regular_equation :
    cmComplexDiagonal.ker.comap zDiagonalVSumAmbientOpen = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {algebraMap ProductRing (Localization.Away diagonalVSum) diagonalUEquation}).map
        (Scheme.ΓSpecIso (.of (Localization.Away diagonalVSum))).inv.hom) ∧
    IsRegular (algebraMap ProductRing (Localization.Away diagonalVSum) diagonalUEquation) := by
  constructor
  · dsimp only [zDiagonalVSumAmbientOpen, ambientAwayOpen]
    rw [Scheme.IdealSheafData.comap_comp, zActualDiagonal_ideal_coordinates, specOpen_coordinateIdeal_comap]
    change Scheme.IdealSheafData.ofIdealTop
      ((diagonalIdeal.map (algebraMap ProductRing (Localization.Away diagonalVSum))).map
        (Scheme.ΓSpecIso (.of (Localization.Away diagonalVSum))).inv.hom) = _
    rw [diagonalIdeal_on_vsum_face]
  · exact diagonalUEquation_regular_on_vsum_face

#print axioms zGraphFactorActual_regular_equation
#print axioms zGraphVSumActual_regular_equation
#print axioms zDiagonalFactorActual_regular_equation
#print axioms zDiagonalVSumActual_regular_equation
end Holonics.Hodge.CMGraphSource
