import CMZAmbientProduct
import CMGraphChartPullback
import CMProjectiveFixedComparison
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Genuine restrictions of the actual graph/diagonal ideal sheaves on
E x_C E to its actual Z x_C Z tensor spectrum. Further restrictions commute
through the existing ideal-sheaf pullback, rather than an assumed chart ideal. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

theorem zTensorGraph_isPullback : IsPullback zTensorGraph zCurveChartInclusion
    zProductChartInclusion cmConcreteComplexGraph :=
  graphChart_isPullback zCurveChartInclusion zProductChartInclusion
    (Spec.map (CommRingCat.ofHom graphLeft.toRingHom))
    (pullback.fst cmConcreteCubicBase cmConcreteCubicBase)
    zTensorGraph cmConcreteComplexGraph cmConcreteComplexGraph_first_projection
    zProductChart_first_projection zTensorGraph_actual_square

theorem zTensorDiagonal_isPullback : IsPullback zTensorDiagonal zCurveChartInclusion
    zProductChartInclusion cmComplexDiagonal :=
  graphChart_isPullback zCurveChartInclusion zProductChartInclusion
    (Spec.map (CommRingCat.ofHom graphLeft.toRingHom))
    (pullback.fst cmConcreteCubicBase cmConcreteCubicBase)
    zTensorDiagonal cmComplexDiagonal
    (by simp [cmComplexDiagonal]) zProductChart_first_projection zTensorDiagonal_actual_square

theorem zTensorGraph_actual_ideal :
    cmConcreteComplexGraph.ker.comap zProductChartInclusion = zTensorGraph.ker := by
  letI : IsClosedImmersion cmConcreteComplexGraph := cmConcreteGraph_closedImmersion
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← zTensorGraph_isPullback.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

theorem zTensorDiagonal_actual_ideal :
    cmComplexDiagonal.ker.comap zProductChartInclusion = zTensorDiagonal.ker := by
  letI : IsClosedImmersion cmComplexDiagonal := by
    dsimp only [cmComplexDiagonal]
    infer_instance
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← zTensorDiagonal_isPullback.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

theorem zTensorGraph_ideal_restriction {U : Scheme} (r : U ⟶ Spec (.of ProductRing)) :
    cmConcreteComplexGraph.ker.comap (r ≫ zProductChartInclusion) =
      zTensorGraph.ker.comap r := by
  rw [Scheme.IdealSheafData.comap_comp, zTensorGraph_actual_ideal]

theorem zTensorDiagonal_ideal_restriction {U : Scheme} (r : U ⟶ Spec (.of ProductRing)) :
    cmComplexDiagonal.ker.comap (r ≫ zProductChartInclusion) =
      zTensorDiagonal.ker.comap r := by
  rw [Scheme.IdealSheafData.comap_comp, zTensorDiagonal_actual_ideal]

theorem zTensorGraph_support :
    zTensorGraph.ker.support = cmConcreteComplexGraph.ker.support.preimage
      zProductChartInclusion.continuous := by
  rw [← zTensorGraph_actual_ideal, Scheme.IdealSheafData.support_comap]

theorem zTensorDiagonal_support :
    zTensorDiagonal.ker.support = cmComplexDiagonal.ker.support.preimage
      zProductChartInclusion.continuous := by
  rw [← zTensorDiagonal_actual_ideal, Scheme.IdealSheafData.support_comap]

#print axioms zTensorGraph_isPullback
#print axioms zTensorDiagonal_isPullback
#print axioms zTensorGraph_actual_ideal
#print axioms zTensorDiagonal_actual_ideal
#print axioms zTensorGraph_ideal_restriction
#print axioms zTensorDiagonal_ideal_restriction
#print axioms zTensorGraph_support
#print axioms zTensorDiagonal_support
end Holonics.Hodge.CMGraphSource
