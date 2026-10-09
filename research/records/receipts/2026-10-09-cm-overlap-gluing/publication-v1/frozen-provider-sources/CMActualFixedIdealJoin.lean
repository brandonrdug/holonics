import CMProjectiveFixedComparison
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! The actual graph--diagonal fixed scheme is cut out on either copy of the
cubic by the other actual ideal. These identities join the local equations to
the existing scheme. They assert neither preservation of regularity under
arbitrary pullback nor any intersection-degree or cohomological comparison. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

local instance : IsClosedImmersion cmConcreteComplexGraph :=
  cmConcreteGraph_closedImmersion

local instance : IsClosedImmersion cmComplexDiagonal := by
  unfold cmComplexDiagonal
  infer_instance

theorem cmFixed_ideal_eq_diagonalRestriction :
    cmFixedInclusion.ker = cmComplexDiagonal.ker.comap cmConcreteComplexGraph := by
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    cmComplexDiagonal cmConcreteComplexGraph

theorem cmFixed_ideal_eq_graphRestriction :
    cmFixedInclusion.ker = cmConcreteComplexGraph.ker.comap cmComplexDiagonal := by
  calc
    cmFixedInclusion.ker =
        (pullback.snd cmConcreteComplexGraph cmComplexDiagonal).ker :=
      congrArg (fun f => f.ker) cmFixed_projections_agree
    _ = ((pullbackSymmetry cmConcreteComplexGraph cmComplexDiagonal).hom ≫
        pullback.fst cmComplexDiagonal cmConcreteComplexGraph).ker := by
      rw [pullbackSymmetry_hom_comp_fst]
    _ = (pullback.fst cmComplexDiagonal cmConcreteComplexGraph).ker :=
      Scheme.Hom.ker_comp_of_isIso _ _
    _ = cmConcreteComplexGraph.ker.comap cmComplexDiagonal :=
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
        cmConcreteComplexGraph cmComplexDiagonal

theorem cmFixed_support_eq_graphRestriction :
    cmFixedInclusion.ker.support =
      cmConcreteComplexGraph.ker.support.preimage cmComplexDiagonal.continuous := by
  rw [cmFixed_ideal_eq_graphRestriction, Scheme.IdealSheafData.support_comap]

#print axioms cmFixed_ideal_eq_diagonalRestriction
#print axioms cmFixed_ideal_eq_graphRestriction
#print axioms cmFixed_support_eq_graphRestriction
end Holonics.Hodge.CMGraphSource
