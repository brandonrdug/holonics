import CMActualFixedIntrinsicLength

/-! Scheme intersection multiplicities of the actual graph--diagonal cut.
CMProjectiveFixedScheme is the actual pullback, and its inclusion ideal is
proved equal to the diagonal ideal pulled back along the actual graph.
The local quotient-to-intrinsic-stalk maps below therefore identify the
scheme-cut local multiplicities, including their actual inclusion scalars.

agent-inferred: identify the actual cut and the scalar square before naming
its multiplicities. This avoids an assumed intersection comparison. The
external helical pair receiver touches faces and placement, cell holonomy
and tube; helix, pair and tower remain attached. This source does not provide
a higher-Tor computation or an intersection product in a Chow/Hodge receiver. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

attribute [local instance] cmActualYFixedStalkAlgebra cmActualZFixedStalkAlgebra

abbrev cmActualGraphDiagonalCutIdeal : CMProjectiveCubic.IdealSheafData :=
  cmComplexDiagonal.ker.comap cmConcreteComplexGraph

theorem cmActualGraphDiagonalCutIdeal_eq_fixed :
    cmActualGraphDiagonalCutIdeal = cmFixedInclusion.ker :=
  cmFixed_ideal_eq_diagonalRestriction.symm

theorem cmActualFixed_graphDiagonal_square :
    cmFixedInclusion ≫ cmConcreteComplexGraph = cmFixedInclusion ≫ cmComplexDiagonal := by
  have h := pullback.condition (f := cmConcreteComplexGraph) (g := cmComplexDiagonal)
  change cmFixedInclusion ≫ cmConcreteComplexGraph =
    pullback.snd cmConcreteComplexGraph cmComplexDiagonal ≫ cmComplexDiagonal at h
  rwa [← cmFixed_projections_agree] at h

abbrev cmActualYGraphDiagonalStalkIdeal : Ideal cmActualYOriginLocalRing :=
  spectrumImageStalkIdeal cmActualGraphDiagonalCutIdeal (.of YRestrictedQAway)
    cmActualRestrictedYCurveOpen yRestrictedOriginLift.toRingHom

abbrev cmActualZGraphDiagonalStalkIdeal : Ideal cmActualZOriginLocalRing :=
  spectrumImageStalkIdeal cmActualGraphDiagonalCutIdeal (.of ActualRestrictedZRing)
    cmActualRestrictedZCurveOpen cmActualZOriginLift.toRingHom

theorem cmActualYGraphDiagonalStalkIdeal_eq :
    cmActualYGraphDiagonalStalkIdeal = cmActualYOriginStalkIdeal := by
  change spectrumImageStalkIdeal cmActualGraphDiagonalCutIdeal _ _ _ = _
  rw [cmActualGraphDiagonalCutIdeal_eq_fixed]

theorem cmActualZGraphDiagonalStalkIdeal_eq :
    cmActualZGraphDiagonalStalkIdeal = cmActualZOriginStalkIdeal := by
  change spectrumImageStalkIdeal cmActualGraphDiagonalCutIdeal _ _ _ = _
  rw [cmActualGraphDiagonalCutIdeal_eq_fixed]

def cmActualYGraphDiagonalQuotientToFixedStalk :
    (cmActualYOriginLocalRing ⧸ cmActualYGraphDiagonalStalkIdeal) ≃ₐ[cmActualYOriginLocalRing]
      cmActualYFixedLocalRing := by
  rw [cmActualYGraphDiagonalStalkIdeal_eq]
  exact cmActualYQuotientToFixedStalkAlgEquiv

def cmActualZGraphDiagonalQuotientToFixedStalk :
    (cmActualZOriginLocalRing ⧸ cmActualZGraphDiagonalStalkIdeal) ≃ₐ[cmActualZOriginLocalRing]
      cmActualZFixedLocalRing := by
  rw [cmActualZGraphDiagonalStalkIdeal_eq]
  exact cmActualZQuotientToFixedStalkAlgEquiv

abbrev cmActualYGraphDiagonalMultiplicity : ℕ∞ :=
  Module.length cmActualYOriginLocalRing
    (cmActualYOriginLocalRing ⧸ cmActualYGraphDiagonalStalkIdeal)

abbrev cmActualZGraphDiagonalMultiplicity : ℕ∞ :=
  Module.length cmActualZOriginLocalRing
    (cmActualZOriginLocalRing ⧸ cmActualZGraphDiagonalStalkIdeal)

theorem cmActualYGraphDiagonalMultiplicity_eq_intrinsic :
    cmActualYGraphDiagonalMultiplicity =
      Module.length cmActualYFixedLocalRing cmActualYFixedLocalRing :=
  cmActualYGraphDiagonalQuotientToFixedStalk.toLinearEquiv.length_eq.trans
    (Module.length_eq_of_surjective
      (S := cmActualYOriginLocalRing) (R := cmActualYFixedLocalRing)
      (M := cmActualYFixedLocalRing) (by
        change Function.Surjective cmActualYOriginToFixedStalk.hom
        exact cmActualYOriginToFixedStalk_surjective))

theorem cmActualZGraphDiagonalMultiplicity_eq_intrinsic :
    cmActualZGraphDiagonalMultiplicity =
      Module.length cmActualZFixedLocalRing cmActualZFixedLocalRing :=
  cmActualZGraphDiagonalQuotientToFixedStalk.toLinearEquiv.length_eq.trans
    (Module.length_eq_of_surjective
      (S := cmActualZOriginLocalRing) (R := cmActualZFixedLocalRing)
      (M := cmActualZFixedLocalRing) (by
        change Function.Surjective cmActualZOriginToFixedStalk.hom
        exact cmActualZOriginToFixedStalk_surjective))

theorem cmActualYGraphDiagonalMultiplicityOne : cmActualYGraphDiagonalMultiplicity = 1 :=
  cmActualYGraphDiagonalMultiplicity_eq_intrinsic.trans cmActualYFixedIntrinsicLengthOne

theorem cmActualZGraphDiagonalMultiplicityOne : cmActualZGraphDiagonalMultiplicity = 1 :=
  cmActualZGraphDiagonalMultiplicity_eq_intrinsic.trans cmActualZFixedIntrinsicLengthOne

theorem cmActualGraphDiagonalCut_support :
    (cmActualGraphDiagonalCutIdeal.support : Set CMProjectiveCubic) =
      {cmActualYOriginPoint, cmActualZOriginPoint} := by
  rw [cmActualGraphDiagonalCutIdeal_eq_fixed]
  exact cmActualFixed_support_eq_two_origins

#print axioms cmActualFixed_graphDiagonal_square
#print axioms cmActualYGraphDiagonalQuotientToFixedStalk
#print axioms cmActualZGraphDiagonalQuotientToFixedStalk
#print axioms cmActualYGraphDiagonalMultiplicity_eq_intrinsic
#print axioms cmActualZGraphDiagonalMultiplicity_eq_intrinsic
#print axioms cmActualYGraphDiagonalMultiplicityOne
#print axioms cmActualZGraphDiagonalMultiplicityOne
#print axioms cmActualGraphDiagonalCut_support
end Holonics.Hodge.CMGraphSource
