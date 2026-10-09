import CMActualFixedChartIdealTransport
import CMActualRestrictedYLength
import CMActualRestrictedZLength
import CMAmbientAwayIdeals

/-! Actual consumers of the restricted equations. The projective fixed
inclusion's kernel is restricted through its real Y/Z curve open maps,
identified with the principal coordinate equations, and paired with the
constructed length-one coordinate quotients.

agent-inferred: use the Y diagonal-Q and Z diagonal-factor opens because
their actual origin residues are respectively 1 and -1. This identifies
genuine neighborhoods of the two fixed points without assuming that an
ambient regular section stays regular after graph pullback.

Coverage of these smaller fixed-point opens and the global
intersection-degree/cycle-class comparison remain separate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

abbrev cmActualRestrictedYCurveOpen : Spec (.of YRestrictedQAway) ⟶ CMProjectiveCubic :=
  ambientAwayOpen yCurveChartInclusion yRestrictedQ

abbrev cmActualRestrictedZCurveOpen : Spec (.of ActualRestrictedZRing) ⟶ CMProjectiveCubic :=
  ambientAwayOpen zCurveChartInclusion (u ^ 2 - 1)

theorem cmActualFixedYRestricted_regular_equation :
    cmFixedInclusion.ker.comap cmActualRestrictedYCurveOpen =
      Scheme.IdealSheafData.ofIdealTop
        ((Ideal.span {yRestrictedA}).map
          (Scheme.ΓSpecIso (.of YRestrictedQAway)).inv.hom) ∧
    IsRegular yRestrictedA := by
  constructor
  · exact ambientAwayOpen_principal
      (R := CommRingCat.of YChartCubicRing) (X := CMProjectiveCubic)
      cmFixedInclusion.ker yFixedDifferenceIdeal
      yCurveChartInclusion cmActualFixedY_ideal_coordinates
      yRestrictedQ yAmbientA actualRestrictedY_fixedIdeal_eq_a
  · exact yRestrictedA_regular

theorem cmActualFixedZRestricted_regular_equation :
    cmFixedInclusion.ker.comap cmActualRestrictedZCurveOpen =
      Scheme.IdealSheafData.ofIdealTop
        ((Ideal.span {algebraMap CurveRing ActualRestrictedZRing v}).map
          (Scheme.ΓSpecIso (.of ActualRestrictedZRing)).inv.hom) ∧
    IsRegular (algebraMap CurveRing ActualRestrictedZRing v) := by
  constructor
  · have hcoord : cmFixedInclusion.ker.comap zCurveChartInclusion =
        Scheme.IdealSheafData.ofIdealTop
          (fixedIdeal.map (Scheme.ΓSpecIso (.of CurveRing)).inv.hom) := by
      rw [← cmActualFixedZDifference_eq_fixedIdeal]
      exact cmActualFixedZ_ideal_coordinates
    exact ambientAwayOpen_principal
      (R := CommRingCat.of CurveRing) (X := CMProjectiveCubic)
      cmFixedInclusion.ker fixedIdeal
      zCurveChartInclusion hcoord (u ^ 2 - 1) v actualRestrictedZ_fixedIdeal_eq_v
  · exact actualRestrictedZ_v_regular

theorem cmActualFixedYRestricted_coordinate_length_one :
    Module.length ℂ (YRestrictedQAway ⧸ Ideal.span {yRestrictedA}) = 1 := by
  rw [← yRestrictedFixedIdeal_eq_spanA]
  exact yRestrictedFixedQuotient_length_eq_one

theorem cmActualFixedZRestricted_coordinate_length_one :
    Module.length ℂ (ActualRestrictedZRing ⧸
      Ideal.span {algebraMap CurveRing ActualRestrictedZRing v}) = 1 :=
  actualRestrictedZ_quotient_length_one

#print axioms cmActualFixedYRestricted_regular_equation
#print axioms cmActualFixedZRestricted_regular_equation
#print axioms cmActualFixedYRestricted_coordinate_length_one
#print axioms cmActualFixedZRestricted_coordinate_length_one
end Holonics.Hodge.CMGraphSource
