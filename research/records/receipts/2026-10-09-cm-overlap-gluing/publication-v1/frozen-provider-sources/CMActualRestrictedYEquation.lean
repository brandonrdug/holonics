import CMYAmbientRegular
import CMGraphPrincipalCharts
import CMYFixedPoint

/-! The actual Y-chart graph restricts the diagonal to a principal equation on
the fixed-point localization. The nonzero localization parameter is certified
by the actual origin receiver; ambient regularity is never transported by
pullback. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open Polynomial
namespace Holonics.Hodge.CMGraphSource

abbrev yRestrictedQ : YChartCubicRing := yGraphReceiver yDiagonalQ
abbrev YRestrictedQAway := Localization.Away yRestrictedQ

def yRestrictedMap : YProductRing →+* YRestrictedQAway :=
  (algebraMap YChartCubicRing YRestrictedQAway).comp yGraphReceiver.toRingHom

abbrev yRestrictedA : YRestrictedQAway :=
  algebraMap YChartCubicRing YRestrictedQAway yAmbientA
abbrev yRestrictedB : YRestrictedQAway :=
  algebraMap YChartCubicRing YRestrictedQAway yAmbientB

theorem yRestrictedGraphDiagonalA :
    yGraphReceiver yDiagonalAEquation =
      algebraMap ℂ YChartCubicRing (Complex.I - 1) * yAmbientA := by
  simp only [yDiagonalAEquation, map_sub, yGraphReceiver_right,
    yGraphReceiver_left, yIotaAlgebraMap_a]
  simp [Algebra.smul_def]
  ring

theorem yRestrictedGraphDiagonalB :
    yGraphReceiver yDiagonalBEquation =
      algebraMap ℂ YChartCubicRing (-Complex.I - 1) * yAmbientB := by
  simp only [yDiagonalBEquation, map_sub, yGraphReceiver_right,
    yGraphReceiver_left, yIotaAlgebraMap_b]
  simp [Algebra.smul_def]
  ring

theorem yRestrictedQ_formula :
    yRestrictedQ =
      1 + algebraMap ℂ YChartCubicRing (1 - Complex.I) * yAmbientA * yAmbientB := by
  change yGraphReceiver yDiagonalQ = _
  rw [yDiagonalQ]
  simp only [map_add, map_mul, map_one, yGraphReceiver_left,
    yGraphReceiver_right, yIotaAlgebraMap_b]
  simp [Algebra.smul_def]
  ring

theorem yRestrictedQ_ne_zero : yRestrictedQ ≠ 0 := by
  intro h
  have hmap := congrArg yOriginReceiver h
  rw [yRestrictedQ_formula] at hmap
  have hA : yOriginReceiver yAmbientA = 0 := by
    change yOriginReceiver yA = 0
    exact yOriginReceiver_v
  have hB : yOriginReceiver yAmbientB = 0 := by
    change yOriginReceiver yB = 0
    exact yOriginReceiver_u
  simp [hA, hB] at hmap

local instance yRestrictedQAway_domain : IsDomain YRestrictedQAway :=
  Localization.Away.isDomain yRestrictedQ_ne_zero

theorem yAmbientA_ne_zero : yAmbientA ≠ 0 := by
  change AdjoinRoot.root yMonicCubic ≠ 0
  rw [← AdjoinRoot.mk_X]
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt yMonicCubic_monic
    (by simp) (by rw [yMonicCubic_natDegree]; norm_num)

theorem yRestrictedA_regular : IsRegular yRestrictedA := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  have hA : yAmbientA ∈ nonZeroDivisors YChartCubicRing :=
    isRegular_iff_mem_nonZeroDivisors.mp (IsRegular.of_ne_zero yAmbientA_ne_zero)
  exact IsLocalization.nonZeroDivisors_le_comap (R := YChartCubicRing)
    (Submonoid.powers yRestrictedQ) YRestrictedQAway hA

theorem yRestrictedDiagonalDifferenceRelation :
    yRestrictedMap yDiagonalAEquation * yRestrictedMap yDiagonalP =
      yRestrictedMap yDiagonalBEquation * yRestrictedMap yDiagonalQ := by
  have h := congrArg yRestrictedMap yDiagonal_difference_relation
  simpa only [map_mul] using h

theorem yRestrictedQ_isUnit : IsUnit (yRestrictedMap yDiagonalQ) := by
  change IsUnit (algebraMap YChartCubicRing YRestrictedQAway yRestrictedQ)
  exact IsLocalization.Away.algebraMap_isUnit yRestrictedQ

theorem yRestrictedI_minus_one_ne_zero : Complex.I - 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

theorem yRestrictedI_minus_one_isUnit :
    IsUnit (algebraMap ℂ YRestrictedQAway (Complex.I - 1)) :=
  IsUnit.map (algebraMap ℂ YRestrictedQAway)
    (isUnit_iff_ne_zero.mpr yRestrictedI_minus_one_ne_zero)

theorem yRestrictedActualDiagonalIdeal_principal :
    Ideal.map yRestrictedMap yDiagonalIdeal = Ideal.span {yRestrictedA} := by
  rw [yDiagonalIdeal_eq_two_equations, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  calc
    Ideal.span {yRestrictedMap yDiagonalAEquation,
        yRestrictedMap yDiagonalBEquation} =
        Ideal.span {yRestrictedMap yDiagonalAEquation} := by
      exact two_equations_principal_of_unit yRestrictedMap yDiagonalAEquation
        yDiagonalBEquation yDiagonalP yDiagonalQ
        yDiagonal_difference_relation yRestrictedQ_isUnit
    _ = Ideal.span {yRestrictedA} := by
      rw [show yRestrictedMap yDiagonalAEquation =
        algebraMap ℂ YRestrictedQAway (Complex.I - 1) * yRestrictedA by
          change algebraMap YChartCubicRing YRestrictedQAway
            (yGraphReceiver yDiagonalAEquation) = _
          rw [yRestrictedGraphDiagonalA, map_mul,
            ← IsScalarTower.algebraMap_apply ℂ YChartCubicRing YRestrictedQAway]]
      exact Ideal.span_singleton_mul_left_unit yRestrictedI_minus_one_isUnit yRestrictedA

theorem yRestrictedQ_eq_one_mod_principal :
    algebraMap YChartCubicRing YRestrictedQAway yRestrictedQ - 1 ∈
      Ideal.span {yRestrictedA} := by
  have hq : algebraMap YChartCubicRing YRestrictedQAway yRestrictedQ =
      1 + algebraMap ℂ YRestrictedQAway (1 - Complex.I) * yRestrictedA * yRestrictedB := by
    have h := congrArg (algebraMap YChartCubicRing YRestrictedQAway) yRestrictedQ_formula
    simpa only [map_add, map_mul, map_one,
      ← IsScalarTower.algebraMap_apply ℂ YChartCubicRing YRestrictedQAway] using h
  rw [hq]
  have hm : yRestrictedA *
      (algebraMap ℂ YRestrictedQAway (1 - Complex.I) * yRestrictedB) ∈
        Ideal.span {yRestrictedA} :=
    Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  convert hm using 1
  ring

#print axioms yRestrictedGraphDiagonalA
#print axioms yRestrictedGraphDiagonalB
#print axioms yRestrictedQ_formula
#print axioms yRestrictedQ_ne_zero
#print axioms yAmbientA_ne_zero
#print axioms yRestrictedA_regular
#print axioms yRestrictedDiagonalDifferenceRelation
#print axioms yRestrictedActualDiagonalIdeal_principal
#print axioms yRestrictedQ_eq_one_mod_principal
end Holonics.Hodge.CMGraphSource
