import CMYCoordinateFractions

/-! Construct denominator rescaling directly from gradedIota(Y), avoiding
an equality-recursion RingEquiv between dependent localization types. This
is a new presentation of the actual map, not a new source assumption. -/
noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yCoordinate_actual_phase_inverse :
    yCoordinate = gradedIota yCoordinate * MvPolynomial.C (-Complex.I) := by
  rw [gradedIota_yPhase]
  exact yCoordinate_phase_inverse

def yActualPhaseToChart : Away CMGrading (gradedIota yCoordinate) →+* YChartAway :=
  unitDegreeZeroChartMap (gradedIota yCoordinate) yCoordinate (MvPolynomial.C (-Complex.I))
    (chartConstant_degree_zero (-Complex.I)) yCoordinate_actual_phase_inverse

def yDirectAwayIota : YChartAway →+* YChartAway :=
  yActualPhaseToChart.comp (Away.map gradedIota yCoordinate)

set_option linter.defProp false in
def yActualPhaseToChart_square :=
  unitDegreeZeroChartMap_square (gradedIota yCoordinate) yCoordinate
    (MvPolynomial.C (-Complex.I)) (gradedIota.map_mem (coordinate_degree_one 1))
    (by norm_num) (chartConstant_degree_zero (-Complex.I)) yCoordinate_actual_phase_inverse

theorem yDirectAwayIota_mk (n : ℕ) (p : HomogeneousRing) (hp : p ∈ CMGrading n) :
    yDirectAwayIota (Away.mk CMGrading (coordinate_degree_one 1) n p (by simpa using hp)) =
      Away.mk CMGrading (coordinate_degree_one 1) n
        (gradedIota p * MvPolynomial.C (-Complex.I) ^ n)
        (by simpa using (SetLike.mul_mem_graded (gradedIota.map_mem hp)
          (SetLike.pow_mem_graded n (chartConstant_degree_zero (-Complex.I))))) := by
  unfold yDirectAwayIota yActualPhaseToChart
  rw [RingHom.comp_apply, Away.map_mk, unitDegreeZeroChartMap_mk]

theorem yDirectAwayIota_eq_existing : yDirectAwayIota = yAwayIota := by
  apply RingHom.ext
  intro p
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective CMGrading (coordinate_degree_one 1) p
  rw [yDirectAwayIota_mk n p (by simpa using hp), yAwayIota_mk n p (by simpa using hp)]

#print axioms yActualPhaseToChart_square
#print axioms yDirectAwayIota_eq_existing
end Holonics.Hodge.CMGraphSource
