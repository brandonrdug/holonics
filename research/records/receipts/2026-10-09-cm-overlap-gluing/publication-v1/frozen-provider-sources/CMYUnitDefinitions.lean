import CMYChartLocalization
import CMCoordinateTransport
import CMUnitDegreeZeroChart

/-! Honest unit rescaling of the Y denominator for the actual CM chart map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem chartConstant_degree_zero (c : ℂ) : MvPolynomial.C c ∈ CMGrading 0 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ c)
def yPhaseCoordinate : HomogeneousRing := MvPolynomial.C Complex.I * yCoordinate
abbrev YPhaseAway := Away CMGrading yPhaseCoordinate
theorem yPhaseCoordinate_degree_one : yPhaseCoordinate ∈ CMGrading 1 :=
  SetLike.mul_mem_graded (chartConstant_degree_zero Complex.I) (coordinate_degree_one 1)
theorem yPhaseCoordinate_factor : yPhaseCoordinate = yCoordinate * MvPolynomial.C Complex.I := by
  exact mul_comm _ _
theorem gradedIota_yPhase : gradedIota yCoordinate = yPhaseCoordinate := by
  calc
    gradedIota yCoordinate = homogeneousIota yCoordinate := rfl
    _ = MvPolynomial.C Complex.I * yCoordinate := by
      change homogeneousPullback Complex.I (MvPolynomial.X 1) = _
      rw [homogeneousPullback, MvPolynomial.aeval_X]
      rfl
    _ = _ := rfl
theorem yCoordinate_phase_inverse : yCoordinate = yPhaseCoordinate * MvPolynomial.C (-Complex.I) := by
  rw [yPhaseCoordinate_factor]
  have hc : (MvPolynomial.C Complex.I : HomogeneousRing) * MvPolynomial.C (-Complex.I) = 1 := by
    rw [← MvPolynomial.C_mul]
    norm_num
  calc
    yCoordinate = yCoordinate * (MvPolynomial.C Complex.I * MvPolynomial.C (-Complex.I)) := by rw [hc, mul_one]
    _ = _ := by ring

def yToPhaseChart : YChartAway →+* YPhaseAway :=
  awayMap CMGrading (chartConstant_degree_zero Complex.I) yPhaseCoordinate_factor
def yPhaseToChart : YPhaseAway →+* YChartAway :=
  unitDegreeZeroChartMap yPhaseCoordinate yCoordinate (MvPolynomial.C (-Complex.I))
    (chartConstant_degree_zero (-Complex.I)) yCoordinate_phase_inverse
def yRawAwayIota : YChartAway →+* YPhaseAway :=
  (awayCoordinateTransport gradedIota_yPhase).toRingHom.comp (Away.map gradedIota yCoordinate)
def yAwayIota : YChartAway →+* YChartAway :=
  yPhaseToChart.comp yRawAwayIota


#print axioms yAwayIota
end Holonics.Hodge.CMGraphSource
