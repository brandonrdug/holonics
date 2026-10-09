import CMYUnitDefinitions

/-! Exact fractions for the constructed actual Y chart ring map; the scheme square remains separate. -/
noncomputable section
open HomogeneousLocalization
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yAwayIota_mk (n : ℕ) (p : HomogeneousRing) (hp : p ∈ CMGrading n) :
    yAwayIota (Away.mk CMGrading (coordinate_degree_one 1) n p (by simpa using hp)) =
      Away.mk CMGrading (coordinate_degree_one 1) n
        (gradedIota p * MvPolynomial.C (-Complex.I) ^ n)
        (by simpa using (SetLike.mul_mem_graded (gradedIota.map_mem hp)
          (SetLike.pow_mem_graded n (chartConstant_degree_zero (-Complex.I))))) := by
  unfold yAwayIota yRawAwayIota yPhaseToChart
  rw [RingHom.comp_apply, RingHom.comp_apply, Away.map_mk]
  change unitDegreeZeroChartMap _ _ _ _ _ (awayCoordinateTransport gradedIota_yPhase
    (Away.mk CMGrading _ n (gradedIota p) _)) = _
  rw [awayCoordinateTransport_mk (hg := yPhaseCoordinate_degree_one),
    unitDegreeZeroChartMap_mk]

#print axioms yAwayIota_mk
end Holonics.Hodge.CMGraphSource
