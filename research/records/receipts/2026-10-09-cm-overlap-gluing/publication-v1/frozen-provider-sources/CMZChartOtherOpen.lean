import CMZChartSheaf
import CMYChartLocalization

/-! Actual Proj Z chart: membership in the other ambient basic open is
exactly nonvanishing of the degree-zero ratio Y/Z. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HomogeneousLocalization AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem zAwayι_mem_yBasicOpen (q : PrimeSpectrum ZChartAway) :
    Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num) q ∈
        Proj.basicOpen CMGrading yCoordinate ↔ zRatio 1 ∉ q.asIdeal := by
  rw [zAwayι_point]
  change yCoordinate ∉ ProjIsoSpecTopComponent.FromSpec.carrier
    (coordinate_degree_one 2) q ↔ _
  have h := ProjIsoSpecTopComponent.FromSpec.num_mem_carrier_iff
    (coordinate_degree_one 2) (by norm_num) q
    ⟨1, ⟨yCoordinate, by simpa only [yCoordinate] using coordinate_degree_one 1⟩,
      ⟨zCoordinate ^ 1, SetLike.pow_mem_graded 1 (coordinate_degree_one 2)⟩, ⟨1, rfl⟩⟩
  change yCoordinate ∈ ProjIsoSpecTopComponent.FromSpec.carrier
    (coordinate_degree_one 2) q ↔ zRatio 1 ∈ q.asIdeal at h
  exact not_congr h

#print axioms zAwayι_mem_yBasicOpen
end Holonics.Hodge.CMGraphSource
