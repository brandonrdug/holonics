import CMYMonoOnly

/-! The existing inclusion square uses right-associated composition. The
fixed-chart restriction instead expects (chartInv >> inclusion) >> iota.
Supply Category.assoc explicitly, rather than asking definitional equality
to normalize the large concrete scheme composite. -/
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

theorem yFixedChart_associated_square :
    Spec.map (CommRingCat.ofHom yIotaCoordinateRing) ≫
        (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) =
      (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) ≫ cubicIotaHom := by
  rw [Category.assoc]
  exact yCubicChart_iota_inclusion_square.symm

#print axioms yFixedChart_associated_square
end Holonics.Hodge.CMGraphSource
