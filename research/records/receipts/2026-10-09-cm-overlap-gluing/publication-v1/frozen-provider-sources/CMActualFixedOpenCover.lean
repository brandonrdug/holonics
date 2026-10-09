import CMYActualFixedPointMap
import CMZActualFixedPointIso

/-! The actual graph-diagonal fixed scheme is covered by the two pullbacks
already proved isomorphic to Spec C. This does not yet assert disjointness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

instance yChartInclusion_isOpenImmersion :
    IsOpenImmersion (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) := by infer_instance
instance zChartInclusion_isOpenImmersion :
    IsOpenImmersion (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) := by infer_instance

def yFixedOpenMap :
    pullback cmFixedInclusion (yReducedCubicChartIso.inv ≫ yReducedCubicOpen.ι) ⟶
      CMProjectiveFixedScheme := pullback.fst _ _
def zFixedOpenMap :
    pullback cmFixedInclusion (zReducedCubicChartIso.inv ≫ zCubicOpen.ι) ⟶
      CMProjectiveFixedScheme := pullback.fst _ _
instance yFixedOpenMap_isOpenImmersion : IsOpenImmersion yFixedOpenMap := by
  dsimp only [yFixedOpenMap]
  infer_instance
instance zFixedOpenMap_isOpenImmersion : IsOpenImmersion zFixedOpenMap := by
  dsimp only [zFixedOpenMap]
  infer_instance

theorem yFixedOpen_range :
    yFixedOpenMap.opensRange = cmFixedInclusion ⁻¹ᵁ yReducedCubicOpen := by
  dsimp only [yFixedOpenMap]
  rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]
theorem zFixedOpen_range : zFixedOpenMap.opensRange = cmFixedInclusion ⁻¹ᵁ zCubicOpen := by
  dsimp only [zFixedOpenMap]
  rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

theorem actualFixed_opens_cover : yFixedOpenMap.opensRange ⊔ zFixedOpenMap.opensRange = ⊤ := by
  rw [yFixedOpen_range, zFixedOpen_range]
  ext p
  change (cmFixedInclusion p ∈ yReducedCubicOpen ∨ cmFixedInclusion p ∈ zCubicOpen) ↔ True
  exact iff_true_intro (cubic_chart_opens_cover (cmFixedInclusion p))

#print axioms yFixedOpen_range
#print axioms zFixedOpen_range
#print axioms actualFixed_opens_cover
end Holonics.Hodge.CMGraphSource
