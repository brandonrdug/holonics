import CMActualAffineIdealTransport
import CMGlobalRegularEquationCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-! Fresh actual cover reconstruction; historical receipts do not authenticate it. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Holonics.Hodge.CMGraphSource

inductive CMGraphAffineEquationIndex
  | B | A | V | X
  | away (U : CMActualAmbientProduct.affineOpens)
      (inside : U.1 ≤ idealComplementOpen cmConcreteComplexGraph.ker)

def cmGraphActualAffineOpen : CMGraphAffineEquationIndex → CMActualAmbientProduct.Opens
  | .B => yGraphPAmbientOpen ''ᵁ ⊤
  | .A => yGraphQAmbientOpen ''ᵁ ⊤
  | .V => zGraphFactorAmbientOpen ''ᵁ ⊤
  | .X => zGraphVSumAmbientOpen ''ᵁ ⊤
  | .away U _ => U.1

theorem cmGraphActualAffineOpen_isAffine (i : CMGraphAffineEquationIndex) :
    IsAffineOpen (cmGraphActualAffineOpen i) := by
  cases i with
  | B => exact (isAffineOpen_top _).image_of_isOpenImmersion yGraphPAmbientOpen
  | A => exact (isAffineOpen_top _).image_of_isOpenImmersion yGraphQAmbientOpen
  | V => exact (isAffineOpen_top _).image_of_isOpenImmersion zGraphFactorAmbientOpen
  | X => exact (isAffineOpen_top _).image_of_isOpenImmersion zGraphVSumAmbientOpen
  | away U _ => exact U.2

def cmGraphActualAffineEquation (i : CMGraphAffineEquationIndex) :
    Γ(CMActualAmbientProduct, cmGraphActualAffineOpen i) := by
  cases i with
  | B =>
    exact spectrumImageEquation (.of (Localization.Away yGraphP)) yGraphPAmbientOpen
      (algebraMap YProductRing (Localization.Away yGraphP) yGraphBEquation)
  | A =>
    exact spectrumImageEquation (.of (Localization.Away yGraphQ)) yGraphQAmbientOpen
      (algebraMap YProductRing (Localization.Away yGraphQ) yGraphAEquation)
  | V =>
    exact spectrumImageEquation (.of (Localization.Away graphCubicFactor))
      zGraphFactorAmbientOpen
      (algebraMap ProductRing (Localization.Away graphCubicFactor) graphVEquation)
  | X =>
    exact spectrumImageEquation (.of (Localization.Away graphVSum)) zGraphVSumAmbientOpen
      (algebraMap ProductRing (Localization.Away graphVSum) graphXEquation)
  | away _ _ => exact 1

theorem cmGraphActualAffineEquation_regular (i : CMGraphAffineEquationIndex) :
    IsRegular (cmGraphActualAffineEquation i) := by
  cases i with
  | B =>
    exact spectrumImageEquation_regular (.of (Localization.Away yGraphP)) yGraphPAmbientOpen
      (algebraMap YProductRing (Localization.Away yGraphP) yGraphBEquation)
      yGraphPActual_regular_equation.2
  | A =>
    exact spectrumImageEquation_regular (.of (Localization.Away yGraphQ)) yGraphQAmbientOpen
      (algebraMap YProductRing (Localization.Away yGraphQ) yGraphAEquation)
      yGraphQActual_regular_equation.2
  | V =>
    exact spectrumImageEquation_regular (.of (Localization.Away graphCubicFactor)) zGraphFactorAmbientOpen
      (algebraMap ProductRing (Localization.Away graphCubicFactor) graphVEquation)
      zGraphFactorActual_regular_equation.2
  | X =>
    exact spectrumImageEquation_regular (.of (Localization.Away graphVSum)) zGraphVSumAmbientOpen
      (algebraMap ProductRing (Localization.Away graphVSum) graphXEquation)
      zGraphVSumActual_regular_equation.2
  | away _ _ => exact isRegular_one

theorem cmGraphActualAffineEquation_ideal (i : CMGraphAffineEquationIndex) :
    cmConcreteComplexGraph.ker.ideal
      ⟨cmGraphActualAffineOpen i, cmGraphActualAffineOpen_isAffine i⟩ =
        Ideal.span {cmGraphActualAffineEquation i} := by
  cases i with
  | B =>
    exact spectrumImageEquation_ideal cmConcreteComplexGraph.ker
      (.of (Localization.Away yGraphP)) yGraphPAmbientOpen
      (algebraMap YProductRing (Localization.Away yGraphP) yGraphBEquation)
      yGraphPActual_regular_equation.1
  | A =>
    exact spectrumImageEquation_ideal cmConcreteComplexGraph.ker
      (.of (Localization.Away yGraphQ)) yGraphQAmbientOpen
      (algebraMap YProductRing (Localization.Away yGraphQ) yGraphAEquation)
      yGraphQActual_regular_equation.1
  | V =>
    exact spectrumImageEquation_ideal cmConcreteComplexGraph.ker
      (.of (Localization.Away graphCubicFactor)) zGraphFactorAmbientOpen
      (algebraMap ProductRing (Localization.Away graphCubicFactor) graphVEquation)
      zGraphFactorActual_regular_equation.1
  | X =>
    exact spectrumImageEquation_ideal cmConcreteComplexGraph.ker
      (.of (Localization.Away graphVSum)) zGraphVSumAmbientOpen
      (algebraMap ProductRing (Localization.Away graphVSum) graphXEquation)
      zGraphVSumActual_regular_equation.1
  | away U hU =>
    let : IsAffine U.1 := U.2
    have hrestrict : cmConcreteComplexGraph.ker.comap U.1.ι = ⊤ := by
      rw [← Scheme.homOfLE_ι CMActualAmbientProduct hU,
        Scheme.IdealSheafData.comap_comp, idealComplementOpen_unit,
        Scheme.IdealSheafData.comap_top]
    have h := affineImageUnitIdeal cmConcreteComplexGraph.ker U.1.ι hrestrict
    -- agent-inferred: ideal's section-ring codomain depends on the full affine
    -- open. Transport its proposition through equality of affine-open indices.
    have he :
        (⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩ :
          CMActualAmbientProduct.affineOpens) = U := by
      exact Subtype.ext ((Scheme.Hom.image_top_eq_opensRange U.1.ι).trans
        (Scheme.Opens.opensRange_ι U.1))
    have htop : cmConcreteComplexGraph.ker.ideal U = ⊤ :=
      Eq.mp (congrArg (fun W : CMActualAmbientProduct.affineOpens =>
        cmConcreteComplexGraph.ker.ideal W = ⊤) he) h
    simpa only [cmGraphActualAffineOpen, cmGraphActualAffineEquation,
      Ideal.span_singleton_one] using htop

theorem cmGraphActualAffineOpen_point_cover (p : CMActualAmbientProduct) :
    ∃ i, p ∈ cmGraphActualAffineOpen i := by
  rcases actual_graph_global_regular_open_cover p with h | h | h | h | h
  · refine ⟨.B, ?_⟩
    simpa only [cmGraphActualAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h
  · refine ⟨.A, ?_⟩
    simpa only [cmGraphActualAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h
  · refine ⟨.V, ?_⟩
    simpa only [cmGraphActualAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h
  · refine ⟨.X, ?_⟩
    simpa only [cmGraphActualAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h
  · obtain ⟨U, hU, hp, hUC⟩ := exists_isAffineOpen_mem_and_subset h
    exact ⟨.away ⟨U, hU⟩ hUC, hp⟩

theorem cmGraphActualAffineOpen_coversTop :
    (Opens.grothendieckTopology CMActualAmbientProduct).CoversTop cmGraphActualAffineOpen := by
  intro W
  rw [Opens.mem_grothendieckTopology]
  intro p hp
  obtain ⟨i, hi⟩ := cmGraphActualAffineOpen_point_cover p
  refine ⟨W ⊓ cmGraphActualAffineOpen i, homOfLE inf_le_left, ?_, ⟨hp, hi⟩⟩
  exact ⟨i, ⟨homOfLE inf_le_right⟩⟩

#print axioms cmGraphActualAffineOpen_isAffine
#print axioms cmGraphActualAffineEquation_regular
#print axioms cmGraphActualAffineEquation_ideal
#print axioms cmGraphActualAffineOpen_point_cover
#print axioms cmGraphActualAffineOpen_coversTop
end Holonics.Hodge.CMGraphSource
