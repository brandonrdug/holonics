import CMActualGraphAffineEquationCover

/-! Actual affine local equations for the diagonal ideal on the ambient cubic
product. The cover, regular generators, and ideal equalities are assembled
from the existing B/A/V/X diagonal face owners and the complement of the
actual diagonal support. No smoothness, Cartier-divisor, or intersection
degree theorem is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Holonics.Hodge.CMGraphSource

inductive CMActualDiagonalAffineIndex
  | B | A | V | X
  | away (U : CMActualAmbientProduct.affineOpens)
      (inside : U.1 ≤ idealComplementOpen cmComplexDiagonal.ker)

def cmActualDiagonalAffineOpen : CMActualDiagonalAffineIndex →
    CMActualAmbientProduct.Opens
  | .B => yDiagonalPAmbientOpen ''ᵁ ⊤
  | .A => yDiagonalQAmbientOpen ''ᵁ ⊤
  | .V => zDiagonalFactorAmbientOpen ''ᵁ ⊤
  | .X => zDiagonalVSumAmbientOpen ''ᵁ ⊤
  | .away U _ => U.1

theorem cmActualDiagonalAffineOpen_isAffine
    (i : CMActualDiagonalAffineIndex) :
    IsAffineOpen (cmActualDiagonalAffineOpen i) := by
  cases i with
  | B => exact (isAffineOpen_top _).image_of_isOpenImmersion yDiagonalPAmbientOpen
  | A => exact (isAffineOpen_top _).image_of_isOpenImmersion yDiagonalQAmbientOpen
  | V => exact (isAffineOpen_top _).image_of_isOpenImmersion zDiagonalFactorAmbientOpen
  | X => exact (isAffineOpen_top _).image_of_isOpenImmersion zDiagonalVSumAmbientOpen
  | away U _ => exact U.2

def cmActualDiagonalAffineEquation (i : CMActualDiagonalAffineIndex) :
    Γ(CMActualAmbientProduct, cmActualDiagonalAffineOpen i) := by
  cases i with
  | B =>
    exact spectrumImageEquation (.of (Localization.Away yDiagonalP))
      yDiagonalPAmbientOpen
      (algebraMap YProductRing (Localization.Away yDiagonalP) yDiagonalBEquation)
  | A =>
    exact spectrumImageEquation (.of (Localization.Away yDiagonalQ))
      yDiagonalQAmbientOpen
      (algebraMap YProductRing (Localization.Away yDiagonalQ) yDiagonalAEquation)
  | V =>
    exact spectrumImageEquation (.of (Localization.Away diagonalCubicFactor))
      zDiagonalFactorAmbientOpen
      (algebraMap ProductRing (Localization.Away diagonalCubicFactor) diagonalVEquation)
  | X =>
    exact spectrumImageEquation (.of (Localization.Away diagonalVSum))
      zDiagonalVSumAmbientOpen
      (algebraMap ProductRing (Localization.Away diagonalVSum) diagonalUEquation)
  | away _ _ => exact 1

theorem cmActualDiagonalAffineEquation_regular
    (i : CMActualDiagonalAffineIndex) :
    IsRegular (cmActualDiagonalAffineEquation i) := by
  cases i with
  | B =>
    exact spectrumImageEquation_regular (.of (Localization.Away yDiagonalP))
      yDiagonalPAmbientOpen
      (algebraMap YProductRing (Localization.Away yDiagonalP) yDiagonalBEquation)
      yDiagonalPActual_regular_equation.2
  | A =>
    exact spectrumImageEquation_regular (.of (Localization.Away yDiagonalQ))
      yDiagonalQAmbientOpen
      (algebraMap YProductRing (Localization.Away yDiagonalQ) yDiagonalAEquation)
      yDiagonalQActual_regular_equation.2
  | V =>
    exact spectrumImageEquation_regular (.of (Localization.Away diagonalCubicFactor))
      zDiagonalFactorAmbientOpen
      (algebraMap ProductRing (Localization.Away diagonalCubicFactor) diagonalVEquation)
      zDiagonalFactorActual_regular_equation.2
  | X =>
    exact spectrumImageEquation_regular (.of (Localization.Away diagonalVSum))
      zDiagonalVSumAmbientOpen
      (algebraMap ProductRing (Localization.Away diagonalVSum) diagonalUEquation)
      zDiagonalVSumActual_regular_equation.2
  | away _ _ => exact isRegular_one

theorem cmActualDiagonalAffineEquation_ideal
    (i : CMActualDiagonalAffineIndex) :
    cmComplexDiagonal.ker.ideal
      ⟨cmActualDiagonalAffineOpen i, cmActualDiagonalAffineOpen_isAffine i⟩ =
        Ideal.span {cmActualDiagonalAffineEquation i} := by
  cases i with
  | B =>
    exact spectrumImageEquation_ideal cmComplexDiagonal.ker
      (.of (Localization.Away yDiagonalP)) yDiagonalPAmbientOpen
      (algebraMap YProductRing (Localization.Away yDiagonalP) yDiagonalBEquation)
      yDiagonalPActual_regular_equation.1
  | A =>
    exact spectrumImageEquation_ideal cmComplexDiagonal.ker
      (.of (Localization.Away yDiagonalQ)) yDiagonalQAmbientOpen
      (algebraMap YProductRing (Localization.Away yDiagonalQ) yDiagonalAEquation)
      yDiagonalQActual_regular_equation.1
  | V =>
    exact spectrumImageEquation_ideal cmComplexDiagonal.ker
      (.of (Localization.Away diagonalCubicFactor)) zDiagonalFactorAmbientOpen
      (algebraMap ProductRing (Localization.Away diagonalCubicFactor) diagonalVEquation)
      zDiagonalFactorActual_regular_equation.1
  | X =>
    exact spectrumImageEquation_ideal cmComplexDiagonal.ker
      (.of (Localization.Away diagonalVSum)) zDiagonalVSumAmbientOpen
      (algebraMap ProductRing (Localization.Away diagonalVSum) diagonalUEquation)
      zDiagonalVSumActual_regular_equation.1
  | away U hU =>
    let : IsAffine U.1 := U.2
    have hrestrict : cmComplexDiagonal.ker.comap U.1.ι = ⊤ := by
      rw [← Scheme.homOfLE_ι CMActualAmbientProduct hU,
        Scheme.IdealSheafData.comap_comp, idealComplementOpen_unit,
        Scheme.IdealSheafData.comap_top]
    have h := affineImageUnitIdeal cmComplexDiagonal.ker U.1.ι hrestrict
    have he :
        (⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩ :
          CMActualAmbientProduct.affineOpens) = U := by
      exact Subtype.ext ((Scheme.Hom.image_top_eq_opensRange U.1.ι).trans
        (Scheme.Opens.opensRange_ι U.1))
    have htop : cmComplexDiagonal.ker.ideal U = ⊤ :=
      Eq.mp (congrArg (fun W : CMActualAmbientProduct.affineOpens =>
        cmComplexDiagonal.ker.ideal W = ⊤) he) h
    simpa only [cmActualDiagonalAffineOpen, cmActualDiagonalAffineEquation,
      Ideal.span_singleton_one] using htop

theorem cmActualDiagonalAffineOpen_point_cover (p : CMActualAmbientProduct) :
    ∃ i, p ∈ cmActualDiagonalAffineOpen i := by
  rcases actual_diagonal_global_regular_open_cover p with h | h | h | h | h
  · exact ⟨.B, by
      simpa only [cmActualDiagonalAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h⟩
  · exact ⟨.A, by
      simpa only [cmActualDiagonalAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h⟩
  · exact ⟨.V, by
      simpa only [cmActualDiagonalAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h⟩
  · exact ⟨.X, by
      simpa only [cmActualDiagonalAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h⟩
  · obtain ⟨U, hU, hp, hUC⟩ := exists_isAffineOpen_mem_and_subset h
    exact ⟨.away ⟨U, hU⟩ hUC, hp⟩

theorem cmActualDiagonalAffineOpen_coversTop :
    (Opens.grothendieckTopology CMActualAmbientProduct).CoversTop
      cmActualDiagonalAffineOpen := by
  intro W
  rw [Opens.mem_grothendieckTopology]
  intro p hp
  obtain ⟨i, hi⟩ := cmActualDiagonalAffineOpen_point_cover p
  refine ⟨W ⊓ cmActualDiagonalAffineOpen i, homOfLE inf_le_left, ?_, ⟨hp, hi⟩⟩
  exact ⟨i, ⟨homOfLE inf_le_right⟩⟩

/-- The actual diagonal ideal is locally generated by a regular section on a
cover by affine opens: the local Cartier condition needed before any global
intersection calculation. -/
theorem cmActualDiagonal_local_regular_principal_data :
    (∀ i, IsAffineOpen (cmActualDiagonalAffineOpen i)) ∧
    (Opens.grothendieckTopology CMActualAmbientProduct).CoversTop
      cmActualDiagonalAffineOpen ∧
    (∀ i, IsRegular (cmActualDiagonalAffineEquation i)) ∧
    (∀ i, cmComplexDiagonal.ker.ideal
      ⟨cmActualDiagonalAffineOpen i, cmActualDiagonalAffineOpen_isAffine i⟩ =
        Ideal.span {cmActualDiagonalAffineEquation i}) := by
  exact ⟨cmActualDiagonalAffineOpen_isAffine,
    cmActualDiagonalAffineOpen_coversTop,
    cmActualDiagonalAffineEquation_regular,
    cmActualDiagonalAffineEquation_ideal⟩

#print axioms cmActualDiagonalAffineOpen_isAffine
#print axioms cmActualDiagonalAffineEquation_regular
#print axioms cmActualDiagonalAffineEquation_ideal
#print axioms cmActualDiagonalAffineOpen_point_cover
#print axioms cmActualDiagonalAffineOpen_coversTop
#print axioms cmActualDiagonal_local_regular_principal_data
end Holonics.Hodge.CMGraphSource
