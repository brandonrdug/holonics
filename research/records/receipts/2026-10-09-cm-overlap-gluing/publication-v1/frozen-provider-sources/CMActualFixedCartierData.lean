import CMActualRestrictedFixedSupportCover
import CMActualGraphAffineEquationCover

/-! The actual fixed inclusion has an affine regular-principal equation cover.
The actual smaller-open support cover is consumed, and the support complement
is refined by affine opens carrying equation 1. The equations are transported
by the actual open immersion appIso, not assumed local isomorphisms.

agent-inferred: adapt the existing diagonal cover construction to the actual
fixed kernel, keeping its actual Y/Z regularity proofs. This avoids treating
ambient regularity as preserved by an arbitrary pullback. No local-stalk
length, intersection degree, divisor-cycle class or Hodge pairing is asserted.
The helical pair interaction and its faces, cell holonomy and tube stay
attached, with helix, pair and tower thread retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Holonics.Hodge.CMGraphSource

inductive CMActualFixedAffineIndex
  | Y | Z
  | away (U : CMProjectiveCubic.affineOpens)
      (inside : U.1 ≤ idealComplementOpen cmFixedInclusion.ker)

def cmActualFixedAffineOpen : CMActualFixedAffineIndex →
    CMProjectiveCubic.Opens
  | .Y => cmActualRestrictedYCurveOpen ''ᵁ ⊤
  | .Z => cmActualRestrictedZCurveOpen ''ᵁ ⊤
  | .away U _ => U.1

theorem cmActualFixedAffineOpen_isAffine
    (i : CMActualFixedAffineIndex) :
    IsAffineOpen (cmActualFixedAffineOpen i) := by
  cases i with
  | Y => exact (isAffineOpen_top _).image_of_isOpenImmersion cmActualRestrictedYCurveOpen
  | Z => exact (isAffineOpen_top _).image_of_isOpenImmersion cmActualRestrictedZCurveOpen
  | away U _ => exact U.2

def cmActualFixedAffineEquation (i : CMActualFixedAffineIndex) :
    Γ(CMProjectiveCubic, cmActualFixedAffineOpen i) := by
  cases i with
  | Y =>
    exact spectrumImageEquation (.of YRestrictedQAway)
      cmActualRestrictedYCurveOpen
      yRestrictedA
  | Z =>
    exact spectrumImageEquation (.of ActualRestrictedZRing)
      cmActualRestrictedZCurveOpen
      (algebraMap CurveRing ActualRestrictedZRing v)
  | away _ _ => exact 1

theorem cmActualFixedAffineEquation_regular
    (i : CMActualFixedAffineIndex) :
    IsRegular (cmActualFixedAffineEquation i) := by
  cases i with
  | Y =>
    exact spectrumImageEquation_regular (.of YRestrictedQAway)
      cmActualRestrictedYCurveOpen
      yRestrictedA
      cmActualFixedYRestricted_regular_equation.2
  | Z =>
    exact spectrumImageEquation_regular (.of ActualRestrictedZRing)
      cmActualRestrictedZCurveOpen
      (algebraMap CurveRing ActualRestrictedZRing v)
      cmActualFixedZRestricted_regular_equation.2
  | away _ _ => exact isRegular_one

theorem cmActualFixedAffineEquation_ideal
    (i : CMActualFixedAffineIndex) :
    cmFixedInclusion.ker.ideal
      ⟨cmActualFixedAffineOpen i, cmActualFixedAffineOpen_isAffine i⟩ =
        Ideal.span {cmActualFixedAffineEquation i} := by
  cases i with
  | Y =>
    exact spectrumImageEquation_ideal cmFixedInclusion.ker
      (.of YRestrictedQAway) cmActualRestrictedYCurveOpen
      yRestrictedA
      cmActualFixedYRestricted_regular_equation.1
  | Z =>
    exact spectrumImageEquation_ideal cmFixedInclusion.ker
      (.of ActualRestrictedZRing) cmActualRestrictedZCurveOpen
      (algebraMap CurveRing ActualRestrictedZRing v)
      cmActualFixedZRestricted_regular_equation.1
  | away U hU =>
    let : IsAffine U.1 := U.2
    have hrestrict : cmFixedInclusion.ker.comap U.1.ι = ⊤ := by
      rw [← Scheme.homOfLE_ι CMProjectiveCubic hU,
        Scheme.IdealSheafData.comap_comp, idealComplementOpen_unit,
        Scheme.IdealSheafData.comap_top]
    have h := affineImageUnitIdeal cmFixedInclusion.ker U.1.ι hrestrict
    have he :
        (⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩ :
          CMProjectiveCubic.affineOpens) = U := by
      exact Subtype.ext ((Scheme.Hom.image_top_eq_opensRange U.1.ι).trans
        (Scheme.Opens.opensRange_ι U.1))
    have htop : cmFixedInclusion.ker.ideal U = ⊤ :=
      Eq.mp (congrArg (fun W : CMProjectiveCubic.affineOpens =>
        cmFixedInclusion.ker.ideal W = ⊤) he) h
    simpa only [cmActualFixedAffineOpen, cmActualFixedAffineEquation,
      Ideal.span_singleton_one] using htop

theorem cmActualFixedAffineOpen_point_cover (p : CMProjectiveCubic) :
    ∃ i, p ∈ cmActualFixedAffineOpen i := by
  rcases cmActualFixed_restricted_complement_cover p with h | h | h
  · exact ⟨.Y, by
      simpa only [cmActualFixedAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h⟩
  · exact ⟨.Z, by
      simpa only [cmActualFixedAffineOpen, Scheme.Hom.image_top_eq_opensRange] using h⟩
  · obtain ⟨U, hU, hp, hUC⟩ := exists_isAffineOpen_mem_and_subset h
    exact ⟨.away ⟨U, hU⟩ hUC, hp⟩

theorem cmActualFixedAffineOpen_coversTop :
    (Opens.grothendieckTopology CMProjectiveCubic).CoversTop
      cmActualFixedAffineOpen := by
  intro W
  rw [Opens.mem_grothendieckTopology]
  intro p hp
  obtain ⟨i, hi⟩ := cmActualFixedAffineOpen_point_cover p
  refine ⟨W ⊓ cmActualFixedAffineOpen i, homOfLE inf_le_left, ?_, ⟨hp, hi⟩⟩
  exact ⟨i, ⟨homOfLE inf_le_right⟩⟩

/-- The actual fixed ideal is locally generated by a regular section on a
cover by affine opens: the local Cartier condition needed before any global
intersection calculation. -/
theorem cmActualFixed_local_regular_principal_data :
    (∀ i, IsAffineOpen (cmActualFixedAffineOpen i)) ∧
    (Opens.grothendieckTopology CMProjectiveCubic).CoversTop
      cmActualFixedAffineOpen ∧
    (∀ i, IsRegular (cmActualFixedAffineEquation i)) ∧
    (∀ i, cmFixedInclusion.ker.ideal
      ⟨cmActualFixedAffineOpen i, cmActualFixedAffineOpen_isAffine i⟩ =
        Ideal.span {cmActualFixedAffineEquation i}) := by
  exact ⟨cmActualFixedAffineOpen_isAffine,
    cmActualFixedAffineOpen_coversTop,
    cmActualFixedAffineEquation_regular,
    cmActualFixedAffineEquation_ideal⟩

#print axioms cmActualFixedAffineOpen_isAffine
#print axioms cmActualFixedAffineEquation_regular
#print axioms cmActualFixedAffineEquation_ideal
#print axioms cmActualFixedAffineOpen_point_cover
#print axioms cmActualFixedAffineOpen_coversTop
#print axioms cmActualFixed_local_regular_principal_data
end Holonics.Hodge.CMGraphSource
