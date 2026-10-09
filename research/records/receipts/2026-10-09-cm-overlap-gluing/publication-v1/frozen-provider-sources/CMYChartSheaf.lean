import CMYChartLocalization
import CMZChartSheaf
import CMProjectiveCubic

/-!
The actual Y Proj chart map is compared to the spectrum-point correspondence.
The reduced cubic's chart ideal is derived from its vanishing ideal, rather
than postulated as the principal cubic ideal.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def yCubicChartIdeal : Ideal YChartAway := Ideal.span {yNormalizedCubic}
theorem yChart_correspondence_cubic (q : PrimeSpectrum YChartAway) :
    (ProjIsoSpecTopComponent.FromSpec.toFun
      (coordinate_degree_one 1) (by norm_num) q).1 ∈ cubicProjectiveLocus ↔
      q ∈ PrimeSpectrum.zeroLocus (yCubicChartIdeal : Set YChartAway) := by
  change ({projectiveCubic} : Set HomogeneousRing) ⊆
    (ProjIsoSpecTopComponent.FromSpec.carrier.asHomogeneousIdeal
      (coordinate_degree_one 1) (by norm_num) q : Set HomogeneousRing) ↔ _
  simp only [Set.singleton_subset_iff]
  change projectiveCubic ∈
    ProjIsoSpecTopComponent.FromSpec.carrier
      (coordinate_degree_one 1) q ↔ _
  rw [ProjIsoSpecTopComponent.FromSpec.num_mem_carrier_iff
    (coordinate_degree_one 1) (by norm_num) q
    ⟨3, ⟨projectiveCubic, cubic_degree_three⟩,
      ⟨yCoordinate ^ 3, SetLike.pow_mem_graded 3 (coordinate_degree_one 1)⟩, ⟨3, rfl⟩⟩]
  change yNormalizedCubic ∈ q.asIdeal ↔ yCubicChartIdeal ≤ q.asIdeal
  rw [yCubicChartIdeal, Ideal.span_le, Set.singleton_subset_iff]
  rfl


def yAmbientAffineOpen : CMProjectiveAmbient.affineOpens :=
  ⟨Proj.basicOpen CMGrading yCoordinate,
    Proj.isAffineOpen_basicOpen CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num)⟩
def yAmbientChartRingIso : CommRingCat.of YChartAway ≅ Γ(CMProjectiveAmbient, yAmbientAffineOpen) :=
  Proj.basicOpenIsoAway CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num)

theorem yChart_toLRS :
    (Proj.basicOpenToSpec CMGrading yCoordinate).toLRSHom =
      ProjectiveSpectrum.Proj.toSpec CMGrading yCoordinate := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

theorem yAwayι_point (q : PrimeSpectrum YChartAway) :
    Proj.awayι CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num) q =
      (ProjIsoSpecTopComponent.FromSpec.toFun
        (coordinate_degree_one 1) (by norm_num) q).1 := by
  let e := Proj.basicOpenIsoSpec CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num)
  have he : e.hom (ProjIsoSpecTopComponent.FromSpec.toFun
      (coordinate_degree_one 1) (by norm_num) q) = q := by
    change (Proj.basicOpenToSpec CMGrading yCoordinate).toLRSHom.base _ = q
    rw [yChart_toLRS]
    exact (ProjectiveSpectrum.Proj.toSpec_base_apply_eq CMGrading _).trans
      (ProjIsoSpecTopComponent.toSpec_fromSpec _ _ _ _)
  have hi : e.inv q = ProjIsoSpecTopComponent.FromSpec.toFun
      (coordinate_degree_one 1) (by norm_num) q := by
    calc
      e.inv q = e.inv (e.hom (ProjIsoSpecTopComponent.FromSpec.toFun
        (coordinate_degree_one 1) (by norm_num) q)) := congrArg (fun p => e.inv p) he.symm
      _ = _ := by
        change (e.hom ≫ e.inv) _ = _
        rw [Iso.hom_inv_id]
        rfl
  change (Proj.basicOpen CMGrading yCoordinate).ι (e.inv q) = _
  rw [hi]
  rfl

theorem yAwayι_cubic_preimage :
    (Proj.awayι CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num)) ⁻¹'
      cubicProjectiveLocus = PrimeSpectrum.zeroLocus (yCubicChartIdeal : Set YChartAway) := by
  ext q
  change Proj.awayι CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num) q ∈
    cubicProjectiveLocus ↔ _
  have he := congrArg (fun p : CMProjectiveAmbient => p ∈ cubicProjectiveLocus)
    (yAwayι_point q)
  rw [he]
  exact yChart_correspondence_cubic q

theorem ySpecChart_fromSpec :
    Spec.map yAmbientChartRingIso.inv ≫ yAmbientAffineOpen.2.fromSpec =
      Proj.awayι CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num) := by
  let eS := Proj.basicOpenIsoSpec CMGrading yCoordinate (coordinate_degree_one 1) (by norm_num)
  have he : eS.hom = yAmbientAffineOpen.1.toSpecΓ ≫ Spec.map yAmbientChartRingIso.hom := rfl
  apply (cancel_epi eS.hom).mp
  change eS.hom ≫ Spec.map yAmbientChartRingIso.inv ≫ yAmbientAffineOpen.2.fromSpec =
    eS.hom ≫ eS.inv ≫ yAmbientAffineOpen.1.ι
  calc
    _ = yAmbientAffineOpen.1.toSpecΓ ≫ Spec.map yAmbientChartRingIso.hom ≫
        Spec.map yAmbientChartRingIso.inv ≫ yAmbientAffineOpen.2.fromSpec := by
      rw [he, Category.assoc]
    _ = yAmbientAffineOpen.1.toSpecΓ ≫ yAmbientAffineOpen.2.fromSpec := by
      rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
    _ = yAmbientAffineOpen.1.ι := IsAffineOpen.toSpecΓ_fromSpec _
    _ = _ := by rw [Iso.hom_inv_id_assoc]

theorem yReducedChartIdeal_radical :
    (cubicIdealSheaf.ideal yAmbientAffineOpen).comap yAmbientChartRingIso.hom.hom =
      yCubicChartIdeal.radical := by
  rw [cubicIdealSheaf, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change (PrimeSpectrum.vanishingIdeal (yAmbientAffineOpen.2.fromSpec ⁻¹'
    (cubicClosed : Set CMProjectiveAmbient))).comap
      yAmbientChartRingIso.commRingCatIsoToRingEquiv.toRingHom = _
  rw [vanishingIdeal_comap_equiv]
  have he : PrimeSpectrum.comap yAmbientChartRingIso.inv.hom ⁻¹'
      (yAmbientAffineOpen.2.fromSpec ⁻¹' (cubicClosed : Set CMProjectiveAmbient)) =
      PrimeSpectrum.zeroLocus (yCubicChartIdeal : Set YChartAway) := by
    change (Spec.map yAmbientChartRingIso.inv ≫ yAmbientAffineOpen.2.fromSpec) ⁻¹'
      cubicProjectiveLocus = _
    rw [ySpecChart_fromSpec]
    exact yAwayι_cubic_preimage
  change PrimeSpectrum.vanishingIdeal (PrimeSpectrum.comap yAmbientChartRingIso.inv.hom ⁻¹'
    (yAmbientAffineOpen.2.fromSpec ⁻¹' (cubicClosed : Set CMProjectiveAmbient))) = _
  exact (congrArg PrimeSpectrum.vanishingIdeal he).trans
    (PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical _)

#print axioms yChart_toLRS
#print axioms yAwayι_point
#print axioms yAwayι_cubic_preimage
#print axioms ySpecChart_fromSpec
#print axioms yReducedChartIdeal_radical
end Holonics.Hodge.CMGraphSource
