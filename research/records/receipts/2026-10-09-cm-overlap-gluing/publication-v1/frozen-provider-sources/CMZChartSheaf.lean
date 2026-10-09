import CMZChartEquation
import CMProjectiveCubic

/-!
The actual Proj chart map is compared to the spectrum-point correspondence.
The reduced cubic's chart ideal is derived from its vanishing ideal, rather
than postulated as the principal cubic ideal.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace Holonics.Hodge.CMGraphSource
attribute [local instance] MvPolynomial.gradedAlgebra

def zAmbientAffineOpen : CMProjectiveAmbient.affineOpens :=
  ⟨Proj.basicOpen CMGrading zCoordinate,
    Proj.isAffineOpen_basicOpen CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num)⟩
def zAmbientChartRingIso : CommRingCat.of ZChartAway ≅ Γ(CMProjectiveAmbient, zAmbientAffineOpen) :=
  Proj.basicOpenIsoAway CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num)

theorem zChart_toLRS :
    (Proj.basicOpenToSpec CMGrading zCoordinate).toLRSHom =
      ProjectiveSpectrum.Proj.toSpec CMGrading zCoordinate := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

theorem zAwayι_point (q : PrimeSpectrum ZChartAway) :
    Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num) q =
      (ProjIsoSpecTopComponent.FromSpec.toFun
        (coordinate_degree_one 2) (by norm_num) q).1 := by
  let e := Proj.basicOpenIsoSpec CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num)
  have he : e.hom (ProjIsoSpecTopComponent.FromSpec.toFun
      (coordinate_degree_one 2) (by norm_num) q) = q := by
    change (Proj.basicOpenToSpec CMGrading zCoordinate).toLRSHom.base _ = q
    rw [zChart_toLRS]
    exact (ProjectiveSpectrum.Proj.toSpec_base_apply_eq CMGrading _).trans
      (ProjIsoSpecTopComponent.toSpec_fromSpec _ _ _ _)
  have hi : e.inv q = ProjIsoSpecTopComponent.FromSpec.toFun
      (coordinate_degree_one 2) (by norm_num) q := by
    calc
      e.inv q = e.inv (e.hom (ProjIsoSpecTopComponent.FromSpec.toFun
        (coordinate_degree_one 2) (by norm_num) q)) := congrArg (fun p => e.inv p) he.symm
      _ = _ := by
        change (e.hom ≫ e.inv) _ = _
        rw [Iso.hom_inv_id]
        rfl
  change (Proj.basicOpen CMGrading zCoordinate).ι (e.inv q) = _
  rw [hi]
  rfl

theorem zAwayι_cubic_preimage :
    (Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num)) ⁻¹'
      cubicProjectiveLocus = PrimeSpectrum.zeroLocus (zCubicChartIdeal : Set ZChartAway) := by
  ext q
  change Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num) q ∈
    cubicProjectiveLocus ↔ _
  have he := congrArg (fun p : CMProjectiveAmbient => p ∈ cubicProjectiveLocus)
    (zAwayι_point q)
  rw [he]
  exact zChart_correspondence_cubic q

theorem vanishingIdeal_comap_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (T : Set (PrimeSpectrum S)) :
    (PrimeSpectrum.vanishingIdeal T).comap e.toRingHom =
      PrimeSpectrum.vanishingIdeal (PrimeSpectrum.comap e.symm.toRingHom ⁻¹' T) := by
  ext x
  simp only [Ideal.mem_comap, PrimeSpectrum.mem_vanishingIdeal, Set.mem_preimage]
  constructor
  · intro h q hq
    have hx := h (PrimeSpectrum.comap e.symm.toRingHom q) hq
    change e.symm (e x) ∈ q.asIdeal at hx
    simpa only [RingEquiv.symm_apply_apply] using hx
  · intro h q hq
    have he : PrimeSpectrum.comap e.symm.toRingHom (PrimeSpectrum.comap e.toRingHom q) = q :=
      (PrimeSpectrum.homeomorphOfRingEquiv e).right_inv q
    have hx := h (PrimeSpectrum.comap e.toRingHom q) (he.symm ▸ hq)
    exact hx

theorem zSpecChart_fromSpec :
    Spec.map zAmbientChartRingIso.inv ≫ zAmbientAffineOpen.2.fromSpec =
      Proj.awayι CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num) := by
  let eS := Proj.basicOpenIsoSpec CMGrading zCoordinate (coordinate_degree_one 2) (by norm_num)
  have he : eS.hom = zAmbientAffineOpen.1.toSpecΓ ≫ Spec.map zAmbientChartRingIso.hom := rfl
  apply (cancel_epi eS.hom).mp
  change eS.hom ≫ Spec.map zAmbientChartRingIso.inv ≫ zAmbientAffineOpen.2.fromSpec =
    eS.hom ≫ eS.inv ≫ zAmbientAffineOpen.1.ι
  calc
    _ = zAmbientAffineOpen.1.toSpecΓ ≫ Spec.map zAmbientChartRingIso.hom ≫
        Spec.map zAmbientChartRingIso.inv ≫ zAmbientAffineOpen.2.fromSpec := by
      rw [he, Category.assoc]
    _ = zAmbientAffineOpen.1.toSpecΓ ≫ zAmbientAffineOpen.2.fromSpec := by
      rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
    _ = zAmbientAffineOpen.1.ι := IsAffineOpen.toSpecΓ_fromSpec _
    _ = _ := by rw [Iso.hom_inv_id_assoc]

theorem zReducedChartIdeal_radical :
    (cubicIdealSheaf.ideal zAmbientAffineOpen).comap zAmbientChartRingIso.hom.hom =
      zCubicChartIdeal.radical := by
  rw [cubicIdealSheaf, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change (PrimeSpectrum.vanishingIdeal (zAmbientAffineOpen.2.fromSpec ⁻¹'
    (cubicClosed : Set CMProjectiveAmbient))).comap
      zAmbientChartRingIso.commRingCatIsoToRingEquiv.toRingHom = _
  rw [vanishingIdeal_comap_equiv]
  have he : PrimeSpectrum.comap zAmbientChartRingIso.inv.hom ⁻¹'
      (zAmbientAffineOpen.2.fromSpec ⁻¹' (cubicClosed : Set CMProjectiveAmbient)) =
      PrimeSpectrum.zeroLocus (zCubicChartIdeal : Set ZChartAway) := by
    change (Spec.map zAmbientChartRingIso.inv ≫ zAmbientAffineOpen.2.fromSpec) ⁻¹'
      cubicProjectiveLocus = _
    rw [zSpecChart_fromSpec]
    exact zAwayι_cubic_preimage
  change PrimeSpectrum.vanishingIdeal (PrimeSpectrum.comap zAmbientChartRingIso.inv.hom ⁻¹'
    (zAmbientAffineOpen.2.fromSpec ⁻¹' (cubicClosed : Set CMProjectiveAmbient))) = _
  exact (congrArg PrimeSpectrum.vanishingIdeal he).trans
    (PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical _)

#print axioms zChart_toLRS
#print axioms zAwayι_point
#print axioms zAwayι_cubic_preimage
#print axioms zSpecChart_fromSpec
#print axioms zReducedChartIdeal_radical
end Holonics.Hodge.CMGraphSource
