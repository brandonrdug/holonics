import CMSpecGammaRegular
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Fresh reconstruction from Library v12 source owners; historical receipts do not authenticate it. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
universe u

def spectrumImageEquation {Y : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (r : R) : Γ(Y, j ''ᵁ ⊤) :=
  (j.appIso ⊤).inv.hom ((Scheme.ΓSpecIso R).inv.hom r)

theorem spectrumImageEquation_regular {Y : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (r : R) (hr : IsRegular r) :
    IsRegular (spectrumImageEquation R j r) :=
  ringEquiv_regular (j.appIso ⊤).symm.commRingCatIsoToRingEquiv
    ((Scheme.ΓSpecIso R).inv.hom r) (specGamma_regular R r hr)

theorem spectrumImageEquation_ideal {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (R : CommRingCat.{u}) (j : Spec R ⟶ Y) [IsOpenImmersion j] (r : R)
    (hI : I.comap j = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {r}).map (Scheme.ΓSpecIso R).inv.hom)) :
    I.ideal ⟨j ''ᵁ ⊤, (isAffineOpen_top (Spec R)).image_of_isOpenImmersion j⟩ =
      Ideal.span {spectrumImageEquation R j r} := by
  have hs : (I.comap j).ideal ⟨⊤, isAffineOpen_top (Spec R)⟩ =
      Ideal.span {(Scheme.ΓSpecIso R).inv.hom r} := by
    rw [hI]
    simp [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
  have ht := I.ideal_comap_of_isOpenImmersion j ⟨⊤, isAffineOpen_top (Spec R)⟩
  have hp := congrArg
    (fun J : Ideal Γ(Spec R, ⊤) => J.map (j.appIso ⊤).inv.hom) (ht.symm.trans hs)
  have hj : Function.Surjective (j.appIso ⊤).inv.hom :=
    (j.appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective
  simpa only [Ideal.map_comap_of_surjective _ hj, Ideal.map_span,
    Set.image_singleton, spectrumImageEquation] using hp

theorem affineImageUnitIdeal {X Y : Scheme.{u}} [IsAffine X]
    (I : Y.IdealSheafData) (j : X ⟶ Y) [IsOpenImmersion j]
    (hI : I.comap j = ⊤) :
    I.ideal ⟨j ''ᵁ ⊤, (isAffineOpen_top X).image_of_isOpenImmersion j⟩ = ⊤ := by
  have hs : (I.comap j).ideal ⟨⊤, isAffineOpen_top X⟩ = ⊤ := by
    rw [hI]
    rfl
  have ht := I.ideal_comap_of_isOpenImmersion j ⟨⊤, isAffineOpen_top X⟩
  have hp := congrArg
    (fun J : Ideal Γ(X, ⊤) => J.map (j.appIso ⊤).inv.hom) (ht.symm.trans hs)
  have hj : Function.Surjective (j.appIso ⊤).inv.hom :=
    (j.appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective
  simpa only [Ideal.map_comap_of_surjective _ hj, Ideal.map_top]
    using hp

#print axioms spectrumImageEquation_regular
#print axioms spectrumImageEquation_ideal
#print axioms affineImageUnitIdeal
end Holonics.Hodge.CMGraphSource
