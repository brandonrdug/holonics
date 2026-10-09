import CMSpecKernelCoordinates
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Actual ideal-sheaf restriction along an affine open immersion agrees
with extension of the global-section ideal. No intersection pairing is defined. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
universe u

theorem openImmersion_ideal_top {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  let V : Y.affineOpens := ⟨f ''ᵁ ⊤, (isAffineOpen_top X).image_of_isOpenImmersion f⟩
  rw [← I.map_ideal (U := V) (V := ⟨⊤, isAffineOpen_top Y⟩) (show V.1 ≤ ⊤ from le_top)]
  have he (J : Ideal Γ(Y, V)) : J.comap (f.appIso ⊤).inv.hom =
      J.map (f.appIso ⊤).hom.hom :=
    (Ideal.map_comap_of_equiv (f.appIso ⊤).commRingCatIsoToRingEquiv).symm
  rw [he, Ideal.map_map, ← CommRingCat.hom_comp]
  congr 1
  apply congrArg CommRingCat.Hom.hom
  apply (cancel_mono (f.appIso ⊤).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
    change f.appLE ⊤ (f ⁻¹ᵁ ⊤) le_rfl = f.app ⊤
    exact f.appLE_eq_app
  have h := f.appLE_appIso_inv (U := ⊤) (V := ⊤) (by simp)
  rw [ht] at h
  exact h.symm

#print axioms openImmersion_ideal_top
end Holonics.Hodge.CMGraphSource
