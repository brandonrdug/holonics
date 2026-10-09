import CMOpenIdealCoordinates

/-! Coordinate ideals restrict to actual affine opens by extension through
the actual ring map. This is derived from the existing ideal-sheaf comap. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
universe u

theorem specOpen_coordinateIdeal_comap {R S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)] (I : Ideal R) :
    (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso R).inv.hom)).comap
        (Spec.map f) =
      Scheme.IdealSheafData.ofIdealTop ((I.map f.hom).map (Scheme.ΓSpecIso S).inv.hom) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [openImmersion_ideal_top]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id,
    (Spec R).presheaf.map_id, (Spec S).presheaf.map_id,
    CommRingCat.hom_id, Ideal.map_id]
  rw [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, ← Scheme.ΓSpecIso_inv_naturality]

#print axioms specOpen_coordinateIdeal_comap
end Holonics.Hodge.CMGraphSource
