import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! The actual affine morphism's kernel ideal sheaf is the coordinate-ring
kernel, transported by the existing Gamma-Spec isomorphism. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
universe u

theorem specMap_coordinate_kernel {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (RingHom.ker (Spec.map f).appTop.hom).comap (Scheme.ΓSpecIso R).inv.hom =
      RingHom.ker f.hom := by
  rw [RingHom.comap_ker, ← CommRingCat.hom_comp, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.hom_comp]
  exact RingHom.ker_comp_of_injective f.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).inv).1

theorem specMap_idealSheaf_coordinates {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Spec.map f).ker = Scheme.IdealSheafData.ofIdealTop
      ((RingHom.ker f.hom).map (Scheme.ΓSpecIso R).inv.hom) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  rw [← specMap_coordinate_kernel f]
  exact (Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2 _).symm

#print axioms specMap_coordinate_kernel
#print axioms specMap_idealSheaf_coordinates
end Holonics.Hodge.CMGraphSource
