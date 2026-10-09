import CMOpenCoordinateExtension

/-! An actual ideal-sheaf chart comparison restricts to a principal open
by the existing comap functor. No Cartier or intersection functional is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource
universe u

def ambientAwayOpen {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : Spec R ⟶ X) (s : R) : Spec (.of (Localization.Away s)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s))) ≫ j
instance ambientAwayOpen_open {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (s : R) : IsOpenImmersion (ambientAwayOpen j s) := by
  dsimp only [ambientAwayOpen]
  infer_instance

theorem ambientAwayOpen_principal {R : CommRingCat.{u}} {X : Scheme.{u}}
    (I : X.IdealSheafData) (J : Ideal R) (j : Spec R ⟶ X) [IsOpenImmersion j]
    (h : I.comap j = Scheme.IdealSheafData.ofIdealTop (J.map (Scheme.ΓSpecIso R).inv.hom))
    (s g : R)
    (hp : J.map (algebraMap R (Localization.Away s)) =
      Ideal.span {algebraMap R (Localization.Away s) g}) :
    I.comap (ambientAwayOpen j s) = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {algebraMap R (Localization.Away s) g}).map
        (Scheme.ΓSpecIso (.of (Localization.Away s))).inv.hom) := by
  rw [ambientAwayOpen, Scheme.IdealSheafData.comap_comp, h, specOpen_coordinateIdeal_comap]
  change Scheme.IdealSheafData.ofIdealTop
    ((J.map (algebraMap R (Localization.Away s))).map
      (Scheme.ΓSpecIso (.of (Localization.Away s))).inv.hom) = _
  rw [hp]

theorem ambientAwayOpen_ideal_restrict {R : CommRingCat.{u}} {X U : Scheme.{u}}
    (I : X.IdealSheafData) (j : Spec R ⟶ X) (s : R)
    (r : U ⟶ Spec (.of (Localization.Away s))) :
    I.comap (r ≫ ambientAwayOpen j s) = (I.comap (ambientAwayOpen j s)).comap r :=
  Scheme.IdealSheafData.comap_comp _ _ _

#print axioms ambientAwayOpen_open
#print axioms ambientAwayOpen_principal
#print axioms ambientAwayOpen_ideal_restrict
end Holonics.Hodge.CMGraphSource
