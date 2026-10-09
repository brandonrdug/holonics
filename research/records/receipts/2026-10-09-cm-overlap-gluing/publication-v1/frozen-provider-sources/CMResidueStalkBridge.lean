import CMActualAffineIdealTransport
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Length

/-! Construct the local residue quotient from an actual spectrum map and
an actual open immersion. The section ideal is extended through its germ,
and its kernel identity is proved using the chart stalk localization and
the open immersion's proved stalk isomorphism. No desired local quotient
isomorphism or stalk kernel equality is an input.

agent-inferred: use map_under at the actual chart point, rather than treat
the nonlocal coordinate ring as a stalk. The source section map and its
consumer commute explicitly; length uses the stalk ring as its scalar.
This external receiver face keeps the helical pair interaction, cell
holonomy and tube attached, with helix, pair and tower thread retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace Holonics.Hodge.CMGraphSource
universe u

variable {k : Type u} [Field k]

local instance specStalkAlgebra (R : CommRingCat.{u}) (x : Spec R) :
    Algebra R ((Spec R).presheaf.stalk x) :=
  StructureSheaf.stalkAlgebra R x

local instance specStalkLocalization (R : CommRingCat.{u}) (x : Spec R) :
    IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk R x

abbrev specResiduePoint (R : CommRingCat.{u}) (g : R →+* k) : Spec R :=
  Spec.map (CommRingCat.ofHom g) (closedPoint k)

abbrev specResidueMap (R : CommRingCat.{u}) (g : R →+* k) :
    (Spec R).presheaf.stalk (specResiduePoint R g) ⟶ .of k :=
  Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom g))

theorem specResidueMap_comp (R : CommRingCat.{u}) (g : R →+* k) :
    (specResidueMap R g).hom.comp
      (algebraMap R ((Spec R).presheaf.stalk (specResiduePoint R g))) = g := by
  have hgerm : (Spec R).presheaf.germ ⊤ (specResiduePoint R g) trivial ≫
      specResidueMap R g = (Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom g :=
    Scheme.germ_stalkClosedPointTo_Spec (R := R) (S := CommRingCat.of k)
      (CommRingCat.ofHom g)
  have hcat : (Scheme.ΓSpecIso R).inv ≫
      (Spec R).presheaf.germ ⊤ (specResiduePoint R g) trivial ≫
        specResidueMap R g = CommRingCat.ofHom g := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun f => (Scheme.ΓSpecIso R).inv ≫ f) hgerm
  exact CommRingCat.hom_ext_iff.mp hcat

theorem specResidueMap_kernel (R : CommRingCat.{u}) (g : R →+* k) :
    RingHom.ker (specResidueMap R g).hom =
      (RingHom.ker g).map
        (algebraMap R ((Spec R).presheaf.stalk (specResiduePoint R g))) := by
  have hunder : (RingHom.ker (specResidueMap R g).hom).under R = RingHom.ker g := by
    rw [Ideal.under_def, RingHom.comap_ker, specResidueMap_comp]
  calc
    RingHom.ker (specResidueMap R g).hom =
        ((RingHom.ker (specResidueMap R g).hom).under R).map
          (algebraMap R ((Spec R).presheaf.stalk (specResiduePoint R g))) :=
      (IsLocalization.map_under (specResiduePoint R g).asIdeal.primeCompl
        ((Spec R).presheaf.stalk (specResiduePoint R g))
        (RingHom.ker (specResidueMap R g).hom)).symm
    _ = _ := by rw [hunder]

theorem specResidueMap_surjective (R : CommRingCat.{u}) (g : R →+* k)
    (hg : Function.Surjective g) : Function.Surjective (specResidueMap R g).hom := by
  intro c
  obtain ⟨r, hr⟩ := hg c
  refine ⟨algebraMap R ((Spec R).presheaf.stalk (specResiduePoint R g)) r, ?_⟩
  change ((specResidueMap R g).hom.comp
    (algebraMap R ((Spec R).presheaf.stalk (specResiduePoint R g)))) r = c
  rw [specResidueMap_comp]
  exact hr

theorem spectrumImage_germ_stalkMap {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] (x : Spec R) :
    (j.appIso ⊤).inv ≫ X.presheaf.germ (j ''ᵁ ⊤) (j x)
      (by exact ⟨x, trivial, rfl⟩) ≫ j.stalkMap x =
        (Spec R).presheaf.germ ⊤ x trivial := by
  rw [Scheme.Hom.germ_stalkMap, ← Category.assoc, Scheme.Hom.appIso_inv_app,
    TopCat.Presheaf.germ_res]

abbrev spectrumResiduePoint {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) (g : R →+* k) : X :=
  j (specResiduePoint R g)

abbrev spectrumResidueMap {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) (g : R →+* k) :
    X.presheaf.stalk (spectrumResiduePoint R j g) ⟶ .of k :=
  Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom g) ≫ j)

def spectrumImageStalkIdeal {X : Scheme.{u}} (I : X.IdealSheafData)
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j] (g : R →+* k) :
    Ideal (X.presheaf.stalk (spectrumResiduePoint R j g)) :=
  (I.ideal ⟨j ''ᵁ ⊤, (isAffineOpen_top (Spec R)).image_of_isOpenImmersion j⟩).map
    (X.presheaf.germ (j ''ᵁ ⊤) (spectrumResiduePoint R j g)
      (by exact ⟨specResiduePoint R g, trivial, rfl⟩)).hom

theorem spectrumImageStalkIdeal_kernel {X : Scheme.{u}} (I : X.IdealSheafData)
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j]
    (g : R →+* k) (r : R)
    (hI : I.comap j = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {r}).map (Scheme.ΓSpecIso R).inv.hom))
    (hg : RingHom.ker g = Ideal.span {r}) :
    RingHom.ker (spectrumResidueMap R j g).hom = spectrumImageStalkIdeal I R j g := by
  let x := specResiduePoint R g
  let e := (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
  have hsection : (j.stalkMap x).hom
      ((X.presheaf.germ (j ''ᵁ ⊤) (j x) (by exact ⟨x, trivial, rfl⟩)).hom
        (spectrumImageEquation R j r)) =
      algebraMap R ((Spec R).presheaf.stalk x) r := by
    have h := congrArg
      (fun f : Γ(Spec R, ⊤) ⟶ (Spec R).presheaf.stalk x =>
        f.hom ((Scheme.ΓSpecIso R).inv.hom r))
      (spectrumImage_germ_stalkMap R j x)
    exact h
  have hmap : (spectrumImageStalkIdeal I R j g).map (j.stalkMap x).hom =
      RingHom.ker (specResidueMap R g).hom := by
    rw [spectrumImageStalkIdeal, spectrumImageEquation_ideal I R j r hI,
      Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
      hsection, specResidueMap_kernel, hg, Ideal.map_span, Set.image_singleton]
  rw [spectrumResidueMap, Scheme.stalkClosedPointTo_comp]
  change RingHom.ker ((specResidueMap R g).hom.comp (j.stalkMap x).hom) = _
  rw [← RingHom.comap_ker, ← hmap]
  exact Ideal.comap_map_of_bijective (j.stalkMap x).hom e.bijective

theorem spectrumResidueMap_surjective {X : Scheme.{u}} (R : CommRingCat.{u})
    (j : Spec R ⟶ X) [IsOpenImmersion j] (g : R →+* k)
    (hg : Function.Surjective g) :
    Function.Surjective (spectrumResidueMap R j g).hom := by
  rw [spectrumResidueMap, Scheme.stalkClosedPointTo_comp]
  change Function.Surjective
    ((specResidueMap R g).hom.comp (j.stalkMap (specResiduePoint R g)).hom)
  exact (specResidueMap_surjective R g hg).comp
    (asIso (j.stalkMap (specResiduePoint R g))).commRingCatIsoToRingEquiv.surjective

def spectrumStalkQuotientEquiv {X : Scheme.{u}} (I : X.IdealSheafData)
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j]
    (g : R →+* k) (r : R)
    (hI : I.comap j = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {r}).map (Scheme.ΓSpecIso R).inv.hom))
    (hg : RingHom.ker g = Ideal.span {r}) (hs : Function.Surjective g) :
    (X.presheaf.stalk (spectrumResiduePoint R j g) ⧸
      spectrumImageStalkIdeal I R j g) ≃+* k :=
  (Ideal.quotEquivOfEq (spectrumImageStalkIdeal_kernel I R j g r hI hg).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (spectrumResidueMap_surjective R j g hs))

theorem spectrumStalkQuotient_length_one {X : Scheme.{u}} (I : X.IdealSheafData)
    (R : CommRingCat.{u}) (j : Spec R ⟶ X) [IsOpenImmersion j]
    (g : R →+* k) (r : R)
    (hI : I.comap j = Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {r}).map (Scheme.ΓSpecIso R).inv.hom))
    (hg : RingHom.ker g = Ideal.span {r}) (hs : Function.Surjective g) :
    Module.length (X.presheaf.stalk (spectrumResiduePoint R j g))
      (X.presheaf.stalk (spectrumResiduePoint R j g) ⧸
        spectrumImageStalkIdeal I R j g) = 1 := by
  have hmax : (spectrumImageStalkIdeal I R j g).IsMaximal := by
    rw [← spectrumImageStalkIdeal_kernel I R j g r hI hg]
    exact RingHom.ker_isMaximal_of_surjective (spectrumResidueMap R j g).hom
      (spectrumResidueMap_surjective R j g hs)
  apply Module.length_eq_one_iff.mpr
  exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hmax)

#print axioms specResidueMap_comp
#print axioms specResidueMap_kernel
#print axioms specResidueMap_surjective
#print axioms spectrumImage_germ_stalkMap
#print axioms spectrumImageStalkIdeal_kernel
#print axioms spectrumResidueMap_surjective
#print axioms spectrumStalkQuotientEquiv
#print axioms spectrumStalkQuotient_length_one
end Holonics.Hodge.CMGraphSource
