import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
The affine equalizer is constructed from the ideal of actual differences.
The universal property ranges over all schemes, via the Gamma--Spec
adjunction, rather than merely over affine test schemes.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace Holonics.Hodge.CMGraphSource
universe u

def affineReceiverMap {T : Scheme.{u}} {A : Type u} [CommRing A]
    (f : T ⟶ Spec (.of A)) : A →+* Γ(T, ⊤) :=
  ((ΓSpec.adjunction.homEquiv T (op (.of A))).symm f).unop.hom

def affineSchemeMap {T : Scheme.{u}} {A : Type u} [CommRing A]
    (f : A →+* Γ(T, ⊤)) : T ⟶ Spec (.of A) :=
  (ΓSpec.adjunction.homEquiv T (op (.of A))) (CommRingCat.ofHom f).op

theorem affineReceiverMap_comp {T : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] (f : T ⟶ Spec (.of A)) (g : B →+* A) :
    affineReceiverMap (f ≫ Spec.map (CommRingCat.ofHom g)) =
      (affineReceiverMap f).comp g := by
  unfold affineReceiverMap
  erw [ΓSpec.adjunction.homEquiv_naturality_right_symm]
  rfl

theorem affineReceiverMap_schemeMap {T : Scheme.{u}} {A : Type u} [CommRing A]
    (f : A →+* Γ(T, ⊤)) : affineReceiverMap (affineSchemeMap f) = f := by
  unfold affineReceiverMap affineSchemeMap
  erw [Equiv.symm_apply_apply]
  rfl

theorem affineReceiverMap_injective {T : Scheme.{u}} {A : Type u} [CommRing A] :
    Function.Injective (affineReceiverMap (T := T) (A := A)) := by
  intro f g h
  apply (ΓSpec.adjunction.homEquiv T (op (.of A))).symm.injective
  apply Quiver.Hom.unop_inj
  exact CommRingCat.hom_ext h

def affineDifferenceIdeal {A B : Type u} [CommRing A] [CommRing B]
    (f g : A →+* B) : Ideal B := Ideal.span (Set.range fun a => f a - g a)

theorem affineDifferenceQuotient_condition {A B : Type u} [CommRing A] [CommRing B]
    (f g : A →+* B) :
    (Ideal.Quotient.mk (affineDifferenceIdeal f g)).comp f =
      (Ideal.Quotient.mk (affineDifferenceIdeal f g)).comp g := by
  ext a
  simp only [RingHom.comp_apply]
  apply sub_eq_zero.mp
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨a, rfl⟩

def affineDifferenceFork {A B : Type u} [CommRing A] [CommRing B] (f g : A →+* B) :
    Fork (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom g)) :=
  Fork.ofι (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (affineDifferenceIdeal f g))))
    (by rw [← Spec.map_comp, ← Spec.map_comp];
        exact congrArg (fun k => Spec.map (CommRingCat.ofHom k))
          (affineDifferenceQuotient_condition f g))

def affineDifferenceFork_isLimit {A B : Type u} [CommRing A] [CommRing B]
    (f g : A →+* B) : IsLimit (affineDifferenceFork f g) :=
  Fork.IsLimit.mk' _ fun s => by
    have hc : (affineReceiverMap s.ι).comp f = (affineReceiverMap s.ι).comp g := by
      simpa only [affineReceiverMap_comp] using congrArg affineReceiverMap s.condition
    have hi : affineDifferenceIdeal f g ≤ RingHom.ker (affineReceiverMap s.ι) := by
      rw [affineDifferenceIdeal, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      change affineReceiverMap s.ι (f a - g a) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (RingHom.congr_fun hc a)
    let h : B ⧸ affineDifferenceIdeal f g →+* Γ(s.pt, ⊤) :=
      Ideal.Quotient.lift _ (affineReceiverMap s.ι) hi
    refine ⟨affineSchemeMap h, ?_, ?_⟩
    · apply affineReceiverMap_injective
      change affineReceiverMap (affineSchemeMap h ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (affineDifferenceIdeal f g)))) = _
      rw [affineReceiverMap_comp, affineReceiverMap_schemeMap]
      exact Ideal.Quotient.lift_comp_mk _ _ _
    · intro m hm
      apply affineReceiverMap_injective
      rw [affineReceiverMap_schemeMap]
      apply Ideal.Quotient.ringHom_ext
      have hh := congrArg affineReceiverMap hm
      change affineReceiverMap (m ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (affineDifferenceIdeal f g)))) = _ at hh
      simpa only [affineReceiverMap_comp, h, Ideal.Quotient.lift_comp_mk] using hh

#print axioms affineDifferenceQuotient_condition
#print axioms affineDifferenceFork_isLimit

def affineFixedFork {A : Type u} [CommRing A] (f : A →+* A) :
    Fork (Spec.map (CommRingCat.ofHom f)) (𝟙 (Spec (.of A))) :=
  Fork.ofι (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (affineDifferenceIdeal f (RingHom.id A))))) (by
      have hc := (affineDifferenceFork f (RingHom.id A)).condition
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (affineDifferenceIdeal f (RingHom.id A)))) ≫ Spec.map (CommRingCat.ofHom f) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (affineDifferenceIdeal f (RingHom.id A)))) ≫
              Spec.map (CommRingCat.ofHom (RingHom.id A)) at hc
      simpa only [CommRingCat.ofHom_id, Spec.map_id] using hc)

def affineFixedFork_isLimit {A : Type u} [CommRing A] (f : A →+* A) :
    IsLimit (affineFixedFork f) :=
  Fork.IsLimit.mk' _ fun s => by
    have hc : (affineReceiverMap s.ι).comp f = affineReceiverMap s.ι := by
      simpa only [affineReceiverMap_comp, Category.comp_id] using
        congrArg affineReceiverMap s.condition
    have hi : affineDifferenceIdeal f (RingHom.id A) ≤ RingHom.ker (affineReceiverMap s.ι) := by
      rw [affineDifferenceIdeal, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      change affineReceiverMap s.ι (f a - a) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (RingHom.congr_fun hc a)
    let h : A ⧸ affineDifferenceIdeal f (RingHom.id A) →+* Γ(s.pt, ⊤) :=
      Ideal.Quotient.lift _ (affineReceiverMap s.ι) hi
    refine ⟨affineSchemeMap h, ?_, ?_⟩
    · apply affineReceiverMap_injective
      change affineReceiverMap (affineSchemeMap h ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (affineDifferenceIdeal f (RingHom.id A))))) = _
      rw [affineReceiverMap_comp, affineReceiverMap_schemeMap]
      exact Ideal.Quotient.lift_comp_mk _ _ _
    · intro m hm
      apply affineReceiverMap_injective
      rw [affineReceiverMap_schemeMap]
      apply Ideal.Quotient.ringHom_ext
      have hh := congrArg affineReceiverMap hm
      change affineReceiverMap (m ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (affineDifferenceIdeal f (RingHom.id A))))) = _ at hh
      simpa only [affineReceiverMap_comp, h, Ideal.Quotient.lift_comp_mk] using hh

#print axioms affineFixedFork_isLimit
end Holonics.Hodge.CMGraphSource
