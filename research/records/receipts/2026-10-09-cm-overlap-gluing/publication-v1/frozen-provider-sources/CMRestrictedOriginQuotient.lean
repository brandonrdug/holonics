import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length

/-!
# Residue quotient on a genuine principal open

For a residue map from an algebra to its coefficient field, if the chosen
principal-open denominator has nonzero residue, the residue map extends to
the actual localization. Its kernel is proved to be the localization of the
original kernel; the quotient-to-field equivalence is then constructed from
surjectivity and the quotient-kernel equivalence.
-/
noncomputable section
namespace Holonics.Hodge.CMGraphSource

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

abbrev RestrictedOriginLocalization (x : R) := Localization.Away x

def restrictedOriginLift (f : R →ₐ[k] k) (x : R) (hx : IsUnit (f x)) :
    RestrictedOriginLocalization x →ₐ[k] k :=
  IsLocalization.Away.liftAlgHom (f := f) x hx

theorem restrictedOriginLift_ker_map (f : R →ₐ[k] k) (x : R)
    (hx : IsUnit (f x)) :
    RingHom.ker (restrictedOriginLift f x hx).toRingHom =
      (RingHom.ker f.toRingHom).map
        (algebraMap R (RestrictedOriginLocalization x)) := by
  let S := RestrictedOriginLocalization x
  let L : S →ₐ[k] k := restrictedOriginLift f x hx
  have hcomp : L.toRingHom.comp (algebraMap R S) = f.toRingHom := by
    ext r
    simp [L, restrictedOriginLift]
  have hunder : (RingHom.ker L.toRingHom).under R = RingHom.ker f.toRingHom := by
    rw [Ideal.under_def, RingHom.comap_ker, hcomp]
  calc
    RingHom.ker L.toRingHom =
        ((RingHom.ker L.toRingHom).under R).map (algebraMap R S) :=
      (IsLocalization.map_under (Submonoid.powers x) S
        (RingHom.ker L.toRingHom)).symm
    _ = (RingHom.ker f.toRingHom).map (algebraMap R S) := by rw [hunder]

theorem restrictedOriginLift_surjective (f : R →ₐ[k] k) (x : R)
    (hx : IsUnit (f x)) : Function.Surjective (restrictedOriginLift f x hx) := by
  intro y
  refine ⟨algebraMap k (RestrictedOriginLocalization x) y, ?_⟩
  simp [restrictedOriginLift]

noncomputable def restrictedOriginQuotientEquiv (f : R →ₐ[k] k) (x : R)
    (hx : IsUnit (f x)) :
    (RestrictedOriginLocalization x ⧸
      (RingHom.ker f.toRingHom).map (algebraMap R (RestrictedOriginLocalization x))) ≃ₐ[k] k := by
  let L : RestrictedOriginLocalization x →ₐ[k] k := restrictedOriginLift f x hx
  exact (Ideal.quotientEquivAlgOfEq k
      (restrictedOriginLift_ker_map f x hx).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := L)
      (restrictedOriginLift_surjective f x hx))

theorem restrictedOriginQuotient_length_eq_one (f : R →ₐ[k] k) (x : R)
    (hx : IsUnit (f x)) :
    Module.length k (RestrictedOriginLocalization x ⧸
      (RingHom.ker f.toRingHom).map (algebraMap R (RestrictedOriginLocalization x))) = 1 := by
  rw [(restrictedOriginQuotientEquiv f x hx).toLinearEquiv.length_eq]
  exact Module.length_eq_one k k

#print axioms restrictedOriginLift_ker_map
#print axioms restrictedOriginLift_surjective
#print axioms restrictedOriginQuotientEquiv
#print axioms restrictedOriginQuotient_length_eq_one
end Holonics.Hodge.CMGraphSource
