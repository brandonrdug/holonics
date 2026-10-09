import CMSpecKernelCoordinates
import Mathlib.Algebra.Regular.Basic

noncomputable section
set_option autoImplicit false
open AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

theorem ringEquiv_regular {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (g : R) (hg : IsRegular g) : IsRegular (e g) := by
  rw [← isLeftRegular_iff_isRegular]
  intro x y h
  apply e.symm.injective
  apply hg.1
  simpa only [map_mul, RingEquiv.symm_apply_apply] using congrArg e.symm h

theorem specGamma_regular (R : CommRingCat) (g : R) (hg : IsRegular g) :
    IsRegular ((Scheme.ΓSpecIso R).inv.hom g) :=
  ringEquiv_regular (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv g hg

#print axioms ringEquiv_regular
#print axioms specGamma_regular
end Holonics.Hodge.CMGraphSource
