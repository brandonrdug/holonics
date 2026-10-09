import CMActualRestrictedZEquation
import CMRestrictedOriginQuotient
import Mathlib.RingTheory.Length

/-!
# The actual restricted Z-origin quotient

This consumes the actual origin receiver and actual graph-diagonal equation.
The localization map is constructed from the residue map; its kernel is
identified with the localized fixed ideal and then with the equation (v).
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
namespace Holonics.Hodge.CMGraphSource

private theorem originReceiver_factor_value : originReceiver (u ^ 2 - 1) = -1 := by
  simp [originReceiver_u]

theorem originReceiver_ker_eq_zeroPointIdeal :
    RingHom.ker originReceiver.toRingHom = zeroPointIdeal := by
  apply le_antisymm
  · intro a ha
    change originReceiver a = 0 at ha
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    apply zeroPointCoordinateEquiv.injective
    have hmap : zeroPointCoordinateEquiv (Ideal.Quotient.mk zeroPointIdeal a) =
        originReceiver a := by
      change originQuotientReceiver (Ideal.Quotient.mk zeroPointIdeal a) = _
      rw [originQuotientReceiver, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      rfl
    rw [hmap, map_zero]
    exact ha
  · intro a ha
    exact zeroPointIdeal_le_originKernel ha

theorem actualRestrictedZ_originKernel_map_eq_v :
    (RingHom.ker originReceiver.toRingHom).map
        (algebraMap CurveRing ActualRestrictedZRing) =
      Ideal.span ({algebraMap CurveRing ActualRestrictedZRing v} : Set ActualRestrictedZRing) := by
  calc
    (RingHom.ker originReceiver.toRingHom).map
        (algebraMap CurveRing ActualRestrictedZRing) =
      fixedIdeal.map (algebraMap CurveRing ActualRestrictedZRing) := by
        rw [originReceiver_ker_eq_zeroPointIdeal, ← fixedIdeal_eq_zeroPointIdeal]
    _ = Ideal.span ({algebraMap CurveRing ActualRestrictedZRing v} : Set ActualRestrictedZRing) :=
      actualRestrictedZ_fixedIdeal_eq_v

private theorem originReceiver_factor_unit :
    IsUnit (originReceiver (u ^ 2 - 1)) := by
  rw [originReceiver_factor_value]
  exact isUnit_iff_ne_zero.mpr (by norm_num : (-1 : ℂ) ≠ 0)

noncomputable def actualRestrictedZ_quotientEquiv :
    (ActualRestrictedZRing ⧸
      Ideal.span ({algebraMap CurveRing ActualRestrictedZRing v} : Set ActualRestrictedZRing)) ≃ₐ[ℂ] ℂ := by
  have hI :
      Ideal.span ({algebraMap CurveRing ActualRestrictedZRing v} : Set ActualRestrictedZRing) =
        (RingHom.ker originReceiver.toRingHom).map
          (algebraMap CurveRing ActualRestrictedZRing) :=
    actualRestrictedZ_originKernel_map_eq_v.symm
  exact (Ideal.quotientEquivAlgOfEq ℂ hI).trans
    (restrictedOriginQuotientEquiv originReceiver (u ^ 2 - 1) originReceiver_factor_unit)

theorem actualRestrictedZ_quotient_length_one :
    Module.length ℂ (ActualRestrictedZRing ⧸
      Ideal.span ({algebraMap CurveRing ActualRestrictedZRing v} : Set ActualRestrictedZRing)) = 1 := by
  rw [actualRestrictedZ_quotientEquiv.toLinearEquiv.length_eq]
  exact Module.length_eq_one ℂ ℂ

#print axioms originReceiver_ker_eq_zeroPointIdeal
#print axioms actualRestrictedZ_originKernel_map_eq_v
#print axioms actualRestrictedZ_quotientEquiv
#print axioms actualRestrictedZ_quotient_length_one
end Holonics.Hodge.CMGraphSource
