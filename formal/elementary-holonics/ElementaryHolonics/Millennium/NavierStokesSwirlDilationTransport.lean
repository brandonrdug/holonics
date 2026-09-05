import ElementaryHolonics.Millennium.NavierStokesDilationResonance
import ElementaryHolonics.Millennium.NavierStokesAxialPrimitive
import ElementaryHolonics.Millennium.NavierStokesFirstRadialLift

/-!
# The source swirl carrier in its reciprocal axial coordinate

The actual constructed axis supplies `I'=1/F`, `Gamma=(alpha+2 beta) F I` and its velocity
derivative. A radial swirl carrier `K=F^(m+1) L(I)` then returns the singular dilation operator
with its source-derived coefficient `m(alpha-beta)/(alpha+2 beta)`.
-/

noncomputable section

open ContDiff

namespace Soma.Holonics.Millennium.NavierStokesSwirlDilationTransport

open Soma.Holonics.Millennium.NavierStokesAxialPrimitive
open Soma.Holonics.Millennium.NavierStokesFirstRadialLift
open Soma.Holonics.Millennium.NavierStokesDilationResonance

def swirlCarrier (m : ℕ) (F L : ℝ → ℝ) (z : ℝ) : ℝ :=
  F z ^ (m + 1) * L (primitiveInv F z)

def swirlExponent (m : ℕ) (alpha beta : ℝ) : ℝ :=
  (m : ℝ) * (alpha - beta) / (alpha + 2 * beta)

theorem swirlCarrier_hasDerivAt (m : ℕ) (F L : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z) (z : ℝ)
    (hL : DifferentiableAt ℝ L (primitiveInv F z)) :
    HasDerivAt (swirlCarrier m F L)
      (((m + 1 : ℕ) : ℝ) * F z ^ m * deriv F z * L (primitiveInv F z)
        + F z ^ (m + 1) * (deriv L (primitiveInv F z) * (F z)⁻¹)) z := by
  have hf := ((hF.of_le (by norm_num)).differentiable_one z).hasDerivAt
  have hi := hasDerivAt_primitiveInv F hF hpositive z
  have hl := hL.hasDerivAt.comp z hi
  have h := (hf.pow (m + 1)).mul hl
  convert h using 1 <;>
    first | rfl | (simp only [Nat.add_sub_cancel, mul_assoc] <;> ring)

/-- The linear part of the actual radial swirl equation is conjugate to dilation transport.
All axis factors come from the constructed reciprocal primitive. -/
theorem swirl_linear_transport (m : ℕ) (alpha beta : ℝ) (F L : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z)
    (hk : alpha + 2 * beta ≠ 0) (z : ℝ)
    (hL : DifferentiableAt ℝ L (primitiveInv F z)) :
    axialGamma alpha beta F z * deriv (swirlCarrier m F L) z +
      (alpha + (2 * (m : ℝ) + 1) * beta - ((m : ℝ) + 1) * deriv (axialW alpha beta F) z)
        * swirlCarrier m F L z =
      (alpha + 2 * beta) * F z ^ (m + 1) *
        dilationTransport (swirlExponent m alpha beta) L (primitiveInv F z) := by
  rw [(swirlCarrier_hasDerivAt m F L hF hpositive z hL).deriv,
    (hasDerivAt_axialW alpha beta F hF hpositive z).deriv]
  simp only [axialGamma, swirlCarrier, dilationTransport, swirlExponent, pow_succ, Nat.cast_add,
    Nat.cast_one]
  field_simp [(hpositive z).ne', hk]
  ring

/-- At the first radial order this is the exact source coefficient already returned by the
Cartesian momentum owner, with the pressure correction's forcing still oriented. -/
theorem firstSwirlCoefficient_eq_dilation (alpha beta : ℝ) (F H L : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hpositive : ∀ z, 0 < F z)
    (hk : alpha + 2 * beta ≠ 0) (z : ℝ)
    (hL : DifferentiableAt ℝ L (primitiveInv F z)) :
    firstSwirlCoefficient alpha beta F (axialW alpha beta F) H (swirlCarrier 1 F L) z =
      (alpha + 2 * beta) * F z ^ 2 *
          dilationTransport (swirlExponent 1 alpha beta) L (primitiveInv F z)
        + H z * deriv F z - deriv H z * F z / 2 := by
  have h := swirl_linear_transport 1 alpha beta F L hF hpositive hk z hL
  unfold firstSwirlCoefficient
  have hg : axialW alpha beta F z + beta * z = axialGamma alpha beta F z := by
    simp [axialW]
  rw [hg]
  convert congrArg (fun a : ℝ ↦ a + H z * deriv F z - deriv H z * F z / 2) h using 1 <;> norm_num

theorem swirlExponent_energyCritical (m : ℕ) (beta : ℝ) (hbeta : beta ≠ 0) :
    swirlExponent m (3 * beta / 2) beta = (m : ℝ) / 7 := by
  unfold swirlExponent
  field_simp
  ring

theorem firstSwirlExponent_window {alpha beta : ℝ}
    (hbeta : 0 < beta) (halpha : beta < alpha) (hupper : 2 * alpha ≤ 3 * beta) :
    0 < swirlExponent 1 alpha beta ∧ swirlExponent 1 alpha beta ≤ 1 / 7 := by
  have hk : 0 < alpha + 2 * beta := by linarith
  simp only [swirlExponent, Nat.cast_one, one_mul]
  constructor
  · exact div_pos (sub_pos.mpr halpha) hk
  · apply (div_le_iff₀ hk).mpr
    linarith

/-- Changing the positive swirl strength changes the reciprocal axial coordinate by its inverse
factor. The actual axial strain is preserved when the strength is nonzero. -/
theorem primitiveInv_const_mul (a : ℝ) (F : ℝ → ℝ) (z : ℝ) :
    primitiveInv (fun x ↦ a * F x) z = a⁻¹ * primitiveInv F z := by
  unfold primitiveInv
  calc
    (∫ t in (0 : ℝ)..z, (a * F t)⁻¹) = ∫ t in (0 : ℝ)..z, a⁻¹ * (F t)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp [mul_inv_rev, mul_comm]
    _ = a⁻¹ * ∫ t in (0 : ℝ)..z, (F t)⁻¹ := intervalIntegral.integral_const_mul _ _

theorem axialGamma_const_mul (alpha beta a : ℝ) (ha : a ≠ 0) (F : ℝ → ℝ) (z : ℝ) :
    axialGamma alpha beta (fun x ↦ a * F x) z = axialGamma alpha beta F z := by
  rw [axialGamma, primitiveInv_const_mul]
  unfold axialGamma
  field_simp

theorem axialW_const_mul (alpha beta a : ℝ) (ha : a ≠ 0) (F : ℝ → ℝ) :
    axialW alpha beta (fun x ↦ a * F x) = axialW alpha beta F := by
  funext z
  unfold axialW
  rw [axialGamma_const_mul alpha beta a ha F z]

#print axioms swirl_linear_transport
#print axioms firstSwirlCoefficient_eq_dilation
#print axioms swirlExponent_energyCritical
#print axioms firstSwirlExponent_window
#print axioms primitiveInv_const_mul
#print axioms axialW_const_mul

end Soma.Holonics.Millennium.NavierStokesSwirlDilationTransport
