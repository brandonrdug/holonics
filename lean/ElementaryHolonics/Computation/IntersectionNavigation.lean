import Mathlib

/-!
# Intersecting analytic generators: the exact first-order navigation fibre

For simultaneous source values in a receiving space Y, the local Jacobian
J : X →ₗ[ℂ] Y carries a configuration motion to a receiving motion. A source
motion and requested residual rate define the target receiving motion. If
J has a right inverse, every realizing configuration motion is a particular
lift plus an element of ker J; the kernel is the complete unresolved
tangential fibre, not an arbitrary solver choice.

This is first-order algebra. To turn the fibre into a local complex manifold
requires a holomorphic source and the hypotheses of the implicit-function
theorem. A finite propagation speed needs a separately supplied
metric/locality law.
-/

noncomputable section

namespace Soma.Holonics.Computation.IntersectionNavigation

variable {X Y : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- On a regular zero-free chart, a product of a pulled-back generator
and a local unit carries the sum of the pulled-back source current and
the unit current. The derivative of the inner generator is indispensable:
it is the phase transport rather than a copied current. -/
theorem product_pullback_logCurrent
    {f g unit : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (g z))
    (hg : DifferentiableAt ℂ g z)
    (hunit : DifferentiableAt ℂ unit z)
    (hfg : f (g z) ≠ 0) (hu : unit z ≠ 0) :
    logDeriv (fun w => f (g w) * unit w) z =
      logDeriv f (g z) * deriv g z + logDeriv unit z := by
  have hmul := logDeriv_mul (f := f ∘ g) (g := unit) z hfg hu (hf.comp z hg) hunit
  rw [logDeriv_comp hf hg] at hmul
  simpa only [Function.comp_apply] using hmul

/-- A local analytic factorization of a source, with its zero-free factor
supplied as a separate function. -/
def localZeroFactor (center : ℂ) (multiplicity : ℕ)
    (unit : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - center) ^ multiplicity * unit z

/-- A local generator branched to order k over a receiving center. -/
def branchedGenerator (target source : ℂ) (k : ℕ)
    (unit : ℂ → ℂ) (z : ℂ) : ℂ :=
  target + (z - source) ^ k * unit z

/-- Pulling a multiplicity-m local factor through an order-k generator
produces an order-km factor. This is an exact identity of source functions;
the next theorem checks nonvanishing of the remaining local factor at the
base point. -/
theorem branch_pullback_factor (target source : ℂ) (m k : ℕ)
    (outerUnit innerUnit : ℂ → ℂ) (z : ℂ) :
    localZeroFactor target m outerUnit
        (branchedGenerator target source k innerUnit z) =
      (z - source) ^ (k * m) *
        ((innerUnit z) ^ m *
          outerUnit (branchedGenerator target source k innerUnit z)) := by
  simp only [localZeroFactor, branchedGenerator, add_sub_cancel_left, mul_pow, pow_mul]
  ring

/-- If both supplied factors are nonzero at their base points, the factor
remaining after pullback is also nonzero there. If those factors are analytic
nearby, this is the normal form whose zero order is k m. -/
theorem branch_pullback_unit_nonzero (target source : ℂ) (m k : ℕ)
    (hk : 0 < k) (outerUnit innerUnit : ℂ → ℂ)
    (houter : outerUnit target ≠ 0) (hinner : innerUnit source ≠ 0) :
    (innerUnit source) ^ m *
      outerUnit (branchedGenerator target source k innerUnit source) ≠ 0 := by
  rw [branchedGenerator, sub_self, zero_pow (Nat.ne_of_gt hk), zero_mul, add_zero]
  exact mul_ne_zero (pow_ne_zero m hinner) houter

/-- The receiving motion required to decrease a source value at rate rate
while the source itself moves by sourceMotion. -/
def requiredMotion (value sourceMotion : Y) (rate : ℂ) : Y :=
  -(rate • value + sourceMotion)

/-- A right inverse of the joint generator Jacobian supplies one exact
configuration direction for the requested receiving motion. -/
theorem particular_direction (J : X →ₗ[ℂ] Y) (lift : Y →ₗ[ℂ] X)
    (hsection : J.comp lift = LinearMap.id)
    (value sourceMotion : Y) (rate : ℂ) :
    J (lift (requiredMotion value sourceMotion rate)) + sourceMotion =
      -(rate • value) := by
  have hright (y : Y) : J (lift y) = y :=
    LinearMap.congr_fun hsection y
  rw [hright]
  simp [requiredMotion]

/-- The complete preimage fibre of the simultaneous first-order residual
equation. Every other direction differs from the canonical lift by an
element of the Jacobian kernel, and every such direction realizes the same
receiving motion. -/
theorem direction_fibre (J : X →ₗ[ℂ] Y) (lift : Y →ₗ[ℂ] X)
    (hsection : J.comp lift = LinearMap.id)
    (value sourceMotion : Y) (rate : ℂ) (velocity : X) :
    J velocity + sourceMotion = -(rate • value) ↔
      ∃ tangent : J.ker,
        velocity = lift (requiredMotion value sourceMotion rate) + tangent.1 := by
  have hright (y : Y) : J (lift y) = y :=
    LinearMap.congr_fun hsection y
  constructor
  · intro hvelocity
    have htarget : J velocity = requiredMotion value sourceMotion rate := by
      unfold requiredMotion
      exact eq_neg_of_add_eq_zero_left (by
        calc
          J velocity + (rate • value + sourceMotion) =
              (J velocity + sourceMotion) + rate • value := by abel
          _ = 0 := by rw [hvelocity]; exact neg_add_cancel _)
    let tangent : J.ker := ⟨velocity - lift (requiredMotion value sourceMotion rate), by
      rw [LinearMap.mem_ker, map_sub, hright, htarget, sub_self]⟩
    refine ⟨tangent, ?_⟩
    dsimp [tangent]
    abel
  · rintro ⟨tangent, rfl⟩
    have htangent : J (tangent : X) = 0 := tangent.property
    rw [map_add, hright, htangent, add_zero]
    simp [requiredMotion]

/-- If the requested receiving motion is outside the image of the joint
Jacobian, no first-order action can realize it. This is the exact rank-loss
obstruction returned by the receiver. -/
theorem no_direction_of_unreachable (J : X →ₗ[ℂ] Y)
    (value sourceMotion : Y) (rate : ℂ)
    (hunreachable : requiredMotion value sourceMotion rate ∉ LinearMap.range J) :
    ¬ ∃ velocity : X,
      J velocity + sourceMotion = -(rate • value) := by
  rintro ⟨velocity, hvelocity⟩
  apply hunreachable
  refine ⟨velocity, ?_⟩
  unfold requiredMotion
  calc
    J velocity = (J velocity + sourceMotion) - sourceMotion := by abel
    _ = -(rate • value) - sourceMotion := by rw [hvelocity]
    _ = -(rate • value + sourceMotion) := by abel

/-- A translated affine source has its root at any prescribed target,
and one exact Newton action from zero reaches that target. The geometry of
holomorphic generators alone therefore supplies no uniform spatial speed. -/
theorem affine_newton_reaches_arbitrary_target (target : ℂ) :
    (0 : ℂ) -
      (fun z : ℂ => z - target) 0 /
        deriv (fun z : ℂ => z - target) 0 = target := by
  simp

end Soma.Holonics.Computation.IntersectionNavigation

section Audit
open Soma.Holonics.Computation.IntersectionNavigation
#print axioms product_pullback_logCurrent
#print axioms branch_pullback_factor
#print axioms branch_pullback_unit_nonzero
#print axioms particular_direction
#print axioms direction_fibre
#print axioms no_direction_of_unreachable
#print axioms affine_newton_reaches_arbitrary_target
end Audit
