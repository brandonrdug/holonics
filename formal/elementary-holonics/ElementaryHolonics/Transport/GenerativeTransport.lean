import Mathlib

/-!
# Exact affine transport: the kernel of an open receiver fiber

This is the small formal kernel of the bounded construction in
`research/records/2026-07-27_THE_OBSTRUCTION_CAUSES_THE_FAMILY_THE_OPEN_FIBER_PREDICTS_BEFORE_IT_CLOSES.md`.
It proves that an observation functional which kills the fiber's unresolved directions is fixed
on that compatible parameter fiber, and that a functional which sees one such direction
distinguishes two compatible models. It does **not** formalize the Rust elimination routine, its
canonical query search, or a theorem that its routine always chooses a discriminator.

The event family is the declared time-affine law `A(τ) = M + τ(S + K + R)`. The four carriers
are left abstract here; diagonal-capacity, symmetric/skew-pair, reaction, positivity, and
physical admissibility conditions are additional constitutive hypotheses, not consequences of
this identity. The formal observation theorem below is receiver-relative: one fixed source
potential and one fixed receiver functional in one declared frame. The current Rust event's
receiver lineage is not bound across events, so this file makes no cross-receiver claim.
-/

open scoped BigOperators
open Matrix

namespace Soma.Holonics.Transport.GenerativeTransport

variable {n : ℕ}

/-- The bounded construction's declared time-affine family of complete operators. -/
def eventOperator (M S K R : Matrix (Fin n) (Fin n) ℚ) (τ : ℚ) :
    Matrix (Fin n) (Fin n) ℚ := M + τ • (S + K + R)

/-- The event operator changes by exactly the interval difference times its fixed generator. -/
theorem eventOperator_interval_difference
    (M S K R : Matrix (Fin n) (Fin n) ℚ) (τ σ : ℚ) :
    eventOperator M S K R σ - eventOperator M S K R τ
      = (σ - τ) • (S + K + R) := by
  simp [eventOperator, sub_smul]
  module

variable {X Y : Type*}
variable [AddCommGroup X] [Module ℚ X]
variable [AddCommGroup Y] [Module ℚ Y]

/-- Parameters compatible with one exact returned observation. -/
def observationFiber (observe : X →ₗ[ℚ] Y) (returned : Y) : Set X :=
  {x | observe x = returned}

/-- A prediction is invariant on the complete compatible fiber when it annihilates every
unresolved direction in the observation kernel. -/
theorem prediction_invariant_on_fiber
    (observe : X →ₗ[ℚ] Y) (predict : X →ₗ[ℚ] ℚ) (returned : Y)
    (x x' : X) (hx : x ∈ observationFiber observe returned)
    (hx' : x' ∈ observationFiber observe returned)
    (annihilates_kernel : ∀ z, observe z = 0 → predict z = 0) :
    predict x = predict x' := by
  have hdiff : observe (x - x') = 0 := by
    simp only [map_sub]
    simp [observationFiber] at hx hx'
    rw [hx, hx']
    simp
  have hzero := annihilates_kernel (x - x') hdiff
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- If a receiver query varies along an unresolved kernel direction, two models with the same
returned observation give different predictions. This existential discriminator theorem does
not specify how an implementation finds the direction or chooses a query. -/
theorem kernel_direction_distinguishes
    (observe : X →ₗ[ℚ] Y) (predict : X →ₗ[ℚ] ℚ) (returned : Y)
    (x z : X) (hx : x ∈ observationFiber observe returned)
    (hz : observe z = 0) (varies : predict z ≠ 0) :
    ∃ x', x' ∈ observationFiber observe returned ∧ predict x' ≠ predict x := by
  refine ⟨x + z, ?_, ?_⟩
  · change observe (x + z) = returned
    rw [map_add, hx, hz, add_zero]
  · intro equal
    have hsum : predict x + predict z = predict x + 0 := by
      simpa [map_add] using equal
    exact varies (add_left_cancel hsum)

end Soma.Holonics.Transport.GenerativeTransport

#print axioms Soma.Holonics.Transport.GenerativeTransport.eventOperator_interval_difference
#print axioms Soma.Holonics.Transport.GenerativeTransport.prediction_invariant_on_fiber
#print axioms Soma.Holonics.Transport.GenerativeTransport.kernel_direction_distinguishes
