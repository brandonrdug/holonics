import ElementaryHolonics.Physics.CoupledIncidence

/-!
# A changing conformation changes the complete coupled response

[definition] In this finite real chart, conformation is presented through the actual incidence
`B` and mutual constitutive form `M`. The standing response is the existing `Bᵀ M B x` owner.
The same algebra can describe a mechanical stiffness, an electrical admittance, or a local
linearization of a molecular interaction once those constitutive identifications are supplied.

[proved-derived] The exact finite difference below retains changes in both occurrences of `B`,
in `M`, and in the internal state. Its shifted factors include every mixed term. It requires no
infinitesimal update or invertibility. It is not a molecular force law or a native learning rule.
-/

noncomputable section

namespace Soma.Holonics.Physics.ConstitutiveModulation

open scoped BigOperators
open Soma.Holonics.Millennium.HolonicComplexParametron

variable {Node Branch : Type*} [Fintype Node] [Fintype Branch]

/-- The complete finite response, with each changing factor returned in its producing order.
The two incidence contributions are separate even though both are presented by the same `B`.
Replacing every shifted factor by its predecessor would retain only a tangent approximation. -/
theorem coupledResponse_finite_change
    (beforeCoupling afterCoupling : Branch → Branch → ℝ)
    (beforeIncidence afterIncidence : Branch → Node → ℝ)
    (beforeState afterState : Node → ℝ) (node : Node) :
    coupledResponse afterCoupling afterIncidence afterState node -
        coupledResponse beforeCoupling beforeIncidence beforeState node =
      coupledResponse afterCoupling afterIncidence (fun n ↦ afterState n - beforeState n) node +
      (∑ first, (afterIncidence first node - beforeIncidence first node) *
        ∑ second, afterCoupling first second *
          branchDrop afterIncidence beforeState second) +
      (∑ first, beforeIncidence first node *
        ∑ second, (afterCoupling first second - beforeCoupling first second) *
          branchDrop afterIncidence beforeState second) +
      (∑ first, beforeIncidence first node *
        ∑ second, beforeCoupling first second *
          branchDrop (fun b n ↦ afterIncidence b n - beforeIncidence b n)
            beforeState second) := by
  simp only [coupledResponse, branchDrop, sub_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  abel

/-- With incidence held fixed, changing material and current still returns a mixed term.
This is an exact finite law for the existing response, not a claim that its first derivative
alone gives the finite successor. -/
theorem coupledResponse_material_state_change
    (coupling deltaCoupling : Branch → Branch → ℝ)
    (incidence : Branch → Node → ℝ) (state deltaState : Node → ℝ) (node : Node) :
    coupledResponse (fun a b ↦ coupling a b + deltaCoupling a b) incidence
        (fun n ↦ state n + deltaState n) node -
        coupledResponse coupling incidence state node =
      coupledResponse coupling incidence deltaState node +
      coupledResponse deltaCoupling incidence state node +
      coupledResponse deltaCoupling incidence deltaState node := by
  simp only [coupledResponse, branchDrop, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  abel

/-- [counterexample] One scalar coupled carrier already separates a zero tangent return from
the finite response. With `B = 1`, `M = x = 1`, `delta M = 1`, `delta x = -1`, the two tangent
contributions cancel, while the mixed contribution and full response change equal `-1`. -/
theorem tangent_cancellation_does_not_close_finite_response :
    let B : Unit → Unit → ℝ := fun _ _ ↦ 1
    let M : Unit → Unit → ℝ := fun _ _ ↦ 1
    let x : Unit → ℝ := fun _ ↦ 1
    let dx : Unit → ℝ := fun _ ↦ -1
    coupledResponse M B dx () + coupledResponse M B x () = 0 ∧
      coupledResponse (fun _ _ ↦ 2) B (fun _ ↦ 0) () - coupledResponse M B x () = -1 := by
  norm_num [coupledResponse, branchDrop]

end Soma.Holonics.Physics.ConstitutiveModulation

section Audit
open Soma.Holonics.Physics.ConstitutiveModulation
#print axioms coupledResponse_finite_change
#print axioms coupledResponse_material_state_change
#print axioms tangent_cancellation_does_not_close_finite_response
end Audit
