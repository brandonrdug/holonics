import Holonics.Physics.CoupledIncidence
import Holonics.Transport.ChangingReceiver
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

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

namespace Holonics.Physics.ConstitutiveModulation

open scoped BigOperators
open Holonics.Physics.HolonicComplexParametron

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

section RodStrain

/-!
## A finite twist/bend/stretch rod chart

This is a three-coordinate constitutive specialization of the existing finite response owner.
`bend`, `twist`, and `stretch` are dimensionless chart coordinates; the six coefficients are
caller-supplied entries of one symmetric constitutive matrix. The chart retains reciprocal
twist/stretch coupling and is not a calibrated DNA, protein, or material rod law. -/

/-- A finite rod strain chart with bending, material twist, and extension coordinates. -/
structure RodStrain where
  bend : ℝ
  twist : ℝ
  stretch : ℝ

/-- Independent entries of a symmetric bend/twist/stretch constitutive matrix. -/
structure RodConstitutive where
  bendBend : ℝ
  twistTwist : ℝ
  stretchStretch : ℝ
  bendTwist : ℝ
  bendStretch : ℝ
  twistStretch : ℝ

/-- The symmetric constitutive matrix represented by `RodConstitutive`. -/
def rodMatrix (c : RodConstitutive) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![c.bendBend, c.bendTwist, c.bendStretch;
     c.bendTwist, c.twistTwist, c.twistStretch;
     c.bendStretch, c.twistStretch, c.stretchStretch]

/-- The identity branch/node incidence used to expose a three-coordinate constitutive response. -/
def rodIdentityIncidence : Fin 3 → Fin 3 → ℝ :=
  fun branch node ↦ if branch = node then 1 else 0

/-- Coordinates of one rod strain in the existing branch-state interface. -/
def rodStrainCoords (x : RodStrain) : Fin 3 → ℝ :=
  ![x.bend, x.twist, x.stretch]

/-- The stored coefficient matrix is symmetric by construction. -/
theorem rodMatrix_symmetric (c : RodConstitutive) : (rodMatrix c).transpose = rodMatrix c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rodMatrix]

/-- The finite quadratic energy of the dimensionless rod chart. -/
def rodEnergy (c : RodConstitutive) (x : RodStrain) : ℝ :=
  (1 / 2 : ℝ) * (c.bendBend * x.bend ^ 2 + c.twistTwist * x.twist ^ 2 +
    c.stretchStretch * x.stretch ^ 2 + 2 * c.bendTwist * x.bend * x.twist +
    2 * c.bendStretch * x.bend * x.stretch + 2 * c.twistStretch * x.twist * x.stretch)

/-- The bend moment, torque, and extension force returned by the quadratic rod energy. -/
structure RodResponse where
  bendMoment : ℝ
  torque : ℝ
  force : ℝ

/-- The constitutive response, including all reciprocal cross-coupled terms. -/
def rodResponse (c : RodConstitutive) (x : RodStrain) : RodResponse where
  bendMoment := c.bendBend * x.bend + c.bendTwist * x.twist + c.bendStretch * x.stretch
  torque := c.bendTwist * x.bend + c.twistTwist * x.twist + c.twistStretch * x.stretch
  force := c.bendStretch * x.bend + c.twistStretch * x.twist + c.stretchStretch * x.stretch

/-- Coordinates of the constitutive response in bend, twist, and stretch order. -/
def rodResponseCoords (c : RodConstitutive) (x : RodStrain) : Fin 3 → ℝ :=
  ![(rodResponse c x).bendMoment, (rodResponse c x).torque, (rodResponse c x).force]

/-- The rod response is the existing `coupledResponse` owner on the identity incidence chart. -/
theorem rodResponse_coords_eq_coupledResponse (c : RodConstitutive) (x : RodStrain) :
    rodResponseCoords c x =
      fun node ↦ coupledResponse (rodMatrix c) rodIdentityIncidence (rodStrainCoords x) node := by
  funext node
  fin_cases node <;>
    simp [rodResponseCoords, rodResponse, rodMatrix, rodIdentityIncidence, rodStrainCoords,
      coupledResponse, branchDrop, Fin.sum_univ_succ] <;> ring

/-- The quadratic energy is one half of strain paired with its constitutive response. -/
theorem rodEnergy_eq_half_response_pairing (c : RodConstitutive) (x : RodStrain) :
    rodEnergy c x = (1 / 2 : ℝ) *
      (x.bend * (rodResponse c x).bendMoment + x.twist * (rodResponse c x).torque +
        x.stretch * (rodResponse c x).force) := by
  simp [rodEnergy, rodResponse]
  ring

/-- A finite twist increment returns its torque and the twist diagonal remainder. -/
theorem rodEnergy_twist_increment (c : RodConstitutive) (x : RodStrain) (delta : ℝ) :
    rodEnergy c {x with twist := x.twist + delta} - rodEnergy c x =
      (rodResponse c x).torque * delta + (c.twistTwist / 2) * delta ^ 2 := by
  simp [rodEnergy, rodResponse]
  ring

/-- A finite extension increment returns its force and the extension diagonal remainder. -/
theorem rodEnergy_stretch_increment (c : RodConstitutive) (x : RodStrain) (delta : ℝ) :
    rodEnergy c {x with stretch := x.stretch + delta} - rodEnergy c x =
      (rodResponse c x).force * delta + (c.stretchStretch / 2) * delta ^ 2 := by
  simp [rodEnergy, rodResponse]
  ring

/-- Holding bend and twist fixed, extension changes torque through the cross coefficient. -/
theorem rodTorque_same_twist_different_extension
    (c : RodConstitutive) (left right : RodStrain)
    (same_bend : left.bend = right.bend) (same_twist : left.twist = right.twist) :
    (rodResponse c left).torque - (rodResponse c right).torque =
      c.twistStretch * (left.stretch - right.stretch) := by
  simp [rodResponse, same_bend, same_twist]
  ring

/-- Nonzero twist/extension coupling makes equal-twist, unequal-extension states torque-distinct. -/
theorem rodTorque_separates_extension
    (c : RodConstitutive) (left right : RodStrain)
    (same_bend : left.bend = right.bend) (same_twist : left.twist = right.twist)
    (coupling_ne : c.twistStretch ≠ 0) (extension_ne : left.stretch ≠ right.stretch) :
    (rodResponse c left).torque ≠ (rodResponse c right).torque := by
  intro equal_torque
  have zero_product : c.twistStretch * (left.stretch - right.stretch) = 0 := by
    rw [← rodTorque_same_twist_different_extension c left right same_bend same_twist]
    simp [equal_torque]
  rcases mul_eq_zero.mp zero_product with coupling_zero | extension_zero
  · exact coupling_ne coupling_zero
  · exact extension_ne (sub_eq_zero.mp extension_zero)

/-- The same coupling is returned reciprocally by extension force under a twist change. -/
theorem rod_cross_response_reciprocal
    (c : RodConstitutive) (x : RodStrain) (twist_delta stretch_delta : ℝ) :
    (rodResponse c {x with stretch := x.stretch + stretch_delta}).torque -
        (rodResponse c x).torque = c.twistStretch * stretch_delta ∧
      (rodResponse c {x with twist := x.twist + twist_delta}).force -
        (rodResponse c x).force = c.twistStretch * twist_delta := by
  constructor <;> simp [rodResponse] <;> ring

end RodStrain

section ConstitutivePullback

variable {Strain : Type*} [NormedAddCommGroup Strain] [NormedSpace ℝ Strain]

/-- The first variation of a declared potential through its actual strain chart. -/
theorem potential_strain_first_variation
    (potential : Strain → ℝ) (strain : ℝ → Strain) (time : ℝ)
    (stress : Strain →L[ℝ] ℝ) (velocity : Strain)
    (hpotential : HasFDerivAt potential stress (strain time))
    (hstrain : HasDerivAt strain velocity time) :
    HasDerivAt (fun t ↦ potential (strain t)) (stress velocity) time :=
  hpotential.comp_hasDerivAt time hstrain

/-- The derivative of the pulled-back force retains material and geometric/prestress terms.
`strainRate` is the actual first strain derivative where the potential interpretation is made;
the displayed hypotheses supply its value and derivative at this cut. `stiffness` is the actual
derivative of stress, rather than a caller's replacement of the nonlinear geometry by `Bᵀ M B`.
This is the moving-receiver theorem with stress as receiver and strain rate as its current. -/
theorem stress_strain_rate_return
    (stress : Strain → Strain →L[ℝ] ℝ) (strain strainRate : ℝ → Strain)
    (time : ℝ) (velocity acceleration : Strain)
    (stiffness : Strain →L[ℝ] Strain →L[ℝ] ℝ)
    (hstrain : HasDerivAt strain velocity time)
    (hstrainRate : HasDerivAt strainRate acceleration time)
    (rate_at : strainRate time = velocity)
    (hstress : HasFDerivAt stress stiffness (strain time)) :
    HasDerivAt (fun t ↦ stress (strain t) (strainRate t))
      (stiffness velocity velocity + stress (strain time) acceleration) time := by
  have h := Transport.ChangingReceiver.moving_receiver_rate
    (fun t ↦ stress (strain t)) strainRate time (stiffness velocity)
    (fun _ ↦ acceleration) (fun _ ↦ 0)
    (hstress.comp_hasDerivAt time hstrain) hstrainRate
  simpa [Transport.ChangingReceiver.rateDefect, rate_at] using h

end ConstitutivePullback

end Holonics.Physics.ConstitutiveModulation

section Audit
open Holonics.Physics.ConstitutiveModulation
#print axioms coupledResponse_finite_change
#print axioms coupledResponse_material_state_change
#print axioms tangent_cancellation_does_not_close_finite_response
#print axioms rodMatrix_symmetric
#print axioms rodResponse_coords_eq_coupledResponse
#print axioms rodEnergy_eq_half_response_pairing
#print axioms rodEnergy_twist_increment
#print axioms rodEnergy_stretch_increment
#print axioms rodTorque_same_twist_different_extension
#print axioms rodTorque_separates_extension
#print axioms rod_cross_response_reciprocal
#print axioms potential_strain_first_variation
#print axioms stress_strain_rate_return
end Audit
