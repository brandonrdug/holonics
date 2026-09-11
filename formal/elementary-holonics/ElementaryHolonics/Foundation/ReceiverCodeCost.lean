import ElementaryHolonics.Foundation.Holon
import ElementaryHolonics.Foundation.SituatedInformationRate

/-!
# Receiver-relative code cost

This owner keeps a code face, its declared cost, and the endpoint potential terms in one
receiver chart.  Serial composition uses the existing pullback interaction, so the middle
potential cancels only through its stored joining equality.

[proved-derived] The theorems retain their displayed balance, positivity, residual and
feasibility hypotheses. They define no physical constitutive identification or generic optimizer.
-/

namespace Soma.Holonics.Foundation.ReceiverCodeCost

open Soma.Holonics

/-! ## Serial boundary balance -/

theorem serial_boundary_balance
    {Source Middle Target : Type*}
    (left : Holon Source Middle ℝ) (right : Holon Middle Target ℝ)
    (C : ℝ) (costL : left.Occurrence → ℝ) (costR : right.Occurrence → ℝ)
    (sourcePotential : Source → ℝ) (middlePotential : Middle → ℝ)
    (targetPotential : Target → ℝ)
    (residualL : left.Occurrence → ℝ) (residualR : right.Occurrence → ℝ)
    (hL : ∀ x, left.receive x =
      C * costL x + sourcePotential (left.source x) - middlePotential (left.target x) + residualL x)
    (hR : ∀ y, right.receive y =
      C * costR y + middlePotential (right.source y) - targetPotential (right.target y) + residualR y)
    (joined : Holon.Interaction left right) :
    left.receive (joined.left : left.Occurrence) + right.receive (joined.right : right.Occurrence) =
      C * (costL (joined.left : left.Occurrence) + costR (joined.right : right.Occurrence)) +
        sourcePotential (left.source (joined.left : left.Occurrence)) -
        targetPotential (right.target (joined.right : right.Occurrence)) +
        (residualL (joined.left : left.Occurrence) + residualR (joined.right : right.Occurrence)) := by
  let lx : left.Occurrence := joined.left
  let ry : right.Occurrence := joined.right
  have hLj := hL lx
  have hRj := hR ry
  have hjoin : left.target lx = right.source ry := joined.joins
  rw [hLj, hRj]
  change C * costL lx + sourcePotential (left.source lx) - middlePotential (left.target lx) + residualL lx +
      (C * costR ry + middlePotential (right.source ry) - targetPotential (right.target ry) + residualR ry) = _
  rw [hjoin]
  ring

/-! ## A real cost bracket from a receiver reading -/

theorem cost_mem_Icc_of_code_balance
    {C cost ell boundary residual B E : ℝ}
    (hC : 0 < C)
    (balance : ell = C * cost + boundary + residual)
    (hboundary : |boundary| ≤ B) (hresidual : |residual| ≤ E) :
    cost ∈ Set.Icc ((ell - B - E) / C) ((ell + B + E) / C) := by
  constructor
  · apply (div_le_iff₀ hC).2
    have hb : boundary ≤ B := le_trans (le_abs_self boundary) hboundary
    have he : residual ≤ E := le_trans (le_abs_self residual) hresidual
    rw [balance]
    have hb' : 0 ≤ B - boundary := by linarith
    have he' : 0 ≤ E - residual := by linarith
    have hcomm : C * cost = cost * C := by ring
    linarith
  · apply (le_div_iff₀ hC).2
    have hb : -B ≤ boundary := neg_le_of_abs_le hboundary
    have he : -E ≤ residual := neg_le_of_abs_le hresidual
    rw [balance]
    have hb' : 0 ≤ boundary + B := by linarith
    have he' : 0 ≤ residual + E := by linarith
    have hcomm : C * cost = cost * C := by ring
    linarith

/-! ## Transport of an optimum across an exact candidate equivalence -/

theorem feasible_cost_le_transported
    {Candidate Candidate' : Type*} (equiv : Candidate ≃ Candidate')
    (feasible : Candidate → Prop) (feasible' : Candidate' → Prop)
    (cost : Candidate → ℝ) (cost' : Candidate' → ℝ)
    (feasible_transport : ∀ x, feasible x ↔ feasible' (equiv x))
    (cost_transport : ∀ x, cost' (equiv x) = cost x)
    {x : Candidate} (hx : feasible x)
    (hmin : ∀ z, feasible z → cost x ≤ cost z) :
    feasible' (equiv x) ∧ ∀ z, feasible' z → cost' (equiv x) ≤ cost' z := by
  constructor
  · exact (feasible_transport x).1 hx
  · intro z hz
    calc
      cost' (equiv x) = cost x := cost_transport x
      _ ≤ cost (equiv.symm z) := hmin (equiv.symm z)
        ((feasible_transport (equiv.symm z)).2 (by simpa using hz))
      _ = cost' z := by
        convert (cost_transport (equiv.symm z)).symm using 1 <;> simp

end Soma.Holonics.Foundation.ReceiverCodeCost
