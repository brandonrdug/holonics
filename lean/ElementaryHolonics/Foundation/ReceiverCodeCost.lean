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
open scoped BigOperators

/-! ## A positive generator supplies an explicit code/boundary law

Given a positive eigenvector v of a nonnegative finite weighted adjacency A, the normalized
transition is A_ij v_j / (lambda v_i). The actual eigenvector equation, support and positive
scale are hypotheses. This constructs a code comparison, not a generic efficient eigensolver
or a physical dissipation identification.
-/

noncomputable def perronTransition (weight sourceMode targetMode eigenvalue : ℝ) : ℝ :=
  weight * targetMode / (eigenvalue * sourceMode)

theorem perronTransition_nonnegative {weight sourceMode targetMode eigenvalue : ℝ}
    (hw : 0 ≤ weight) (hs : 0 < sourceMode) (ht : 0 < targetMode)
    (hl : 0 < eigenvalue) :
    0 ≤ perronTransition weight sourceMode targetMode eigenvalue := by
  exact div_nonneg (mul_nonneg hw ht.le) (mul_pos hl hs).le

theorem perronTransition_normalized {Index : Type*} [Fintype Index]
    (weight : Index → Index → ℝ) (mode : Index → ℝ) (eigenvalue : ℝ) (source : Index)
    (hs : mode source ≠ 0) (hl : eigenvalue ≠ 0)
    (row : ∑ target, weight source target * mode target = eigenvalue * mode source) :
    ∑ target, perronTransition (weight source target) (mode source) (mode target) eigenvalue = 1 := by
  unfold perronTransition
  rw [← Finset.sum_div, row, div_self (mul_ne_zero hl hs)]

theorem perron_edge_code_balance {weight sourceMode targetMode eigenvalue : ℝ}
    (hw : 0 < weight) (hs : 0 < sourceMode) (ht : 0 < targetMode)
    (hl : 0 < eigenvalue) :
    -Real.log (perronTransition weight sourceMode targetMode eigenvalue) / Real.log 2 =
      (Real.log eigenvalue - Real.log weight) / Real.log 2 +
        Real.log sourceMode / Real.log 2 - Real.log targetMode / Real.log 2 := by
  unfold perronTransition
  rw [Real.log_div (mul_pos hw ht).ne' (mul_pos hl hs).ne',
    Real.log_mul hw.ne' ht.ne', Real.log_mul hl.ne' hs.ne']
  ring

/-- Symmetric edge weights make squared eigenvector weights balance the two directed currents.
Normalizing these squared weights supplies the stationary law when the rows normalize. -/
theorem perron_detailed_balance {weight sourceMode targetMode eigenvalue : ℝ}
    (hs : sourceMode ≠ 0) (ht : targetMode ≠ 0) (hl : eigenvalue ≠ 0) :
    sourceMode ^ 2 * perronTransition weight sourceMode targetMode eigenvalue =
      targetMode ^ 2 * perronTransition weight targetMode sourceMode eigenvalue := by
  unfold perronTransition
  field_simp [hs, ht, hl]

/-! ## Directed flux comparison -/

/-- A paired directed-flux code comparison. If the two positive inputs are occurrence rates
in the same clock/units, this is a bit rate. It becomes physical entropy production only
through an admitted stochastic/constitutive source and its boundary assumptions. -/
noncomputable def edgeCodeProduction (forward backward : ℝ) : ℝ :=
  (forward - backward) * (Real.log forward - Real.log backward) / Real.log 2

/-- The oriented flux difference and code ratio both reverse sign under exchanging directions;
their paired production is unchanged. This is distinct from reversing elapsed coordinates. -/
theorem edgeCodeProduction_swap (forward backward : ℝ) :
    edgeCodeProduction backward forward = edgeCodeProduction forward backward := by
  unfold edgeCodeProduction
  ring

theorem edgeCodeProduction_nonnegative {forward backward : ℝ}
    (hf : 0 < forward) (hb : 0 < backward) :
    0 ≤ edgeCodeProduction forward backward := by
  apply div_nonneg _ (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  rcases le_total backward forward with h | h
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.log_le_log hb h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (Real.log_le_log hf h))

/-- The actual symmetric-generator balance annihilates this paired code production. -/
theorem perron_edgeCodeProduction_zero {weight sourceMode targetMode eigenvalue : ℝ}
    (hs : sourceMode ≠ 0) (ht : targetMode ≠ 0) (hl : eigenvalue ≠ 0) :
    edgeCodeProduction
      (sourceMode ^ 2 * perronTransition weight sourceMode targetMode eigenvalue)
      (targetMode ^ 2 * perronTransition weight targetMode sourceMode eigenvalue) = 0 := by
  rw [perron_detailed_balance hs ht hl]
  simp [edgeCodeProduction]

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

#print axioms perronTransition_nonnegative
#print axioms perronTransition_normalized
#print axioms perron_edge_code_balance
#print axioms perron_detailed_balance

end Soma.Holonics.Foundation.ReceiverCodeCost
