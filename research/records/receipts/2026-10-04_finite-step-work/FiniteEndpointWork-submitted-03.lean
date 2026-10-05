import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

namespace Holonics.Geometry.Motion

open Matrix

/-! ## 13. Finite work between independently charted receiver sections -/

section FiniteMetric

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

/-- [proved-derived; source-only] The finite work form transports through the initial
chart. `P` and `V` are the ending chart and its left inverse; `W` pulls the initial
chart back. Distinct endpoint charts are allowed. No symmetry or positivity is
needed for this algebraic identity. The material forms may genuinely differ.
Record: `2026-10-04_FINITE_STEP_WORK_AND_GAIN_TRANSPORT_BETWEEN_ENDPOINT_CHARTS`.
Consumer: the decoder/metric square of a native continuation opening, beside its
independently computed physical work and `opening_difference`; that square is owed. -/
theorem finite_work_form_rechart (P V W T G0 G1 : Matrix n n K) (hVP : V * P = 1) :
    (P * T * W)ᵀ * (Vᵀ * G1 * V) * (P * T * W) - Wᵀ * G0 * W =
      Wᵀ * (Tᵀ * G1 * T - G0) * W := by
  have hL : ∀ Y : Matrix n n K, Pᵀ * (Vᵀ * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hVP, Matrix.transpose_one,
      Matrix.one_mul]
  have hR : ∀ Y : Matrix n n K, V * (P * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, hVP, Matrix.one_mul]
  simp only [Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, hL, hR]

/-- [proved-derived; source-only] Twice the energy change of the affine motion
`x_next = T x + b`. The cross term and the source's self-energy both remain. This
statement is undivided and needs no inverse of two; a symmetric ending form is the
hypothesis joining its two cross terms. -/
theorem affine_quadratic_work (T G0 G1 : Matrix n n K) (x b : n → K)
    (hG1 : G1ᵀ = G1) :
    (T *ᵥ x + b) ⬝ᵥ (G1 *ᵥ (T *ᵥ x + b)) - x ⬝ᵥ (G0 *ᵥ x) =
      x ⬝ᵥ ((Tᵀ * G1 * T - G0) *ᵥ x) +
        2 * (x ⬝ᵥ ((Tᵀ * G1) *ᵥ b)) + b ⬝ᵥ (G1 *ᵥ b) := by
  have hsymm (u v : n → K) : u ⬝ᵥ (G1 *ᵥ v) = v ⬝ᵥ (G1 *ᵥ u) := by
    have hu : u ᵥ* G1 = G1 *ᵥ u := by
      conv_lhs => rw [← hG1]
      exact Matrix.vecMul_transpose G1 u
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, hu]
  have hT : (T *ᵥ x) ⬝ᵥ (G1 *ᵥ (T *ᵥ x)) =
      x ⬝ᵥ ((Tᵀ * G1 * T) *ᵥ x) := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hcross : (T *ᵥ x) ⬝ᵥ (G1 *ᵥ b) = x ⬝ᵥ ((Tᵀ * G1) *ᵥ b) := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    hsymm b (T *ᵥ x), hT, Matrix.sub_mulVec, dotProduct_sub]
  simp only [hcross]
  ring

end FiniteMetric

end Holonics.Geometry.Motion

#print axioms Holonics.Geometry.Motion.finite_work_form_rechart
#print axioms Holonics.Geometry.Motion.affine_quadratic_work
