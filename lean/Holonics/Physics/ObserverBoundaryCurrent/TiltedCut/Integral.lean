import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The oriented current integral on one transported cut

This is the scalar integral consumer of a constant boost with PLUS off-diagonal
xi. The inverse field argument and (dy,-dtau) surface covector are explicit.
The field-current consumer in TiltedCut supplies the existing Tensor/covector
current, not a desired integral equality. Ordinary integrable traces only.
Refs #62 / #146.
-/

noncomputable section
namespace Holonics.Physics.ObserverBoundaryCurrent.TiltedCut
open MeasureTheory

/-- The actual inverse time argument for the plus-sign boost. -/
def inverseTime (γ ξ τ y : ℝ) : ℝ := γ * τ - ξ * y

/-- The actual inverse space argument for the plus-sign boost. -/
def inverseSpace (γ ξ τ y : ℝ) : ℝ := γ * y - ξ * τ

/-- The graph of the transported source cut t=constant, parameterized by y. -/
def graphTime (γ ξ t y : ℝ) : ℝ := t / γ + (ξ / γ) * y

/-- Both current values are evaluated at the same inverse event. -/
def pulledCurrent0 (γ ξ : ℝ) (J0 J1 : ℝ → ℝ → ℝ) (τ y : ℝ) : ℝ :=
  γ * J0 (inverseTime γ ξ τ y) (inverseSpace γ ξ τ y) +
    ξ * J1 (inverseTime γ ξ τ y) (inverseSpace γ ξ τ y)

def pulledCurrent1 (γ ξ : ℝ) (J0 J1 : ℝ → ℝ → ℝ) (τ y : ℝ) : ℝ :=
  ξ * J0 (inverseTime γ ξ τ y) (inverseSpace γ ξ τ y) +
    γ * J1 (inverseTime γ ξ τ y) (inverseSpace γ ξ τ y)

/-- J'^0 dy - J'^1 dtau, with dtau/dy=xi/gamma. -/
def orientedFlux (γ ξ : ℝ) (J0 J1 : ℝ → ℝ → ℝ) (t y : ℝ) : ℝ :=
  pulledCurrent0 γ ξ J0 J1 (graphTime γ ξ t y) y -
    (ξ / γ) * pulledCurrent1 γ ξ J0 J1 (graphTime γ ξ t y) y

theorem inverse_graph_time (γ ξ t y : ℝ) (hγ : γ ≠ 0) :
    inverseTime γ ξ (graphTime γ ξ t y) y = t := by
  unfold inverseTime graphTime
  field_simp [hγ]
  ring

theorem inverse_graph_space (γ ξ t y : ℝ) (hγ : γ ≠ 0)
    (hLorentz : γ ^ 2 - ξ ^ 2 = 1) :
    inverseSpace γ ξ (graphTime γ ξ t y) y = (y - ξ * t) / γ := by
  unfold inverseSpace graphTime
  calc
    γ * y - ξ * (t / γ + ξ / γ * y) =
        (γ ^ 2 - ξ ^ 2) * (y / γ) - ξ * t / γ := by
      field_simp [hγ]
      ring
    _ = (y - ξ * t) / γ := by rw [hLorentz]; ring

/-- The complete oriented surface contraction cancels the boosted spatial
current, after the inverse event has been identified. -/
theorem orientedFlux_eq (γ ξ : ℝ) (J0 J1 : ℝ → ℝ → ℝ) (t y : ℝ)
    (hγ : γ ≠ 0) (hLorentz : γ ^ 2 - ξ ^ 2 = 1) :
    orientedFlux γ ξ J0 J1 t y = J0 t ((y - ξ * t) / γ) / γ := by
  unfold orientedFlux pulledCurrent0 pulledCurrent1
  rw [inverse_graph_time γ ξ t y hγ, inverse_graph_space γ ξ t y hγ hLorentz]
  calc
    γ * J0 t ((y - ξ * t) / γ) + ξ * J1 t ((y - ξ * t) / γ) -
        ξ / γ * (ξ * J0 t ((y - ξ * t) / γ) + γ * J1 t ((y - ξ * t) / γ)) =
        (γ ^ 2 - ξ ^ 2) * (J0 t ((y - ξ * t) / γ) / γ) := by
      field_simp [hγ]
      ring
    _ = _ := by rw [hLorentz]; simp

/-- Integrability is transported rather than assumed for the desired flux.
Cancellation precedes integration, so the two summands need not separately
be integrable. -/
theorem orientedFlux_integrable (γ ξ : ℝ) (J0 J1 : ℝ → ℝ → ℝ)
    (t l r : ℝ) (hγ : 0 < γ) (hLorentz : γ ^ 2 - ξ ^ 2 = 1)
    (htrace : IntervalIntegrable (J0 t) volume l r) :
    IntervalIntegrable (orientedFlux γ ξ J0 J1 t) volume
      (γ * l + ξ * t) (γ * r + ξ * t) := by
  have heq : orientedFlux γ ξ J0 J1 t =
      fun y => J0 t ((y - ξ * t) / γ) / γ :=
    funext (fun y => orientedFlux_eq γ ξ J0 J1 t y (ne_of_gt hγ) hLorentz)
  rw [heq]
  have hi := ((htrace.comp_mul_left (c := γ⁻¹)).comp_add_right (-(ξ * t))).div_const γ
  simpa only [div_eq_mul_inv, inv_inv, sub_eq_add_neg, neg_neg, mul_comm] using hi

/-- A genuine same-surface integral covariance statement. The affine
change-of-variable owner supplies its Jacobian; no field equation or
independent constant-time target cut is used. -/
theorem transported_cut_integral (γ ξ : ℝ) (J0 J1 : ℝ → ℝ → ℝ)
    (t l r : ℝ) (hγ : 0 < γ) (hLorentz : γ ^ 2 - ξ ^ 2 = 1)
    (htrace : IntervalIntegrable (J0 t) volume l r) :
    IntervalIntegrable (orientedFlux γ ξ J0 J1 t) volume
      (γ * l + ξ * t) (γ * r + ξ * t) ∧
      (∫ y in (γ * l + ξ * t)..(γ * r + ξ * t), orientedFlux γ ξ J0 J1 t y) =
        ∫ x in l..r, J0 t x := by
  refine ⟨orientedFlux_integrable γ ξ J0 J1 t l r hγ hLorentz htrace, ?_⟩
  have hc : ∀ x, orientedFlux γ ξ J0 J1 t (γ * x + ξ * t) = J0 t x / γ := by
    intro x
    rw [orientedFlux_eq γ ξ J0 J1 t _ (ne_of_gt hγ) hLorentz]
    congr 2
    field_simp [ne_of_gt hγ]
    ring
  calc
    (∫ y in (γ * l + ξ * t)..(γ * r + ξ * t), orientedFlux γ ξ J0 J1 t y) =
        γ * ∫ x in l..r, orientedFlux γ ξ J0 J1 t (γ * x + ξ * t) := by
      simpa only [smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_add (orientedFlux γ ξ J0 J1 t) γ (ξ * t)).symm
    _ = γ * ∫ x in l..r, J0 t x / γ := by simp_rw [hc]
    _ = ∫ x in l..r, J0 t x := by
      rw [intervalIntegral.integral_div]
      exact mul_div_cancel₀ _ (ne_of_gt hγ)

end Holonics.Physics.ObserverBoundaryCurrent.TiltedCut
