import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Released motion in a constant-acceleration chart

This is the exact weak-field, constant-acceleration passage, used for GR-derived motion
simulation and biomechanical prediction. Its acceleration field is prescribed in a local chart.
-/

namespace Holonics.Physics.ReleasedMotion

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def position (x₀ v₀ g : V) (t : ℝ) : V :=
  x₀ + t • v₀ + (t ^ 2 / 2) • g

def velocity (v₀ g : V) (t : ℝ) : V := v₀ + t • g

theorem position_zero (x₀ v₀ g : V) : position x₀ v₀ g 0 = x₀ := by
  simp [position]

theorem velocity_zero (v₀ g : V) : velocity v₀ g 0 = v₀ := by
  simp [velocity]

theorem flow_position (x₀ v₀ g : V) (t s : ℝ) :
    position x₀ v₀ g (t + s) =
      position (position x₀ v₀ g t) (velocity v₀ g t) g s := by
  simp only [position, velocity, add_smul]
  module

theorem flow_velocity (v₀ g : V) (t s : ℝ) :
    velocity v₀ g (t + s) = velocity (velocity v₀ g t) g s := by
  simp only [velocity, add_smul]
  module

def releasedVelocity (v J : V) (m : ℝ) : V := v + (1 / m) • J

theorem releasedVelocity_momentum_increment (v J : V) {m : ℝ} (hm : 0 < m) :
    m • releasedVelocity v J m - m • v = J := by
  simp [releasedVelocity, smul_add, smul_smul, hm.ne']

def kineticEnergy (m : ℝ) (v : V) : ℝ := m / 2 * ‖v‖ ^ 2

/-- Potential for the supplied spatially uniform acceleration field. -/
def potentialEnergy (m : ℝ) (g x : V) : ℝ := -m * inner ℝ g x

theorem constant_acceleration_total_energy (m : ℝ) (x₀ v₀ g : V) (t : ℝ) :
    kineticEnergy m (velocity v₀ g t) + potentialEnergy m g (position x₀ v₀ g t) =
      kineticEnergy m v₀ + potentialEnergy m g x₀ := by
  unfold kineticEnergy potentialEnergy velocity position
  rw [norm_add_sq_real]
  simp only [inner_add_right, real_inner_smul_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq, real_inner_comm g v₀, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

theorem releasedVelocity_kinetic_work_increment (v J : V) {m : ℝ} (hm : 0 < m) :
    kineticEnergy m (releasedVelocity v J m) - kineticEnergy m v =
      inner ℝ v J + ‖J‖ ^ 2 / (2 * m) := by
  unfold kineticEnergy releasedVelocity
  rw [norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [hm.ne']
  ring

def endpointDefect (xΔ vΔ gΔ : V) (t : ℝ) : V :=
  xΔ + t • vΔ + (t ^ 2 / 2) • gΔ

theorem position_endpoint_defect
    (x₀ x₁ v₀ v₁ g₀ g₁ : V) (t : ℝ) :
    position x₁ v₁ g₁ t - position x₀ v₀ g₀ t =
      endpointDefect (x₁ - x₀) (v₁ - v₀) (g₁ - g₀) t := by
  simp only [position, endpointDefect, smul_sub]
  module

theorem endpoint_defect_norm_le
    (xΔ vΔ gΔ : V) (t : ℝ) :
    ‖endpointDefect xΔ vΔ gΔ t‖ ≤
      ‖xΔ‖ + |t| * ‖vΔ‖ + (t ^ 2 / 2) * ‖gΔ‖ := by
  unfold endpointDefect
  calc
    ‖xΔ + t • vΔ + (t ^ 2 / 2) • gΔ‖ ≤
        ‖xΔ‖ + ‖t • vΔ‖ + ‖(t ^ 2 / 2) • gΔ‖ := by
          rw [show xΔ + t • vΔ + (t ^ 2 / 2) • gΔ =
            (xΔ + t • vΔ) + (t ^ 2 / 2) • gΔ by abel]
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖xΔ‖ + |t| * ‖vΔ‖ + (t ^ 2 / 2) * ‖gΔ‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (sq_nonneg t) (by norm_num))]

section Audit

#print axioms flow_position
#print axioms flow_velocity
#print axioms constant_acceleration_total_energy
#print axioms releasedVelocity_momentum_increment
#print axioms releasedVelocity_kinetic_work_increment
#print axioms position_endpoint_defect
#print axioms endpoint_defect_norm_le

end Audit

end
end Holonics.Physics.ReleasedMotion
