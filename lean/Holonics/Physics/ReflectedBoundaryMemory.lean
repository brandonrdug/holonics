import Mathlib

/-!
# Reflected boundary memory

An algebraic boundary elimination is not automatically a dynamic closure.  This owner keeps the
changing chart `K` and its rate explicit, and derives the residual evolution from the supplied
interior and boundary rates.
-/

namespace Holonics.Physics.ReflectedBoundaryMemory

variable {𝕜 X Z : Type*} [Field 𝕜]
  [AddCommGroup X] [Module 𝕜 X]
  [AddCommGroup Z] [Module 𝕜 Z]

section Continuous

variable (A : X →ₗ[𝕜] X) (B : Z →ₗ[𝕜] X) (C : X →ₗ[𝕜] Z) (D : Z →ₗ[𝕜] Z)
  (K Kdot : X →ₗ[𝕜] Z) (x : X) (z r : Z) (f : X) (g : Z)

/-- The derivative of the reflected residual `r = z - K x`. -/
def residualDerivative (x : X) (dx : X) (dz : Z) : Z := dz - K dx - Kdot x

/-- Substituting the two supplied rates gives the complete residual equation. -/
theorem residualDerivative_eq
    (hr : r = z - K x) :
    residualDerivative K Kdot x (A x + B z + f) (C x + D z + g) =
      (D - K.comp B) r +
        (C + D.comp K - K.comp A - K.comp (B.comp K) - Kdot) x + g - K f := by
  have hz : z = r + K x := by
    rw [hr]
    simp only [sub_eq_add_neg]
    abel
  rw [hz]
  simp [residualDerivative, LinearMap.comp_apply, sub_eq_add_neg]
  abel_nf

/-- The rate identity with the declared rates named as state equations. -/
theorem reflectedResidual_rate
    (dx : X) (dz : Z)
    (hdx : dx = A x + B z + f) (hdz : dz = C x + D z + g)
    (hr : r = z - K x) :
    residualDerivative K Kdot x dx dz =
      (D - K.comp B) r +
        (C + D.comp K - K.comp A - K.comp (B.comp K) - Kdot) x + g - K f := by
  rw [hdx, hdz]
  exact residualDerivative_eq A B C D K Kdot x z r f g hr

end Continuous

section Discrete

variable (A : X →ₗ[𝕜] X) (B : Z →ₗ[𝕜] X) (C : X →ₗ[𝕜] Z) (D : Z →ₗ[𝕜] Z)
  (K Knext : X →ₗ[𝕜] Z) (x : X) (z r rnext : Z) (f : X) (g : Z)

/-- One changing-chart step, with the next chart used to measure the next residual. -/
theorem reflectedResidual_step
    (hr : r = z - K x) (hrnext : rnext = (C x + D z + g) - Knext (A x + B z + f)) :
    rnext = (D - Knext.comp B) r +
      (C + D.comp K - Knext.comp A - Knext.comp (B.comp K)) x + g - Knext f := by
  have hz : z = r + K x := by
    rw [hr]
    simp only [sub_eq_add_neg]
    abel
  rw [hrnext, hz]
  simp [LinearMap.comp_apply, sub_eq_add_neg]
  abel_nf

end Discrete

section BoundaryReduction

variable {Q : Type*} [AddCommGroup Q] [Module 𝕜 Q]

/-- A changing boundary encoding eliminates an arbitrary interior exactly when the boundary
action descends and the interior coupling is invisible in the next encoding. This is an operator
criterion, not an assertion that unmeasured circulation is absent or that its history is stored. -/
theorem boundary_reduction_iff
    (A : X →ₗ[𝕜] X) (B : Z →ₗ[𝕜] X)
    (E Enext : X →ₗ[𝕜] Q) (U : Q →ₗ[𝕜] Q) :
    (∀ x z, Enext (A x + B z) = U (E x)) ↔
      Enext.comp A = U.comp E ∧ Enext.comp B = 0 := by
  constructor
  · intro h
    constructor
    · ext x
      simpa using h x 0
    · ext z
      simpa using h 0 z
  · rintro ⟨hA, hB⟩ x z
    have hx := LinearMap.congr_fun hA x
    have hz := LinearMap.congr_fun hB z
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hx hz
    rw [map_add, hx, hz, add_zero]

/-- Boundary forcing is transported by the same next encoding. With these hypotheses at each
step, the reduced recurrence follows by induction, without expanding the interior trajectory. -/
theorem boundary_reduction_with_forcing
    (A : X →ₗ[𝕜] X) (B : Z →ₗ[𝕜] X)
    (E Enext : X →ₗ[𝕜] Q) (U : Q →ₗ[𝕜] Q)
    (hA : Enext.comp A = U.comp E) (hB : Enext.comp B = 0)
    (x : X) (z : Z) (f : X) :
    Enext (A x + B z + f) = U (E x) + Enext f := by
  rw [map_add, (boundary_reduction_iff A B E Enext U).mpr ⟨hA, hB⟩]

/-- In a moving continuous chart the encoder derivative participates in the dynamics. -/
theorem moving_boundary_rate
    (A : X →ₗ[𝕜] X) (B : Z →ₗ[𝕜] X)
    (E Edot : X →ₗ[𝕜] Q) (U : Q →ₗ[𝕜] Q)
    (hA : Edot + E.comp A = U.comp E) (hB : E.comp B = 0)
    (x : X) (z : Z) (f : X) :
    Edot x + E (A x + B z + f) = U (E x) + E f := by
  have hx := LinearMap.congr_fun hA x
  have hz := LinearMap.congr_fun hB z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hx hz
  simp only [map_add]
  rw [hz, add_zero, ← add_assoc, hx]

end BoundaryReduction

section Trajectory

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The residual rate above is the actual derivative of a changing boundary chart along a
differentiable trajectory. The chart-rate term is supplied by the product rule, not omitted
by treating a contemporary Schur map as constant. -/
theorem hasDerivAt_reflectedResidual
    (x : ℝ → U) (z : ℝ → V) (K : ℝ → U →L[ℝ] V)
    (time : ℝ) (dx : U) (dz : V) (Kdot : U →L[ℝ] V)
    (hx : HasDerivAt x dx time) (hz : HasDerivAt z dz time)
    (hK : HasDerivAt K Kdot time) :
    HasDerivAt (fun t ↦ z t - K t (x t))
      (dz - K time dx - Kdot (x time)) time := by
  have h := hz.sub (hK.clm_apply hx)
  have rate : dz - (Kdot (x time) + K time dx) = dz - K time dx - Kdot (x time) := by abel
  rw [rate] at h
  exact h

end Trajectory

section Counterexample

/-! A static Schur chart can vanish while its residual immediately moves. -/

def counterA : ℝ →ₗ[ℝ] ℝ := 0
def counterB : ℝ →ₗ[ℝ] ℝ := -LinearMap.id
def counterC : ℝ →ₗ[ℝ] ℝ := LinearMap.id
def counterD : ℝ →ₗ[ℝ] ℝ := -LinearMap.id
def counterK : ℝ →ₗ[ℝ] ℝ := LinearMap.id

theorem counterexample_static_interior_equilibrium :
    counterC + counterD.comp counterK = 0 := by
  simp [counterC, counterD, counterK]

/-- The coupled example is passive: its total quadratic energy loses z² at every state,
even though discarding its dynamically returning interior is incorrect. -/
theorem counterexample_energy_rate (x z : ℝ) :
    x * (counterA x + counterB z) + z * (counterC x + counterD z) = -(z ^ 2) := by
  simp only [counterA, counterB, counterC, counterD, LinearMap.zero_apply,
    LinearMap.neg_apply, LinearMap.id_apply]
  ring

theorem counterexample_residual_at_one :
    (1 : ℝ) - counterK 1 = 0 := by
  simp [counterK]

theorem counterexample_residual_derivative_at_one :
    (counterC 1 + counterD 1) - counterK (counterA 1 + counterB 1) = 1 := by
  norm_num [counterA, counterB, counterC, counterD, counterK]

theorem counterexample_energy_derivative_at_one :
    ((1 : ℝ) * (counterA 1 + counterB 1) +
      (1 : ℝ) * (counterC 1 + counterD 1)) = -1 := by
  norm_num [counterA, counterB, counterC, counterD]

end Counterexample

end Holonics.Physics.ReflectedBoundaryMemory
