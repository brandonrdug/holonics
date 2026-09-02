import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# The finite-dimensional Hodge decomposition

A differential `d` with `d ∘ d = 0` on a finite-dimensional real inner product space has the
codifferential `δ = d†`, the Laplacian `Δ = d δ + δ d`, and the harmonic space `ker Δ`.  The
theorem is the three-way orthogonal decomposition

```text
E = range d ⊕ range δ ⊕ ker Δ,      ker Δ = ker d ∩ ker δ,
```

and its cohomological reading: every closed element is a harmonic element plus an exact one, and
the harmonic representative is unique.  This is the exact linear-algebraic spine of the Hodge
decomposition: the receiver-visible balance (`Δ x = 0`) is exactly closed-and-coclosed, and the
class of every closed element has one balanced representative.
-/

noncomputable section

open InnerProductSpace

namespace Soma.Holonics.Millennium.HodgeFiniteDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A differential: a continuous linear map squaring to zero. -/
structure Differential (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  d : E →L[ℝ] E
  d_sq : d ∘L d = 0

namespace Differential

variable (D : Differential E)

/-- The codifferential: the adjoint of the differential. -/
def delta : E →L[ℝ] E := ContinuousLinearMap.adjoint D.d

/-- The Hodge Laplacian `Δ = d δ + δ d`. -/
def laplacian : E →L[ℝ] E := D.d ∘L D.delta + D.delta ∘L D.d

/-- The harmonic space `ker Δ`. -/
def harmonic : Submodule ℝ E := LinearMap.ker (D.laplacian : E →ₗ[ℝ] E)

omit [FiniteDimensional ℝ E] in
theorem d_sq_apply (x : E) : D.d (D.d x) = 0 := by
  have := congrArg (fun T : E →L[ℝ] E => T x) D.d_sq
  simpa using this

theorem delta_sq_apply (x : E) : D.delta (D.delta x) = 0 := by
  unfold delta
  have h : ContinuousLinearMap.adjoint D.d ∘L ContinuousLinearMap.adjoint D.d = 0 := by
    rw [← ContinuousLinearMap.adjoint_comp, D.d_sq, map_zero]
  have := congrArg (fun T : E →L[ℝ] E => T x) h
  simpa using this

theorem inner_d_left (x y : E) : ⟪D.d x, y⟫_ℝ = ⟪x, D.delta y⟫_ℝ := by
  unfold delta
  exact (ContinuousLinearMap.adjoint_inner_right D.d x y).symm

theorem inner_delta_left (x y : E) : ⟪D.delta x, y⟫_ℝ = ⟪x, D.d y⟫_ℝ := by
  unfold delta
  exact ContinuousLinearMap.adjoint_inner_left D.d y x

/-- **Harmonic is closed and coclosed.** -/
theorem mem_harmonic_iff (x : E) : x ∈ D.harmonic ↔ D.d x = 0 ∧ D.delta x = 0 := by
  constructor
  · intro h
    have h0 : D.laplacian x = 0 := h
    have e1 : ⟪D.d (D.delta x), x⟫_ℝ = ‖D.delta x‖ ^ 2 := by
      rw [inner_d_left, real_inner_self_eq_norm_sq]
    have e2 : ⟪D.delta (D.d x), x⟫_ℝ = ‖D.d x‖ ^ 2 := by
      rw [inner_delta_left, real_inner_self_eq_norm_sq]
    have hexp : ⟪D.laplacian x, x⟫_ℝ = ‖D.delta x‖ ^ 2 + ‖D.d x‖ ^ 2 := by
      have : D.laplacian x = D.d (D.delta x) + D.delta (D.d x) := rfl
      rw [this, inner_add_left, e1, e2]
    rw [h0, inner_zero_left] at hexp
    have h1 : ‖D.delta x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖D.delta x‖, sq_nonneg ‖D.d x‖]
    have h2 : ‖D.d x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖D.delta x‖, sq_nonneg ‖D.d x‖]
    exact ⟨norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2),
      norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)⟩
  · rintro ⟨hd, hδ⟩
    show D.laplacian x = 0
    simp [laplacian, hd, hδ]

/-! ## Orthogonality -/

theorem inner_range_d_range_delta {x y : E} (hx : x ∈ LinearMap.range (D.d : E →ₗ[ℝ] E))
    (hy : y ∈ LinearMap.range (D.delta : E →ₗ[ℝ] E)) : ⟪x, y⟫_ℝ = 0 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  show ⟪D.d a, D.delta b⟫_ℝ = 0
  rw [inner_d_left, delta_sq_apply, inner_zero_right]

theorem inner_harmonic_range_d {h x : E} (hh : h ∈ D.harmonic) (hx : x ∈ LinearMap.range (D.d : E →ₗ[ℝ] E)) :
    ⟪h, x⟫_ℝ = 0 := by
  obtain ⟨a, rfl⟩ := hx
  show ⟪h, D.d a⟫_ℝ = 0
  rw [real_inner_comm, inner_d_left, (D.mem_harmonic_iff h).mp hh |>.2, inner_zero_right]

theorem inner_harmonic_range_delta {h x : E} (hh : h ∈ D.harmonic)
    (hx : x ∈ LinearMap.range (D.delta : E →ₗ[ℝ] E)) : ⟪h, x⟫_ℝ = 0 := by
  obtain ⟨b, rfl⟩ := hx
  show ⟪h, D.delta b⟫_ℝ = 0
  rw [real_inner_comm, inner_delta_left, (D.mem_harmonic_iff h).mp hh |>.1, inner_zero_right]

/-- **The harmonic space is the orthogonal complement of `range d ⊔ range δ`.** -/
theorem harmonic_eq_orthogonal :
    D.harmonic = (LinearMap.range (D.d : E →ₗ[ℝ] E) ⊔ LinearMap.range (D.delta : E →ₗ[ℝ] E))ᗮ := by
  ext x
  rw [Submodule.mem_orthogonal]
  constructor
  · intro hx u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [inner_add_left, real_inner_comm, inner_harmonic_range_d D hx ha, real_inner_comm,
      inner_harmonic_range_delta D hx hb, add_zero]
  · intro hx
    rw [mem_harmonic_iff]
    constructor
    · have : ⟪D.d x, D.d x⟫_ℝ = 0 := by
        rw [inner_d_left, real_inner_comm]
        exact hx _ (Submodule.mem_sup_right ⟨D.d x, rfl⟩)
      exact inner_self_eq_zero.mp this
    · have : ⟪D.delta x, D.delta x⟫_ℝ = 0 := by
        rw [inner_delta_left, real_inner_comm]
        exact hx _ (Submodule.mem_sup_left ⟨D.delta x, rfl⟩)
      exact inner_self_eq_zero.mp this

/-- **The Hodge decomposition**: `E = range d ⊔ range δ ⊔ harmonic`. -/
theorem sup_eq_top : LinearMap.range (D.d : E →ₗ[ℝ] E) ⊔ LinearMap.range (D.delta : E →ₗ[ℝ] E) ⊔ D.harmonic = ⊤ := by
  rw [harmonic_eq_orthogonal]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- **Every closed element is harmonic plus exact.** -/
theorem exists_harmonic_add_exact {x : E} (hx : D.d x = 0) :
    ∃ h ∈ D.harmonic, ∃ a, x = h + D.d a := by
  have hmem : x ∈ LinearMap.range (D.d : E →ₗ[ℝ] E) ⊔ LinearMap.range (D.delta : E →ₗ[ℝ] E) ⊔ D.harmonic := by
    rw [sup_eq_top]; exact Submodule.mem_top
  obtain ⟨kl, hkl, h, hh, rfl⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨k, hk, l, hl, rfl⟩ := Submodule.mem_sup.mp hkl
  obtain ⟨a, rfl⟩ := hk
  obtain ⟨b, rfl⟩ := hl
  simp only [ContinuousLinearMap.coe_coe] at hx ⊢
  -- the coexact part vanishes
  have hdl : D.d (D.delta b) = 0 := by
    have h1 : D.d (D.d a + D.delta b + h) = D.d (D.delta b) := by
      simp only [map_add, d_sq_apply, (D.mem_harmonic_iff h).mp hh |>.1, zero_add, add_zero]
    rw [← h1, hx]
  have hl0 : D.delta b = 0 := by
    have : ⟪D.delta b, D.delta b⟫_ℝ = 0 := by rw [inner_delta_left, hdl, inner_zero_right]
    exact inner_self_eq_zero.mp this
  refine ⟨h, hh, a, ?_⟩
  rw [hl0]
  abel

/-- **The harmonic representative is unique**: harmonic and exact only at zero. -/
theorem harmonic_inf_range_d_eq_bot : D.harmonic ⊓ LinearMap.range (D.d : E →ₗ[ℝ] E) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h1 : x ∈ D.harmonic := hx.1
  have h2 : x ∈ LinearMap.range (D.d : E →ₗ[ℝ] E) := hx.2
  have : ⟪x, x⟫_ℝ = 0 := inner_harmonic_range_d D h1 h2
  exact inner_self_eq_zero.mp this

end Differential

section Audit

#print axioms Differential.mem_harmonic_iff
#print axioms Differential.sup_eq_top
#print axioms Differential.exists_harmonic_add_exact
#print axioms Differential.harmonic_inf_range_d_eq_bot

end Audit

end Soma.Holonics.Millennium.HodgeFiniteDecomposition
