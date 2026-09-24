import ElementaryHolonics.Millennium.HodgeLeastNorm

/-!
# The Green operator: the Laplacian is invertible on the harmonic complement

The Laplacian `Δ = d δ + δ d` is self-adjoint, so it preserves the orthogonal complement of the
harmonic forms; there it is injective because its kernel is exactly the harmonic space, hence
bijective by finite dimension.  Every form is therefore a harmonic form plus a Laplacian of a form
in the harmonic complement: the Hodge--Green decomposition `x = H x + Δ G x`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeFiniteDecomposition

namespace Differential

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (D : Differential E)

/-- **The Laplacian is self-adjoint.** -/
theorem inner_laplacian_left (x y : E) : ⟪D.laplacian x, y⟫_ℝ = ⟪x, D.laplacian y⟫_ℝ := by
  have hx : D.laplacian x = D.d (D.delta x) + D.delta (D.d x) := rfl
  have hy : D.laplacian y = D.d (D.delta y) + D.delta (D.d y) := rfl
  rw [hx, hy, inner_add_left, inner_add_right, inner_d_left, inner_delta_left, inner_delta_left,
    inner_d_left]

/-- The range of the Laplacian lies in the harmonic complement. -/
theorem laplacian_mem_orthogonal (x : E) : D.laplacian x ∈ D.harmonicᗮ := by
  rw [Submodule.mem_orthogonal]
  intro h hh
  have hzero : D.laplacian h = 0 := LinearMap.mem_ker.mp hh
  rw [← D.inner_laplacian_left, hzero, inner_zero_left]

/-- The Laplacian restricted to the harmonic complement. -/
def laplacianRestrict : D.harmonicᗮ →ₗ[ℝ] D.harmonicᗮ :=
  LinearMap.restrict (D.laplacian : E →ₗ[ℝ] E) (fun x _ => D.laplacian_mem_orthogonal x)

theorem laplacianRestrict_apply (x : D.harmonicᗮ) :
    (D.laplacianRestrict x : E) = D.laplacian x := rfl

/-- **Injectivity on the harmonic complement.** -/
theorem laplacianRestrict_injective : Function.Injective D.laplacianRestrict := by
  intro x y hxy
  have h1 : D.laplacian x = D.laplacian y := by
    have := congrArg Subtype.val hxy
    rwa [laplacianRestrict_apply, laplacianRestrict_apply] at this
  have h : D.laplacian ((x : E) - y) = 0 := by
    rw [map_sub, h1, sub_self]
  have hmem : ((x : E) - y) ∈ D.harmonic ⊓ D.harmonicᗮ :=
    ⟨LinearMap.mem_ker.mpr h, D.harmonicᗮ.sub_mem x.2 y.2⟩
  rw [Submodule.inf_orthogonal_eq_bot] at hmem
  exact Subtype.ext (sub_eq_zero.mp ((Submodule.mem_bot ℝ).mp hmem))

/-- **Surjectivity on the harmonic complement**: the Green operator exists. -/
theorem exists_green {x : E} (hx : x ∈ D.harmonicᗮ) :
    ∃ y ∈ D.harmonicᗮ, D.laplacian y = x := by
  obtain ⟨y, hy⟩ :=
    LinearMap.injective_iff_surjective.mp D.laplacianRestrict_injective ⟨x, hx⟩
  refine ⟨y, y.2, ?_⟩
  have := congrArg Subtype.val hy
  rwa [laplacianRestrict_apply] at this

/-- **The Hodge--Green decomposition.** Every form is a harmonic form plus the Laplacian of a
form in the harmonic complement. -/
theorem exists_harmonic_add_laplacian (x : E) :
    ∃ h ∈ D.harmonic, ∃ y ∈ D.harmonicᗮ, x = h + D.laplacian y := by
  obtain ⟨h, hh, z, hz, hx⟩ := Submodule.exists_add_mem_mem_orthogonal (K := D.harmonic) x
  obtain ⟨y, hy, hyz⟩ := D.exists_green hz
  exact ⟨h, hh, y, hy, by rw [hx, hyz]⟩

end Differential

end Soma.Holonics.Millennium.HodgeFiniteDecomposition
