import ElementaryHolonics.Millennium.HodgeHarmonicRepresentative

/-!
# The harmonic representative is the least-norm member of its class

For a closed form `x = h + d a` with `h` harmonic, the two summands are orthogonal, so
`‖x‖² = ‖h‖² + ‖d a‖²`.  Hence the harmonic representative has the least norm in its cohomology
class, and it is the unique member with that norm.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeFiniteDecomposition

namespace Differential

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (D : Differential E)

/-- **Pythagoras across the Hodge splitting.** -/
theorem norm_sq_harmonic_add_exact {h a : E} (hh : h ∈ D.harmonic) :
    ‖h + D.d a‖ ^ 2 = ‖h‖ ^ 2 + ‖D.d a‖ ^ 2 := by
  have horth : ⟪h, D.d a⟫_ℝ = 0 := D.inner_harmonic_range_d hh ⟨a, rfl⟩
  rw [@norm_add_sq_real, horth]
  ring

/-- **Least norm.** Every member of the class of a harmonic form is at least as long. -/
theorem norm_harmonic_le {h a : E} (hh : h ∈ D.harmonic) : ‖h‖ ≤ ‖h + D.d a‖ := by
  have h1 := D.norm_sq_harmonic_add_exact (a := a) hh
  nlinarith [h1, norm_nonneg h, norm_nonneg (h + D.d a), sq_nonneg ‖D.d a‖]

/-- **Uniqueness of the least-norm member.** Equality of norms forces the exact part to vanish. -/
theorem eq_harmonic_of_norm_eq {h a : E} (hh : h ∈ D.harmonic) (heq : ‖h + D.d a‖ = ‖h‖) :
    D.d a = 0 := by
  have h1 := D.norm_sq_harmonic_add_exact (a := a) hh
  rw [heq] at h1
  have h2 : ‖D.d a‖ ^ 2 = 0 := by linarith
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

end Differential

end Soma.Holonics.Millennium.HodgeFiniteDecomposition
