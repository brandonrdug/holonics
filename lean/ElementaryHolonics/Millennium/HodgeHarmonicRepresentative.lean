import ElementaryHolonics.Millennium.HodgeFiniteDecomposition

/-!
# The harmonic representative: harmonic forms are the cohomology of a finite differential

For a finite-dimensional real inner product space with a differential `d` (`d ∘ d = 0`), the
closed forms are the harmonic forms plus the exact forms, and the two summands meet only at zero.
So the harmonic forms map isomorphically onto the cohomology `closed ⧸ exact`, and every class has
exactly one harmonic representative.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeFiniteDecomposition

namespace Differential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (D : Differential E)

/-- The closed forms. -/
def closed : Submodule ℝ E := LinearMap.ker (D.d : E →ₗ[ℝ] E)

/-- The exact forms. -/
def exact : Submodule ℝ E := LinearMap.range (D.d : E →ₗ[ℝ] E)

omit [FiniteDimensional ℝ E] in
theorem exact_le_closed : D.exact ≤ D.closed := by
  rintro x ⟨a, rfl⟩
  exact D.d_sq_apply a

theorem harmonic_le_closed : D.harmonic ≤ D.closed :=
  fun x hx => ((D.mem_harmonic_iff x).mp hx).1

theorem closed_eq_harmonic_sup_exact : D.closed = D.harmonic ⊔ D.exact := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h, hh, a, rfl⟩ := D.exists_harmonic_add_exact (LinearMap.mem_ker.mp hx)
    exact Submodule.add_mem_sup hh ⟨a, rfl⟩
  · exact sup_le D.harmonic_le_closed D.exact_le_closed

/-- The exact forms, read inside the closed forms. -/
def exactInClosed : Submodule ℝ D.closed := D.exact.comap D.closed.subtype

/-- The harmonic forms, read inside the closed forms. -/
def harmonicInClosed : Submodule ℝ D.closed := D.harmonic.comap D.closed.subtype

/-- The cohomology: closed forms modulo exact forms. -/
abbrev cohomology := D.closed ⧸ D.exactInClosed

theorem isCompl_harmonicInClosed_exactInClosed : IsCompl D.harmonicInClosed D.exactInClosed := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have hmem : (x : E) ∈ D.harmonic ⊓ LinearMap.range (D.d : E →ₗ[ℝ] E) := ⟨hx, hy⟩
    rw [D.harmonic_inf_range_d_eq_bot] at hmem
    exact Subtype.ext ((Submodule.mem_bot ℝ).mp hmem)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨h, hh, a, hx⟩ := D.exists_harmonic_add_exact (LinearMap.mem_ker.mp x.2)
    have hhc : h ∈ D.closed := D.harmonic_le_closed hh
    have hac : D.d a ∈ D.closed := D.exact_le_closed ⟨a, rfl⟩
    have hx' : x = (⟨h, hhc⟩ : D.closed) + ⟨D.d a, hac⟩ := Subtype.ext hx
    rw [hx']
    exact Submodule.add_mem_sup (Submodule.mem_comap.mpr hh) (Submodule.mem_comap.mpr ⟨a, rfl⟩)

/-- **Hodge isomorphism (inside the closed forms).** -/
def harmonicInClosedEquivCohomology : D.harmonicInClosed ≃ₗ[ℝ] D.cohomology :=
  (Submodule.quotientEquivOfIsCompl D.exactInClosed D.harmonicInClosed
    D.isCompl_harmonicInClosed_exactInClosed.symm).symm

/-- **Hodge isomorphism.** The harmonic forms are linearly equivalent to the cohomology. -/
def harmonicEquivCohomology : D.harmonic ≃ₗ[ℝ] D.cohomology :=
  (Submodule.comapSubtypeEquivOfLe D.harmonic_le_closed).symm.trans
    D.harmonicInClosedEquivCohomology

theorem finrank_harmonic_eq_finrank_cohomology :
    Module.finrank ℝ D.harmonic = Module.finrank ℝ D.cohomology :=
  D.harmonicEquivCohomology.finrank_eq

/-- **The unique harmonic receiver.** Every cohomology class has exactly one harmonic
representative. -/
theorem existsUnique_harmonic_representative (c : D.cohomology) :
    ∃! h : D.closed, h ∈ D.harmonicInClosed ∧ (Submodule.Quotient.mk h : D.cohomology) = c := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective D.exactInClosed c
  obtain ⟨h, hh, a, hx⟩ := D.exists_harmonic_add_exact (LinearMap.mem_ker.mp x.2)
  have hhc : h ∈ D.closed := D.harmonic_le_closed hh
  have hmk : (Submodule.Quotient.mk (⟨h, hhc⟩ : D.closed) : D.cohomology) =
      Submodule.Quotient.mk x := by
    rw [Submodule.Quotient.eq]
    refine Submodule.mem_comap.mpr ?_
    show h - (x : E) ∈ D.exact
    rw [hx]
    exact ⟨-a, by rw [map_neg, sub_add_cancel_left]; rfl⟩
  refine ⟨⟨h, hhc⟩, ⟨Submodule.mem_comap.mpr hh, hmk⟩, ?_⟩
  rintro h' ⟨hh', hq⟩
  have hdiff : h' - ⟨h, hhc⟩ ∈ D.exactInClosed := by
    rw [← Submodule.Quotient.eq, hq, hmk]
  have hmem : ((h' : E) - h) ∈ D.harmonic ⊓ LinearMap.range (D.d : E →ₗ[ℝ] E) :=
    ⟨D.harmonic.sub_mem hh' hh, hdiff⟩
  rw [D.harmonic_inf_range_d_eq_bot] at hmem
  exact Subtype.ext (sub_eq_zero.mp ((Submodule.mem_bot ℝ).mp hmem))

end Differential

section Audit

#print axioms Differential.isCompl_harmonicInClosed_exactInClosed
#print axioms Differential.finrank_harmonic_eq_finrank_cohomology
#print axioms Differential.existsUnique_harmonic_representative

end Audit

end Soma.Holonics.Millennium.HodgeFiniteDecomposition
