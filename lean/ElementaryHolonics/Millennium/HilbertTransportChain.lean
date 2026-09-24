import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import ElementaryHolonics.Millennium.Coupling

/-!
# A finite-dimensional Hilbert enrichment of the transport chain

`Coupling.TransportChain` retains the additive incidence of two consecutive transports

```text
A --into--> B --outOf--> C,       outOf (into a) = 0.
```

This file equips the same occurrence with continuous real-linear maps between finite-dimensional
Hilbert spaces.  It therefore has actual adjoints and a middle Hodge Laplacian

```text
into ∘ into† + outOf† ∘ outOf : B → B.
```

The energy identity proves that the Laplacian loses exactly the population which is simultaneously
closed under `outOf` and coclosed under `into†`.  This is the shared finite-dimensional spine for
later discrete de Rham, Leray, and linearized gauge instances.  It does not assert a continuum
Hodge decomposition, closed range in an infinite-dimensional function space, the Hodge conjecture,
or a Yang--Mills mass gap.
-/

noncomputable section

open InnerProductSpace

namespace Soma.Holonics.Millennium.Coupling

universe u

variable {A B C : Type u}
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]

/-- A continuous real-linear enrichment of `TransportChain` on finite-dimensional Hilbert
carriers.  The composite-zero law retains the same addressed incidence as the additive owner. -/
structure HilbertTransportChain (A B C : Type u)
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C] where
  /-- The incoming continuous-linear transport. -/
  into : A →L[ℝ] B
  /-- The outgoing continuous-linear transport. -/
  outOf : B →L[ℝ] C
  /-- The boundary-of-boundary law at every addressed source occurrence. -/
  composite_zero : ∀ a, outOf (into a) = 0

namespace HilbertTransportChain

variable (T : HilbertTransportChain A B C)

/-- Forget norms and scalar transport to recover the repository's original additive chain
exactly. -/
def toTransportChain : TransportChain A B C where
  into := T.into.toLinearMap.toAddMonoidHom
  outOf := T.outOf.toLinearMap.toAddMonoidHom
  composite_zero := T.composite_zero

@[simp]
theorem toTransportChain_into (a : A) : T.toTransportChain.into a = T.into a := rfl

@[simp]
theorem toTransportChain_outOf (b : B) : T.toTransportChain.outOf b = T.outOf b := rfl

/-- The continuous-linear form of the chain law. -/
theorem outOf_comp_into : T.outOf.comp T.into = 0 := by
  ext a
  exact T.composite_zero a

/-- The incoming codifferential at the middle carrier. -/
def incomingAdjoint : B →L[ℝ] A :=
  T.into.adjoint

/-- The outgoing adjoint returning from the target carrier. -/
def outgoingAdjoint : C →L[ℝ] B :=
  T.outOf.adjoint

/-- The middle Hodge Laplacian `d₋ d₋† + d₊† d₊`. -/
def middleLaplacian : B →L[ℝ] B :=
  T.into.comp T.incomingAdjoint + T.outgoingAdjoint.comp T.outOf

/-- The harmonic population at the middle: outgoing-closed and incoming-coclosed. -/
def harmonic : Submodule ℝ B :=
  T.outOf.ker ⊓ T.incomingAdjoint.ker

/-- The exact middle population, transported in from the preceding carrier. -/
def exact : Submodule ℝ B :=
  T.into.range

/-- The coexact middle population, returned by the outgoing adjoint. -/
def coexact : Submodule ℝ B :=
  T.outgoingAdjoint.range

/-- The non-harmonic middle population generated jointly by exact and coexact transport. -/
def nonharmonic : Submodule ℝ B :=
  T.exact ⊔ T.coexact

/-- The middle Hodge Laplacian is self-adjoint. -/
theorem middleLaplacian_adjoint : T.middleLaplacian.adjoint = T.middleLaplacian := by
  simp [middleLaplacian, incomingAdjoint, outgoingAdjoint]

/-- **Middle Hodge energy identity.**  The Laplacian's quadratic reading is exactly the sum of
the squared incoming-adjoint and outgoing returns. -/
theorem inner_middleLaplacian_self (x : B) :
    ⟪T.middleLaplacian x, x⟫_ℝ =
      ‖T.incomingAdjoint x‖ ^ 2 + ‖T.outOf x‖ ^ 2 := by
  change
    ⟪T.into (T.into.adjoint x) + T.outOf.adjoint (T.outOf x), x⟫_ℝ =
      ‖T.into.adjoint x‖ ^ 2 + ‖T.outOf x‖ ^ 2
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.adjoint_inner_right]
  simp only [real_inner_self_eq_norm_sq]

/-- The middle Laplacian is positive semidefinite at every occurrence. -/
theorem middleLaplacian_nonnegative (x : B) :
    0 ≤ ⟪T.middleLaplacian x, x⟫_ℝ := by
  rw [T.inner_middleLaplacian_self]
  positivity

/-- **Kernel characterization.**  A middle occurrence is killed by the Hodge Laplacian exactly
when both its outgoing differential and incoming codifferential vanish. -/
theorem middleLaplacian_apply_eq_zero_iff (x : B) :
    T.middleLaplacian x = 0 ↔
      T.incomingAdjoint x = 0 ∧ T.outOf x = 0 := by
  constructor
  · intro hx
    have henergy := T.inner_middleLaplacian_self x
    rw [hx, inner_zero_left] at henergy
    have hincomingNorm : ‖T.incomingAdjoint x‖ = 0 := by
      nlinarith [sq_nonneg ‖T.incomingAdjoint x‖, sq_nonneg ‖T.outOf x‖]
    have houtgoingNorm : ‖T.outOf x‖ = 0 := by
      nlinarith [sq_nonneg ‖T.incomingAdjoint x‖, sq_nonneg ‖T.outOf x‖]
    exact ⟨norm_eq_zero.mp hincomingNorm, norm_eq_zero.mp houtgoingNorm⟩
  · rintro ⟨hincoming, houtgoing⟩
    change T.into (T.into.adjoint x) + T.outOf.adjoint (T.outOf x) = 0
    change T.into.adjoint x = 0 at hincoming
    rw [hincoming, houtgoing, map_zero, map_zero, add_zero]

/-- The kernel of the middle Laplacian is exactly the harmonic population. -/
theorem middleLaplacian_ker : T.middleLaplacian.ker = T.harmonic := by
  ext x
  change T.middleLaplacian x = 0 ↔ x ∈ T.harmonic
  rw [T.middleLaplacian_apply_eq_zero_iff]
  simp [harmonic, incomingAdjoint, and_comm]

/-- Every exact occurrence is orthogonal to every harmonic occurrence. -/
theorem inner_into_harmonic_eq_zero (a : A) {h : B} (hh : h ∈ T.harmonic) :
    ⟪T.into a, h⟫_ℝ = 0 := by
  have hcoclosed : T.incomingAdjoint h = 0 := hh.2
  calc
    ⟪T.into a, h⟫_ℝ = ⟪a, T.incomingAdjoint h⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_right T.into a h).symm
    _ = 0 := by rw [hcoclosed, inner_zero_right]

/-- Every coexact occurrence is orthogonal to every harmonic occurrence. -/
theorem inner_outgoingAdjoint_harmonic_eq_zero (c : C) {h : B} (hh : h ∈ T.harmonic) :
    ⟪T.outgoingAdjoint c, h⟫_ℝ = 0 := by
  have hclosed : T.outOf h = 0 := hh.1
  change ⟪T.outOf.adjoint c, h⟫_ℝ = 0
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [hclosed]

/-- The exact and coexact populations are mutually orthogonal.  This is the Hilbert-space reading
of the retained boundary-of-boundary law. -/
theorem inner_into_outgoingAdjoint_eq_zero (a : A) (c : C) :
    ⟪T.into a, T.outgoingAdjoint c⟫_ℝ = 0 := by
  calc
    ⟪T.into a, T.outgoingAdjoint c⟫_ℝ = ⟪T.outOf (T.into a), c⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_right T.outOf (T.into a) c
    _ = 0 := by rw [T.composite_zero, inner_zero_left]

/-- The submodule-level exact--harmonic orthogonality law. -/
theorem inner_exact_harmonic_eq_zero {e h : B} (he : e ∈ T.exact) (hh : h ∈ T.harmonic) :
    inner ℝ e h = 0 := by
  obtain ⟨a, rfl⟩ := he
  exact T.inner_into_harmonic_eq_zero a hh

/-- The submodule-level coexact--harmonic orthogonality law. -/
theorem inner_coexact_harmonic_eq_zero {c h : B} (hc : c ∈ T.coexact) (hh : h ∈ T.harmonic) :
    inner ℝ c h = 0 := by
  obtain ⟨z, rfl⟩ := hc
  exact T.inner_outgoingAdjoint_harmonic_eq_zero z hh

/-- The submodule-level exact--coexact orthogonality law. -/
theorem inner_exact_coexact_eq_zero {e c : B} (he : e ∈ T.exact) (hc : c ∈ T.coexact) :
    inner ℝ e c = 0 := by
  obtain ⟨a, rfl⟩ := he
  obtain ⟨z, rfl⟩ := hc
  exact T.inner_into_outgoingAdjoint_eq_zero a z

/-- Harmonic occurrences are exactly the orthogonal complement of the jointly exact and coexact
population. -/
theorem harmonic_eq_nonharmonic_orthogonal : T.harmonic = T.nonharmonicᗮ := by
  rw [nonharmonic, exact, coexact, ← Submodule.inf_orthogonal]
  simp only [ContinuousLinearMap.orthogonal_range]
  simp [harmonic, incomingAdjoint, outgoingAdjoint, inf_comm]

/-- The jointly exact/coexact population and the harmonic population are complementary. -/
theorem nonharmonic_isCompl_harmonic : IsCompl T.nonharmonic T.harmonic := by
  rw [T.harmonic_eq_nonharmonic_orthogonal]
  exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

/-- The exact, harmonic, and coexact populations span the complete middle carrier. -/
theorem exact_sup_harmonic_sup_coexact_eq_top :
    T.exact ⊔ T.harmonic ⊔ T.coexact = ⊤ := by
  calc
    T.exact ⊔ T.harmonic ⊔ T.coexact = T.nonharmonic ⊔ T.harmonic := by
      rw [nonharmonic]
      ac_rfl
    _ = ⊤ := T.nonharmonic_isCompl_harmonic.sup_eq_top

/-- Exact and coexact populations meet only at zero. -/
theorem exact_disjoint_coexact : Disjoint T.exact T.coexact := by
  rw [Submodule.disjoint_def]
  intro x hxExact hxCoexact
  exact inner_self_eq_zero.mp (T.inner_exact_coexact_eq_zero hxExact hxCoexact)

/-- **Finite-dimensional Hodge decomposition.**  Every middle occurrence is the sum of an exact,
harmonic, and coexact occurrence. -/
theorem exists_hodge_decomposition (x : B) :
    ∃ e h c : B,
      e ∈ T.exact ∧ h ∈ T.harmonic ∧ c ∈ T.coexact ∧ x = e + h + c := by
  obtain ⟨n, h, hn, hh, hnh⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.mp T.nonharmonic_isCompl_harmonic.codisjoint x
  obtain ⟨e, he, c, hc, hec⟩ := Submodule.mem_sup.mp hn
  refine ⟨e, h, c, he, hh, hc, ?_⟩
  rw [← hnh, ← hec]
  abel

/-- **Uniqueness of the finite-dimensional Hodge decomposition.**  Any two exact--harmonic--
coexact presentations of the same occurrence agree componentwise. -/
theorem hodge_decomposition_unique
    {e h c e' h' c' : B}
    (he : e ∈ T.exact) (hh : h ∈ T.harmonic) (hc : c ∈ T.coexact)
    (he' : e' ∈ T.exact) (hh' : h' ∈ T.harmonic) (hc' : c' ∈ T.coexact)
    (hsum : e + h + c = e' + h' + c') :
    e = e' ∧ h = h' ∧ c = c' := by
  have hec_mem : e + c ∈ T.nonharmonic := by
    exact Submodule.add_mem_sup he hc
  have hec_mem' : e' + c' ∈ T.nonharmonic := by
    exact Submodule.add_mem_sup he' hc'
  obtain ⟨n, k, hnk, hunique⟩ :=
    Submodule.existsUnique_add_of_isCompl T.nonharmonic_isCompl_harmonic (e + h + c)
  have hfirst := hunique ⟨e + c, hec_mem⟩ ⟨h, hh⟩ (by
    change (e + c) + h = e + h + c
    abel)
  have hsecond := hunique ⟨e' + c', hec_mem'⟩ ⟨h', hh'⟩ (by
    change (e' + c') + h' = e + h + c
    rw [hsum]
    abel)
  have hec_eq : e + c = e' + c' := by
    exact congrArg Subtype.val (hfirst.1.trans hsecond.1.symm)
  have hhq : h = h' := by
    exact congrArg Subtype.val (hfirst.2.trans hsecond.2.symm)
  have he_difference : e - e' = c' - c := by
    calc
      e - e' = (e + c) - (e' + c') + (c' - c) := by abel
      _ = c' - c := by rw [hec_eq, sub_self, zero_add]
  have he_difference_exact : e - e' ∈ T.exact := T.exact.sub_mem he he'
  have he_difference_coexact : e - e' ∈ T.coexact := by
    rw [he_difference]
    exact T.coexact.sub_mem hc' hc
  have heq : e = e' := by
    apply sub_eq_zero.mp
    exact (Submodule.disjoint_def.mp T.exact_disjoint_coexact)
      (e - e') he_difference_exact he_difference_coexact
  have hcq : c = c' := by
    rw [heq] at hec_eq
    exact add_left_cancel hec_eq
  exact ⟨heq, hhq, hcq⟩

/-- A coexact occurrence which is also outgoing-closed is zero. -/
theorem eq_zero_of_mem_coexact_of_outOf_eq_zero {c : B}
    (hc : c ∈ T.coexact) (hclosed : T.outOf c = 0) : c = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  obtain ⟨z, rfl⟩ := hc
  change T.outOf (T.outOf.adjoint z) = 0 at hclosed
  change inner ℝ (T.outOf.adjoint z) (T.outOf.adjoint z) = 0
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [hclosed, inner_zero_right]

/-- Every outgoing-closed occurrence has an exact plus harmonic presentation.  This is the
representative theorem underlying finite-dimensional chain homology, stated without founding a
second quotient owner. -/
theorem exists_exact_harmonic_of_outOf_eq_zero {x : B} (hx : T.outOf x = 0) :
    ∃ e h : B, e ∈ T.exact ∧ h ∈ T.harmonic ∧ x = e + h := by
  obtain ⟨e, h, c, he, hh, hc, hxsum⟩ := T.exists_hodge_decomposition x
  have heclosed : T.outOf e = 0 := by
    obtain ⟨a, rfl⟩ := he
    exact T.composite_zero a
  have hhclosed : T.outOf h = 0 := hh.1
  have hcclosed : T.outOf c = 0 := by
    calc
      T.outOf c = T.outOf (e + h + c) := by simp [heclosed, hhclosed]
      _ = T.outOf x := congrArg T.outOf hxsum.symm
      _ = 0 := hx
  have hczero := T.eq_zero_of_mem_coexact_of_outOf_eq_zero hc hcclosed
  exact ⟨e, h, he, hh, by simpa [hczero] using hxsum⟩

/-- The exact plus harmonic presentation of a closed occurrence is unique. -/
theorem exact_harmonic_decomposition_unique
    {e h e' h' : B}
    (he : e ∈ T.exact) (hh : h ∈ T.harmonic)
    (he' : e' ∈ T.exact) (hh' : h' ∈ T.harmonic)
    (hsum : e + h = e' + h') : e = e' ∧ h = h' := by
  obtain ⟨heq, hhq, -⟩ := T.hodge_decomposition_unique
    he hh T.coexact.zero_mem he' hh' T.coexact.zero_mem (by simpa using hsum)
  exact ⟨heq, hhq⟩

section Audit

#print axioms inner_middleLaplacian_self
#print axioms middleLaplacian_adjoint
#print axioms middleLaplacian_apply_eq_zero_iff
#print axioms middleLaplacian_ker
#print axioms inner_into_harmonic_eq_zero
#print axioms inner_outgoingAdjoint_harmonic_eq_zero
#print axioms inner_into_outgoingAdjoint_eq_zero
#print axioms harmonic_eq_nonharmonic_orthogonal
#print axioms exact_sup_harmonic_sup_coexact_eq_top
#print axioms exists_hodge_decomposition
#print axioms hodge_decomposition_unique
#print axioms exists_exact_harmonic_of_outOf_eq_zero
#print axioms exact_harmonic_decomposition_unique

end Audit

end HilbertTransportChain

end Soma.Holonics.Millennium.Coupling
