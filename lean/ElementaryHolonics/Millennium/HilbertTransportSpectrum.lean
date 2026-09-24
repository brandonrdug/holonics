import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import ElementaryHolonics.Millennium.AlgebraicGNS
import ElementaryHolonics.Millennium.HilbertTransportChain
import ElementaryHolonics.Millennium.YangMillsLimit

/-!
# Spectrum of a finite Hilbert transport chain

This owner continues `HilbertTransportChain` without changing its chain or decomposition owner.
The middle Laplacian supplies a positive-semidefinite bilinear energy form.  Its radical is exactly
the harmonic population, so the existing algebraic GNS construction gives a positive-definite
energy form on the quotient by harmonic degeneracy.

The finite-dimensional spectral theorem then gives a finite, nonnegative spectrum.  When both the
harmonic and non-harmonic populations are nontrivial, zero is a spectral value and a positive
spectral value exists; finiteness separates the nonzero spectrum from zero.  This is an exact finite
`SpectrumHasMassGap` instance.  It deliberately does not assert a scale-uniform gap, a continuum
limit, a gauge-field Hamiltonian realization, or the quantum Yang--Mills mass gap.
-/

noncomputable section

open InnerProductSpace

namespace Soma.Holonics.Millennium.Coupling

universe u

variable {A B C : Type u}
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]

namespace HilbertTransportChain

variable (T : HilbertTransportChain A B C)

/-! ## The Laplacian energy form and its positive quotient -/

/-- The bilinear energy form induced by the middle Laplacian. -/
def laplacianEnergyForm : LinearMap.BilinForm ℝ B :=
  (innerₗ B).comp T.middleLaplacian.toLinearMap

@[simp]
theorem laplacianEnergyForm_apply (x y : B) :
    T.laplacianEnergyForm x y = inner ℝ (T.middleLaplacian x) y := rfl

/-- The energy form records exactly the squared incoming-adjoint and outgoing returns. -/
theorem laplacianEnergyForm_self (x : B) :
    T.laplacianEnergyForm x x =
      ‖T.incomingAdjoint x‖ ^ 2 + ‖T.outOf x‖ ^ 2 :=
  T.inner_middleLaplacian_self x

/-- The middle Laplacian is symmetric in Mathlib's linear-operator vocabulary. -/
theorem middleLaplacian_isSymmetric : T.middleLaplacian.toLinearMap.IsSymmetric := by
  intro x y
  calc
    inner ℝ (T.middleLaplacian x) y = inner ℝ x (T.middleLaplacian.adjoint y) :=
      (ContinuousLinearMap.adjoint_inner_right T.middleLaplacian x y).symm
    _ = inner ℝ x (T.middleLaplacian y) := by rw [T.middleLaplacian_adjoint]

/-- The Laplacian energy form is symmetric. -/
theorem laplacianEnergyForm_isSymm : T.laplacianEnergyForm.IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  change inner ℝ (T.middleLaplacian x) y = inner ℝ (T.middleLaplacian y) x
  calc
    inner ℝ (T.middleLaplacian x) y = inner ℝ x (T.middleLaplacian y) :=
      T.middleLaplacian_isSymmetric x y
    _ = inner ℝ (T.middleLaplacian y) x :=
      (real_inner_comm x (T.middleLaplacian y)).symm

/-- The Laplacian energy form is nonnegative on the diagonal. -/
theorem laplacianEnergyForm_nonnegative (x : B) :
    0 ≤ T.laplacianEnergyForm x x := by
  exact T.middleLaplacian_nonnegative x

/-- The radical of the energy form is exactly the harmonic population. -/
theorem laplacianEnergyForm_ker :
    LinearMap.ker T.laplacianEnergyForm = T.harmonic := by
  ext x
  rw [← T.middleLaplacian_ker]
  change T.laplacianEnergyForm x = 0 ↔ T.middleLaplacian x = 0
  constructor
  · intro hx
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hvalue := LinearMap.congr_fun hx (T.middleLaplacian x)
    exact hvalue
  · intro hx
    apply LinearMap.ext
    intro y
    simp [hx]

/-- The energy quotient removes precisely the Laplacian's harmonic degeneracy. -/
abbrev LaplacianEnergyQuotient :=
  B ⧸ LinearMap.ker T.laplacianEnergyForm

/-- The descended energy form on the quotient by its radical. -/
def quotientEnergyForm : LinearMap.BilinForm ℝ T.LaplacianEnergyQuotient :=
  AlgebraicGNS.gnsForm T.laplacianEnergyForm T.laplacianEnergyForm_isSymm

/-- The quotient energy form is positive definite. -/
theorem quotientEnergyForm_posDef :
    (LinearMap.BilinMap.toQuadraticMap T.quotientEnergyForm).PosDef := by
  exact AlgebraicGNS.theGnsFormIsPosDef T.laplacianEnergyForm
    T.laplacianEnergyForm_nonnegative T.laplacianEnergyForm_isSymm

/-- The quotient energy form is nondegenerate. -/
theorem quotientEnergyForm_nondegenerate : T.quotientEnergyForm.Nondegenerate := by
  exact AlgebraicGNS.theGnsFormIsNondegenerate T.laplacianEnergyForm
    T.laplacianEnergyForm_nonnegative T.laplacianEnergyForm_isSymm

/-- The middle Laplacian is a positive linear operator. -/
theorem middleLaplacian_isPositive : T.middleLaplacian.toLinearMap.IsPositive := by
  rw [LinearMap.isPositive_iff]
  exact ⟨T.middleLaplacian_isSymmetric, T.middleLaplacian_nonnegative⟩

/-! ## Finite nonnegative spectrum -/

/-- The real spectrum of the finite-dimensional middle Laplacian. -/
def middleSpectrum : Set ℝ :=
  spectrum ℝ T.middleLaplacian.toLinearMap

/-- The finite-dimensional middle spectrum is finite. -/
theorem middleSpectrum_finite : T.middleSpectrum.Finite :=
  Module.End.finite_spectrum T.middleLaplacian.toLinearMap

/-- Every spectral value of the positive middle Laplacian is nonnegative. -/
theorem middleSpectrum_nonnegative {μ : ℝ} (hμ : μ ∈ T.middleSpectrum) : 0 ≤ μ := by
  apply eigenvalue_nonneg_of_nonneg (Module.End.HasEigenvalue.of_mem_spectrum hμ)
  intro x
  exact T.middleLaplacian_isPositive.inner_nonneg_right x

/-- The zero eigenspace is exactly the harmonic population. -/
theorem middleLaplacian_eigenspace_zero :
    Module.End.eigenspace T.middleLaplacian.toLinearMap 0 = T.harmonic := by
  rw [Module.End.eigenspace_zero]
  exact T.middleLaplacian_ker

/-- Zero is spectral exactly when the harmonic population is nontrivial. -/
theorem zero_mem_middleSpectrum_iff :
    0 ∈ T.middleSpectrum ↔ T.harmonic ≠ ⊥ := by
  rw [middleSpectrum, ← Module.End.hasEigenvalue_iff_mem_spectrum]
  change Module.End.eigenspace T.middleLaplacian.toLinearMap 0 ≠ ⊥ ↔ T.harmonic ≠ ⊥
  rw [T.middleLaplacian_eigenspace_zero]

/-- A nontrivial non-harmonic population forces the positive middle Laplacian to be nonzero. -/
theorem middleLaplacian_ne_zero_of_nonharmonic_ne_bot
    (hnonharmonic : T.nonharmonic ≠ ⊥) : T.middleLaplacian.toLinearMap ≠ 0 := by
  have hharmonic_ne_top : T.harmonic ≠ ⊤ :=
    T.nonharmonic_isCompl_harmonic.disjoint.ne_top_of_ne_bot hnonharmonic
  intro hzero
  apply hharmonic_ne_top
  rw [← T.middleLaplacian_ker]
  have hzero' : T.middleLaplacian = 0 := by
    ext x
    exact LinearMap.congr_fun hzero x
  rw [hzero']
  simp

/-- A nonzero positive self-adjoint middle Laplacian has a strictly positive eigenvalue. -/
theorem exists_positive_middleSpectrum
    (hnonharmonic : T.nonharmonic ≠ ⊥) : ∃ μ ∈ T.middleSpectrum, 0 < μ := by
  let hpositive := T.middleLaplacian_isPositive
  let hsymm := T.middleLaplacian_isSymmetric
  have hne : T.middleLaplacian.toLinearMap ≠ 0 :=
    T.middleLaplacian_ne_zero_of_nonharmonic_ne_bot hnonharmonic
  have hexists :
      ∃ i : Fin (Module.finrank ℝ B), hsymm.eigenvalues rfl i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    apply LinearMap.ext
    intro x
    apply (hsymm.eigenvectorBasis rfl).repr.injective
    ext i
    rw [hsymm.eigenvectorBasis_apply_self_apply]
    simp [h i]
  obtain ⟨i, hi⟩ := hexists
  refine ⟨hsymm.eigenvalues rfl i, ?_, ?_⟩
  · exact (hsymm.hasEigenvalue_eigenvalues rfl i).mem_spectrum
  · exact lt_of_le_of_ne (hpositive.nonneg_eigenvalues rfl i) hi.symm

/-! ## Exact finite mass gap -/

/-- A finite nonnegative spectrum containing a vacuum and a positive excitation has a positive
separator.  This is the exact finite-set fact used by the middle Laplacian instance below. -/
theorem finiteSpectrum_hasMassGap
    {s : Set ℝ} (hfinite : s.Finite) (hzero : 0 ∈ s)
    (hnonnegative : ∀ μ ∈ s, 0 ≤ μ) (hpositive : ∃ μ ∈ s, 0 < μ) :
    YangMillsLimit.SpectrumHasMassGap s := by
  let nonzero : Finset ℝ := hfinite.toFinset.filter fun μ ↦ μ ≠ 0
  have hnonempty : nonzero.Nonempty := by
    obtain ⟨μ, hμs, hμpos⟩ := hpositive
    refine ⟨μ, ?_⟩
    simp [nonzero, hμs, hμpos.ne']
  let Δ := nonzero.min' hnonempty
  have hΔmem : Δ ∈ nonzero := Finset.min'_mem nonzero hnonempty
  have hΔs : Δ ∈ s := by
    exact hfinite.mem_toFinset.mp (Finset.mem_filter.mp hΔmem).1
  have hΔne : Δ ≠ 0 := (Finset.mem_filter.mp hΔmem).2
  have hΔpos : 0 < Δ := lt_of_le_of_ne (hnonnegative Δ hΔs) hΔne.symm
  refine ⟨hzero, hnonnegative, hpositive, Δ, hΔpos, ?_⟩
  intro μ hμs
  by_cases hμzero : μ = 0
  · exact Or.inl hμzero
  · right
    apply Finset.min'_le
    simp [nonzero, hμs, hμzero]

/-- **Finite middle-Laplacian mass gap.**  If harmonic zero modes and non-harmonic modes are
both present, the finite-dimensional spectrum satisfies the repository's spectral mass-gap
predicate. -/
theorem middleSpectrum_hasMassGap
    (hharmonic : T.harmonic ≠ ⊥) (hnonharmonic : T.nonharmonic ≠ ⊥) :
    YangMillsLimit.SpectrumHasMassGap T.middleSpectrum := by
  apply finiteSpectrum_hasMassGap T.middleSpectrum_finite
  · exact T.zero_mem_middleSpectrum_iff.mpr hharmonic
  · intro μ hμ
    exact T.middleSpectrum_nonnegative hμ
  · exact T.exists_positive_middleSpectrum hnonharmonic

section Audit

#print axioms laplacianEnergyForm_ker
#print axioms laplacianEnergyForm_self
#print axioms quotientEnergyForm_posDef
#print axioms quotientEnergyForm_nondegenerate
#print axioms middleLaplacian_isPositive
#print axioms middleSpectrum_finite
#print axioms middleSpectrum_nonnegative
#print axioms zero_mem_middleSpectrum_iff
#print axioms exists_positive_middleSpectrum
#print axioms finiteSpectrum_hasMassGap
#print axioms middleSpectrum_hasMassGap

end Audit

end HilbertTransportChain

end Soma.Holonics.Millennium.Coupling
