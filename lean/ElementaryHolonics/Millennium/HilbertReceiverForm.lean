import ElementaryHolonics.Millennium.HilbertTransportSpectrum
import ElementaryHolonics.Millennium.MillenniumCoupling

/-!
# The Hilbert transport Laplacian as a receiver form

This file joins two existing owners without changing either of them:

* `HilbertTransportChain` owns the finite Hilbert chain, its Hodge decomposition, middle
  Laplacian, energy form, harmonic kernel, and finite spectrum;
* `MillenniumCoupling.ReceiverForm` owns positivity, definiteness, coercivity, null populations,
  and transport of quantitative lower bounds.

The middle Laplacian is installed as an actual receiver form.  Its null population is proved to
be exactly the harmonic population.  Consequently the global receiver is coercive exactly when
there is no harmonic kernel.  When harmonic vectors are retained as vacuum states, coercivity
instead lives on the orthogonal non-harmonic complement; the compressed receiver there is always
positive definite and, in this finite-dimensional owner, coercive.

The final theorem pairs that complement coercivity with the existing finite spectral mass-gap
receipt.  It does not identify the chain with a gauge-field complex or Hamiltonian, and it does
not supply a scale-uniform continuum gap.
-/

noncomputable section

open InnerProductSpace

namespace Soma.Holonics.Millennium.Coupling

open Soma.Holonics.Millennium.MillenniumCoupling
open Soma.Holonics.Millennium.MillenniumCoupling.ReceiverForm

universe u

variable {A B C : Type u}
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]

namespace HilbertTransportChain

variable (T : HilbertTransportChain A B C)

/-! ## The global Laplacian receiver -/

/-- The actual middle Laplacian, read through the shared receiver-form owner. -/
def laplacianReceiverForm : ReceiverForm B where
  T := T.middleLaplacian
  selfAdjoint := T.middleLaplacian_isSymmetric

/-- The receiver reading is definitionally the Laplacian energy form. -/
@[simp]
theorem laplacianReceiverForm_reading (x y : B) :
    T.laplacianReceiverForm.B x y = T.laplacianEnergyForm x y := rfl

/-- The Laplacian receiver is positive semidefinite. -/
theorem laplacianReceiverForm_isPositive : T.laplacianReceiverForm.IsPositive := by
  intro x
  exact T.laplacianEnergyForm_nonnegative x

/-- The receiver's diagonal null population is exactly the harmonic population. -/
theorem laplacianReceiverForm_nullCone :
    T.laplacianReceiverForm.nullCone = (T.harmonic : Set B) := by
  ext x
  change T.laplacianEnergyForm x x = 0 ↔ x ∈ T.harmonic
  constructor
  · intro hx
    have hsum : ‖T.incomingAdjoint x‖ ^ 2 + ‖T.outOf x‖ ^ 2 = 0 := by
      rw [← T.laplacianEnergyForm_self]
      exact hx
    have hincomingNorm : ‖T.incomingAdjoint x‖ = 0 := by
      nlinarith [sq_nonneg ‖T.incomingAdjoint x‖, sq_nonneg ‖T.outOf x‖]
    have houtgoingNorm : ‖T.outOf x‖ = 0 := by
      nlinarith [sq_nonneg ‖T.incomingAdjoint x‖, sq_nonneg ‖T.outOf x‖]
    change T.outOf x = 0 ∧ T.incomingAdjoint x = 0
    exact ⟨norm_eq_zero.mp houtgoingNorm, norm_eq_zero.mp hincomingNorm⟩
  · intro hx
    change T.outOf x = 0 ∧ T.incomingAdjoint x = 0 at hx
    rw [T.laplacianEnergyForm_self, hx.1, hx.2]
    simp

/-- The global Laplacian receiver is definite exactly when its harmonic kernel is trivial. -/
theorem laplacianReceiverForm_isDefinite_iff :
    T.laplacianReceiverForm.IsDefinite ↔ T.harmonic = ⊥ := by
  constructor
  · intro hdef
    apply T.harmonic.eq_bot_iff.mpr
    intro x hx
    apply hdef x
    have hnull : x ∈ T.laplacianReceiverForm.nullCone := by
      rw [T.laplacianReceiverForm_nullCone]
      exact hx
    exact hnull
  · intro hharmonic x hx
    have hnull : x ∈ T.laplacianReceiverForm.nullCone := hx
    have hxharmonic : x ∈ T.harmonic :=
      (Set.ext_iff.mp T.laplacianReceiverForm_nullCone x).mp hnull
    rw [hharmonic] at hxharmonic
    exact (Submodule.mem_bot ℝ).mp hxharmonic

/-- In finite dimensions, the global receiver is coercive exactly when the harmonic kernel is
trivial.  In particular, a retained nonzero harmonic vacuum prevents a global gap. -/
theorem laplacianReceiverForm_isCoercive_iff :
    T.laplacianReceiverForm.IsCoercive ↔ T.harmonic = ⊥ := by
  constructor
  · intro hgap
    exact T.laplacianReceiverForm_isDefinite_iff.mp
      (T.laplacianReceiverForm.theGapForcesDefiniteness hgap)
  · intro hharmonic
    exact T.laplacianReceiverForm.theGapIsFreeInFiniteDimensions
      T.laplacianReceiverForm_isPositive
      (T.laplacianReceiverForm_isDefinite_iff.mpr hharmonic)

/-- A nontrivial harmonic vacuum rules out coercivity on the complete middle carrier. -/
theorem laplacianReceiverForm_not_coercive_of_harmonic_ne_bot
    (hharmonic : T.harmonic ≠ ⊥) : ¬ T.laplacianReceiverForm.IsCoercive := by
  intro hgap
  exact hharmonic (T.laplacianReceiverForm_isCoercive_iff.mp hgap)

/-! ## Compression to the non-harmonic complement -/

/-- The Laplacian receiver compressed to the exact-plus-coexact, hence non-harmonic, population.
Orthogonal projection is used only to return the operator to the subtype; its pairing against a
non-harmonic vector is exactly the original Laplacian energy pairing. -/
def nonharmonicReceiverForm : ReceiverForm T.nonharmonic where
  T := T.nonharmonic.orthogonalProjection.comp
    (T.middleLaplacian.comp T.nonharmonic.subtypeL)
  selfAdjoint := by
    have hpositive : T.middleLaplacian.IsPositive :=
      (ContinuousLinearMap.isPositive_toLinearMap_iff T.middleLaplacian).mp
        T.middleLaplacian_isPositive
    exact (hpositive.orthogonalProjection_comp T.nonharmonic).isSymmetric

/-- Compression does not change the Laplacian reading on non-harmonic vectors. -/
@[simp]
theorem nonharmonicReceiverForm_reading (x y : T.nonharmonic) :
    T.nonharmonicReceiverForm.B x y =
      T.laplacianEnergyForm (x : B) (y : B) := by
  change inner ℝ
      (T.nonharmonic.orthogonalProjection (T.middleLaplacian (x : B))) y =
    inner ℝ (T.middleLaplacian (x : B)) (y : B)
  exact T.nonharmonic.inner_orthogonalProjection_eq_of_mem_right y
    (T.middleLaplacian (x : B))

/-- The compressed receiver remains positive. -/
theorem nonharmonicReceiverForm_isPositive : T.nonharmonicReceiverForm.IsPositive := by
  intro x
  rw [T.nonharmonicReceiverForm_reading]
  exact T.middleLaplacian_nonnegative (x : B)

/-- Removing the harmonic population makes the Laplacian receiver definite. -/
theorem nonharmonicReceiverForm_isDefinite : T.nonharmonicReceiverForm.IsDefinite := by
  intro x hx
  have hglobal : (x : B) ∈ T.laplacianReceiverForm.nullCone := by
    change T.laplacianReceiverForm.B (x : B) (x : B) = 0
    simpa using hx
  have hxharmonic : (x : B) ∈ T.harmonic :=
    (Set.ext_iff.mp T.laplacianReceiverForm_nullCone (x : B)).mp hglobal
  have hxzero : (x : B) = 0 :=
    (Submodule.disjoint_def.mp T.nonharmonic_isCompl_harmonic.disjoint)
      (x : B) x.property hxharmonic
  apply Subtype.ext
  exact hxzero

/-- **Finite complement gap.**  The positive definite Laplacian receiver on the non-harmonic
population is coercive. -/
theorem nonharmonicReceiverForm_isCoercive : T.nonharmonicReceiverForm.IsCoercive :=
  T.nonharmonicReceiverForm.theGapIsFreeInFiniteDimensions
    T.nonharmonicReceiverForm_isPositive T.nonharmonicReceiverForm_isDefinite

/-- When both vacuum and excited populations are present, complement coercivity and the existing
finite spectral mass-gap receipt hold simultaneously.  This is a finite-dimensional statement;
it supplies no scale-uniform continuum separator. -/
theorem nonharmonicCoercivity_and_middleSpectrum_hasMassGap
    (hharmonic : T.harmonic ≠ ⊥) (hnonharmonic : T.nonharmonic ≠ ⊥) :
    T.nonharmonicReceiverForm.IsCoercive ∧
      YangMillsLimit.SpectrumHasMassGap T.middleSpectrum :=
  ⟨T.nonharmonicReceiverForm_isCoercive,
    T.middleSpectrum_hasMassGap hharmonic hnonharmonic⟩

section Audit

#print axioms laplacianReceiverForm_nullCone
#print axioms laplacianReceiverForm_isDefinite_iff
#print axioms laplacianReceiverForm_isCoercive_iff
#print axioms nonharmonicReceiverForm_reading
#print axioms nonharmonicReceiverForm_isDefinite
#print axioms nonharmonicReceiverForm_isCoercive
#print axioms nonharmonicCoercivity_and_middleSpectrum_hasMassGap

end Audit

end HilbertTransportChain

end Soma.Holonics.Millennium.Coupling
