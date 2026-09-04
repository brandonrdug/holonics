import ElementaryHolonics.Millennium.HodgeSmoothProjectiveReceiver
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The common finite projective-space ambient over `ℂ`

This file factors the algebraic construction shared by every finite complex projective space.
For `coordinateCount` homogeneous coordinates it proves, without assuming any Hodge conclusion,
that:

* the degree-zero part of the standard grading is exactly `ℂ`;
* the coordinate population generates the homogeneous coordinate algebra over degree zero;
* the resulting `Proj` is finite type and proper over the complex point;
* its identity map supplies an actual `ProjectivePresentation`; and
* whenever at least one coordinate exists, the projective scheme is nonempty.

Thus the zero-space and positive-dimensional projective-space lines use one typed algebraic owner.
Smoothness, analytification, Hodge decomposition, and cycle class remain subsequent
source-specific obligations; none is hidden in this ambient construction.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Soma.Holonics.Millennium.HodgeProjectiveSpaceAmbient

open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver

/-- [definition] The homogeneous coordinate ring with the declared finite coordinate population. -/
abbrev CoordinateRing (coordinateCount : ℕ) := MvPolynomial (Fin coordinateCount) ℂ

/-- [definition] The standard total-degree grading on the coordinate ring. -/
abbrev Grading (coordinateCount : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin coordinateCount) ℂ

/-- [definition] The retained degree-zero coefficient ring. -/
abbrev DegreeZero (coordinateCount : ℕ) := Grading coordinateCount 0

attribute [local instance] MvPolynomial.gradedAlgebra

/-- [definition] A complex coefficient as a situated degree-zero polynomial occurrence. -/
def constantOccurrence (coordinateCount : ℕ) (coefficient : ℂ) :
    DegreeZero coordinateCount :=
  ⟨MvPolynomial.C coefficient, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_C (Fin coordinateCount) coefficient⟩

/-- [proved-standard; formal-checked] Every degree-zero homogeneous polynomial, independently of
the number of projective coordinates, is its constant coefficient. -/
theorem homogeneous_zero_eq_constant (coordinateCount : ℕ)
    (polynomial : DegreeZero coordinateCount) :
    (polynomial : CoordinateRing coordinateCount) =
      MvPolynomial.C ((polynomial : CoordinateRing coordinateCount).coeff 0) := by
  have homogeneous :
      (polynomial : CoordinateRing coordinateCount).IsHomogeneous 0 := by
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact polynomial.property
  calc
    (polynomial : CoordinateRing coordinateCount) =
        MvPolynomial.homogeneousComponent 0
          (polynomial : CoordinateRing coordinateCount) :=
      (MvPolynomial.homogeneousComponent_eq_self homogeneous).symm
    _ = MvPolynomial.C
          ((polynomial : CoordinateRing coordinateCount).coeff 0) :=
      MvPolynomial.homogeneousComponent_zero _

/-- [proved-standard; formal-checked] The typed degree-zero base of every finite standard
projective ambient is exactly the complex coefficient ring. -/
def degreeZeroEquiv (coordinateCount : ℕ) : DegreeZero coordinateCount ≃+* ℂ where
  toFun polynomial := (polynomial : CoordinateRing coordinateCount).coeff 0
  invFun coefficient := constantOccurrence coordinateCount coefficient
  left_inv polynomial := by
    apply Subtype.ext
    rw [homogeneous_zero_eq_constant coordinateCount polynomial]
    simp [constantOccurrence]
  right_inv coefficient := by simp [constantOccurrence]
  map_add' left right := by simp
  map_mul' left right := by
    have hleft := homogeneous_zero_eq_constant coordinateCount left
    have hright := homogeneous_zero_eq_constant coordinateCount right
    calc
      ((left : CoordinateRing coordinateCount) *
          (right : CoordinateRing coordinateCount)).coeff 0 =
          (MvPolynomial.C ((left : CoordinateRing coordinateCount).coeff 0) *
            MvPolynomial.C ((right : CoordinateRing coordinateCount).coeff 0)).coeff 0 := by
        congr 1
        exact congrArg₂ (· * ·) hleft hright
      _ = (left : CoordinateRing coordinateCount).coeff 0 *
          (right : CoordinateRing coordinateCount).coeff 0 := by simp

/-- [proved-standard; formal-checked] Evaluation at all declared projective coordinates reaches
every homogeneous-coordinate polynomial over the typed degree-zero base. -/
theorem coordinateAeval_surjective (coordinateCount : ℕ) : Function.Surjective
    (MvPolynomial.aeval (R := DegreeZero coordinateCount)
      (fun index : Fin coordinateCount =>
        (MvPolynomial.X index : CoordinateRing coordinateCount))) := by
  intro polynomial
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient =>
      refine ⟨MvPolynomial.C (constantOccurrence coordinateCount coefficient), ?_⟩
      simp [constantOccurrence]
  | add left right hleft hright =>
      obtain ⟨left', hleft'⟩ := hleft
      obtain ⟨right', hright'⟩ := hright
      refine ⟨left' + right', ?_⟩
      simp only [map_add, hleft', hright']
  | mul_X polynomial index hpolynomial =>
      obtain ⟨polynomial', hpolynomial'⟩ := hpolynomial
      refine ⟨polynomial' * MvPolynomial.X index, ?_⟩
      simp only [map_mul, MvPolynomial.aeval_X, hpolynomial']

/-- [proved-standard; formal-checked] The complete finite coordinate population generates the
homogeneous coordinate algebra over degree zero. -/
theorem coordinateAdjoin_eq_top (coordinateCount : ℕ) :
    Algebra.adjoin (DegreeZero coordinateCount)
      (Set.range fun index : Fin coordinateCount =>
        (MvPolynomial.X index : CoordinateRing coordinateCount)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
  exact coordinateAeval_surjective coordinateCount

/-- [proved-standard; formal-checked] The finite coordinate population is an exact finite-type
presentation over the degree-zero base. -/
theorem finiteType (coordinateCount : ℕ) :
    Algebra.FiniteType (DegreeZero coordinateCount)
      (CoordinateRing coordinateCount) := by
  apply Algebra.FiniteType.iff_exists_generators.mpr
  exact ⟨coordinateCount, ⟨Algebra.Generators.ofSurjective
    (fun index : Fin coordinateCount =>
      (MvPolynomial.X index : CoordinateRing coordinateCount))
    (coordinateAeval_surjective coordinateCount)⟩⟩

/-- [proved-standard; formal-checked] Every declared projective coordinate has degree one. -/
theorem variable_mem_degree_one (coordinateCount : ℕ) (index : Fin coordinateCount) :
    (MvPolynomial.X index : CoordinateRing coordinateCount) ∈
      Grading coordinateCount 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X ℂ index

/-- [proved-standard; formal-checked] The coordinate basic opens jointly cover the complete
projective carrier. -/
theorem coordinateBasicOpens_iSup_eq_top (coordinateCount : ℕ) :
    ⨆ index : Fin coordinateCount,
      Proj.basicOpen (Grading coordinateCount)
        (MvPolynomial.X index : CoordinateRing coordinateCount) = ⊤ := by
  exact Proj.iSup_basicOpen_eq_top' (Grading coordinateCount)
    (fun index : Fin coordinateCount =>
      (MvPolynomial.X index : CoordinateRing coordinateCount))
    (fun index => ⟨1, variable_mem_degree_one coordinateCount index⟩)
    (coordinateAdjoin_eq_top coordinateCount)

/-- [definition] The shared graded ambient consumed by the genuine projective receiver. -/
abbrev ambient (coordinateCount : ℕ) : GradedAmbient where
  Ring := CoordinateRing coordinateCount
  commRing := inferInstance
  Piece := Submodule ℂ (CoordinateRing coordinateCount)
  setLike := inferInstance
  addSubgroupClass := inferInstance
  grading := Grading coordinateCount
  gradedRing := MvPolynomial.gradedAlgebra

/-- [proved-standard; formal-checked] Every finite standard projective ambient is proper over its
typed degree-zero base. -/
theorem properProjection (coordinateCount : ℕ) :
    IsProper (ambient coordinateCount).projection := by
  letI : CommRing (ambient coordinateCount).Ring := (ambient coordinateCount).commRing
  letI : SetLike (ambient coordinateCount).Piece (ambient coordinateCount).Ring :=
    (ambient coordinateCount).setLike
  letI : AddSubgroupClass (ambient coordinateCount).Piece
      (ambient coordinateCount).Ring := (ambient coordinateCount).addSubgroupClass
  letI : GradedRing (ambient coordinateCount).grading :=
    (ambient coordinateCount).gradedRing
  letI : Algebra.FiniteType ((ambient coordinateCount).grading 0)
      (ambient coordinateCount).Ring := finiteType coordinateCount
  change IsProper (Proj.toSpecZero (Grading coordinateCount))
  infer_instance

/-- [proved-standard; formal-checked] The degree-zero base scheme is the complex point. -/
def baseIso (coordinateCount : ℕ) :
    (ambient coordinateCount).baseScheme ≅ ComplexPoint := by
  change Spec (.of (DegreeZero coordinateCount)) ≅ Spec (.of ℂ)
  exact Scheme.Spec.mapIso
    ((degreeZeroEquiv coordinateCount).symm.toCommRingCatIso.op)

/-- [proved-standard; formal-checked] The identity occurrence of a standard finite `Proj` is a
closed immersion. -/
theorem identity_isClosedImmersion (coordinateCount : ℕ) :
    IsClosedImmersion (𝟙 (Proj (Grading coordinateCount))) := by
  infer_instance

/-- [proved-standard; formal-checked] The standard finite `Proj` carries a genuine projective
presentation over `Spec ℂ`; no geometric conclusion is stored in the certificate. -/
noncomputable abbrev presentation (coordinateCount : ℕ) :
    HodgeSmoothProjectiveReceiver.ProjectivePresentation
      (Proj (Grading coordinateCount)) where
  ambient := ambient coordinateCount
  finiteType := finiteType coordinateCount
  properProjection := properProjection coordinateCount
  baseIso := baseIso coordinateCount
  embedding := 𝟙 (Proj (Grading coordinateCount))
  closedEmbedding := identity_isClosedImmersion coordinateCount

/-- [proved-standard; formal-checked] A projective ambient with at least one coordinate has an
actual homogeneous prime point. -/
theorem projectiveScheme_nonempty {coordinateCount : ℕ}
    (positive : 0 < coordinateCount) : Nonempty (Proj (Grading coordinateCount)) := by
  let coordinate : Fin coordinateCount := ⟨0, positive⟩
  let point : ProjectiveSpectrum (Grading coordinateCount) :=
    ⟨⊥, Ideal.isPrime_bot, by
      intro containsIrrelevant
      have variable_mem :
          (MvPolynomial.X coordinate : CoordinateRing coordinateCount) ∈
            HomogeneousIdeal.irrelevant (Grading coordinateCount) := by
        apply HomogeneousIdeal.mem_irrelevant_of_mem (Grading coordinateCount)
          (i := 1) (by norm_num)
        exact variable_mem_degree_one coordinateCount coordinate
      have variable_mem_bot :
          (MvPolynomial.X coordinate : CoordinateRing coordinateCount) ∈
            (⊥ : HomogeneousIdeal (Grading coordinateCount)) :=
        containsIrrelevant variable_mem
      have variable_eq_zero :
          (MvPolynomial.X coordinate : CoordinateRing coordinateCount) = 0 :=
        (Submodule.mem_bot ℂ).mp variable_mem_bot
      exact MvPolynomial.X_ne_zero coordinate variable_eq_zero⟩
  exact ⟨point⟩

section Audit

#print axioms degreeZeroEquiv
#print axioms coordinateAeval_surjective
#print axioms finiteType
#print axioms coordinateBasicOpens_iSup_eq_top
#print axioms properProjection
#print axioms presentation
#print axioms projectiveScheme_nonempty

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveSpaceAmbient
