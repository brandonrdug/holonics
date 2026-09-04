import ElementaryHolonics.Millennium.HodgeSmoothProjectiveReceiver
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# The genuine projective-zero ambient over the complex point

This file constructs the first nonempty algebraic source behind the smooth-projective Hodge
receiver.  It uses the standard grading on `ℂ[X]`, proves that the degree-zero base is exactly
`ℂ`, proves finite type over that base, obtains the proper `Proj` projection, and exhibits an
actual homogeneous prime point of `Proj(ℂ[X])`.  It then proves `D₊(X) = ⊤`, identifies the
homogeneous localization `Away(X)` with the degree-zero ring, derives that `Proj.toSpecZero` is an
isomorphism, and packages the resulting nonempty smooth projective complex scheme.

The file then closes the source-specific semantic loop.  It proves the projective scheme and its
closed-point population are singletons, uses the terminal singular simplicial set to calculate
rational homology and cohomology, classifies its actual algebraic cycles by codimension, constructs
the pure Hodge splitting and point fundamental cycle class, and proves the Hodge conclusion in
every codimension of this realization.  This local carrier is a complete calibration source for
the universal receiver, not a substitute for the conjectural algebraicity law on every smooth
projective complex variety.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

namespace Soma.Holonics.Millennium.HodgeProjectiveZeroAmbient

open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction

/-- [definition] The homogeneous coordinate ring of complex projective zero-space. -/
abbrev CoordinateRing := MvPolynomial (Fin 1) ℂ

/-- [definition] Its standard total-degree grading. -/
abbrev Grading := MvPolynomial.homogeneousSubmodule (Fin 1) ℂ

/-- [definition] The degree-zero ring retained as a subtype before rebasing it to `ℂ`. -/
abbrev DegreeZero := Grading 0

attribute [local instance] MvPolynomial.gradedAlgebra

/-- [definition] A complex coefficient as a degree-zero homogeneous polynomial occurrence. -/
def constantOccurrence (coefficient : ℂ) : DegreeZero :=
  ⟨MvPolynomial.C coefficient, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_C (Fin 1) coefficient⟩

/-- [proved-standard; formal-checked] Every degree-zero homogeneous polynomial in one variable is
the constant selected by its zero-monomial coefficient. -/
theorem homogeneous_zero_eq_constant (polynomial : DegreeZero) :
    (polynomial : CoordinateRing) =
      MvPolynomial.C ((polynomial : CoordinateRing).coeff 0) := by
  have homogeneous : (polynomial : CoordinateRing).IsHomogeneous 0 := by
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact polynomial.property
  calc
    (polynomial : CoordinateRing) =
        MvPolynomial.homogeneousComponent 0 (polynomial : CoordinateRing) :=
      (MvPolynomial.homogeneousComponent_eq_self homogeneous).symm
    _ = MvPolynomial.C ((polynomial : CoordinateRing).coeff 0) :=
      MvPolynomial.homogeneousComponent_zero (polynomial : CoordinateRing)

/-- [proved-standard; formal-checked] On a one-coordinate exponent face, total degree is the
single retained exponent. -/
theorem finOne_degree (exponent : Fin 1 →₀ ℕ) :
    exponent.degree = exponent 0 := by
  classical
  by_cases exponent_zero : exponent 0 = 0
  · have exponent_eq_zero : exponent = 0 := by
      apply Finsupp.ext
      intro index
      fin_cases index
      exact exponent_zero
    simp [exponent_eq_zero]
  · have support_eq : exponent.support = {0} := by
      ext index
      fin_cases index
      simp [Finsupp.mem_support_iff, exponent_zero]
    rw [Finsupp.degree_apply, support_eq]
    simp

/-- [proved-standard; formal-checked] Every degree-`n` homogeneous polynomial in one variable is
one coefficient carried by the unique monomial `Xⁿ`. -/
theorem homogeneous_eq_constant_mul_X_pow {polynomial : CoordinateRing} {degree : ℕ}
    (homogeneous : polynomial.IsHomogeneous degree) :
    polynomial =
      MvPolynomial.C
          (polynomial.coeff (Finsupp.single (0 : Fin 1) degree)) *
        MvPolynomial.X 0 ^ degree := by
  classical
  apply MvPolynomial.ext
  intro exponent
  rw [MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  by_cases sameExponent : exponent = Finsupp.single (0 : Fin 1) degree
  · subst exponent
    simp
  · have differentDegree : exponent.degree ≠ degree := by
      intro degree_eq
      apply sameExponent
      apply Finsupp.ext
      intro index
      fin_cases index
      simpa [finOne_degree exponent] using degree_eq
    rw [homogeneous.coeff_eq_zero differentDegree]
    have reverseExponent :
        Finsupp.single (0 : Fin 1) degree ≠ exponent :=
      Ne.symm sameExponent
    simp [reverseExponent]

/-- [proved-standard; formal-checked] The typed degree-zero base is exactly the complex
coefficient ring. -/
def degreeZeroEquiv : DegreeZero ≃+* ℂ where
  toFun polynomial := (polynomial : CoordinateRing).coeff 0
  invFun coefficient := constantOccurrence coefficient
  left_inv polynomial := by
    apply Subtype.ext
    rw [homogeneous_zero_eq_constant polynomial]
    simp [constantOccurrence]
  right_inv coefficient := by simp [constantOccurrence]
  map_add' left right := by simp
  map_mul' left right := by
    have hleft := homogeneous_zero_eq_constant left
    have hright := homogeneous_zero_eq_constant right
    calc
      ((left : CoordinateRing) * (right : CoordinateRing)).coeff 0 =
          (MvPolynomial.C ((left : CoordinateRing).coeff 0) *
            MvPolynomial.C ((right : CoordinateRing).coeff 0)).coeff 0 := by
        congr 1
        exact congrArg₂ (· * ·) hleft hright
      _ = (left : CoordinateRing).coeff 0 *
          (right : CoordinateRing).coeff 0 := by simp

/-- [proved-standard; formal-checked] Evaluation at the unique variable is surjective over the
typed degree-zero coefficient ring. -/
theorem generator_aeval_surjective : Function.Surjective
    (MvPolynomial.aeval (R := DegreeZero)
      (fun _ : Fin 1 => (MvPolynomial.X 0 : CoordinateRing))) := by
  intro polynomial
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient =>
      refine ⟨MvPolynomial.C (constantOccurrence coefficient), ?_⟩
      simp [constantOccurrence]
  | add left right hleft hright =>
      obtain ⟨left', hleft'⟩ := hleft
      obtain ⟨right', hright'⟩ := hright
      refine ⟨left' + right', ?_⟩
      simp only [map_add, hleft', hright']
  | mul_X polynomial index hpolynomial =>
      obtain ⟨polynomial', hpolynomial'⟩ := hpolynomial
      rw [Fin.eq_zero index]
      refine ⟨polynomial' * MvPolynomial.X 0, ?_⟩
      simp only [map_mul, MvPolynomial.aeval_X, hpolynomial']

/-- [proved-standard; formal-checked] The unique degree-one coordinate generates the whole
homogeneous coordinate algebra over degree zero. -/
theorem generator_adjoin_eq_top :
    Algebra.adjoin DegreeZero
      (Set.range fun _ : Fin 1 => (MvPolynomial.X 0 : CoordinateRing)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
  exact generator_aeval_surjective

/-- [proved-standard; formal-checked] One polynomial generator presents the homogeneous
coordinate ring over its typed degree-zero base. -/
theorem finiteType : Algebra.FiniteType DegreeZero CoordinateRing := by
  apply Algebra.FiniteType.iff_exists_generators.mpr
  exact ⟨1, ⟨Algebra.Generators.ofSurjective
    (fun _ : Fin 1 => (MvPolynomial.X 0 : CoordinateRing))
      generator_aeval_surjective⟩⟩

/-- [proved-standard; formal-checked] The unique coordinate has degree one. -/
theorem variable_mem_degree_one :
    (MvPolynomial.X (0 : Fin 1) : CoordinateRing) ∈ Grading 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X ℂ 0

/-- [proved-standard; formal-checked] The degree of the projective coordinate is positive. -/
theorem degreeOne_positive : 0 < (1 : ℕ) := by omega

/-- [proved-standard; formal-checked] The unique projective basic open covers the entire
projective-zero carrier. -/
theorem basicOpen_variable_eq_top :
    Proj.basicOpen Grading
      (MvPolynomial.X (0 : Fin 1) : CoordinateRing) = ⊤ := by
  have cover := Proj.iSup_basicOpen_eq_top' Grading
    (fun _ : Fin 1 => (MvPolynomial.X 0 : CoordinateRing))
    (fun _ => ⟨1, variable_mem_degree_one⟩)
    generator_adjoin_eq_top
  simpa [Fin.eq_zero] using cover

/-- [proved-standard; formal-checked] Every degree-zero homogeneous fraction away from the unique
coordinate comes from the degree-zero coefficient ring.  Numerator and denominator carry the same
degree, so the unique monomial powers cancel exactly. -/
theorem fromZeroRingHom_surjective : Function.Surjective
    (HomogeneousLocalization.fromZeroRingHom Grading
      (Submonoid.powers
        (MvPolynomial.X (0 : Fin 1) : CoordinateRing))) := by
  intro fraction
  obtain ⟨degree, numerator, numeratorHomogeneous, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective Grading
      variable_mem_degree_one fraction
  let coefficient :=
    numerator.coeff (Finsupp.single (0 : Fin 1) degree)
  refine ⟨constantOccurrence coefficient, ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  let denominator : Submonoid.powers
      (MvPolynomial.X (0 : Fin 1) : CoordinateRing) :=
    ⟨MvPolynomial.X (0 : Fin 1) ^ degree, by
      rw [Submonoid.mem_powers_iff]
      exact ⟨degree, rfl⟩⟩
  change Localization.mk (MvPolynomial.C coefficient) 1 =
    Localization.mk numerator denominator
  rw [homogeneous_eq_constant_mul_X_pow numeratorHomogeneous]
  rw [Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp [coefficient, denominator, mul_comm]

/-- [proved-standard; formal-checked] The degree-zero localization map is injective.  The unique
coordinate is nonzero in the polynomial domain, so all its powers are non-zero-divisors. -/
theorem fromZeroRingHom_injective : Function.Injective
    (HomogeneousLocalization.fromZeroRingHom Grading
      (Submonoid.powers
        (MvPolynomial.X (0 : Fin 1) : CoordinateRing))) := by
  intro left right equalFractions
  apply Subtype.ext
  have equalValues := congrArg HomogeneousLocalization.val equalFractions
  apply IsLocalization.injective
    (Localization
      (Submonoid.powers
        (MvPolynomial.X (0 : Fin 1) : CoordinateRing)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin 1)))
  exact equalValues

/-- [proved-standard; formal-checked] The degree-zero homogeneous localization away from `X` is
exactly the typed degree-zero coefficient ring. -/
def awayEquiv : DegreeZero ≃+*
    HomogeneousLocalization.Away Grading
      (MvPolynomial.X (0 : Fin 1) : CoordinateRing) :=
  RingEquiv.ofBijective
    (HomogeneousLocalization.fromZeroRingHom Grading
      (Submonoid.powers
        (MvPolynomial.X (0 : Fin 1) : CoordinateRing)))
    ⟨fromZeroRingHom_injective, fromZeroRingHom_surjective⟩

/-- [proved-standard; formal-checked] The unique affine projective chart is the entire `Proj`, so
its canonical open immersion is an isomorphism. -/
theorem awayι_isIso : IsIso
    (Proj.awayι Grading
      (MvPolynomial.X (0 : Fin 1) : CoordinateRing)
      variable_mem_degree_one degreeOne_positive) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Proj.opensRange_awayι, basicOpen_variable_eq_top]

/-- [proved-standard; formal-checked] Complex projective zero-space is scheme-isomorphic to its
degree-zero base. -/
noncomputable def projectiveSchemeIsoBase :
    Proj Grading ≅ Spec (.of DegreeZero) := by
  letI : IsIso
      (Proj.awayι Grading
        (MvPolynomial.X (0 : Fin 1) : CoordinateRing)
        variable_mem_degree_one degreeOne_positive) :=
    awayι_isIso
  exact
    (asIso (Proj.awayι Grading
      (MvPolynomial.X (0 : Fin 1) : CoordinateRing)
      variable_mem_degree_one degreeOne_positive)).symm ≪≫
      Scheme.Spec.mapIso (awayEquiv.toCommRingCatIso.op)

/-- [proved-standard; formal-checked] The projective-zero structure map is an isomorphism. -/
theorem toSpecZero_isIso : IsIso (Proj.toSpecZero Grading) := by
  letI : IsIso
      (Proj.awayι Grading
        (MvPolynomial.X (0 : Fin 1) : CoordinateRing)
        variable_mem_degree_one degreeOne_positive) :=
    awayι_isIso
  letI : IsIso
      (CommRingCat.ofHom
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers
            (MvPolynomial.X (0 : Fin 1) : CoordinateRing)))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fromZeroRingHom_injective, fromZeroRingHom_surjective⟩
  haveI : IsIso
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers
            (MvPolynomial.X (0 : Fin 1) : CoordinateRing))))) :=
    inferInstance
  rw [← isIso_comp_left_iff
    (Proj.awayι Grading
      (MvPolynomial.X (0 : Fin 1) : CoordinateRing)
      variable_mem_degree_one degreeOne_positive)]
  rw [Proj.awayι_toSpecZero]
  infer_instance

/-- [definition] The actual graded ambient consumed by `ProjectivePresentation`. -/
abbrev ambient : GradedAmbient where
  Ring := CoordinateRing
  commRing := inferInstance
  Piece := Submodule ℂ CoordinateRing
  setLike := inferInstance
  addSubgroupClass := inferInstance
  grading := Grading
  gradedRing := MvPolynomial.gradedAlgebra

/-- [proved-standard; formal-checked] The packaged projective projection is proper. -/
theorem properProjection : IsProper ambient.projection := by
  letI : CommRing ambient.Ring := ambient.commRing
  letI : SetLike ambient.Piece ambient.Ring := ambient.setLike
  letI : AddSubgroupClass ambient.Piece ambient.Ring := ambient.addSubgroupClass
  letI : GradedRing ambient.grading := ambient.gradedRing
  letI : Algebra.FiniteType (ambient.grading 0) ambient.Ring := by
    change Algebra.FiniteType DegreeZero CoordinateRing
    exact finiteType
  change IsProper (Proj.toSpecZero Grading)
  infer_instance

/-- [proved-standard; formal-checked] The degree-zero base scheme is the complex point. -/
def baseIso : ambient.baseScheme ≅ ComplexPoint := by
  change Spec (.of DegreeZero) ≅ Spec (.of ℂ)
  exact Scheme.Spec.mapIso (degreeZeroEquiv.symm.toCommRingCatIso.op)

/-- [proved-standard; formal-checked] The projective-zero ambient is genuinely inhabited.  The
point is the zero homogeneous prime, which excludes the irrelevant ideal because `X ≠ 0`. -/
theorem projectiveScheme_nonempty : Nonempty ambient.projectiveScheme := by
  letI : CommRing ambient.Ring := ambient.commRing
  letI : SetLike ambient.Piece ambient.Ring := ambient.setLike
  letI : AddSubgroupClass ambient.Piece ambient.Ring := ambient.addSubgroupClass
  letI : GradedRing ambient.grading := ambient.gradedRing
  let point : ProjectiveSpectrum ambient.grading :=
    ⟨⊥, Ideal.isPrime_bot, by
      intro containsIrrelevant
      have variable_mem :
          (MvPolynomial.X (0 : Fin 1) : ambient.Ring) ∈
            HomogeneousIdeal.irrelevant ambient.grading := by
        apply HomogeneousIdeal.mem_irrelevant_of_mem ambient.grading
          (i := 1) (by norm_num)
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.isHomogeneous_X ℂ 0
      have variable_mem_bot :
          (MvPolynomial.X (0 : Fin 1) : ambient.Ring) ∈
            (⊥ : HomogeneousIdeal ambient.grading) :=
        containsIrrelevant variable_mem
      have variable_eq_zero :
          (MvPolynomial.X (0 : Fin 1) : ambient.Ring) = 0 :=
        (Submodule.mem_bot ℂ).mp variable_mem_bot
      exact MvPolynomial.X_ne_zero _ variable_eq_zero⟩
  exact ⟨point⟩

/-! ## The completed smooth-projective carrier -/

/-- [proved-standard; formal-checked] The identity occurrence of projective zero-space is a
closed immersion.  Keeping this witness at the unbundled `Proj Grading` type prevents the ambient
record projection from obscuring the identity morphism during instance synthesis. -/
theorem identity_isClosedImmersion :
    IsClosedImmersion (𝟙 (Proj Grading)) := by
  infer_instance

/-- [proved-standard; formal-checked] The projective-zero scheme carries the required actual
projective presentation over `Spec ℂ`. -/
noncomputable abbrev presentation :
    HodgeSmoothProjectiveReceiver.ProjectivePresentation (Proj Grading) where
  ambient := ambient
  finiteType := by
    change Algebra.FiniteType DegreeZero CoordinateRing
    exact finiteType
  properProjection := properProjection
  baseIso := baseIso
  embedding := 𝟙 (Proj Grading)
  closedEmbedding := identity_isClosedImmersion

/-- [proved-standard; formal-checked] The retained complex structure map is an isomorphism. -/
theorem presentation_structureMap_isIso :
    IsIso presentation.structureMap := by
  letI : IsIso (Proj.toSpecZero Grading) := toSpecZero_isIso
  letI : IsIso baseIso.hom := baseIso.isIso_hom
  change IsIso
    ((𝟙 (Proj Grading)) ≫ Proj.toSpecZero Grading ≫ baseIso.hom)
  rw [Category.id_comp]
  exact IsIso.comp_isIso' toSpecZero_isIso baseIso.isIso_hom

/-- [proved-standard; formal-checked] The projective-zero structure map is smooth.  Smoothness is
derived from the completed scheme isomorphism rather than admitted as a free field. -/
theorem presentation_smooth : Smooth presentation.structureMap := by
  letI : IsIso presentation.structureMap := presentation_structureMap_isIso
  infer_instance

/-- [proved-standard; formal-checked] A genuine nonempty smooth projective complex scheme admitted
by the geometric half of the Hodge receiver. -/
noncomputable def carrier : SmoothProjectiveComplexScheme where
  X := Proj Grading
  projective := presentation
  smooth := presentation_smooth

/-- [proved-standard; formal-checked] The completed smooth-projective carrier has an actual
geometric point. -/
theorem carrier_nonempty : Nonempty carrier.X :=
  projectiveScheme_nonempty

/-! ## The exact analytic-point population -/

/-- [proved-standard; formal-checked] The underlying projective-zero carrier has only one point.
The proof transports equality through the already-constructed scheme isomorphism to `Spec ℂ`,
whose point population is `Unique`. -/
theorem projectiveScheme_subsingleton : Subsingleton (Proj Grading) := by
  letI : IsIso presentation.structureMap := presentation_structureMap_isIso
  constructor
  intro left right
  apply (ConcreteCategory.bijective_of_isIso presentation.structureMap.base).1
  exact Subsingleton.elim _ _

/-- [proved-standard; formal-checked] The nonempty projective-zero carrier is a unique pointed
space, not merely an abstract subsingleton. -/
noncomputable instance projectiveScheme_unique : Unique (Proj Grading) where
  default := Classical.choice projectiveScheme_nonempty
  uniq left := projectiveScheme_subsingleton.elim left _

/-- [definition] The genuine analytic carrier of a complex point. -/
abbrev AnalyticPoint : TopCat := TopCat.of PUnit

/-- [definition] The unique analytic point transported to projective zero-space. -/
def analyticToZariski : AnalyticPoint ⟶ (Proj Grading : TopCat) :=
  TopCat.ofHom (ContinuousMap.const AnalyticPoint (default : Proj Grading))

/-- [proved-standard; formal-checked] Every point of projective zero-space is closed. -/
theorem projectivePoint_isClosed (point : Proj Grading) :
    IsClosed ({point} : Set (Proj Grading)) := by
  have singleton_eq_univ : ({point} : Set (Proj Grading)) = Set.univ := by
    ext other
    simp [projectiveScheme_subsingleton.elim other point]
  rw [singleton_eq_univ]
  exact isClosed_univ

/-- [proved-standard; formal-checked] The analytic point and the closed complex points of
projective zero-space are exactly the same occurrence population. -/
theorem analyticToClosedPoint_bijective :
    Function.Bijective fun point : AnalyticPoint =>
      (⟨analyticToZariski point,
        projectivePoint_isClosed (analyticToZariski point)⟩ :
        ComplexClosedPoint (Proj Grading)) := by
  constructor
  · exact fun _ _ _ => Subsingleton.elim _ _
  · intro point
    refine ⟨PUnit.unit, ?_⟩
    exact Subtype.ext (projectiveScheme_subsingleton.elim _ _)

/-! ## Codimension collapse on the one-point source -/

/-- [proved-standard; formal-checked] The unique projective-zero point has coheight zero. -/
theorem projectivePoint_coheight (point : Proj Grading) :
    Order.coheight point = 0 := by
  rw [Order.coheight_eq_zero, isMax_iff_forall_not_lt]
  intro other
  rw [projectiveScheme_subsingleton.elim other point]
  exact lt_irrefl point

/-- [proved-standard; formal-checked] A genuine integral algebraic cycle on projective zero-space
with positive codimension is necessarily zero. -/
theorem integralPositiveCodimension_eq_zero {p : ℕ} (positive : p ≠ 0)
    (cycle : IntegralCodimensionCycles (Proj Grading) p) : cycle = 0 := by
  apply Subtype.ext
  ext point
  have coefficient_zero : (cycle : AlgebraicCycle (Proj Grading) ℤ) point = 0 := by
    by_contra coefficient_nonzero
    have codimension := cycle.property point coefficient_nonzero
    rw [projectivePoint_coheight] at codimension
    have p_zero : p = 0 := by exact_mod_cast codimension.symm
    exact positive p_zero
  simpa [coefficient_zero]

/-- [proved-standard; formal-checked] Positive-codimension integral cycle populations on the
complex point have only the zero occurrence. -/
theorem integralPositiveCodimension_subsingleton {p : ℕ} (positive : p ≠ 0) :
    Subsingleton (IntegralCodimensionCycles (Proj Grading) p) := by
  constructor
  intro left right
  rw [integralPositiveCodimension_eq_zero positive left,
    integralPositiveCodimension_eq_zero positive right]

/-- [proved-standard; formal-checked] Rationalization does not manufacture a
positive-codimension source occurrence on projective zero-space. -/
theorem rationalPositiveCodimension_eq_zero {p : ℕ} (positive : p ≠ 0)
    (cycle : RationalCodimensionCycles (Proj Grading) p) : cycle = 0 := by
  letI : Subsingleton (IntegralCodimensionCycles (Proj Grading) p) :=
    integralPositiveCodimension_subsingleton positive
  refine TensorProduct.induction_on cycle rfl ?_ ?_
  · intro coefficient integralCycle
    rw [Subsingleton.elim integralCycle 0, TensorProduct.tmul_zero]
  · intro left right left_zero right_zero
    rw [left_zero, right_zero, add_zero]

/-- [definition] Evaluate an integral codimension-zero cycle at the unique projective point. -/
def integralZeroEvaluation :
    IntegralCodimensionCycles (Proj Grading) 0 →ₗ[ℤ] ℤ where
  toFun cycle := (cycle : AlgebraicCycle (Proj Grading) ℤ) default
  map_add' left right := rfl
  map_smul' coefficient cycle := rfl

/-- [proved-standard; formal-checked] Evaluation at the unique projective point is injective on
integral codimension-zero cycles. -/
theorem integralZeroEvaluation_injective :
    Function.Injective integralZeroEvaluation := by
  intro left right sameCoefficient
  apply Subtype.ext
  ext point
  change (left : AlgebraicCycle (Proj Grading) ℤ) default =
    (right : AlgebraicCycle (Proj Grading) ℤ) default at sameCoefficient
  rw [projectiveScheme_subsingleton.elim point (default : Proj Grading)]
  exact sameCoefficient

/-- [proved-standard; formal-checked] Every integral coefficient occurs as the unique
projective-point cycle. -/
theorem integralZeroEvaluation_surjective :
    Function.Surjective integralZeroEvaluation := by
  intro coefficient
  let cycle : IntegralCodimensionCycles (Proj Grading) 0 :=
    ⟨Function.locallyFinsuppWithin.single (default : Proj Grading) coefficient,
      fun point _ => projectivePoint_coheight point⟩
  refine ⟨cycle, ?_⟩
  change Function.locallyFinsuppWithin.single
    (default : Proj Grading) coefficient default = coefficient
  simp

/-- [proved-standard; formal-checked] Integral codimension-zero cycles on projective zero-space
are exactly one addressed integer coefficient. -/
noncomputable def integralZeroEquivInteger :
    IntegralCodimensionCycles (Proj Grading) 0 ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective integralZeroEvaluation
    ⟨integralZeroEvaluation_injective, integralZeroEvaluation_surjective⟩

/-- [proved-standard; formal-checked] Exact tensor rationalization turns the unique integral
point-cycle coefficient into one rational source line. -/
noncomputable def rationalZeroEquivRational :
    RationalCodimensionCycles (Proj Grading) 0 ≃ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl ℚ ℚ) integralZeroEquivInteger).trans
    (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ)

/-! ## Degree-zero Betti cohomology of the analytic point -/

/-- [proved-standard; formal-checked] Rational singular degree-zero homology of the analytic point
is one rational line. -/
noncomputable def analyticPointH0EquivRational :
    RationalSingularHomology 0 AnalyticPoint ≃ₗ[ℚ] ℚ :=
  (asIso (TopCat.singularHomology₀ε AnalyticPoint rationalCoefficient)).toLinearEquiv

/-- [proved-standard; formal-checked] Rational Betti degree-zero cohomology of the analytic point
is the dual of that same one-dimensional line and hence is again `ℚ`. -/
noncomputable def analyticPointH0CohomologyEquivRational :
    RationalBettiCohomology AnalyticPoint 0 ≃ₗ[ℚ] ℚ :=
  analyticPointH0EquivRational.dualMap.symm.trans
    (LinearMap.ringLmapEquivSelf ℚ ℚ ℚ)

/-- [proved-standard; formal-checked] The singular simplicial set of the analytic point is a
terminal simplicial set. -/
noncomputable def analyticPointSSet_isTerminal :
    IsTerminal (TopCat.toSSet.obj AnalyticPoint) :=
  IsTerminal.ofUniqueHom
    (fun _ => SSet.const
      (TopCat.toSSetObj₀Equiv.symm (PUnit.unit : AnalyticPoint)))
    (fun _ morphism => by
      ext simplex
      apply (TopCat.toSSetObjEquiv AnalyticPoint simplex).injective
      ext point)

/-- [proved-standard; formal-checked] The singular simplicial set of a point has no
nondegenerate simplex in positive degree. -/
noncomputable instance analyticPointSSet_hasDimensionLT :
    (TopCat.toSSet.obj AnalyticPoint).HasDimensionLT 1 :=
  (SSet.hasDimensionLT_iff_of_iso
    (SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso analyticPointSSet_isTerminal) 1).mp
      inferInstance

/-- [proved-standard; formal-checked] Every positive even rational singular-homology carrier of
the analytic point is zero. -/
theorem analyticPointPositiveEvenHomology_isZero {p : ℕ} (positive : p ≠ 0) :
    IsZero (RationalSingularHomology (2 * p) AnalyticPoint) := by
  exact (TopCat.toSSet.obj AnalyticPoint).isZero_homology_of_hasDimensionLT
    rationalCoefficient (2 * p) 1 (by omega)

/-- [proved-standard; formal-checked] Consequently every positive even rational Betti
cohomology occurrence of the analytic point is zero. -/
theorem analyticPointPositiveBettiCohomology_subsingleton {p : ℕ} (positive : p ≠ 0) :
    Subsingleton (RationalBettiCohomology AnalyticPoint p) := by
  letI : Subsingleton (RationalSingularHomology (2 * p) AnalyticPoint) :=
    ModuleCat.subsingleton_of_isZero
      (analyticPointPositiveEvenHomology_isZero positive)
  constructor
  intro left right
  apply LinearMap.ext
  intro homologyClass
  rw [Subsingleton.elim homologyClass 0]
  simp

/-! ## The exact point Hodge splitting -/

/-- [proved-derived; formal-checked] Tensoring against a zero receiver cannot create a complexified
occurrence. -/
theorem complexification_eq_zero_of_subsingleton (H : ModuleCat ℚ) [Subsingleton H]
    (vector : Complexification H) : vector = 0 := by
  refine TensorProduct.induction_on vector rfl ?_ ?_
  · intro coefficient occurrence
    rw [Subsingleton.elim occurrence 0, TensorProduct.tmul_zero]
  · intro left right left_zero right_zero
    rw [left_zero, right_zero, add_zero]

/-- [proved-derived; formal-checked] A zero rational receiver has the unique zero pure Hodge
splitting in every weight. -/
noncomputable def zeroHodgeDecomposition (H : ModuleCat ℚ) [Subsingleton H] (weight : ℕ) :
    PureHodgeDecomposition H weight where
  component := fun _ => ⊥
  internal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro index
      simp
    · have bot_eq_top : (⊥ : Submodule ℂ (Complexification H)) = ⊤ := by
        ext vector
        constructor
        · exact fun _ => Submodule.mem_top
        · intro _
          rw [complexification_eq_zero_of_subsingleton H vector]
          exact Submodule.zero_mem _
      simp [bot_eq_top]
  conjugation_exchanges := by
    intro index vector
    rw [complexification_eq_zero_of_subsingleton H vector]
    simp

/-- [proved-derived; formal-checked] In weight zero the sole Hodge component is the complete
complexified receiver. -/
noncomputable def weightZeroHodgeDecomposition (H : ModuleCat ℚ) :
    PureHodgeDecomposition H 0 where
  component := fun _ => ⊤
  internal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · simpa using (iSupIndep_unique (fun _ : Fin 1 =>
        (⊤ : Submodule ℂ (Complexification H))))
    · simp
  conjugation_exchanges := by simp

/-- [proved-standard; formal-checked] The analytic point has exactly its weight-zero line in
codimension zero and the zero Hodge splitting in every positive codimension. -/
noncomputable def analyticPointHodgeDecomposition (p : ℕ) :
    PureHodgeDecomposition (RationalBettiCohomology AnalyticPoint p) (2 * p) := by
  by_cases positive : p ≠ 0
  · letI : Subsingleton (RationalBettiCohomology AnalyticPoint p) :=
      analyticPointPositiveBettiCohomology_subsingleton positive
    exact zeroHodgeDecomposition _ _
  · have p_zero : p = 0 := by omega
    subst p
    exact weightZeroHodgeDecomposition _

/-! ## The point cycle-class passage and completed realization -/

/-- [proved-standard; formal-checked] The unique rational point-cycle coefficient is identified
with the unique rational degree-zero Betti cohomology coefficient. -/
noncomputable def rationalZeroCycleClassEquiv :
    RationalCodimensionCycles (Proj Grading) 0 ≃ₗ[ℚ]
      RationalBettiCohomology AnalyticPoint 0 :=
  rationalZeroEquivRational.trans analyticPointH0CohomologyEquivRational.symm

/-- [proved-standard; formal-checked] The cycle-class map of the complex point is the
degree-zero fundamental-class equivalence and the uniquely forced zero map in positive
codimension. -/
noncomputable def analyticPointCycleClass (p : ℕ) :
    ModuleCat.of ℚ (RationalCodimensionCycles (Proj Grading) p) ⟶
      RationalBettiCohomology AnalyticPoint p := by
  by_cases positive : p ≠ 0
  · exact 0
  · have p_zero : p = 0 := by omega
    subst p
    exact ModuleCat.ofHom rationalZeroCycleClassEquiv.toLinearMap

/-- [proved-standard; formal-checked] The point cycle-class map is surjective in every
codimension: by the fundamental-class equivalence at zero and by exact source/receiver vanishing
above zero. -/
theorem analyticPointCycleClass_surjective (p : ℕ) :
    Function.Surjective (analyticPointCycleClass p).hom := by
  by_cases positive : p ≠ 0
  · letI : Subsingleton (RationalBettiCohomology AnalyticPoint p) :=
      analyticPointPositiveBettiCohomology_subsingleton positive
    intro hodgeClass
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  · have p_zero : p = 0 := by omega
    subst p
    exact rationalZeroCycleClassEquiv.surjective

/-- [proved-standard; formal-checked] Every point-cycle class lands in the exact middle Hodge
receiver selected by the point splitting. -/
theorem analyticPointCycleClassesAreHodge (p : ℕ) :
    LinearMap.range (analyticPointCycleClass p).hom ≤
      (analyticPointHodgeDecomposition p).rationalMiddle p := by
  intro hodgeClass _
  by_cases positive : p ≠ 0
  · letI : Subsingleton (RationalBettiCohomology AnalyticPoint p) :=
      analyticPointPositiveBettiCohomology_subsingleton positive
    rw [Subsingleton.elim hodgeClass 0]
    exact Submodule.zero_mem _
  · have p_zero : p = 0 := by omega
    subst p
    exact Submodule.mem_top

/-- [proved-standard; formal-checked] The projective-zero carrier now has its complete
source-specific analytic, Hodge, and cycle-class semantics. -/
noncomputable def semantics : HodgeSemantics (Proj Grading) where
  complexDimension := 0
  analyticSpace := AnalyticPoint
  toZariski := analyticToZariski
  toZariski_closed := fun point =>
    projectivePoint_isClosed (analyticToZariski point)
  toClosedPoint_bijective := analyticToClosedPoint_bijective
  hodgeDecomposition := analyticPointHodgeDecomposition
  cycleClass := analyticPointCycleClass
  cycleClassesAreHodge := analyticPointCycleClassesAreHodge

/-- [proved-standard; formal-checked] The completed projective-zero realization retains the same
scheme in its geometric and semantic faces. -/
noncomputable def realization : Realization where
  geometry := carrier
  semantics := semantics

/-- [proved-standard; formal-checked] The source-specific Hodge conclusion holds in every
codimension of the genuine complex point realization. -/
theorem realization_hodgeConclusion (p : ℕ) :
    (realization.datum p).Conclusion := by
  change (analyticPointHodgeDecomposition p).rationalMiddle p =
    LinearMap.range (analyticPointCycleClass p).hom
  have range_eq_top : LinearMap.range (analyticPointCycleClass p).hom = ⊤ :=
    LinearMap.range_eq_top.mpr (analyticPointCycleClass_surjective p)
  apply le_antisymm
  · rw [range_eq_top]
    exact le_top
  · exact analyticPointCycleClassesAreHodge p

/-- [definition] The exact source-specific canonical family containing only the completed complex
point realization. -/
def ProjectiveZeroCanonical (R : Realization) : Prop :=
  R = realization

/-- [proved-standard; formal-checked] The official Hodge receiver is inhabited and closed for the
nonempty canonical family consisting of the genuine complex point realization. -/
theorem projectiveZeroTheHodgeConjecture :
    TheHodgeConjecture ProjectiveZeroCanonical := by
  intro R canonical
  subst R
  exact realization_hodgeConclusion

section Audit

#print axioms homogeneous_zero_eq_constant
#print axioms degreeZeroEquiv
#print axioms finiteType
#print axioms fromZeroRingHom_surjective
#print axioms fromZeroRingHom_injective
#print axioms awayEquiv
#print axioms awayι_isIso
#print axioms projectiveSchemeIsoBase
#print axioms toSpecZero_isIso
#print axioms properProjection
#print axioms baseIso
#print axioms projectiveScheme_nonempty
#print axioms presentation
#print axioms presentation_structureMap_isIso
#print axioms presentation_smooth
#print axioms carrier
#print axioms carrier_nonempty
#print axioms analyticPointSSet_isTerminal
#print axioms analyticPointPositiveEvenHomology_isZero
#print axioms rationalZeroEquivRational
#print axioms analyticPointHodgeDecomposition
#print axioms analyticPointCycleClass
#print axioms semantics
#print axioms realization_hodgeConclusion
#print axioms projectiveZeroTheHodgeConjecture

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveZeroAmbient
