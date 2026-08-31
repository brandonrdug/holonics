import ElementaryHolonics.Millennium.HodgeProjectiveLineScheme
import ElementaryHolonics.Millennium.HodgeProjectiveLineTopology
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# The analytic projective line and the closed points of the exact `Proj`

This file joins the already-constructed analytic projective-line carrier to the genuine
scheme-theoretic `Proj ℂ[X₀,X₁]`.  The first step retains the two algebraic chart currents as
actual `ℂ`-points of the smooth projective carrier.  The intended return is an equivalence between
the quotient-level complex projective line and the closed complex points of that exact scheme,
followed by continuity of its underlying point map from the one-point topology.

No Hodge splitting, cycle class, or universal conclusion is assumed here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped OnePoint

namespace Soma.Holonics.Millennium.HodgeProjectiveLineAnalyticComparison

open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver
open Soma.Holonics.Millennium.HodgeProjectiveSpaceAmbient
open Soma.Holonics.Millennium.HodgeProjectiveLineScheme
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineTopology

attribute [local instance] MvPolynomial.gradedAlgebra

/-- [definition] Evaluate the first affine chart `X₁/X₀` at a complex coordinate. -/
def evaluateFirstChart (coordinate : ℂ) : AwayFirst →+* ℂ :=
  (Polynomial.evalRingHom coordinate).comp awayFirstEquivPolynomial.toRingHom

/-- [definition] Evaluate the second affine chart `X₀/X₁` at a complex coordinate. -/
def evaluateSecondChart (coordinate : ℂ) : AwaySecond →+* ℂ :=
  (Polynomial.evalRingHom coordinate).comp awaySecondEquivPolynomial.toRingHom

/-- [definition] A finite complex coordinate as an actual scheme morphism into the first
standard affine chart of the exact projective line. -/
def firstChartSchemePoint (coordinate : ℂ) : ComplexPoint ⟶ ProjectiveLineScheme :=
  Spec.map (CommRingCat.ofHom (evaluateFirstChart coordinate)) ≫
    Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num)

/-- [definition] A complex coordinate as an actual scheme morphism into the second standard
affine chart of the exact projective line. -/
def secondChartSchemePoint (coordinate : ℂ) : ComplexPoint ⟶ ProjectiveLineScheme :=
  Spec.map (CommRingCat.ofHom (evaluateSecondChart coordinate)) ≫
    Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one (by norm_num)

/-- [proved-standard; formal-checked] The first chart evaluation returns the exact degree-zero
complex coefficient after the declared base rebase. -/
theorem evaluateFirstChart_fromZero (coordinate : ℂ) (coefficient : DegreeZero) :
    evaluateFirstChart coordinate
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers firstCoordinate) coefficient) =
      (degreeZeroEquiv 2) coefficient := by
  rw [evaluateFirstChart, RingHom.comp_apply,
    show awayFirstEquivPolynomial.toRingHom
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers firstCoordinate) coefficient) =
        awayFirstEquivPolynomial
          (HomogeneousLocalization.fromZeroRingHom Grading
            (Submonoid.powers firstCoordinate) coefficient) from rfl,
    awayFirstEquivPolynomial_fromZero]
  simp

/-- [proved-standard; formal-checked] The second chart evaluation returns the exact degree-zero
complex coefficient after the declared base rebase. -/
theorem evaluateSecondChart_fromZero (coordinate : ℂ) (coefficient : DegreeZero) :
    evaluateSecondChart coordinate
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers denominatorCoordinate) coefficient) =
      (degreeZeroEquiv 2) coefficient := by
  rw [evaluateSecondChart, RingHom.comp_apply,
    show awaySecondEquivPolynomial.toRingHom
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers denominatorCoordinate) coefficient) =
        awaySecondEquivPolynomial
          (HomogeneousLocalization.fromZeroRingHom Grading
            (Submonoid.powers denominatorCoordinate) coefficient) from rfl,
    awaySecondEquivPolynomial_fromZero]
  simp

/-- [definition] The actual complex-valued points of the projective-line carrier, retaining the
required equality over its declared `Spec ℂ` receiver. -/
abbrev ProjectiveLineKPoint :=
  {point : ComplexPoint ⟶ ProjectiveLineScheme //
    point ≫ (HodgeProjectiveSpaceAmbient.presentation 2).structureMap = 𝟙 ComplexPoint}

private theorem baseIso_hom_eq :
    (HodgeProjectiveSpaceAmbient.baseIso 2).hom =
      Spec.map (CommRingCat.ofHom (degreeZeroEquiv 2).symm.toRingHom) :=
  rfl

/-- [proved-standard; formal-checked] A first-chart evaluation is a point over the exact complex
base receiver. -/
theorem firstChartSchemePoint_over_base (coordinate : ℂ) :
    firstChartSchemePoint coordinate ≫
        (HodgeProjectiveSpaceAmbient.presentation 2).structureMap =
      𝟙 ComplexPoint := by
  change
    (Spec.map (CommRingCat.ofHom (evaluateFirstChart coordinate)) ≫
          Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num)) ≫
        ((𝟙 ProjectiveLineScheme ≫ Proj.toSpecZero Grading) ≫
          (HodgeProjectiveSpaceAmbient.baseIso 2).hom) =
      𝟙 ComplexPoint
  simp only [Category.id_comp, Category.assoc]
  rw [← Category.assoc
      (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num))
      (Proj.toSpecZero Grading) (HodgeProjectiveSpaceAmbient.baseIso 2).hom,
    Proj.awayι_toSpecZero, baseIso_hom_eq]
  rw [← Spec.map_id, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rw [Spec.map_injective.eq_iff]
  ext coefficient
  simpa using
    evaluateFirstChart_fromZero coordinate ((degreeZeroEquiv 2).symm coefficient)

/-- [proved-standard; formal-checked] A second-chart evaluation is a point over the exact complex
base receiver. -/
theorem secondChartSchemePoint_over_base (coordinate : ℂ) :
    secondChartSchemePoint coordinate ≫
        (HodgeProjectiveSpaceAmbient.presentation 2).structureMap =
      𝟙 ComplexPoint := by
  change
    (Spec.map (CommRingCat.ofHom (evaluateSecondChart coordinate)) ≫
          Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
            (by norm_num)) ≫
        ((𝟙 ProjectiveLineScheme ≫ Proj.toSpecZero Grading) ≫
          (HodgeProjectiveSpaceAmbient.baseIso 2).hom) =
      𝟙 ComplexPoint
  simp only [Category.id_comp, Category.assoc]
  rw [← Category.assoc
      (Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
        (by norm_num))
      (Proj.toSpecZero Grading) (HodgeProjectiveSpaceAmbient.baseIso 2).hom,
    Proj.awayι_toSpecZero, baseIso_hom_eq]
  rw [← Spec.map_id, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rw [Spec.map_injective.eq_iff]
  ext coefficient
  simpa using
    evaluateSecondChart_fromZero coordinate ((degreeZeroEquiv 2).symm coefficient)

/-- [proved-standard; formal-checked] Package a finite analytic coordinate as an actual complex
point of the smooth projective scheme. -/
def firstChartKPoint (coordinate : ℂ) : ProjectiveLineKPoint :=
  ⟨firstChartSchemePoint coordinate, firstChartSchemePoint_over_base coordinate⟩

/-- [proved-standard; formal-checked] Package a second-chart coordinate as an actual complex
point of the smooth projective scheme. -/
def secondChartKPoint (coordinate : ℂ) : ProjectiveLineKPoint :=
  ⟨secondChartSchemePoint coordinate, secondChartSchemePoint_over_base coordinate⟩

/-- [definition] The structure morphism whose sections are the actual complex-valued points of
the projective line. -/
noncomputable abbrev lineStructureMap : ProjectiveLineScheme ⟶ ComplexPoint :=
  (HodgeProjectiveSpaceAmbient.presentation 2).structureMap

noncomputable local instance lineStructureMap_locallyOfFiniteType :
    LocallyOfFiniteType lineStructureMap := by
  haveI : Smooth lineStructureMap := presentation_structureMap_smooth
  infer_instance

/-- [proved-standard; formal-checked] Over the algebraically closed complex receiver, actual
scheme-valued points are exactly the closed points of the genuine projective-line scheme. -/
def kPointEquivClosedPoint :
    ProjectiveLineKPoint ≃ closedPoints ProjectiveLineScheme :=
  AlgebraicGeometry.pointEquivClosedPoint lineStructureMap

/-- [definition] The existing one-point analytic chart sends every finite coordinate through the
first affine current and sends infinity through the origin of the complementary current. -/
def onePointToKPoint (value : OnePoint ℂ) : ProjectiveLineKPoint :=
  value.elim (secondChartKPoint 0) firstChartKPoint

/-- [definition] The quotient-level analytic projective line mapped into the actual complex
scheme-valued points through its exact one-point normal form. -/
def analyticToKPoint (projectivePoint : ComplexProjectiveLine) : ProjectiveLineKPoint :=
  onePointToKPoint (projectiveLineEquivOnePoint projectivePoint)

/-- [definition] The resulting closed point of the genuine algebraic projective line. -/
def analyticToClosedPoint (projectivePoint : ComplexProjectiveLine) :
    closedPoints ProjectiveLineScheme :=
  kPointEquivClosedPoint (analyticToKPoint projectivePoint)

@[simp]
theorem onePointToKPoint_infinity :
    onePointToKPoint (∞ : OnePoint ℂ) = secondChartKPoint 0 :=
  rfl

@[simp]
theorem onePointToKPoint_finite (coordinate : ℂ) :
    onePointToKPoint (coordinate : OnePoint ℂ) = firstChartKPoint coordinate :=
  rfl

/-- [proved-standard; formal-checked] The first affine current retains its complex coordinate;
distinct finite coordinates cannot collapse to one projective scheme point. -/
theorem firstChartSchemePoint_injective : Function.Injective firstChartSchemePoint := by
  intro left right pointsEqual
  have affineMapsEqual :
      Spec.map (CommRingCat.ofHom (evaluateFirstChart left)) =
        Spec.map (CommRingCat.ofHom (evaluateFirstChart right)) := by
    apply (cancel_mono
      (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num))).1
    exact pointsEqual
  rw [Spec.map_injective.eq_iff] at affineMapsEqual
  have evaluationsEqual : evaluateFirstChart left = evaluateFirstChart right := by
    exact congrArg CommRingCat.Hom.hom affineMapsEqual
  have ratioEqual := DFunLike.congr_fun evaluationsEqual
    (awayFirstEquivPolynomial.symm Polynomial.X)
  simpa [evaluateFirstChart] using ratioEqual

/-- [proved-standard; formal-checked] The complementary affine current likewise retains its
complex coordinate. -/
theorem secondChartSchemePoint_injective : Function.Injective secondChartSchemePoint := by
  intro left right pointsEqual
  have affineMapsEqual :
      Spec.map (CommRingCat.ofHom (evaluateSecondChart left)) =
        Spec.map (CommRingCat.ofHom (evaluateSecondChart right)) := by
    apply (cancel_mono
      (Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
        (by norm_num))).1
    exact pointsEqual
  rw [Spec.map_injective.eq_iff] at affineMapsEqual
  have evaluationsEqual : evaluateSecondChart left = evaluateSecondChart right := by
    exact congrArg CommRingCat.Hom.hom affineMapsEqual
  have ratioEqual := DFunLike.congr_fun evaluationsEqual
    (awaySecondEquivPolynomial.symm Polynomial.X)
  simpa [evaluateSecondChart] using ratioEqual

@[simp]
theorem evaluateSecondChart_zero_affineRatio :
    evaluateSecondChart 0 affineRatio = 0 := by
  rw [evaluateSecondChart, RingHom.comp_apply,
    show awaySecondEquivPolynomial.toRingHom affineRatio =
      awaySecondEquivPolynomial affineRatio from rfl,
    show awaySecondEquivPolynomial affineRatio = Polynomial.X by
      exact awaySecondToPolynomial_affineRatio]
  simp

private theorem overlapElement_eq_affineRatio :
    HomogeneousLocalization.Away.isLocalizationElem
        denominatorCoordinate_mem_degree_one firstCoordinate_mem_degree_one =
      affineRatio :=
  by simp [HomogeneousLocalization.Away.isLocalizationElem, affineRatio]

/-- [proved-standard; formal-checked] At the complementary-chart origin, the overlap coordinate
belongs to the pulled-back closed prime. -/
theorem secondEvaluation_not_mem_overlapBasicOpen :
    PrimeSpectrum.comap (evaluateSecondChart 0) (IsLocalRing.closedPoint ℂ) ∉
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          denominatorCoordinate_mem_degree_one firstCoordinate_mem_degree_one) := by
  rw [PrimeSpectrum.mem_basicOpen, not_not, overlapElement_eq_affineRatio,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  rw [evaluateSecondChart_zero_affineRatio]
  exact Ideal.zero_mem _

/-- [proved-standard; formal-checked] Every finite first-chart point lands in the first standard
basic open. -/
theorem firstChartSchemePoint_mem_firstBasicOpen (coordinate : ℂ) :
    firstChartSchemePoint coordinate (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate := by
  let sourcePoint : ComplexPoint := IsLocalRing.closedPoint ℂ
  change firstChartSchemePoint coordinate sourcePoint ∈
    Proj.basicOpen Grading firstCoordinate
  rw [firstChartSchemePoint]
  rw [Scheme.Hom.comp_apply,
    ← Proj.opensRange_awayι Grading firstCoordinate firstCoordinate_mem_degree_one
      (by norm_num)]
  exact ⟨_, rfl⟩

/-- [proved-standard; formal-checked] The origin of the complementary chart is the point at
infinity: it lies outside the first standard basic open. -/
theorem secondChartSchemePoint_zero_not_mem_firstBasicOpen :
    secondChartSchemePoint 0 (IsLocalRing.closedPoint ℂ) ∉
      Proj.basicOpen Grading firstCoordinate := by
  intro pointMem
  let sourcePoint : ComplexPoint := IsLocalRing.closedPoint ℂ
  change secondChartSchemePoint 0 sourcePoint ∈
    Proj.basicOpen Grading firstCoordinate at pointMem
  rw [secondChartSchemePoint, Scheme.Hom.comp_apply] at pointMem
  change
    Spec.map (CommRingCat.ofHom (evaluateSecondChart 0)) sourcePoint ∈
      Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
          (by norm_num) ⁻¹ᵁ Proj.basicOpen Grading firstCoordinate at pointMem
  rw [Proj.awayι_preimage_basicOpen Grading denominatorCoordinate_mem_degree_one
      (by norm_num) firstCoordinate_mem_degree_one (by norm_num)] at pointMem
  exact secondEvaluation_not_mem_overlapBasicOpen pointMem

/-- [proved-standard; formal-checked] The point at infinity and every finite first-chart point are
different actual scheme morphisms. -/
theorem secondChartSchemePoint_zero_ne_first (coordinate : ℂ) :
    secondChartSchemePoint 0 ≠ firstChartSchemePoint coordinate := by
  intro pointsEqual
  apply secondChartSchemePoint_zero_not_mem_firstBasicOpen
  rw [pointsEqual]
  exact firstChartSchemePoint_mem_firstBasicOpen coordinate

/-- [proved-standard; formal-checked] The one-point normal form is retained by the actual
projective scheme-valued point. -/
theorem onePointToKPoint_injective : Function.Injective onePointToKPoint := by
  intro left right pointsEqual
  induction left using OnePoint.rec with
  | infty =>
      induction right using OnePoint.rec with
      | infty => rfl
      | coe coordinate =>
          exfalso
          apply secondChartSchemePoint_zero_ne_first coordinate
          exact congrArg Subtype.val pointsEqual
  | coe leftCoordinate =>
      induction right using OnePoint.rec with
      | infty =>
          exfalso
          apply secondChartSchemePoint_zero_ne_first leftCoordinate
          exact (congrArg Subtype.val pointsEqual).symm
      | coe rightCoordinate =>
          exact congrArg OnePoint.some
            (firstChartSchemePoint_injective (congrArg Subtype.val pointsEqual))

/-- [proved-standard; formal-checked] The quotient-level analytic projective line embeds
injectively into the actual complex-valued points of `Proj ℂ[X₀,X₁]`. -/
theorem analyticToKPoint_injective : Function.Injective analyticToKPoint := by
  intro left right pointsEqual
  apply projectiveLineEquivOnePoint.injective
  exact onePointToKPoint_injective pointsEqual

/-- [proved-standard; formal-checked] Consequently the analytic projective line embeds
injectively into the closed-point receiver of the genuine algebraic projective line. -/
theorem analyticToClosedPoint_injective : Function.Injective analyticToClosedPoint := by
  intro left right pointsEqual
  apply analyticToKPoint_injective
  exact kPointEquivClosedPoint.injective pointsEqual

/-! ## The reverse chart passage -/

/-- [definition] A complex point whose underlying closed point lies in the first basic open has a
unique lift through that affine open immersion. -/
def firstChartLift (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) :
    ComplexPoint ⟶ Spec (.of AwayFirst) :=
  IsOpenImmersion.lift
    (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num))
    point.1 (by
      let closedSource : ComplexPoint := IsLocalRing.closedPoint ℂ
      rintro _ ⟨sourcePoint, rfl⟩
      obtain rfl := Subsingleton.elim sourcePoint closedSource
      have pointInOpen : point.1 closedSource ∈
          Proj.basicOpen Grading firstCoordinate := by
        simpa [closedSource] using memFirst
      have pointInRange : point.1 closedSource ∈
          (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one
            (by norm_num)).opensRange := by
        rw [Proj.opensRange_awayι Grading firstCoordinate firstCoordinate_mem_degree_one
          (by norm_num)]
        exact pointInOpen
      exact pointInRange)

/-- [proved-standard; formal-checked] The affine lift retains its exact factorization through the
projective point. -/
@[reassoc]
theorem firstChartLift_fac (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) :
    firstChartLift point memFirst ≫
        Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num) =
      point.1 :=
  IsOpenImmersion.lift_fac _ _ _

/-- [definition] The ring current presented by the first affine lift. -/
def firstChartLiftRingHom (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) : AwayFirst →+* ℂ :=
  (Spec.preimage (firstChartLift point memFirst)).hom

/-- [proved-standard; formal-checked] The first-chart lift remains a point over the declared
complex base after passing through the degree-zero localization map. -/
theorem firstChartLift_over_base (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) :
    (firstChartLift point memFirst ≫
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom Grading
            (Submonoid.powers firstCoordinate)))) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom =
      𝟙 ComplexPoint := by
  calc
    (firstChartLift point memFirst ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.fromZeroRingHom Grading
              (Submonoid.powers firstCoordinate)))) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom =
      (firstChartLift point memFirst ≫
          (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num) ≫
            Proj.toSpecZero Grading)) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom := by
          rw [Proj.awayι_toSpecZero]
    _ = ((firstChartLift point memFirst ≫
          Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num)) ≫
            Proj.toSpecZero Grading) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom := by
          simp only [Category.assoc]
    _ = (point.1 ≫ Proj.toSpecZero Grading) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom := by
          rw [firstChartLift_fac]
    _ = point.1 ≫ (HodgeProjectiveSpaceAmbient.presentation 2).structureMap := by
          rfl
    _ = 𝟙 ComplexPoint := point.2

/-- [proved-standard; formal-checked] The recovered affine ring current fixes every complex
coefficient after the exact degree-zero rebase. -/
theorem firstChartLift_fromZero (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) (coefficient : DegreeZero) :
    firstChartLiftRingHom point memFirst
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers firstCoordinate) coefficient) =
      (degreeZeroEquiv 2) coefficient := by
  have ringReturn := congrArg
    (fun morphism : ComplexPoint ⟶ ComplexPoint => Spec.preimage morphism)
    (firstChartLift_over_base point memFirst)
  simp only [Spec.preimage_comp, baseIso_hom_eq, Spec.preimage_map,
    Spec.preimage_id] at ringReturn
  have applied := congrArg
    (fun morphism : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ =>
      morphism.hom ((degreeZeroEquiv 2) coefficient)) ringReturn
  simpa [firstChartLiftRingHom] using applied

private theorem awayFirstEquivPolynomial_symm_C (coefficient : ℂ) :
    awayFirstEquivPolynomial.symm (Polynomial.C coefficient) =
      HomogeneousLocalization.fromZeroRingHom Grading
        (Submonoid.powers firstCoordinate) ((degreeZeroEquiv 2).symm coefficient) := by
  apply awayFirstEquivPolynomial.injective
  rw [awayFirstEquivPolynomial.apply_symm_apply,
    awayFirstEquivPolynomial_fromZero]
  simp

/-- [definition] The unique finite coordinate read from the lifted affine ring current. -/
def firstChartRecoveredCoordinate (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) : ℂ :=
  firstChartLiftRingHom point memFirst
    (awayFirstEquivPolynomial.symm Polynomial.X)

/-- [definition] Present the lifted affine current on the polynomial chart. -/
def transportedFirstChartLiftRingHom (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) : Polynomial ℂ →+* ℂ :=
  (firstChartLiftRingHom point memFirst).comp
    awayFirstEquivPolynomial.symm.toRingHom

/-- [proved-standard; formal-checked] Any point over the complex base which factors through the
first affine chart is exactly evaluation at its recovered coordinate. -/
theorem transportedFirstChartLiftRingHom_eq_eval (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) :
    transportedFirstChartLiftRingHom point memFirst =
      Polynomial.evalRingHom (firstChartRecoveredCoordinate point memFirst) := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    rw [transportedFirstChartLiftRingHom, RingHom.comp_apply,
      show awayFirstEquivPolynomial.symm.toRingHom (Polynomial.C coefficient) =
        awayFirstEquivPolynomial.symm (Polynomial.C coefficient) from rfl,
      awayFirstEquivPolynomial_symm_C, firstChartLift_fromZero]
    simp
  · simp [transportedFirstChartLiftRingHom, firstChartRecoveredCoordinate]

/-- [proved-standard; formal-checked] The lifted affine ring current is the exact first-chart
evaluation map. -/
theorem firstChartLiftRingHom_eq_evaluate (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) :
    firstChartLiftRingHom point memFirst =
      evaluateFirstChart (firstChartRecoveredCoordinate point memFirst) := by
  ext fraction
  have evaluated := DFunLike.congr_fun
    (transportedFirstChartLiftRingHom_eq_eval point memFirst)
    (awayFirstEquivPolynomial fraction)
  simpa [transportedFirstChartLiftRingHom, evaluateFirstChart] using evaluated

/-- [proved-standard; formal-checked] The scheme lift itself is the standard evaluation point of
the first affine chart. -/
theorem firstChartLift_eq_evaluation (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) :
    firstChartLift point memFirst =
      Spec.map (CommRingCat.ofHom
        (evaluateFirstChart (firstChartRecoveredCoordinate point memFirst))) := by
  rw [← Spec.map_preimage (firstChartLift point memFirst),
    Spec.map_injective.eq_iff]
  apply CommRingCat.hom_ext
  exact firstChartLiftRingHom_eq_evaluate point memFirst

/-- [proved-standard; formal-checked] Every complex-valued projective point lying in the first
basic open is reconstructed by one unique finite coordinate. -/
theorem eq_firstChartKPoint_of_mem (point : ProjectiveLineKPoint)
    (memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate) :
    point = firstChartKPoint (firstChartRecoveredCoordinate point memFirst) := by
  apply Subtype.ext
  rw [← firstChartLift_fac point memFirst, firstChartLift_eq_evaluation]
  rfl

/-- [definition] The complementary affine lift of a complex point lying in the second standard
basic open. -/
def secondChartLift (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) :
    ComplexPoint ⟶ Spec (.of AwaySecond) :=
  IsOpenImmersion.lift
    (Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
      (by norm_num)) point.1 (by
      let closedSource : ComplexPoint := IsLocalRing.closedPoint ℂ
      rintro _ ⟨sourcePoint, rfl⟩
      obtain rfl := Subsingleton.elim sourcePoint closedSource
      have pointInOpen : point.1 closedSource ∈
          Proj.basicOpen Grading denominatorCoordinate := by
        simpa [closedSource] using memSecond
      have pointInRange : point.1 closedSource ∈
          (Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
            (by norm_num)).opensRange := by
        rw [Proj.opensRange_awayι Grading denominatorCoordinate
          denominatorCoordinate_mem_degree_one (by norm_num)]
        exact pointInOpen
      exact pointInRange)

@[reassoc]
theorem secondChartLift_fac (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) :
    secondChartLift point memSecond ≫
        Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
          (by norm_num) = point.1 :=
  IsOpenImmersion.lift_fac _ _ _

def secondChartLiftRingHom (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) : AwaySecond →+* ℂ :=
  (Spec.preimage (secondChartLift point memSecond)).hom

theorem secondChartLift_over_base (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) :
    (secondChartLift point memSecond ≫
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom Grading
            (Submonoid.powers denominatorCoordinate)))) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom =
      𝟙 ComplexPoint := by
  calc
    (secondChartLift point memSecond ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.fromZeroRingHom Grading
              (Submonoid.powers denominatorCoordinate)))) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom =
      (secondChartLift point memSecond ≫
          (Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
              (by norm_num) ≫ Proj.toSpecZero Grading)) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom := by
          rw [Proj.awayι_toSpecZero]
    _ = ((secondChartLift point memSecond ≫
          Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
            (by norm_num)) ≫ Proj.toSpecZero Grading) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom := by
          simp only [Category.assoc]
    _ = (point.1 ≫ Proj.toSpecZero Grading) ≫
        (HodgeProjectiveSpaceAmbient.baseIso 2).hom := by
          rw [secondChartLift_fac]
    _ = point.1 ≫ (HodgeProjectiveSpaceAmbient.presentation 2).structureMap := by
          rfl
    _ = 𝟙 ComplexPoint := point.2

theorem secondChartLift_fromZero (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) (coefficient : DegreeZero) :
    secondChartLiftRingHom point memSecond
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers denominatorCoordinate) coefficient) =
      (degreeZeroEquiv 2) coefficient := by
  have ringReturn := congrArg
    (fun morphism : ComplexPoint ⟶ ComplexPoint => Spec.preimage morphism)
    (secondChartLift_over_base point memSecond)
  simp only [Spec.preimage_comp, baseIso_hom_eq, Spec.preimage_map,
    Spec.preimage_id] at ringReturn
  have applied := congrArg
    (fun morphism : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ =>
      morphism.hom ((degreeZeroEquiv 2) coefficient)) ringReturn
  simpa [secondChartLiftRingHom] using applied

private theorem awaySecondEquivPolynomial_symm_C (coefficient : ℂ) :
    awaySecondEquivPolynomial.symm (Polynomial.C coefficient) =
      HomogeneousLocalization.fromZeroRingHom Grading
        (Submonoid.powers denominatorCoordinate)
          ((degreeZeroEquiv 2).symm coefficient) := by
  apply awaySecondEquivPolynomial.injective
  rw [awaySecondEquivPolynomial.apply_symm_apply,
    awaySecondEquivPolynomial_fromZero]
  simp

def secondChartRecoveredCoordinate (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) : ℂ :=
  secondChartLiftRingHom point memSecond
    (awaySecondEquivPolynomial.symm Polynomial.X)

def transportedSecondChartLiftRingHom (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) : Polynomial ℂ →+* ℂ :=
  (secondChartLiftRingHom point memSecond).comp
    awaySecondEquivPolynomial.symm.toRingHom

theorem transportedSecondChartLiftRingHom_eq_eval (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) :
    transportedSecondChartLiftRingHom point memSecond =
      Polynomial.evalRingHom (secondChartRecoveredCoordinate point memSecond) := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    rw [transportedSecondChartLiftRingHom, RingHom.comp_apply,
      show awaySecondEquivPolynomial.symm.toRingHom (Polynomial.C coefficient) =
        awaySecondEquivPolynomial.symm (Polynomial.C coefficient) from rfl,
      awaySecondEquivPolynomial_symm_C, secondChartLift_fromZero]
    simp
  · simp [transportedSecondChartLiftRingHom, secondChartRecoveredCoordinate]

theorem secondChartLiftRingHom_eq_evaluate (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) :
    secondChartLiftRingHom point memSecond =
      evaluateSecondChart (secondChartRecoveredCoordinate point memSecond) := by
  ext fraction
  have evaluated := DFunLike.congr_fun
    (transportedSecondChartLiftRingHom_eq_eval point memSecond)
    (awaySecondEquivPolynomial fraction)
  simpa [transportedSecondChartLiftRingHom, evaluateSecondChart] using evaluated

theorem secondChartLift_eq_evaluation (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) :
    secondChartLift point memSecond =
      Spec.map (CommRingCat.ofHom
        (evaluateSecondChart (secondChartRecoveredCoordinate point memSecond))) := by
  rw [← Spec.map_preimage (secondChartLift point memSecond),
    Spec.map_injective.eq_iff]
  apply CommRingCat.hom_ext
  exact secondChartLiftRingHom_eq_evaluate point memSecond

theorem eq_secondChartKPoint_of_mem (point : ProjectiveLineKPoint)
    (memSecond : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate) :
    point = secondChartKPoint (secondChartRecoveredCoordinate point memSecond) := by
  apply Subtype.ext
  rw [← secondChartLift_fac point memSecond, secondChartLift_eq_evaluation]
  rfl

@[simp]
theorem evaluateSecondChart_affineRatio (coordinate : ℂ) :
    evaluateSecondChart coordinate affineRatio = coordinate := by
  rw [evaluateSecondChart, RingHom.comp_apply,
    show awaySecondEquivPolynomial.toRingHom affineRatio =
      awaySecondEquivPolynomial affineRatio from rfl,
    show awaySecondEquivPolynomial affineRatio = Polynomial.X by
      exact awaySecondToPolynomial_affineRatio]
  simp

theorem secondEvaluation_mem_overlapBasicOpen_iff (coordinate : ℂ) :
    PrimeSpectrum.comap (evaluateSecondChart coordinate) (IsLocalRing.closedPoint ℂ) ∈
        PrimeSpectrum.basicOpen
          (HomogeneousLocalization.Away.isLocalizationElem
            denominatorCoordinate_mem_degree_one firstCoordinate_mem_degree_one) ↔
      coordinate ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen, overlapElement_eq_affineRatio,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    evaluateSecondChart_affineRatio]
  have closedPoint_eq_bot :
      IsLocalRing.closedPoint ℂ = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ) :=
    Subsingleton.elim _ _
  rw [closedPoint_eq_bot]
  simp

/-- [proved-standard; formal-checked] A complementary-chart coordinate lies in the first basic
open exactly when it is nonzero. -/
theorem secondChartSchemePoint_mem_firstBasicOpen_iff (coordinate : ℂ) :
    secondChartSchemePoint coordinate (IsLocalRing.closedPoint ℂ) ∈
        Proj.basicOpen Grading firstCoordinate ↔
      coordinate ≠ 0 := by
  let sourcePoint : ComplexPoint := IsLocalRing.closedPoint ℂ
  change secondChartSchemePoint coordinate sourcePoint ∈
      Proj.basicOpen Grading firstCoordinate ↔ coordinate ≠ 0
  rw [secondChartSchemePoint, Scheme.Hom.comp_apply]
  change
    Spec.map (CommRingCat.ofHom (evaluateSecondChart coordinate)) sourcePoint ∈
        Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
            (by norm_num) ⁻¹ᵁ Proj.basicOpen Grading firstCoordinate ↔
      coordinate ≠ 0
  rw [Proj.awayι_preimage_basicOpen Grading denominatorCoordinate_mem_degree_one
    (by norm_num) firstCoordinate_mem_degree_one (by norm_num)]
  exact secondEvaluation_mem_overlapBasicOpen_iff coordinate

/-- [proved-standard; formal-checked] If a projective complex point misses the first basic open,
the two-coordinate cover forces it into the complementary chart. -/
theorem mem_secondBasicOpen_of_not_mem_first (point : ProjectiveLineKPoint)
    (notMemFirst : point.1 (IsLocalRing.closedPoint ℂ) ∉
      Proj.basicOpen Grading firstCoordinate) :
    point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading denominatorCoordinate := by
  have topMem : point.1 (IsLocalRing.closedPoint ℂ) ∈
      (⊤ : ProjectiveLineScheme.Opens) := trivial
  rw [← coordinateBasicOpens_iSup_eq_top 2,
    TopologicalSpace.Opens.mem_iSup] at topMem
  obtain ⟨index, indexMem⟩ := topMem
  fin_cases index
  · exact (notMemFirst indexMem).elim
  · exact indexMem

/-- [proved-standard; formal-checked] The entire complement of the first affine chart is the
single complementary-chart origin. -/
theorem eq_secondChartKPoint_zero_of_not_mem_first (point : ProjectiveLineKPoint)
    (notMemFirst : point.1 (IsLocalRing.closedPoint ℂ) ∉
      Proj.basicOpen Grading firstCoordinate) :
    point = secondChartKPoint 0 := by
  let memSecond := mem_secondBasicOpen_of_not_mem_first point notMemFirst
  let coordinate := secondChartRecoveredCoordinate point memSecond
  have reconstructed : point = secondChartKPoint coordinate :=
    eq_secondChartKPoint_of_mem point memSecond
  have coordinateZero : coordinate = 0 := by
    by_contra coordinateNonzero
    apply notMemFirst
    rw [reconstructed]
    exact (secondChartSchemePoint_mem_firstBasicOpen_iff coordinate).2 coordinateNonzero
  simpa [coordinateZero] using reconstructed

/-- [proved-standard; formal-checked] Every actual complex-valued projective point is reached by
the one-point analytic normal form. -/
theorem onePointToKPoint_surjective : Function.Surjective onePointToKPoint := by
  intro point
  by_cases memFirst : point.1 (IsLocalRing.closedPoint ℂ) ∈
      Proj.basicOpen Grading firstCoordinate
  · let coordinate := firstChartRecoveredCoordinate point memFirst
    refine ⟨(coordinate : OnePoint ℂ), ?_⟩
    simpa [coordinate] using (eq_firstChartKPoint_of_mem point memFirst).symm
  · refine ⟨(∞ : OnePoint ℂ), ?_⟩
    simpa using (eq_secondChartKPoint_zero_of_not_mem_first point memFirst).symm

/-- [proved-standard; formal-checked] The analytic one-point chart is exactly equivalent to the
actual complex-valued points of the projective scheme. -/
def onePointEquivKPoint : OnePoint ℂ ≃ ProjectiveLineKPoint :=
  Equiv.ofBijective onePointToKPoint
    ⟨onePointToKPoint_injective, onePointToKPoint_surjective⟩

/-- [proved-standard; formal-checked] The quotient-level complex projective line is exactly
equivalent to the complex-valued points of the genuine `Proj`. -/
def analyticEquivKPoint : ComplexProjectiveLine ≃ ProjectiveLineKPoint :=
  projectiveLineEquivOnePoint.trans onePointEquivKPoint

/-- [proved-standard; formal-checked] The quotient-level analytic projective line and the closed
points of the genuine algebraic projective line are exactly equivalent. -/
def analyticClosedPointEquiv :
    ComplexProjectiveLine ≃ closedPoints ProjectiveLineScheme :=
  analyticEquivKPoint.trans kPointEquivClosedPoint

/-- [definition] The first affine evaluation as a prime of the exact localized coordinate ring. -/
def firstChartPrimePoint (coordinate : ℂ) : PrimeSpectrum AwayFirst :=
  PrimeSpectrum.comap (evaluateFirstChart coordinate) (IsLocalRing.closedPoint ℂ)

/-- [proved-standard; formal-checked] Membership of a first-chart prime in an affine basic open
is exactly nonvanishing of the transported complex polynomial. -/
theorem firstChartPrimePoint_mem_basicOpen_iff (coordinate : ℂ) (fraction : AwayFirst) :
    firstChartPrimePoint coordinate ∈ PrimeSpectrum.basicOpen fraction ↔
      Polynomial.eval coordinate (awayFirstEquivPolynomial fraction) ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen, firstChartPrimePoint,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have closedPoint_eq_bot :
      (IsLocalRing.closedPoint ℂ).asIdeal = ⊥ :=
    IsLocalRing.maximalIdeal_eq_bot
  rw [closedPoint_eq_bot]
  simp [evaluateFirstChart]

/-- [proved-standard; formal-checked] The affine evaluation current is continuous for the
Zariski topology because every basic open is the nonvanishing locus of one continuous
polynomial. -/
theorem firstChartPrimePoint_continuous : Continuous firstChartPrimePoint := by
  rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
  rintro _ ⟨fraction, rfl⟩
  rw [show firstChartPrimePoint ⁻¹' (PrimeSpectrum.basicOpen fraction : Set _) =
      {coordinate | Polynomial.eval coordinate (awayFirstEquivPolynomial fraction) ≠ 0} by
    ext coordinate
    exact firstChartPrimePoint_mem_basicOpen_iff coordinate fraction]
  exact isOpen_ne.preimage (awayFirstEquivPolynomial fraction).continuous

theorem firstChartUnderlying_eq (coordinate : ℂ) :
    firstChartSchemePoint coordinate (IsLocalRing.closedPoint ℂ) =
      (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num))
        (firstChartPrimePoint coordinate) := by
  rfl

/-- [proved-standard; formal-checked] The finite analytic chart is continuous into the genuine
projective scheme carrier. -/
theorem firstChartUnderlying_continuous :
    Continuous (fun coordinate : ℂ =>
      firstChartSchemePoint coordinate (IsLocalRing.closedPoint ℂ)) := by
  rw [show (fun coordinate : ℂ =>
      firstChartSchemePoint coordinate (IsLocalRing.closedPoint ℂ)) =
      (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num)) ∘
        firstChartPrimePoint by
    funext coordinate
    exact firstChartUnderlying_eq coordinate]
  exact (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one
    (by norm_num)).continuous.comp firstChartPrimePoint_continuous

/-- [definition] The one-point normal form evaluated in the underlying carrier of the exact
projective scheme. -/
def onePointUnderlying (value : OnePoint ℂ) : ProjectiveLineScheme :=
  (onePointToKPoint value).1 (IsLocalRing.closedPoint ℂ)

@[simp]
theorem onePointUnderlying_finite (coordinate : ℂ) :
    onePointUnderlying (coordinate : OnePoint ℂ) =
      firstChartSchemePoint coordinate (IsLocalRing.closedPoint ℂ) :=
  rfl

@[simp]
theorem onePointUnderlying_infinity :
    onePointUnderlying (∞ : OnePoint ℂ) =
      secondChartSchemePoint 0 (IsLocalRing.closedPoint ℂ) :=
  rfl

/-- [definition] The exact first-chart dehomogenization of a homogeneous projective
coordinate occurrence. -/
def firstChartPolynomial {degree : ℕ} (polynomial : CoordinateRing)
    (homogeneous : polynomial ∈ HodgeProjectiveLineScheme.Grading degree) : Polynomial ℂ :=
  awayFirstEquivPolynomial
    (HomogeneousLocalization.Away.isLocalizationElem
      firstCoordinate_mem_degree_one homogeneous)

/-- [proved-standard; formal-checked] The localization chart polynomial is literally the
source-authored first dehomogenization. -/
theorem firstChartPolynomial_eq_dehomogenizeFirst {degree : ℕ}
    (polynomial : CoordinateRing)
    (homogeneous : polynomial ∈ HodgeProjectiveLineScheme.Grading degree) :
    firstChartPolynomial polynomial homogeneous = dehomogenizeFirst polynomial := by
  change awayFirstToPolynomial _ = dehomogenizeFirst polynomial
  simpa [firstChartPolynomial, HomogeneousLocalization.Away.isLocalizationElem] using
    (awayFirstToPolynomial_mk degree polynomial homogeneous)

/-- [proved-standard; formal-checked] On the finite analytic chart, a positive-degree
homogeneous projective basic open pulls back to exact polynomial nonvanishing. -/
theorem onePointUnderlying_finite_mem_homogeneousBasicOpen_iff {degree : ℕ}
    (polynomial : CoordinateRing)
    (homogeneous : polynomial ∈ HodgeProjectiveLineScheme.Grading degree)
    (positiveDegree : 0 < degree) (coordinate : ℂ) :
    onePointUnderlying (coordinate : OnePoint ℂ) ∈ Proj.basicOpen Grading polynomial ↔
      Polynomial.eval coordinate (firstChartPolynomial polynomial homogeneous) ≠ 0 := by
  rw [onePointUnderlying_finite, firstChartUnderlying_eq]
  change firstChartPrimePoint coordinate ∈
      (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one
        (by norm_num)) ⁻¹ᵁ Proj.basicOpen Grading polynomial ↔ _
  rw [Proj.awayι_preimage_basicOpen Grading firstCoordinate_mem_degree_one
    (by norm_num) homogeneous positiveDegree]
  exact firstChartPrimePoint_mem_basicOpen_iff coordinate _

/-- [proved-standard; formal-checked] If a homogeneous projective basic open contains infinity,
its first-chart dehomogenization is nonzero. -/
theorem firstChartPolynomial_ne_zero_of_infinity_mem {degree : ℕ}
    (polynomial : CoordinateRing)
    (homogeneous : polynomial ∈ HodgeProjectiveLineScheme.Grading degree)
    (infinityMem : onePointUnderlying (∞ : OnePoint ℂ) ∈
      Proj.basicOpen Grading polynomial) :
    firstChartPolynomial polynomial homogeneous ≠ 0 := by
  intro polynomialZero
  have dehomogenizedZero : dehomogenizeFirst polynomial = 0 := by
    rw [← firstChartPolynomial_eq_dehomogenizeFirst polynomial homogeneous]
    exact polynomialZero
  have polynomialZero' : polynomial = 0 := by
    apply dehomogenizeFirst_eq_zero_of_homogeneous
    · rw [← MvPolynomial.mem_homogeneousSubmodule]
      exact homogeneous
    · exact dehomogenizedZero
  rw [polynomialZero', Proj.basicOpen_zero] at infinityMem
  exact infinityMem

/-- [proved-standard; formal-checked] Every positive-degree homogeneous projective basic open
has open preimage in the one-point analytic chart.  At infinity its complement is exactly a
closed finite root population, hence compact. -/
theorem onePointUnderlying_preimage_homogeneousBasicOpen_isOpen {degree : ℕ}
    (polynomial : CoordinateRing)
    (homogeneous : polynomial ∈ HodgeProjectiveLineScheme.Grading degree)
    (positiveDegree : 0 < degree) :
    IsOpen (onePointUnderlying ⁻¹' (Proj.basicOpen Grading polynomial : Set _)) := by
  let preimageSet := onePointUnderlying ⁻¹' (Proj.basicOpen Grading polynomial : Set _)
  by_cases infinityMem : (∞ : OnePoint ℂ) ∈ preimageSet
  · rw [OnePoint.isOpen_iff_of_mem infinityMem]
    constructor
    · rw [show ((↑) : ℂ → OnePoint ℂ) ⁻¹' preimageSet =
          {coordinate | Polynomial.eval coordinate
            (firstChartPolynomial polynomial homogeneous) ≠ 0} by
        ext coordinate
        exact onePointUnderlying_finite_mem_homogeneousBasicOpen_iff
          polynomial homogeneous positiveDegree coordinate]
      simp only [Set.compl_ofPred, not_ne_iff]
      exact isClosed_singleton.preimage
        (firstChartPolynomial polynomial homogeneous).continuous
    · rw [show ((↑) : ℂ → OnePoint ℂ) ⁻¹' preimageSet =
          {coordinate | Polynomial.eval coordinate
            (firstChartPolynomial polynomial homogeneous) ≠ 0} by
        ext coordinate
        exact onePointUnderlying_finite_mem_homogeneousBasicOpen_iff
          polynomial homogeneous positiveDegree coordinate]
      simp only [Set.compl_ofPred, not_ne_iff]
      have polynomialNonzero := firstChartPolynomial_ne_zero_of_infinity_mem
        polynomial homogeneous infinityMem
      simpa [Polynomial.IsRoot] using
        (Polynomial.finite_setOfPred_isRoot polynomialNonzero).isCompact
  · rw [OnePoint.isOpen_iff_of_notMem infinityMem]
    rw [show ((↑) : ℂ → OnePoint ℂ) ⁻¹' preimageSet =
        {coordinate | Polynomial.eval coordinate
          (firstChartPolynomial polynomial homogeneous) ≠ 0} by
      ext coordinate
      exact onePointUnderlying_finite_mem_homogeneousBasicOpen_iff
        polynomial homogeneous positiveDegree coordinate]
    exact isOpen_ne.preimage (firstChartPolynomial polynomial homogeneous).continuous

/-- [proved-standard; formal-checked] A degree-zero homogeneous projective basic open is either
empty or the whole carrier; its scalar coordinate has not been treated as an untyped identity. -/
theorem homogeneousDegreeZero_basicOpen_eq_bot_or_top
    (polynomial : CoordinateRing)
    (homogeneous : polynomial ∈ HodgeProjectiveLineScheme.Grading 0) :
    Proj.basicOpen Grading polynomial = ⊥ ∨
      Proj.basicOpen Grading polynomial = ⊤ := by
  let occurrence : DegreeZero := ⟨polynomial, homogeneous⟩
  rw [show polynomial = MvPolynomial.C
      ((HodgeProjectiveSpaceAmbient.degreeZeroEquiv 2) occurrence) by
    exact HodgeProjectiveSpaceAmbient.homogeneous_zero_eq_constant 2 occurrence]
  by_cases coefficientZero :
      (HodgeProjectiveSpaceAmbient.degreeZeroEquiv 2) occurrence = 0
  · left
    simp [coefficientZero]
  · right
    apply TopologicalSpace.Opens.ext
    ext point
    change (MvPolynomial.C
      ((HodgeProjectiveSpaceAmbient.degreeZeroEquiv 2) occurrence) : CoordinateRing) ∉
        point.asHomogeneousIdeal ↔ True
    have unitCoefficient : IsUnit (MvPolynomial.C
        ((HodgeProjectiveSpaceAmbient.degreeZeroEquiv 2) occurrence) : CoordinateRing) :=
      (isUnit_iff_ne_zero.mpr coefficientZero).map MvPolynomial.C
    exact ⟨fun _ => trivial, fun _ coefficientMem =>
      point.isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem point.asHomogeneousIdeal.toIdeal coefficientMem
          unitCoefficient)⟩

/-- [proved-standard; formal-checked] Degree-zero projective basic opens have open analytic
preimage. -/
theorem onePointUnderlying_preimage_degreeZeroBasicOpen_isOpen
    (polynomial : CoordinateRing)
    (homogeneous : polynomial ∈ HodgeProjectiveLineScheme.Grading 0) :
    IsOpen (onePointUnderlying ⁻¹' (Proj.basicOpen Grading polynomial : Set _)) := by
  rcases homogeneousDegreeZero_basicOpen_eq_bot_or_top polynomial homogeneous with h | h
  · rw [h]
    exact isOpen_empty
  · rw [h]
    exact isOpen_univ

/-- [proved-standard; formal-checked] Every homogeneous projection of an arbitrary coordinate
polynomial has open analytic preimage. -/
theorem onePointUnderlying_preimage_projectedBasicOpen_isOpen
    (polynomial : CoordinateRing) (degree : ℕ) :
    IsOpen (onePointUnderlying ⁻¹'
      (Proj.basicOpen Grading (GradedRing.proj Grading degree polynomial) : Set _)) := by
  have homogeneous :
      GradedRing.proj HodgeProjectiveLineScheme.Grading degree polynomial ∈
        HodgeProjectiveLineScheme.Grading degree :=
    (DirectSum.decompose HodgeProjectiveLineScheme.Grading polynomial degree).property
  rcases degree with _ | degree
  · exact onePointUnderlying_preimage_degreeZeroBasicOpen_isOpen _ homogeneous
  · exact onePointUnderlying_preimage_homogeneousBasicOpen_isOpen _ homogeneous (Nat.succ_pos _)

/-- [proved-standard; formal-checked] Every projective basic open, with no homogeneity
assumption on its presenting coordinate polynomial, has open analytic preimage. -/
theorem onePointUnderlying_preimage_basicOpen_isOpen (polynomial : CoordinateRing) :
    IsOpen (onePointUnderlying ⁻¹' (Proj.basicOpen Grading polynomial : Set _)) := by
  rw [Proj.basicOpen_eq_iSup_proj]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.preimage_iUnion]
  exact isOpen_iUnion fun degree =>
    onePointUnderlying_preimage_projectedBasicOpen_isOpen polynomial degree

/-- [proved-standard; formal-checked] The explicit one-point analytic normal form is continuous
into the genuine Zariski projective-line carrier. -/
theorem onePointUnderlying_continuous : Continuous onePointUnderlying := by
  rw [continuous_def]
  intro openSet openSetOpen
  let U : ProjectiveLineScheme.Opens := ⟨openSet, openSetOpen⟩
  obtain ⟨index, polynomial, basisReturn⟩ :=
    (Proj.isBasis_basicOpen Grading).exists_iSup_eq U
  rw [show openSet = (U : Set ProjectiveLineScheme) from rfl, basisReturn]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.preimage_iUnion]
  exact isOpen_iUnion fun i =>
    onePointUnderlying_preimage_basicOpen_isOpen (polynomial i)

theorem analyticToClosedPoint_val_eq (projectivePoint : ComplexProjectiveLine) :
    (analyticToClosedPoint projectivePoint : ProjectiveLineScheme) =
      onePointUnderlying (projectiveLineEquivOnePoint projectivePoint) :=
  rfl

/-- [proved-standard; formal-checked] The quotient-level analytic projective line maps
continuously into the closed-point subspace of the genuine algebraic projective line. -/
theorem analyticToClosedPoint_continuous : Continuous analyticToClosedPoint := by
  apply Continuous.subtype_mk
  let closedSource : ComplexPoint := IsLocalRing.closedPoint ℂ
  change Continuous (fun projectivePoint : ComplexProjectiveLine =>
    (analyticToKPoint projectivePoint).1 closedSource)
  rw [show (fun projectivePoint : ComplexProjectiveLine =>
      (analyticToKPoint projectivePoint).1 closedSource) =
      onePointUnderlying ∘ projectiveLineEquivOnePoint by rfl]
  exact onePointUnderlying_continuous.comp projectiveLineHomeomorphOnePoint.continuous

@[simp]
theorem analyticClosedPointEquiv_apply (projectivePoint : ComplexProjectiveLine) :
    analyticClosedPointEquiv projectivePoint = analyticToClosedPoint projectivePoint :=
  rfl

/-- [proved-standard; formal-checked] The forward function of the exact analytic/closed-point
equivalence is continuous.  No inverse-continuity claim is made: the receiver is the Zariski
closed-point topology. -/
theorem analyticClosedPointEquiv_continuous :
    Continuous (analyticClosedPointEquiv :
      ComplexProjectiveLine → closedPoints ProjectiveLineScheme) := by
  rw [show (analyticClosedPointEquiv :
      ComplexProjectiveLine → closedPoints ProjectiveLineScheme) =
      analyticToClosedPoint by rfl]
  exact analyticToClosedPoint_continuous

section Audit

#print axioms evaluateFirstChart_fromZero
#print axioms evaluateSecondChart_fromZero
#print axioms firstChartSchemePoint_over_base
#print axioms secondChartSchemePoint_over_base
#print axioms kPointEquivClosedPoint
#print axioms onePointToKPoint_infinity
#print axioms onePointToKPoint_finite
#print axioms firstChartSchemePoint_injective
#print axioms secondChartSchemePoint_injective
#print axioms evaluateSecondChart_zero_affineRatio
#print axioms secondEvaluation_not_mem_overlapBasicOpen
#print axioms firstChartSchemePoint_mem_firstBasicOpen
#print axioms secondChartSchemePoint_zero_ne_first
#print axioms onePointToKPoint_injective
#print axioms analyticToKPoint_injective
#print axioms analyticToClosedPoint_injective
#print axioms firstChartLift_fac
#print axioms firstChartLift_over_base
#print axioms firstChartLift_fromZero
#print axioms transportedFirstChartLiftRingHom_eq_eval
#print axioms eq_firstChartKPoint_of_mem
#print axioms secondChartLift_fac
#print axioms secondChartLift_over_base
#print axioms secondChartLift_fromZero
#print axioms transportedSecondChartLiftRingHom_eq_eval
#print axioms eq_secondChartKPoint_of_mem
#print axioms secondChartSchemePoint_mem_firstBasicOpen_iff
#print axioms mem_secondBasicOpen_of_not_mem_first
#print axioms eq_secondChartKPoint_zero_of_not_mem_first
#print axioms onePointToKPoint_surjective
#print axioms onePointEquivKPoint
#print axioms analyticClosedPointEquiv
#print axioms firstChartPrimePoint_continuous
#print axioms onePointUnderlying_preimage_homogeneousBasicOpen_isOpen
#print axioms onePointUnderlying_preimage_basicOpen_isOpen
#print axioms onePointUnderlying_continuous
#print axioms analyticToClosedPoint_continuous
#print axioms analyticClosedPointEquiv_continuous

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineAnalyticComparison
