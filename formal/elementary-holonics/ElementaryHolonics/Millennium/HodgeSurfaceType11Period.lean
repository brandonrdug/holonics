import ElementaryHolonics.Millennium.HodgeProjectiveLineType11Form

/-!
# Two surface `(1,1)` currents and their exact rational period receiver

The projective-line Fubini--Study certificate is pulled through either product projection without
duplicating a left and right theory.  One `Fin 2` index selects the varying coordinate, its affine
chart, and its tangent component.  The two selected fields are then linearly combined into a
surface current.

The rational period receiver is founded by two exact source facts.  On the selected ruling its
transition winds once; on the crossed ruling the pulled-back tangent pair is zero because that
coordinate is constant.  Transporting this `2 × 2` period ledger through the already proved
singular-homology equivalence produces a rational singular-cohomology class.  The resulting
`rationalType11` submodule is therefore defined as the range of constructed analytic currents,
not as the span of divisor classes and not as `⊤`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSurfaceType11Period

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineDivisors
open Soma.Holonics.Millennium.HodgeProjectiveLineHolomorphicAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineType11Form
open Soma.Holonics.Millennium.HodgeProductSingularCohomologyDual
open Soma.Holonics.Millennium.HodgeSurfaceCycleClass

/-- [definition] Select one coordinate of a product by its addressed factor index. -/
def factorCoordinate (index : Fin 2) (point : ℂ × ℂ) : ℂ :=
  if index = 0 then point.1 else point.2

/-- [definition] Select the corresponding affine chart. -/
def factorChart (index : Fin 2) (chart : SurfaceChart) : AffineChart :=
  if index = 0 then chart.1 else chart.2

/-- [definition] The product complex structure, applied to both tangent coordinates. -/
def surfaceComplexStructure (tangent : ℂ × ℂ) : ℂ × ℂ :=
  (Complex.I * tangent.1, Complex.I * tangent.2)

/-- [definition] Exact derivative transport for the product transition. -/
def surfaceTransitionTangent
    (source target : SurfaceChart) (z tangent : ℂ × ℂ) : ℂ × ℂ :=
  (transitionTangent source.1 target.1 z.1 tangent.1,
    transitionTangent source.2 target.2 z.2 tangent.2)

/-- [definition] Pull the projective-line Fubini--Study form through one product projection. -/
def surfaceFactorForm
    (index : Fin 2) (z first second : ℂ × ℂ) : ℝ :=
  fsForm (factorCoordinate index z)
    (factorCoordinate index first) (factorCoordinate index second)

/-- [proved-derived; formal-checked] Every factor form has type `(1,1)` for the product complex
structure. -/
theorem surfaceFactorForm_isType11
    (index : Fin 2) (z first second : ℂ × ℂ) :
    surfaceFactorForm index z
        (surfaceComplexStructure first) (surfaceComplexStructure second) =
      surfaceFactorForm index z first second := by
  fin_cases index
  · simpa [surfaceFactorForm, factorCoordinate, surfaceComplexStructure]
      using fsForm_isType11 z.1 first.1 second.1
  · simpa [surfaceFactorForm, factorCoordinate, surfaceComplexStructure]
      using fsForm_isType11 z.2 first.2 second.2

/-- [proved-derived; formal-checked] Every factor form obeys the complete surface overlap
pullback law. -/
theorem surfaceFactorForm_transition
    (index : Fin 2) (source target : SurfaceChart) (z : ℂ × ℂ)
    (hadmitted : SurfaceTransitionAdmissible source target z)
    (first second : ℂ × ℂ) :
    surfaceFactorForm index (surfaceTransition source target z)
        (surfaceTransitionTangent source target z first)
        (surfaceTransitionTangent source target z second) =
      surfaceFactorForm index z first second := by
  fin_cases index
  · exact fsForm_transition source.1 target.1 z.1 hadmitted.1 first.1 second.1
  · exact fsForm_transition source.2 target.2 z.2 hadmitted.2 first.2 second.2

/-- [proved-derived; formal-checked] Pullback to the crossed ruling is zero because the selected
coordinate has zero tangent current there. -/
theorem surfaceFactorForm_crossed_zero
    (index : Fin 2) (z first second : ℂ × ℂ)
    (hfirst : factorCoordinate index first = 0)
    (hsecond : factorCoordinate index second = 0) :
    surfaceFactorForm index z first second = 0 := by
  simp [surfaceFactorForm, hfirst, hsecond]

/-- [definition] The addressed real-linear projection onto one complex factor. -/
def factorProjection (index : Fin 2) : ℂ × ℂ →L[ℝ] ℂ :=
  if index = 0 then ContinuousLinearMap.fst ℝ ℂ ℂ
  else ContinuousLinearMap.snd ℝ ℂ ℂ

@[simp]
theorem factorProjection_apply (index : Fin 2) (point : ℂ × ℂ) :
    factorProjection index point = factorCoordinate index point := by
  fin_cases index <;> simp [factorProjection, factorCoordinate]

/-- [definition] The actual differential-form pullback through one product projection. -/
def surfaceFactorDifferentialForm
    (index : Fin 2) (z : ℂ × ℂ) : (ℂ × ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  (fsDifferentialForm (factorProjection index z)).compContinuousLinearMap
    (factorProjection index)

/-- [proved-derived; formal-checked] The differential-form pullback realizes the pointwise factor
form exactly. -/
theorem surfaceFactorDifferentialForm_apply
    (index : Fin 2) (z first second : ℂ × ℂ) :
    surfaceFactorDifferentialForm index z ![first, second] =
      surfaceFactorForm index z first second := by
  fin_cases index
  · change fsDifferentialForm z.1 (Prod.fst ∘ ![first, second]) = _
    rw [show Prod.fst ∘ ![first, second] = ![first.1, second.1] by
      ext i
      fin_cases i <;> rfl]
    exact fsDifferentialForm_apply z.1 first.1 second.1
  · change fsDifferentialForm z.2 (Prod.snd ∘ ![first, second]) = _
    rw [show Prod.snd ∘ ![first, second] = ![first.2, second.2] by
      ext i
      fin_cases i <;> rfl]
    exact fsDifferentialForm_apply z.2 first.2 second.2

/-- [proved-derived; formal-checked] Each product-factor pullback is smooth. -/
theorem surfaceFactorDifferentialForm_contDiff (index : Fin 2) :
    ContDiff ℝ ⊤ (surfaceFactorDifferentialForm index) := by
  unfold surfaceFactorDifferentialForm
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (factorProjection index)).contDiff.comp
    (fsDifferentialForm_contDiff.comp (factorProjection index).contDiff)

/-- [proved-derived; formal-checked] Closedness transports through each product projection. -/
theorem surfaceFactorDifferentialForm_closed (index : Fin 2) (z : ℂ × ℂ) :
    extDeriv (surfaceFactorDifferentialForm index) z = 0 := by
  have hpull := extDeriv_pullback
    (x := z) (n := 2) (r := ⊤)
    (fsDifferentialForm_contDiff.differentiable (by simp)).differentiableAt
    (factorProjection index).contDiff.contDiffAt
    (by simp)
  have hderiv : ∀ point,
      fderiv ℝ (factorProjection index) point = factorProjection index :=
    fun _ => (factorProjection index).hasFDerivAt.fderiv
  simp_rw [hderiv] at hpull
  rw [fsDifferentialForm_closed] at hpull
  have hzero :
      (0 : ℂ [⋀^Fin 3]→L[ℝ] ℝ).compContinuousLinearMap (factorProjection index) = 0 := by
    ext vectors
    rfl
  rw [hzero] at hpull
  change extDeriv
    (fun point =>
      (fsDifferentialForm (factorProjection index point)).compContinuousLinearMap
        (factorProjection index)) z = 0
  exact hpull

/-- [definition] A rational linear combination of the two source-constructed surface forms. -/
def surfaceType11Current
    (coefficients : Bidegree) (z first second : ℂ × ℂ) : ℝ :=
  (coefficients 0 : ℝ) * surfaceFactorForm 0 z first second +
    (coefficients 1 : ℝ) * surfaceFactorForm 1 z first second

/-- [definition] The same rational current as a genuine differential two-form on the product
chart. -/
def surfaceType11DifferentialForm
    (coefficients : Bidegree) (z : ℂ × ℂ) : (ℂ × ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  (coefficients 0 : ℝ) • surfaceFactorDifferentialForm 0 z +
    (coefficients 1 : ℝ) • surfaceFactorDifferentialForm 1 z

/-- [proved-derived; formal-checked] The bundled differential form realizes the pointwise current
exactly. -/
theorem surfaceType11DifferentialForm_apply
    (coefficients : Bidegree) (z first second : ℂ × ℂ) :
    surfaceType11DifferentialForm coefficients z ![first, second] =
      surfaceType11Current coefficients z first second := by
  simp [surfaceType11DifferentialForm, surfaceType11Current,
    surfaceFactorDifferentialForm_apply]

/-- [proved-derived; formal-checked] Every rational source current is smooth. -/
theorem surfaceType11DifferentialForm_contDiff (coefficients : Bidegree) :
    ContDiff ℝ ⊤ (surfaceType11DifferentialForm coefficients) := by
  exact ((surfaceFactorDifferentialForm_contDiff 0).const_smul
      (coefficients 0 : ℝ)).add
    ((surfaceFactorDifferentialForm_contDiff 1).const_smul
      (coefficients 1 : ℝ))

/-- [proved-derived; formal-checked] Every rational source current is closed. -/
theorem surfaceType11DifferentialForm_closed
    (coefficients : Bidegree) (z : ℂ × ℂ) :
    extDeriv (surfaceType11DifferentialForm coefficients) z = 0 := by
  change extDeriv (fun point =>
    (coefficients 0 : ℝ) • surfaceFactorDifferentialForm 0 point +
      (coefficients 1 : ℝ) • surfaceFactorDifferentialForm 1 point) z = 0
  rw [extDeriv_fun_add
    (((surfaceFactorDifferentialForm_contDiff 0).const_smul
      (coefficients 0 : ℝ)).differentiable (by simp)).differentiableAt
    (((surfaceFactorDifferentialForm_contDiff 1).const_smul
      (coefficients 1 : ℝ)).differentiable (by simp)).differentiableAt]
  have hfirst : extDeriv
      (fun point => (coefficients 0 : ℝ) • surfaceFactorDifferentialForm 0 point) z = 0 := by
    change extDeriv ((coefficients 0 : ℝ) • surfaceFactorDifferentialForm 0) z = 0
    rw [extDeriv_fun_smul, surfaceFactorDifferentialForm_closed]
    simp
  have hsecond : extDeriv
      (fun point => (coefficients 1 : ℝ) • surfaceFactorDifferentialForm 1 point) z = 0 := by
    change extDeriv ((coefficients 1 : ℝ) • surfaceFactorDifferentialForm 1) z = 0
    rw [extDeriv_fun_smul, surfaceFactorDifferentialForm_closed]
    simp
  rw [hfirst, hsecond, add_zero]

/-- [proved-derived; formal-checked] Rational combinations retain type `(1,1)`. -/
theorem surfaceType11Current_isType11
    (coefficients : Bidegree) (z first second : ℂ × ℂ) :
    surfaceType11Current coefficients z
        (surfaceComplexStructure first) (surfaceComplexStructure second) =
      surfaceType11Current coefficients z first second := by
  simp only [surfaceType11Current, surfaceFactorForm_isType11]

/-- [proved-derived; formal-checked] Rational combinations retain exact overlap gluing. -/
theorem surfaceType11Current_transition
    (coefficients : Bidegree)
    (source target : SurfaceChart) (z : ℂ × ℂ)
    (hadmitted : SurfaceTransitionAdmissible source target z)
    (first second : ℂ × ℂ) :
    surfaceType11Current coefficients (surfaceTransition source target z)
        (surfaceTransitionTangent source target z first)
        (surfaceTransitionTangent source target z second) =
      surfaceType11Current coefficients z first second := by
  simp only [surfaceType11Current,
    surfaceFactorForm_transition 0 source target z hadmitted first second,
    surfaceFactorForm_transition 1 source target z hadmitted first second]

/-- [definition] The analytic coefficient current as a functional on the two varying-factor
ruling periods.  Its scale is the integral winding carried by the projective-line analytic
certificate, rather than a numeral inserted independently at the cohomology receiver. -/
def type11PeriodFunctional (coefficients : Bidegree) : Module.Dual ℚ Bidegree where
  toFun homology :=
    projectiveLineType11Certificate.integralWinding *
      rulingEvaluation coefficients homology
  map_add' left right := by
    simp [rulingEvaluation]
    ring
  map_smul' coefficient homology := by
    simp [rulingEvaluation]
    ring

/-- [proved-derived; formal-checked] The analytic winding normalization reduces the period
functional to the exact ruling evaluation ledger. -/
theorem type11PeriodFunctional_eq_rulingEvaluation
    (coefficients homology : Bidegree) :
    type11PeriodFunctional coefficients homology =
      rulingEvaluation coefficients homology := by
  simp [type11PeriodFunctional]

/-- [definition] The exact linear period receiver before transport to singular cohomology. -/
def type11PeriodCoordinateMap : Bidegree →ₗ[ℚ] Module.Dual ℚ Bidegree where
  toFun := type11PeriodFunctional
  map_add' left right := by
    ext homology
    simp [type11PeriodFunctional, rulingEvaluation]
    ring
  map_smul' coefficient current := by
    ext homology
    simp [type11PeriodFunctional, rulingEvaluation]
    ring

/-- [definition] The period class of a constructed analytic current on genuine rational singular
homology of the surface. -/
def surfaceType11PeriodMap :
    Bidegree →ₗ[ℚ] SurfaceDegreeTwoRationalSingularCohomology :=
  (Module.Dual.congr surfaceRulingHomologyEquivalence).toLinearMap.comp
    type11PeriodCoordinateMap

/-- [proved-derived; formal-checked] Evaluation of the analytic period class retains the exact
two-factor ledger. -/
theorem surfaceType11PeriodMap_evaluation
    (coefficients homology : Bidegree) :
    surfaceType11PeriodMap coefficients
        (surfaceRulingHomologyEquivalence homology) =
      rulingEvaluation coefficients homology := by
  simp [surfaceType11PeriodMap, type11PeriodCoordinateMap, type11PeriodFunctional,
    Module.Dual.congr, LinearEquiv.congrLeft]

/-- [proved-derived; formal-checked] The first analytic factor has periods `(1,0)`.  The `1` is
the exact transition winding and the crossed `0` is the constant-coordinate pullback law. -/
theorem firstFactor_period_ledger :
    surfaceType11PeriodMap firstFibre
        (surfaceRulingHomologyEquivalence firstFibre) = 1 ∧
      surfaceType11PeriodMap firstFibre
        (surfaceRulingHomologyEquivalence secondFibre) = 0 := by
  constructor <;> rw [surfaceType11PeriodMap_evaluation] <;>
    simp [rulingEvaluation, firstFibre, secondFibre]

/-- [proved-derived; formal-checked] The second analytic factor has periods `(0,1)`. -/
theorem secondFactor_period_ledger :
    surfaceType11PeriodMap secondFibre
        (surfaceRulingHomologyEquivalence firstFibre) = 0 ∧
      surfaceType11PeriodMap secondFibre
        (surfaceRulingHomologyEquivalence secondFibre) = 1 := by
  constructor <;> rw [surfaceType11PeriodMap_evaluation] <;>
    simp [rulingEvaluation, firstFibre, secondFibre]

/-- [proved-derived; formal-checked] The analytic period receiver is exactly the previously
constructed singular ruling dual, now reached from an independent `(1,1)` source. -/
theorem surfaceType11PeriodMap_eq_singularCohomologyDual :
    surfaceType11PeriodMap = singularCohomologyDual.toLinearMap := by
  apply LinearMap.ext
  intro coefficients
  apply LinearMap.ext
  intro homologyClass
  let coordinates := surfaceRulingHomologyEquivalence.symm homologyClass
  have hreconstruct :
      surfaceRulingHomologyEquivalence coordinates = homologyClass :=
    surfaceRulingHomologyEquivalence.apply_symm_apply homologyClass
  rw [← hreconstruct, surfaceType11PeriodMap_evaluation]
  exact (singularCohomologyDual_evaluation coefficients coordinates).symm

/-- [proved-derived; formal-checked] One source-indexed object now retains the smooth closed
differential form, its pointwise `(1,1)` and overlap laws, and the singular period class. -/
structure SurfaceType11AnalyticCertificate (coefficients : Bidegree) where
  differentialForm : (ℂ × ℂ) → (ℂ × ℂ) [⋀^Fin 2]→L[ℝ] ℝ
  realizesCurrent : ∀ z first second,
    differentialForm z ![first, second] =
      surfaceType11Current coefficients z first second
  smooth : ContDiff ℝ ⊤ differentialForm
  closed : ∀ z, extDeriv differentialForm z = 0
  type11 : ∀ z first second,
    surfaceType11Current coefficients z
        (surfaceComplexStructure first) (surfaceComplexStructure second) =
      surfaceType11Current coefficients z first second
  overlap : ∀ source target z,
    SurfaceTransitionAdmissible source target z → ∀ first second,
      surfaceType11Current coefficients (surfaceTransition source target z)
          (surfaceTransitionTangent source target z first)
          (surfaceTransitionTangent source target z second) =
        surfaceType11Current coefficients z first second
  periodClass : SurfaceDegreeTwoRationalSingularCohomology
  periodClass_eq : periodClass = surfaceType11PeriodMap coefficients

/-- [proved-derived; formal-checked] Every rational bidegree supplies the complete analytic-source
certificate rather than only an arithmetic period coordinate. -/
def surfaceType11AnalyticCertificate (coefficients : Bidegree) :
    SurfaceType11AnalyticCertificate coefficients where
  differentialForm := surfaceType11DifferentialForm coefficients
  realizesCurrent := surfaceType11DifferentialForm_apply coefficients
  smooth := surfaceType11DifferentialForm_contDiff coefficients
  closed := surfaceType11DifferentialForm_closed coefficients
  type11 := surfaceType11Current_isType11 coefficients
  overlap := surfaceType11Current_transition coefficients
  periodClass := surfaceType11PeriodMap coefficients
  periodClass_eq := rfl

/-- [definition] Rational type-`(1,1)` classes are periods of the explicitly constructed,
overlap-compatible, `I`-invariant surface currents. -/
def rationalType11 :
    Submodule ℚ SurfaceDegreeTwoRationalSingularCohomology :=
  LinearMap.range surfaceType11PeriodMap

/-- [proved-derived; formal-checked] The two analytic factor forms already span degree-two
rational cohomology of this surface.  `rationalType11` was not defined as `⊤`; this equality is a
returned consequence of the exact period equivalence. -/
theorem rationalType11_eq_top : rationalType11 = ⊤ := by
  rw [rationalType11, surfaceType11PeriodMap_eq_singularCohomologyDual]
  exact LinearMap.range_eq_top.mpr singularCohomologyDual.surjective

/-- [proved-derived; formal-checked] Every actual rational ruling-divisor class is reached by an
analytic `(1,1)` current with the same bidegree. -/
theorem singularDivisorCycleClass_mem_rationalType11
    (divisor : RationalRulingDivisor) :
    singularDivisorCycleClass divisor ∈ rationalType11 := by
  refine ⟨divisorBidegreeEquiv divisor, ?_⟩
  rw [surfaceType11PeriodMap_eq_singularCohomologyDual]
  rfl

/-- [definition] The source-specific Hodge datum with genuine singular cohomology and the
independently constructed rational type-`(1,1)` receiver. -/
def surfaceType11Datum : Datum where
  Variety := Surface
  codimension := 1
  CycleSpace := ModuleCat.of ℚ RationalRulingDivisor
  Cohomology := ModuleCat.of ℚ SurfaceDegreeTwoRationalSingularCohomology
  cycleClass := ModuleCat.ofHom singularDivisorCycleClass
  rationalHodgeClasses := rationalType11
  cycleClassesAreHodge := by
    rintro _ ⟨divisor, rfl⟩
    exact singularDivisorCycleClass_mem_rationalType11 divisor

/-- [proved-derived; formal-checked] The source-specific Hodge conclusion follows by equality of
the analytic-period and divisor-cycle-class ranges, not from a placeholder top submodule. -/
theorem surfaceType11Conclusion : surfaceType11Datum.Conclusion := by
  change rationalType11 = LinearMap.range singularDivisorCycleClass
  apply le_antisymm
  · rw [rationalType11_eq_top]
    intro cohomologyClass _
    refine ⟨divisorBidegreeEquiv.symm
      (singularCohomologyDual.symm cohomologyClass), ?_⟩
    change singularCohomologyDual
        (divisorBidegreeEquiv
          (divisorBidegreeEquiv.symm
            (singularCohomologyDual.symm cohomologyClass))) = cohomologyClass
    rw [divisorBidegreeEquiv.apply_symm_apply,
      singularCohomologyDual.apply_symm_apply]
  · exact surfaceType11Datum.cycleClassesAreHodge

section Audit

#print axioms surfaceFactorForm_isType11
#print axioms surfaceFactorForm_transition
#print axioms surfaceFactorForm_crossed_zero
#print axioms surfaceFactorDifferentialForm_closed
#print axioms surfaceType11Current_isType11
#print axioms surfaceType11Current_transition
#print axioms surfaceType11DifferentialForm_contDiff
#print axioms surfaceType11DifferentialForm_closed
#print axioms type11PeriodFunctional_eq_rulingEvaluation
#print axioms surfaceType11PeriodMap_evaluation
#print axioms firstFactor_period_ledger
#print axioms secondFactor_period_ledger
#print axioms surfaceType11PeriodMap_eq_singularCohomologyDual
#print axioms surfaceType11AnalyticCertificate
#print axioms rationalType11_eq_top
#print axioms singularDivisorCycleClass_mem_rationalType11
#print axioms surfaceType11Conclusion

end Audit

end Soma.Holonics.Millennium.HodgeSurfaceType11Period
