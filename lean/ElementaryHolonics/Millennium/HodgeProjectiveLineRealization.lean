import ElementaryHolonics.Foundation.CycleFilling
import ElementaryHolonics.Millennium.HodgeProjectiveLineAnalyticComparison
import ElementaryHolonics.Millennium.HodgeSphereLowDegreeHomology
import ElementaryHolonics.Millennium.HodgeSphereHomologyEquivalence
import Mathlib.RingTheory.KrullDimension.PID

/-!
# Genuine projective-line cycle currents and reduction-parametrized Hodge realization

The exact analytic/Zariski comparison now meets actual algebraic-cycle sources.  Properness makes
the underlying projective-line scheme compact.  Consequently every locally finite algebraic cycle
has finite support, and its complete coefficient sum is a genuine integral linear current.  Exact
tensor rationalization turns that current into a rational degree map without replacing the source
by a synthetic coordinate module.

Two explicitly addressed source occurrences show that this current reaches every rational
coefficient in the Hodge-relevant degrees:

* the generic point of the first affine chart has coheight zero and supplies the codimension-zero
  fundamental cycle; and
* the origin of that chart has coheight one and supplies an actual closed-point divisor cycle.

The established homeomorphism `ℙ¹(ℂ) ≃ S²` then transports the exact rational `H₀` and `H₂`
calculations to the analytic projective line.  Dualizing gives genuine Betti-cohomology receivers,
and the two algebraic-cycle currents surject onto them.  A complete middle-only pure Hodge
decomposition is also constructed for any addressed even-degree receiver.

This file closes the genuine source/cycle passage in codimensions zero and one, proves that every
scheme point has coheight at most one, and therefore proves that every higher integral and rational
cycle source vanishes.  The minimal remaining analytic obligation is not a complete chain model:
it is a retained filling current for every closed singular chain in each higher even degree.  The
generic `CycleFilling` owner proves that precisely this data annihilates the addressed homology.
Given that family of fillings, the file packages a complete `HodgeSemantics`, `Realization`, and
source-indexed official conclusion in every codimension.  The older all-degree tetrahedral
`HomotopyEquiv` remains as a strictly stronger sufficient route.  Neither conditional package is
an unconditional proof of the classical Hodge conjecture: constructing the higher-even filling
family is the explicit remaining projective-line fibre.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

namespace Soma.Holonics.Millennium.HodgeProjectiveLineRealization

open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver
open Soma.Holonics.Millennium.HodgeProjectiveSpaceAmbient
open Soma.Holonics.Millennium.HodgeProjectiveLineScheme
open Soma.Holonics.Millennium.HodgeProjectiveLineAnalyticComparison
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineTopology
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeSphereLowDegreeHomology
open Soma.Holonics.Millennium.HodgeSphereHomologyEquivalence
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Foundation

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Compact support and the exact coefficient current -/

/-- [proved-standard; formal-checked] Properness over the noetherian complex point returns a
compact underlying Zariski carrier for the genuine projective line. -/
noncomputable local instance projectiveLineSchemeCompactSpace :
    CompactSpace ProjectiveLineScheme :=
  (quasiCompact_iff_compactSpace
    (HodgeProjectiveSpaceAmbient.presentation 2).structureMap).mp inferInstance

/-- [proved-standard; formal-checked] Every genuine algebraic cycle on the proper projective line
has finite support.  This uses compactness and the defining locally-finite support testimony; no
finite source population is postulated. -/
theorem algebraicCycle_support_finite
    (cycle : AlgebraicCycle ProjectiveLineScheme ℤ) :
    cycle.support.Finite := by
  rw [← Set.univ_inter cycle.support]
  exact cycle.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ

/-- [proved-standard; formal-checked] Sum all addressed integral coefficients of one genuine
codimension-`p` algebraic cycle.  Finite support makes addition and signed scaling exact. -/
noncomputable def integralCycleTotal (p : ℕ) :
    IntegralCodimensionCycles ProjectiveLineScheme p →ₗ[ℤ] ℤ where
  toFun cycle := ∑ᶠ point,
    (cycle : AlgebraicCycle ProjectiveLineScheme ℤ) point
  map_add' left right := by
    exact finsum_add_distrib
      (algebraicCycle_support_finite
        (left : AlgebraicCycle ProjectiveLineScheme ℤ))
      (algebraicCycle_support_finite
        (right : AlgebraicCycle ProjectiveLineScheme ℤ))
  map_smul' coefficient cycle := by
    exact ((DistribSMul.toAddMonoidHom ℤ coefficient).map_finsum
      (algebraicCycle_support_finite
        (cycle : AlgebraicCycle ProjectiveLineScheme ℤ))).symm

/-- [proved-standard; formal-checked] Rationalize the complete integral coefficient current
through the actual tensor-product source. -/
noncomputable def rationalCycleTotal (p : ℕ) :
    RationalCodimensionCycles ProjectiveLineScheme p →ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.map
      (LinearMap.id (R := ℚ) (M := ℚ)) (integralCycleTotal p))

/-! ## Exact codimension-zero and codimension-one source occurrences -/

noncomputable local instance awayFirstIsDomain : IsDomain AwayFirst :=
  awayFirstEquivPolynomial.isDomain_iff.mpr inferInstance

/-- [definition] The generic prime of the exact first affine chart. -/
noncomputable def firstChartGenericPoint : Spec (.of AwayFirst) :=
  ⟨⊥, Ideal.isPrime_bot⟩

/-- [definition] The first-chart generic point transported into the genuine projective scheme. -/
noncomputable def projectiveLineGenericPoint : ProjectiveLineScheme :=
  (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num))
    firstChartGenericPoint

/-- [proved-standard; formal-checked] The transported generic occurrence has exact coheight zero. -/
theorem projectiveLineGenericPoint_coheight :
    Order.coheight projectiveLineGenericPoint = 0 := by
  rw [projectiveLineGenericPoint, coheight_eq_of_isOpenImmersion]
  rw [← idealHeight_eq_coheight]
  exact Ideal.height_bot

/-- [proved-standard; formal-checked] Evaluation at the chart origin is onto the complex
coefficient field. -/
theorem evaluateFirstChart_surjective :
    Function.Surjective (evaluateFirstChart 0) := by
  exact (Polynomial.eval_surjective (R := ℂ) 0).comp
    awayFirstEquivPolynomial.surjective

/-- [proved-standard; formal-checked] The chart-origin prime is maximal. -/
theorem firstChartPrimePoint_zero_ideal_isMaximal :
    (firstChartPrimePoint 0).asIdeal.IsMaximal := by
  rw [firstChartPrimePoint, PrimeSpectrum.comap_asIdeal]
  have closedPoint_eq_bot :
      (IsLocalRing.closedPoint ℂ).asIdeal = ⊥ :=
    IsLocalRing.maximalIdeal_eq_bot
  rw [closedPoint_eq_bot]
  exact RingHom.ker_isMaximal_of_surjective (evaluateFirstChart 0)
    evaluateFirstChart_surjective

noncomputable local instance awayFirstIsPrincipalIdealRing :
    IsPrincipalIdealRing AwayFirst :=
  IsPrincipalIdealRing.of_surjective
    awayFirstEquivPolynomial.symm.toRingHom
    awayFirstEquivPolynomial.symm.surjective

noncomputable local instance awaySecondIsDomain : IsDomain AwaySecond :=
  awaySecondEquivPolynomial.isDomain_iff.mpr inferInstance

noncomputable local instance awaySecondIsPrincipalIdealRing :
    IsPrincipalIdealRing AwaySecond :=
  IsPrincipalIdealRing.of_surjective
    awaySecondEquivPolynomial.symm.toRingHom
    awaySecondEquivPolynomial.symm.surjective

/-- [proved-standard; formal-checked] The chart-origin prime has exact coheight one. -/
theorem firstChartPrimePoint_zero_coheight :
    Order.coheight
      (show Spec (.of AwayFirst) from firstChartPrimePoint 0) = 1 := by
  rw [← idealHeight_eq_coheight]
  letI : (firstChartPrimePoint 0).asIdeal.IsMaximal :=
    firstChartPrimePoint_zero_ideal_isMaximal
  exact IsPrincipalIdealRing.height_eq_one_of_isMaximal
    (firstChartPrimePoint 0).asIdeal
    (by
      intro h
      exact Polynomial.not_isField ℂ
        (awayFirstEquivPolynomial.symm.toMulEquiv.isField h))

/-- [definition] The origin of the first analytic chart as an underlying point of the genuine
projective scheme. -/
noncomputable def projectiveLineClosedPoint : ProjectiveLineScheme :=
  firstChartSchemePoint 0 (IsLocalRing.closedPoint ℂ)

/-- [proved-standard; formal-checked] The addressed chart origin is a genuine coheight-one
closed-point source. -/
theorem projectiveLineClosedPoint_coheight :
    Order.coheight projectiveLineClosedPoint = 1 := by
  rw [projectiveLineClosedPoint, firstChartUnderlying_eq]
  change Order.coheight
      ((Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one (by norm_num))
        (show Spec (.of AwayFirst) from firstChartPrimePoint 0)) = 1
  rw [coheight_eq_of_isOpenImmersion]
  exact firstChartPrimePoint_zero_coheight

/-! ## Exact global dimension and higher-source collapse -/

/-- [proved-standard; formal-checked] Every point of the genuine projective line has coheight at
most one.  The two projective coordinate opens cover the carrier; on either exact affine chart,
coheight is ideal height and the polynomial/PID chart has Krull dimension at most one. -/
theorem projectiveLine_coheight_le_one
    (point : ProjectiveLineScheme) : Order.coheight point ≤ 1 := by
  have topMem : point ∈ (⊤ : ProjectiveLineScheme.Opens) := trivial
  rw [← coordinateBasicOpens_iSup_eq_top 2,
    TopologicalSpace.Opens.mem_iSup] at topMem
  obtain ⟨index, indexMem⟩ := topMem
  fin_cases index
  · have pointInRange : point ∈
        (Proj.awayι Grading firstCoordinate firstCoordinate_mem_degree_one
          (by norm_num)).opensRange := by
      rw [Proj.opensRange_awayι]
      exact indexMem
    obtain ⟨chartPoint, chartPoint_eq⟩ := pointInRange
    rw [← chartPoint_eq, coheight_eq_of_isOpenImmersion]
    rw [← idealHeight_eq_coheight]
    letI : chartPoint.asIdeal.IsPrime := chartPoint.2
    have heightBound : chartPoint.asIdeal.height ≤ ringKrullDim AwayFirst :=
      Ideal.height_le_ringKrullDim_of_isPrime (I := chartPoint.asIdeal)
    have chartDimension : ringKrullDim AwayFirst ≤ (1 : WithBot ℕ∞) :=
      (Ring.krullDimLE_iff).mp inferInstance
    exact_mod_cast heightBound.trans chartDimension
  · have pointInRange : point ∈
        (Proj.awayι Grading denominatorCoordinate denominatorCoordinate_mem_degree_one
          (by norm_num)).opensRange := by
      rw [Proj.opensRange_awayι]
      exact indexMem
    obtain ⟨chartPoint, chartPoint_eq⟩ := pointInRange
    rw [← chartPoint_eq, coheight_eq_of_isOpenImmersion]
    rw [← idealHeight_eq_coheight]
    letI : chartPoint.asIdeal.IsPrime := chartPoint.2
    have heightBound : chartPoint.asIdeal.height ≤ ringKrullDim AwaySecond :=
      Ideal.height_le_ringKrullDim_of_isPrime (I := chartPoint.asIdeal)
    have chartDimension : ringKrullDim AwaySecond ≤ (1 : WithBot ℕ∞) :=
      (Ring.krullDimLE_iff).mp inferInstance
    exact_mod_cast heightBound.trans chartDimension

/-- [proved-standard; formal-checked] A genuine integral cycle whose declared codimension is at
least two has no supported occurrence on the one-dimensional projective carrier. -/
theorem integralCodimensionCycles_eq_zero_of_two_le
    {p : ℕ} (two_le : 2 ≤ p)
    (cycle : IntegralCodimensionCycles ProjectiveLineScheme p) : cycle = 0 := by
  apply Subtype.ext
  ext point
  by_cases coefficientZero :
      (cycle : AlgebraicCycle ProjectiveLineScheme ℤ) point = 0
  · exact coefficientZero
  · have coheightBound := projectiveLine_coheight_le_one point
    have declaredCodimension := cycle.property point coefficientZero
    have p_le_one : p ≤ 1 := by
      exact_mod_cast (declaredCodimension ▸ coheightBound)
    omega

/-- [proved-standard; formal-checked] Integral cycle populations in codimension at least two are
the singleton zero population. -/
theorem integralCodimensionCycles_subsingleton_of_two_le
    {p : ℕ} (two_le : 2 ≤ p) :
    Subsingleton (IntegralCodimensionCycles ProjectiveLineScheme p) := by
  constructor
  intro left right
  rw [integralCodimensionCycles_eq_zero_of_two_le two_le left,
    integralCodimensionCycles_eq_zero_of_two_le two_le right]

/-- [proved-standard; formal-checked] Exact tensor rationalization cannot manufacture a higher
codimension source after the complete integral source has collapsed. -/
theorem rationalCodimensionCycles_eq_zero_of_two_le
    {p : ℕ} (two_le : 2 ≤ p)
    (cycle : RationalCodimensionCycles ProjectiveLineScheme p) : cycle = 0 := by
  letI : Subsingleton (IntegralCodimensionCycles ProjectiveLineScheme p) :=
    integralCodimensionCycles_subsingleton_of_two_le two_le
  refine TensorProduct.induction_on cycle rfl ?_ ?_
  · intro coefficient integralCycle
    rw [Subsingleton.elim integralCycle 0, TensorProduct.tmul_zero]
  · intro left right leftZero rightZero
    rw [leftZero, rightZero, add_zero]

/-- [proved-standard; formal-checked] Rational cycle populations in codimension at least two are
the singleton zero population. -/
theorem rationalCodimensionCycles_subsingleton_of_two_le
    {p : ℕ} (two_le : 2 ≤ p) :
    Subsingleton (RationalCodimensionCycles ProjectiveLineScheme p) := by
  constructor
  intro left right
  rw [rationalCodimensionCycles_eq_zero_of_two_le two_le left,
    rationalCodimensionCycles_eq_zero_of_two_le two_le right]

/-- [definition] The actual integral codimension-zero generator supported at the generic point. -/
noncomputable def integralGenericCycle :
    IntegralCodimensionCycles ProjectiveLineScheme 0 := by
  classical
  exact ⟨Function.locallyFinsuppWithin.single projectiveLineGenericPoint 1, by
    intro point nonzero
    have equal : point = projectiveLineGenericPoint := by
      by_contra different
      exact nonzero (by
        simp [Function.locallyFinsuppWithin.single_apply, different])
    subst point
    exact projectiveLineGenericPoint_coheight⟩

/-- [definition] The actual integral codimension-one generator supported at one closed point. -/
noncomputable def integralClosedPointCycle :
    IntegralCodimensionCycles ProjectiveLineScheme 1 := by
  classical
  exact ⟨Function.locallyFinsuppWithin.single projectiveLineClosedPoint 1, by
    intro point nonzero
    have equal : point = projectiveLineClosedPoint := by
      by_contra different
      exact nonzero (by
        simp [Function.locallyFinsuppWithin.single_apply, different])
    subst point
    exact projectiveLineClosedPoint_coheight⟩

/-- [proved-standard; formal-checked] The generic source carries unit total coefficient. -/
theorem integralCycleTotal_generic :
    integralCycleTotal 0 integralGenericCycle = 1 := by
  classical
  change (∑ᶠ point, Function.locallyFinsuppWithin.single
    projectiveLineGenericPoint (1 : ℤ) point) = 1
  rw [finsum_eq_single _ projectiveLineGenericPoint]
  · simp
  · intro point different
    simp [Function.locallyFinsuppWithin.single_apply, different]

/-- [proved-standard; formal-checked] The closed-point divisor source carries unit total
coefficient. -/
theorem integralCycleTotal_closedPoint :
    integralCycleTotal 1 integralClosedPointCycle = 1 := by
  classical
  change (∑ᶠ point, Function.locallyFinsuppWithin.single
    projectiveLineClosedPoint (1 : ℤ) point) = 1
  rw [finsum_eq_single _ projectiveLineClosedPoint]
  · simp
  · intro point different
    simp [Function.locallyFinsuppWithin.single_apply, different]

/-- [definition] The rationalized generic fundamental cycle. -/
noncomputable def rationalGenericCycle :
    RationalCodimensionCycles ProjectiveLineScheme 0 :=
  (1 : ℚ) ⊗ₜ integralGenericCycle

/-- [definition] The rationalized closed-point divisor cycle. -/
noncomputable def rationalClosedPointCycle :
    RationalCodimensionCycles ProjectiveLineScheme 1 :=
  (1 : ℚ) ⊗ₜ integralClosedPointCycle

@[simp]
theorem rationalCycleTotal_generic :
    rationalCycleTotal 0 rationalGenericCycle = 1 := by
  simp [rationalCycleTotal, rationalGenericCycle, integralCycleTotal_generic]

@[simp]
theorem rationalCycleTotal_closedPoint :
    rationalCycleTotal 1 rationalClosedPointCycle = 1 := by
  simp [rationalCycleTotal, rationalClosedPointCycle,
    integralCycleTotal_closedPoint]

/-- [proved-standard; formal-checked] Actual rational codimension-zero cycles reach every total
coefficient. -/
theorem rationalCycleTotal_surjective_zero :
    Function.Surjective (rationalCycleTotal 0) := by
  intro coefficient
  refine ⟨coefficient • rationalGenericCycle, ?_⟩
  rw [map_smul, rationalCycleTotal_generic, smul_eq_mul, mul_one]

/-- [proved-standard; formal-checked] Actual rational codimension-one cycles reach every total
coefficient. -/
theorem rationalCycleTotal_surjective_one :
    Function.Surjective (rationalCycleTotal 1) := by
  intro coefficient
  refine ⟨coefficient • rationalClosedPointCycle, ?_⟩
  rw [map_smul, rationalCycleTotal_closedPoint, smul_eq_mul, mul_one]

/-! ## Genuine analytic homology, cohomology, and cycle classes -/

/-- [definition] The already-constructed analytic projective-line topology as a `TopCat`. -/
def analyticProjectiveLineTopCat : TopCat :=
  TopCat.of ComplexProjectiveLine

/-- [proved-standard; formal-checked] The genuine analytic projective-line point crosses to the
underlying Zariski carrier through the exact closed-point comparison. -/
def analyticProjectiveLineToZariski :
    analyticProjectiveLineTopCat ⟶ (ProjectiveLineScheme : TopCat) :=
  TopCat.ofHom
    ⟨fun point => (analyticToClosedPoint point : ProjectiveLineScheme),
      by
        change Continuous (fun point : ComplexProjectiveLine =>
          onePointUnderlying (projectiveLineEquivOnePoint point))
        exact onePointUnderlying_continuous.comp
          projectiveLineHomeomorphOnePoint.continuous⟩

/-- [proved-standard; formal-checked] Every point returned by the analytic comparison is an
actual closed scheme point. -/
theorem analyticProjectiveLineToZariski_closed
    (point : analyticProjectiveLineTopCat) :
    IsClosed ({analyticProjectiveLineToZariski point} : Set ProjectiveLineScheme) :=
  (analyticToClosedPoint point).property

/-- [proved-standard; formal-checked] The analytic population and the genuine closed-point
population are exactly the same addressed occurrences. -/
theorem analyticProjectiveLineToClosedPoint_bijective :
    Function.Bijective fun point : analyticProjectiveLineTopCat =>
      (⟨analyticProjectiveLineToZariski point,
        analyticProjectiveLineToZariski_closed point⟩ :
        ComplexClosedPoint ProjectiveLineScheme) := by
  change Function.Bijective analyticToClosedPoint
  exact analyticClosedPointEquiv.bijective

/-- [proved-standard; formal-checked] The explicit projective-line/two-sphere homeomorphism as a
topological isomorphism. -/
def analyticProjectiveLineSphereTopIso :
    analyticProjectiveLineTopCat ≅ sphereTopCat :=
  TopCat.isoOfHomeo projectiveLineHomeomorphTwoSphere

/-- [proved-standard; formal-checked] Genuine rational singular homology transports across the
explicit sphere homeomorphism in every degree. -/
def analyticProjectiveLineHomologyEquivSphere (degree : ℕ) :
    RationalSingularHomology degree analyticProjectiveLineTopCat ≃ₗ[ℚ]
      RationalSingularHomology degree sphereTopCat :=
  ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) degree).obj
    rationalCoefficient).mapIso analyticProjectiveLineSphereTopIso).toLinearEquiv)

/-- [proved-standard; formal-checked] Genuine projective-line `H₀` is one rational line. -/
def analyticProjectiveLineH0EquivQ :
    RationalSingularHomology 0 analyticProjectiveLineTopCat ≃ₗ[ℚ] ℚ :=
  (analyticProjectiveLineHomologyEquivSphere 0).trans sphereH0EquivQ

/-- [proved-standard; formal-checked] Genuine projective-line `H₂` is one rational line. -/
def analyticProjectiveLineH2EquivQ :
    RationalSingularHomology 2 analyticProjectiveLineTopCat ≃ₗ[ℚ] ℚ :=
  (analyticProjectiveLineHomologyEquivSphere 2).trans sphereH2EquivQ

/-! ## The minimal higher-even analytic filling seam -/

/-- [definition] The complete residual family for the projective-line receiver.  For every
codimension above the geometric dimension it retains a linear current which fills each closed
singular chain in the corresponding even degree.  No choices in odd degrees and no inverse chain
map are requested. -/
structure SphereHigherEvenCycleFillings where
  filling : ∀ (p : ℕ), 2 ≤ p → CycleFilling SphereSingularChainComplex (2 * p)

/-- [proved-derived; formal-checked] A retained higher-even filling current annihilates the
corresponding genuine rational singular-homology receiver of the sphere. -/
theorem sphereHigherEvenHomology_isZero_of_fillings
    (fillings : SphereHigherEvenCycleFillings)
    {p : ℕ} (two_le : 2 ≤ p) :
    IsZero (RationalSingularHomology (2 * p) sphereTopCat) :=
  (fillings.filling p two_le).homologyIsZero

/-- [proved-derived; formal-checked] The explicit analytic-projective-line/sphere homeomorphism
transports the same higher-even vanishing to the genuine analytic carrier. -/
theorem analyticProjectiveLineHigherEvenHomology_isZero_of_fillings
    (fillings : SphereHigherEvenCycleFillings)
    {p : ℕ} (two_le : 2 ≤ p) :
    IsZero (RationalSingularHomology (2 * p) analyticProjectiveLineTopCat) := by
  apply IsZero.of_iso
    (e := (analyticProjectiveLineHomologyEquivSphere (2 * p)).toModuleIso)
  exact sphereHigherEvenHomology_isZero_of_fillings fillings two_le

/-! ## A stronger all-degree tetrahedral reduction route -/

/-- [definition] The exact all-degree reduction still required to replace singular sphere chains
by the finite tetrahedral `2 → 1 → 0` incidence complex.  Its fields are two chain maps and the
two chain homotopies; it is not a homology-dimension assertion. -/
abbrev SphereTetrahedralReduction :=
  HomotopyEquiv SphereSingularChainComplex tetrahedralChainComplex

/-- [proved-derived; formal-checked] An all-degree tetrahedral reduction makes every rational
sphere homology carrier above degree two zero, because its finite target has no chain occurrence
there. -/
theorem sphereHigherHomology_isZero_of_reduction
    (reduction : SphereTetrahedralReduction)
    {degree : ℕ} (three_le : 3 ≤ degree) :
    IsZero (RationalSingularHomology degree sphereTopCat) := by
  apply IsZero.of_iso (e := reduction.toHomologyIso degree)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  apply HomologicalComplex.ExactAt.of_isZero
  change IsZero (tetrahedralChainComplex.X degree)
  cases degree with
  | zero => omega
  | succ degree =>
      cases degree with
      | zero => omega
      | succ degree =>
          cases degree with
          | zero => omega
          | succ degree =>
              change IsZero (ModuleCat.of ℚ (Fin 0 → ℚ))
              exact ModuleCat.isZero_of_subsingleton _

/-- [proved-derived; formal-checked] The same chain reduction returns exact higher even homology
vanishing on the genuine analytic projective-line topology. -/
theorem analyticProjectiveLineHigherEvenHomology_isZero_of_reduction
    (reduction : SphereTetrahedralReduction)
    {p : ℕ} (two_le : 2 ≤ p) :
    IsZero (RationalSingularHomology (2 * p) analyticProjectiveLineTopCat) := by
  apply IsZero.of_iso
    (e := (analyticProjectiveLineHomologyEquivSphere (2 * p)).toModuleIso)
  exact sphereHigherHomology_isZero_of_reduction reduction (by omega)

/-- [proved-standard; formal-checked] Degree-zero Betti cohomology of analytic `ℙ¹` is one
rational line. -/
def analyticProjectiveLineH0CohomologyEquivQ :
    RationalBettiCohomology analyticProjectiveLineTopCat 0 ≃ₗ[ℚ] ℚ :=
  analyticProjectiveLineH0EquivQ.dualMap.symm.trans
    (LinearMap.ringLmapEquivSelf ℚ ℚ ℚ)

/-- [proved-standard; formal-checked] Degree-two Betti cohomology of analytic `ℙ¹` is one
rational line. -/
def analyticProjectiveLineH2CohomologyEquivQ :
    RationalBettiCohomology analyticProjectiveLineTopCat 1 ≃ₗ[ℚ] ℚ := by
  change Module.Dual ℚ
      (RationalSingularHomology 2 analyticProjectiveLineTopCat) ≃ₗ[ℚ] ℚ
  exact analyticProjectiveLineH2EquivQ.dualMap.symm.trans
    (LinearMap.ringLmapEquivSelf ℚ ℚ ℚ)

/-- [proved-derived; formal-checked] The minimal retained filling family makes every
projective-line Betti receiver above complex codimension one the zero module. -/
theorem analyticProjectiveLineHigherBettiCohomology_subsingleton_of_fillings
    (fillings : SphereHigherEvenCycleFillings)
    {p : ℕ} (two_le : 2 ≤ p) :
    Subsingleton (RationalBettiCohomology analyticProjectiveLineTopCat p) := by
  letI : Subsingleton
      (RationalSingularHomology (2 * p) analyticProjectiveLineTopCat) :=
    ModuleCat.subsingleton_of_isZero
      (analyticProjectiveLineHigherEvenHomology_isZero_of_fillings fillings two_le)
  constructor
  intro left right
  apply LinearMap.ext
  intro homologyClass
  rw [Subsingleton.elim homologyClass 0]
  simp

/-- [proved-derived; formal-checked] Once the all-degree singular/tetrahedral reduction is
returned, every projective-line Betti receiver above complex codimension one is the zero module. -/
theorem analyticProjectiveLineHigherBettiCohomology_subsingleton_of_reduction
    (reduction : SphereTetrahedralReduction)
    {p : ℕ} (two_le : 2 ≤ p) :
    Subsingleton (RationalBettiCohomology analyticProjectiveLineTopCat p) := by
  letI : Subsingleton
      (RationalSingularHomology (2 * p) analyticProjectiveLineTopCat) :=
    ModuleCat.subsingleton_of_isZero
      (analyticProjectiveLineHigherEvenHomology_isZero_of_reduction reduction two_le)
  constructor
  intro left right
  apply LinearMap.ext
  intro homologyClass
  rw [Subsingleton.elim homologyClass 0]
  simp

/-- [proved-standard; formal-checked] The actual generic-cycle coefficient is the degree-zero
Betti fundamental class. -/
def projectiveLineCycleClassZero :
    RationalCodimensionCycles ProjectiveLineScheme 0 →ₗ[ℚ]
      RationalBettiCohomology analyticProjectiveLineTopCat 0 :=
  analyticProjectiveLineH0CohomologyEquivQ.symm.toLinearMap.comp
    (rationalCycleTotal 0)

/-- [proved-standard; formal-checked] The actual closed-point degree current is the degree-two
Betti divisor class. -/
def projectiveLineCycleClassOne :
    RationalCodimensionCycles ProjectiveLineScheme 1 →ₗ[ℚ]
      RationalBettiCohomology analyticProjectiveLineTopCat 1 :=
  analyticProjectiveLineH2CohomologyEquivQ.symm.toLinearMap.comp
    (rationalCycleTotal 1)

/-- [proved-standard; formal-checked] The genuine codimension-zero cycle class fills `H⁰`. -/
theorem projectiveLineCycleClassZero_surjective :
    Function.Surjective projectiveLineCycleClassZero :=
  analyticProjectiveLineH0CohomologyEquivQ.symm.surjective.comp
    rationalCycleTotal_surjective_zero

/-- [proved-standard; formal-checked] The genuine codimension-one cycle class fills `H²`. -/
theorem projectiveLineCycleClassOne_surjective :
    Function.Surjective projectiveLineCycleClassOne :=
  analyticProjectiveLineH2CohomologyEquivQ.symm.surjective.comp
    rationalCycleTotal_surjective_one

/-- [proved-standard; formal-checked] The complete projective-line cycle-class family uses the
generic fundamental current in codimension zero, the closed-point degree current in codimension
one, and the uniquely forced zero current above the scheme's coheight bound. -/
noncomputable def projectiveLineCycleClass (p : ℕ) :
    ModuleCat.of ℚ (RationalCodimensionCycles ProjectiveLineScheme p) ⟶
      RationalBettiCohomology analyticProjectiveLineTopCat p := by
  cases p with
  | zero => exact ModuleCat.ofHom projectiveLineCycleClassZero
  | succ p =>
      cases p with
      | zero => exact ModuleCat.ofHom projectiveLineCycleClassOne
      | succ p => exact 0

/-- [proved-derived; formal-checked] The low-degree source currents and any proof that all higher
Betti receivers are singleton jointly make the complete cycle-class family onto.  This is the
common receiver passage used by both the minimal filling and stronger reduction routes. -/
theorem projectiveLineCycleClass_surjective_of_higherBettiSubsingleton
    (higher : ∀ {q : ℕ}, 2 ≤ q →
      Subsingleton (RationalBettiCohomology analyticProjectiveLineTopCat q))
    (p : ℕ) :
    Function.Surjective (projectiveLineCycleClass p).hom := by
  cases p with
  | zero => exact projectiveLineCycleClassZero_surjective
  | succ p =>
      cases p with
      | zero => exact projectiveLineCycleClassOne_surjective
      | succ p =>
          letI : Subsingleton
              (RationalBettiCohomology analyticProjectiveLineTopCat (p + 2)) :=
            higher (by omega)
          intro hodgeClass
          refine ⟨0, ?_⟩
          exact Subsingleton.elim _ _

/-- [proved-derived; formal-checked] The retained higher-even filling family makes the complete
cycle-class family onto in every codimension. -/
theorem projectiveLineCycleClass_surjective_of_fillings
    (fillings : SphereHigherEvenCycleFillings) (p : ℕ) :
    Function.Surjective (projectiveLineCycleClass p).hom :=
  projectiveLineCycleClass_surjective_of_higherBettiSubsingleton
    (analyticProjectiveLineHigherBettiCohomology_subsingleton_of_fillings fillings) p

/-- [proved-derived; formal-checked] The stronger all-degree tetrahedral reduction also makes the
complete cycle-class family onto in every codimension. -/
theorem projectiveLineCycleClass_surjective_of_reduction
    (reduction : SphereTetrahedralReduction) (p : ℕ) :
    Function.Surjective (projectiveLineCycleClass p).hom :=
  projectiveLineCycleClass_surjective_of_higherBettiSubsingleton
    (analyticProjectiveLineHigherBettiCohomology_subsingleton_of_reduction reduction) p

/-! ## The exact pure middle Hodge splitting -/

/-- [proved-derived; formal-checked] Reflection about weight `2p` fixes the middle Hodge address
and only that address. -/
theorem conjugateHodgeIndex_eq_middle_iff (p : ℕ)
    (index : Fin (2 * p + 1)) :
    conjugateHodgeIndex index = middleHodgeIndex p ↔
      index = middleHodgeIndex p := by
  constructor
  · intro equal
    apply Fin.ext
    have values := congrArg Fin.val equal
    simp [conjugateHodgeIndex, middleHodgeIndex] at values ⊢
    omega
  · intro equal
    subst index
    apply Fin.ext
    simp [conjugateHodgeIndex, middleHodgeIndex]
    omega

/-- [proved-derived; formal-checked] Complex conjugation on the rational complexification is an
involution. -/
theorem complexificationConjugation_involutive (H : ModuleCat ℚ)
    (vector : Complexification H) :
    complexificationConjugation H
        (complexificationConjugation H vector) = vector := by
  refine TensorProduct.induction_on vector ?_ ?_ ?_
  · simp
  · intro coefficient occurrence
    simp [complexificationConjugation]
  · intro left right hleft hright
    simp [map_add, hleft, hright]

/-- [proved-derived; formal-checked] Complex conjugation has a null output exactly on a null
input. -/
theorem complexificationConjugation_eq_zero_iff (H : ModuleCat ℚ)
    (vector : Complexification H) :
    complexificationConjugation H vector = 0 ↔ vector = 0 := by
  constructor
  · intro zero
    have returned := congrArg (complexificationConjugation H) zero
    simpa [complexificationConjugation_involutive] using returned
  · rintro rfl
    exact map_zero _

/-- [proved-derived; formal-checked] A pure even-weight receiver whose complete complexification
occupies the middle `(p,p)` address and whose other components vanish. -/
def middleOnlyHodgeDecomposition (H : ModuleCat ℚ) (p : ℕ) :
    PureHodgeDecomposition H (2 * p) where
  component index := if index = middleHodgeIndex p then ⊤ else ⊥
  internal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · intro index
      by_cases middle : index = middleHodgeIndex p
      · subst index
        change Disjoint
          (if middleHodgeIndex p = middleHodgeIndex p then ⊤ else ⊥)
          (⨆ (index : Fin (2 * p + 1))
              (_ : index ≠ middleHodgeIndex p),
            (if index = middleHodgeIndex p then ⊤ else ⊥))
        rw [if_pos rfl]
        have otherComponents :
            (⨆ (index : Fin (2 * p + 1))
                (_ : index ≠ middleHodgeIndex p),
              (if index = middleHodgeIndex p then
                (⊤ : Submodule ℂ (Complexification H)) else ⊥)) = ⊥ := by
          apply le_antisymm
          · refine iSup_le fun index => iSup_le fun different => ?_
            simp [different]
          · exact bot_le
        rw [otherComponents]
        exact disjoint_bot_right
      · change Disjoint (if index = middleHodgeIndex p then ⊤ else ⊥) _
        rw [if_neg middle]
        exact disjoint_bot_left
    · apply le_antisymm le_top
      calc
        ⊤ = (if middleHodgeIndex p = middleHodgeIndex p then ⊤ else ⊥) := by simp
        _ ≤ ⨆ index : Fin (2 * p + 1),
            (if index = middleHodgeIndex p then ⊤ else ⊥) :=
          le_iSup (fun index : Fin (2 * p + 1) =>
            (if index = middleHodgeIndex p then ⊤ else ⊥))
              (middleHodgeIndex p)
  conjugation_exchanges := by
    intro index vector
    by_cases middle : index = middleHodgeIndex p
    · subst index
      simp [conjugateHodgeIndex_eq_middle_iff]
    · have conjugateNotMiddle :
          conjugateHodgeIndex index ≠ middleHodgeIndex p :=
        (conjugateHodgeIndex_eq_middle_iff p index).not.mpr middle
      change (vector ∈ if index = middleHodgeIndex p then ⊤ else ⊥) ↔
        (complexificationConjugation H vector ∈
          if conjugateHodgeIndex index = middleHodgeIndex p then ⊤ else ⊥)
      simp only [middle, conjugateNotMiddle, if_false, Submodule.mem_bot]
      exact (complexificationConjugation_eq_zero_iff H vector).symm

/-- [proved-derived; formal-checked] The rational middle receiver of the middle-only splitting is
the complete addressed rational cohomology carrier. -/
theorem middleOnlyHodgeDecomposition_rationalMiddle
    (H : ModuleCat ℚ) (p : ℕ) :
    (middleOnlyHodgeDecomposition H p).rationalMiddle p = ⊤ := by
  ext occurrence
  simp [PureHodgeDecomposition.rationalMiddle, middleOnlyHodgeDecomposition]

/-! ## Low-degree Hodge returns -/

/-- [proved-standard; formal-checked] Actual codimension-zero classes land in the complete
middle Hodge receiver. -/
theorem projectiveLineCycleClassZero_areHodge :
    LinearMap.range projectiveLineCycleClassZero ≤
      (middleOnlyHodgeDecomposition
        (RationalBettiCohomology analyticProjectiveLineTopCat 0) 0).rationalMiddle 0 := by
  rw [middleOnlyHodgeDecomposition_rationalMiddle]
  exact le_top

/-- [proved-standard; formal-checked] Actual codimension-one classes land in the complete
`(1,1)` receiver. -/
theorem projectiveLineCycleClassOne_areHodge :
    LinearMap.range projectiveLineCycleClassOne ≤
      (middleOnlyHodgeDecomposition
        (RationalBettiCohomology analyticProjectiveLineTopCat 1) 1).rationalMiddle 1 := by
  rw [middleOnlyHodgeDecomposition_rationalMiddle]
  exact le_top

/-- [proved-standard; formal-checked] The genuine projective-line Hodge conclusion holds in
codimension zero. -/
theorem projectiveLineHodgeConclusion_zero :
    (middleOnlyHodgeDecomposition
      (RationalBettiCohomology analyticProjectiveLineTopCat 0) 0).rationalMiddle 0 =
        LinearMap.range projectiveLineCycleClassZero := by
  rw [middleOnlyHodgeDecomposition_rationalMiddle]
  exact (LinearMap.range_eq_top.mpr projectiveLineCycleClassZero_surjective).symm

/-- [proved-standard; formal-checked] The genuine projective-line Hodge conclusion holds in
codimension one. -/
theorem projectiveLineHodgeConclusion_one :
    (middleOnlyHodgeDecomposition
      (RationalBettiCohomology analyticProjectiveLineTopCat 1) 1).rationalMiddle 1 =
        LinearMap.range projectiveLineCycleClassOne := by
  rw [middleOnlyHodgeDecomposition_rationalMiddle]
  exact (LinearMap.range_eq_top.mpr projectiveLineCycleClassOne_surjective).symm

/-- [proved-derived; formal-checked] The minimal retained higher-even filling family closes the
Hodge conclusion for the genuine projective line in every codimension. -/
theorem projectiveLineHodgeConclusion_of_fillings
    (fillings : SphereHigherEvenCycleFillings) (p : ℕ) :
    (middleOnlyHodgeDecomposition
      (RationalBettiCohomology analyticProjectiveLineTopCat p) p).rationalMiddle p =
        LinearMap.range (projectiveLineCycleClass p).hom := by
  rw [middleOnlyHodgeDecomposition_rationalMiddle]
  exact (LinearMap.range_eq_top.mpr
    (projectiveLineCycleClass_surjective_of_fillings fillings p)).symm

/-- [proved-derived; formal-checked] An all-degree singular/tetrahedral reduction closes the
Hodge conclusion for the genuine projective line in every codimension.  The conclusion is
nontrivial in codimensions zero and one and follows from exact source/receiver collapse above
one. -/
theorem projectiveLineHodgeConclusion_of_reduction
    (reduction : SphereTetrahedralReduction) (p : ℕ) :
    (middleOnlyHodgeDecomposition
      (RationalBettiCohomology analyticProjectiveLineTopCat p) p).rationalMiddle p =
        LinearMap.range (projectiveLineCycleClass p).hom := by
  rw [middleOnlyHodgeDecomposition_rationalMiddle]
  exact (LinearMap.range_eq_top.mpr
    (projectiveLineCycleClass_surjective_of_reduction reduction p)).symm

/-- [proved-derived; formal-checked] Every member of the complete projective-line cycle-class
family lands in the addressed middle Hodge component. -/
theorem projectiveLineCycleClassesAreHodge (p : ℕ) :
    LinearMap.range (projectiveLineCycleClass p).hom ≤
      (middleOnlyHodgeDecomposition
        (RationalBettiCohomology analyticProjectiveLineTopCat p) p).rationalMiddle p := by
  rw [middleOnlyHodgeDecomposition_rationalMiddle]
  exact le_top

/-! ## The filling-parametrized complete receiver -/

/-- [proved-derived; formal-checked] The common analytic, Hodge, and genuine algebraic-cycle
semantics of projective one-space.  Construction hypotheses are retained by the realization
wrappers below rather than duplicated inside this source-independent record. -/
noncomputable def projectiveLineSemantics :
    HodgeSemantics ProjectiveLineScheme where
  complexDimension := 1
  analyticSpace := analyticProjectiveLineTopCat
  toZariski := analyticProjectiveLineToZariski
  toZariski_closed := analyticProjectiveLineToZariski_closed
  toClosedPoint_bijective := analyticProjectiveLineToClosedPoint_bijective
  hodgeDecomposition := fun p => middleOnlyHodgeDecomposition
    (RationalBettiCohomology analyticProjectiveLineTopCat p) p
  cycleClass := projectiveLineCycleClass
  cycleClassesAreHodge := projectiveLineCycleClassesAreHodge

/-- [proved-derived; formal-checked] Retain the exact higher-even filling family while exposing
the common projective-line semantics. -/
noncomputable def projectiveLineSemanticsOfFillings
    (_fillings : SphereHigherEvenCycleFillings) :
    HodgeSemantics ProjectiveLineScheme :=
  projectiveLineSemantics

/-- [proved-derived; formal-checked] Retain the stronger tetrahedral reduction while exposing the
same common projective-line semantics. -/
noncomputable def projectiveLineSemanticsOfReduction
    (_reduction : SphereTetrahedralReduction) :
    HodgeSemantics ProjectiveLineScheme :=
  projectiveLineSemantics

/-- [proved-derived; formal-checked] The filling-parametrized semantics and the already-proved
smooth projective scheme share exactly the same source carrier. -/
noncomputable def projectiveLineRealizationOfFillings
    (fillings : SphereHigherEvenCycleFillings) : Realization where
  geometry := HodgeProjectiveLineScheme.carrier
  semantics := projectiveLineSemanticsOfFillings fillings

/-- [proved-derived; formal-checked] The completed higher-even filling family returns the official
Hodge conclusion in every codimension of this positive-dimensional realization. -/
theorem projectiveLineRealization_hodgeConclusion_of_fillings
    (fillings : SphereHigherEvenCycleFillings) (p : ℕ) :
    ((projectiveLineRealizationOfFillings fillings).datum p).Conclusion := by
  change (middleOnlyHodgeDecomposition
      (RationalBettiCohomology analyticProjectiveLineTopCat p) p).rationalMiddle p =
    LinearMap.range (projectiveLineCycleClass p).hom
  exact projectiveLineHodgeConclusion_of_fillings fillings p

/-- [definition] The exact canonical family selected by one retained higher-even filling family. -/
def ProjectiveLineCanonicalOfFillings
    (fillings : SphereHigherEvenCycleFillings) (realization : Realization) : Prop :=
  realization = projectiveLineRealizationOfFillings fillings

/-- [proved-derived; formal-checked] One retained higher-even filling family is sufficient to
inhabit and close the official Hodge receiver for the genuine projective-line source family. -/
theorem projectiveLineTheHodgeConjecture_of_fillings
    (fillings : SphereHigherEvenCycleFillings) :
    TheHodgeConjecture (ProjectiveLineCanonicalOfFillings fillings) := by
  intro realization canonical p
  subst realization
  exact projectiveLineRealization_hodgeConclusion_of_fillings fillings p

/-! ## The stronger reduction-parametrized receiver -/

/-- [proved-derived; formal-checked] The reduction-parametrized semantics and the already-proved
smooth projective scheme share exactly the same source carrier. -/
noncomputable def projectiveLineRealizationOfReduction
    (reduction : SphereTetrahedralReduction) : Realization where
  geometry := HodgeProjectiveLineScheme.carrier
  semantics := projectiveLineSemanticsOfReduction reduction

/-- [proved-derived; formal-checked] The completed reduction returns the official Hodge
conclusion in every codimension of this positive-dimensional realization. -/
theorem projectiveLineRealization_hodgeConclusion
    (reduction : SphereTetrahedralReduction) (p : ℕ) :
    ((projectiveLineRealizationOfReduction reduction).datum p).Conclusion := by
  change (middleOnlyHodgeDecomposition
      (RationalBettiCohomology analyticProjectiveLineTopCat p) p).rationalMiddle p =
    LinearMap.range (projectiveLineCycleClass p).hom
  exact projectiveLineHodgeConclusion_of_reduction reduction p

/-- [definition] The exact canonical family selected by one constructed all-degree reduction. -/
def ProjectiveLineCanonicalOfReduction
    (reduction : SphereTetrahedralReduction) (realization : Realization) : Prop :=
  realization = projectiveLineRealizationOfReduction reduction

/-- [proved-derived; formal-checked] One exact all-degree tetrahedral reduction is sufficient to
inhabit and close the official Hodge receiver for the genuine projective-line source family. -/
theorem projectiveLineTheHodgeConjecture_of_reduction
    (reduction : SphereTetrahedralReduction) :
    TheHodgeConjecture (ProjectiveLineCanonicalOfReduction reduction) := by
  intro realization canonical p
  subst realization
  exact projectiveLineRealization_hodgeConclusion reduction p

section Audit

#print axioms algebraicCycle_support_finite
#print axioms integralCycleTotal
#print axioms rationalCycleTotal
#print axioms projectiveLineGenericPoint_coheight
#print axioms projectiveLineClosedPoint_coheight
#print axioms projectiveLine_coheight_le_one
#print axioms rationalCodimensionCycles_eq_zero_of_two_le
#print axioms rationalCycleTotal_surjective_zero
#print axioms rationalCycleTotal_surjective_one
#print axioms analyticProjectiveLineH0EquivQ
#print axioms analyticProjectiveLineH2EquivQ
#print axioms sphereHigherEvenHomology_isZero_of_fillings
#print axioms analyticProjectiveLineHigherEvenHomology_isZero_of_fillings
#print axioms sphereHigherHomology_isZero_of_reduction
#print axioms analyticProjectiveLineHigherEvenHomology_isZero_of_reduction
#print axioms projectiveLineCycleClassZero_surjective
#print axioms projectiveLineCycleClassOne_surjective
#print axioms projectiveLineCycleClass
#print axioms middleOnlyHodgeDecomposition
#print axioms projectiveLineHodgeConclusion_zero
#print axioms projectiveLineHodgeConclusion_one
#print axioms projectiveLineHodgeConclusion_of_fillings
#print axioms projectiveLineHodgeConclusion_of_reduction
#print axioms projectiveLineSemanticsOfFillings
#print axioms projectiveLineSemanticsOfReduction
#print axioms projectiveLineRealization_hodgeConclusion_of_fillings
#print axioms projectiveLineRealization_hodgeConclusion
#print axioms projectiveLineTheHodgeConjecture_of_fillings
#print axioms projectiveLineTheHodgeConjecture_of_reduction

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineRealization
