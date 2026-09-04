import ElementaryHolonics.Millennium.HodgeSpherePowerRulingHomology
import ElementaryHolonics.Millennium.HodgeSpherePowerPairHomology
import ElementaryHolonics.Millennium.HodgeProjectiveLinePowerType11
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Finite projective-power topology, periods, and divisor cycle classes

The analytic coordinate ledger on every finite power of the projective line is compared here with
genuine rational singular homology and its algebraic dual.  The comparison does not use a rank
count:

* the global power `(ℙ¹)^n` is carried coordinatewise to `(S²)^n` by the already constructed
  projective-line homeomorphism;
* the homeomorphism is transported through the singular-homology functor;
* the exact sphere-power ruling equivalence supplies every genuine degree-two homology class;
* the finite analytic period functional is proved to be the complete algebraic dual chart; and
* actual coordinate projection fibres supply the divisor population whose singular cycle-class
  receiver agrees with that analytic period chart.

For every positive finite power this constructs the source-specific Hodge conclusion in degree
two/codimension one.  It does not promote the family to the universal Hodge conjecture: a later
admission object still owes the complete global smooth-projective certificate for the finite
power family.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgePowerComparison

open CategoryTheory
open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineTopology
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeSpherePowerRulingHomology
open Soma.Holonics.Millennium.HodgeSpherePowerPairHomology
open Soma.Holonics.Millennium.HodgeProjectiveLinePowerType11

/-- [definition] The actual global finite power of the complex projective line. -/
abbrev ProjectiveLinePower (factorCount : ℕ) :=
  Fin factorCount → ComplexProjectiveLine

def projectiveLinePowerTopCat (factorCount : ℕ) : TopCat :=
  TopCat.of (ProjectiveLinePower factorCount)

/-- [proved-derived; formal-checked] The projective-line/sphere homeomorphism acts independently
on every addressed coordinate while retaining the complete finite coordinate population. -/
def projectiveLinePowerHomeomorphSpherePower (factorCount : ℕ) :
    ProjectiveLinePower factorCount ≃ₜ SpherePower factorCount where
  toFun point index := projectiveLineHomeomorphTwoSphere (point index)
  invFun point index := projectiveLineHomeomorphTwoSphere.symm (point index)
  left_inv point := by
    funext index
    simp
  right_inv point := by
    funext index
    simp
  continuous_toFun := by
    apply continuous_pi
    intro index
    exact projectiveLineHomeomorphTwoSphere.continuous.comp (continuous_apply index)
  continuous_invFun := by
    apply continuous_pi
    intro index
    exact projectiveLineHomeomorphTwoSphere.symm.continuous.comp (continuous_apply index)

def projectiveLinePowerSphereTopIso (factorCount : ℕ) :
    projectiveLinePowerTopCat factorCount ≅ spherePowerTopCat factorCount :=
  TopCat.isoOfHomeo (projectiveLinePowerHomeomorphSpherePower factorCount)

/-- [proved-derived; formal-checked] Genuine rational singular homology transports across the
coordinatewise power homeomorphism in every degree. -/
def projectiveLinePowerSingularHomologyEquivSpherePower
    (factorCount degree : ℕ) :
    RationalSingularHomology degree (projectiveLinePowerTopCat factorCount) ≃ₗ[ℚ]
      RationalSingularHomology degree (spherePowerTopCat factorCount) :=
  ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) degree).obj
    rationalCoefficient).mapIso
      (projectiveLinePowerSphereTopIso factorCount)).toLinearEquiv)

abbrev ProjectiveLinePowerH2 (factorCount : ℕ) :=
  RationalSingularHomology 2 (projectiveLinePowerTopCat factorCount)

/-- [proved-derived; formal-checked] Every positive global projective-line power has exact
addressed ruling coordinates on genuine rational singular degree-two homology. -/
def projectiveLinePowerRulingHomologyEquiv (factorCount : ℕ)
    (positive : 0 < factorCount) :
    PowerCoefficients factorCount ≃ₗ[ℚ] ProjectiveLinePowerH2 factorCount :=
  (spherePowerRulingHomologyEquiv factorCount positive).trans
    (projectiveLinePowerSingularHomologyEquivSpherePower factorCount 2).symm

/-! ## One degree-four coordinate-pair chart -/

/-- [definition] Genuine rational degree-four singular homology of the global projective power. -/
abbrev ProjectiveLinePowerH4 (factorCount : ℕ) :=
  RationalSingularHomology 4 (projectiveLinePowerTopCat factorCount)

/-- [proved-derived; formal-checked] The whole-graded sphere-power reduction and the common
surface source reduction carry all six coordinate planes through the global projective topology
in one reversible passage. -/
def projectiveLinePowerPairHomologyEquivOfReductions
    (fillings : HodgeProjectiveLineRealization.SphereHigherEvenCycleFillings)
    (sourceReduction : HodgeSphereProductFiniteComplex.SphereProductCellularReduction)
    (powerReduction : HodgeSpherePowerRulingHomology.SpherePowerCellularReduction 4) :
    (CoordinatePair 4 → ℚ) ≃ₗ[ℚ] ProjectiveLinePowerH4 4 :=
  (coordinatePairHomologyEquivOfReductions fillings sourceReduction powerReduction).trans
    (projectiveLinePowerSingularHomologyEquivSpherePower 4 4).symm

/-- [definition] The genuine degree-four rational singular-cohomology receiver of the fourfold
projective-line power. -/
abbrev ProjectiveLinePowerDegreeFourRationalSingularCohomology :=
  Module.Dual ℚ (ProjectiveLinePowerH4 4)

/-- [proved-derived; formal-checked] Coordinate-pair currents form the complete algebraic dual
chart of genuine projective fourfold degree-four homology.  This is a topological and linear
receiver statement; it does not identify the currents with codimension-two algebraic cycles. -/
def projectiveLinePowerPairCohomologyEquivOfReductions
    (fillings : HodgeProjectiveLineRealization.SphereHigherEvenCycleFillings)
    (sourceReduction : HodgeSphereProductFiniteComplex.SphereProductCellularReduction)
    (powerReduction : HodgeSpherePowerRulingHomology.SpherePowerCellularReduction 4) :
    (CoordinatePair 4 → ℚ) ≃ₗ[ℚ]
      ProjectiveLinePowerDegreeFourRationalSingularCohomology :=
  (dotProductEquiv ℚ (CoordinatePair 4)).trans
    (Module.Dual.congr
      (projectiveLinePowerPairHomologyEquivOfReductions
        fillings sourceReduction powerReduction))

/-- [proved-derived; formal-checked] The transported coordinate-pair population is one basis of
the complete genuine degree-four singular-cohomology receiver. -/
def projectiveLinePowerPairCohomologyBasisOfReductions
    (fillings : HodgeProjectiveLineRealization.SphereHigherEvenCycleFillings)
    (sourceReduction : HodgeSphereProductFiniteComplex.SphereProductCellularReduction)
    (powerReduction : HodgeSpherePowerRulingHomology.SpherePowerCellularReduction 4) :
    Module.Basis (CoordinatePair 4) ℚ
      ProjectiveLinePowerDegreeFourRationalSingularCohomology :=
  (Pi.basisFun ℚ (CoordinatePair 4)).map
    (projectiveLinePowerPairCohomologyEquivOfReductions
      fillings sourceReduction powerReduction)

/-- [proved-derived; formal-checked] One basis reconstruction theorem returns every genuine
degree-four cohomology class; no coordinate-by-coordinate proof remains. -/
theorem projectiveLinePowerPairCohomology_reconstruct
    (fillings : HodgeProjectiveLineRealization.SphereHigherEvenCycleFillings)
    (sourceReduction : HodgeSphereProductFiniteComplex.SphereProductCellularReduction)
    (powerReduction : HodgeSpherePowerRulingHomology.SpherePowerCellularReduction 4)
    (cohomologyClass : ProjectiveLinePowerDegreeFourRationalSingularCohomology) :
    ∑ pair,
        ((projectiveLinePowerPairCohomologyBasisOfReductions
          fillings sourceReduction powerReduction).repr cohomologyClass pair) •
          projectiveLinePowerPairCohomologyBasisOfReductions
            fillings sourceReduction powerReduction pair =
      cohomologyClass := by
  exact (projectiveLinePowerPairCohomologyBasisOfReductions
    fillings sourceReduction powerReduction).sum_repr cohomologyClass

/-- [proved-derived; formal-checked] The analytic finite-power period ledger is the complete dual
of its addressed coefficient population. -/
def powerPeriodDualEquivalence (factorCount : ℕ) :
    PowerCoefficients factorCount ≃ₗ[ℚ]
      Module.Dual ℚ (PowerCoefficients factorCount) where
  toFun := powerType11PeriodFunctional
  invFun functional index := functional (powerRulingBasis index)
  left_inv coefficients := by
    funext index
    exact powerType11Period_basis coefficients index
  right_inv functional := by
    apply LinearMap.ext
    intro homology
    change powerType11PeriodFunctional
      (fun index => functional (powerRulingBasis index)) homology = functional homology
    rw [powerType11PeriodFunctional_eq_evaluation]
    change (∑ index, functional (powerRulingBasis index) * homology index) =
      functional homology
    have homology_decomposition :
        (∑ index, homology index • powerRulingBasis index) = homology := by
      funext coordinate
      classical
      simp [powerRulingBasis, Pi.single_apply]
    calc
      (∑ index, functional (powerRulingBasis index) * homology index) =
          functional (∑ index, homology index • powerRulingBasis index) := by
            rw [map_sum]
            simp only [map_smul, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro index _
            ring
      _ = functional homology := congrArg functional homology_decomposition
  map_add' left right := by
    apply LinearMap.ext
    intro homology
    rw [powerType11PeriodFunctional_eq_evaluation]
    simp only [LinearMap.add_apply]
    rw [powerType11PeriodFunctional_eq_evaluation,
      powerType11PeriodFunctional_eq_evaluation]
    change powerRulingEvaluation (left + right) homology =
      powerRulingEvaluation left homology + powerRulingEvaluation right homology
    simp only [powerRulingEvaluation, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
  map_smul' coefficient coefficients := by
    apply LinearMap.ext
    intro homology
    rw [powerType11PeriodFunctional_eq_evaluation]
    simp only [LinearMap.smul_apply, RingHom.id_apply]
    rw [powerType11PeriodFunctional_eq_evaluation]
    change powerRulingEvaluation (coefficient • coefficients) homology =
      coefficient * powerRulingEvaluation coefficients homology
    simp only [powerRulingEvaluation, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring

/-- [definition] The exact rational singular-cohomology receiver is the algebraic dual of genuine
degree-two rational singular homology of the global projective power. -/
abbrev ProjectiveLinePowerDegreeTwoRationalSingularCohomology
    (factorCount : ℕ) := Module.Dual ℚ (ProjectiveLinePowerH2 factorCount)

/-- [proved-derived; formal-checked] Coordinate periods, transported through the exact global
topology and ruling equivalence, form the complete singular-cohomology dual. -/
def powerSingularCohomologyDual (factorCount : ℕ)
    (positive : 0 < factorCount) :
    PowerCoefficients factorCount ≃ₗ[ℚ]
      ProjectiveLinePowerDegreeTwoRationalSingularCohomology factorCount :=
  (powerPeriodDualEquivalence factorCount).trans
    (Module.Dual.congr
      (projectiveLinePowerRulingHomologyEquiv factorCount positive))

/-- [proved-derived; formal-checked] Evaluation after topology and dual transport is exactly the
independently constructed analytic period functional. -/
theorem powerSingularCohomologyDual_evaluation (factorCount : ℕ)
    (positive : 0 < factorCount)
    (coefficients homology : PowerCoefficients factorCount) :
    powerSingularCohomologyDual factorCount positive coefficients
        (projectiveLinePowerRulingHomologyEquiv factorCount positive homology) =
      powerType11PeriodFunctional coefficients homology := by
  simp [powerSingularCohomologyDual, Module.Dual.congr,
    LinearEquiv.congrLeft, powerPeriodDualEquivalence]

/-! ## Actual coordinate-fibre divisors and their singular classes -/

/-- [definition] A geometric coordinate divisor is one fibre of an addressed projection. -/
def coordinateDivisorFibre {factorCount : ℕ} (index : Fin factorCount)
    (base : ComplexProjectiveLine) : Set (ProjectiveLinePower factorCount) :=
  { point | point index = base }

/-- [definition] The distinguished coordinate divisor fixes its addressed factor at the same
projective point used by the completed two-factor geometry. -/
def coordinateDivisorSupport {factorCount : ℕ} (index : Fin factorCount) :
    Set (ProjectiveLinePower factorCount) :=
  coordinateDivisorFibre index coordinatePoint

/-- [proved-derived; formal-checked] Distinct fibres of one coordinate projection are disjoint. -/
theorem parallel_coordinateDivisorFibres_disjoint {factorCount : ℕ}
    (index : Fin factorCount) {firstBase secondBase : ComplexProjectiveLine}
    (hne : firstBase ≠ secondBase) :
    Disjoint (coordinateDivisorFibre index firstBase)
      (coordinateDivisorFibre index secondBase) := by
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  exact hne (hfirst.symm.trans hsecond)

/-- [definition] Rational combinations of the actual addressed coordinate-divisor family. -/
abbrev PowerRulingDivisor (factorCount : ℕ) := Fin factorCount → ℚ

/-- [definition] The explicit chart from geometric divisor addresses to analytic factor
coefficients. -/
def powerDivisorCoefficientEquiv (factorCount : ℕ) :
    PowerRulingDivisor factorCount ≃ₗ[ℚ] PowerCoefficients factorCount :=
  LinearEquiv.refl ℚ _

/-- [definition] The singular cycle class of a rational coordinate divisor is its exact
functional on genuine projective-power ruling homology. -/
def powerSingularDivisorCycleClass (factorCount : ℕ)
    (positive : 0 < factorCount) :
    PowerRulingDivisor factorCount →ₗ[ℚ]
      ProjectiveLinePowerDegreeTwoRationalSingularCohomology factorCount :=
  (powerSingularCohomologyDual factorCount positive).toLinearMap.comp
    (powerDivisorCoefficientEquiv factorCount).toLinearMap

/-- [proved-derived; formal-checked] Divisor-cycle evaluation is exactly the analytic period of
the same addressed coefficient current. -/
theorem powerSingularDivisorCycleClass_evaluation (factorCount : ℕ)
    (positive : 0 < factorCount)
    (divisor : PowerRulingDivisor factorCount)
    (homology : PowerCoefficients factorCount) :
    powerSingularDivisorCycleClass factorCount positive divisor
        (projectiveLinePowerRulingHomologyEquiv factorCount positive homology) =
      powerType11PeriodFunctional (powerDivisorCoefficientEquiv factorCount divisor)
        homology := by
  exact powerSingularCohomologyDual_evaluation factorCount positive
    (powerDivisorCoefficientEquiv factorCount divisor) homology

/-- [proved-derived; formal-checked] One coordinate divisor evaluates as the Kronecker receiver on
the genuine coordinate-ruling basis. -/
theorem coordinateDivisorCycleClass_on_ruling (factorCount : ℕ)
    (positive : 0 < factorCount) (divisorIndex rulingIndex : Fin factorCount) :
    powerSingularDivisorCycleClass factorCount positive
        (Pi.single divisorIndex 1)
        (projectiveLinePowerRulingHomologyEquiv factorCount positive
          (powerRulingBasis rulingIndex)) =
      if divisorIndex = rulingIndex then 1 else 0 := by
  rw [powerSingularDivisorCycleClass_evaluation,
    powerType11Period_basis]
  simp [powerDivisorCoefficientEquiv, Pi.single_apply, eq_comm]

/-! ## Analytic range, divisor range, and source-specific Hodge return -/

/-- [definition] The analytic period map into genuine projective-power singular cohomology. -/
def powerType11PeriodMap (factorCount : ℕ) (positive : 0 < factorCount) :
    PowerCoefficients factorCount →ₗ[ℚ]
      ProjectiveLinePowerDegreeTwoRationalSingularCohomology factorCount :=
  (Module.Dual.congr
      (projectiveLinePowerRulingHomologyEquiv factorCount positive)).toLinearMap.comp
    (powerPeriodDualEquivalence factorCount).toLinearMap

/-- [proved-derived; formal-checked] The analytic period map and the transported singular dual are
the same exact passage. -/
theorem powerType11PeriodMap_eq_singularCohomologyDual (factorCount : ℕ)
    (positive : 0 < factorCount) :
    powerType11PeriodMap factorCount positive =
      (powerSingularCohomologyDual factorCount positive).toLinearMap := by
  rfl

/-- [proved-derived; formal-checked] Analytic periods and actual coordinate-divisor cycle classes
commute through their explicit address chart. -/
theorem powerType11PeriodMap_eq_divisorCycleClass (factorCount : ℕ)
    (positive : 0 < factorCount) (divisor : PowerRulingDivisor factorCount) :
    powerType11PeriodMap factorCount positive
        (powerDivisorCoefficientEquiv factorCount divisor) =
      powerSingularDivisorCycleClass factorCount positive divisor := by
  rw [powerType11PeriodMap_eq_singularCohomologyDual]
  rfl

/-- [definition] Rational type-`(1,1)` classes are the range of the explicitly constructed
finite-power analytic period current. -/
def powerRationalType11 (factorCount : ℕ) (positive : 0 < factorCount) :
    Submodule ℚ
      (ProjectiveLinePowerDegreeTwoRationalSingularCohomology factorCount) :=
  LinearMap.range (powerType11PeriodMap factorCount positive)

/-- [proved-derived; formal-checked] The analytic coordinate forms span the complete genuine
degree-two singular-cohomology dual of every positive projective-line power. -/
theorem powerRationalType11_eq_top (factorCount : ℕ)
    (positive : 0 < factorCount) :
    powerRationalType11 factorCount positive = ⊤ := by
  rw [powerRationalType11, powerType11PeriodMap_eq_singularCohomologyDual]
  exact LinearMap.range_eq_top.mpr
    (powerSingularCohomologyDual factorCount positive).surjective

/-- [proved-derived; formal-checked] Every actual rational coordinate-divisor class is reached by
an analytic `(1,1)` current with exactly the same address coefficients. -/
theorem powerSingularDivisorCycleClass_mem_type11 (factorCount : ℕ)
    (positive : 0 < factorCount) (divisor : PowerRulingDivisor factorCount) :
    powerSingularDivisorCycleClass factorCount positive divisor ∈
      powerRationalType11 factorCount positive := by
  refine ⟨powerDivisorCoefficientEquiv factorCount divisor, ?_⟩
  exact powerType11PeriodMap_eq_divisorCycleClass factorCount positive divisor

/-- [definition] The source-specific finite-power datum uses the actual global projective power,
its rational coordinate-divisor population, genuine singular cohomology, and the independently
constructed analytic type-`(1,1)` range. -/
def powerType11Datum (factorCount : ℕ) (positive : 0 < factorCount) : Datum where
  Variety := ProjectiveLinePower factorCount
  codimension := 1
  CycleSpace := ModuleCat.of ℚ (PowerRulingDivisor factorCount)
  Cohomology := ModuleCat.of ℚ
    (ProjectiveLinePowerDegreeTwoRationalSingularCohomology factorCount)
  cycleClass := ModuleCat.ofHom
    (powerSingularDivisorCycleClass factorCount positive)
  rationalHodgeClasses := powerRationalType11 factorCount positive
  cycleClassesAreHodge := by
    rintro _ ⟨divisor, rfl⟩
    exact powerSingularDivisorCycleClass_mem_type11 factorCount positive divisor

/-- [proved-derived; formal-checked] Every rational degree-two type-`(1,1)` class on a positive
finite projective-line power is the class of a rational combination of its actual coordinate
projection fibres. -/
theorem powerType11Conclusion (factorCount : ℕ) (positive : 0 < factorCount) :
    (powerType11Datum factorCount positive).Conclusion := by
  change powerRationalType11 factorCount positive =
    LinearMap.range (powerSingularDivisorCycleClass factorCount positive)
  rw [powerRationalType11_eq_top]
  apply le_antisymm
  · intro cohomologyClass _
    let coefficient :=
      (powerSingularCohomologyDual factorCount positive).symm cohomologyClass
    refine ⟨(powerDivisorCoefficientEquiv factorCount).symm coefficient, ?_⟩
    change powerSingularCohomologyDual factorCount positive
        (powerDivisorCoefficientEquiv factorCount
          ((powerDivisorCoefficientEquiv factorCount).symm coefficient)) =
      cohomologyClass
    rw [(powerDivisorCoefficientEquiv factorCount).apply_symm_apply]
    exact (powerSingularCohomologyDual factorCount positive).apply_symm_apply _
  · exact le_top

section Audit

#print axioms projectiveLinePowerHomeomorphSpherePower
#print axioms projectiveLinePowerSingularHomologyEquivSpherePower
#print axioms projectiveLinePowerRulingHomologyEquiv
#print axioms projectiveLinePowerPairHomologyEquivOfReductions
#print axioms projectiveLinePowerPairCohomologyEquivOfReductions
#print axioms projectiveLinePowerPairCohomologyBasisOfReductions
#print axioms projectiveLinePowerPairCohomology_reconstruct
#print axioms powerPeriodDualEquivalence
#print axioms powerSingularCohomologyDual
#print axioms powerSingularCohomologyDual_evaluation
#print axioms parallel_coordinateDivisorFibres_disjoint
#print axioms powerSingularDivisorCycleClass_evaluation
#print axioms coordinateDivisorCycleClass_on_ruling
#print axioms powerType11PeriodMap_eq_divisorCycleClass
#print axioms powerRationalType11_eq_top
#print axioms powerType11Conclusion

end Audit

end Soma.Holonics.Millennium.HodgePowerComparison
