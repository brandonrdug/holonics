import ElementaryHolonics.Millennium.HodgeProductRulingDecomposition
import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# The rational singular-cohomology dual of the projective-line product

The preceding source-level filling identifies genuine rational singular `H₂(S² × S²)` with
the two geometric ruling coordinates.  This file transports that equivalence back across the
constructed homeomorphism `ℙ¹ × ℙ¹ ≃ S² × S²` and dualizes it.

The singular ruling cycles are indexed by the factor which varies, whereas a projection-fibre
divisor is indexed by the factor which is fixed.  Consequently the evaluation matrix in these
two deliberately different charts is the identity: the first fixed-coordinate divisor meets the
first varying-coordinate cycle transversely, and likewise for the second.  Replacing this pairing
by the divisor--divisor intersection matrix would silently identify the two indexing charts.

The relation to the geometric divisor intersection form is retained explicitly: evaluating on a
varying-factor coordinate is the same as intersecting with the corresponding fixed-factor class,
which is obtained by swapping the homology coordinates.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProductSingularCohomologyDual

open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeSphereProductRulingHomology
open Soma.Holonics.Millennium.HodgeProductRulingDecomposition

/-- [definition] Evaluation of a fixed-coordinate divisor bidegree on the varying-coordinate
singular ruling basis. -/
def rulingEvaluation (divisor homology : Bidegree) : ℚ :=
  divisor 0 * homology 0 + divisor 1 * homology 1

/-- [definition] A divisor bidegree as a functional on the varying-coordinate ruling chart. -/
def rulingEvaluationFunctional (divisor : Bidegree) : Module.Dual ℚ Bidegree where
  toFun homology := rulingEvaluation divisor homology
  map_add' left right := by
    simp only [rulingEvaluation, Pi.add_apply]
    ring
  map_smul' coefficient homology := by
    simp only [rulingEvaluation, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- [proved-derived; formal-checked] The two singular ruling coordinates and their fixed-factor
divisor coordinates are exact algebraic duals. -/
def rulingEvaluationDualEquivalence : Bidegree ≃ₗ[ℚ] Module.Dual ℚ Bidegree where
  toFun := rulingEvaluationFunctional
  invFun functional index :=
    if index = 0 then functional firstFibre else functional secondFibre
  left_inv divisor := by
    funext index
    fin_cases index <;>
      simp [rulingEvaluationFunctional, rulingEvaluation, firstFibre, secondFibre]
  right_inv functional := by
    apply LinearMap.ext
    intro homology
    rw [bidegree_decomposition homology]
    simp [rulingEvaluationFunctional, rulingEvaluation, firstFibre, secondFibre]
    ring
  map_add' left right := by
    ext homology
    simp [rulingEvaluationFunctional, rulingEvaluation]
    ring
  map_smul' coefficient divisor := by
    ext homology
    simp [rulingEvaluationFunctional, rulingEvaluation]
    ring

/-- [definition] The coordinate reversal from a varying-factor cycle chart to the corresponding
fixed-factor divisor chart. -/
def swapRulingCoordinates (homology : Bidegree) : Bidegree := fun index =>
  if index = 0 then homology 1 else homology 0

/-- [proved-derived; formal-checked] Ruling evaluation is geometric divisor intersection after
the explicit varying-factor/fixed-factor chart transition. -/
theorem rulingEvaluation_eq_intersection_swap
    (divisor homology : Bidegree) :
    rulingEvaluation divisor homology =
      intersection divisor (swapRulingCoordinates homology) := by
  simp only [rulingEvaluation, intersection, swapRulingCoordinates]
  norm_num

/-- [proved-derived; formal-checked] The source-level ruling equivalence transported from the
sphere product to the actual topological projective-line product. -/
def surfaceRulingHomologyEquivalence :
    Bidegree ≃ₗ[ℚ] RationalSingularHomology 2 surfaceTopCat :=
  rulingHomologyEquivalence.trans
    (surfaceSingularHomologyEquivSphereProduct 2).symm

/-- [definition] The exact rational singular-cohomology receiver used here is the algebraic dual
of genuine rational singular homology of the actual surface. -/
abbrev SurfaceDegreeTwoRationalSingularCohomology :=
  Module.Dual ℚ (RationalSingularHomology 2 surfaceTopCat)

/-- [proved-derived; formal-checked] The fixed-factor/varying-factor evaluation receiver and the
source-level ruling equivalence construct the complete degree-two rational singular-cohomology
dual. -/
def singularCohomologyDual :
    Bidegree ≃ₗ[ℚ] SurfaceDegreeTwoRationalSingularCohomology :=
  rulingEvaluationDualEquivalence.trans
    (Module.Dual.congr surfaceRulingHomologyEquivalence)

/-- [proved-derived; formal-checked] Evaluation after the dual transport is exactly the
fixed-factor/varying-factor ruling pairing. -/
theorem singularCohomologyDual_evaluation
    (divisor homology : Bidegree) :
    singularCohomologyDual divisor
        (surfaceRulingHomologyEquivalence homology) =
      rulingEvaluation divisor homology := by
  simp [singularCohomologyDual, Module.Dual.congr, LinearEquiv.congrLeft,
    rulingEvaluationDualEquivalence, rulingEvaluationFunctional]

theorem firstRulingDual_on_firstRuling :
    singularCohomologyDual firstFibre
        (surfaceRulingHomologyEquivalence firstFibre) = 1 := by
  rw [singularCohomologyDual_evaluation]
  simp [rulingEvaluation, firstFibre]

theorem firstRulingDual_on_secondRuling :
    singularCohomologyDual firstFibre
        (surfaceRulingHomologyEquivalence secondFibre) = 0 := by
  rw [singularCohomologyDual_evaluation]
  simp [rulingEvaluation, firstFibre, secondFibre]

theorem secondRulingDual_on_firstRuling :
    singularCohomologyDual secondFibre
        (surfaceRulingHomologyEquivalence firstFibre) = 0 := by
  rw [singularCohomologyDual_evaluation]
  simp [rulingEvaluation, firstFibre, secondFibre]

theorem secondRulingDual_on_secondRuling :
    singularCohomologyDual secondFibre
        (surfaceRulingHomologyEquivalence secondFibre) = 1 := by
  rw [singularCohomologyDual_evaluation]
  simp [rulingEvaluation, secondFibre]

section Audit

#print axioms rulingEvaluationDualEquivalence
#print axioms rulingEvaluation_eq_intersection_swap
#print axioms surfaceRulingHomologyEquivalence
#print axioms singularCohomologyDual
#print axioms singularCohomologyDual_evaluation

end Audit

end Soma.Holonics.Millennium.HodgeProductSingularCohomologyDual
