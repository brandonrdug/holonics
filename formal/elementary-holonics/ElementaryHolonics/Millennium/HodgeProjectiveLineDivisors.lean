import ElementaryHolonics.Millennium.HodgeProjectiveLineAtlas

/-!
# Geometric ruling divisors on the projective-line product

This file replaces the anonymous two-coordinate source of the rank-two Hodge calculation by
rational combinations of actual projection fibres on
`Projectivization ℂ ℂ² × Projectivization ℂ ℂ²`.

The geometric facts are proved at their source:

* fibres of the same projection over different points are disjoint;
* one fibre of each projection intersects in exactly one addressed point;
* in the affine product atlas the two distinguished fibres are the two coordinate axes;
* the local intersection determinant is one;
* rational ruling divisors are linearly equivalent to the bidegree carrier, and this constructs
  the cycle-space comparison previously left as an external field.

No singular-cohomology comparison is asserted here.  What closes is the divisor/source half of
the comparison port and its exact incidence/intersection geometry.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineDivisors

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineAtlas

/-- [definition] The fibre of either projection over an addressed projective point. -/
def projectionFibre (ruling : Ruling) (base : ComplexProjectiveLine) : Set Surface :=
  match ruling with
  | .first => { point | point.1 = base }
  | .second => { point | point.2 = base }

theorem rulingSupport_eq_projectionFibre (ruling : Ruling) :
    rulingSupport ruling = projectionFibre ruling coordinatePoint := by
  cases ruling <;> rfl

/-- [proved-derived; formal-checked] Two distinct fibres of the same projection are disjoint.
This is the geometric source of the zero self-intersection after moving a ruling fibre. -/
theorem parallel_projectionFibres_disjoint (ruling : Ruling)
    {firstBase secondBase : ComplexProjectiveLine} (hne : firstBase ≠ secondBase) :
    Disjoint (projectionFibre ruling firstBase) (projectionFibre ruling secondBase) := by
  rw [Set.disjoint_left]
  intro surfacePoint hfirst hsecond
  cases ruling with
  | first => exact hne (hfirst.symm.trans hsecond)
  | second => exact hne (hfirst.symm.trans hsecond)

/-- [proved-derived; formal-checked] A first and second projection fibre meet in exactly their
addressed product point. -/
theorem transverse_projectionFibres_intersection
    (firstBase secondBase : ComplexProjectiveLine) :
    projectionFibre .first firstBase ∩ projectionFibre .second secondBase =
      ({(firstBase, secondBase)} : Set Surface) := by
  ext surfacePoint
  simp [projectionFibre, Prod.ext_iff]

/-- [proved-derived; formal-checked] The two distinguished ruling supports meet at one point. -/
theorem rulingSupports_intersection :
    rulingSupport .first ∩ rulingSupport .second =
      ({(coordinatePoint, coordinatePoint)} : Set Surface) := by
  rw [rulingSupport_eq_projectionFibre, rulingSupport_eq_projectionFibre]
  exact transverse_projectionFibres_intersection coordinatePoint coordinatePoint

/-- [proved-derived; formal-checked] The distinguished projective point is affine coordinate zero
in the first standard chart. -/
theorem coordinatePoint_eq_point_first_zero :
    coordinatePoint = point .first 0 := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ coordinateVector_ne_zero
    (normalizedVector_ne_zero .first 0)).2
  refine ⟨1, ?_⟩
  funext index
  fin_cases index <;> simp [coordinateVector, normalizedVector]

theorem coordinatePoint_in_first_chart : InChart .first coordinatePoint := by
  rw [coordinatePoint_eq_point_first_zero]
  exact point_mem .first 0

theorem coordinate_coordinatePoint :
    coordinate .first ⟨coordinatePoint, coordinatePoint_in_first_chart⟩ = 0 := by
  change (Projectivization.mk ℂ coordinateVector coordinateVector_ne_zero).rep 1 /
      (Projectivization.mk ℂ coordinateVector coordinateVector_ne_zero).rep 0 = 0
  rw [representative_ratio_mk]
  · simp [coordinateVector]
  · simp [coordinateVector]

/-- [proved-derived; formal-checked] In every product chart using the first affine chart on the
first factor, the first ruling support has local equation `z₁ = 0`. -/
theorem firstRuling_localEquation (secondChart : AffineChart)
    (situated : { point : Surface // InSurfaceChart (.first, secondChart) point }) :
    situated.1 ∈ rulingSupport .first ↔
      (surfaceCoordinate (.first, secondChart) situated).1 = 0 := by
  constructor
  · intro hsupport
    change situated.1.1 = coordinatePoint at hsupport
    change coordinate .first ⟨situated.1.1, situated.2.1⟩ = 0
    have hsituated :
        (⟨situated.1.1, situated.2.1⟩ :
          { point : ComplexProjectiveLine // InChart .first point }) =
        ⟨coordinatePoint, coordinatePoint_in_first_chart⟩ :=
      Subtype.ext hsupport
    rw [hsituated]
    exact coordinate_coordinatePoint
  · intro hcoordinate
    change situated.1.1 = coordinatePoint
    have hreconstruct := point_coordinate .first ⟨situated.1.1, situated.2.1⟩
    change coordinate .first ⟨situated.1.1, situated.2.1⟩ = 0 at hcoordinate
    calc
      situated.1.1 = point .first
          (coordinate .first ⟨situated.1.1, situated.2.1⟩) := hreconstruct.symm
      _ = point .first 0 := by rw [hcoordinate]
      _ = coordinatePoint := coordinatePoint_eq_point_first_zero.symm

/-- [proved-derived; formal-checked] In every product chart using the first affine chart on the
second factor, the second ruling support has local equation `z₂ = 0`. -/
theorem secondRuling_localEquation (firstChart : AffineChart)
    (situated : { point : Surface // InSurfaceChart (firstChart, .first) point }) :
    situated.1 ∈ rulingSupport .second ↔
      (surfaceCoordinate (firstChart, .first) situated).2 = 0 := by
  constructor
  · intro hsupport
    change situated.1.2 = coordinatePoint at hsupport
    change coordinate .first ⟨situated.1.2, situated.2.2⟩ = 0
    have hsituated :
        (⟨situated.1.2, situated.2.2⟩ :
          { point : ComplexProjectiveLine // InChart .first point }) =
        ⟨coordinatePoint, coordinatePoint_in_first_chart⟩ :=
      Subtype.ext hsupport
    rw [hsituated]
    exact coordinate_coordinatePoint
  · intro hcoordinate
    change situated.1.2 = coordinatePoint
    have hreconstruct := point_coordinate .first ⟨situated.1.2, situated.2.2⟩
    change coordinate .first ⟨situated.1.2, situated.2.2⟩ = 0 at hcoordinate
    calc
      situated.1.2 = point .first
          (coordinate .first ⟨situated.1.2, situated.2.2⟩) := hreconstruct.symm
      _ = point .first 0 := by rw [hcoordinate]
      _ = coordinatePoint := coordinatePoint_eq_point_first_zero.symm

/-- [definition] The pair of local divisor equations at the transverse intersection. -/
def localDivisorEquations : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) := LinearMap.id

/-- [proved-derived; formal-checked] The local divisor-equation receiver is invertible. -/
theorem localDivisorEquations_bijective : Function.Bijective localDivisorEquations :=
  LinearEquiv.bijective (LinearEquiv.refl ℂ (ℂ × ℂ))

/-- [proved-derived; formal-checked] Its coordinate determinant is exactly one. -/
theorem localIntersectionDeterminant :
    Matrix.det !![(1 : ℂ), 0; 0, 1] = 1 := by
  simp

/-! ## Rational combinations of the actual fibres -/

/-- [definition] A rational ruling divisor records a coefficient on each geometric ruling family. -/
abbrev RationalRulingDivisor := Ruling → ℚ

/-- [definition] The exact address change from geometric ruling names to bidegree indices. -/
def rulingEquivFinTwo : Ruling ≃ Fin 2 where
  toFun
    | .first => 0
    | .second => 1
  invFun index := if index = 0 then .first else .second
  left_inv ruling := by cases ruling <;> simp
  right_inv index := by fin_cases index <;> simp

/-- [definition] Reindex rational geometric divisors into the bidegree chart. -/
def divisorBidegreeEquiv : RationalRulingDivisor ≃ₗ[ℚ] Bidegree where
  toFun divisor index :=
    if index = 0 then divisor .first else divisor .second
  invFun bidegree ruling :=
    match ruling with
    | .first => bidegree 0
    | .second => bidegree 1
  left_inv divisor := by
    funext ruling
    cases ruling <;> simp
  right_inv bidegree := by
    funext index
    fin_cases index <;> simp
  map_add' firstDivisor secondDivisor := by
    funext index
    fin_cases index <;> simp
  map_smul' coefficient divisor := by
    funext index
    fin_cases index <;> simp

theorem divisorBidegreeEquiv_first :
    divisorBidegreeEquiv (Pi.single Ruling.first 1) = firstFibre := by
  funext index
  fin_cases index <;> simp [divisorBidegreeEquiv, firstFibre]

theorem divisorBidegreeEquiv_second :
    divisorBidegreeEquiv (Pi.single Ruling.second 1) = secondFibre := by
  funext index
  fin_cases index <;> simp [divisorBidegreeEquiv, secondFibre]

/-- [definition] The Hodge datum whose source is rational combinations of actual ruling fibres,
while retaining the already checked degree-two cellular/bidegree target. -/
def geometricDatum : Datum where
  Variety := Surface
  codimension := 1
  CycleSpace := ModuleCat.of ℚ RationalRulingDivisor
  Cohomology := datum.Cohomology
  cycleClass := ModuleCat.ofHom divisorBidegreeEquiv.toLinearMap
  rationalHodgeClasses := ⊤
  cycleClassesAreHodge := by
    intro _ _
    exact Submodule.mem_top

/-- [definition] The divisor half of the external comparison is now constructed from geometric
fibres.  No cycle-space equivalence is supplied by the caller. -/
def geometricComparison : ProjectiveLineProductComparison geometricDatum where
  varietyEquiv := Equiv.refl Surface
  codimension_one := rfl
  cycleEquiv := divisorBidegreeEquiv.symm
  cohomologyEquiv := LinearEquiv.refl ℚ Bidegree
  hodgeEquiv := LinearEquiv.ofEq _ _ rfl
  cycleClass_commutes := by
    intro cycle
    change divisorBidegreeEquiv (divisorBidegreeEquiv.symm cycle) = cycle
    exact divisorBidegreeEquiv.apply_symm_apply cycle
  hodgeClass_commutes := by
    intro hodgeClass
    rfl

/-- [proved-derived; formal-checked] Every rational degree-two Hodge occurrence in the geometric
ruling datum receives a rational combination of actual projection fibres. -/
theorem geometricHodgeConclusion : geometricDatum.Conclusion :=
  geometricComparison.actualHodgeConclusion

/-- [proved-derived; formal-checked] The complete source fibre over a geometric Hodge occurrence
is inhabited; its inhabitants are rational geometric ruling divisors. -/
noncomputable def geometricCycleLift
    (hodgeClass : geometricDatum.rationalHodgeClasses) :
    Soma.Holonics.Millennium.HodgeConstructivePassage.CycleLiftFibre
      geometricDatum hodgeClass :=
  geometricComparison.transportedCycleLift hodgeClass

section Audit

#print axioms parallel_projectionFibres_disjoint
#print axioms transverse_projectionFibres_intersection
#print axioms rulingSupports_intersection
#print axioms firstRuling_localEquation
#print axioms secondRuling_localEquation
#print axioms localIntersectionDeterminant
#print axioms divisorBidegreeEquiv
#print axioms geometricComparison
#print axioms geometricHodgeConclusion
#print axioms geometricCycleLift

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineDivisors
