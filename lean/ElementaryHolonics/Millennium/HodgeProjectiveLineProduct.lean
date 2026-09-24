import ElementaryHolonics.Millennium.HodgeConstructivePassage
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# The rank-two Hodge carrier of a product of two complex projective lines

This file advances the constructive Hodge line beyond its rank-one theorem.  The geometric body is
not an anonymous vector space: it is the product of two actual Mathlib projectivizations of
`ℂ²`.  Its two projection fibres are retained as addressed subsets of that body.  Their formal
rational cycle combinations form the bidegree lattice `ℚ²`.

On this carrier we prove exactly:

* the two fibre classes reconstruct every bidegree;
* their intersection matrix is `[[0,1],[1,0]]`;
* the ample/primitive change of chart is invertible, with positive square on the ample direction
  and negative square on the primitive direction;
* the two returned fibre cycles form a finite Hodge basis, hence construct a cycle antecedent for
  every rational Hodge occurrence and close the corresponding `Datum.Conclusion`;
* the complete reconstruction fibre is retained rather than replaced by one chosen inverse.

The remaining classical comparison is exposed as `ProjectiveLineProductComparison`.  It must
identify this exact finite carrier with the divisor-cycle map and rational `(1,1)` part of singular
cohomology of the smooth projective surface `ℙ¹_ℂ × ℙ¹_ℂ`, and supply admission to the caller's
official Hodge family.  Subsequent source-specific files construct that comparison layer by layer;
the comparison port here is an ordered theorem obligation rather than an external-library
dependency.  The rank-two algebra below is `[proved-derived; formal-checked]`; the comparison port
is `[open]`.  No theorem here claims the general Hodge conjecture.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineProduct

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage

open scoped LinearAlgebra.Projectivization

/-- [definition] The complex projective line as the projectivization of `ℂ²`. -/
abbrev ComplexProjectiveLine := Projectivization ℂ (Fin 2 → ℂ)

/-- [definition] The addressed geometric surface underlying this rank-two realization. -/
abbrev Surface := ComplexProjectiveLine × ComplexProjectiveLine

/-- [definition] One concrete point used only to address the two projection fibres. -/
def coordinateVector : Fin 2 → ℂ := fun index => if index = 0 then 1 else 0

theorem coordinateVector_ne_zero : coordinateVector ≠ 0 := by
  intro hzero
  have hatZero := congrFun hzero (0 : Fin 2)
  simp [coordinateVector] at hatZero

/-- [definition] The projective point represented by the first coordinate vector. -/
def coordinatePoint : ComplexProjectiveLine :=
  Projectivization.mk ℂ coordinateVector coordinateVector_ne_zero

/-- [definition] The two geometric rulings of the product. -/
inductive Ruling
  | first
  | second
  deriving DecidableEq

/-- [definition] The actual subset of the projective-line product carried by a ruling fibre. -/
def rulingSupport : Ruling → Set Surface
  | .first => { point | point.1 = coordinatePoint }
  | .second => { point | point.2 = coordinatePoint }

/-- [definition] Rational combinations of the two addressed ruling fibres. -/
abbrev Bidegree := Fin 2 → ℚ

/-- [definition] The first projection-fibre class. -/
def firstFibre : Bidegree := Pi.single 0 1

/-- [definition] The second projection-fibre class. -/
def secondFibre : Bidegree := Pi.single 1 1

/-- [definition] The support label's returned rational bidegree class. -/
def rulingClass : Ruling → Bidegree
  | .first => firstFibre
  | .second => secondFibre

/-- [proved-derived; formal-checked] The two geometric ruling labels have different supports. -/
theorem rulingSupport_ne : rulingSupport .first ≠ rulingSupport .second := by
  intro hequal
  let diagonalPoint : ComplexProjectiveLine :=
    Projectivization.mk ℂ (fun _ => 1)
      (by intro h; have := congrFun h (0 : Fin 2); simp at this)
  have hdiagonal_ne : diagonalPoint ≠ coordinatePoint := by
    intro hequalPoint
    change Projectivization.mk ℂ (fun _ => 1) _ =
      Projectivization.mk ℂ coordinateVector coordinateVector_ne_zero at hequalPoint
    rw [Projectivization.mk_eq_mk_iff'] at hequalPoint
    obtain ⟨coefficient, hcoefficient⟩ := hequalPoint
    have hatOne := congrFun hcoefficient (1 : Fin 2)
    simp [coordinateVector] at hatOne
  have hpoint : (coordinatePoint, diagonalPoint) ∈ rulingSupport .first := rfl
  rw [hequal] at hpoint
  exact hdiagonal_ne hpoint

/-! ## Exact bidegree and intersection calculus -/

/-- [proved-derived; formal-checked] Every bidegree is reconstructed from the two fibre classes. -/
theorem bidegree_decomposition (x : Bidegree) :
    x = x 0 • firstFibre + x 1 • secondFibre := by
  funext index
  fin_cases index <;> simp [firstFibre, secondFibre]

/-- [definition] The exact intersection form in the two ruling coordinates. -/
def intersection (x y : Bidegree) : ℚ :=
  x 0 * y 1 + x 1 * y 0

theorem intersection_symmetric (x y : Bidegree) : intersection x y = intersection y x := by
  simp only [intersection]
  ring

theorem firstFibre_square : intersection firstFibre firstFibre = 0 := by
  simp [intersection, firstFibre]

theorem secondFibre_square : intersection secondFibre secondFibre = 0 := by
  simp [intersection, secondFibre]

theorem fibre_intersection : intersection firstFibre secondFibre = 1 := by
  simp [intersection, firstFibre, secondFibre]

theorem intersection_self (x : Bidegree) : intersection x x = 2 * x 0 * x 1 := by
  simp only [intersection]
  ring

/-- [definition] The positive diagonal class. -/
def ampleClass : Bidegree := firstFibre + secondFibre

/-- [definition] The oriented difference of the two rulings. -/
def primitiveClass : Bidegree := firstFibre - secondFibre

theorem ampleClass_square : intersection ampleClass ampleClass = 2 := by
  norm_num [intersection, ampleClass, firstFibre, secondFibre]

theorem primitiveClass_square : intersection primitiveClass primitiveClass = -2 := by
  norm_num [intersection, primitiveClass, firstFibre, secondFibre]

theorem ample_primitive_orthogonal : intersection ampleClass primitiveClass = 0 := by
  simp [intersection, ampleClass, primitiveClass, firstFibre, secondFibre]

/-- [definition] The coefficient seen by the diagonal/ample receiver. -/
def ampleCoefficient (x : Bidegree) : ℚ := (x 0 + x 1) / 2

/-- [definition] The retained signed difference between the two ruling coordinates. -/
def primitiveCoefficient (x : Bidegree) : ℚ := (x 0 - x 1) / 2

/-- [proved-derived; formal-checked] The ample and difference faces reconstruct the source
bidegree exactly.  Neither coordinate alone is sufficient. -/
theorem ample_primitive_decomposition (x : Bidegree) :
    x = ampleCoefficient x • ampleClass + primitiveCoefficient x • primitiveClass := by
  funext index
  fin_cases index <;>
    simp [ampleCoefficient, primitiveCoefficient, ampleClass, primitiveClass,
      firstFibre, secondFibre] <;> ring

/-- [proved-derived; formal-checked] The intersection form diagonalizes into one positive and one
negative receiver direction. -/
theorem intersection_in_ample_primitive_coordinates (x y : Bidegree) :
    intersection x y =
      2 * (ampleCoefficient x * ampleCoefficient y -
        primitiveCoefficient x * primitiveCoefficient y) := by
  simp [intersection, ampleCoefficient, primitiveCoefficient]
  ring

/-- [proved-derived; formal-checked] Orthogonality to the ample class is exactly the signed
difference line. -/
theorem orthogonal_to_ample_iff (x : Bidegree) :
    intersection x ampleClass = 0 ↔ ∃ coefficient : ℚ, x = coefficient • primitiveClass := by
  constructor
  · intro horthogonal
    refine ⟨x 0, ?_⟩
    funext index
    fin_cases index
    · simp [primitiveClass, firstFibre, secondFibre]
    · have hsum : x 0 + x 1 = 0 := by
        simpa [intersection, ampleClass, firstFibre, secondFibre] using horthogonal
      simp [primitiveClass, firstFibre, secondFibre]
      linarith
  · rintro ⟨coefficient, rfl⟩
    simp [intersection, ampleClass, primitiveClass, firstFibre, secondFibre]

/-- [proved-derived; formal-checked] The primitive receiver has nonpositive square, the rank-two
Hodge-index inequality for this carrier. -/
theorem primitive_intersection_nonpositive (x : Bidegree)
    (horthogonal : intersection x ampleClass = 0) : intersection x x ≤ 0 := by
  have hsum : x 0 + x 1 = 0 := by
    simpa [intersection, ampleClass, firstFibre, secondFibre] using horthogonal
  have hx1 : x 1 = -x 0 := by linarith
  rw [intersection_self]
  rw [hx1]
  nlinarith [sq_nonneg (x 0)]

/-- [proved-derived; formal-checked] Equality in the primitive inequality occurs only at the null
class; the receiver radical is trivial. -/
theorem primitive_intersection_eq_zero_iff (x : Bidegree)
    (horthogonal : intersection x ampleClass = 0) :
    intersection x x = 0 ↔ x = 0 := by
  have hsum : x 0 + x 1 = 0 := by
    simpa [intersection, ampleClass, firstFibre, secondFibre] using horthogonal
  constructor
  · intro hsquare
    rw [intersection_self] at hsquare
    have hx1 : x 1 = -x 0 := by linarith
    rw [hx1] at hsquare
    have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0)]
    have hx1 : x 1 = 0 := by linarith
    funext index
    fin_cases index <;> simp [hx0, hx1]
  · rintro rfl
    simp [intersection]

/-! ## The concrete rank-two Hodge datum and its returned cycle basis -/

/-- [definition] The identity cycle-class receiver on the exact two-ruling model. -/
def cycleClass : ModuleCat.of ℚ Bidegree ⟶ ModuleCat.of ℚ Bidegree :=
  ModuleCat.ofHom LinearMap.id

/-- [definition] The finite rational Hodge model attached to the projective-line product body. -/
def datum : Datum where
  Variety := Surface
  codimension := 1
  CycleSpace := ModuleCat.of ℚ Bidegree
  Cohomology := ModuleCat.of ℚ Bidegree
  cycleClass := cycleClass
  rationalHodgeClasses := ⊤
  cycleClassesAreHodge := by
    intro _ _
    exact Submodule.mem_top

/-- [definition] The exact basis of the top rational Hodge carrier. -/
local instance datumCohomologyModule : Module ℚ (datum.Cohomology) :=
  ModuleCat.isModule datum.Cohomology

noncomputable def hodgeCarrierEquiv : datum.rationalHodgeClasses ≃ₗ[ℚ] Bidegree := by
  letI : Module ℚ (datum.Cohomology) := ModuleCat.isModule datum.Cohomology
  exact {
    toFun := fun x => x.1
    invFun := fun x => ⟨x, by
      change x ∈ (⊤ : Submodule ℚ Bidegree)
      exact Submodule.mem_top⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

noncomputable def hodgeBasis : Module.Basis (Fin 2) ℚ datum.rationalHodgeClasses :=
  Module.Basis.ofEquivFun hodgeCarrierEquiv

theorem hodgeBasis_value (index : Fin 2) :
    (hodgeBasis index : datum.Cohomology) = Pi.single index 1 := by
  change (hodgeBasis index).val = Pi.single index 1
  rw [hodgeBasis, Module.Basis.coe_ofEquivFun]
  rfl

/-- [definition] The two addressed fibre cycles close the finite Hodge basis locally. -/
noncomputable def finiteBasisRealization :
    FiniteHodgeBasisRealization datum (Fin 2) where
  basis := hodgeBasis
  basisCycle := fun index => Pi.single index 1
  basisCycle_returns := by
    intro index
    change (Pi.single index 1 : Bidegree) = (hodgeBasis index).val
    exact (hodgeBasis_value index).symm

/-- [proved-derived; formal-checked] Every rational Hodge occurrence in the rank-two model has an
explicit returned rational combination of the two ruling cycles. -/
noncomputable def returnedCycle (hodgeClass : datum.rationalHodgeClasses) : datum.CycleSpace :=
  finiteBasisRealization.reconstructedCycle hodgeClass

theorem returnedCycle_returns (hodgeClass : datum.rationalHodgeClasses) :
    datum.cycleClass.hom (returnedCycle hodgeClass) =
      (hodgeClass : datum.Cohomology) :=
  finiteBasisRealization.reconstructedCycle_returns hodgeClass

/-- [proved-derived; formal-checked] The complete antecedent population is inhabited for every
rational Hodge occurrence in the rank-two model. -/
noncomputable def returnedCycleLift (hodgeClass : datum.rationalHodgeClasses) :
    CycleLiftFibre datum hodgeClass :=
  finiteBasisRealization.cycleLift hodgeClass

/-- [proved-derived; formal-checked] The rank-two projective-line product model closes its Hodge
conclusion by actual finite-basis cycle reconstruction. -/
theorem hodgeConclusion : datum.Conclusion :=
  finiteBasisRealization.hodgeConclusion

/-- [proved-derived; formal-checked] The singleton model family is a fully quantified Hodge family,
not merely one chosen cohomology class. -/
theorem modelFamilyConclusion :
    TheHodgeConjectureIn (fun D => D = datum) := by
  intro D hD
  subst D
  exact hodgeConclusion

/-! ## Exact passage into an externally realized projective surface -/

/-- [definition] The complete source-specific comparison required to transport the checked
rank-two calculation into an externally realized Hodge datum.

The structure does **not** contain a surjectivity or Hodge-conclusion field.  It contains only
invertible chart changes and their two naturality squares.  Consequently the conclusion below is
derived by transporting the already constructed source cycles, not assumed inside the bridge. -/
structure ProjectiveLineProductComparison (actual : Datum) where
  /-- The actual variety carrier is the same addressed projective-line product body. -/
  varietyEquiv : Surface ≃ actual.Variety
  /-- The actual problem is codimension one. -/
  codimension_one : actual.codimension = 1
  /-- Formal ruling combinations rebase to the actual rational divisor-cycle space. -/
  cycleEquiv : datum.CycleSpace ≃ₗ[ℚ] actual.CycleSpace
  /-- Model cohomology rebases to the actual degree-two rational cohomology. -/
  cohomologyEquiv : datum.Cohomology ≃ₗ[ℚ] actual.Cohomology
  /-- The modeled rational Hodge carrier rebases to the actual rational `(1,1)` carrier. -/
  hodgeEquiv : datum.rationalHodgeClasses ≃ₗ[ℚ] actual.rationalHodgeClasses
  /-- The actual cycle-class map commutes with the two source/target rebases. -/
  cycleClass_commutes : ∀ cycle : datum.CycleSpace,
    actual.cycleClass.hom (cycleEquiv cycle) =
      cohomologyEquiv (datum.cycleClass.hom cycle)
  /-- The Hodge-subspace inclusion commutes with the cohomology rebase. -/
  hodgeClass_commutes : ∀ hodgeClass : datum.rationalHodgeClasses,
    cohomologyEquiv (hodgeClass : datum.Cohomology) =
      (hodgeEquiv hodgeClass : actual.Cohomology)

namespace ProjectiveLineProductComparison

variable {actual : Datum}

/-- [proved-derived; formal-checked] One actual rational Hodge occurrence receives an explicit
actual divisor-cycle antecedent by transport through the comparison squares. -/
noncomputable def transportedCycleLift
    (comparison : ProjectiveLineProductComparison actual)
    (hodgeClass : actual.rationalHodgeClasses) :
    CycleLiftFibre actual hodgeClass := by
  let modelHodgeClass : datum.rationalHodgeClasses :=
    comparison.hodgeEquiv.symm hodgeClass
  let modelLift : CycleLiftFibre datum modelHodgeClass :=
    returnedCycleLift modelHodgeClass
  refine ⟨comparison.cycleEquiv modelLift.1, ?_⟩
  calc
    actual.cycleClass.hom (comparison.cycleEquiv modelLift.1) =
        comparison.cohomologyEquiv (datum.cycleClass.hom modelLift.1) :=
      comparison.cycleClass_commutes modelLift.1
    _ = comparison.cohomologyEquiv (modelHodgeClass : datum.Cohomology) := by
      exact congrArg comparison.cohomologyEquiv modelLift.2
    _ = (comparison.hodgeEquiv modelHodgeClass : actual.Cohomology) :=
      comparison.hodgeClass_commutes modelHodgeClass
    _ = (hodgeClass : actual.Cohomology) := by
      simp [modelHodgeClass]

/-- [proved-derived; formal-checked] The source-specific comparison transports the complete
rank-two cycle reconstruction theorem into the external datum. -/
theorem actualHodgeConclusion
    (comparison : ProjectiveLineProductComparison actual) :
    actual.Conclusion := by
  rw [hodgeConclusion_iff_every_cycleLiftFibre_nonempty]
  intro hodgeClass
  exact ⟨comparison.transportedCycleLift hodgeClass⟩

/-- [proved-derived; formal-checked] Once the external datum is admitted to the caller's official
smooth-projective Hodge family, the official receiver is inhabited and every one of its rational
Hodge occurrences has a transported source cycle. -/
theorem officialConclusion (Official : Datum → Prop)
    (comparison : ProjectiveLineProductComparison actual)
    (hOfficial : Official actual) :
    Official actual ∧ actual.Conclusion :=
  ⟨hOfficial, comparison.actualHodgeConclusion⟩

end ProjectiveLineProductComparison

section Audit

#print axioms bidegree_decomposition
#print axioms intersection_in_ample_primitive_coordinates
#print axioms orthogonal_to_ample_iff
#print axioms primitive_intersection_nonpositive
#print axioms primitive_intersection_eq_zero_iff
#print axioms finiteBasisRealization
#print axioms returnedCycle_returns
#print axioms hodgeConclusion
#print axioms modelFamilyConclusion
#print axioms ProjectiveLineProductComparison.transportedCycleLift
#print axioms ProjectiveLineProductComparison.actualHodgeConclusion
#print axioms ProjectiveLineProductComparison.officialConclusion

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineProduct
