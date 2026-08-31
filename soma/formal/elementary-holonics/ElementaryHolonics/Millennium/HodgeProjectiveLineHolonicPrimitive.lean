import ElementaryHolonics.Millennium.HodgeHolonicPrimitiveCut
import ElementaryHolonics.Millennium.HodgeProjectiveLineProduct

/-!
# The projective-line product realizes the holonic primitive cut

The generic holonic cut is not left as an untested wrapper.  This file feeds the exact two-ruling
intersection calculus of `ℙ¹ × ℙ¹` through it.  The lower face is the ample line, the
primitive face is its intersection-orthogonal complement, and the Hodge--Riemann polarity is the
negative orientation of the primitive square.

Every nonzero primitive receiver occurrence is detected by its own explicitly reconstructed
ruling cycle.  Thus the `Holon.ReconstructionFibre` formulation, signed polarization, primitive
decomposition, and source return all compose on the existing geometric validation family.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineHolonicPrimitive

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeHolonicPrimitiveCut
open Soma.Holonics.Millennium.HodgeProjectiveLineProduct

/-! ## The ample lower face and its source transport -/

/-- [definition] The rank-one ample face below the two-ruling codimension-one carrier. -/
def ampleDatum : Datum where
  Variety := Surface
  codimension := 0
  CycleSpace := ModuleCat.of ℚ ℚ
  Cohomology := ModuleCat.of ℚ ℚ
  cycleClass := ModuleCat.ofHom LinearMap.id
  rationalHodgeClasses := ⊤
  cycleClassesAreHodge := by
    intro _ _
    exact Submodule.mem_top

local instance ampleCycleModule : Module ℚ ampleDatum.CycleSpace :=
  ModuleCat.isModule ampleDatum.CycleSpace

local instance ampleCohomologyModule : Module ℚ ampleDatum.Cohomology :=
  ModuleCat.isModule ampleDatum.Cohomology

local instance datumCycleModule : Module ℚ datum.CycleSpace :=
  ModuleCat.isModule datum.CycleSpace

local instance datumCohomologyModule : Module ℚ datum.Cohomology :=
  ModuleCat.isModule datum.Cohomology

local instance datumCohomologyFiniteDimensional :
    FiniteDimensional ℚ datum.Cohomology := by
  change FiniteDimensional ℚ Bidegree
  infer_instance

/-- [definition] A lower source coefficient is transported to that multiple of the ample
ruling sum. -/
def ampleCycleTransport : ampleDatum.CycleSpace →ₗ[ℚ] datum.CycleSpace where
  toFun coefficient :=
    show datum.CycleSpace from ((show ℚ from coefficient) • ampleClass : Bidegree)
  map_add' left right := by
    change ((show ℚ from left) + (show ℚ from right)) • ampleClass =
      (show ℚ from left) • ampleClass + (show ℚ from right) • ampleClass
    rw [add_smul]
  map_smul' scalar coefficient := by
    change (scalar * (show ℚ from coefficient)) • ampleClass =
      scalar • ((show ℚ from coefficient) • ampleClass)
    rw [smul_smul]

/-- [definition] The same ample transport on rational Hodge receiver faces. -/
def ampleHodgeTransport :
    ampleDatum.rationalHodgeClasses →ₗ[ℚ] datum.rationalHodgeClasses where
  toFun coefficient :=
    ⟨show datum.Cohomology from
      ((show ℚ from coefficient.1) • ampleClass : Bidegree), by
        change ((show ℚ from coefficient.1) • ampleClass : Bidegree) ∈
          (⊤ : Submodule ℚ Bidegree)
        exact Submodule.mem_top⟩
  map_add' left right := by
    apply Subtype.ext
    change ((show ℚ from left.1) + (show ℚ from right.1)) • ampleClass =
      (show ℚ from left.1) • ampleClass +
        (show ℚ from right.1) • ampleClass
    rw [add_smul]
  map_smul' scalar coefficient := by
    apply Subtype.ext
    change (scalar * (show ℚ from coefficient.1)) • ampleClass =
      scalar • ((show ℚ from coefficient.1) • ampleClass)
    rw [smul_smul]

/-- [definition] Intersection with the ample direction as one exact linear receiver. -/
def ampleIntersectionFunctional : datum.rationalHodgeClasses →ₗ[ℚ] ℚ where
  toFun hodgeClass := intersection (show Bidegree from hodgeClass.1) ampleClass
  map_add' left right := by
    change
      (((show Bidegree from left.1) 0 + (show Bidegree from right.1) 0) * ampleClass 1 +
        ((show Bidegree from left.1) 1 + (show Bidegree from right.1) 1) * ampleClass 0) =
      ((show Bidegree from left.1) 0 * ampleClass 1 +
        (show Bidegree from left.1) 1 * ampleClass 0) +
      ((show Bidegree from right.1) 0 * ampleClass 1 +
        (show Bidegree from right.1) 1 * ampleClass 0)
    ring
  map_smul' scalar hodgeClass := by
    change
      (scalar * (show Bidegree from hodgeClass.1) 0) * ampleClass 1 +
        (scalar * (show Bidegree from hodgeClass.1) 1) * ampleClass 0 =
      scalar * ((show Bidegree from hodgeClass.1) 0 * ampleClass 1 +
        (show Bidegree from hodgeClass.1) 1 * ampleClass 0)
    ring

/-- [definition] The primitive receiver is the exact orthogonal complement of the ample class. -/
def ampleOrthogonal : Submodule ℚ datum.rationalHodgeClasses :=
  LinearMap.ker ampleIntersectionFunctional

/-- [proved-derived; formal-checked] The ample/primitive coordinate decomposition is an exact
`PrimitiveHodgeStep`; the source and receiver transports commute with cycle class. -/
def amplePrimitiveStep : PrimitiveHodgeStep ampleDatum datum where
  cycleTransport := ampleCycleTransport
  hodgeTransport := ampleHodgeTransport
  cycleClass_commutes := by
    intro coefficient
    change (show ℚ from coefficient) • ampleClass =
      (show ℚ from coefficient) • ampleClass
    rfl
  Primitive := ampleOrthogonal
  decompose := by
    intro hodgeClass
    let primitiveHodge : datum.rationalHodgeClasses :=
      ⟨show datum.Cohomology from
        (primitiveCoefficient (show Bidegree from hodgeClass.1) • primitiveClass : Bidegree),
          by
            change
              (primitiveCoefficient (show Bidegree from hodgeClass.1) •
                primitiveClass : Bidegree) ∈ (⊤ : Submodule ℚ Bidegree)
            exact Submodule.mem_top⟩
    have primitiveOrthogonal :
        intersection (primitiveHodge : datum.Cohomology) ampleClass = 0 := by
      simp [primitiveHodge, intersection, ampleClass, primitiveClass, firstFibre, secondFibre]
    let primitive : ampleOrthogonal := ⟨primitiveHodge, primitiveOrthogonal⟩
    let lowerClass : ampleDatum.rationalHodgeClasses :=
      ⟨show ampleDatum.Cohomology from
        ampleCoefficient (show Bidegree from hodgeClass.1), by
          change ampleCoefficient (show Bidegree from hodgeClass.1) ∈
            (⊤ : Submodule ℚ ℚ)
          exact Submodule.mem_top⟩
    refine ⟨primitive, lowerClass, ?_⟩
    apply Subtype.ext
    simp only [primitive, primitiveHodge, lowerClass, ampleHodgeTransport,
      Submodule.coe_add]
    change
      primitiveCoefficient (show Bidegree from hodgeClass.1) • primitiveClass +
        ampleCoefficient (show Bidegree from hodgeClass.1) • ampleClass =
      (show Bidegree from hodgeClass.1)
    rw [add_comm]
    exact (ample_primitive_decomposition (show Bidegree from hodgeClass.1)).symm

/-! ## The exact signed primitive polarization -/

/-- The bidegree represented by one primitive occurrence. -/
def primitiveBidegree (primitive : amplePrimitiveStep.Primitive) : Bidegree :=
  show Bidegree from primitive.1.1

/-- [definition] The geometric two-ruling intersection form on its original bidegree carrier. -/
def bidegreeIntersection : LinearMap.BilinForm ℚ Bidegree :=
  LinearMap.mk₂ ℚ intersection
    (by intro left right third; simp [intersection]; ring)
    (by intro scalar left right; simp [intersection]; ring)
    (by intro left right third; simp [intersection]; ring)
    (by intro scalar left right; simp [intersection]; ring)

/-- [definition] Forget the nested primitive/Hodge proofs while retaining the exact bidegree. -/
def primitiveBidegreeMap : amplePrimitiveStep.Primitive →ₗ[ℚ] Bidegree where
  toFun := primitiveBidegree
  map_add' left right := by
    rfl
  map_smul' scalar primitive := by
    rfl

/-- [definition] Restriction of the geometric two-ruling intersection form to the primitive
holonic carrier. -/
def primitiveIntersection :
    LinearMap.BilinForm ℚ amplePrimitiveStep.Primitive :=
  bidegreeIntersection.compl₁₂ primitiveBidegreeMap primitiveBidegreeMap

/-- [proved-derived; formal-checked] The exact negative primitive square supplies the signed
Hodge--Riemann polarization required by the holonic cut. -/
def signedPrimitivePolarization :
    SignedDefinitePrimitivePolarization amplePrimitiveStep where
  finiteDimensional := inferInstance
  intersection := primitiveIntersection
  symmetric := by
    rw [LinearMap.BilinForm.isSymm_iff, LinearMap.isSymm_def]
    intro left right
    exact intersection_symmetric (primitiveBidegree left) (primitiveBidegree right)
  polarity := .negative
  signedPositive := by
    intro primitive hprimitive
    have horthogonal :
        intersection (primitiveBidegree primitive) ampleClass = 0 := primitive.property
    have hnonpositive :=
      primitive_intersection_nonpositive (primitiveBidegree primitive) horthogonal
    have hbidegreeNonzero : primitiveBidegree primitive ≠ 0 := by
      intro hzero
      apply hprimitive
      apply Subtype.ext
      apply Subtype.ext
      exact hzero
    have hsquareNonzero :
        intersection (primitiveBidegree primitive) (primitiveBidegree primitive) ≠ 0 := by
      intro hzero
      exact hbidegreeNonzero
        ((primitive_intersection_eq_zero_iff
          (primitiveBidegree primitive) horthogonal).mp hzero)
    change 0 < -intersection (primitiveBidegree primitive) (primitiveBidegree primitive)
    have hstrict :
        intersection (primitiveBidegree primitive) (primitiveBidegree primitive) < 0 :=
      lt_of_le_of_ne hnonpositive hsquareNonzero
    linarith

/-! ## Occupied primitive fibres -/

/-- [proved-derived; formal-checked] Every nonzero primitive direction is detected by its own
returned ruling cycle.  The occurrence retains that source lift inside the reconstruction fibre. -/
theorem detectsEveryNonzero : DetectsEveryNonzero signedPrimitivePolarization := by
  intro primitive hprimitive
  let sourceLift : CycleLiftFibre datum
      (primitive : datum.rationalHodgeClasses) :=
    returnedCycleLift (primitive : datum.rationalHodgeClasses)
  refine ⟨⟨⟨primitive, sourceLift, primitive, ?_⟩, rfl⟩⟩
  exact signedPrimitivePolarization.selfPairing_ne_zero primitive hprimitive

/-- [proved-derived; formal-checked] The projective-line product primitive step is source
liftable through the elementary holonic detector, without a repeated basis argument. -/
theorem primitiveLiftable : amplePrimitiveStep.PrimitiveLiftable :=
  signedPrimitivePolarization.primitiveLiftable_of_detectsEveryNonzero detectsEveryNonzero

/-- [proved-derived; formal-checked] The ample lower face plus the occupied primitive holon returns
the complete two-ruling Hodge conclusion. -/
theorem hodgeConclusion_from_holonicPrimitiveCut : datum.Conclusion := by
  apply amplePrimitiveStep.hodgeConclusion_of_lower_of_primitiveLiftable
  · change (⊤ : Submodule ℚ ℚ) = LinearMap.range LinearMap.id
    simp
  · exact primitiveLiftable

section Audit

#print axioms amplePrimitiveStep
#print axioms signedPrimitivePolarization
#print axioms detectsEveryNonzero
#print axioms primitiveLiftable
#print axioms hodgeConclusion_from_holonicPrimitiveCut

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineHolonicPrimitive
