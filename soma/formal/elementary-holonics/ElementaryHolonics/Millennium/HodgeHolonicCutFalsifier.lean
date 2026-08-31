import ElementaryHolonics.Millennium.HodgeHolonicPrimitiveCut

/-!
# The Hodge--Riemann form does not manufacture algebraic source occurrences

The holonic primitive cut deliberately leaves one source law open.  This file proves that the law
cannot be obtained from signed definiteness, finite dimensionality, or complete reconstruction
fibres alone.  A two-direction rational Hodge carrier is given a negative-definite intersection
form, while its cycle-class holon reaches only the first direction.  The second direction is
nonzero, has nonzero polarized self-interaction, and has an empty cycle-class reconstruction fibre.

This is a firing counterexample to an implication between the admitted abstract laws.  It is not a
counterexample to the classical Hodge conjecture: the datum is a receiver-level linear model, not
the cohomology of a smooth projective complex variety.  Its consequence is exact: the next
universal construction must create algebraic source occurrences through geometry, monodromy, or a
source-specific gluing law; positivity cannot be reused as that construction.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeHolonicCutFalsifier

open Soma.Holonics
open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeHolonicPrimitiveCut

/-- [definition] The two addressed primitive receiver directions. -/
abbrev Plane := Fin 2 → ℚ

/-- [definition] The only direction reached by the algebraic source. -/
def sourceAxis : Plane := Pi.single 0 1

/-- [definition] The receiver direction deliberately separated from the source axis. -/
def missingAxis : Plane := Pi.single 1 1

/-- [definition] The source occurrence sends one rational coefficient along the first axis. -/
def axisCycleClass : ℚ →ₗ[ℚ] Plane where
  toFun coefficient := coefficient • sourceAxis
  map_add' left right := by rw [add_smul]
  map_smul' scalar coefficient := by
    ext index
    simp only [Pi.smul_apply, smul_eq_mul]
    simpa using (mul_assoc scalar coefficient (sourceAxis index))

/-- [definition] A two-direction top Hodge carrier with only one algebraic source direction. -/
def upperDatum : Datum where
  Variety := Plane
  codimension := 1
  CycleSpace := ModuleCat.of ℚ ℚ
  Cohomology := ModuleCat.of ℚ Plane
  cycleClass := ModuleCat.ofHom axisCycleClass
  rationalHodgeClasses := ⊤
  cycleClassesAreHodge := by
    intro _ _
    exact Submodule.mem_top

/-- [definition] A closed rank-one lower face. -/
def lowerDatum : Datum where
  Variety := ℚ
  codimension := 0
  CycleSpace := ModuleCat.of ℚ ℚ
  Cohomology := ModuleCat.of ℚ ℚ
  cycleClass := ModuleCat.ofHom LinearMap.id
  rationalHodgeClasses := ⊤
  cycleClassesAreHodge := by
    intro _ _
    exact Submodule.mem_top

local instance lowerCycleModule : Module ℚ lowerDatum.CycleSpace :=
  ModuleCat.isModule lowerDatum.CycleSpace

local instance lowerCohomologyModule : Module ℚ lowerDatum.Cohomology :=
  ModuleCat.isModule lowerDatum.Cohomology

local instance upperCycleModule : Module ℚ upperDatum.CycleSpace :=
  ModuleCat.isModule upperDatum.CycleSpace

local instance upperCohomologyModule : Module ℚ upperDatum.Cohomology :=
  ModuleCat.isModule upperDatum.Cohomology

/-- [definition] The primitive decomposition exposes the complete upper receiver as the residue;
the lower transport is zero. -/
def primitiveStep : PrimitiveHodgeStep lowerDatum upperDatum where
  cycleTransport := 0
  hodgeTransport := 0
  cycleClass_commutes := by
    intro cycle
    simp
  Primitive := ⊤
  decompose := by
    intro hodgeClass
    refine ⟨⟨hodgeClass, Submodule.mem_top⟩, 0, ?_⟩
    simp

/-- [definition] Forget the two subtype proofs while retaining the addressed plane coordinate. -/
def primitivePlane (primitive : primitiveStep.Primitive) : Plane :=
  show Plane from primitive.1.1

/-- [definition] The negative Euclidean dot form on the two addressed directions. -/
def negativeDot : LinearMap.BilinForm ℚ Plane :=
  LinearMap.mk₂ ℚ (fun left right =>
      -(left 0 * right 0 + left 1 * right 1))
    (by intro left right third; simp; ring)
    (by intro scalar left right; simp; ring)
    (by intro left right third; simp; ring)
    (by intro scalar left right; simp; ring)

/-- [definition] The linear chart from primitive occurrences to their plane coordinates. -/
def primitivePlaneMap : primitiveStep.Primitive →ₗ[ℚ] Plane where
  toFun := primitivePlane
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- [definition] The negative-definite intersection form on the complete primitive carrier. -/
def primitiveIntersection :
    LinearMap.BilinForm ℚ primitiveStep.Primitive :=
  negativeDot.compl₁₂ primitivePlaneMap primitivePlaneMap

/-- [proved-derived; formal-checked] The receiver satisfies the complete signed-definite
primitive-polarization contract. -/
def signedPolarization : SignedDefinitePrimitivePolarization primitiveStep where
  finiteDimensional := FiniteDimensional.of_injective primitivePlaneMap (by
    intro left right hequal
    apply Subtype.ext
    apply Subtype.ext
    exact hequal)
  intersection := primitiveIntersection
  symmetric := by
    rw [LinearMap.BilinForm.isSymm_iff, LinearMap.isSymm_def]
    intro left right
    change
      -(primitivePlane left 0 * primitivePlane right 0 +
          primitivePlane left 1 * primitivePlane right 1) =
        -(primitivePlane right 0 * primitivePlane left 0 +
          primitivePlane right 1 * primitivePlane left 1)
    ring
  polarity := .negative
  signedPositive := by
    intro primitive hprimitive
    have hplane : primitivePlane primitive ≠ 0 := by
      intro hzero
      apply hprimitive
      apply Subtype.ext
      apply Subtype.ext
      exact hzero
    have hcoordinate : primitivePlane primitive 0 ≠ 0 ∨
        primitivePlane primitive 1 ≠ 0 := by
      by_contra hboth
      push_neg at hboth
      apply hplane
      funext index
      fin_cases index
      · exact hboth.1
      · exact hboth.2
    change 0 < -(-(primitivePlane primitive 0 * primitivePlane primitive 0 +
      primitivePlane primitive 1 * primitivePlane primitive 1))
    rcases hcoordinate with hfirst | hsecond
    · nlinarith [sq_pos_of_ne_zero hfirst,
        sq_nonneg (primitivePlane primitive 1)]
    · nlinarith [sq_nonneg (primitivePlane primitive 0),
        sq_pos_of_ne_zero hsecond]

/-- [definition] The separated nonzero Hodge receiver face. -/
def missingHodgeClass : upperDatum.rationalHodgeClasses := by
  change (⊤ : Submodule ℚ Plane)
  exact ⟨missingAxis, Submodule.mem_top⟩

/-- [definition] The same face as a primitive occurrence. -/
def missingPrimitive : primitiveStep.Primitive :=
  ⟨missingHodgeClass, Submodule.mem_top⟩

/-- [proved-derived; formal-checked] The separated primitive receiver face is nonzero. -/
theorem missingPrimitive_ne_zero : missingPrimitive ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg
    (fun primitive : primitiveStep.Primitive => primitivePlane primitive 1) hzero
  change missingAxis 1 = (0 : Plane) 1 at hcoordinate
  norm_num [missingAxis] at hcoordinate

/-- [counterexample; formal-checked] No source occurrence of the cycle-class holon reconstructs
the separated receiver face. -/
theorem missingCycleLiftFibre_empty :
    ¬ Nonempty (CycleLiftFibre upperDatum missingHodgeClass) := by
  rintro ⟨⟨coefficient, hreturns⟩⟩
  change ℚ at coefficient
  change axisCycleClass coefficient = missingAxis at hreturns
  have hcoordinate := congrFun hreturns (1 : Fin 2)
  have hsource : sourceAxis (1 : Fin 2) = 0 := by
    norm_num [sourceAxis, Pi.single_apply]
  have hmissing : missingAxis (1 : Fin 2) = 1 := by
    norm_num [missingAxis, Pi.single_apply]
  change (coefficient • sourceAxis) 1 = missingAxis 1 at hcoordinate
  rw [Pi.smul_apply, hsource, smul_zero, hmissing] at hcoordinate
  exact zero_ne_one hcoordinate

/-- [counterexample; formal-checked] The equivalent elementary-holon reconstruction fibre is
empty as well. -/
theorem missingHolonFibre_empty :
    ¬ Nonempty ((cycleClassHolon upperDatum).ReconstructionFibre missingHodgeClass) := by
  rintro ⟨carried⟩
  exact missingCycleLiftFibre_empty
    ⟨(cycleClassHolonReconstructionFibreEquiv upperDatum missingHodgeClass)
      carried⟩

/-- [counterexample; formal-checked] Signed Hodge--Riemann definiteness, finite dimensionality,
and exact holonic reconstruction do not imply the algebraic detector law. -/
theorem signedPolarization_does_not_detect :
    ¬ DetectsEveryNonzero signedPolarization := by
  intro detects
  have primitiveLiftable :=
    signedPolarization.primitiveLiftable_of_detectsEveryNonzero detects
  exact missingCycleLiftFibre_empty (primitiveLiftable missingPrimitive)

section Audit

#print axioms signedPolarization
#print axioms missingPrimitive_ne_zero
#print axioms missingCycleLiftFibre_empty
#print axioms missingHolonFibre_empty
#print axioms signedPolarization_does_not_detect

end Audit

end Soma.Holonics.Millennium.HodgeHolonicCutFalsifier
