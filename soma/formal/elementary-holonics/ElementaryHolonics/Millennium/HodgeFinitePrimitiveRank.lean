import ElementaryHolonics.Foundation.Holon
import ElementaryHolonics.Millennium.HodgeDimensionBoundedLefschetz

/-!
# Finite primitive rank as a source-complete Hodge cut

The dimension-bounded Hodge receiver leaves finitely many primitive cycle-source obligations on
each smooth projective variety.  Finite dimensionality turns each such obligation into an exact
rank comparison, but a bare numerical equality is not a source construction.  This file keeps the
two statements separate and then joins them:

* `primitiveLiftable_iff_algebraicFinrank_eq` identifies the conjectural primitive fibre
  occupation law with equality between the actual algebraic primitive subspace and the complete
  primitive receiver rank;
* `FiniteRankPrimitiveSource` retains a finite source module, its actual cycle current, its
  primitive class current, the cycle-class commuting square, injectivity, and the exact rank
  return; and
* the source map becomes a linear equivalence by theorem, so every primitive class receives an
  explicit reconstructed cycle lift.

This is the rank-general owner used by source-specific lattices such as the Mestre twelve-section
carrier.  Rank equality never manufactures a cycle: the `cycleSource` and commuting square remain
indispensable fields.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeFinitePrimitiveRank

open Soma.Holonics
open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver
open Soma.Holonics.Millennium.HodgeDimensionBoundedLefschetz
open Soma.Holonics.Millennium.HodgeDimensionBoundedLefschetz.DimensionBoundedLefschetzSystem

/-! ## The exact finite-rank form of one primitive obligation -/

/-- [proved-derived; formal-checked] In a finite primitive carrier, occupation of every complete
cycle-lift fibre is equivalent to equality of the actual algebraic primitive rank and the full
primitive rank.  The forward direction retains source membership before taking dimensions; the
reverse direction first proves the algebraic subspace is top and only then reconstructs fibres. -/
theorem primitiveLiftable_iff_algebraicFinrank_eq
    {lower upper : Datum} (step : PrimitiveHodgeStep lower upper)
    (finitePrimitive : FiniteDimensional ℚ step.Primitive) :
    step.PrimitiveLiftable ↔
      Module.finrank ℚ (primitiveAlgebraicClasses step) =
        Module.finrank ℚ step.Primitive := by
  letI : FiniteDimensional ℚ step.Primitive := finitePrimitive
  constructor
  · intro liftable
    have algebraicTop : primitiveAlgebraicClasses step = ⊤ := by
      apply eq_top_iff.mpr
      intro primitive _
      change
        (((primitive : step.Primitive) : upper.rationalHodgeClasses) :
          upper.Cohomology) ∈ upper.algebraicSpan
      rw [← cycleLiftFibre_nonempty_iff_mem_algebraicSpan]
      exact liftable primitive
    rw [algebraicTop, finrank_top]
  · intro equalRank
    have algebraicTop : primitiveAlgebraicClasses step = ⊤ :=
      Submodule.eq_top_of_finrank_eq equalRank
    intro primitive
    rw [cycleLiftFibre_nonempty_iff_mem_algebraicSpan]
    change primitive ∈ primitiveAlgebraicClasses step
    rw [algebraicTop]
    exact Submodule.mem_top

/-! ## A finite source whose rank pays into the primitive receiver -/

/-- [definition] A source-bearing finite-rank comparison into one primitive Hodge carrier.

The source is not identified with a coordinate count.  `cycleSource` retains its actual algebraic
cycle current, while `primitiveClass` is the returned primitive receiver face.  Injectivity and
equal finite rank imply surjectivity; no surjectivity or primitive conclusion is stored. -/
structure FiniteRankPrimitiveSource {lower upper : Datum}
    (step : PrimitiveHodgeStep lower upper)
    (Source : Type*) [AddCommGroup Source] [Module ℚ Source] where
  finiteDimensionalSource : FiniteDimensional ℚ Source
  finiteDimensionalPrimitive : FiniteDimensional ℚ step.Primitive
  cycleSource : Source →ₗ[ℚ] upper.CycleSpace
  primitiveClass : Source →ₗ[ℚ] step.Primitive
  cycleClass_commutes : ∀ source,
    upper.cycleClass.hom (cycleSource source) =
      ((primitiveClass source : step.Primitive) : upper.rationalHodgeClasses)
  primitiveClass_injective : Function.Injective primitiveClass
  equalFinrank : Module.finrank ℚ Source = Module.finrank ℚ step.Primitive

namespace FiniteRankPrimitiveSource

variable {lower upper : Datum} {step : PrimitiveHodgeStep lower upper}
variable {Source : Type*} [AddCommGroup Source] [Module ℚ Source]

/-- [definition] The comparison itself is an elementary source-retaining Holon.  Its occurrence
is one source current and its receiver face is the induced primitive Hodge class. -/
def sourceHolon (comparison : FiniteRankPrimitiveSource step Source) :
    Holon Source step.Primitive step.Primitive where
  Occurrence := Source
  source source := source
  target source := comparison.primitiveClass source
  receive source := comparison.primitiveClass source

/-- [proved-derived; formal-checked] Every presented source has its own occupied reconstruction
fibre before any rank completion is used. -/
theorem sourceHolon_fibre_occupied
    (comparison : FiniteRankPrimitiveSource step Source) (source : Source) :
    Nonempty (comparison.sourceHolon.ReconstructionFibre
      (comparison.primitiveClass source)) :=
  ⟨⟨source, rfl⟩⟩

/-- [proved-derived; formal-checked] Injectivity plus equal finite rank forces the primitive-class
current onto the full receiver. -/
theorem primitiveClass_surjective
    (comparison : FiniteRankPrimitiveSource step Source) :
    Function.Surjective comparison.primitiveClass := by
  letI : FiniteDimensional ℚ Source := comparison.finiteDimensionalSource
  letI : FiniteDimensional ℚ step.Primitive := comparison.finiteDimensionalPrimitive
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank comparison.equalFinrank).mp
      comparison.primitiveClass_injective

/-- [proved-derived; formal-checked] The finite source and primitive receiver are linearly
equivalent.  This is the reversible chart transition returned by the rank comparison. -/
noncomputable def primitiveEquiv
    (comparison : FiniteRankPrimitiveSource step Source) :
    Source ≃ₗ[ℚ] step.Primitive :=
  LinearEquiv.ofBijective comparison.primitiveClass
    ⟨comparison.primitiveClass_injective, comparison.primitiveClass_surjective⟩

/-- [proved-derived; formal-checked] Every primitive receiver occurrence reconstructs an actual
cycle antecedent through the inverse finite source chart and the retained cycle-class square. -/
noncomputable def reconstructedCycleLift
    (comparison : FiniteRankPrimitiveSource step Source)
    (primitive : step.Primitive) :
    CycleLiftFibre upper (primitive : upper.rationalHodgeClasses) := by
  let source : Source := comparison.primitiveEquiv.symm primitive
  refine ⟨comparison.cycleSource source, ?_⟩
  calc
    upper.cycleClass.hom (comparison.cycleSource source) =
        ((comparison.primitiveClass source : step.Primitive) :
          upper.rationalHodgeClasses) := comparison.cycleClass_commutes source
    _ = (primitive : upper.rationalHodgeClasses) := by
      have returned : comparison.primitiveClass source = primitive := by
        exact comparison.primitiveEquiv.apply_symm_apply primitive
      exact congrArg (fun value : step.Primitive =>
        (((value : step.Primitive) : upper.rationalHodgeClasses) :
          upper.Cohomology)) returned

/-- [proved-derived; formal-checked] A finite source of matching rank closes the complete
primitive cycle-lift obligation. -/
theorem primitiveLiftable
    (comparison : FiniteRankPrimitiveSource step Source) :
    step.PrimitiveLiftable := by
  intro primitive
  exact ⟨comparison.reconstructedCycleLift primitive⟩

/-- [proved-derived; formal-checked] The same source comparison returns the exact algebraic
primitive rank equality, retaining the direction from source construction to receiver shadow. -/
theorem algebraicFinrank_eq
    (comparison : FiniteRankPrimitiveSource step Source) :
    Module.finrank ℚ (primitiveAlgebraicClasses step) =
      Module.finrank ℚ step.Primitive :=
  (primitiveLiftable_iff_algebraicFinrank_eq step
    comparison.finiteDimensionalPrimitive).mp comparison.primitiveLiftable

end FiniteRankPrimitiveSource

/-! ## The finite lower-half rank receiver -/

/-- [definition] The complete finite population of lower primitive rank equalities for one
dimension-bounded smooth-projective receiver. -/
def FiniteLowerPrimitiveRankComplete {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (finitePrimitive : ∀ index : LowerPrimitiveIndex system.dimension,
      FiniteDimensional ℚ
        (system.lowStep index (lowerHalf_of_index index)).Primitive) : Prop :=
  ∀ index : LowerPrimitiveIndex system.dimension,
    letI := finitePrimitive index
    Module.finrank ℚ
        (primitiveAlgebraicClasses
          (system.lowStep index (lowerHalf_of_index index))) =
      Module.finrank ℚ
        (system.lowStep index (lowerHalf_of_index index)).Primitive

/-- [proved-derived; formal-checked] The exact finite lower primitive lift population and its
finite-rank receiver shadow are equivalent. -/
theorem finiteLowerPrimitiveLiftable_iff_rankComplete {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (finitePrimitive : ∀ index : LowerPrimitiveIndex system.dimension,
      FiniteDimensional ℚ
        (system.lowStep index (lowerHalf_of_index index)).Primitive) :
    system.FiniteLowerPrimitiveLiftable ↔
      FiniteLowerPrimitiveRankComplete system finitePrimitive := by
  constructor
  · intro liftable index
    exact
      (primitiveLiftable_iff_algebraicFinrank_eq
        (system.lowStep index (lowerHalf_of_index index))
        (finitePrimitive index)).mp (liftable index)
  · intro rankComplete index
    exact
      (primitiveLiftable_iff_algebraicFinrank_eq
        (system.lowStep index (lowerHalf_of_index index))
        (finitePrimitive index)).mpr (rankComplete index)

/-- [proved-derived; formal-checked] Once the standard dimension-bounded geometry and finite
primitive carriers are fixed, the classical Hodge receiver is exactly the finite population of
algebraic/full primitive rank equalities.  Each equality remains a receiver shadow of actual
cycle-lift occupation; it is not treated as a source by itself. -/
theorem theHodgeConjecture_iff_finiteLowerPrimitiveRankComplete
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (finitePrimitive : ∀ (R : Realization) (hR : Canonical R)
      (index : LowerPrimitiveIndex (system R hR).dimension),
      FiniteDimensional ℚ
        ((system R hR).lowStep index
          (lowerHalf_of_index index)).Primitive) :
    TheHodgeConjecture Canonical ↔
      ∀ (R : Realization) (hR : Canonical R),
        FiniteLowerPrimitiveRankComplete (system R hR)
          (finitePrimitive R hR) := by
  rw [theHodgeConjecture_iff_finiteLowerPrimitiveLiftable Canonical system]
  constructor
  · intro liftable R hR
    exact (finiteLowerPrimitiveLiftable_iff_rankComplete
      (system R hR) (finitePrimitive R hR)).mp (liftable R hR)
  · intro rankComplete R hR
    exact (finiteLowerPrimitiveLiftable_iff_rankComplete
      (system R hR) (finitePrimitive R hR)).mpr (rankComplete R hR)

section Audit

#print axioms primitiveLiftable_iff_algebraicFinrank_eq
#print axioms FiniteRankPrimitiveSource.primitiveClass_surjective
#print axioms FiniteRankPrimitiveSource.primitiveEquiv
#print axioms FiniteRankPrimitiveSource.reconstructedCycleLift
#print axioms FiniteRankPrimitiveSource.primitiveLiftable
#print axioms FiniteRankPrimitiveSource.algebraicFinrank_eq
#print axioms finiteLowerPrimitiveLiftable_iff_rankComplete
#print axioms theHodgeConjecture_iff_finiteLowerPrimitiveRankComplete

end Audit

end Soma.Holonics.Millennium.HodgeFinitePrimitiveRank
