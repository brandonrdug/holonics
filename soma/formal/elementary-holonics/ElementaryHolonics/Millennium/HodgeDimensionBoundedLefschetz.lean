import ElementaryHolonics.Millennium.HodgeSmoothProjectiveReceiver

/-!
# Dimension-bounded Lefschetz transport

An infinite staircase of injective hyperplane transports is not the geometry of a smooth
projective variety: hard Lefschetz is injective only through the lower half of cohomology.  Above
the middle, the exact passage is a surjective reflection from complementary degree; above the
complex dimension, cohomology vanishes.

This file installs that finite receiver without assuming a Hodge conclusion.  Lower-half
primitive liftability is propagated by the existing source-bearing primitive step.  A separate
source transport realizes the upper-half hard-Lefschetz return, and an actual zero cohomology
carrier closes degrees above the dimension.  The resulting theorem isolates precisely the finite
population of primitive algebraicity obligations which can remain on one variety.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Soma.Holonics.Millennium.HodgeDimensionBoundedLefschetz

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver

/-! ## Surjective upper-half transport -/

/-- [definition] A source-retaining transport from one lower Hodge receiver onto one upper Hodge
receiver.  In geometric use this is the appropriate power of the hyperplane class supplied by
hard Lefschetz. -/
structure SurjectiveHodgeTransport (lower upper : Datum) where
  cycleTransport : lower.CycleSpace →ₗ[ℚ] upper.CycleSpace
  hodgeTransport : lower.rationalHodgeClasses →ₗ[ℚ] upper.rationalHodgeClasses
  cycleClass_commutes : ∀ cycle : lower.CycleSpace,
    upper.cycleClass.hom (cycleTransport cycle) =
      (hodgeTransport
        ⟨lower.cycleClass.hom cycle,
          lower.cycleClassesAreHodge ⟨cycle, rfl⟩⟩ : upper.Cohomology)
  hodgeTransport_surjective : Function.Surjective hodgeTransport

namespace SurjectiveHodgeTransport

variable {lower upper : Datum}

/-- [proved-derived; formal-checked] A surjective Hodge transport whose source transport commutes
with cycle classes carries an established lower algebraicity conclusion to the upper receiver. -/
theorem hodgeConclusion
    (transport : SurjectiveHodgeTransport lower upper)
    (lowerConclusion : lower.Conclusion) :
    upper.Conclusion := by
  rw [hodgeConclusion_iff_every_cycleLiftFibre_nonempty]
  intro upperClass
  obtain ⟨lowerClass, lowerReturns⟩ :=
    transport.hodgeTransport_surjective upperClass
  obtain ⟨lowerLift⟩ :=
    (hodgeConclusion_iff_every_cycleLiftFibre_nonempty lower).mp
      lowerConclusion lowerClass
  let lowerCycle : lower.CycleSpace := lowerLift.1
  have lowerClassIdentity :
      (⟨lower.cycleClass.hom lowerCycle,
          lower.cycleClassesAreHodge ⟨lowerCycle, rfl⟩⟩ :
        lower.rationalHodgeClasses) = lowerClass := by
    apply Subtype.ext
    exact lowerLift.2
  refine ⟨⟨transport.cycleTransport lowerCycle, ?_⟩⟩
  calc
    upper.cycleClass.hom (transport.cycleTransport lowerCycle) =
        (transport.hodgeTransport
          ⟨lower.cycleClass.hom lowerCycle,
            lower.cycleClassesAreHodge ⟨lowerCycle, rfl⟩⟩ : upper.Cohomology) :=
      transport.cycleClass_commutes lowerCycle
    _ = (transport.hodgeTransport lowerClass : upper.Cohomology) := by
      rw [lowerClassIdentity]
    _ = (upperClass : upper.Cohomology) := congrArg Subtype.val lowerReturns

end SurjectiveHodgeTransport

/-! ## Exact vanishing beyond geometric dimension -/

/-- [proved-derived; formal-checked] A genuinely zero cohomology carrier has no open Hodge
occurrence: both the middle receiver and the algebraic range contain only the null class. -/
theorem hodgeConclusion_of_isZeroCohomology (D : Datum)
    (zeroCohomology : IsZero D.Cohomology) :
    D.Conclusion := by
  letI : Subsingleton D.Cohomology :=
    ModuleCat.subsingleton_of_isZero zeroCohomology
  apply le_antisymm
  · intro hodgeClass _
    rw [Subsingleton.elim hodgeClass 0]
    exact Submodule.zero_mem D.algebraicSpan
  · exact D.cycleClassesAreHodge

/-! ## One finite source-indexed Lefschetz system -/

/-- [definition] The exact finite Lefschetz geometry required on one genuine realization.

* `lowInjectiveStep` is requested only where `2p < dimension`, exactly the injective range;
* `highReflection` transports the complementary lower codimension `dimension - p` onto every
  upper-half receiver still inside the geometric dimension; and
* `aboveDimension` retains actual zero cohomology testimony rather than an authored conclusion.
-/
structure DimensionBoundedLefschetzSystem (R : Realization) where
  baseLift : ∀ hodgeClass : (R.datum 0).rationalHodgeClasses,
    Nonempty (CycleLiftFibre (R.datum 0) hodgeClass)
  lowInjectiveStep : ∀ (p : ℕ), 2 * p < R.complexDimension →
    InjectiveLefschetzStep R p
  highReflection : ∀ (p : ℕ), p ≤ R.complexDimension →
      R.complexDimension < 2 * p →
    SurjectiveHodgeTransport (R.datum (R.complexDimension - p)) (R.datum p)
  aboveDimension : ∀ (p : ℕ), R.complexDimension < p →
    IsZero (R.datum p).Cohomology

namespace DimensionBoundedLefschetzSystem

variable {R : Realization}

/-- [definition] The Lefschetz system consumes the realization's dimension occurrence; it owns
no independently authored natural number. -/
abbrev dimension (_system : DimensionBoundedLefschetzSystem R) : ℕ :=
  R.complexDimension

/-- [definition] The lower primitive returned-difference carrier is reconstructed from the
source-indexed injective Lefschetz square; it is not an independently authored decomposition. -/
noncomputable def lowStep (system : DimensionBoundedLefschetzSystem R)
    (p : ℕ) (lowerHalf : 2 * p < system.dimension) :
    PrimitiveHodgeStep (R.datum p) (R.datum (p + 1)) :=
  (system.lowInjectiveStep p lowerHalf).toPrimitiveHodgeStep

/-- [proved-derived; formal-checked] The codimension-zero conclusion is reconstructed from the
complete population of retained base cycle-lift fibres; it is not stored as a conclusion field. -/
theorem baseConclusion (system : DimensionBoundedLefschetzSystem R) :
    (R.datum 0).Conclusion :=
  (hodgeConclusion_iff_every_cycleLiftFibre_nonempty (R.datum 0)).mpr system.baseLift

/-- [definition] The exact finite index carrier of primitive steps needed to reconstruct the
closed lower half of a complex `dimension`-fold.  Its cardinality is `floor(dimension / 2)`:
the extra step into the first upper-half codimension in odd dimension is excluded because the
source-bearing hard-Lefschetz reflection already returns that receiver. -/
abbrev LowerPrimitiveIndex (dimension : ℕ) := Fin (dimension / 2)

/-- [proved-derived; formal-checked] The residual source population has exactly
`floor(dimension / 2)` addressed occurrences. -/
@[simp]
theorem lowerPrimitiveIndex_card (dimension : ℕ) :
    Fintype.card (LowerPrimitiveIndex dimension) = dimension / 2 := by
  simp only [LowerPrimitiveIndex, Fintype.card_fin]

/-- [proved-derived; formal-checked] Every retained finite index is an actually required step:
its target codimension `index + 1` remains in the closed lower half. -/
theorem lowerStepRequired_of_index {dimension : ℕ}
    (index : LowerPrimitiveIndex dimension) :
    2 * ((index : ℕ) + 1) ≤ dimension := by
  omega

/-- [proved-derived; formal-checked] A retained target in the closed lower half supplies the
strict source inequality required by the injective Lefschetz step. -/
theorem lowerHalf_of_required {dimension p : ℕ}
    (required : 2 * (p + 1) ≤ dimension) :
    2 * p < dimension := by
  omega

/-- [proved-derived; formal-checked] Every finite lower index lies strictly below the Lefschetz
middle: the multiplication by two is the geometric degree/codimension passage. -/
theorem lowerHalf_of_index {dimension : ℕ} (index : LowerPrimitiveIndex dimension) :
    2 * (index : ℕ) < dimension := by
  omega

/-- [definition] Every required lower primitive step has its exact occurrence in the finite
index carrier. -/
def indexOfLowerStep {dimension p : ℕ} (required : 2 * (p + 1) ≤ dimension) :
    LowerPrimitiveIndex dimension :=
  ⟨p, by omega⟩

@[simp]
theorem indexOfLowerStep_value {dimension p : ℕ}
    (required : 2 * (p + 1) ≤ dimension) :
    (indexOfLowerStep required : ℕ) = p := rfl

/-- [definition] The same lower primitive source obligation written over its finite carrier. -/
def FiniteLowerPrimitiveLiftable
    (system : DimensionBoundedLefschetzSystem R) : Prop :=
  ∀ index : LowerPrimitiveIndex system.dimension,
    (system.lowStep index (lowerHalf_of_index index)).PrimitiveLiftable

/-- [definition] The minimal conjectural population: primitive cycle lifts are required only for
steps whose target remains in the closed lower half.  In an odd dimension the next injective
step lands in the upper half and is deliberately absent. -/
def LowerPrimitiveLiftable
    (system : DimensionBoundedLefschetzSystem R) : Prop :=
  ∀ (p : ℕ) (required : 2 * (p + 1) ≤ system.dimension),
    (system.lowStep p (lowerHalf_of_required required)).PrimitiveLiftable

/-- [proved-derived; formal-checked] The inequality-indexed lower obligation and the exact finite
carrier are equivalent.  This is the non-Zeno audit: one variety emits a bounded population of
primitive source cuts, not an open-ended staircase. -/
theorem lowerPrimitiveLiftable_iff_finite
    (system : DimensionBoundedLefschetzSystem R) :
    system.LowerPrimitiveLiftable ↔ system.FiniteLowerPrimitiveLiftable := by
  constructor
  · intro liftable index
    exact liftable index (lowerStepRequired_of_index index)
  · intro finiteLiftable p required
    simpa only [indexOfLowerStep_value] using
      finiteLiftable (indexOfLowerStep required)

/-- [proved-derived; formal-checked] Complex dimension zero or one emits no primitive source
obligation: the exact lower index carrier is empty. -/
theorem lowerPrimitiveLiftable_of_dimension_lt_two
    (system : DimensionBoundedLefschetzSystem R)
    (smallDimension : system.dimension < 2) :
    system.LowerPrimitiveLiftable := by
  intro p required
  omega

/-- [proved-derived; formal-checked] Lower-half primitive lifts propagate from codimension zero
through every receiver satisfying `2p ≤ dimension`. -/
theorem lowerConclusion
    (system : DimensionBoundedLefschetzSystem R)
    (primitiveLiftable : system.LowerPrimitiveLiftable) :
    ∀ (p : ℕ), 2 * p ≤ system.dimension → (R.datum p).Conclusion := by
  intro p
  induction p with
  | zero =>
      intro _
      exact system.baseConclusion
  | succ p lowerConclusion =>
      intro upperInLowerHalf
      have stepRequired : 2 * (p + 1) ≤ system.dimension := upperInLowerHalf
      exact
        (system.lowStep p (lowerHalf_of_required stepRequired)).hodgeConclusion_of_lower_of_primitiveLiftable
          (lowerConclusion (by omega))
          (primitiveLiftable p stepRequired)

/-- [proved-derived; formal-checked] The finite lower staircase, upper hard-Lefschetz reflection,
and above-dimension vanishing close every codimension of the genuine realization. -/
theorem allConclusions
    (system : DimensionBoundedLefschetzSystem R)
    (primitiveLiftable : system.LowerPrimitiveLiftable) :
    ∀ p : ℕ, (R.datum p).Conclusion := by
  intro p
  by_cases insideDimension : p ≤ system.dimension
  · by_cases lowerHalf : 2 * p ≤ system.dimension
    · exact system.lowerConclusion primitiveLiftable p lowerHalf
    · have upperHalf : system.dimension < 2 * p := by omega
      have reflectedLowerHalf :
          2 * (system.dimension - p) ≤ system.dimension := by omega
      exact
        (system.highReflection p insideDimension upperHalf).hodgeConclusion
          (system.lowerConclusion primitiveLiftable
            (system.dimension - p) reflectedLowerHalf)
  · have aboveDimension : R.complexDimension < p := by
      change ¬ p ≤ R.complexDimension at insideDimension
      omega
    exact hodgeConclusion_of_isZeroCohomology (R.datum p)
      (system.aboveDimension p aboveDimension)

/-- [proved-derived; formal-checked] On a zero- or one-dimensional admitted realization, the
base source, hard-Lefschetz reflection, and vanishing close every codimension without a primitive
algebraicity hypothesis. -/
theorem allConclusions_of_dimension_lt_two
    (system : DimensionBoundedLefschetzSystem R)
    (smallDimension : system.dimension < 2) :
    ∀ p : ℕ, (R.datum p).Conclusion :=
  system.allConclusions
    (system.lowerPrimitiveLiftable_of_dimension_lt_two smallDimension)

end DimensionBoundedLefschetzSystem

/-! ## Universal composition -/

/-- [proved-derived; formal-checked] A canonically admitted family is reduced to a finite
primitive population on each source: no impossible infinite injective staircase remains. -/
theorem theHodgeConjecture_of_dimensionBoundedLefschetz
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (primitiveLiftable : ∀ (R : Realization) (hR : Canonical R),
      (system R hR).LowerPrimitiveLiftable) :
    TheHodgeConjecture Canonical := by
  intro R hR
  exact (system R hR).allConclusions (primitiveLiftable R hR)

/-- [proved-derived; formal-checked] A canonically admitted family of complex dimension at most
one satisfies the complete Hodge receiver from the standard dimension-bounded geometry alone. -/
theorem theHodgeConjecture_of_dimension_lt_two
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (smallDimension : ∀ (R : Realization) (hR : Canonical R),
      (system R hR).dimension < 2) :
    TheHodgeConjecture Canonical := by
  intro R hR
  exact (system R hR).allConclusions_of_dimension_lt_two
    (smallDimension R hR)

/-- [proved-derived; formal-checked] Once the standard dimension-bounded geometry is fixed, the
classical universal receiver is exactly the finite population of lower-half primitive cycle-source
fibres.  This equivalence is the complete assumption audit before choosing a detector,
monodromy, or any other method of constructing those sources. -/
theorem theHodgeConjecture_iff_finiteLowerPrimitiveLiftable
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R) :
    TheHodgeConjecture Canonical ↔
      ∀ (R : Realization) (hR : Canonical R),
        (system R hR).FiniteLowerPrimitiveLiftable := by
  constructor
  · intro hodge R hR
    rw [← (system R hR).lowerPrimitiveLiftable_iff_finite]
    intro p required
    exact
      (((system R hR).lowStep p
          (DimensionBoundedLefschetzSystem.lowerHalf_of_required
            required)).hodgeConclusion_iff_primitiveLiftable_of_lower
        (hodge R hR p)).mp (hodge R hR (p + 1))
  · intro finiteLiftable
    apply theHodgeConjecture_of_dimensionBoundedLefschetz Canonical system
    intro R hR
    exact ((system R hR).lowerPrimitiveLiftable_iff_finite).mpr
      (finiteLiftable R hR)

/-- [proved-derived; formal-checked] The source-determined universal receiver has one graded
residual, not a succession of independently scheduled homology computations.  A single
dimension-bounded Lefschetz system transports the codimension-zero source through the whole lower
half, reflects the upper half, and closes the above-dimension carrier.  Consequently *all* degrees
on *all* smooth-projective sources are equivalent to occupation of the finite primitive source
fibre indexed by that source's dimension.

This is the non-Zeno source form: specializing the theorem at `p - 1`, `p`, or `p + 1` introduces
no new proof obligation.  Every such face is reconstructed by the same successor/reflection law.
-/
theorem SourceDeterminedHodgeTheory.conclusion_iff_finiteLowerPrimitiveLiftable
    (theory : SourceDeterminedHodgeTheory)
    (system : ∀ geometry : SmoothProjectiveComplexScheme,
      DimensionBoundedLefschetzSystem (theory.realization geometry)) :
    theory.Conclusion ↔
      ∀ geometry : SmoothProjectiveComplexScheme,
        (system geometry).FiniteLowerPrimitiveLiftable := by
  constructor
  · intro conclusion geometry
    rw [← (system geometry).lowerPrimitiveLiftable_iff_finite]
    intro p required
    exact
      (((system geometry).lowStep p
          (DimensionBoundedLefschetzSystem.lowerHalf_of_required required)).hodgeConclusion_iff_primitiveLiftable_of_lower
        (conclusion geometry p)).mp (conclusion geometry (p + 1))
  · intro finiteLiftable geometry
    exact (system geometry).allConclusions
      ((system geometry).lowerPrimitiveLiftable_iff_finite.mpr
        (finiteLiftable geometry))

section Audit

#print axioms SurjectiveHodgeTransport.hodgeConclusion
#print axioms hodgeConclusion_of_isZeroCohomology
#print axioms DimensionBoundedLefschetzSystem.baseConclusion
#print axioms DimensionBoundedLefschetzSystem.lowerPrimitiveLiftable_iff_finite
#print axioms DimensionBoundedLefschetzSystem.lowerPrimitiveLiftable_of_dimension_lt_two
#print axioms DimensionBoundedLefschetzSystem.lowerConclusion
#print axioms DimensionBoundedLefschetzSystem.allConclusions
#print axioms DimensionBoundedLefschetzSystem.allConclusions_of_dimension_lt_two
#print axioms theHodgeConjecture_of_dimensionBoundedLefschetz
#print axioms theHodgeConjecture_of_dimension_lt_two
#print axioms theHodgeConjecture_iff_finiteLowerPrimitiveLiftable
#print axioms SourceDeterminedHodgeTheory.conclusion_iff_finiteLowerPrimitiveLiftable

end Audit

end Soma.Holonics.Millennium.HodgeDimensionBoundedLefschetz
