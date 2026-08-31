import ElementaryHolonics.Foundation.EuclideanResidueTransport
import ElementaryHolonics.Millennium.HodgeFinitePrimitiveRank

/-!
# The divisor exponential passage into the Hodge receiver

The first nontrivial Hodge source is not a numerical rank assertion.  The classical
Lefschetz `(1,1)` mechanism is an exact local-to-global current: a rationalized Picard source
maps by first Chern class into rationalized integral degree-two cohomology, whose analytic
obstruction vanishes precisely on the divisor image.  The resulting line-bundle occurrence then
returns an actual codimension-one algebraic cycle through the cycle-class commuting square.

This file retains every part of that passage.  It does not assume surjectivity onto the Hodge
receiver.  Exactness and obstruction nullity derive the source occurrence.  Composed with the
minimal dimension-bounded Lefschetz receiver, the passage closes all codimensions in complex
dimension at most three; reflection supplies the upper half.  Consequently the first primitive
obligation not covered by this divisor mechanism occurs at codimension two in dimension four.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeDivisorExponentialPassage

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver
open Soma.Holonics.Millennium.HodgeDimensionBoundedLefschetz
open Soma.Holonics.Millennium.HodgeDimensionBoundedLefschetz.DimensionBoundedLefschetzSystem
open Soma.Holonics.Millennium.HodgeFinitePrimitiveRank
open Soma.Holonics.Foundation.EuclideanResidueTransport

/-! ## One exact divisor source passage -/

/-- [definition] A source-bearing rational form of the exponential-sequence divisor passage for
one Hodge datum.

`PicardRational` and `IntegralCohomologyRational` are already transported to the rational receiver
chart, but remain distinct addressed module carriers.  `exponentialExact` is the local-to-global
kernel law.  `hodgeIntegralLift` retains the integral-rational antecedent of each rational Hodge
class, and `divisorCycle` retains the actual algebraic-cycle current associated with the Picard
source. -/
structure DivisorExponentialPassage (D : Datum) where
  PicardRational : ModuleCat ℚ
  IntegralCohomologyRational : ModuleCat ℚ
  AnalyticObstruction : ModuleCat ℚ
  firstChern : PicardRational ⟶ IntegralCohomologyRational
  obstruction : IntegralCohomologyRational ⟶ AnalyticObstruction
  exponentialExact : Function.Exact firstChern.hom obstruction.hom
  hodgeIntegralLift :
    ModuleCat.of ℚ D.rationalHodgeClasses ⟶ IntegralCohomologyRational
  integralClass : IntegralCohomologyRational ⟶ D.Cohomology
  hodgeIntegralLift_commutes : ∀ hodgeClass,
    integralClass.hom (hodgeIntegralLift.hom hodgeClass) =
      (hodgeClass : D.Cohomology)
  hodgeObstruction_zero : ∀ hodgeClass,
    obstruction.hom (hodgeIntegralLift.hom hodgeClass) = 0
  divisorCycle : PicardRational ⟶ D.CycleSpace
  firstChern_cycleClass_commutes : ∀ lineBundle,
    D.cycleClass.hom (divisorCycle.hom lineBundle) =
      integralClass.hom (firstChern.hom lineBundle)

namespace DivisorExponentialPassage

variable {D : Datum}

/-- [proved-derived; formal-checked] Every rational Hodge occurrence reconstructs a rationalized
Picard antecedent.  This is exactness applied to the vanishing analytic obstruction, not a stored
surjectivity field. -/
theorem firstChern_preimage
    (passage : DivisorExponentialPassage D)
    (hodgeClass : D.rationalHodgeClasses) :
    ∃ lineBundle : passage.PicardRational,
      passage.firstChern.hom lineBundle =
        passage.hodgeIntegralLift.hom hodgeClass := by
  have inKernel :
      passage.hodgeIntegralLift.hom hodgeClass ∈
        LinearMap.ker passage.obstruction.hom := by
    rw [LinearMap.mem_ker]
    exact passage.hodgeObstruction_zero hodgeClass
  have inRange :
      passage.hodgeIntegralLift.hom hodgeClass ∈
        LinearMap.range passage.firstChern.hom := by
    rw [← LinearMap.exact_iff.mp passage.exponentialExact]
    exact inKernel
  exact inRange

/-- [proved-derived; formal-checked] The Picard antecedent returns an actual codimension-one
cycle occurrence whose cycle class is the requested rational Hodge class. -/
theorem cycleLiftFibre_nonempty
    (passage : DivisorExponentialPassage D)
    (hodgeClass : D.rationalHodgeClasses) :
    Nonempty (CycleLiftFibre D hodgeClass) := by
  obtain ⟨lineBundle, firstChernReturns⟩ := passage.firstChern_preimage hodgeClass
  refine ⟨⟨passage.divisorCycle.hom lineBundle, ?_⟩⟩
  calc
    D.cycleClass.hom (passage.divisorCycle.hom lineBundle) =
        passage.integralClass.hom (passage.firstChern.hom lineBundle) :=
      passage.firstChern_cycleClass_commutes lineBundle
    _ = passage.integralClass.hom
        (passage.hodgeIntegralLift.hom hodgeClass) := by
      rw [firstChernReturns]
    _ = (hodgeClass : D.Cohomology) :=
      passage.hodgeIntegralLift_commutes hodgeClass

/-- [proved-derived; formal-checked] An exact divisor exponential passage closes the complete
Hodge conclusion of its degree-two datum. -/
theorem hodgeConclusion (passage : DivisorExponentialPassage D) : D.Conclusion :=
  (hodgeConclusion_iff_every_cycleLiftFibre_nonempty D).mpr
    passage.cycleLiftFibre_nonempty

end DivisorExponentialPassage

/-! ## The exact low-dimensional consequence -/

/-- [proved-derived; formal-checked] A divisor passage on codimension one closes the first
primitive step whenever that step is required. -/
theorem codimensionOnePrimitiveLiftable {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (atLeastTwo : 2 ≤ system.dimension)
    (divisors : DivisorExponentialPassage (R.datum 1)) :
    (system.lowStep 0 (by omega)).PrimitiveLiftable :=
  ((system.lowStep 0 (by omega)).hodgeConclusion_iff_primitiveLiftable_of_lower
    system.baseConclusion).mp divisors.hodgeConclusion

/-- [proved-derived; formal-checked] In complex dimension at most three, every retained lower
primitive index is the divisor step `p = 0`.  The exact divisor passage therefore closes the
minimal lower primitive population. -/
theorem lowerPrimitiveLiftable_of_dimension_lt_four {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (smallDimension : system.dimension < 4)
    (divisors : DivisorExponentialPassage (R.datum 1)) :
    system.LowerPrimitiveLiftable := by
  intro p required
  have pZero : p = 0 := by omega
  subst p
  exact codimensionOnePrimitiveLiftable system (by omega) divisors

/-- [proved-derived; formal-checked] The divisor exponential passage, lower Lefschetz step,
upper reflection, and vanishing close every Hodge codimension on one admitted realization of
complex dimension at most three. -/
theorem allConclusions_of_dimension_lt_four {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (smallDimension : system.dimension < 4)
    (divisors : DivisorExponentialPassage (R.datum 1)) :
    ∀ p : ℕ, (R.datum p).Conclusion :=
  system.allConclusions
    (lowerPrimitiveLiftable_of_dimension_lt_four system smallDimension divisors)

/-- [proved-derived; formal-checked] A canonical smooth-projective family of complex dimension
at most three satisfies the complete Hodge receiver once its genuine divisor exponential passage
is constructed. -/
theorem theHodgeConjecture_of_divisorExponentialPassage_dimension_lt_four
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (smallDimension : ∀ (R : Realization) (hR : Canonical R),
      (system R hR).dimension < 4)
    (divisors : ∀ (R : Realization), Canonical R →
      DivisorExponentialPassage (R.datum 1)) :
    TheHodgeConjecture Canonical := by
  intro R hR
  exact allConclusions_of_dimension_lt_four (system R hR)
    (smallDimension R hR) (divisors R hR)

/-! ## Removing the divisor index from the universal residual -/

/-- [definition] The exact remaining primitive index carrier after the divisor step has been
closed.  Its occurrence `i` addresses the original primitive step `p = i + 1`, whose target has
codimension at least two. -/
abbrev HigherPrimitiveIndex (dimension : ℕ) := Fin (dimension / 2 - 1)

/-! ### The lower-half count is an exact Euclidean residue passage -/

/-- [proved-derived; formal-checked] The lower primitive population is the winding coordinate of
the lossless radix-two Euclidean chart of the complex dimension.  The equality is definitional;
`dimension / 2` is not a rounded measurement here. -/
theorem lowerPrimitiveIndex_card_eq_binaryWinding (dimension : ℕ) :
    Fintype.card (LowerPrimitiveIndex dimension) =
      ((natEuclideanHolon 2).target dimension).2 := by
  simp only [lowerPrimitiveIndex_card]
  change dimension / 2 = dimension / 2
  rfl

/-- [proved-derived; formal-checked] The dimension reconstructs exactly from its parity receiver
face and twice its lower-primitive winding coordinate. -/
theorem dimension_eq_parity_add_twice_lowerPrimitiveCard (dimension : ℕ) :
    dimension =
      ((natEuclideanHolon 2).receive dimension).val +
        2 * Fintype.card (LowerPrimitiveIndex dimension) := by
  simp only [lowerPrimitiveIndex_card]
  change dimension = (dimension : ZMod 2).val + 2 * (dimension / 2)
  rw [ZMod.val_natCast]
  exact (Nat.mod_add_div dimension 2).symm

/-- [proved-derived; formal-checked] The apparent difference between floor-half and ceiling-half
is exactly the binary residue face.  It is not an estimate or a second count convention. -/
theorem ceilingHalf_eq_lowerPrimitiveCard_add_parity (dimension : ℕ) :
    (dimension + 1) / 2 =
      Fintype.card (LowerPrimitiveIndex dimension) +
        ((natEuclideanHolon 2).receive dimension).val := by
  have residueBound : dimension % 2 < 2 := Nat.mod_lt dimension (by decide)
  simp only [lowerPrimitiveIndex_card]
  change (dimension + 1) / 2 = dimension / 2 + (dimension : ZMod 2).val
  rw [ZMod.val_natCast]
  omega

/-- [proved-derived; formal-checked] After divisor reconstruction, the number of remaining
primitive source apertures is exactly `floor(dimension / 2) - 1`. -/
@[simp]
theorem higherPrimitiveIndex_card (dimension : ℕ) :
    Fintype.card (HigherPrimitiveIndex dimension) = dimension / 2 - 1 := by
  simp only [HigherPrimitiveIndex, Fintype.card_fin]

/-- [proved-derived; formal-checked] After the divisor occurrence is removed, the remaining
higher primitive population is exactly one less than the same winding coordinate. -/
theorem higherPrimitiveIndex_card_eq_binaryWinding_sub_one (dimension : ℕ) :
    Fintype.card (HigherPrimitiveIndex dimension) =
      ((natEuclideanHolon 2).target dimension).2 - 1 := by
  simp only [higherPrimitiveIndex_card]
  change dimension / 2 - 1 = dimension / 2 - 1
  rfl

/-- [proved-derived; formal-checked] In every dimension where the divisor step exists, the full
dimension reconstructs from parity, the removed divisor occurrence, and the retained higher
primitive population. -/
theorem dimension_eq_parity_add_twice_higherPrimitiveCard_succ
    {dimension : ℕ} (divisorStepExists : 2 ≤ dimension) :
    dimension =
      ((natEuclideanHolon 2).receive dimension).val +
        2 * (Fintype.card (HigherPrimitiveIndex dimension) + 1) := by
  rw [higherPrimitiveIndex_card]
  have halfPositive : 0 < dimension / 2 := by omega
  have reconstructed := dimension_eq_parity_add_twice_lowerPrimitiveCard dimension
  simp only [lowerPrimitiveIndex_card] at reconstructed
  omega

/-- [definition] Insert a higher-cycle index into the complete lower primitive carrier. -/
def higherToLowerIndex {dimension : ℕ} (index : HigherPrimitiveIndex dimension) :
    LowerPrimitiveIndex dimension :=
  ⟨(index : ℕ) + 1, by omega⟩

@[simp]
theorem higherToLowerIndex_value {dimension : ℕ}
    (index : HigherPrimitiveIndex dimension) :
    (higherToLowerIndex index : ℕ) = (index : ℕ) + 1 := rfl

/-- [definition] The actual primitive Hodge step addressed by one higher-cycle index. -/
noncomputable def higherPrimitiveStep {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (index : HigherPrimitiveIndex system.dimension) :
    PrimitiveHodgeStep (R.datum ((index : ℕ) + 1))
      (R.datum (((index : ℕ) + 1) + 1)) :=
  system.lowStep ((index : ℕ) + 1) (by
    have indexBound := index.isLt
    omega)

/-- [definition] The exact finite population of primitive source obligations left after
codimension one has been reconstructed by the divisor exponential passage. -/
def HigherPrimitiveLiftable {R : Realization}
    (system : DimensionBoundedLefschetzSystem R) : Prop :=
  ∀ index : HigherPrimitiveIndex system.dimension,
    (higherPrimitiveStep system index).PrimitiveLiftable

/-- [proved-derived; formal-checked] Once the divisor passage closes `p = 0`, the complete
minimal lower primitive population is equivalent to its higher-cycle tail. -/
theorem lowerPrimitiveLiftable_iff_higher_of_divisors {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (divisors : DivisorExponentialPassage (R.datum 1)) :
    system.LowerPrimitiveLiftable ↔ HigherPrimitiveLiftable system := by
  constructor
  · intro lower index
    exact lower ((index : ℕ) + 1) (by
      have indexBound := index.isLt
      omega)
  · intro higher p required
    cases p with
    | zero =>
        exact codimensionOnePrimitiveLiftable system (by omega) divisors
    | succ p =>
        let index : HigherPrimitiveIndex system.dimension := ⟨p, by omega⟩
        exact higher index

/-- [proved-derived; formal-checked] Given the genuine divisor exponential passage on every
canonical realization, the official Hodge conjecture is exactly the remaining finite population
of codimension-at-least-two primitive cycle-source fibres. -/
theorem theHodgeConjecture_iff_higherPrimitiveLiftable_of_divisors
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (divisors : ∀ (R : Realization), Canonical R →
      DivisorExponentialPassage (R.datum 1)) :
    TheHodgeConjecture Canonical ↔
      ∀ (R : Realization) (hR : Canonical R),
        HigherPrimitiveLiftable (system R hR) := by
  constructor
  · intro hodge R hR
    have finiteLower :=
      (theHodgeConjecture_iff_finiteLowerPrimitiveLiftable Canonical system).mp
        hodge R hR
    have lower :=
      ((system R hR).lowerPrimitiveLiftable_iff_finite).mpr finiteLower
    exact
      (lowerPrimitiveLiftable_iff_higher_of_divisors
        (system R hR) (divisors R hR)).mp lower
  · intro higher
    apply theHodgeConjecture_of_dimensionBoundedLefschetz Canonical system
    intro R hR
    exact
      (lowerPrimitiveLiftable_iff_higher_of_divisors
        (system R hR) (divisors R hR)).mpr (higher R hR)

/-! ## Higher finite-rank sources and their exact receiver shadow -/

/-- [definition] Equality between the actual algebraic primitive rank and the full primitive rank
at every residual codimension-at-least-two index. -/
def HigherPrimitiveRankComplete {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (finitePrimitive : ∀ index : HigherPrimitiveIndex system.dimension,
      FiniteDimensional ℚ (higherPrimitiveStep system index).Primitive) : Prop :=
  ∀ index : HigherPrimitiveIndex system.dimension,
    letI := finitePrimitive index
    Module.finrank ℚ
        (primitiveAlgebraicClasses (higherPrimitiveStep system index)) =
      Module.finrank ℚ (higherPrimitiveStep system index).Primitive

/-- [proved-derived; formal-checked] Finite-dimensionality identifies the remaining source-fibre
population exactly with the remaining algebraic/full primitive rank equalities. -/
theorem higherPrimitiveLiftable_iff_rankComplete {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (finitePrimitive : ∀ index : HigherPrimitiveIndex system.dimension,
      FiniteDimensional ℚ (higherPrimitiveStep system index).Primitive) :
    HigherPrimitiveLiftable system ↔
      HigherPrimitiveRankComplete system finitePrimitive := by
  constructor
  · intro liftable index
    exact
      (primitiveLiftable_iff_algebraicFinrank_eq
        (higherPrimitiveStep system index)
        (finitePrimitive index)).mp (liftable index)
  · intro rankComplete index
    exact
      (primitiveLiftable_iff_algebraicFinrank_eq
        (higherPrimitiveStep system index)
        (finitePrimitive index)).mpr (rankComplete index)

/-- [definition] The complete source-bearing higher-cycle package.  Each addressed residual index
owns its source module and a `FiniteRankPrimitiveSource`, hence its actual cycle current and
cycle-class commuting square; no conclusion is stored. -/
structure HigherFiniteRankPrimitiveSources {R : Realization}
    (system : DimensionBoundedLefschetzSystem R) where
  Source : HigherPrimitiveIndex system.dimension → ModuleCat ℚ
  comparison : ∀ index : HigherPrimitiveIndex system.dimension,
    FiniteRankPrimitiveSource (higherPrimitiveStep system index) (Source index)

namespace HigherFiniteRankPrimitiveSources

/-- [proved-derived; formal-checked] The source-bearing family occupies every residual primitive
cycle-lift population. -/
theorem higherPrimitiveLiftable {R : Realization}
    {system : DimensionBoundedLefschetzSystem R}
    (sources : HigherFiniteRankPrimitiveSources system) :
    HigherPrimitiveLiftable system := by
  intro index
  exact (sources.comparison index).primitiveLiftable

end HigherFiniteRankPrimitiveSources

/-- [proved-derived; formal-checked] After the divisor passage, a finite-rank source package at
each remaining higher index closes the official universal Hodge receiver. -/
theorem theHodgeConjecture_of_higherFiniteRankPrimitiveSources
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (divisors : ∀ (R : Realization), Canonical R →
      DivisorExponentialPassage (R.datum 1))
    (sources : ∀ (R : Realization) (hR : Canonical R),
      HigherFiniteRankPrimitiveSources (system R hR)) :
    TheHodgeConjecture Canonical :=
  (theHodgeConjecture_iff_higherPrimitiveLiftable_of_divisors
    Canonical system divisors).mpr fun R hR =>
      (sources R hR).higherPrimitiveLiftable

/-- [proved-derived; formal-checked] Once the divisor passage and finite primitive carriers are
fixed, the official universal Hodge receiver is exactly the `floor(n/2)-1` population of actual
algebraic/full primitive rank equalities. -/
theorem theHodgeConjecture_iff_higherPrimitiveRankComplete_of_divisors
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (divisors : ∀ (R : Realization), Canonical R →
      DivisorExponentialPassage (R.datum 1))
    (finitePrimitive : ∀ (R : Realization) (hR : Canonical R)
      (index : HigherPrimitiveIndex (system R hR).dimension),
      FiniteDimensional ℚ (higherPrimitiveStep (system R hR) index).Primitive) :
    TheHodgeConjecture Canonical ↔
      ∀ (R : Realization) (hR : Canonical R),
        HigherPrimitiveRankComplete (system R hR)
          (finitePrimitive R hR) := by
  rw [theHodgeConjecture_iff_higherPrimitiveLiftable_of_divisors
    Canonical system divisors]
  constructor
  · intro liftable R hR
    exact
      (higherPrimitiveLiftable_iff_rankComplete
        (system R hR) (finitePrimitive R hR)).mp (liftable R hR)
  · intro rankComplete R hR
    exact
      (higherPrimitiveLiftable_iff_rankComplete
        (system R hR) (finitePrimitive R hR)).mpr (rankComplete R hR)

section Audit

#print axioms DivisorExponentialPassage.firstChern_preimage
#print axioms DivisorExponentialPassage.cycleLiftFibre_nonempty
#print axioms DivisorExponentialPassage.hodgeConclusion
#print axioms codimensionOnePrimitiveLiftable
#print axioms lowerPrimitiveLiftable_of_dimension_lt_four
#print axioms allConclusions_of_dimension_lt_four
#print axioms theHodgeConjecture_of_divisorExponentialPassage_dimension_lt_four
#print axioms lowerPrimitiveLiftable_iff_higher_of_divisors
#print axioms theHodgeConjecture_iff_higherPrimitiveLiftable_of_divisors
#print axioms higherPrimitiveLiftable_iff_rankComplete
#print axioms HigherFiniteRankPrimitiveSources.higherPrimitiveLiftable
#print axioms theHodgeConjecture_of_higherFiniteRankPrimitiveSources
#print axioms theHodgeConjecture_iff_higherPrimitiveRankComplete_of_divisors

end Audit

end Soma.Holonics.Millennium.HodgeDivisorExponentialPassage
