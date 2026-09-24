import ElementaryHolonics.Millennium.HodgeDimensionBoundedLefschetz
import ElementaryHolonics.Millennium.HodgeMonodromyPrimitivePropagation

/-!
# Dimension-bounded primitive propagation

The genuine smooth-projective receiver has only finitely many primitive algebraicity cuts on
each variety.  `HodgeDimensionBoundedLefschetz` isolates exactly the steps whose targets remain
in the closed lower half, `2(p+1) ≤ dim X`; hard-Lefschetz reflection and above-dimension
vanishing close every other degree.

This file rotates the existing elementary holonic detector and source-bearing monodromy owners
into that corrected receiver.  Pointwise detector occupation, one algebraic seed in each
irreducible monodromy block, and a source-bearing orbit cover are three exact constructions of
the same finite `LowerPrimitiveLiftable` return.  None is requested beyond the middle dimension.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeDimensionBoundedPrimitivePropagation

open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver
open Soma.Holonics.Millennium.HodgeHolonicPrimitiveCut
open Soma.Holonics.Millennium.HodgeMonodromyPrimitivePropagation
open Soma.Holonics.Millennium.HodgeDimensionBoundedLefschetz
open Soma.Holonics.Millennium.HodgeDimensionBoundedLefschetz.DimensionBoundedLefschetzSystem

/-! ## The finite holonic primitive cut -/

/-- [proved-derived; formal-checked] Occupying every nonzero primitive interaction fibre in the
lower half constructs the complete finite primitive return of a dimension-bounded system. -/
theorem lowerPrimitiveLiftable_of_detection {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (polarization : ∀ (p : ℕ) (required : 2 * (p + 1) ≤ system.dimension),
      SignedDefinitePrimitivePolarization
        (system.lowStep p (lowerHalf_of_required required)))
    (detects : ∀ (p : ℕ) (required : 2 * (p + 1) ≤ system.dimension),
      DetectsEveryNonzero (polarization p required)) :
    system.LowerPrimitiveLiftable := by
  intro p required
  exact (polarization p required).primitiveLiftable_of_detectsEveryNonzero
    (detects p required)

/-- [proved-derived; formal-checked] With the finite geometric Lefschetz system and its signed
polarizations fixed, the classical universal receiver is equivalent to occupation of every
nonzero source-bearing holonic detector fibre at precisely the lower-half primitive indices.

The reverse implication constructs all degrees by finite lower propagation, upper reflection,
and vanishing.  The forward implication recovers detector occurrences from the already occupied
cycle-lift fibres. -/
theorem hodge_iff_dimensionBoundedPrimitiveDetection
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (polarization : ∀ (R : Realization) (hR : Canonical R)
      (p : ℕ) (required : 2 * (p + 1) ≤ (system R hR).dimension),
      SignedDefinitePrimitivePolarization
        ((system R hR).lowStep p (lowerHalf_of_required required))) :
    TheHodgeConjecture Canonical ↔
      ∀ (R : Realization) (hR : Canonical R)
        (p : ℕ) (required : 2 * (p + 1) ≤ (system R hR).dimension),
        DetectsEveryNonzero (polarization R hR p required) := by
  constructor
  · intro hodge R hR p required
    apply (polarization R hR p required).detectsEveryNonzero_of_primitiveLiftable
    exact
      (((system R hR).lowStep p
          (lowerHalf_of_required required)).hodgeConclusion_iff_primitiveLiftable_of_lower
        (hodge R hR p)).mp (hodge R hR (p + 1))
  · intro detects
    apply theHodgeConjecture_of_dimensionBoundedLefschetz Canonical system
    intro R hR
    exact lowerPrimitiveLiftable_of_detection (system R hR)
      (polarization R hR) (detects R hR)

/-- [proved-derived; formal-checked] The forward construction half of the exact finite holonic
cut, exposed independently for callers which already carry the detector law. -/
theorem theHodgeConjecture_of_dimensionBoundedHolonicPrimitiveDetection
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (polarization : ∀ (R : Realization) (hR : Canonical R)
      (p : ℕ) (required : 2 * (p + 1) ≤ (system R hR).dimension),
      SignedDefinitePrimitivePolarization
        ((system R hR).lowStep p (lowerHalf_of_required required)))
    (detects : ∀ (R : Realization) (hR : Canonical R)
      (p : ℕ) (required : 2 * (p + 1) ≤ (system R hR).dimension),
      DetectsEveryNonzero (polarization R hR p required)) :
    TheHodgeConjecture Canonical :=
  (hodge_iff_dimensionBoundedPrimitiveDetection Canonical system polarization).mpr detects

/-! ## Finite monodromy propagation -/

/-- [proved-derived; formal-checked] One source-bearing algebraic seed and irreducible monodromy
on each lower-half primitive block construct exactly the finite primitive return; no monodromy
obligation is emitted in reflected or vanishing degrees. -/
theorem lowerPrimitiveLiftable_of_irreducibleMonodromySeeds {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (monodromy : ∀ (p : ℕ) (required : 2 * (p + 1) ≤ system.dimension),
      PrimitiveMonodromySystem
        (system.lowStep p (lowerHalf_of_required required))) :
    system.LowerPrimitiveLiftable := by
  intro p required
  exact (monodromy p required).primitiveLiftable

/-- [proved-derived; formal-checked] Dimension-bounded irreducible monodromy seed propagation
closes the universal smooth-projective receiver from finitely many primitive blocks per source. -/
theorem theHodgeConjecture_of_dimensionBoundedIrreducibleMonodromySeeds
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (monodromy : ∀ (R : Realization) (hR : Canonical R)
      (p : ℕ) (required : 2 * (p + 1) ≤ (system R hR).dimension),
      PrimitiveMonodromySystem
        ((system R hR).lowStep p (lowerHalf_of_required required))) :
    TheHodgeConjecture Canonical := by
  apply theHodgeConjecture_of_dimensionBoundedLefschetz Canonical system
  intro R hR
  exact lowerPrimitiveLiftable_of_irreducibleMonodromySeeds
    (system R hR) (monodromy R hR)

/-- [proved-derived; formal-checked] A source-bearing orbit cover at every lower-half primitive
index constructs the same finite primitive return without imposing irreducibility or a chosen
block decomposition. -/
theorem lowerPrimitiveLiftable_of_monodromyOrbitCovers {R : Realization}
    (system : DimensionBoundedLefschetzSystem R)
    (covers : ∀ (p : ℕ) (required : 2 * (p + 1) ≤ system.dimension),
      PrimitiveOrbitSourceCover
        (system.lowStep p (lowerHalf_of_required required))) :
    system.LowerPrimitiveLiftable := by
  intro p required
  exact (covers p required).primitiveLiftable

/-- [proved-derived; formal-checked] Dimension-bounded source-bearing monodromy orbit covers
close the universal receiver while retaining every transported algebraic-cycle antecedent. -/
theorem theHodgeConjecture_of_dimensionBoundedMonodromyOrbitCovers
    (Canonical : Realization → Prop)
    (system : ∀ (R : Realization), Canonical R →
      DimensionBoundedLefschetzSystem R)
    (covers : ∀ (R : Realization) (hR : Canonical R)
      (p : ℕ) (required : 2 * (p + 1) ≤ (system R hR).dimension),
      PrimitiveOrbitSourceCover
        ((system R hR).lowStep p (lowerHalf_of_required required))) :
    TheHodgeConjecture Canonical := by
  apply theHodgeConjecture_of_dimensionBoundedLefschetz Canonical system
  intro R hR
  exact lowerPrimitiveLiftable_of_monodromyOrbitCovers
    (system R hR) (covers R hR)

section Audit

#print axioms lowerPrimitiveLiftable_of_detection
#print axioms hodge_iff_dimensionBoundedPrimitiveDetection
#print axioms theHodgeConjecture_of_dimensionBoundedHolonicPrimitiveDetection
#print axioms lowerPrimitiveLiftable_of_irreducibleMonodromySeeds
#print axioms theHodgeConjecture_of_dimensionBoundedIrreducibleMonodromySeeds
#print axioms lowerPrimitiveLiftable_of_monodromyOrbitCovers
#print axioms theHodgeConjecture_of_dimensionBoundedMonodromyOrbitCovers

end Audit

end Soma.Holonics.Millennium.HodgeDimensionBoundedPrimitivePropagation
