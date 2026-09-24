import ElementaryHolonics.Millennium.HodgeHolonicPrimitiveCut
import ElementaryHolonics.Millennium.HodgeFinitePrimitiveRank
import ElementaryHolonics.Millennium.MestreHeightLattice

/-!
# Mestre sections as a source-bearing Hodge primitive passage

`MestreHeightLattice` supplies an exact positive-definite height form on twelve addressed
section directions.  The preceding Hodge falsifier proves why the word *section* matters:
definiteness on an anonymous receiver cannot manufacture an algebraic source occurrence.

This file therefore retains the twelve section combinations as the occurrences of an elementary
`Holon`.  It polarizes the checked quadratic height into an exact bilinear form and proves that
every nonzero receiver direction has a source occurrence which detects it.  The final structure
states the source-specific comparison square required to move that result onto a primitive Hodge
carrier: an actual cycle source map, a primitive-class transport into a finite primitive carrier
of exact rank twelve, cycle-class naturality, and equality between the primitive intersection form
and the negative height form.  Anisotropy forces this transport to be injective, and the exact rank
comparison then forces surjectivity.  Once that comparison is constructed for the Mestre K3
surface, the existing holonic primitive cut returns its complete primitive algebraicity conclusion.

The comparison is not silently inferred from the numerical Gram form.  It is the exact geometric
seam between the Mordell--Weil section lattice and the Néron--Severi primitive lattice.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeMestrePrimitivePassage

open Soma.Holonics
open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeHolonicPrimitiveCut
open Soma.Holonics.Millennium.HodgeFinitePrimitiveRank
open Soma.Holonics.Millennium.MestreHeightLattice

/-- [definition] Rational combinations of the twelve addressed Mestre sections. -/
abbrev SectionCombination := Fin 12 → ℚ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- [definition] Polarization of the exact Mestre height quadratic form. -/
def heightPairing : LinearMap.BilinForm ℚ SectionCombination :=
  LinearMap.mk₂ ℚ
    (fun left right => (Q (left + right) - Q left - Q right) / 2)
    (by intros; simp only [Q, Pi.add_apply]; ring)
    (by intros; simp only [Q, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Q, Pi.add_apply]; ring)
    (by intros; simp only [Q, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- [proved-derived; formal-checked] The polarized form returns the original exact height on the
diagonal. -/
theorem heightPairing_self (combination : SectionCombination) :
    heightPairing combination combination = Q combination := by
  change (Q (combination + combination) - Q combination - Q combination) / 2 =
    Q combination
  simp only [Q, Pi.add_apply]
  ring

/-- [proved-derived; formal-checked] The exact height pairing is symmetric. -/
theorem heightPairing_symmetric : heightPairing.IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff, LinearMap.isSymm_def]
  intro left right
  change (Q (left + right) - Q left - Q right) / 2 =
    (Q (right + left) - Q right - Q left) / 2
  rw [add_comm]
  ring

/-- [proved-derived; formal-checked] A nonzero section combination has nonzero self-pairing. -/
theorem heightPairing_self_ne_zero (combination : SectionCombination)
    (hcombination : combination ≠ 0) :
    heightPairing combination combination ≠ 0 := by
  rw [heightPairing_self]
  intro hzero
  exact hcombination (theHeightFormIsAnisotropic combination hzero)

/-- [definition] The addressed section population itself.  The source is retained; the target and
receiver are its section-lattice direction. -/
def sectionHolon : Holon SectionCombination SectionCombination SectionCombination where
  Occurrence := SectionCombination
  source combination := combination
  target combination := combination
  receive combination := combination

/-- [proved-derived; formal-checked] Every section direction has an occupied exact reconstruction
fibre, with no choice of inverse and no source deletion. -/
theorem sectionHolon_fibre_occupied (combination : SectionCombination) :
    Nonempty (sectionHolon.PreimageFibre combination) :=
  ⟨⟨combination, rfl⟩⟩

/-- [definition] One source section combination detecting one receiver direction through the
exact height pairing. -/
structure SectionDetectionOccurrence where
  sourceSection : SectionCombination
  targetDirection : SectionCombination
  interacts : heightPairing sourceSection targetDirection ≠ 0

/-- [definition] The source-bearing height-interaction Holon. -/
def sectionDetectionHolon :
    Holon SectionCombination SectionCombination SectionCombination where
  Occurrence := SectionDetectionOccurrence
  source occurrence := occurrence.sourceSection
  target occurrence := occurrence.targetDirection
  receive occurrence := occurrence.targetDirection

/-- [proved-derived; formal-checked] Every nonzero section-lattice direction is detected by an
actual section source occurrence: take its self-interaction and use anisotropy. -/
theorem every_nonzero_section_direction_detected
    (combination : SectionCombination) (hcombination : combination ≠ 0) :
    Nonempty (sectionDetectionHolon.PreimageFibre combination) :=
  ⟨⟨⟨combination, combination,
    heightPairing_self_ne_zero combination hcombination⟩, rfl⟩⟩

/-! ## The exact source-specific bridge into a primitive Hodge carrier -/

/-- [definition] The comparison passage which identifies the addressed Mestre section lattice
with a primitive algebraic sublattice of an actual Hodge datum.

The negative sign is Shioda's comparison: on the Mordell--Weil lattice the height is positive,
while on the corresponding primitive Néron--Severi directions the surface intersection form is
negative.  The field is an obligation, not an identification by terminology. -/
structure PrimitiveComparison {lower upper : Datum}
    {step : PrimitiveHodgeStep lower upper}
    (polarization : SignedDefinitePrimitivePolarization step) where
  cycleSource : SectionCombination →ₗ[ℚ] upper.CycleSpace
  primitiveClass : SectionCombination →ₗ[ℚ] step.Primitive
  finiteDimensionalPrimitive : FiniteDimensional ℚ step.Primitive
  primitiveFinrank : Module.finrank ℚ step.Primitive = 12
  cycleClass_commutes : ∀ combination,
    upper.cycleClass.hom (cycleSource combination) =
      ((primitiveClass combination : step.Primitive) : upper.rationalHodgeClasses)
  intersection_is_negative_height : ∀ left right,
    polarization.intersection (primitiveClass left) (primitiveClass right) =
      -heightPairing left right

namespace PrimitiveComparison

variable {lower upper : Datum} {step : PrimitiveHodgeStep lower upper}
variable {polarization : SignedDefinitePrimitivePolarization step}

/-- [proved-derived; formal-checked] The negative-height comparison makes the section-to-
primitive map injective.  A collapsed primitive direction would have zero height, and the checked
Mestre anisotropy reconstructs the original section combination as zero. -/
theorem primitiveClass_injective (comparison : PrimitiveComparison polarization) :
    Function.Injective comparison.primitiveClass := by
  intro left right hequal
  apply sub_eq_zero.mp
  let difference := left - right
  have hmap : comparison.primitiveClass difference = 0 := by
    simp only [difference, map_sub, hequal, sub_self]
  apply theHeightFormIsAnisotropic difference
  have comparisonIdentity :=
    comparison.intersection_is_negative_height difference difference
  rw [hmap] at comparisonIdentity
  have heightZero : heightPairing difference difference = 0 := by
    have signedHeightZero : -(heightPairing difference difference) = 0 := by
      simpa using comparisonIdentity.symm
    exact neg_eq_zero.mp signedHeightZero
  simpa only [heightPairing_self] using heightZero

/-- [proved-derived; formal-checked] The Mestre comparison instantiates the generic finite-rank
primitive source owner.  Its twelve-coordinate face is retained only as the exact source-rank
calculation; the cycle source, commuting square, and anisotropy-derived injection carry the
geometric content. -/
def toFiniteRankPrimitiveSource (comparison : PrimitiveComparison polarization) :
    FiniteRankPrimitiveSource step SectionCombination where
  finiteDimensionalSource := inferInstance
  finiteDimensionalPrimitive := comparison.finiteDimensionalPrimitive
  cycleSource := comparison.cycleSource
  primitiveClass := comparison.primitiveClass
  cycleClass_commutes := comparison.cycleClass_commutes
  primitiveClass_injective := comparison.primitiveClass_injective
  equalFinrank := by
    calc
      Module.finrank ℚ SectionCombination = 12 := by
        simpa only [SectionCombination] using
          (Module.finrank_fin_fun (R := ℚ) (n := 12))
      _ = Module.finrank ℚ step.Primitive := comparison.primitiveFinrank.symm

/-- [proved-derived; formal-checked] Exact rank twelve upgrades the derived injection to a
surjection.  Thus global primitive coverage is not an independent comparison field. -/
theorem primitiveClass_surjective (comparison : PrimitiveComparison polarization) :
    Function.Surjective comparison.primitiveClass :=
  comparison.toFiniteRankPrimitiveSource.primitiveClass_surjective

/-- [proved-derived; formal-checked] A complete Mestre primitive comparison occupies every
nonzero algebraic detector fibre.  The occurrence retains the section coefficient source, its
cycle source, the transported primitive face, and the exact pairing comparison. -/
theorem detectsEveryNonzero (comparison : PrimitiveComparison polarization) :
    DetectsEveryNonzero polarization := by
  intro primitive hprimitive
  obtain ⟨combination, hcombination⟩ := comparison.primitiveClass_surjective primitive
  have hcombinationNonzero : combination ≠ 0 := by
    intro hzero
    apply hprimitive
    rw [← hcombination, hzero, map_zero]
  have hinteracts :
      polarization.intersection (comparison.primitiveClass combination) primitive ≠ 0 := by
    rw [← hcombination, comparison.intersection_is_negative_height]
    exact neg_ne_zero.mpr
      (heightPairing_self_ne_zero combination hcombinationNonzero)
  refine ⟨⟨⟨comparison.primitiveClass combination, ?_, primitive, hinteracts⟩, rfl⟩⟩
  exact ⟨comparison.cycleSource combination,
    comparison.cycleClass_commutes combination⟩

/-- [proved-derived; formal-checked] The source-specific comparison closes the primitive
algebraicity obligation, rather than only proving nondegeneracy of its receiver form. -/
theorem primitiveLiftable (comparison : PrimitiveComparison polarization) :
    step.PrimitiveLiftable :=
  comparison.toFiniteRankPrimitiveSource.primitiveLiftable

end PrimitiveComparison

section Audit

#print axioms heightPairing_self
#print axioms heightPairing_symmetric
#print axioms heightPairing_self_ne_zero
#print axioms sectionHolon_fibre_occupied
#print axioms every_nonzero_section_direction_detected
#print axioms PrimitiveComparison.primitiveClass_injective
#print axioms PrimitiveComparison.toFiniteRankPrimitiveSource
#print axioms PrimitiveComparison.primitiveClass_surjective
#print axioms PrimitiveComparison.detectsEveryNonzero
#print axioms PrimitiveComparison.primitiveLiftable

end Audit

end Soma.Holonics.Millennium.HodgeMestrePrimitivePassage
