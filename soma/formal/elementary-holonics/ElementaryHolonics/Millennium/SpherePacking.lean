import ElementaryHolonics.Foundation.Lineage
import ElementaryHolonics.Millennium.Chronology

/-!
# Sphere packing as a noncommuting reflection orbit

For five mutually tangent oriented spheres in three dimensions, the bends satisfy the
Soddy--Gossett relation

`(b₀ + b₁ + b₂ + b₃ + b₄)² = 3 (b₀² + b₁² + b₂² + b₃² + b₄²)`.

Holding four bends fixed leaves two roots for the fifth, and exchanging those roots replaces
`bᵢ` by the sum of the other four bends minus `bᵢ`.  The five exchanges below are integral
involutions preserving the tangency quadric.  Their noncommutation proves that a generated
packing face needs the ordered reflection word, not only a set or count of reflections.

The exact content is deliberately bounded.  This file establishes the bend orbit and one integral
root.  It does not construct sphere centres, prove non-overlap, prove that the group orbit is
infinite, construct the residual compact set, or compute a fractal dimension.  Those require
geometric realization plus separation and scale hypotheses, not the bend equation alone.

Every theorem is discharged.  Nothing here asserts a result about a named Millennium problem.
-/

namespace Soma.Holonics.Millennium.SpherePacking

open Soma.Holonics
open Soma.Holonics.Millennium.Chronology

/-- Five oriented sphere bends in dimension three. -/
structure FiveBends where
  first : ℤ
  second : ℤ
  third : ℤ
  fourth : ℤ
  fifth : ℤ
deriving DecidableEq, Repr

/-- The five coordinate reflections of the Soddy--Gossett quadric. -/
inductive ReflectionHand
  | first
  | second
  | third
  | fourth
  | fifth
deriving DecidableEq, Repr

/-- The bend sum. -/
def bendSum (b : FiveBends) : ℤ :=
  b.first + b.second + b.third + b.fourth + b.fifth

/-- The Soddy--Gossett quadratic defect.  Tangent bend populations have defect zero. -/
def soddyGossettDefect (b : FiveBends) : ℤ :=
  bendSum b ^ 2 -
    3 * (b.first ^ 2 + b.second ^ 2 + b.third ^ 2 + b.fourth ^ 2 + b.fifth ^ 2)

/-- The bend population lies on the three-dimensional tangency quadric. -/
def SatisfiesTangency (b : FiveBends) : Prop := soddyGossettDefect b = 0

/-- Exchange one bend for the other root while retaining the four tangent neighbours. -/
def reflect : ReflectionHand → FiveBends → FiveBends
  | .first, b =>
      { b with first := b.second + b.third + b.fourth + b.fifth - b.first }
  | .second, b =>
      { b with second := b.first + b.third + b.fourth + b.fifth - b.second }
  | .third, b =>
      { b with third := b.first + b.second + b.fourth + b.fifth - b.third }
  | .fourth, b =>
      { b with fourth := b.first + b.second + b.third + b.fifth - b.fourth }
  | .fifth, b =>
      { b with fifth := b.first + b.second + b.third + b.fourth - b.fifth }

/-- Every bend exchange is an involution. -/
theorem everyReflectionIsInvolutive (hand : ReflectionHand) (b : FiveBends) :
    reflect hand (reflect hand b) = b := by
  cases hand <;> cases b <;> simp [reflect]

/-- Every bend exchange preserves the exact Soddy--Gossett defect. -/
theorem everyReflectionPreservesTheTangencyDefect (hand : ReflectionHand) (b : FiveBends) :
    soddyGossettDefect (reflect hand b) = soddyGossettDefect b := by
  cases hand <;> cases b <;> simp [reflect, soddyGossettDefect, bendSum] <;> ring

/-- Therefore every reflection carries a tangent bend population to another tangent one. -/
theorem everyReflectionPreservesTangency (hand : ReflectionHand) {b : FiveBends}
    (h : SatisfiesTangency b) : SatisfiesTangency (reflect hand b) := by
  rw [SatisfiesTangency, everyReflectionPreservesTheTangencyDefect]
  exact h

/-- Every ordered reflection word preserves the tangency defect. -/
theorem everyReflectionWordPreservesTheTangencyDefect
    (word : List ReflectionHand) (b : FiveBends) :
    soddyGossettDefect (transportWord reflect word b) = soddyGossettDefect b := by
  induction word with
  | nil => rfl
  | cons hand word ih =>
      rw [transportWord_cons, everyReflectionPreservesTheTangencyDefect, ih]

/-- The smallest useful integral bowl root in the five-bend chart. -/
def bowlRoot : FiveBends := ⟨-1, 2, 2, 3, 3⟩

/-- The root lies exactly on the tangency quadric. -/
theorem theBowlRootSatisfiesTangency : SatisfiesTangency bowlRoot := by
  norm_num [SatisfiesTangency, soddyGossettDefect, bendSum, bowlRoot]

/-- Two reflected additions, retained as an exact ordered-word face. -/
theorem twoReflectionsGrowTheIntegralBendPopulation :
    transportWord reflect [.second, .first] bowlRoot = ⟨11, 17, 2, 3, 3⟩ := by
  norm_num [transportWord, reflect, bowlRoot]

/-- The reflection generators do not commute on the integral root. -/
theorem thePackingChronologyCannotCollapseToAMultiset :
    transportWord reflect [.second, .first] bowlRoot ≠
      transportWord reflect [.first, .second] bowlRoot := by
  norm_num [transportWord, reflect, bowlRoot]

/-- The generated bend population is the orbit of the compact generator plus its ordered word. -/
def Generated (b : FiveBends) : Prop :=
  ∃ word : List ReflectionHand, transportWord reflect word bowlRoot = b

/-- The generator itself is in the orbit. -/
theorem theRootIsGenerated : Generated bowlRoot := ⟨[], rfl⟩

/-- The generated population is closed under every local reflection. -/
theorem theGeneratedPopulationIsClosedUnderReflection
    (hand : ReflectionHand) {b : FiveBends} (h : Generated b) : Generated (reflect hand b) := by
  obtain ⟨word, rfl⟩ := h
  exact ⟨hand :: word, rfl⟩

/-- Every generated bend population remains on the exact tangency quadric. -/
theorem everyGeneratedPopulationSatisfiesTangency {b : FiveBends} (h : Generated b) :
    SatisfiesTangency b := by
  obtain ⟨word, rfl⟩ := h
  rw [SatisfiesTangency, everyReflectionWordPreservesTheTangencyDefect]
  exact theBowlRootSatisfiesTangency

/-! ## The orbit as an addressed passage -/

/--
Every reflection word is an occurrence carrying the root to one generated bend face.

Closed words may share an endpoint while remaining distinct occurrences; the word is the lineage.
-/
def orbitPassage : AddressedPassage Unit FiveBends where
  Occurrence := List ReflectionHand
  source _ := ()
  target word := transportWord reflect word bowlRoot

/-- A closed two-reflection word returns the same face while remaining a different occurrence. -/
theorem aReturnedFaceDoesNotEraseTheReflectionLineage :
    orbitPassage.target [] = orbitPassage.target [.first, .first]
      ∧ ([] : orbitPassage.Occurrence) ≠ [.first, .first] := by
  constructor
  · change bowlRoot = reflect .first (reflect .first bowlRoot)
    exact (everyReflectionIsInvolutive .first bowlRoot).symm
  · decide

end Soma.Holonics.Millennium.SpherePacking

section Audit
open Soma.Holonics.Millennium.SpherePacking
#print axioms everyReflectionIsInvolutive
#print axioms everyReflectionPreservesTheTangencyDefect
#print axioms thePackingChronologyCannotCollapseToAMultiset
#print axioms everyGeneratedPopulationSatisfiesTangency
#print axioms aReturnedFaceDoesNotEraseTheReflectionLineage
end Audit
