import ElementaryHolonics.Foundation.Receiver
import Mathlib.Logic.Equiv.Defs

/-!
# Addressed passages retain the witness that relational composition forgets

`Rel.comp` is the propositional shadow of a passage: it says that an intermediate exists and
then discards which intermediate occurrence carried the transport.  That quotient is lawful for
an extensional receiver and insufficient for lineage.

An `AddressedPassage X Y` therefore carries its own occurrence population together with the two
boundary maps.  Serial composition is the pullback of adjacent occurrence populations over their
shared boundary.  The pullback witness is the complete finite, one-categorical form of the
addressed lineage: it records both occurrences and the equality by which they actually glue.

Nothing here identifies equal endpoints, equal bytes, or equal receiver faces with equal
occurrences.  Every theorem is discharged.
-/

namespace Soma.Holonics

universe u v w x

/-- A passage from `X` to `Y` with the population of occurrences that actually carries it. -/
structure AddressedPassage (X : Type u) (Y : Type v) where
  /-- The occurrences of this passage.  Two occurrences may have the same two boundary faces. -/
  Occurrence : Type w
  /-- The source boundary of an occurrence. -/
  source : Occurrence → X
  /-- The target boundary of an occurrence. -/
  target : Occurrence → Y

namespace AddressedPassage

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type x}

/-- The addressed fibre between two boundary faces.  It retains every carrying occurrence. -/
def Fibre (P : AddressedPassage X Y) (x : X) (y : Y) : Type _ :=
  { occurrence : P.Occurrence // P.source occurrence = x ∧ P.target occurrence = y }

/-- The extensional relation seen after the addressed fibre is truncated to mere existence. -/
def shadow (P : AddressedPassage X Y) : Rel X Y :=
  fun x y ↦ Nonempty (P.Fibre x y)

/-- The identity passage.  Its occurrence is the boundary occurrence itself. -/
def id (X : Type u) : AddressedPassage X X where
  Occurrence := X
  source := _root_.id
  target := _root_.id

/--
Two adjacent occurrences joined at their common boundary.

This is a pullback population, not a pair chosen independently: `joins` is part of the witness.
-/
structure Join (P : AddressedPassage X Y) (Q : AddressedPassage Y Z) where
  /-- The predecessor occurrence. -/
  left : P.Occurrence
  /-- The successor occurrence. -/
  right : Q.Occurrence
  /-- The exact boundary at which the two occurrences join. -/
  joins : P.target left = Q.source right

/-- Serial composition by pullback over the shared boundary. -/
def comp (Q : AddressedPassage Y Z) (P : AddressedPassage X Y) : AddressedPassage X Z where
  Occurrence := Join P Q
  source joined := P.source joined.left
  target joined := Q.target joined.right

/-
Two passages with the same boundary types are equivalent only when their occurrence populations
are equivalent *and* that equivalence preserves both addressed boundary maps.  A bare cardinality
or bijection is not passage equality.
-/
structure PassageEquiv (P Q : AddressedPassage X Y) where
  /-- The occurrence populations correspond. -/
  occurrence : P.Occurrence ≃ Q.Occurrence
  /-- The correspondence retains the source address. -/
  source_exact : ∀ carried, Q.source (occurrence carried) = P.source carried
  /-- The correspondence retains the target address. -/
  target_exact : ∀ carried, Q.target (occurrence carried) = P.target carried

/-- Rebracketing serial composition only rebrackets the same three addressed occurrences. -/
def compAssociator (R : AddressedPassage Z W) (Q : AddressedPassage Y Z)
    (P : AddressedPassage X Y) :
    PassageEquiv (comp R (comp Q P)) (comp (comp R Q) P) where
  occurrence :=
    { toFun := fun joined =>
        ⟨joined.left.left,
          ⟨joined.left.right, joined.right, joined.joins⟩,
          joined.left.joins⟩
      invFun := fun joined =>
        ⟨⟨joined.left, joined.right.left, joined.joins⟩,
          joined.right.right,
          joined.right.joins⟩
      left_inv := by
        intro joined
        rcases joined with ⟨⟨left, middle, left_join⟩, right, right_join⟩
        rfl
      right_inv := by
        intro joined
        rcases joined with ⟨left, ⟨middle, right, right_join⟩, left_join⟩
        rfl }
  source_exact _ := rfl
  target_exact _ := rfl

/-- Composing the identity before a passage preserves its addressed occurrence population. -/
def rightIdentityEquiv (P : AddressedPassage X Y) :
    PassageEquiv (comp P (id X)) P where
  occurrence :=
    { toFun := fun joined => joined.right
      invFun := fun occurrence => ⟨P.source occurrence, occurrence, rfl⟩
      left_inv := by
        intro joined
        rcases joined with ⟨source, occurrence, joins⟩
        change source = P.source occurrence at joins
        subst source
        rfl
      right_inv := by intro _; rfl }
  source_exact joined := joined.joins.symm
  target_exact _ := rfl

/-- Composing the identity after a passage preserves its addressed occurrence population. -/
def leftIdentityEquiv (P : AddressedPassage X Y) :
    PassageEquiv (comp (id Y) P) P where
  occurrence :=
    { toFun := fun joined => joined.left
      invFun := fun occurrence => ⟨occurrence, P.target occurrence, rfl⟩
      left_inv := by
        intro joined
        rcases joined with ⟨occurrence, target, joins⟩
        change P.target occurrence = target at joins
        subst target
        rfl
      right_inv := by intro _; rfl }
  source_exact _ := rfl
  target_exact joined := joined.joins

/-- Split one composite fibre into its shared boundary and its two addressed component fibres. -/
def splitCompositeFibre (Q : AddressedPassage Y Z) (P : AddressedPassage X Y)
    {x : X} {z : Z} (carried : (comp Q P).Fibre x z) :
    Σ y : Y, P.Fibre x y × Q.Fibre y z :=
  ⟨P.target carried.1.left,
    ⟨carried.1.left, carried.2.1, rfl⟩,
    ⟨carried.1.right, carried.1.joins.symm, carried.2.2⟩⟩

/-- Glue two addressed component fibres into one occurrence of the composite passage. -/
def joinCompositeFibre (Q : AddressedPassage Y Z) (P : AddressedPassage X Y)
    {x : X} {z : Z} :
    (Σ y : Y, P.Fibre x y × Q.Fibre y z) → (comp Q P).Fibre x z
  | ⟨_, left, right⟩ =>
      ⟨⟨left.1, right.1, left.2.2.trans right.2.1.symm⟩, left.2.1, right.2.2⟩

/-- Splitting and rejoining a composite occurrence retains that occurrence exactly. -/
theorem join_split (Q : AddressedPassage Y Z) (P : AddressedPassage X Y)
    {x : X} {z : Z} (carried : (comp Q P).Fibre x z) :
    joinCompositeFibre Q P (splitCompositeFibre Q P carried) = carried := by
  rcases carried with ⟨⟨left, right, joins⟩, source_eq, target_eq⟩
  rfl

/-- Rejoining and splitting retains both component occurrences and their shared boundary. -/
theorem split_join (Q : AddressedPassage Y Z) (P : AddressedPassage X Y)
    {x : X} {z : Z} (pieces : Σ y : Y, P.Fibre x y × Q.Fibre y z) :
    splitCompositeFibre Q P (joinCompositeFibre Q P pieces) = pieces := by
  rcases pieces with ⟨y, ⟨left, source_eq, left_target⟩,
    ⟨right, right_source, target_eq⟩⟩
  subst y
  rfl

/--
The relational shadow of pullback composition is ordinary relational composition.

This theorem identifies the exact quotient: `Rel.comp` keeps the existence of the shared witness
and forgets the witness population returned by `splitCompositeFibre`.
-/
theorem shadow_comp (Q : AddressedPassage Y Z) (P : AddressedPassage X Y) :
    shadow (comp Q P) = Rel.comp (shadow Q) (shadow P) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨carried⟩
    obtain ⟨y, left, right⟩ := splitCompositeFibre Q P carried
    exact ⟨y, ⟨left⟩, ⟨right⟩⟩
  · rintro ⟨y, ⟨left⟩, ⟨right⟩⟩
    exact ⟨joinCompositeFibre Q P ⟨y, left, right⟩⟩

/-- The identity passage has the relational identity as its shadow. -/
theorem shadow_id (X : Type u) : shadow (id X) = Rel.id X := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨occurrence, source_eq, target_eq⟩⟩
    exact source_eq.symm.trans target_eq
  · intro h
    exact ⟨⟨x, rfl, h⟩⟩

/-! ## A finite control: one relational edge can hide two distinct occurrences -/

/-- One extensional edge carried by one occurrence. -/
def singleUnitPassage : AddressedPassage Unit Unit where
  Occurrence := Unit
  source _ := ()
  target _ := ()

/-- The same extensional edge carried by two distinct occurrences. -/
def parallelUnitPassage : AddressedPassage Unit Unit where
  Occurrence := Bool
  source _ := ()
  target _ := ()

/-- The two passages have exactly the same relational shadow. -/
theorem theSameRelationCanHideDifferentOccurrencePopulations :
    shadow singleUnitPassage = shadow parallelUnitPassage := by
  funext _ _
  apply propext
  constructor <;> intro _
  · exact ⟨⟨false, rfl, rfl⟩⟩
  · exact ⟨⟨(), rfl, rfl⟩⟩

/-- The hidden parallel occurrences are genuinely distinct. -/
theorem theParallelOccurrencesRemainDistinct :
    (false : parallelUnitPassage.Occurrence) ≠ true := by
  decide

end AddressedPassage

end Soma.Holonics

section Audit
open Soma.Holonics
#print axioms AddressedPassage.join_split
#print axioms AddressedPassage.split_join
#print axioms AddressedPassage.compAssociator
#print axioms AddressedPassage.shadow_comp
#print axioms AddressedPassage.theSameRelationCanHideDifferentOccurrencePopulations
end Audit
