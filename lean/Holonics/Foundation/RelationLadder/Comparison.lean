import Holonics.Foundation.CausalRelevance

/-! [agent-inferred] The declared receiver/navigator comparison is used by
Standing independently of occurrence-bearing tower witnesses. These are the
existing Situation, potential and tolerance declarations, moved once with
unchanged canonical names and exact proof bodies. -/

namespace Holonics.Foundation.RelationLadder

open Holonics
open Holonics.Foundation.Chronology
open Holonics.Foundation.CausalRelevance.NonLinear

universe u v w

/-! ## The declared situation -/

/-- [definition] A **situation**: the admitted receivers and the admitted generators. This is the
pair `(G, R)` of the plan, packaged so that a rung is a statement about a declared situation and
never about a bare carrier.

Rust counterpart: `relation_ladder.rs::Situation`. -/
structure Situation (Generator : Type u) (Receiver : Type v)
    (Source : Type w) (Face : Type*) where
  /-- What each admitted receiver returns from an occurrence. -/
  observe : Receiver → Source → Face
  /-- How each admitted generator carries an occurrence to its successor. -/
  step : Generator → Source → Source

variable {Generator : Type u} {Receiver : Type v} {Source : Type w} {Face : Type*}

/-! ## The six rungs -/

/-- [definition] **Rung 1 — strict occurrence identity**: Lean's own equality inside one situated
type. It is named only so that the ladder names all six rungs; it adds nothing to `=`. -/
abbrev SameOccurrence (x y : Source) : Prop := x = y

/-- [definition] **Rung 2 — causal continuation**: an addressed passage occurrence carrying `x` to
`y`. This is `Foundation/Lineage.lean::AddressedPassage.Fibre` exactly — the *type* of carrying
occurrences, not the mere existence of one, which is
`Foundation/Lineage.lean::AddressedPassage.shadow`. -/
abbrev Continues {X : Type u} {Y : Type v} (P : AddressedPassage X Y) (x : X) (y : Y) : Type _ :=
  P.Fibre x y

/-- [definition] **Rung 3 — structure-preserving isomorphism**, read at the element level as a
*symmetry of the situation carrying `x` to `y`*.

`carrier` alone is a bare bijection and is **not** rung 3: `step_natural` and `observe_natural`
are the equivariance hypothesis, stated exactly, and each half is separately necessary. This is
`Foundation/Holon.lean::Rebase` with the situation's own two ports — the generator square and the
receiver triangle — in place of the holon's source/target/face squares.

Rust counterpart: `relation_ladder.rs::SituationAutomorphism`. -/
structure SituationAuto (S : Situation Generator Receiver Source Face) (x y : Source) where
  /-- The symmetry of the carrier. -/
  carrier : Source ≃ Source
  /-- It commutes with every admitted generator. -/
  step_natural : ∀ generator source,
    carrier (S.step generator source) = S.step generator (carrier source)
  /-- Every admitted receiver reads the same face through it. -/
  observe_natural : ∀ receiver source,
    S.observe receiver (carrier source) = S.observe receiver source
  /-- And it carries the first occurrence to the second. -/
  carries : carrier x = y

/-- [definition] **Rung 4 — equal under one declared receiver.** -/
def ReceiverEqualAt (S : Situation Generator Receiver Source Face)
    (receiver : Receiver) (x y : Source) : Prop :=
  S.observe receiver x = S.observe receiver y

/-- [definition] Rung 4 over the whole declared receiver family. This is
`Foundation/Receiver.lean::ReceiverEq` at `S.observe`, cited rather than rebuilt. -/
def PresentAgreement (S : Situation Generator Receiver Source Face) (x y : Source) : Prop :=
  ReceiverEq S.observe x y

/-- [definition] The **potential** `Pot_{G,R}(x) = [(w, ρ) ↦ ρ(T_w x)]` of the plan, as the
function it is. -/
def potential (S : Situation Generator Receiver Source Face) (x : Source) :
    Receiver × List Generator → Face :=
  fun receiverWord => S.observe receiverWord.1 (transportWord S.step receiverWord.2 x)

/-- [definition] **Rung 5 — equal potential.** This **is**
`Foundation/CausalRelevance.lean::futureAgreement`; it is a name for that predicate at a
`Situation`, not a second definition. -/
def EqualPotential (S : Situation Generator Receiver Source Face) (x y : Source) : Prop :=
  futureAgreement S.observe S.step x y

/-- [definition] **Rung 6 — receiver difference inside a declared tolerance.** The reading is
exact and rational, as every reading this project admits is; `tolerance` is the receiver's
*declared* tolerance, never a fitted one. -/
def WithinTolerance (read : Source → ℚ) (tolerance : ℚ) (x y : Source) : Prop :=
  |read x - read y| ≤ tolerance

/-- [proved-derived; formal-checked] Equal potential is exactly equality of the two potentials. -/
theorem equalPotentialIffPotentialEq (S : Situation Generator Receiver Source Face)
    (x y : Source) : EqualPotential S x y ↔ potential S x = potential S y := by
  constructor
  · intro same
    funext receiverWord
    exact same receiverWord.1 receiverWord.2
  · intro same receiver word
    exact congrFun same (receiver, word)


end Holonics.Foundation.RelationLadder
