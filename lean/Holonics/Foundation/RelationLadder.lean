import Holonics.Foundation.CausalRelevance
import Holonics.Foundation.Holon
import Holonics.Foundation.ContinuingTower
import Holonics.Foundation.ReceiverRelease
import Holonics.Transport.ChangingReceiver

/-!
# T1 — the relation ladder: one typed scale between two occurrences

[definition] This file deposits item **T1** of
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. It founds no new
relation. Every rung is *defined by citing the owner that already carries it*, and the deliverable
is the single typed scale, its proved implications, and a constructed counterexample for every
implication that fails.

[project-postulate] The governing statement (Brandon, September 18): *Identity belongs to an
occurrence. Persistence belongs to lineage. Sameness belongs to a receiver. Potential belongs to a
family of future interactions.* Nothing has to survive for two occurrences to be literally
identical, because if anything has changed they are not the same occurrence. `4` and `2^2` differ
in `Expression` and agree under `eval`; the equality belongs to the scalar receiver and does not
ascend to identify the formulations. This is `docs/canon/08_CORE_MATHEMATICAL_INSTRUMENTS.md` §1.1
("unqualified equality is occurrence identity; every other equality is typed") and
`docs/canon/TABLET_THE_OPERATIONS.md`'s retained Holobrochos list made executable.

## The six rungs and their owners

| rung | written | owner cited |
|---|---|---|
| 1 | `x = y` | Lean's own equality, inside **one** situated type |
| 2 | `x ⇝ y` | `Foundation/Lineage.lean::AddressedPassage.Fibre` |
| 3 | `x ≅ y` | `Foundation/Holon.lean::Rebase` read as a situation automorphism |
| 4 | `x ~_ρ y` | `Foundation/Receiver.lean::ReceiverEq` |
| 5 | `x ~_{G,R} y` | `Foundation/CausalRelevance.lean::futureAgreement` — *identified, not redefined* |
| 6 | `x ≈_{ρ,ε} y` | `Foundation/ReceiverRelease.lean::width` inside a declared tolerance |

Rung 5 **is** `Holonics.Foundation.CausalRelevance.NonLinear.futureAgreement`:
`EqualPotential` unfolds to it, so everything that owner proves —
`futureAgreement_is_greatest_stable`, `futureAgreement_le_presentAgreement`,
`futureAgreement_equivalence`, `futureAgreement_preserved_by_step`,
`futureAgreement_iff_collapseOf` — is a theorem about this rung and is cited rather than restated.
Rung 6 is `withinTolerance_of_width_le`: the two-element family's
`Foundation/ReceiverRelease.lean::width` inside the receiver's declared tolerance, by that owner's
own `abs_sub_le_width`.

## Three relativity classes, which is the ladder's first finding

[proved-derived] The rungs are not relative to the same thing, and conflating that is how a
"sameness" claim smuggles in an identity claim.

* Rung 1 is **absolute**: it mentions nothing but the two occurrences and their one type.
* Rungs 3, 4, 5 and 6 are relative to the **declared situation** `(G, R)` (and, for rung 6, the
  declared tolerance): `Situation` carries exactly those declarations.
* Rung 2 is relative to a **declared lineage** — an `AddressedPassage`. It is therefore not a
  property of the pair at all, and `equalPotentialWithoutAGeneratorContinuation` shows the honest
  negative form: the situation's own transports do not reach. In the order below, the arrows
  *into* `continuation` are witnessed by passages built from the situation's own data
  (`identityContinues`, `SituationAuto.continues`); a passage declared from outside the situation
  can of course fail to carry anything (`continuationWithoutAnyEqualFace` is the converse
  direction of the same observation).

## What is proved to hold

* `identityImpliesEveryRung` — rung 1 implies all of 2–6.
* `equalPotentialImpliesPresentAgreement` — rung 5 implies rung 4 for every `ρ ∈ R`; it is
  `futureAgreement_le_presentAgreement` at the empty word, cited.
* `receiverEqualImpliesWithinTolerance` — rung 4 implies rung 6 at any non-negative tolerance.
* `situationAutoImpliesEqualPotential` — rung 3 implies rung 5 **when the generators and the
  receivers are transported along the isomorphism**. That hypothesis is exactly
  `SituationAuto.step_natural` and `SituationAuto.observe_natural`, and *each half is necessary*:
  `receiverEquivarianceIsNecessary` drops the second and `generatorEquivarianceIsNecessary` drops
  the first, each with a constructed witness in which the potentials differ.
* `SituationIso.equalPotentialOf` and `situationIsoTransportsEqualPotential` — the same statement
  between two different situations, where "transported along the iso" is the content.
* `equalPotentialAntitone` — enlarging `(G, R)` refines the potential equivalence.
* `separatorRefutesEqualPotential` — one `(w, ρ)` refutes it, the elementary form of
  `Foundation/CausalRelevance.lean::futureHistory_quotientNe_returns_separator`.

## What is proved to fail, with a constructed witness for each

* `receiverEqualityWithoutEqualPotential` — the three-step example of `CausalRelevance`, cited
  (`swap_reopens_second_coordinate`).
* `equalPotentialWithoutIsomorphism` — a blind receiver over a generator with one fixed point and
  one two-cycle: the two occurrences have equal potential and **no** situation automorphism
  carries one to the other.
* `isomorphismWithoutIdentity` — a situation automorphism carrying `false` to `true`.
* `continuationWithoutAnyEqualFace` — `Transport/ChangingReceiver.lean::translationPassage`,
  cited: a passage occurrence carries `0` to `1` and the declared receiver separates them at
  every rung below.
* `lossyContinuationIsNotAnIsomorphism` — a `Foundation/ContinuingTower.lean::Transition` whose
  residual is not a subsingleton, so it is a continuation and is not invertible
  (`Transition.injective_of_subsingleton_residual` is the converse, cited).
* `toleranceIsWithoutIdentification` and `toleranceIsNotTransitive` — `0, 1, 2` at tolerance `1`.
  Rung 6 is reflexive and symmetric and **not** transitive; what it has instead is
  `withinToleranceIterate`, an `n`-step chain inside `n · ε`.
* `noRungBelowIdentityAscendsToIdentity` — the headline: each of rungs 2–6 is inhabited by a pair
  that is not identical, so from none of them can `x = y` be concluded.

## Across two times, identity is not even statable

[proved-derived] For `X : T → Type` with `x : X t` and `y : X u`, `t ≠ u`, the expression `x = y`
is a type error: the two occurrences do not inhabit one type. The honest statement lives in
`Σ t, X t`, and there `situatedOccurrenceEqIff` shows that equality of situated occurrences is
exactly *equal index together with* `HEq`, `distinctIndexGivesDistinctOccurrence` shows distinct
indices give distinct situated occurrences outright, and `passageDoesNotIdentify` shows that a
carrying passage does not repair it. `shadowOfRelation` shows that whatever relation one declares
between the two types is the shadow of an addressed passage — a passage is what the framework
supplies — and `Foundation/Lineage.lean::theSameRelationCanHideDifferentOccurrencePopulations` is
why the addressed form is the content and the relation is its truncation.

## Rust counterpart

[definition] `crates/holonic-engine/src/relation_ladder.rs`, with the same names — `Rung`,
`Rung::entails`, `rung_meet`, `Situation`, `classify`, `Classification`, `Separator`,
`PotentialVerdict`, `Expression`, `eval`, `Enactment`, `musical_face`, `absolute_face` — every
theorem below mirrored as a test, and the separator search bounded by a declared history-length
ceiling with a typed refusal. "Not separated within the declared bound" is its own return there
and is never reported as equal potential.
-/

namespace Holonics.Foundation.RelationLadder

open Holonics
open Holonics.Foundation.ContinuingTower
open Holonics.Millennium.Chronology
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

/-! ## The typed scale -/

/-- [definition] The rungs as a type, so that "which relation was established" is data. `noRelation`
is the bottom: nothing on this ladder was established, which is the honest return and not a claim.

Rust counterpart: `relation_ladder.rs::Rung`. -/
inductive Rung
  /-- Rung 1. -/
  | identity
  /-- Rung 3. -/
  | isomorphism
  /-- Rung 5. -/
  | equalPotential
  /-- Rung 4. -/
  | receiverEqual
  /-- Rung 6. -/
  | withinTolerance
  /-- Rung 2. -/
  | continuation
  /-- Nothing on this ladder. -/
  | noRelation
  deriving DecidableEq, Repr

/-- [definition] The complete enumeration of the seven rungs, so every law about them is decided by
the kernel over all cases. -/
instance : Fintype Rung where
  elems := {.identity, .isomorphism, .equalPotential, .receiverEqual, .withinTolerance,
    .continuation, .noRelation}
  complete := by intro rung; cases rung <;> decide

/-- [definition] Everything a rung entails, itself included. Each arrow below is discharged by a
theorem in this file and each omission by a constructed counterexample.

Rust counterpart: `relation_ladder.rs::Rung::entailed`. -/
def Rung.entailed : Rung → List Rung
  | .identity => [.identity, .isomorphism, .equalPotential, .receiverEqual, .withinTolerance,
      .continuation, .noRelation]
  | .isomorphism => [.isomorphism, .equalPotential, .receiverEqual, .withinTolerance,
      .continuation, .noRelation]
  | .equalPotential => [.equalPotential, .receiverEqual, .withinTolerance, .noRelation]
  | .receiverEqual => [.receiverEqual, .withinTolerance, .noRelation]
  | .withinTolerance => [.withinTolerance, .noRelation]
  | .continuation => [.continuation, .noRelation]
  | .noRelation => [.noRelation]

/-- [definition] `a.entails b` when every pair standing in relation `a` also stands in relation `b`.

Rust counterpart: `relation_ladder.rs::Rung::entails`. -/
def Rung.entails (a b : Rung) : Bool := a.entailed.contains b

/-- [proved-derived; formal-checked] The order is reflexive. -/
theorem entails_refl (a : Rung) : a.entails a = true := by revert a; decide

/-- [proved-derived; formal-checked] The order is transitive. -/
theorem entails_trans (a b c : Rung) (hab : a.entails b = true) (hbc : b.entails c = true) :
    a.entails c = true := by revert hab hbc; revert a b c; decide

/-- [proved-derived; formal-checked] The order is antisymmetric, so it is a genuine partial order
and the seven rungs are seven. -/
theorem entails_antisymm (a b : Rung) (hab : a.entails b = true) (hba : b.entails a = true) :
    a = b := by revert hab hba; revert a b; decide

/-- [proved-derived; formal-checked] It is **not** total: a continuation and a receiver equality
are incomparable, and so are a continuation and an equal potential. This is the first relativity
finding in order form — a lineage and a face are different declarations. -/
theorem entails_is_not_total :
    Rung.continuation.entails .receiverEqual = false ∧
      Rung.receiverEqual.entails .continuation = false ∧
      Rung.continuation.entails .equalPotential = false ∧
      Rung.equalPotential.entails .continuation = false := by decide

/-- [proved-derived; formal-checked] **No rung below identity ascends to identity**, in the
declared order. `noRungBelowIdentityAscendsToIdentity` is the same statement with witnesses. -/
theorem no_rung_below_identity_entails_identity (a : Rung) (h : a ≠ .identity) :
    a.entails .identity = false := by revert h; revert a; decide

/-- [definition] The greatest common lower bound of two rungs. Unlike
`Foundation/Bridge.lean::statusMeet` no arm is off the order, so the meet is total and lands in
`noRelation` exactly when the two rungs are incomparable.

Rust counterpart: `relation_ladder.rs::rung_meet`. -/
def rungMeet (a b : Rung) : Rung :=
  if a.entails b then b else if b.entails a then a else .noRelation

/-- [proved-derived; formal-checked] The meet is symmetric. -/
theorem rungMeet_comm (a b : Rung) : rungMeet a b = rungMeet b a := by revert a b; decide

/-- [proved-derived; formal-checked] The meet is a lower bound of both. -/
theorem rungMeet_lower (a b : Rung) :
    a.entails (rungMeet a b) = true ∧ b.entails (rungMeet a b) = true := by revert a b; decide

/-- [proved-derived; formal-checked] And it is the greatest one. -/
theorem rungMeet_greatest (a b c : Rung) (ha : a.entails c = true) (hb : b.entails c = true) :
    (rungMeet a b).entails c = true := by revert ha hb; revert a b c; decide

/-! ## The implications that hold -/

/-- [proved-derived; formal-checked] Rung 1 supplies rung 3: the identity symmetry. -/
def identityAuto (S : Situation Generator Receiver Source Face) {x y : Source} (h : x = y) :
    SituationAuto S x y where
  carrier := Equiv.refl Source
  step_natural _ _ := rfl
  observe_natural _ _ := rfl
  carries := h

/-- [proved-derived; formal-checked] Rung 1 supplies rung 2, through the identity passage of
`Foundation/Lineage.lean`. -/
def identityContinues {x y : Source} (h : x = y) :
    Continues (AddressedPassage.id Source) x y :=
  ⟨x, rfl, h⟩

/-- [definition] A situation automorphism read as an addressed passage: the occurrence population
is the carrier and the target boundary is the symmetry. -/
def SituationAuto.toPassage {S : Situation Generator Receiver Source Face} {x y : Source}
    (auto : SituationAuto S x y) : AddressedPassage Source Source where
  Occurrence := Source
  source := _root_.id
  target := auto.carrier

/-- [proved-derived; formal-checked] Rung 3 supplies rung 2: the symmetry is itself a passage and
`x` is the occurrence carrying `x` to `y`. -/
def SituationAuto.continues {S : Situation Generator Receiver Source Face} {x y : Source}
    (auto : SituationAuto S x y) : Continues auto.toPassage x y :=
  ⟨x, rfl, auto.carries⟩

/-- [proved-derived; formal-checked] The symmetry commutes with every ordered generator word, not
only with each generator. -/
theorem SituationAuto.transportWord_natural {S : Situation Generator Receiver Source Face}
    {x y : Source} (auto : SituationAuto S x y) (word : List Generator) (source : Source) :
    auto.carrier (transportWord S.step word source) =
      transportWord S.step word (auto.carrier source) := by
  induction word with
  | nil => rfl
  | cons generator word ih =>
    simp only [transportWord_cons]
    rw [auto.step_natural, ih]

/-- [proved-derived; formal-checked] **Rung 3 implies rung 5 under the equivariance hypothesis.**
The hypothesis is exactly `step_natural` together with `observe_natural`; both halves are used and
`receiverEquivarianceIsNecessary` / `generatorEquivarianceIsNecessary` show neither can be
dropped. -/
theorem situationAutoImpliesEqualPotential {S : Situation Generator Receiver Source Face}
    {x y : Source} (auto : SituationAuto S x y) : EqualPotential S x y := by
  intro receiver word
  rw [← auto.carries, ← auto.transportWord_natural word x, auto.observe_natural]

/-- [proved-derived; formal-checked] Checking naturality on a generator-closed carrier suffices
for every future from an occurrence in it. A finite executable certificate need not enumerate
the whole ambient source type, but it must check this closure; declaring a probe complete is
not that hypothesis. Rust: `Situation::automorphism_carrier_is_closed`. -/
theorem equalPotential_of_closedCarrier (S : Situation Generator Receiver Source Face)
    (carrier : Set Source) (map : Source → Source)
    (closed : ∀ g s, s ∈ carrier → S.step g s ∈ carrier)
    (natural : ∀ g s, s ∈ carrier → map (S.step g s) = S.step g (map s))
    (observes : ∀ r s, s ∈ carrier → S.observe r (map s) = S.observe r s)
    {x y : Source} (hx : x ∈ carrier) (carries : map x = y) : EqualPotential S x y := by
  have word_closed : ∀ (word : List Generator) s, s ∈ carrier →
      transportWord S.step word s ∈ carrier := by
    intro word
    induction word with
    | nil => intro s hs; exact hs
    | cons g word ih =>
      intro s hs
      exact closed g _ (ih s hs)
  have word_natural : ∀ (word : List Generator) s, s ∈ carrier →
      map (transportWord S.step word s) = transportWord S.step word (map s) := by
    intro word
    induction word with
    | nil => intro s _; rfl
    | cons g word ih =>
      intro s hs
      simp only [transportWord_cons]
      rw [natural g _ (word_closed word s hs), ih s hs]
  intro receiver word
  rw [← carries, ← word_natural word x hx, observes receiver _ (word_closed word x hx)]

/-- [proved-derived; formal-checked] **Rung 5 implies rung 4 at every declared receiver.** This is
`Foundation/CausalRelevance.lean::futureAgreement_le_presentAgreement`, cited. -/
theorem equalPotentialImpliesPresentAgreement {S : Situation Generator Receiver Source Face}
    {x y : Source} (same : EqualPotential S x y) : PresentAgreement S x y :=
  futureAgreement_le_presentAgreement S.observe S.step x y same

/-- [proved-derived; formal-checked] The same statement at one named receiver. -/
theorem equalPotentialImpliesReceiverEqual {S : Situation Generator Receiver Source Face}
    {x y : Source} (same : EqualPotential S x y) (receiver : Receiver) :
    ReceiverEqualAt S receiver x y :=
  same receiver []

/-- [proved-derived; formal-checked] **Rung 4 implies rung 6** at any non-negative declared
tolerance, when the receiver's face is the exact rational reading. -/
theorem receiverEqualImpliesWithinTolerance
    (S : Situation Generator Receiver Source ℚ) (receiver : Receiver)
    {tolerance : ℚ} (nonneg : 0 ≤ tolerance) {x y : Source}
    (same : ReceiverEqualAt S receiver x y) :
    WithinTolerance (S.observe receiver) tolerance x y := by
  simp only [WithinTolerance, ReceiverEqualAt] at same ⊢
  rw [same, sub_self, abs_zero]
  exact nonneg

/-- [proved-derived; formal-checked] Hence rung 5 implies rung 6 as well. -/
theorem equalPotentialImpliesWithinTolerance
    (S : Situation Generator Receiver Source ℚ) (receiver : Receiver)
    {tolerance : ℚ} (nonneg : 0 ≤ tolerance) {x y : Source}
    (same : EqualPotential S x y) :
    WithinTolerance (S.observe receiver) tolerance x y :=
  receiverEqualImpliesWithinTolerance S receiver nonneg
    (equalPotentialImpliesReceiverEqual same receiver)

/-- [proved-derived; formal-checked] **Rung 1 implies every other rung**, each through the owner
that carries it. -/
theorem identityImpliesEveryRung (S : Situation Generator Receiver Source ℚ)
    (receiver : Receiver) {tolerance : ℚ} (nonneg : 0 ≤ tolerance) {x y : Source} (h : x = y) :
    Nonempty (SituationAuto S x y) ∧ EqualPotential S x y ∧ PresentAgreement S x y ∧
      WithinTolerance (S.observe receiver) tolerance x y ∧
      Nonempty (Continues (AddressedPassage.id Source) x y) := by
  have auto : SituationAuto S x y := identityAuto S h
  have potentialEq : EqualPotential S x y := situationAutoImpliesEqualPotential auto
  exact ⟨⟨auto⟩, potentialEq, equalPotentialImpliesPresentAgreement potentialEq,
    equalPotentialImpliesWithinTolerance S receiver nonneg potentialEq,
    ⟨identityContinues h⟩⟩

/-! ## Rung 6 is a tolerance relation, and that is all it is -/

/-- [proved-derived; formal-checked] Reflexive at any non-negative declared tolerance. -/
theorem withinTolerance_refl (read : Source → ℚ) {tolerance : ℚ} (nonneg : 0 ≤ tolerance)
    (x : Source) : WithinTolerance read tolerance x x := by
  simp only [WithinTolerance, sub_self, abs_zero]
  exact nonneg

/-- [proved-derived; formal-checked] Symmetric. -/
theorem withinTolerance_symm {read : Source → ℚ} {tolerance : ℚ} {x y : Source}
    (h : WithinTolerance read tolerance x y) : WithinTolerance read tolerance y x := by
  simpa only [WithinTolerance, abs_sub_comm] using h

/-- [proved-derived; formal-checked] **And not transitive.** The witness is exact: `0`, `1`, `2`
read by the identity at tolerance `1`. A tolerance is an aperture, never an identification — the
same clause `Foundation/Bridge.lean::numericalResemblance_does_not_identify` proves for a
numerical resemblance. -/
theorem toleranceIsNotTransitive :
    WithinTolerance (id : ℚ → ℚ) 1 0 1 ∧ WithinTolerance (id : ℚ → ℚ) 1 1 2 ∧
      ¬ WithinTolerance (id : ℚ → ℚ) 1 0 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [WithinTolerance, id_eq] <;> norm_num

/-- [proved-derived; formal-checked] What it has instead of transitivity: an `n`-step chain of
tolerance-`ε` differences lies inside `n · ε`. The bound degrades linearly; it does not close. -/
theorem withinToleranceIterate (read : Source → ℚ) (tolerance : ℚ) (occurrence : ℕ → Source)
    (linked : ∀ n, WithinTolerance read tolerance (occurrence n) (occurrence (n + 1)))
    (steps : ℕ) :
    WithinTolerance read (steps * tolerance) (occurrence 0) (occurrence steps) := by
  induction steps with
  | zero => simp [WithinTolerance]
  | succ n ih =>
    have triangle : |read (occurrence 0) - read (occurrence (n + 1))| ≤
        |read (occurrence 0) - read (occurrence n)| +
          |read (occurrence n) - read (occurrence (n + 1))| := abs_sub_le _ _ _
    have step := linked n
    simp only [WithinTolerance] at ih step ⊢
    push_cast
    linarith

/-- [proved-derived; formal-checked] Rung 6 **is** `Foundation/ReceiverRelease.lean::width` inside
the declared tolerance, read on the two-element compatible family `{x, y}`: this is that owner's
own `abs_sub_le_width`, composed rather than restated. -/
theorem withinTolerance_of_width_le [DecidableEq Source] (read : Source → ℚ) (x y : Source)
    {tolerance : ℚ}
    (bounded : ReceiverRelease.width ({x, y} : Finset Source) ⟨x, by simp⟩ read ≤ tolerance) :
    WithinTolerance read tolerance x y :=
  le_trans (ReceiverRelease.abs_sub_le_width (F := ({x, y} : Finset Source)) ⟨x, by simp⟩ read
    (by simp) (by simp)) bounded

/-! ## Refinement: a larger declaration is a finer equivalence, and one separator refutes -/

/-- [proved-derived; formal-checked] An ordered word of the smaller generator family transports
exactly as its image in the larger one. -/
theorem transportWord_embed {Generator' : Type*} (S : Situation Generator Receiver Source Face)
    {Receiver' Face' : Type*} (S' : Situation Generator' Receiver' Source Face')
    (embedGenerator : Generator → Generator')
    (agree : ∀ generator source, S.step generator source = S'.step (embedGenerator generator) source)
    (word : List Generator) (source : Source) :
    transportWord S.step word source =
      transportWord S'.step (word.map embedGenerator) source := by
  induction word with
  | nil => rfl
  | cons generator word ih =>
    simp only [List.map_cons, transportWord_cons, ih, agree]

/-- [proved-derived; formal-checked] **Enlarging `(G, R)` refines the potential equivalence.** If
every admitted generator, receiver and face of `S` occurs in `S'` — the face embedding being
injective, so that no distinction is manufactured — then `S'`-equal potential implies `S`-equal
potential. The relation is antitone in the declaration. -/
theorem equalPotentialAntitone {Generator' Receiver' Face' : Type*}
    (S : Situation Generator Receiver Source Face)
    (S' : Situation Generator' Receiver' Source Face')
    (embedGenerator : Generator → Generator') (embedReceiver : Receiver → Receiver')
    (embedFace : Face → Face') (faithful : Function.Injective embedFace)
    (stepAgree : ∀ generator source,
      S.step generator source = S'.step (embedGenerator generator) source)
    (observeAgree : ∀ receiver source,
      embedFace (S.observe receiver source) = S'.observe (embedReceiver receiver) source)
    {x y : Source} (same : EqualPotential S' x y) : EqualPotential S x y := by
  intro receiver word
  apply faithful
  rw [observeAgree, observeAgree,
    transportWord_embed S S' embedGenerator stepAgree word x,
    transportWord_embed S S' embedGenerator stepAgree word y]
  exact same (embedReceiver receiver) (word.map embedGenerator)

/-- [proved-derived; formal-checked] **A single separating `(w, ρ)` refutes equal potential.** This
is the elementary form of `Foundation/CausalRelevance.lean::futureHistory_quotientNe_returns_separator`
and of `Foundation/ReceiverHistoryCompression.lean::separatingSuccessorReopensTheProposedQuotient`:
the separator is returned as content, never as a score. -/
theorem separatorRefutesEqualPotential (S : Situation Generator Receiver Source Face)
    {x y : Source} (receiver : Receiver) (word : List Generator)
    (separates : S.observe receiver (transportWord S.step word x) ≠
      S.observe receiver (transportWord S.step word y)) :
    ¬ EqualPotential S x y :=
  fun same => separates (same receiver word)

/-! ## Two situations, and what "transported along the iso" means -/

/-- [definition] An isomorphism **of situations**: the carriers, the generator index and the
receiver index all correspond, and both declared squares commute. This is the exact sense in which
the generators and receivers are *transported along the iso*.

Rust counterpart: `relation_ladder.rs::SituationIso`. -/
structure SituationIso {Generator' : Type*} {Receiver' : Type*} {Source' : Type*}
    (S : Situation Generator Receiver Source Face)
    (S' : Situation Generator' Receiver' Source' Face) where
  /-- The carriers correspond. -/
  carrier : Source ≃ Source'
  /-- The admitted generator families correspond. -/
  generator : Generator ≃ Generator'
  /-- The admitted receiver families correspond. -/
  receiver : Receiver ≃ Receiver'
  /-- The generator square commutes. -/
  step_natural : ∀ g source,
    carrier (S.step g source) = S'.step (generator g) (carrier source)
  /-- The receiver triangle commutes. -/
  observe_natural : ∀ r source,
    S.observe r source = S'.observe (receiver r) (carrier source)

namespace SituationIso

variable {Generator' Receiver' Source' : Type*}
  {S : Situation Generator Receiver Source Face}
  {S' : Situation Generator' Receiver' Source' Face}

/-- [proved-derived; formal-checked] The correspondence runs on ordered words. -/
theorem transportWord_natural (iso : SituationIso S S') (word : List Generator) (source : Source) :
    iso.carrier (transportWord S.step word source) =
      transportWord S'.step (word.map iso.generator) (iso.carrier source) := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    simp only [List.map_cons, transportWord_cons]
    rw [iso.step_natural, ih]

/-- [definition] The inverse situation isomorphism. -/
def symm (iso : SituationIso S S') : SituationIso S' S where
  carrier := iso.carrier.symm
  generator := iso.generator.symm
  receiver := iso.receiver.symm
  step_natural g source := by
    apply iso.carrier.injective
    rw [Equiv.apply_symm_apply, iso.step_natural, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  observe_natural r source := by
    rw [iso.observe_natural (iso.receiver.symm r) (iso.carrier.symm source),
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- [proved-derived; formal-checked] **Equal potential transports along a situation isomorphism.**
-/
theorem equalPotentialOf (iso : SituationIso S S') {x y : Source}
    (same : EqualPotential S x y) : EqualPotential S' (iso.carrier x) (iso.carrier y) := by
  intro r' word'
  have base := same (iso.receiver.symm r') (word'.map iso.generator.symm)
  rw [iso.observe_natural, iso.observe_natural, Equiv.apply_symm_apply,
    iso.transportWord_natural, iso.transportWord_natural, List.map_map] at base
  simpa using base

end SituationIso

/-- [proved-derived; formal-checked] And therefore in both directions. -/
theorem situationIsoTransportsEqualPotential {Generator' Receiver' Source' : Type*}
    {S : Situation Generator Receiver Source Face}
    {S' : Situation Generator' Receiver' Source' Face}
    (iso : SituationIso S S') (x y : Source) :
    EqualPotential S x y ↔ EqualPotential S' (iso.carrier x) (iso.carrier y) := by
  constructor
  · exact iso.equalPotentialOf
  · intro same
    have carried := iso.symm.equalPotentialOf same
    simpa [SituationIso.symm] using carried

/-! ## Across two times, identity is not statable -/

section TimeIndexed

variable {Time : Type u} {Chart : Time → Type v}

/-- [definition] A **situated occurrence**: the occurrence together with the index at which it
occurs. Two occurrences at distinct indices do not inhabit one type, so `x = y` is not even
statable between them; this sigma type is where the honest statement lives. -/
abbrev SituatedOccurrence (Chart : Time → Type v) := Σ time, Chart time

/-- [proved-derived; formal-checked] Identity of situated occurrences is exactly *equal index*
together with `HEq` of the occurrences. Neither half alone is identity. -/
theorem situatedOccurrenceEqIff {t u : Time} (x : Chart t) (y : Chart u) :
    (⟨t, x⟩ : SituatedOccurrence Chart) = ⟨u, y⟩ ↔ t = u ∧ HEq x y := by
  simp only [Sigma.mk.injEq]

/-- [proved-derived; formal-checked] Distinct indices give distinct situated occurrences outright:
**a later occurrence is not the earlier one**, whatever it carries. -/
theorem distinctIndexGivesDistinctOccurrence {t u : Time} (distinct : t ≠ u)
    (x : Chart t) (y : Chart u) :
    (⟨t, x⟩ : SituatedOccurrence Chart) ≠ ⟨u, y⟩ :=
  fun same => distinct (congrArg Sigma.fst same)

/-- [definition] A **time passage** `T_{u←t} : X t → X u` — the map the framework supplies between
occurrences at two indices, and the only thing it supplies. -/
structure TimePassage (Chart : Time → Type v) (t u : Time) where
  /-- What the passage carries. -/
  carry : Chart t → Chart u

/-- [proved-derived; formal-checked] **A passage does not identify its endpoints.** Even when the
passage carries `x` exactly to `y`, the two situated occurrences remain distinct. -/
theorem passageDoesNotIdentify {t u : Time} (distinct : t ≠ u)
    (passage : TimePassage Chart t u) (x : Chart t) :
    (⟨t, x⟩ : SituatedOccurrence Chart) ≠ ⟨u, passage.carry x⟩ :=
  distinctIndexGivesDistinctOccurrence distinct x _

/-- [definition] The addressed passage carrying exactly the occurrences a declared relation
admits. -/
def ofRelation {X : Type u} {Y : Type v} (related : X → Y → Prop) : AddressedPassage X Y where
  Occurrence := { pair : X × Y // related pair.1 pair.2 }
  source pair := pair.1.1
  target pair := pair.1.2

/-- [proved-derived; formal-checked] **Whatever relation is declared between two occurrence types
is the shadow of an addressed passage.** A passage is therefore what the framework supplies; and
by `Foundation/Lineage.lean::theSameRelationCanHideDifferentOccurrencePopulations` the addressed
form is the content while the relation is its truncation. -/
theorem shadowOfRelation {X : Type u} {Y : Type v} (related : X → Y → Prop) :
    AddressedPassage.shadow (ofRelation related) = related := by
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨⟨a, b⟩, holds⟩, sourceEq, targetEq⟩
    dsimp only [ofRelation] at sourceEq targetEq
    subst sourceEq
    subst targetEq
    exact holds
  · intro holds
    exact ⟨⟨(x, y), holds⟩, rfl, rfl⟩

end TimeIndexed

/-- [definition] A concrete time passage: the clock advances from `0` to `1` and the occurrence is
carried by `x ↦ x + 1`. It is exhibited so that `passageDoesNotIdentify` is not a statement about
an empty family. -/
def exampleTimePassage : TimePassage (fun _ : ℕ => ℚ) 0 1 :=
  ⟨fun value => value + 1⟩

/-- [proved-derived; formal-checked] And on that concrete passage the two situated occurrences
remain two. -/
theorem theExamplePassageDoesNotIdentify (value : ℚ) :
    (⟨0, value⟩ : SituatedOccurrence (fun _ : ℕ => ℚ)) ≠
      ⟨1, exampleTimePassage.carry value⟩ :=
  passageDoesNotIdentify (by decide) exampleTimePassage value


/-! ## The constructed counterexamples -/

open Holonics.Transport.ChangingReceiver in
/-- [definition] The declared lineage of the continuation counterexamples: one exact step forward,
cited from `Transport/ChangingReceiver.lean::translationPassage`. -/
def oneStepForward : AddressedPassage ℚ ℚ := translationPassage 1

/-- [definition] The situation whose single receiver is the exact rational reading itself. -/
def rationalIdentitySituation : Situation Unit Unit ℚ ℚ where
  observe _ value := value
  step _ := _root_.id

/-- [proved-derived; formal-checked] The passage carries `0` to `1`. -/
def zeroContinuesToOne : Continues oneStepForward 0 1 := by
  refine ⟨(0 : ℚ), rfl, ?_⟩
  show (0 : ℚ) + 1 = 1
  norm_num

/-- [counterexample; formal-checked] **A continuation with no equal face at any declared
receiver.** The lineage is real and every rung below it fails: no receiver equality, no equal
potential, and not even a reading inside tolerance `1/2`. Persistence is not sameness. -/
theorem continuationWithoutAnyEqualFace :
    Nonempty (Continues oneStepForward 0 1) ∧
      ¬ PresentAgreement rationalIdentitySituation 0 1 ∧
      ¬ EqualPotential rationalIdentitySituation 0 1 ∧
      ¬ WithinTolerance (rationalIdentitySituation.observe ()) (1 / 2) 0 1 := by
  refine ⟨⟨zeroContinuesToOne⟩, ?_, ?_, ?_⟩
  · intro agree
    have := agree ()
    norm_num [rationalIdentitySituation] at this
  · intro same
    have := equalPotentialImpliesPresentAgreement same ()
    norm_num [rationalIdentitySituation] at this
  · intro inside
    simp only [WithinTolerance, rationalIdentitySituation] at inside
    norm_num at inside

/-- [definition] The lossy passage: the first coordinate is transported and the second is not. -/
def forgetSecond : Transition (ℚ × ℚ) ℚ where
  Residual := ℚ
  apply pair := pair.1
  residual pair := pair.2
  reopen first second := (first, second)
  reopen_apply _ := rfl

/-- [definition] The same passage, addressed. -/
def lossyPassage : AddressedPassage (ℚ × ℚ) ℚ where
  Occurrence := ℚ × ℚ
  source := _root_.id
  target := Prod.fst

/-- [counterexample; formal-checked] **A continuation that is not an isomorphism.** Two distinct
occurrences continue to one face; the transition's residual is not a subsingleton, which by
`Foundation/ContinuingTower.lean::injective_of_subsingleton_residual` is exactly why it cannot be
invertible. The residual is what the later finer receiver would need. -/
theorem lossyContinuationIsNotAnIsomorphism :
    Nonempty (Continues lossyPassage (0, 0) 0) ∧ Nonempty (Continues lossyPassage (0, 1) 0) ∧
      ¬ Function.Injective forgetSecond.apply ∧ ¬ Subsingleton forgetSecond.Residual := by
  refine ⟨⟨⟨(0, 0), rfl, rfl⟩⟩, ⟨⟨(0, 1), rfl, rfl⟩⟩, ?_, ?_⟩
  · intro injective
    have collapse : ((0 : ℚ), (0 : ℚ)) = ((0 : ℚ), (1 : ℚ)) := injective rfl
    rw [Prod.mk.injEq] at collapse
    norm_num at collapse
  · intro subsingleton
    have collapse : (0 : ℚ) = 1 := @Subsingleton.elim ℚ subsingleton 0 1
    norm_num at collapse

/-- [definition] The three-step situation of `Foundation/CausalRelevance.lean`, packaged. Its
generator family is the coordinate swap and the third-coordinate sign flip; its one receiver reads
the first coordinate. -/
def threeSituation : Situation ThreeGenerator Unit ThreeSource ℚ where
  observe := firstReceiver
  step := threeStep

/-- [counterexample; formal-checked] **Equal face without equal potential.** The two occurrences
agree at every declared receiver now, and one swap separates them. The plan names this example and
it is cited, not rebuilt: `CausalRelevance.NonLinear.swap_reopens_second_coordinate`. -/
theorem receiverEqualityWithoutEqualPotential :
    PresentAgreement threeSituation (0, 0, 0) (0, 1, 0) ∧
      ¬ EqualPotential threeSituation (0, 0, 0) (0, 1, 0) :=
  ⟨fun _ => rfl, swap_reopens_second_coordinate⟩

/-- [definition] A generator with one fixed point and one two-cycle, read by a completely blind
receiver. -/
def blindStep : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

/-- [definition] The blind situation over that generator. -/
def blindSituation : Situation Unit Unit (Fin 3) Unit where
  observe _ _ := ()
  step _ := blindStep

/-- [counterexample; formal-checked] **Equal potential without isomorphism.** Nothing any declared
receiver will ever read separates `0` from `1`, so their potentials are equal; and **no** situation
automorphism carries `0` to `1`, because a symmetry commuting with the generator must carry its
fixed point to a fixed point and `1` is not one. Sameness for every future interaction is not
structural correspondence. -/
theorem equalPotentialWithoutIsomorphism :
    EqualPotential blindSituation 0 1 ∧ IsEmpty (SituationAuto blindSituation 0 1) := by
  refine ⟨fun _ _ => rfl, ⟨fun auto => ?_⟩⟩
  have natural : auto.carrier (blindStep 0) = blindStep (auto.carrier 0) :=
    auto.step_natural () 0
  have fixed : blindStep 0 = 0 := rfl
  rw [fixed, auto.carries] at natural
  exact absurd natural (by decide)

/-- [counterexample; formal-checked] And the situation's own transports never reach from `0` to
`1` either, so this pair has equal potential and no **generator** continuation. Rung 5 and rung 2
are genuinely incomparable. -/
theorem equalPotentialWithoutAGeneratorContinuation :
    EqualPotential blindSituation 0 1 ∧
      ∀ word : List Unit, transportWord blindSituation.step word 0 ≠ 1 := by
  refine ⟨fun _ _ => rfl, fun word => ?_⟩
  have fixedPoint : ∀ w : List Unit, transportWord blindSituation.step w 0 = 0 := by
    intro w
    induction w with
    | nil => rfl
    | cons _ w ih => simp only [transportWord_cons, ih]; rfl
  rw [fixedPoint word]
  decide

/-- [definition] A blind situation on `Bool` with no generator content. -/
def blindBoolSituation : Situation Unit Unit Bool Unit where
  observe _ _ := ()
  step _ := _root_.id

/-- [definition] Negation as a symmetry of the blind `Bool` situation. -/
def negationAuto : SituationAuto blindBoolSituation false true where
  carrier := ⟨not, not, by decide, by decide⟩
  step_natural _ _ := rfl
  observe_natural _ _ := rfl
  carries := rfl

/-- [counterexample; formal-checked] **An isomorphism without identity.** A complete symmetry of
the situation carries one occurrence to the other and they remain two occurrences. -/
theorem isomorphismWithoutIdentity :
    Nonempty (SituationAuto blindBoolSituation false true) ∧ (false : Bool) ≠ true :=
  ⟨⟨negationAuto⟩, by decide⟩

/-- [definition] The same carrier, now with a faithful receiver. -/
def faithfulBoolSituation : Situation Unit Unit Bool Bool where
  observe _ value := value
  step _ := _root_.id

/-- [counterexample; formal-checked] **The receiver half of the equivariance hypothesis is
necessary.** A bijection commuting with every admitted generator, carrying `false` to `true`, whose
endpoints have different potentials — because it does not commute with the receiver. -/
theorem receiverEquivarianceIsNecessary :
    ∃ symmetry : Bool ≃ Bool,
      (∀ generator source, symmetry (faithfulBoolSituation.step generator source) =
        faithfulBoolSituation.step generator (symmetry source)) ∧
        symmetry false = true ∧
        ¬ EqualPotential faithfulBoolSituation false true := by
  refine ⟨⟨not, not, by decide, by decide⟩, fun _ _ => rfl, rfl, fun same => ?_⟩
  exact absurd (same () []) (by decide)

/-- [definition] A shift of the second coordinate: it preserves the three-step situation's
receiver exactly and does not commute with its swap generator. -/
def shiftSecond : ThreeSource ≃ ThreeSource where
  toFun source := (source.1, source.2.1 + 1, source.2.2)
  invFun source := (source.1, source.2.1 - 1, source.2.2)
  left_inv := by rintro ⟨a, b, c⟩; simp
  right_inv := by rintro ⟨a, b, c⟩; simp

/-- [counterexample; formal-checked] **The generator half of the equivariance hypothesis is
necessary.** A bijection commuting with every admitted receiver, carrying `(0,0,0)` to `(0,1,0)`,
whose endpoints have different potentials — because it does not commute with the swap. -/
theorem generatorEquivarianceIsNecessary :
    (∀ receiver source, threeSituation.observe receiver (shiftSecond source) =
        threeSituation.observe receiver source) ∧
      shiftSecond (0, 0, 0) = (0, 1, 0) ∧
      ¬ EqualPotential threeSituation (0, 0, 0) (0, 1, 0) ∧
      ¬ (∀ generator source, shiftSecond (threeSituation.step generator source) =
          threeSituation.step generator (shiftSecond source)) := by
  refine ⟨fun _ _ => rfl, ?_, swap_reopens_second_coordinate, ?_⟩
  · show ((0 : ℚ), (0 : ℚ) + 1, (0 : ℚ)) = (0, 1, 0)
    norm_num
  · intro commutes
    have broken := commutes false (0, 0, 0)
    simp only [threeSituation, threeStep, shiftSecond, Equiv.coe_fn_mk] at broken
    norm_num [Prod.ext_iff] at broken

/-- [counterexample; formal-checked] **A tolerance identifies nothing.** Two occurrences read
inside tolerance `1` that no receiver equality and no identity relate. -/
theorem toleranceIsWithoutIdentification :
    WithinTolerance (rationalIdentitySituation.observe ()) 1 0 1 ∧
      ¬ ReceiverEqualAt rationalIdentitySituation () 0 1 ∧ (0 : ℚ) ≠ 1 := by
  refine ⟨?_, ?_, by norm_num⟩
  · simp only [WithinTolerance, rationalIdentitySituation]
    norm_num
  · intro same
    simp only [ReceiverEqualAt, rationalIdentitySituation] at same
    norm_num at same

/-- [proved-derived; formal-checked] **The headline: no rung below identity ascends to identity.**
Each of rungs 2, 3, 4, 5 and 6 is inhabited by a pair that is not identical, so from none of them
can `x = y` be concluded. With `no_rung_below_identity_entails_identity` this is the statement in
both its forms — the declared order and its witnesses. -/
theorem noRungBelowIdentityAscendsToIdentity :
    (Nonempty (Continues oneStepForward 0 1) ∧ (0 : ℚ) ≠ 1) ∧
      (Nonempty (SituationAuto blindBoolSituation false true) ∧ (false : Bool) ≠ true) ∧
      (PresentAgreement threeSituation (0, 0, 0) (0, 1, 0) ∧
        ((0, 0, 0) : ThreeSource) ≠ (0, 1, 0)) ∧
      (EqualPotential blindSituation 0 1 ∧ (0 : Fin 3) ≠ 1) ∧
      (WithinTolerance (rationalIdentitySituation.observe ()) 1 0 1 ∧ (0 : ℚ) ≠ 1) := by
  refine ⟨⟨⟨zeroContinuesToOne⟩, by norm_num⟩, isomorphismWithoutIdentity,
    ⟨receiverEqualityWithoutEqualPotential.1, ?_⟩,
    ⟨equalPotentialWithoutIsomorphism.1, by decide⟩,
    ⟨toleranceIsWithoutIdentification.1, by norm_num⟩⟩
  intro same
  norm_num [Prod.ext_iff] at same

/-! ## A situation isomorphism, constructed, and a pair of situations that admit none -/

/-- [definition] The three-step situation with its two generator labels exchanged. Nothing about
the carrier or the receiver changes; only the index of the generator family does. -/
def swappedThreeSituation : Situation ThreeGenerator Unit ThreeSource ℚ where
  observe := firstReceiver
  step generator := threeStep (!generator)

/-- [proved-derived; formal-checked] A constructed `SituationIso`: the identity on the carrier and
on the receiver index, and negation on the generator index. This is exactly what "the generators
are transported along the iso" means, and it exhibits the structure so that
`situationIsoTransportsEqualPotential` is not a statement about an empty family. -/
def relabelGeneratorsIso : SituationIso threeSituation swappedThreeSituation where
  carrier := Equiv.refl ThreeSource
  generator := ⟨not, not, by decide, by decide⟩
  receiver := Equiv.refl Unit
  step_natural generator source := by cases generator <;> rfl
  observe_natural _ _ := rfl

/-- [proved-derived; formal-checked] The relabelling transports the potential exactly: the pair the
three-step example separates is separated in the relabelled situation too. -/
theorem relabellingTransportsTheSeparation :
    ¬ EqualPotential swappedThreeSituation (0, 0, 0) (0, 1, 0) := by
  intro same
  exact swap_reopens_second_coordinate
    ((situationIsoTransportsEqualPotential relabelGeneratorsIso (0, 0, 0) (0, 1, 0)).mpr same)

/-- [counterexample; formal-checked] And a pair of situations that admits **no** isomorphism at
all: their carriers have different finite cardinalities, so no `Equiv` between them exists. A
structure-preserving correspondence is a real obligation and not a formality. -/
theorem noSituationIsoBetweenCarriersOfDifferentSize :
    IsEmpty (SituationIso blindBoolSituation blindSituation) :=
  ⟨fun iso => by
    have counted : Fintype.card Bool = Fintype.card (Fin 3) := Fintype.card_congr iso.carrier
    simp at counted⟩

/-! ## Worked instance (a): `Expression` against `eval`, with `4` and `2 ^ 2` -/

/-- [definition] A construction, retained as the syntax tree it is. `eval` is one receiver of it. -/
inductive Expression
  /-- A literal. -/
  | lit (value : ℕ)
  /-- A sum. -/
  | add (left right : Expression)
  /-- A product. -/
  | mul (left right : Expression)
  /-- A power. -/
  | pow (base exponent : Expression)
  deriving DecidableEq, Repr

/-- [definition] The scalar receiver: the denoted value. -/
def eval : Expression → ℕ
  | .lit value => value
  | .add left right => eval left + eval right
  | .mul left right => eval left * eval right
  | .pow base exponent => eval base ^ eval exponent

/-- [definition] The literal `4`. -/
def four : Expression := .lit 4

/-- [definition] The construction `2 ^ 2`. -/
def twoSquared : Expression := .pow (.lit 2) (.lit 2)

/-- [definition] A generator that rewrites the **construction**: it increments the exponent of a
power and leaves every other expression alone. Under it the two formulations generalize
differently. -/
def bumpExponent : Expression → Expression
  | .pow base (.lit exponent) => .pow base (.lit (exponent + 1))
  | other => other

/-- [definition] A generator family that only **post-composes** `eval`: it replaces an expression
by the literal of its value shifted by `k`. Every member factors through the scalar receiver. -/
def postcomposeAdd (shift : ℕ) (expression : Expression) : Expression :=
  .lit (eval expression + shift)

/-- [definition] The situation whose generators rewrite the construction. -/
def constructionSituation : Situation Unit Unit Expression ℕ where
  observe _ := eval
  step _ := bumpExponent

/-- [definition] The situation whose generators only post-compose `eval`. -/
def valueSituation : Situation ℕ Unit Expression ℕ where
  observe _ := eval
  step := postcomposeAdd

/-- [definition] Both generator families at once: `none` rewrites the construction, `some k`
post-composes. -/
def jointExpressionSituation : Situation (Option ℕ) Unit Expression ℕ where
  observe _ := eval
  step
    | none, expression => bumpExponent expression
    | some shift, expression => postcomposeAdd shift expression

/-- [proved-derived; formal-checked] The two formulations agree at the scalar receiver. -/
theorem fourAndTwoSquaredAgreeUnderEval : eval four = eval twoSquared := by decide

/-- [counterexample; formal-checked] And they are not the same occurrence: distinct syntax trees,
distinct constructions. -/
theorem fourAndTwoSquaredAreNotIdentical : four ≠ twoSquared := by decide

/-- [counterexample; formal-checked] One construction generator separates them: bumping the
exponent leaves `4` at `4` and takes `2 ^ 2` to `2 ^ 3 = 8`. So **the equality belongs to the
scalar receiver and does not ascend**: they are rung 4 and not rung 5 under this generator
family. -/
theorem bumpExponentSeparatesThem :
    ¬ EqualPotential constructionSituation four twoSquared :=
  separatorRefutesEqualPotential constructionSituation () [()] (by decide)

/-- [proved-derived; formal-checked] Under a generator family that only post-composes `eval`, the
two formulations do have equal potential: nothing that family can do ever reaches the difference in
their construction. Which rung holds is a fact about the declared `(G, R)`, not about the pair. -/
theorem postcomposeFamilyGivesEqualPotential :
    EqualPotential valueSituation four twoSquared := by
  intro _ word
  show eval (transportWord valueSituation.step word four) =
    eval (transportWord valueSituation.step word twoSquared)
  induction word with
  | nil => decide
  | cons shift word ih =>
    simp only [transportWord_cons]
    show eval (postcomposeAdd shift _) = eval (postcomposeAdd shift _)
    simp only [postcomposeAdd, eval]
    rw [ih]

/-- [proved-derived; formal-checked] The complete reading of `4` against `2 ^ 2`: equal at the
scalar receiver, equal in potential under the value-only family, separated in potential by one
construction generator, and never identical. -/
theorem theEqualityBelongsToTheScalarReceiver :
    ReceiverEqualAt constructionSituation () four twoSquared ∧
      EqualPotential valueSituation four twoSquared ∧
      ¬ EqualPotential constructionSituation four twoSquared ∧
      four ≠ twoSquared :=
  ⟨fourAndTwoSquaredAgreeUnderEval, postcomposeFamilyGivesEqualPotential,
    bumpExponentSeparatesThem, fourAndTwoSquaredAreNotIdentical⟩

/-- [proved-derived; formal-checked] Enlarging the generator family refines the class: the
value-only potential equality is implied by the joint one — `equalPotentialAntitone` — and the
joint one fails. Adding a generator can only split a potential class, never merge it. -/
theorem enlargingTheGeneratorFamilyRefines :
    (EqualPotential jointExpressionSituation four twoSquared →
        EqualPotential valueSituation four twoSquared) ∧
      ¬ EqualPotential jointExpressionSituation four twoSquared := by
  refine ⟨?_, separatorRefutesEqualPotential jointExpressionSituation () [none] (by decide)⟩
  intro joint
  exact equalPotentialAntitone valueSituation jointExpressionSituation some _root_.id _root_.id
    Function.injective_id (fun _ _ => rfl) (fun _ _ => rfl) joint

/-! ## Worked instance (b): the same song -/

/-- [definition] An **enactment**: an exact rational pitch sequence, an exact rational onset
sequence, and a declared timbre label. No float participates; the pitches are exact rational
intervals above a reference and the onsets are exact rational times. -/
structure Enactment where
  /-- The pitches, exactly. -/
  pitch : List ℚ
  /-- The onsets, exactly. -/
  onset : List ℚ
  /-- The declared timbre label. -/
  timbre : ℕ
  deriving DecidableEq, Repr

/-- [definition] Consecutive differences of an exact rational sequence. -/
def gaps : List ℚ → List ℚ
  | [] => []
  | [_] => []
  | first :: second :: rest => (second - first) :: gaps (second :: rest)

/-- [definition] A sequence normalized by its first entry. Division in `ℚ` is exact; the total
convention `x / 0 = 0` is Lean's and is declared here rather than hidden. -/
def normalizedByFirst : List ℚ → List ℚ
  | [] => []
  | first :: rest => 1 :: rest.map (fun entry => entry / first)

/-- [definition] The interval contour: transposition-invariant by construction. -/
def intervalContour (enactment : Enactment) : List ℚ := gaps enactment.pitch

/-- [definition] The rhythm-ratio contour: tempo-invariant by construction. -/
def rhythmContour (enactment : Enactment) : List ℚ := normalizedByFirst (gaps enactment.onset)

/-- [definition] **The musical receiver**: interval contour and rhythm-ratio contour. -/
def musicalFace (enactment : Enactment) : List ℚ × List ℚ :=
  (intervalContour enactment, rhythmContour enactment)

/-- [definition] **The richer receiver**: absolute pitch, absolute onset and the timbre label. -/
def absoluteFace (enactment : Enactment) : List ℚ × List ℚ × ℕ :=
  (enactment.pitch, enactment.onset, enactment.timbre)

/-- [definition] Transposition by one exact rational interval. -/
def transpose (interval : ℚ) (enactment : Enactment) : Enactment :=
  { enactment with pitch := enactment.pitch.map (fun value => value + interval) }

/-- [definition] Tempo scaling by an exact nonzero rational factor. -/
def scaleTempo (factor : ℚ) (enactment : Enactment) : Enactment :=
  { enactment with onset := enactment.onset.map (fun time => factor * time) }

/-- [definition] Re-voicing: a different declared timbre, the same pitches and onsets. -/
def revoice (label : ℕ) (enactment : Enactment) : Enactment :=
  { enactment with timbre := label }

/-- [definition] The **admissible transformations of the song**. A zero tempo factor is not
admissible and the constructor carries that proof, so the family cannot be formed with one. -/
inductive Admissible
  /-- Transpose by an exact interval. -/
  | transpose (interval : ℚ)
  /-- Scale the tempo by an exact nonzero factor. -/
  | scaleTempo (factor : ℚ) (nonzero : factor ≠ 0)
  /-- Re-voice. -/
  | revoice (label : ℕ)

/-- [definition] How an admissible transformation acts. -/
def enact : Admissible → Enactment → Enactment
  | .transpose interval, enactment => transpose interval enactment
  | .scaleTempo factor _, enactment => scaleTempo factor enactment
  | .revoice label, enactment => revoice label enactment

/-- [definition] **The song**: the family of admissible enactments together with the admissible
transformations, read by the musical receiver. The song is not one acoustic object. -/
def songSituation : Situation Admissible Unit Enactment (List ℚ × List ℚ) where
  observe _ := musicalFace
  step := enact

/-- [definition] The same family read by the richer receiver. -/
def absoluteSituation : Situation Admissible Unit Enactment (List ℚ × List ℚ × ℕ) where
  observe _ := absoluteFace
  step := enact

/-- [proved-derived; formal-checked] Transposition does not change the interval contour. -/
theorem gaps_map_add (interval : ℚ) :
    ∀ sequence : List ℚ, gaps (sequence.map (fun value => value + interval)) = gaps sequence
  | [] => rfl
  | [_] => rfl
  | first :: second :: rest => by
    have ih := gaps_map_add interval (second :: rest)
    simp only [List.map_cons] at ih ⊢
    simp only [gaps]
    exact congrArg₂ List.cons (by ring) ih

/-- [proved-derived; formal-checked] Tempo scaling scales every gap. -/
theorem gaps_map_mul (factor : ℚ) :
    ∀ sequence : List ℚ, gaps (sequence.map (fun time => factor * time)) =
      (gaps sequence).map (fun gap => factor * gap)
  | [] => rfl
  | [_] => rfl
  | first :: second :: rest => by
    have ih := gaps_map_mul factor (second :: rest)
    simp only [List.map_cons] at ih ⊢
    simp only [gaps, List.map_cons]
    exact congrArg₂ List.cons (by ring) ih

/-- [proved-derived; formal-checked] A nonzero common factor is invisible after normalization. -/
theorem normalizedByFirst_map_mul {factor : ℚ} (nonzero : factor ≠ 0) :
    ∀ sequence : List ℚ,
      normalizedByFirst (sequence.map (fun gap => factor * gap)) = normalizedByFirst sequence
  | [] => rfl
  | first :: rest => by
    have pointwise : (fun entry : ℚ => factor * entry / (factor * first))
        = fun entry : ℚ => entry / first := by
      funext entry
      exact mul_div_mul_left entry first nonzero
    simp only [List.map_cons, normalizedByFirst, List.map_map, Function.comp_def, pointwise]

/-- [proved-derived; formal-checked] **Every admissible transformation is musically invisible.**
That is what makes the family one song at the musical receiver. -/
theorem admissibleTransformationsAreMusicallyInvisible (transformation : Admissible)
    (enactment : Enactment) : musicalFace (enact transformation enactment) = musicalFace enactment := by
  cases transformation with
  | transpose interval =>
    simp only [enact, musicalFace, intervalContour, rhythmContour, transpose, gaps_map_add]
  | scaleTempo factor nonzero =>
    simp only [enact, musicalFace, intervalContour, rhythmContour, scaleTempo, gaps_map_mul,
      normalizedByFirst_map_mul nonzero]
  | revoice label =>
    simp only [enact, musicalFace, intervalContour, rhythmContour, revoice]

/-- [proved-derived; formal-checked] **Equal musical face is equal potential over the admissible
family.** The song class is a rung-5 class, not merely a rung-4 one. -/
theorem equalMusicalFaceGivesEqualPotential {left right : Enactment}
    (same : musicalFace left = musicalFace right) : EqualPotential songSituation left right := by
  intro _ word
  show musicalFace (transportWord songSituation.step word left) =
    musicalFace (transportWord songSituation.step word right)
  induction word with
  | nil => exact same
  | cons transformation word ih =>
    simp only [transportWord_cons]
    show musicalFace (enact transformation _) = musicalFace (enact transformation _)
    rw [admissibleTransformationsAreMusicallyInvisible,
      admissibleTransformationsAreMusicallyInvisible]
    exact ih

/-- [definition] One enactment. -/
def firstEnactment : Enactment := { pitch := [0, 2, 4], onset := [0, 1, 2], timbre := 0 }

/-- [definition] Another: transposed by seven, twice as slow, differently voiced. -/
def secondEnactment : Enactment := revoice 1 (scaleTempo 2 (transpose 7 firstEnactment))

/-- [proved-derived; formal-checked] They are one class at the musical receiver. -/
theorem theTwoEnactmentsAgreeMusically :
    musicalFace firstEnactment = musicalFace secondEnactment := by
  simp only [musicalFace, intervalContour, rhythmContour, firstEnactment, secondEnactment,
    revoice, scaleTempo, transpose, gaps, normalizedByFirst, List.map_cons, List.map_nil]
  norm_num

/-- [counterexample; formal-checked] And the richer receiver separates them. -/
theorem theAbsoluteReceiverSeparatesThem :
    absoluteFace firstEnactment ≠ absoluteFace secondEnactment := by
  simp only [absoluteFace, firstEnactment, secondEnactment, revoice, scaleTempo, transpose,
    List.map_cons, List.map_nil]
  norm_num

/-- [proved-derived; formal-checked] **The song is the family of admissible enactments and
transformations, not one acoustic object.** The two enactments are one class under the musical
receiver — with equal potential over the whole admissible family — and two occurrences under the
richer receiver, which separates them at rung 4 and therefore at rung 5. -/
theorem theSongIsTheFamilyNotOneEnactment :
    firstEnactment ≠ secondEnactment ∧
      EqualPotential songSituation firstEnactment secondEnactment ∧
      ¬ PresentAgreement absoluteSituation firstEnactment secondEnactment ∧
      ¬ EqualPotential absoluteSituation firstEnactment secondEnactment := by
  have musical := equalMusicalFaceGivesEqualPotential theTwoEnactmentsAgreeMusically
  have separated : ¬ PresentAgreement absoluteSituation firstEnactment secondEnactment := by
    intro agree
    exact theAbsoluteReceiverSeparatesThem (agree ())
  refine ⟨?_, musical, separated, fun same => separated (equalPotentialImpliesPresentAgreement same)⟩
  intro identical
  exact theAbsoluteReceiverSeparatesThem (congrArg absoluteFace identical)

end Holonics.Foundation.RelationLadder

section Audit
open Holonics.Foundation.RelationLadder
#print axioms entails_antisymm
#print axioms rungMeet_greatest
#print axioms no_rung_below_identity_entails_identity
#print axioms situationAutoImpliesEqualPotential
#print axioms equalPotential_of_closedCarrier
#print axioms equalPotentialImpliesPresentAgreement
#print axioms receiverEqualImpliesWithinTolerance
#print axioms identityImpliesEveryRung
#print axioms equalPotentialAntitone
#print axioms separatorRefutesEqualPotential
#print axioms situationIsoTransportsEqualPotential
#print axioms withinToleranceIterate
#print axioms withinTolerance_of_width_le
#print axioms situatedOccurrenceEqIff
#print axioms passageDoesNotIdentify
#print axioms shadowOfRelation
#print axioms receiverEqualityWithoutEqualPotential
#print axioms equalPotentialWithoutIsomorphism
#print axioms equalPotentialWithoutAGeneratorContinuation
#print axioms isomorphismWithoutIdentity
#print axioms continuationWithoutAnyEqualFace
#print axioms lossyContinuationIsNotAnIsomorphism
#print axioms receiverEquivarianceIsNecessary
#print axioms generatorEquivarianceIsNecessary
#print axioms toleranceIsNotTransitive
#print axioms noRungBelowIdentityAscendsToIdentity
#print axioms theEqualityBelongsToTheScalarReceiver
#print axioms enlargingTheGeneratorFamilyRefines
#print axioms theExamplePassageDoesNotIdentify
#print axioms relabellingTransportsTheSeparation
#print axioms noSituationIsoBetweenCarriersOfDifferentSize
#print axioms theSongIsTheFamilyNotOneEnactment
end Audit
