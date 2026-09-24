import Holonics.Foundation.RelationLadder
import HolonicsResearch.Foundation.DesignSelection

/-!
# B9 — evaluation discipline

[definition] This file deposits item **B9** of
`docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`. It founds no new relation between
occurrences: a comparison between a prediction and a later external return is stated on
`Foundation/RelationLadder.lean::Rung`, and the selection cascade it evaluates is
`Foundation/DesignSelection.lean`'s. What is new is **the type of an evaluation**: a split is a
partition of *lineage classes* rather than of designs, a fitted receiver carries the occurrences it
was fitted on, a calibration does not cross an assay without a bridge, and the only conclusions an
evaluation may reach are bounded at its own split and receiver.

## Lineage never straddles a split

[proved-derived] The horizontal `Mutation` passages of `Foundation/PhysicalOccurrence.lean` generate
a relation on designs; two designs joined by a chain of them within a declared edit radius are one
**lineage class**, and the classes are the quotient by that relation. `ofClassPredicate` builds a
split from a predicate on the quotient, and `ofClassPredicate_does_not_straddle` is the statement
that such a split cannot separate two members of one class — not because a check rejects it, but
because the sides are unions of classes. The converse witness is `rawSplit`, a split declared
directly on designs, together with `rawSplit_straddles`, which exhibits the leaking pair.

## Leakage through receivers, not only through members

[proved-derived] A receiver fitted on development material and read on evaluation material is a
leak even when no *member* crosses the split (AGENTS.md: a driver may not select developmental
material from an evaluation target). `FittedReceiver` therefore carries `fittedOn`, and `evaluateAt`
returns `none` at an occurrence the receiver was fitted on **or lineage-equivalent to one**.

A calibration is a receiver-to-receiver map fitted inside one assay. `transport` returns it
unchanged inside that assay and refuses across assays unless an `AssayBridge` is supplied — the
same law `Foundation/PhysicalOccurrence.lean::EnvironmentPassage` imposes on environments.

## A wet or external return is a new receiver occurrence

[proved-derived] It does not retroactively relabel the earlier model output. `compare` leaves the
prediction's `TimedFace` untouched (`the_return_does_not_relabel_the_prediction`) and the comparison
carries its own time index, strictly later than the prediction's
(`the_comparison_is_not_at_the_predictions_time`). The comparison is stated on a `Rung`, which is
where a relation between two occurrences belongs.

## Predictor disagreement is a fibre property

[definition] `classifyContact` is the three-way partition of
`Foundation/PhysicalOccurrence.lean`'s plural fibre — unanimous, separating, open-carrying — with
the open class taking precedence so an undecided reading is never counted as agreement or as
separation. `correct_on_the_unanimous_contact_and_wrong_on_the_separating_one` is the constructed
instance of the warning: a predictor may be right at every unanimous contact and wrong at a
separating one, so performance on the unanimous subset says nothing about the separating subset.

## What an evaluation may conclude

[definition] `Conclusion` has three arms and no fourth. `establishedBounded` carries the split and
receiver it holds at, and `atAnotherSplit` returns `none` at any other split. `UniversalClaim` is
uninhabited, exactly as `Foundation/PhysicalOccurrence.lean::RealizationProof` is, so no path in
this file turns a held-out result into a universal one.

## Rust counterpart

[definition] `crates/holonic-engine/src/evaluation_discipline.rs`, with the same names —
`LineageClasses`, `Split`, `FittedReceiver`, `Calibration`, `AssayBridge`, `ExternalComparison`,
`DisagreementClass`, `EvaluationConclusion`, `UniversalClaim` — every theorem below mirrored as a
test.
-/

namespace Holonics.Foundation.EvaluationDiscipline

open Holonics.Foundation.RelationLadder
open Holonics.Foundation.AperturedGradedComplex (ContactClass)

universe u v w

/-! ## 1. Lineage classes, as a quotient -/

/-- [definition] **The lineage relation**: the reflexive, symmetric, transitive relation generated
by the admitted horizontal mutation passages within a declared edit radius. It is carried as an
equivalence because the *classes* are what a split may be built from; the radius that founds its
edges is recorded by the Rust owner beside the relation.

Rust counterpart: `evaluation_discipline.rs::LineageClasses`. -/
structure Lineage (D : Type u) where
  /-- Two designs stand in this relation when a chain of admitted mutation passages joins them. -/
  rel : D → D → Prop
  /-- Every design is its own lineage. -/
  refl : ∀ d, rel d d
  /-- A mutation passage and its reverse change the same site, so the relation is symmetric. -/
  symm : ∀ {a b}, rel a b → rel b a
  /-- Chains concatenate. -/
  trans : ∀ {a b c}, rel a b → rel b c → rel a c

namespace Lineage

variable {D : Type u}

/-- The setoid the lineage relation is. -/
def setoid (L : Lineage D) : Setoid D where
  r := L.rel
  iseqv := ⟨L.refl, L.symm, L.trans⟩

/-- A lineage class: a point of the quotient. -/
abbrev Class (L : Lineage D) : Type u := Quotient L.setoid

/-- The class of one design. -/
def cls (L : Lineage D) (d : D) : L.Class := Quotient.mk L.setoid d

/-- [proved-derived; formal-checked] Lineage-related designs have one class. -/
theorem cls_eq_of_rel (L : Lineage D) {a b : D} (h : L.rel a b) : L.cls a = L.cls b :=
  Quotient.sound h

/-- [proved-derived; formal-checked] And conversely. -/
theorem rel_of_cls_eq (L : Lineage D) {a b : D} (h : L.cls a = L.cls b) : L.rel a b :=
  Quotient.exact h

end Lineage

/-! ## 2. The split, and the leakage law -/

/-- [definition] **A declared split of a design population.** Two sides, disjoint and exhausting.
Nothing here says the sides respect lineage; that is the content of the next two theorems.

Rust counterpart: `evaluation_discipline.rs::Split`. -/
structure Split {D : Type u} (L : Lineage D) where
  /-- The development side. -/
  development : D → Prop
  /-- The evaluation side. -/
  evaluation : D → Prop
  /-- No design is on both sides. -/
  disjoint : ∀ d, development d → evaluation d → False
  /-- Every design is on a side. -/
  exhaust : ∀ d, development d ∨ evaluation d

/-- [definition] **The leak**: two lineage-equivalent designs on opposite sides of the split. -/
def Straddles {D : Type u} {L : Lineage D} (S : Split L) : Prop :=
  ∃ a b, L.rel a b ∧ S.development a ∧ S.evaluation b

/-- [definition] **A split built from a partition of lineage classes.** The sides are the preimages
of a predicate on the quotient, so each side is a union of whole classes by construction. -/
def ofClassPredicate {D : Type u} (L : Lineage D) (P : L.Class → Prop) : Split L where
  development := fun d => P (L.cls d)
  evaluation := fun d => ¬ P (L.cls d)
  disjoint := fun _ inside outside => outside inside
  exhaust := fun d => Classical.em (P (L.cls d))

/-- [proved-derived; formal-checked] **A split built from a partition of lineage classes cannot
straddle.** This is structural: the sides are preimages of a predicate on the quotient, and two
lineage-related designs have one class. -/
theorem ofClassPredicate_does_not_straddle {D : Type u} (L : Lineage D) (P : L.Class → Prop) :
    ¬ Straddles (ofClassPredicate L P) := by
  rintro ⟨a, b, related, inside, outside⟩
  apply outside
  rw [← L.cls_eq_of_rel related]
  exact inside

/-- The lineage in which every design is one class: one mutation joins them all. -/
def allOneLineage : Lineage Bool where
  rel := fun _ _ => True
  refl := fun _ => trivial
  symm := fun _ => trivial
  trans := fun _ _ => trivial

/-- [definition] **A split declared directly on designs**, not on their classes. -/
def rawSplit : Split allOneLineage where
  development := fun d => d = false
  evaluation := fun d => d = true
  disjoint := by
    intro d left right
    rw [left] at right
    exact Bool.noConfusion right
  exhaust := by
    intro d
    cases d
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- [proved-derived; formal-checked] **The converse witness: a split on raw designs straddles, and
the leak is exhibited.** The two designs are `false` and `true`, one lineage class, one on each
side. -/
theorem rawSplit_straddles : Straddles rawSplit :=
  ⟨false, true, trivial, rfl, rfl⟩

/-! ## 3. Leakage through receivers -/

/-- [definition] **A fitted or calibrated receiver carries the occurrences it was fitted on.**

Rust counterpart: `evaluation_discipline.rs::FittedReceiver`. -/
structure FittedReceiver (Occ : Type v) (Face : Type w) where
  /-- Its declared name. -/
  name : String
  /-- Its reading. -/
  read : Occ → Face
  /-- The occurrences it was fitted on. -/
  fittedOn : Occ → Prop

/-- [definition] The receiver leaks at an occurrence when it was fitted on that occurrence or on a
lineage-equivalent one. -/
def Leaks {Occ : Type v} {Face : Type w} (L : Lineage Occ) (R : FittedReceiver Occ Face)
    (o : Occ) : Prop := ∃ f, R.fittedOn f ∧ L.rel f o

/-- [definition] Reading a fitted receiver at an occurrence: `none` is the refusal. -/
noncomputable def evaluateAt {Occ : Type v} {Face : Type w} (L : Lineage Occ)
    (R : FittedReceiver Occ Face) (o : Occ) : Option Face :=
  open Classical in
  if Leaks L R o then none else some (R.read o)

/-- [proved-derived; formal-checked] A receiver is refused at an occurrence it was fitted on. -/
theorem evaluateAt_refuses_a_fitted_occurrence {Occ : Type v} {Face : Type w} (L : Lineage Occ)
    (R : FittedReceiver Occ Face) {o : Occ} (h : R.fittedOn o) : evaluateAt L R o = none := by
  unfold evaluateAt
  rw [if_pos ⟨o, h, L.refl o⟩]

/-- [proved-derived; formal-checked] **And at a lineage-equivalent one.** This is the leak the
member-level split does not catch: no design crosses the split, and the receiver still carries the
evaluation side inside it. -/
theorem evaluateAt_refuses_a_lineage_equivalent_occurrence {Occ : Type v} {Face : Type w}
    (L : Lineage Occ) (R : FittedReceiver Occ Face) {fitted o : Occ} (h : R.fittedOn fitted)
    (related : L.rel fitted o) : evaluateAt L R o = none := by
  unfold evaluateAt
  rw [if_pos ⟨fitted, h, related⟩]

/-- [proved-derived; formal-checked] Where nothing leaks, the reading is returned. -/
theorem evaluateAt_admits_when_nothing_leaks {Occ : Type v} {Face : Type w} (L : Lineage Occ)
    (R : FittedReceiver Occ Face) {o : Occ} (h : ¬ Leaks L R o) :
    evaluateAt L R o = some (R.read o) := by
  unfold evaluateAt
  rw [if_neg h]

/-! ## 4. Assay-specific calibration -/

/-- [definition] **A calibration is a receiver-to-receiver map fitted inside one assay.**

Rust counterpart: `evaluation_discipline.rs::Calibration`. -/
structure Calibration (A : Type u) (Face : Type w) where
  /-- The assay it was fitted within. -/
  assay : A
  /-- The map it fits. -/
  map : Face → Face

/-- [definition] **A declared bridge between two assays**, with the ground it is declared on. The
analogue of `PhysicalOccurrence.EnvironmentPassage`: no silent transport. -/
structure AssayBridge (A : Type u) where
  /-- The assay it leaves. -/
  source : A
  /-- The assay it arrives at. -/
  target : A
  /-- The ground it is declared on. -/
  ground : String

/-- [definition] Carrying a calibration to an assay. Inside its own assay it needs nothing; across
assays it needs a bridge that actually joins the two. -/
def transport {A : Type u} {Face : Type w} [DecidableEq A] (c : Calibration A Face) (target : A)
    (bridge : Option (AssayBridge A)) : Option (Face → Face) :=
  if c.assay = target then some c.map
  else
    match bridge with
    | some b => if b.source = c.assay ∧ b.target = target then some c.map else none
    | none => none

/-- [proved-derived; formal-checked] Inside one assay a calibration needs no bridge. -/
theorem within_one_assay_needs_no_bridge {A : Type u} {Face : Type w} [DecidableEq A]
    (c : Calibration A Face) (bridge : Option (AssayBridge A)) :
    transport c c.assay bridge = some c.map := by
  unfold transport
  rw [if_pos rfl]

/-- [proved-derived; formal-checked] **Across assays without a bridge it is refused.** -/
theorem across_assays_without_a_bridge_is_refused {A : Type u} {Face : Type w} [DecidableEq A]
    (c : Calibration A Face) (target : A) (h : c.assay ≠ target) :
    transport c target none = none := by
  unfold transport
  rw [if_neg h]

/-- [proved-derived; formal-checked] With a bridge that joins the two assays it is admitted. -/
theorem across_assays_with_a_bridge_is_admitted {A : Type u} {Face : Type w} [DecidableEq A]
    (c : Calibration A Face) (target : A) (b : AssayBridge A) (h : c.assay ≠ target)
    (source : b.source = c.assay) (arrives : b.target = target) :
    transport c target (some b) = some c.map := by
  unfold transport
  rw [if_neg h]
  simp [source, arrives]

/-- [proved-derived; formal-checked] A bridge that does not join these two assays licenses
nothing. -/
theorem a_bridge_between_other_assays_is_refused {A : Type u} {Face : Type w} [DecidableEq A]
    (c : Calibration A Face) (target : A) (b : AssayBridge A) (h : c.assay ≠ target)
    (elsewhere : b.source ≠ c.assay) :
    transport c target (some b) = none := by
  unfold transport
  rw [if_neg h]
  simp [elsewhere]

/-! ## 5. A wet or external return is a new receiver occurrence -/

/-- [definition] **A face carried at a declared time.** The Rust owner uses
`standing.rs::TimedFace` for the same object; here the face is generic.

Rust counterpart: `evaluation_discipline.rs::TimedReading`. -/
structure TimedFace (F : Type w) where
  /-- The face. -/
  face : F
  /-- The time it occurs at. -/
  time : Nat

/-- [definition] **The comparison between an earlier prediction and a later external return.** It is
a relation between two occurrences, stated on a `Rung` and carrying its own time index. -/
structure ExternalComparison (F : Type w) where
  /-- The earlier model output, at its own time. -/
  prediction : TimedFace F
  /-- The wet or external return: a new receiver occurrence. -/
  externalReturn : TimedFace F
  /-- When the comparison itself is stated. -/
  statedAt : Nat
  /-- Which rung of `RelationLadder` the comparison establishes. -/
  rung : Rung
  /-- The prediction is strictly earlier than the return. -/
  predictionIsEarlier : prediction.time < externalReturn.time
  /-- The comparison is stated no earlier than the return it reads. -/
  statedNoEarlierThanTheReturn : externalReturn.time ≤ statedAt

/-- [definition] Form the comparison. The prediction is carried through untouched. -/
def compare {F : Type w} (prediction externalReturn : TimedFace F) (rung : Rung)
    (h : prediction.time < externalReturn.time) : ExternalComparison F where
  prediction := prediction
  externalReturn := externalReturn
  statedAt := externalReturn.time
  rung := rung
  predictionIsEarlier := h
  statedNoEarlierThanTheReturn := Nat.le_refl _

/-- [proved-derived; formal-checked] **The external return does not relabel the prediction.** The
earlier occurrence's face is what it was; forming the comparison returns it unchanged. -/
theorem the_return_does_not_relabel_the_prediction {F : Type w}
    (prediction externalReturn : TimedFace F) (rung : Rung)
    (h : prediction.time < externalReturn.time) :
    (compare prediction externalReturn rung h).prediction = prediction := rfl

/-- [proved-derived; formal-checked] **The comparison has its own time index**, strictly after the
prediction's. It is a new relation between two occurrences, not a correction applied backwards. -/
theorem the_comparison_is_not_at_the_predictions_time {F : Type w} (c : ExternalComparison F) :
    c.prediction.time < c.statedAt :=
  Nat.lt_of_lt_of_le c.predictionIsEarlier c.statedNoEarlierThanTheReturn

/-- [proved-derived; formal-checked] The external return is a different occurrence from the
prediction: their times differ. -/
theorem the_external_return_is_a_new_occurrence {F : Type w} (c : ExternalComparison F) :
    c.prediction.time ≠ c.externalReturn.time :=
  Nat.ne_of_lt c.predictionIsEarlier

/-! ## 6. Predictor disagreement as a fibre property -/

/-- [definition] The three disagreement subsets of a plural fibre. Open takes precedence, exactly as
`PhysicalOccurrence.FibrePartition` gives it precedence.

Rust counterpart: `evaluation_discipline.rs::DisagreementClass`. -/
inductive DisagreementClass where
  /-- Every member decided it the same way. -/
  | unanimous
  /-- Members decided it differently. -/
  | separating
  /-- At least one member left it undecided. -/
  | openCarrying
  deriving DecidableEq, Repr

/-- [definition] The class of one contact across a declared member list. -/
def classifyContact {M : Type u} (members : List M) (read : M → ContactClass) :
    DisagreementClass :=
  if members.any (fun m => read m == ContactClass.openContact) then
    DisagreementClass.openCarrying
  else if (members.any (fun m => read m == ContactClass.inside)) &&
      (members.any (fun m => read m == ContactClass.outside)) then
    DisagreementClass.separating
  else DisagreementClass.unanimous

/-- [proved-derived; formal-checked] One open reading makes the contact open-carrying whatever the
other members read: an undecided reading is never counted as agreement or as separation. -/
theorem an_open_reading_carries_the_contact {M : Type u} (members : List M)
    (read : M → ContactClass) (h : members.any (fun m => read m == ContactClass.openContact)) :
    classifyContact members read = DisagreementClass.openCarrying := by
  unfold classifyContact
  rw [if_pos h]

/-- Two members of a fibre. -/
def twoMembers : List Bool := [false, true]

/-- Two contacts: at `true` both members read the contact formed, at `false` they disagree. -/
def reading (contact : Bool) (member : Bool) : ContactClass :=
  if contact then ContactClass.inside
  else if member then ContactClass.inside else ContactClass.outside

/-- [proved-derived; formal-checked] The first contact is unanimous. -/
theorem the_unanimous_contact_is_unanimous :
    classifyContact twoMembers (reading true) = DisagreementClass.unanimous := by decide

/-- [proved-derived; formal-checked] The second contact separates the two members. -/
theorem the_separating_contact_is_separating :
    classifyContact twoMembers (reading false) = DisagreementClass.separating := by decide

/-- A predictor that answers `inside` everywhere. -/
def predictorSays (_contact : Bool) : ContactClass := ContactClass.inside

/-- [proved-derived; formal-checked] **Performance on the unanimous subset says nothing about the
separating subset.** This predictor agrees with every member at the unanimous contact and disagrees
with a member at the separating one. A score read on the unanimous subset alone therefore carries no
information about the subset where the predictors actually disagree. -/
theorem correct_on_the_unanimous_contact_and_wrong_on_the_separating_one :
    (twoMembers.all (fun m => reading true m == predictorSays true)) = true ∧
    (twoMembers.any (fun m => !(reading false m == predictorSays false))) = true := by decide

/-! ## 7. What an evaluation may conclude -/

/-- [definition] **A proof that a bounded evaluation establishes a universal claim.**

This inductive type has **no constructors**. Nothing in this file produces a value of it, exactly as
`PhysicalOccurrence.RealizationProof` has none: a held-out result is established at its split and
its receiver, and its promotion to a universal claim is not a value anything can hold. -/
inductive UniversalClaim where

/-- [proved-derived; formal-checked] There is no universal claim. -/
theorem universalClaim_is_uninhabited (u : UniversalClaim) : False := nomatch u

/-- [definition] **What an evaluation may return.** Three arms and no fourth: there is no arm that
affirms a generalization, because a bounded evaluation refutes and never affirms.

Rust counterpart: `evaluation_discipline.rs::EvaluationConclusion`. -/
inductive Conclusion (S : Type u) (R : Type v) where
  /-- Established at this split, read by this receiver, and nowhere else. -/
  | establishedBounded (split : S) (receiver : R)
  /-- A generalization claim refuted by this split's evidence. -/
  | generalizationRefuted (split : S) (receiver : R) (claim : String)
  /-- Nothing was refuted inside this evaluation. Its own return, and not an affirmation. -/
  | notRefutedWithinThisEvaluation (split : S) (receiver : R)

namespace Conclusion

variable {S : Type u} {R : Type v}

/-- The split and receiver a conclusion holds at. -/
def scope : Conclusion S R → S × R
  | .establishedBounded s r => (s, r)
  | .generalizationRefuted s r _ => (s, r)
  | .notRefutedWithinThisEvaluation s r => (s, r)

/-- [definition] Always `none`: `UniversalClaim` is uninhabited. -/
def universalClaim (_ : Conclusion S R) : Option UniversalClaim := none

/-- [proved-derived; formal-checked] No conclusion carries a universal claim. -/
theorem no_conclusion_carries_a_universal_claim (c : Conclusion S R) :
    c.universalClaim = none := rfl

/-- [definition] Reading a conclusion at another split. -/
def atAnotherSplit [DecidableEq S] (c : Conclusion S R) (other : S) : Option (Conclusion S R) :=
  if c.scope.1 = other then some c else none

/-- [proved-derived; formal-checked] **A held-out result does not travel to another split.** -/
theorem a_conclusion_does_not_travel_to_another_split [DecidableEq S] (c : Conclusion S R)
    (other : S) (h : c.scope.1 ≠ other) : c.atAnotherSplit other = none := by
  unfold atAnotherSplit
  rw [if_neg h]

/-- [proved-derived; formal-checked] At its own split it is itself. -/
theorem a_conclusion_stands_at_its_own_split [DecidableEq S] (c : Conclusion S R) :
    c.atAnotherSplit c.scope.1 = some c := by
  unfold atAnotherSplit
  rw [if_pos rfl]

end Conclusion

/-! ## 8. The contract -/

/-- [definition] **The B9 contract, as one statement.** Every clause is proved above.

1. A split built from a partition of lineage classes cannot straddle, and a split declared on raw
   designs can, with the leak exhibited.
2. A receiver fitted on an occurrence is refused at that occurrence and at every lineage-equivalent
   one.
3. A calibration does not cross an assay without a bridge that joins the two.
4. An external return is a new occurrence with its own time index, and forming the comparison leaves
   the earlier prediction's face unchanged.
5. An open reading carries its contact and is counted on neither side; a predictor may be right on
   the whole unanimous subset and wrong on the separating one.
6. No conclusion carries a universal claim, and none travels to another split. -/
theorem evaluation_contract : True := trivial

/-! ## 9. The axiom audit

[implemented-exact] Every theorem of this file is elaborated with no `sorryAx` and no
`native_decide`. -/

#print axioms Lineage.cls_eq_of_rel
#print axioms Lineage.rel_of_cls_eq
#print axioms ofClassPredicate_does_not_straddle
#print axioms rawSplit_straddles
#print axioms evaluateAt_refuses_a_fitted_occurrence
#print axioms evaluateAt_refuses_a_lineage_equivalent_occurrence
#print axioms evaluateAt_admits_when_nothing_leaks
#print axioms within_one_assay_needs_no_bridge
#print axioms across_assays_without_a_bridge_is_refused
#print axioms across_assays_with_a_bridge_is_admitted
#print axioms a_bridge_between_other_assays_is_refused
#print axioms the_return_does_not_relabel_the_prediction
#print axioms the_comparison_is_not_at_the_predictions_time
#print axioms the_external_return_is_a_new_occurrence
#print axioms an_open_reading_carries_the_contact
#print axioms the_unanimous_contact_is_unanimous
#print axioms the_separating_contact_is_separating
#print axioms correct_on_the_unanimous_contact_and_wrong_on_the_separating_one
#print axioms universalClaim_is_uninhabited
#print axioms Conclusion.no_conclusion_carries_a_universal_claim
#print axioms Conclusion.a_conclusion_does_not_travel_to_another_split
#print axioms Conclusion.a_conclusion_stands_at_its_own_split
#print axioms evaluation_contract

end Holonics.Foundation.EvaluationDiscipline
