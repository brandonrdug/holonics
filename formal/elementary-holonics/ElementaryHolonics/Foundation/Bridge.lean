import ElementaryHolonics.Foundation.GrainRestriction

/-!
# Typed bridges: eight statuses, one grade, and a composition that takes the meet

[definition] This file deposits item **C7** of
`docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md`: `Bridge`, `ProposedBridge` and the
eight statuses that must not share one word — co-presence, numerical resemblance, a shared receiver
face, an actual map, a structure-preserving map, an equivalence, a natural family and a speculative
analogy.

AGENTS.md: "Co-presence is not contact. Contact has a declared interaction; equal receiver output is
not source equality." "Everything is connectable" is true only as a typed discipline in which the
**kind** of connection is data and the weakest kinds carry no map.

## The strength order, and where there is none

[proved-derived] `BridgeStatus.entails` is a genuine partial order (`entails_refl`, `entails_trans`,
`entails_antisymm`), and it is **not** total. `sharedReceiverFace` and `actualMap` are incomparable;
`equivalence` and `naturalFamily` are incomparable above `structurePreservingMap`; and
`speculativeAnalogy` is off the order entirely — it entails nothing and nothing entails it, which is
why `statusMeet` refuses to compose it. Each non-implication below carries a real witness, not only
a `decide` over the declared order.

## The grade is the canon's, and the canon declares no order

[project-postulate] `docs/canon/EPISTEMIC_GRADES.md` gives eleven truth-status grades and **no
ordering among them**. So `composeGrade` does not rank them: it reads each grade's declared
`SupportLevel` — how much a composite may inherit from a link carrying that grade — and returns the
weaker one, refusing `counterexample` and `historical`, which are dispositions rather than support.
The reading is declared here and named as a declared reading wherever it is used.

## Rust counterpart

[definition] The paired executable owner is `crates/holonic-engine/src/bridge.rs`, with the same
names — `EpistemicGrade`, `SupportLevel`, `BridgeStatus`, `Bridge`, `ProposedBridge`,
`BridgeComposition`, `Promotion` — and every theorem below mirrored as a test.
-/

namespace Soma.Holonics.Foundation.Bridges

open Soma.Holonics
open Soma.Holonics.Foundation.ContinuingTower
open Soma.Holonics.Foundation.GrainRestriction
open Soma.Holonics.Foundation.AperturedGradedComplex

universe u w

/-! ## C7 (a) — the epistemic grade, exactly one per bridge -/

/-- [definition] The eleven truth-status grades of `docs/canon/EPISTEMIC_GRADES.md`. A bridge
carries exactly one. `open` is a Lean keyword, so the grade the canon writes `open` is
`openObligation` here.

Rust counterpart: `crates/holonic-engine/src/bridge.rs::EpistemicGrade`. -/
inductive EpistemicGrade
  /-- A declared term or construction. -/
  | definition
  /-- A governing discipline adopted by this project. -/
  | projectPostulate
  /-- A standard external theorem in its ordinary scope. -/
  | provedStandard
  /-- A theorem derived in the project. -/
  | provedDerived
  /-- A factual capability established for a declared construction or receiver family. -/
  | establishedBounded
  /-- A conclusion under named hypotheses. -/
  | conditional
  /-- A proposed structure-preserving correspondence and active theorem-finding program. -/
  | interpretation
  /-- A precise unproved claim. -/
  | conjecture
  /-- A construction refuting a stated stronger claim. -/
  | counterexample
  /-- A named unresolved fibre or missing capability (the canon's `open`). -/
  | openObligation
  /-- Preserved provenance that does not govern current construction. -/
  | historical
  deriving DecidableEq, Repr

/-- [definition] The complete enumeration of the eleven grades, so that every law about them below
is decided by the kernel over all cases. -/
instance : Fintype EpistemicGrade where
  elems := {.definition, .projectPostulate, .provedStandard, .provedDerived, .establishedBounded,
    .conditional, .interpretation, .conjecture, .counterexample, .openObligation, .historical}
  complete := by intro x; cases x <;> decide

/-- [definition] How much a composite bridge may inherit from a link carrying a given grade. This
is a **declared reading** of the grade and not an ordering of the canon's grades, which declares
none.

Rust counterpart: `bridge.rs::SupportLevel`. -/
inductive SupportLevel
  /-- The link supports nothing downstream. -/
  | unsupported
  /-- The link supports a conclusion under its own named hypotheses. -/
  | hypothetical
  /-- The link supports a conclusion inside a declared construction or receiver family. -/
  | bounded
  /-- The link supports a conclusion outright. -/
  | proved
  deriving DecidableEq, Repr

/-- [definition] The complete enumeration of the four support levels. -/
instance : Fintype SupportLevel where
  elems := {.unsupported, .hypothetical, .bounded, .proved}
  complete := by intro x; cases x <;> decide

/-- [definition] The support order, as a rank. -/
def SupportLevel.rank : SupportLevel → ℕ
  | .unsupported => 0
  | .hypothetical => 1
  | .bounded => 2
  | .proved => 3

/-- [definition] The grade a composite carries when two links of the same support level, but
different grades, meet. -/
def SupportLevel.representative : SupportLevel → EpistemicGrade
  | .unsupported => .openObligation
  | .hypothetical => .conditional
  | .bounded => .establishedBounded
  | .proved => .provedDerived

/-- [definition] The declared support reading of each grade. `counterexample` and `historical` have
**none**: a refutation is not a link, and preserved provenance does not govern construction, so a
composite through either is refused rather than graded. -/
def EpistemicGrade.support : EpistemicGrade → Option SupportLevel
  | .definition => some .bounded
  | .projectPostulate => some .bounded
  | .provedStandard => some .proved
  | .provedDerived => some .proved
  | .establishedBounded => some .bounded
  | .conditional => some .hypothetical
  | .interpretation => some .hypothetical
  | .conjecture => some .unsupported
  | .openObligation => some .unsupported
  | .counterexample => none
  | .historical => none

/-- [definition] Compose two grades: the weaker support wins, ties on the same level are
canonicalized to that level's representative, and a link with no support reading refuses.

Rust counterpart: `bridge.rs::compose_grade`. -/
def composeGrade (a b : EpistemicGrade) : Option EpistemicGrade :=
  match a.support, b.support with
  | some sa, some sb =>
      if sa.rank < sb.rank then some a
      else if sb.rank < sa.rank then some b
      else if a = b then some a
      else some sa.representative
  | _, _ => none

/-- [proved-derived; formal-checked] Grade composition is symmetric. -/
theorem composeGrade_comm (a b : EpistemicGrade) : composeGrade a b = composeGrade b a := by
  revert a b; decide

/-- [proved-derived; formal-checked] Grade composition is idempotent. -/
theorem composeGrade_self (a : EpistemicGrade) :
    composeGrade a a = if a.support.isSome then some a else none := by
  revert a; decide

/-- [proved-derived; formal-checked] Grade composition is associative through the refusal. -/
theorem composeGrade_assoc (a b c : EpistemicGrade) :
    (composeGrade a b).bind (fun ab => composeGrade ab c) =
      (composeGrade b c).bind (fun bc => composeGrade a bc) := by
  revert a b c; decide

/-- [proved-derived; formal-checked] The composite never claims more support than either link. -/
theorem composeGrade_support_le (a b g : EpistemicGrade) (h : composeGrade a b = some g) :
    ∃ sg sa sb, g.support = some sg ∧ a.support = some sa ∧ b.support = some sb ∧
      sg.rank ≤ sa.rank ∧ sg.rank ≤ sb.rank := by
  revert h; revert a b g; decide

/-- [counterexample; formal-checked] A `counterexample` link composes with nothing: it is a
refutation, not a passage. -/
theorem counterexample_does_not_compose (b : EpistemicGrade) :
    composeGrade .counterexample b = none := by
  revert b; decide

/-- [counterexample; formal-checked] And neither does a `historical` link. -/
theorem historical_does_not_compose (b : EpistemicGrade) :
    composeGrade .historical b = none := by
  revert b; decide

/-! ## C7 (b) — the eight statuses and their genuine strength order -/

/-- [definition] The eight distinct statuses a connection claim can carry. They must not share one
word: `docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md` C7.

Rust counterpart: `crates/holonic-engine/src/bridge.rs::BridgeStatus`. -/
inductive BridgeStatus
  /-- One aperture in which both occur. Owes no map and no equality. -/
  | coPresence
  /-- Two receivers into a common numeric face, with a tolerance and the aperture. -/
  | numericalResemblance
  /-- One receiver `ρ` with `ρ a = ρ b`. Owes no source identity. -/
  | sharedReceiverFace
  /-- An actual map with its domain and its residual. Owes no preservation. -/
  | actualMap
  /-- A map together with the diagram it preserves. Owes no invertibility. -/
  | structurePreservingMap
  /-- An equivalence with its natural squares. Owes no naturality in a parameter. -/
  | equivalence
  /-- An indexed family of maps commuting with restriction. Owes no exhaustiveness. -/
  | naturalFamily
  /-- A candidate with required hypotheses, supporting receivers and counterexamples. -/
  | speculativeAnalogy
  deriving DecidableEq, Repr

/-- [definition] The complete enumeration of the eight statuses. -/
instance : Fintype BridgeStatus where
  elems := {.coPresence, .numericalResemblance, .sharedReceiverFace, .actualMap,
    .structurePreservingMap, .equivalence, .naturalFamily, .speculativeAnalogy}
  complete := by intro x; cases x <;> decide

/-- [definition] Everything a status entails, itself included. -/
def BridgeStatus.entailed : BridgeStatus → List BridgeStatus
  | .coPresence => [.coPresence]
  | .numericalResemblance => [.numericalResemblance, .coPresence]
  | .sharedReceiverFace => [.sharedReceiverFace, .coPresence]
  | .actualMap => [.actualMap, .coPresence]
  | .structurePreservingMap => [.structurePreservingMap, .actualMap, .coPresence]
  | .equivalence => [.equivalence, .structurePreservingMap, .actualMap, .coPresence]
  | .naturalFamily => [.naturalFamily, .structurePreservingMap, .actualMap, .coPresence]
  | .speculativeAnalogy => [.speculativeAnalogy]

/-- [definition] `a.entails b` when every claim of status `a` is also a claim of status `b`.

Rust counterpart: `bridge.rs::BridgeStatus::entails`. -/
def BridgeStatus.entails (a b : BridgeStatus) : Bool := a.entailed.contains b

/-- [proved-derived; formal-checked] The order is reflexive. -/
theorem entails_refl (a : BridgeStatus) : a.entails a = true := by revert a; decide

/-- [proved-derived; formal-checked] The order is transitive. -/
theorem entails_trans (a b c : BridgeStatus) (hab : a.entails b = true)
    (hbc : b.entails c = true) : a.entails c = true := by
  revert hab hbc; revert a b c; decide

/-- [proved-derived; formal-checked] The order is antisymmetric, so it is a genuine partial order
and the eight statuses are eight. -/
theorem entails_antisymm (a b : BridgeStatus) (hab : a.entails b = true)
    (hba : b.entails a = true) : a = b := by
  revert hab hba; revert a b; decide

/-! ### Which implications hold -/

/-- [proved-derived; formal-checked] An equivalence is a structure-preserving map, which is an
actual map, which is co-presence. -/
theorem equivalence_entails_map :
    BridgeStatus.equivalence.entails .structurePreservingMap = true ∧
      BridgeStatus.structurePreservingMap.entails .actualMap = true ∧
      BridgeStatus.actualMap.entails .coPresence = true := by decide

/-- [proved-derived; formal-checked] A natural family is a structure-preserving map. -/
theorem naturalFamily_entails_structurePreserving :
    BridgeStatus.naturalFamily.entails .structurePreservingMap = true := by decide

/-- [proved-derived; formal-checked] A shared receiver face is co-presence: one receiver read both.
-/
theorem sharedReceiverFace_entails_coPresence :
    BridgeStatus.sharedReceiverFace.entails .coPresence = true := by decide

/-! ### Which do not, with witnesses

The `decide` proofs below state that the *declared* order omits the implication. Each is paired
with a construction that shows the omission is forced. -/

/-- [counterexample; formal-checked] **A shared receiver face does not yield an actual map.** -/
theorem sharedReceiverFace_not_actualMap :
    BridgeStatus.sharedReceiverFace.entails .actualMap = false := by decide

/-- [counterexample; formal-checked] The witness: the blind receiver on `Bool` identifies `false`
and `true`, which the faithful receiver separates, so **no** map from the shared face to the
faithful reading exists. This is `Foundation/Receiver.lean`'s
`ReceiverTransformer.excludesInsufficiency`, cited rather than rebuilt. -/
def sharedFaceInsufficiency :
    ReceiverInsufficiency (fun _ : Bool => PUnit.unit) (fun x : Bool => x) where
  left := false
  right := true
  sameEntering := rfl
  differentReturned := by decide

/-- [counterexample; formal-checked] Hence the shared face supplies no map at all. -/
theorem sharedReceiverFace_supplies_no_map :
    IsEmpty (ReceiverTransformer (fun _ : Bool => PUnit.unit) (fun x : Bool => x)) :=
  ⟨fun t => t.excludesInsufficiency sharedFaceInsufficiency⟩

/-- [counterexample; formal-checked] **An actual map need not preserve structure.** -/
theorem actualMap_not_structurePreserving :
    BridgeStatus.actualMap.entails .structurePreservingMap = false := by decide

/-- [counterexample; formal-checked] The witness is
`Foundation/ContinuingTower.lean::naturality_is_genuine_content`: two perfectly good injective face
maps, each a lawful `Transition` with zero residual, whose square with the tower's own restriction
does not commute. Being a map is not preserving a diagram. -/
theorem actualMap_does_not_preserve_structure :
    ∃ (g₀ g₁ : ℕ → ℕ) (x : ℕ), Function.Injective g₀ ∧ Function.Injective g₁ ∧
      shiftTower.restrict (Nat.zero_le 1) (g₁ x)
        ≠ g₀ (shiftTower.restrict (Nat.zero_le 1) x) :=
  naturality_is_genuine_content

/-- [counterexample; formal-checked] **An equivalence of objects does not give a natural family.**
-/
theorem equivalence_not_naturalFamily :
    BridgeStatus.equivalence.entails .naturalFamily = false := by decide

/-- [counterexample; formal-checked] The witness: `x ↦ x + 1` is an equivalence of `ℤ` with itself,
and its square with the doubling restriction does not commute. Componentwise equivalence says
nothing about naturality in the parameter. -/
theorem equivalence_does_not_give_a_natural_family :
    ∃ (e : ℤ ≃ ℤ) (r : ℤ → ℤ) (x : ℤ), r (e x) ≠ e (r x) := by
  refine ⟨Equiv.addRight 1, fun x => 2 * x, 0, ?_⟩
  show (2 : ℤ) * (0 + 1) ≠ 2 * 0 + 1
  decide

/-- [counterexample; formal-checked] **Numerical resemblance does not give a shared receiver
face.** -/
theorem numericalResemblance_not_sharedReceiverFace :
    BridgeStatus.numericalResemblance.entails .sharedReceiverFace = false := by decide

/-- [counterexample; formal-checked] The witness, in exact integers: `3` and `4` resemble each other
within tolerance `1`, and the identity receiver separates them. A tolerance is an aperture, never an
identification. -/
theorem numericalResemblance_does_not_identify :
    |(3 : ℤ) - 4| ≤ 1 ∧ (3 : ℤ) ≠ 4 := by decide

/-- [counterexample; formal-checked] **Co-presence gives nothing.** It does not even give a
numerical resemblance: two occurrences in one aperture need not have a common numeric face. -/
theorem coPresence_gives_nothing :
    BridgeStatus.coPresence.entails .numericalResemblance = false ∧
      BridgeStatus.coPresence.entails .sharedReceiverFace = false ∧
      BridgeStatus.coPresence.entails .actualMap = false := by decide

/-- [counterexample; formal-checked] **A speculative analogy is off the order entirely.** It entails
nothing but itself, and nothing else entails it: it is a candidate, not a weak connection. -/
theorem speculativeAnalogy_is_off_the_order :
    (∀ b : BridgeStatus, b ≠ BridgeStatus.speculativeAnalogy →
        BridgeStatus.speculativeAnalogy.entails b = false) ∧
      (∀ a : BridgeStatus, a ≠ BridgeStatus.speculativeAnalogy →
        a.entails BridgeStatus.speculativeAnalogy = false) := by
  decide

/-! ### The meet -/

/-- [definition] The greatest common lower bound of two statuses, when there is one. A speculative
analogy has no lower bound in common with anything else, so composing through it is refused.

Rust counterpart: `bridge.rs::status_meet`. -/
def statusMeet : BridgeStatus → BridgeStatus → Option BridgeStatus
  | .speculativeAnalogy, .speculativeAnalogy => some .speculativeAnalogy
  | .speculativeAnalogy, _ => none
  | _, .speculativeAnalogy => none
  | .equivalence, .naturalFamily => some .structurePreservingMap
  | .naturalFamily, .equivalence => some .structurePreservingMap
  | a, b =>
    if a.entails b then some b
    else if b.entails a then some a
    else some .coPresence

/-- [proved-derived; formal-checked] The meet is symmetric. -/
theorem statusMeet_comm (a b : BridgeStatus) : statusMeet a b = statusMeet b a := by
  revert a b; decide

/-- [proved-derived; formal-checked] The meet is a lower bound of both. -/
theorem statusMeet_lower (a b m : BridgeStatus) (h : statusMeet a b = some m) :
    a.entails m = true ∧ b.entails m = true := by
  revert h; revert a b m; decide

/-- [proved-derived; formal-checked] And it is the greatest one. -/
theorem statusMeet_greatest (a b m c : BridgeStatus) (h : statusMeet a b = some m)
    (ha : a.entails c = true) (hb : b.entails c = true) : m.entails c = true := by
  revert h ha hb; revert a b m c; decide

/-- [proved-derived; formal-checked] The two incomparable pairs the brief names, decided: a shared
receiver face and an actual map meet at bare co-presence, and an equivalence and a natural family
meet at a structure-preserving map. -/
theorem statusMeet_of_the_incomparable_pairs :
    statusMeet .sharedReceiverFace .actualMap = some .coPresence ∧
      statusMeet .equivalence .naturalFamily = some .structurePreservingMap := by decide

/-! ## C7 (c) — the `Bridge` -/

/-- [definition] A **bridge**: what kind of connection is claimed, the passage that carries it (a
`Foundation/ContinuingTower.lean::Transition`, so a map arrives with the residual it does not
transport), the diagram claimed preserved, and exactly one epistemic grade.

`passage_of_map` is what makes the status a *typed* claim rather than a word: a status at or above
`actualMap` cannot be declared without supplying the passage.

The domain of a partially defined bridge is carried by its source *type*, exactly as
`Foundation/Receiver.lean`'s `ReceiverTransformer` carries `Set.range entering` — a bridge out of a
restricted domain is a bridge out of that subtype.

Rust counterpart: `crates/holonic-engine/src/bridge.rs::Bridge`. -/
structure Bridge (A B : Type u) where
  /-- Which of the eight is claimed. -/
  status : BridgeStatus
  /-- The passage, with its residual. `none` for the statuses that carry no map. -/
  passage : Option (Transition.{u, u, w} A B)
  /-- The structure claimed preserved. -/
  Preserved : Type w
  /-- What preservation means for it. -/
  preserves : Preserved → Prop
  /-- Exactly one grade from `docs/canon/EPISTEMIC_GRADES.md`. -/
  grade : EpistemicGrade
  /-- A status at or above `actualMap` must supply the passage. -/
  passage_of_map : status.entails .actualMap = true → passage.isSome = true

/-- [definition] The passage a composite carries: the two passages composed, with their residuals
paired by `Transition.comp_residual`.

Rust counterpart: `bridge.rs::composed_passage`. -/
def composedPassage {A B C : Type u} (second : Bridge.{u, w} B C) (first : Bridge.{u, w} A B) :
    Option (Transition.{u, u, w} A C) :=
  first.passage.bind fun f => second.passage.map fun t => Transition.comp t f

/-- [proved-derived; formal-checked] When both passages are present, the composite passage is
exactly `Transition.comp`, so **the composite's residual is the pair of component residuals**
(`Transition.comp_residual`). -/
theorem composedPassage_of_both {A B C : Type u} (second : Bridge.{u, w} B C)
    (first : Bridge.{u, w} A B) {f : Transition.{u, u, w} A B} {t : Transition.{u, u, w} B C}
    (hf : first.passage = some f) (ht : second.passage = some t) :
    composedPassage second first = some (Transition.comp t f) := by
  simp [composedPassage, hf, ht]

/-- [definition] The lawful returns of an attempted composition. A refusal is returned as content
and never raised.

Rust counterpart: `bridge.rs::BridgeComposition`. -/
inductive BridgeComposition (A C : Type u)
  /-- The composite bridge. -/
  | composed (bridge : Bridge.{u, w} A C)
  /-- The two statuses have no common lower bound — a speculative analogy is involved. -/
  | statusIncomparable (left right : BridgeStatus)
  /-- One grade is a disposition rather than a support: `counterexample` or `historical`. -/
  | gradeIncomparable (left right : EpistemicGrade)
  /-- The meet claims a map and no passage was supplied. -/
  | passageMissing (claimed : BridgeStatus)

/-- [definition] The composite at a decided status and grade. -/
def composedBridge {A B C : Type u} (s : BridgeStatus) (g : EpistemicGrade)
    (second : Bridge.{u, w} B C) (first : Bridge.{u, w} A B) : BridgeComposition.{u, w} A C :=
  if hs : s.entails BridgeStatus.actualMap = true then
    match composedPassage second first with
    | some t =>
      .composed
        { status := s
          passage := some t
          Preserved := second.Preserved × first.Preserved
          preserves := fun p => second.preserves p.1 ∧ first.preserves p.2
          grade := g
          passage_of_map := fun _ => rfl }
    | none => .passageMissing s
  else
    .composed
      { status := s
        passage := composedPassage second first
        Preserved := second.Preserved × first.Preserved
        preserves := fun p => second.preserves p.1 ∧ first.preserves p.2
        grade := g
        passage_of_map := fun hm => absurd hm hs }

/-- [definition] **Composition of bridges takes the meet of status and grade, and composes
residuals through `Transition`.**

Rust counterpart: `bridge.rs::Bridge::compose`. -/
def Bridge.comp {A B C : Type u} (second : Bridge.{u, w} B C) (first : Bridge.{u, w} A B) :
    BridgeComposition.{u, w} A C :=
  match statusMeet first.status second.status with
  | none => .statusIncomparable first.status second.status
  | some s =>
    match composeGrade first.grade second.grade with
    | none => .gradeIncomparable first.grade second.grade
    | some g => composedBridge s g second first

/-- [proved-derived; formal-checked] Composition is built at exactly the meet of the two statuses
and the composition of the two grades. -/
theorem comp_at_meet {A B C : Type u} (second : Bridge.{u, w} B C) (first : Bridge.{u, w} A B)
    {s : BridgeStatus} {g : EpistemicGrade}
    (hs : statusMeet first.status second.status = some s)
    (hg : composeGrade first.grade second.grade = some g) :
    Bridge.comp second first = composedBridge s g second first := by
  simp [Bridge.comp, hs, hg]

/-- [proved-derived; formal-checked] The composite's status is that meet and its grade is that
composition. -/
theorem composedBridge_status_grade {A B C : Type u} (s : BridgeStatus) (g : EpistemicGrade)
    (second : Bridge.{u, w} B C) (first : Bridge.{u, w} A B) {b : Bridge.{u, w} A C}
    (h : composedBridge s g second first = .composed b) : b.status = s ∧ b.grade = g := by
  unfold composedBridge at h
  split at h
  · split at h
    · injection h with h'; subst h'; exact ⟨rfl, rfl⟩
    · simp at h
  · injection h with h'; subst h'; exact ⟨rfl, rfl⟩

/-- [proved-derived; formal-checked] **A composite never claims a map it does not carry.** This is
not checked: it is the `passage_of_map` field, so it holds by type for every bridge that exists at
all. -/
theorem comp_respects_map_claim {A C : Type u} (b : Bridge.{u, w} A C)
    (h : b.status.entails .actualMap = true) : b.passage.isSome = true :=
  b.passage_of_map h

/-- [counterexample; formal-checked] And when the meet does claim a map and no passage was supplied,
composition returns `passageMissing` rather than a bridge. -/
theorem composedBridge_refuses_missing_passage {A B C : Type u} (s : BridgeStatus)
    (g : EpistemicGrade) (second : Bridge.{u, w} B C) (first : Bridge.{u, w} A B)
    (hp : composedPassage second first = none) (hs : s.entails .actualMap = true) :
    composedBridge s g second first = .passageMissing s := by
  unfold composedBridge
  rw [dif_pos hs, hp]

/-! ## C7 (d) — `ProposedBridge` and promotion -/

/-- [definition] A **proposed bridge**: a candidate together with what it owes. An `interpretation`
in `docs/canon/EPISTEMIC_GRADES.md` "must carry explicit maps, limits, preserved diagram, first
derivation target, and a falsifier that can fire"; those are exactly these fields.

Rust counterpart: `crates/holonic-engine/src/bridge.rs::ProposedBridge`. -/
structure ProposedBridge (A B : Type u) where
  /-- The candidate connection. -/
  candidate : Bridge.{u, w} A B
  /-- What must be discharged before it may be promoted. -/
  requiredHypotheses : List Prop
  /-- Receivers that read both sides into one face. -/
  supportingReceivers : List ((F : Type w) × ((A → F) × (B → F)))
  /-- Recorded refutations of a stronger claim. -/
  counterexamples : List (A × B)
  /-- The test that can fire. -/
  falsifier : Prop

/-- [definition] A **promotion** of a proposed bridge to a stronger status. Every required
hypothesis is discharged, no counterexample is recorded, and a target at or above `actualMap` must
already have its passage. A recorded counterexample blocks promotion **by type**: there is no
inhabitant of this structure when `counterexamples` is nonempty.

Rust counterpart: `bridge.rs::Promotion`. -/
structure Promotion {A B : Type u} (P : ProposedBridge.{u, w} A B) (target : BridgeStatus) where
  /-- Every required hypothesis holds. -/
  discharged : ∀ h ∈ P.requiredHypotheses, h
  /-- Nothing refutes it. -/
  noCounterexample : P.counterexamples = []
  /-- The target is at least as strong as the candidate's declared status. -/
  reaches : target.entails P.candidate.status = true
  /-- And a target that claims a map has one. -/
  mapSupplied : target.entails .actualMap = true → P.candidate.passage.isSome = true

/-- [definition] The promoted bridge. Only the status changes; the passage, the preserved diagram
and the grade travel unchanged. -/
def Promotion.promoted {A B : Type u} {P : ProposedBridge.{u, w} A B} {target : BridgeStatus}
    (p : Promotion P target) : Bridge.{u, w} A B where
  status := target
  passage := P.candidate.passage
  Preserved := P.candidate.Preserved
  preserves := P.candidate.preserves
  grade := P.candidate.grade
  passage_of_map := p.mapSupplied

/-- [proved-derived; formal-checked] Promotion changes the status and nothing else. -/
theorem promoted_status {A B : Type u} {P : ProposedBridge.{u, w} A B} {target : BridgeStatus}
    (p : Promotion P target) :
    p.promoted.status = target ∧ p.promoted.grade = P.candidate.grade ∧
      p.promoted.passage = P.candidate.passage :=
  ⟨rfl, rfl, rfl⟩

/-- [proved-derived; formal-checked] **A recorded counterexample blocks promotion by type.** -/
theorem counterexample_blocks_promotion {A B : Type u} (P : ProposedBridge.{u, w} A B)
    (target : BridgeStatus) (h : P.counterexamples ≠ []) : IsEmpty (Promotion P target) :=
  ⟨fun p => h p.noCounterexample⟩

/-- [proved-derived; formal-checked] **An undischarged hypothesis blocks promotion by type.** -/
theorem false_hypothesis_blocks_promotion {A B : Type u} (P : ProposedBridge.{u, w} A B)
    (target : BridgeStatus) (h : False ∈ P.requiredHypotheses) : IsEmpty (Promotion P target) :=
  ⟨fun p => p.discharged False h⟩

/-- [proved-derived; formal-checked] **A missing passage blocks promotion to a map.** -/
theorem missing_passage_blocks_promotion {A B : Type u} (P : ProposedBridge.{u, w} A B)
    (target : BridgeStatus) (hp : P.candidate.passage = none)
    (ht : target.entails .actualMap = true) : IsEmpty (Promotion P target) :=
  ⟨fun p => by
    have := p.mapSupplied ht
    rw [hp] at this
    exact absurd this (by simp)⟩

/-! ## C7 (e) — bridges that really exist in this tree -/

/-- [definition] **`rebaseMigration` is an equivalence.** `Holon.Rebase`'s face equivalence read as
a bridge: an invertible passage with subsingleton residual, preserving the receive square.

Cited owners: `Foundation/Holon.lean::Holon.Rebase`,
`Foundation/ContinuingTower.lean::rebaseMigration` and `Transition.ofEquiv`. -/
def rebaseBridge {Src Tgt Fce Src' Tgt' Fce' : Type u}
    {left : Holon.{u, u, u, u} Src Tgt Fce} {right : Holon.{u, u, u, u} Src' Tgt' Fce'}
    (R : Holon.Rebase left right) : Bridge.{u, u} Fce Fce' where
  status := .equivalence
  passage := some (Transition.ofEquiv R.faceEquiv)
  Preserved := PUnit
  preserves := fun _ => ∀ o, R.faceEquiv (left.receive o) = right.receive (R.occurrenceEquiv o)
  grade := .provedDerived
  passage_of_map := fun _ => rfl

/-- [proved-derived; formal-checked] Its preserved diagram is discharged by `Rebase`'s own
`receive_natural`, so the claim is not a promise. -/
theorem rebaseBridge_preserves {Src Tgt Fce Src' Tgt' Fce' : Type u}
    {left : Holon.{u, u, u, u} Src Tgt Fce} {right : Holon.{u, u, u, u} Src' Tgt' Fce'}
    (R : Holon.Rebase left right) : (rebaseBridge R).preserves PUnit.unit :=
  R.receive_natural

/-- [proved-derived; formal-checked] And its residual is subsingleton: an equivalence drops
nothing. -/
theorem rebaseBridge_residual_subsingleton {Src Tgt Fce Src' Tgt' Fce' : Type u}
    {left : Holon.{u, u, u, u} Src Tgt Fce} {right : Holon.{u, u, u, u} Src' Tgt' Fce'}
    (R : Holon.Rebase left right) :
    Subsingleton (Transition.ofEquiv R.faceEquiv).Residual :=
  Transition.ofEquiv_residual_subsingleton R.faceEquiv

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- [definition] **`padicHalfMigration` is a lossy structure-preserving map with a residual.** Its
chart component at level `j` transports `ZMod (p ^ (j + j))` to `ZMod (p ^ j)` and retains the digit
block it drops; the preserved diagram is the migration's naturality square.

Cited owners: `Foundation/ContinuingTower.lean::padicHalfMigration`,
`ResidualMigration.transition`, `padicHalfMigration_face_fibre_card`. -/
def padicHalfBridge (j : ℕ) :
    Bridge.{0, 0} ((padicTower p).Face ((padicHalfMigration p).index j)) ((padicTower p).Face j) where
  status := .structurePreservingMap
  passage := some ((padicHalfMigration p).transition j)
  Preserved := PUnit
  preserves := fun _ => ∀ x, ((padicHalfMigration p).transition j).reopen
    (((padicHalfMigration p).transition j).apply x)
    (((padicHalfMigration p).transition j).residual x) = x
  grade := .provedDerived
  passage_of_map := fun _ => rfl

/-- [proved-derived; formal-checked] Its preserved claim is discharged by `reopen_apply`: the
transported face together with the retained digit block returns the source exactly. -/
theorem padicHalfBridge_preserves (j : ℕ) : (padicHalfBridge p j).preserves PUnit.unit :=
  ((padicHalfMigration p).transition j).reopen_apply

/-- [counterexample; formal-checked] And it is genuinely lossy at every positive chart, so it is
**not** an equivalence: the face map merges `p ^ j` sources. -/
theorem padicHalfBridge_is_not_an_equivalence (j : ℕ) (hj : 0 < j) :
    ¬ Function.Injective ((padicHalfMigration p).transition j).apply :=
  padicHalfMigration_face_not_injective p j hj

end Padic

section Grain

variable {FineCell CoarseCell : Type u} [DecidableEq FineCell]

/-- [definition] **The grain restriction is a lossy structure-preserving map.** The alpha-carbon
selection of `Foundation/GrainRestriction.lean` read as a bridge: the coarse reading is the passage,
every fine reading the selection never looked at is the residual, and the preserved claim is the
exact round trip.

Cited owners: `GrainRestriction.selectionTransition`,
`GrainRestriction.grain_residual_reopens_the_source`, `GrainRestriction.fineReading_factors`.
Its executable counterpart is `crates/holonic-engine/src/grain_tower.rs::GrainSelection`. -/
def grainBridge (π : FineCell → CoarseCell) (sel : CoarseCell → FineCell) :
    Bridge.{u, u} (FineCell → FineCell → ContactClass) (CoarseCell → CoarseCell → ContactClass) where
  status := .structurePreservingMap
  passage := some (selectionTransition π sel)
  Preserved := PUnit
  preserves := fun _ => ∀ φ, (selectionTransition π sel).reopen
    ((selectionTransition π sel).apply φ) ((selectionTransition π sel).residual φ) = φ
  grade := .establishedBounded
  passage_of_map := fun _ => rfl

/-- [proved-derived; formal-checked] Its preserved claim is discharged by
`grain_residual_reopens_the_source`: the coarse face together with the residual reopens the atom
face exactly. -/
theorem grainBridge_preserves (π : FineCell → CoarseCell) (sel : CoarseCell → FineCell) :
    (grainBridge π sel).preserves PUnit.unit :=
  grain_residual_reopens_the_source π sel

/-- [counterexample; formal-checked] And it is **not** a shared receiver face promoted to an
equivalence: at an equal aperture the selection merges what the fine restriction separates, which is
`selection_is_insufficient_for_the_fine_reading`. -/
def grainBridge_is_not_an_equivalence :
    ReceiverInsufficiency
      (fun φ : Bool → Bool → ContactClass => selectionReading (fun _ : Unit => false) φ)
      (fun φ : Bool → Bool → ContactClass => FineInside (fun _ : Bool => ()) φ) :=
  selection_is_insufficient_for_the_fine_reading

end Grain

/-! ### One honest `ProposedBridge` at speculative status and `interpretation` grade -/

section ProteinEmbedding

variable {Contact Embedding : Type}

/-- [definition] **The protein contact atlas against a learned embedding atlas.** The claim being
proposed is that a learned embedding's coordinate atlas and the contact-complex atlas of
`crates/holonic-engine/src/grain_tower.rs` are two charts of one object. It is a *candidate*: no
passage is supplied, the status is `speculativeAnalogy` and the grade is `interpretation`, which
`docs/canon/EPISTEMIC_GRADES.md` requires to carry explicit maps, limits, a preserved diagram, a
first derivation target and a falsifier that can fire.

The three required hypotheses are written out, not gestured at:

1. the contact face separates distinct contact complexes (otherwise the source of the bridge is
   already a quotient and the bridge is about that quotient, not about the protein);
2. the candidate map carries the contact face to the embedding face exactly (otherwise there is a
   residual, and the bridge is at best a lossy map with that residual retained);
3. the candidate map is injective (otherwise it is a coarse graining and owes its residual).

The falsifier fires when two contacts with different faces share an embedding coordinate.

Rust counterpart: `crates/holonic-engine/src/bridge.rs::protein_embedding_proposal`. -/
def proteinEmbeddingProposal (contactFace : Contact → ℤ) (embeddingFace : Embedding → ℤ)
    (candidateMap : Contact → Embedding) : ProposedBridge.{0, 0} Contact Embedding where
  candidate :=
    { status := .speculativeAnalogy
      passage := none
      Preserved := PUnit
      preserves := fun _ => ∀ x, embeddingFace (candidateMap x) = contactFace x
      grade := .interpretation
      passage_of_map := fun h => absurd h (by decide) }
  requiredHypotheses :=
    [ ∀ x y : Contact, contactFace x = contactFace y → x = y,
      ∀ x : Contact, embeddingFace (candidateMap x) = contactFace x,
      Function.Injective candidateMap ]
  supportingReceivers := [⟨ℤ, (contactFace, embeddingFace)⟩]
  counterexamples := []
  falsifier := ∃ x y : Contact, contactFace x ≠ contactFace y ∧ candidateMap x = candidateMap y

/-- [proved-derived; formal-checked] It claims nothing: its status entails only itself and it
carries no passage. -/
theorem proteinEmbeddingProposal_claims_nothing (contactFace : Contact → ℤ)
    (embeddingFace : Embedding → ℤ) (candidateMap : Contact → Embedding) :
    (proteinEmbeddingProposal contactFace embeddingFace candidateMap).candidate.status =
        .speculativeAnalogy ∧
      (proteinEmbeddingProposal contactFace embeddingFace candidateMap).candidate.passage = none ∧
      (proteinEmbeddingProposal contactFace embeddingFace candidateMap).candidate.grade =
        .interpretation :=
  ⟨rfl, rfl, rfl⟩

/-- [proved-derived; formal-checked] **It cannot be promoted to a map while it carries none.** The
refusal is by type, not by policy. -/
theorem proteinEmbeddingProposal_not_promotable_to_a_map (contactFace : Contact → ℤ)
    (embeddingFace : Embedding → ℤ) (candidateMap : Contact → Embedding) (target : BridgeStatus)
    (ht : target.entails .actualMap = true) :
    IsEmpty (Promotion (proteinEmbeddingProposal contactFace embeddingFace candidateMap) target) :=
  missing_passage_blocks_promotion _ target rfl ht

/-- [counterexample; formal-checked] And when the first hypothesis fails — a contact face that
merges two distinct contact complexes — no promotion exists at all, whatever the target. The
witness is the constant face on `Bool`. -/
theorem proteinEmbeddingProposal_blocked_by_a_merging_face (target : BridgeStatus) :
    IsEmpty (Promotion
      (proteinEmbeddingProposal (fun _ : Bool => (0 : ℤ)) (fun _ : Bool => (0 : ℤ)) id) target) := by
  refine ⟨fun p => ?_⟩
  have hsep := p.discharged (∀ x y : Bool, (0 : ℤ) = 0 → x = y) (by simp [proteinEmbeddingProposal])
  exact absurd (hsep false true rfl) (by decide)

end ProteinEmbedding

end Soma.Holonics.Foundation.Bridges

section Audit
open Soma.Holonics.Foundation.Bridges

#print axioms composeGrade_comm
#print axioms composeGrade_self
#print axioms composeGrade_assoc
#print axioms composeGrade_support_le
#print axioms counterexample_does_not_compose
#print axioms historical_does_not_compose
#print axioms entails_refl
#print axioms entails_trans
#print axioms entails_antisymm
#print axioms equivalence_entails_map
#print axioms naturalFamily_entails_structurePreserving
#print axioms sharedReceiverFace_entails_coPresence
#print axioms sharedReceiverFace_not_actualMap
#print axioms sharedReceiverFace_supplies_no_map
#print axioms actualMap_not_structurePreserving
#print axioms actualMap_does_not_preserve_structure
#print axioms equivalence_not_naturalFamily
#print axioms equivalence_does_not_give_a_natural_family
#print axioms numericalResemblance_not_sharedReceiverFace
#print axioms numericalResemblance_does_not_identify
#print axioms coPresence_gives_nothing
#print axioms speculativeAnalogy_is_off_the_order
#print axioms statusMeet_comm
#print axioms statusMeet_lower
#print axioms statusMeet_greatest
#print axioms statusMeet_of_the_incomparable_pairs
#print axioms composedPassage_of_both
#print axioms comp_at_meet
#print axioms composedBridge_status_grade
#print axioms comp_respects_map_claim
#print axioms composedBridge_refuses_missing_passage
#print axioms promoted_status
#print axioms counterexample_blocks_promotion
#print axioms false_hypothesis_blocks_promotion
#print axioms missing_passage_blocks_promotion
#print axioms rebaseBridge_preserves
#print axioms rebaseBridge_residual_subsingleton
#print axioms padicHalfBridge_preserves
#print axioms padicHalfBridge_is_not_an_equivalence
#print axioms grainBridge_preserves
#print axioms grainBridge_is_not_an_equivalence
#print axioms proteinEmbeddingProposal_claims_nothing
#print axioms proteinEmbeddingProposal_not_promotable_to_a_map
#print axioms proteinEmbeddingProposal_blocked_by_a_merging_face
end Audit
