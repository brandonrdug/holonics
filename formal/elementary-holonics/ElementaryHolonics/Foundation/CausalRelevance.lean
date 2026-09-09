import ElementaryHolonics.Foundation.JointReceiverDescent
import ElementaryHolonics.Millennium.ReceiverHistory
import ElementaryHolonics.Millennium.Separation

/-!
# Generator-invariant receiver relevance

The present joint receiver blind subgroup need not be stable under admitted generators.  The
future relevance kernel is the largest additive subgroup whose differences remain invisible to
every declared receiver after every finite ordered generator history.  It is a receiver/history
construction, not a scalar loss and not a claim about nonlinear or categorical relevance.
-/

namespace Soma.Holonics.Foundation.CausalRelevance

open Soma.Holonics
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.Receiver
open Soma.Holonics.Millennium.LineageCompression
open Soma.Holonics.Foundation.JointReceiverDescent
open Soma.Holonics.Millennium.ReceiverHistory

universe u

variable {Generator Receiver X V : Type u}
  [AddCommGroup X] [AddCommGroup V]
  (read : Receiver → (X →+ V))
  (transport : Generator → (X →+ X))

private theorem transportWord_add (word : List Generator) (left right : X) :
    transportWord (fun generator x => transport generator x) word (left + right) =
      transportWord (fun generator x => transport generator x) word left +
        transportWord (fun generator x => transport generator x) word right := by
  induction word with
  | nil => rfl
  | cons generator word ih =>
    simp only [transportWord_cons]
    rw [ih, map_add]

private theorem transportWord_zero (word : List Generator) :
    transportWord (fun generator x => transport generator x) word 0 = 0 := by
  induction word with
  | nil => rfl
  | cons generator word ih =>
    simp only [transportWord_cons, ih, map_zero]

/-- One future receiver is indexed by a present receiver and its ordered history. -/
def futureRead : (Receiver × List Generator) → (X →+ V)
  | (receiver, word) => {
      toFun := fun source =>
        read receiver (transportWord (fun generator x => transport generator x) word source)
      map_zero' := by
        rw [transportWord_zero transport word, map_zero]
      map_add' := by
        intro left right
        rw [transportWord_add transport word left right, map_add] }

/-- The largest subgroup invisible to every declared receiver after every admitted history. -/
abbrev futureCollapsed : AddSubgroup X :=
  collapsedPopulation (futureRead read transport)

theorem mem_futureCollapsed_iff (source : X) :
    source ∈ futureCollapsed read transport ↔
      ∀ receiver word,
        read receiver
          (transportWord (fun generator x => transport generator x) word source) = 0 := by
  change source ∈ collapsedPopulation (futureRead read transport) ↔ _
  simp only [collapsedPopulation, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker]
  constructor
  · intro h receiver word
    exact h (receiver, word)
  · intro h receiverWord
    rcases receiverWord with ⟨receiver, word⟩
    exact h receiver word

private theorem transportWord_append_generator (word : List Generator) (generator : Generator)
    (source : X) :
    transportWord (fun g x => transport g x) (word ++ [generator]) source =
      transportWord (fun g x => transport g x) word (transport generator source) := by
  induction word with
  | nil => rfl
  | cons head word ih =>
    simp only [List.cons_append, transportWord_cons, ih]

theorem futureCollapsed_invariant (generator : Generator) {source : X}
    (hsource : source ∈ futureCollapsed read transport) :
    transport generator source ∈ futureCollapsed read transport := by
  rw [mem_futureCollapsed_iff] at hsource ⊢
  intro receiver word
  rw [← transportWord_append_generator transport word generator source]
  exact hsource receiver (word ++ [generator])

/-- Every future-blind difference is blind at the present receiver. -/
theorem futureCollapsed_le_presentCollapsed :
    futureCollapsed read transport ≤ collapsedPopulation read := by
  intro source hsource
  rw [mem_futureCollapsed_iff] at hsource
  apply AddSubgroup.mem_iInf.mpr
  intro receiver
  simpa using hsource receiver []

def GeneratorInvariant (subgroup : AddSubgroup X) : Prop :=
  ∀ generator source, source ∈ subgroup → transport generator source ∈ subgroup

/-- The future kernel is greatest among present-blind subgroups invariant under every generator. -/
theorem futureCollapsed_is_greatest_generatorInvariant
    (subgroup : AddSubgroup X)
    (presentBlind : subgroup ≤ collapsedPopulation read)
    (invariant : GeneratorInvariant transport subgroup) :
    subgroup ≤ futureCollapsed read transport := by
  intro source hsource
  rw [mem_futureCollapsed_iff]
  intro receiver word
  have transported :
      transportWord (fun generator x => transport generator x) word source ∈ subgroup := by
    induction word with
    | nil => exact hsource
    | cons generator word ih =>
      exact invariant generator _ ih
  exact (AddSubgroup.mem_iInf.mp (presentBlind transported) receiver)

theorem futureCollapsed_is_presentBlind_and_invariant :
    futureCollapsed read transport ≤ collapsedPopulation read ∧
      GeneratorInvariant transport (futureCollapsed read transport) :=
  ⟨futureCollapsed_le_presentCollapsed read transport,
    fun generator source hsource => futureCollapsed_invariant read transport generator hsource⟩

/-- The canonical joint receiver-history package built from the future family itself. -/
def futureHistory : JointReceiverHistory Generator (Receiver × List Generator) X V where
  read := futureRead read transport
  transport := transport
  preservesCollapsed := futureCollapsed_invariant read transport

def completeFutureHistory : CompleteReceiverHistoryQuotient
    Generator (Receiver × List Generator) X
      (JointReceiverHistory.JointQuotient (futureHistory read transport)) V where
  toReceiverHistoryCompression :=
    JointReceiverHistory.historyCompression (futureHistory read transport)
  complete := by
    intro left right equal
    apply (JointReceiverHistory.quotient_eq_iff_joint_readings_eq
      (futureHistory read transport) left right).mpr
    intro receiverWord
    exact equal receiverWord []

theorem completeFutureHistory_quotientEq_iff_causalSignatureEq {left right : X} :
    (completeFutureHistory read transport).present.quotient left =
        (completeFutureHistory read transport).present.quotient right ↔
      (completeFutureHistory read transport).causalSignature left =
        (completeFutureHistory read transport).causalSignature right :=
  CompleteReceiverHistoryQuotient.quotientEq_iff_causalSignatureEq
    (completeFutureHistory read transport)

theorem futureHistory_quotientNe_returns_separator {left right : X}
    (unequal :
      (completeFutureHistory read transport).present.quotient left ≠
        (completeFutureHistory read transport).present.quotient right) :
    ∃ receiver word,
      read receiver
          (transportWord (fun generator x => transport generator x) word left) ≠
        read receiver
          (transportWord (fun generator x => transport generator x) word right) := by
  classical
  by_contra noSeparator
  apply unequal
  apply (JointReceiverHistory.quotient_eq_iff_joint_readings_eq
    (futureHistory read transport) left right).mpr
  intro receiverWord
  by_contra separated
  exact noSeparator ⟨receiverWord.1, receiverWord.2, separated⟩

end Soma.Holonics.Foundation.CausalRelevance

namespace Soma.Holonics.Foundation.CausalRelevance.NonLinear

open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.Separation

universe uG uR uS uF

variable {Generator Receiver Source Face : Type*}

/-- Equality of all declared receiver faces after every ordered deterministic history. -/
def futureAgreement
    (observe : Receiver → Source → Face) (step : Generator → Source → Source)
    (left right : Source) : Prop :=
  ∀ receiver word,
    observe receiver (transportWord step word left) =
      observe receiver (transportWord step word right)

/-- The complete family of future receiver functions. -/
def futureReceiverFamily
    (observe : Receiver → Source → Face) (step : Generator → Source → Source) :
    ReceiverFamily Source Face :=
  Set.range (fun receiverWord : Receiver × List Generator =>
    observe receiverWord.1 ∘ transportWord step receiverWord.2)

theorem futureAgreement_iff_collapseOf
    (observe : Receiver → Source → Face) (step : Generator → Source → Source)
    (left right : Source) :
    futureAgreement observe step left right ↔
      collapseOf (futureReceiverFamily observe step) left right := by
  constructor
  · intro h receiverFace hreceiverFace
    obtain ⟨⟨receiver, word⟩, rfl⟩ := hreceiverFace
    exact h receiver word
  · intro h receiver word
    apply h (observe receiver ∘ transportWord step word)
    exact ⟨(receiver, word), rfl⟩

theorem futureAgreement_equivalence
    (observe : Receiver → Source → Face) (step : Generator → Source → Source) :
    Equivalence (futureAgreement observe step) where
  refl left := by intro receiver word; rfl
  symm h receiver word := (h receiver word).symm
  trans hleft hright receiver word := (hleft receiver word).trans (hright receiver word)

theorem futureAgreement_preserved_by_step
    (observe : Receiver → Source → Face) (step : Generator → Source → Source)
    {left right : Source} (same : futureAgreement observe step left right)
    (generator : Generator) :
    futureAgreement observe step (step generator left) (step generator right) := by
  have append_word : ∀ (word : List Generator) (source : Source),
      transportWord step (word ++ [generator]) source =
        transportWord step word (step generator source) := by
    intro word source
    induction word with
    | nil => rfl
    | cons head word ih =>
      simp only [List.cons_append, transportWord_cons, ih]
  intro receiver word
  rw [← append_word word left, ← append_word word right]
  exact same receiver (word ++ [generator])

theorem futureAgreement_le_presentAgreement
    (observe : Receiver → Source → Face) (step : Generator → Source → Source) :
    futureAgreement observe step ≤ fun left right => ∀ receiver,
      observe receiver left = observe receiver right := by
  intro left right h receiver
  exact h receiver []

/-- The future agreement relation is the greatest present receiver agreement stable under every
deterministic generator. -/
theorem futureAgreement_is_greatest_stable
    (observe : Receiver → Source → Face) (step : Generator → Source → Source)
    (relation : Source → Source → Prop)
    (presentAgreement : relation ≤ fun left right => ∀ receiver,
      observe receiver left = observe receiver right)
    (stable : ∀ generator left right, relation left right →
      relation (step generator left) (step generator right)) :
    relation ≤ futureAgreement observe step := by
  intro left right hrelation receiver word
  have hword : relation (transportWord step word left) (transportWord step word right) := by
    induction word with
    | nil => exact hrelation
    | cons generator word ih =>
      exact stable generator _ _ ih
  exact presentAgreement _ _ hword receiver

/-! ## A small nonlinear control -/

abbrev ThreeSource := ℚ × ℚ × ℚ
abbrev ThreeGenerator := Bool

def threeStep : ThreeGenerator → ThreeSource → ThreeSource
  | false, (first, second, third) => (second, first, third)
  | true, (first, second, third) => (first, second, -third)

def firstReceiver : Unit → ThreeSource → ℚ := fun _ source => source.1

def thirdBlind : ThreeSource → ThreeSource → Prop :=
  fun left right => left.1 = right.1 ∧ left.2.1 = right.2.1

theorem thirdBlind_stable :
    ∀ generator left right, thirdBlind left right →
      thirdBlind (threeStep generator left) (threeStep generator right) := by
  intro generator left right h
  rcases left with ⟨leftFirst, leftSecond, leftThird⟩
  rcases right with ⟨rightFirst, rightSecond, rightThird⟩
  rcases h with ⟨hfirst, hsecond⟩
  cases generator
  · exact ⟨hsecond, hfirst⟩
  · exact ⟨hfirst, hsecond⟩

theorem thirdBlind_future :
    thirdBlind ≤ futureAgreement firstReceiver threeStep := by
  apply futureAgreement_is_greatest_stable firstReceiver threeStep thirdBlind
  · intro left right h receiver
    exact h.1
  · exact thirdBlind_stable

theorem swap_reopens_second_coordinate :
    ¬ futureAgreement firstReceiver threeStep
      (0, 0, 0) (0, 1, 0) := by
  intro h
  have separated := h () [false]
  simp [firstReceiver, threeStep] at separated

end Soma.Holonics.Foundation.CausalRelevance.NonLinear

section Audit
open Soma.Holonics.Foundation.CausalRelevance
#print axioms mem_futureCollapsed_iff
#print axioms futureCollapsed_invariant
#print axioms futureCollapsed_is_greatest_generatorInvariant
#print axioms completeFutureHistory_quotientEq_iff_causalSignatureEq
#print axioms futureHistory_quotientNe_returns_separator
open Soma.Holonics.Foundation.CausalRelevance.NonLinear
#print axioms futureAgreement_iff_collapseOf
#print axioms futureAgreement_preserved_by_step
#print axioms futureAgreement_is_greatest_stable
#print axioms thirdBlind_future
#print axioms swap_reopens_second_coordinate
end Audit
