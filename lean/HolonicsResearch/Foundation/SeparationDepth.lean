import Holonics.Foundation.CausalRelevance
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# The separation depth: a boundary is located within the count of its classes

The record `research/records/2026-10-26_THE_OPERATION_IS_A_LINE_IN_THE_LIFT_AND_THE_RELEASE_READS_THE_RADIX_ITINERARY.md`
(§4) locates the capture boundary of a passage as the future agreement of
`Foundation/CausalRelevance` (`futureAgreement`, atlas `compression.future-agreement-greatest-stable`):
two states are one class when no admitted history of navigator moves, read by any receiver,
separates them. That relation quantifies over every history. This file reads it by depth: two
states agree to depth `d` when no history of at most `d` moves separates them, and the separation
depth of two states is the length of their shortest separating history (`δ = 2^(−depth)` is then a
pseudo-ultrametric). It proves that the depth reading reaches the whole future agreement, and how
soon.

[proved-standard; formal-checked] What is proved.

1. **Depth agreement is an equivalence that coarsens with depth** (`agreeUpTo_equivalence`,
   `agreeUpTo_mono`). Transitivity is the ultrametric inequality: the separation depth of two
   states is at least the smaller of their depths to a third.
2. **The future agreement is every depth at once** (`futureAgreement_iff_forall_agreeUpTo`).
3. **A move spends depth** (`agreeUpTo_transport`): states agreeing to depth `d + k` agree to
   depth `d` after any word of `k` moves; so a word of `k` moves multiplies `δ` by at most `2ᵏ`.
4. **One letter that separates nothing new ends the search** (`futureAgreement_of_stable`): if
   agreement to depth `d` already implies agreement to depth `d + 1`, it is the whole future
   agreement.
5. **The count of classes bounds the depth** (`stable_or_classCount`,
   `futureAgreement_iff_agreeUpTo_card`): on a finite state space each new depth either adds a
   class or ends the search, so two states agree on every history exactly when they agree on every
   history of at most `|states|` moves (Moore's bound).

So the boundary of a passage is not a window chosen in advance: it is read by refining one letter
at a time, and it stops at the first letter that separates no new class, never later than the
count of classes. The stop is global. `futureAgreement_of_stable` needs depth-`d` agreement to
imply depth-`(d + 1)` agreement for every pair of states, over every admitted receiver and word;
one pair whose next letter separates nothing has not stopped the search, since a longer word can
still separate it. A release at depth `d` is lawful only where the declared future is shown stable
there.

The computational object is the helical pair interaction: each move is a navigator step and each
receiver a contact's reading, and the depth is how many steps a contact needs to tell two states
apart. Of the winding guide's six general objects this touches the tube (histories as clocked
words) and the tower thread (the boundary as the quotient the next level reads); the helix, the
pair, faces and placement and the cell holonomy stay attached.

Consumers: the atlas row `compression.separation-depth` and the record's §4.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.SeparationDepth

open Holonics.Foundation.Chronology
open Holonics.Foundation.CausalRelevance.NonLinear

variable {Generator Receiver Source Face : Type*}
variable (observe : Receiver → Source → Face) (step : Generator → Source → Source)

/-- [definition] Agreement of every receiver after every history of at most `d` moves. -/
def agreeUpTo (d : ℕ) (left right : Source) : Prop :=
  ∀ receiver (word : List Generator), word.length ≤ d →
    observe receiver (transportWord step word left) =
      observe receiver (transportWord step word right)

/-- [proved-standard; formal-checked] Depth agreement is an equivalence. -/
theorem agreeUpTo_equivalence (d : ℕ) : Equivalence (agreeUpTo observe step d) where
  refl _ := fun _ _ _ => rfl
  symm h receiver word hw := (h receiver word hw).symm
  trans h₁ h₂ receiver word hw := (h₁ receiver word hw).trans (h₂ receiver word hw)

/-- [proved-standard; formal-checked] Depth agreement coarsens as the depth falls. -/
theorem agreeUpTo_mono {d e : ℕ} (hde : d ≤ e) {left right : Source}
    (h : agreeUpTo observe step e left right) : agreeUpTo observe step d left right :=
  fun receiver word hw => h receiver word (hw.trans hde)

/-- [proved-standard; formal-checked] **The future agreement is every depth at once.** -/
theorem futureAgreement_iff_forall_agreeUpTo (left right : Source) :
    futureAgreement observe step left right ↔ ∀ d, agreeUpTo observe step d left right :=
  ⟨fun h _ receiver word _ => h receiver word,
    fun h receiver word => h word.length receiver word le_rfl⟩

/-- [proved-standard; formal-checked] **A move spends depth:** states agreeing to depth `d + k`
agree to depth `d` after any word of `k` moves. -/
theorem agreeUpTo_transport {d : ℕ} (word : List Generator) {left right : Source}
    (h : agreeUpTo observe step (d + word.length) left right) :
    agreeUpTo observe step d (transportWord step word left) (transportWord step word right) := by
  intro receiver future hfuture
  rw [← transportWord_append, ← transportWord_append]
  exact h receiver (future ++ word) (by rw [List.length_append]; omega)

/-- [proved-standard; formal-checked] **One letter that separates nothing new ends the search:** if
agreement to depth `d` implies agreement to depth `d + 1`, it implies the whole future
agreement. -/
theorem futureAgreement_of_stable {d : ℕ}
    (stable : ∀ left right, agreeUpTo observe step d left right →
      agreeUpTo observe step (d + 1) left right)
    {left right : Source} (h : agreeUpTo observe step d left right) :
    futureAgreement observe step left right := by
  have hpresent : agreeUpTo observe step d ≤ fun left right => ∀ receiver,
      observe receiver left = observe receiver right := by
    intro l r hlr receiver
    exact hlr receiver [] (Nat.zero_le _)
  have hstable : ∀ generator l r, agreeUpTo observe step d l r →
      agreeUpTo observe step d (step generator l) (step generator r) := by
    intro generator l r hlr
    exact agreeUpTo_transport observe step (d := d) [generator] (stable l r hlr)
  exact futureAgreement_is_greatest_stable observe step (agreeUpTo observe step d) hpresent
    hstable left right h

/-- [definition] Depth agreement as a setoid. -/
def depthSetoid (d : ℕ) : Setoid Source :=
  ⟨agreeUpTo observe step d, agreeUpTo_equivalence observe step d⟩

/-- [definition] The number of classes depth agreement separates. -/
noncomputable def classCount (d : ℕ) : ℕ := Nat.card (Quotient (depthSetoid observe step d))

/-- [definition] Each class at depth `d + 1` lies in one class at depth `d`. -/
def coarsen (d : ℕ) :
    Quotient (depthSetoid observe step (d + 1)) → Quotient (depthSetoid observe step d) :=
  Quotient.lift (fun x => Quotient.mk (depthSetoid observe step d) x)
    (fun _ _ h => Quotient.sound (agreeUpTo_mono observe step (d := d) (e := d + 1)
      (Nat.le_succ d) h))

/-- [proved-standard; formal-checked] Every class at depth `d` is reached from depth `d + 1`. -/
theorem coarsen_surjective (d : ℕ) : Function.Surjective (coarsen observe step d) := by
  intro y
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective y
  exact ⟨Quotient.mk _ x, rfl⟩

section Finite

variable [Finite Source]

/-- [proved-standard; formal-checked] Deeper agreement separates at least as many classes. -/
theorem classCount_le_succ (d : ℕ) :
    classCount observe step d ≤ classCount observe step (d + 1) :=
  Nat.card_le_card_of_surjective _ (coarsen_surjective observe step d)

/-- [proved-standard; formal-checked] No depth separates more classes than there are states. -/
theorem classCount_le_card (d : ℕ) : classCount observe step d ≤ Nat.card Source :=
  Nat.card_le_card_of_surjective _ Quotient.mk_surjective

/-- [proved-standard; formal-checked] **No new class means no new separation:** if depth `d + 1`
separates no more classes than depth `d`, agreement to depth `d` implies agreement to depth
`d + 1`. -/
theorem stable_of_classCount_le {d : ℕ}
    (h : classCount observe step (d + 1) ≤ classCount observe step d) :
    ∀ left right, agreeUpTo observe step d left right →
      agreeUpTo observe step (d + 1) left right := by
  have hbij := (coarsen_surjective observe step d).bijective_of_nat_card_le h
  intro left right hlr
  have heq : coarsen observe step d (Quotient.mk _ left) =
      coarsen observe step d (Quotient.mk _ right) := by
    show Quotient.mk (depthSetoid observe step d) left =
      Quotient.mk (depthSetoid observe step d) right
    exact Quotient.sound hlr
  exact Quotient.exact (hbij.injective heq)

/-- [proved-standard; formal-checked] **Each depth adds a class or ends the search:** by depth `d`
either agreement has stabilized, or it separates at least `d + 1` classes. -/
theorem stable_or_classCount (hne : Nonempty Source) (d : ℕ) :
    (∃ e ≤ d, ∀ left right, agreeUpTo observe step e left right →
        agreeUpTo observe step (e + 1) left right) ∨
      d + 1 ≤ classCount observe step d := by
  induction d with
  | zero =>
    right
    have : Nonempty (Quotient (depthSetoid observe step 0)) := ⟨Quotient.mk _ hne.some⟩
    have h0 : 0 < Nat.card (Quotient (depthSetoid observe step 0)) := Nat.card_pos
    unfold classCount
    omega
  | succ d ih =>
    by_cases hs : ∀ left right, agreeUpTo observe step d left right →
        agreeUpTo observe step (d + 1) left right
    · exact Or.inl ⟨d, Nat.le_succ d, hs⟩
    · rcases ih with ⟨e, he, hstab⟩ | hcount
      · exact Or.inl ⟨e, Nat.le_succ_of_le he, hstab⟩
      · right
        have hlt : classCount observe step d < classCount observe step (d + 1) := by
          by_contra hle
          exact hs (stable_of_classCount_le observe step (not_lt.mp hle))
        omega

/-- [proved-standard; formal-checked] **The count of states bounds the depth (Moore):** two states
of a finite state space agree on every history exactly when they agree on every history of at
most `|states|` moves. -/
theorem futureAgreement_iff_agreeUpTo_card (left right : Source) :
    futureAgreement observe step left right ↔
      agreeUpTo observe step (Nat.card Source) left right := by
  refine ⟨fun h => (futureAgreement_iff_forall_agreeUpTo observe step left right).mp h _,
    fun h => ?_⟩
  rcases stable_or_classCount observe step ⟨left⟩ (Nat.card Source) with
    ⟨e, he, hstab⟩ | hcount
  · exact futureAgreement_of_stable observe step hstab (agreeUpTo_mono observe step he h)
  · have := classCount_le_card observe step (Nat.card Source)
    exfalso
    omega

end Finite

end Holonics.Foundation.SeparationDepth
