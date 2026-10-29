import HolonicsResearch.Foundation.ActionDescent
import Holonics.Foundation.HodgeReceiver
import Holonics.Aeon.Production.HodgeTime
import Holonics.Transport.ChangingReceiver.Defect
import Mathlib.Tactic

/-!
# Retention and release through changing receivers

Object 8 of `docs/ELEMENTARY_OBJECTS.md` takes retention relative to the admitted future. When the
admitted receivers and actions themselves change from one phase to the next, the admitted future of
a present includes receivers that are not yet listening: a direction silent now may be read later,
and a retention that releases it at the present receivers has released what a later receiver needs.
This module proves that statement in three parts (#410, "Retention and release through changing
receivers"). It builds on `Foundation/ActionDescent` (the continuation square),
`Foundation/MinimalRetention` (the minimal standing), `Transport/ChangingReceiver/Defect` (the
signed defect), `Foundation/HodgeReceiver`, `Compression/Core/FaceMap` and the hollow triangle of
`Aeon/Production/HodgeTime`, and restates none of them.

[proved-derived; formal-checked] What is proved.

1. **The clocked lift** (`clockedTransport`, `clockedObserve`, `clockedTransport_word_fst`,
   `present_or_later_separator`). Receivers `ρ_(c,R)` and actions `T_(c,a)` that depend on the phase
   `c`, with the phase stepping by `next`, are one medium on `Ctx × Source`; its minimal standing
   (`MinimalRetention.minimalStanding` of the lift) is the retention of a present at its phase. Two
   presents every present receiver reads alike either share their whole admitted future, and are
   released, or a nonempty word reaches a later phase whose receiver reads them apart: the
   later-phase separator.
2. **The changing receiver/action defect** (`stepDefect`, `wordDefect`, `wordDefect_cons`,
   `wordDefect_eq_zero`, `toDescent`, `phaseAgreement_of_encode_eq`). For an encoding `E_c` and
   proposed moves `U_(c,a)`, the step defect `E_(next c a) T_(c,a) x − U_(c,a) E_c x` is
   `Transport/ChangingReceiver.defect`. Along a word the defect composes exactly through the moves:
   with additive moves, the word's defect is the last step's defect plus the last move applied to
   the earlier word's defect, so every step defect vanishing makes every word defect vanish
   (`ChangingReceiver.word_defect_zero` with the receivers and actions changing). Decoders and
   vanishing step defects make the encoding an `ActionDescent.Descent` of the clocked lift, so two
   presents it merges at a phase share their whole admitted future from that phase.
3. **The dormant harmonic mode against node/cell receivers** (`nodeCellRead`,
   `mem_harmonic_iff_forall_nodeCell`, `ker_faceMap_nodeCell`, `futureAgreement_nodeCell_iff`,
   `heatStep_fixes_harmonic`, `heat_releases_harmonic`). On a weighted complex the node receivers
   read the divergence `δ₀x` and the cell receivers the flux `d₁x`. Under any transports that keep
   the harmonic subspace, the relevance kernel of these receivers is exactly the harmonic subspace:
   the node/cell retention releases precisely the harmonic modes, which `Transport/CellHolonomy`
   shows are silent there and reproduced by no potential. The exact heat step `x ↦ x − τ Δ x` over
   ℚ is one such transport (the ℚ chart of
   `Physics/TemporalHodgeResidue.eulerHeatStep_fixes_harmonic`).
4. **The later-phase separator on the hollow triangle** (`Triangle.phaseRead`,
   `Triangle.loop_later_phase_separator`). On `HodgeTime.HollowTriangle` the loop `(1,1,1)` is
   harmonic, so under the heat flow the node receivers share its whole future with zero's, and the
   node/cell retention releases it. The harmonic clock admitted from phase 1 on reads it `3`, so the
   minimal standing of the clocked lift keeps it apart from zero at phase 0, where every present
   receiver reads the two alike: a dormant ring kept across the phase boundary and read later.

[open] A receiver family admitted only by a later action (rather than by the clock), and the
release of the defect's remainder at a declared grain, are not stated here.

The computational object is the helical pair interaction read by its admitted futures: the
receivers that read a contact change with the clock, and retention keeps what any later receiver
of the admitted family reads. Of the winding guide's six general objects this touches the tube (the
clocked span and its words), the cell holonomy (the harmonic circulation a cycle receiver reads) and
the tower thread (the defect composed through the levels' moves); the helix, the pair, faces and
placement stay attached.

Consumers: the atlas rows `retention.changing-receiver-phase` and
`cell.harmonic-release-later-separator`, and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Foundation.ChangingReceiverRetention

open Holonics.Foundation.Chronology
open Holonics.Foundation.CausalRelevance.NonLinear
open Holonics.Foundation.MinimalRetention
open Holonics.Foundation.ActionDescent
open Holonics.Transport.ChangingReceiver

/-! ## 1. The clocked lift -/

section Clocked

variable {Ctx Action Receiver Source Face : Type*}

/-- [definition] **The clocked transport**: an action moves the phase by `next` and the present by
the phase's own transport. -/
def clockedTransport (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (a : Action) (p : Ctx × Source) : Ctx × Source :=
  (next p.1 a, transport p.1 a p.2)

/-- [definition] **The clocked reading**: a receiver reads a present through its phase's chart. -/
def clockedObserve (observe : Ctx → Receiver → Source → Face) (receiver : Receiver)
    (p : Ctx × Source) : Face :=
  observe p.1 receiver p.2

/-- [proved-derived; formal-checked] A word moves the phase by the clock alone. -/
theorem clockedTransport_word_fst (next : Ctx → Action → Ctx)
    (transport : Ctx → Action → Source → Source) (word : List Action) (c : Ctx) (x : Source) :
    (transportWord (clockedTransport next transport) word (c, x)).1 =
      transportWord (fun a c => next c a) word c := by
  induction word with
  | nil => rfl
  | cons a word ih => simp only [transportWord_cons, clockedTransport, ih]

/-- [proved-derived; formal-checked] **Release, or the later-phase separator**: two presents every
receiver of their phase reads alike either share their whole admitted future, or a nonempty word
reaches a later phase whose receiver reads them apart. -/
theorem present_or_later_separator (observe : Ctx → Receiver → Source → Face)
    (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source) (c : Ctx)
    (left right : Source)
    (present : ∀ receiver, observe c receiver left = observe c receiver right) :
    futureAgreement (clockedObserve observe) (clockedTransport next transport) (c, left)
        (c, right) ∨
      ∃ word : List Action, word ≠ [] ∧ ∃ receiver,
        observe (transportWord (fun a c => next c a) word c) receiver
            (transportWord (clockedTransport next transport) word (c, left)).2 ≠
          observe (transportWord (fun a c => next c a) word c) receiver
            (transportWord (clockedTransport next transport) word (c, right)).2 := by
  by_cases h : futureAgreement (clockedObserve observe) (clockedTransport next transport)
      (c, left) (c, right)
  · exact Or.inl h
  · right
    unfold futureAgreement at h
    push Not at h
    obtain ⟨receiver, word, hne⟩ := h
    refine ⟨word, ?_, receiver, ?_⟩
    · rintro rfl
      exact hne (present receiver)
    · intro heq
      apply hne
      simp only [clockedObserve, clockedTransport_word_fst]
      exact heq

end Clocked

/-! ## 2. The changing receiver/action defect -/

section Defect

variable {Ctx Action Source Q : Type*} [AddCommGroup Q]

/-- [definition] **The step defect** of an encoding `E_c` against proposed moves `U_(c,a)`:
`E_(next c a) (T_(c,a) x) − U_(c,a) (E_c x)`, the `Transport/ChangingReceiver` defect of the
step. -/
def stepDefect (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (encode : Ctx → Source → Q) (move : Ctx → Action → Q → Q) (c : Ctx) (a : Action)
    (x : Source) : Q :=
  defect (encode c) (fun y => encode (next c a) (transport c a y)) (move c a) x

/-- [definition] **The word defect**: the encoding after a word against the moves run through the
same phases from the encoded present. -/
def wordDefect (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (encode : Ctx → Source → Q) (move : Ctx → Action → Q → Q) (word : List Action) (c : Ctx)
    (x : Source) : Q :=
  encode (transportWord (clockedTransport next transport) word (c, x)).1
      (transportWord (clockedTransport next transport) word (c, x)).2 -
    (transportWord (clockedTransport next move) word (c, encode c x)).2

theorem wordDefect_nil (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (encode : Ctx → Source → Q) (move : Ctx → Action → Q → Q) (c : Ctx) (x : Source) :
    wordDefect next transport encode move [] c x = 0 := by
  simp only [wordDefect, transportWord_nil, sub_self]

/-- [proved-derived; formal-checked] **The defect composes exactly along a word**: with additive
moves, the defect after `a :: word` is the step defect of `a` at the phase `word` reached plus the
move of `a` applied to the defect after `word`. -/
theorem wordDefect_cons (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (encode : Ctx → Source → Q) (move : Ctx → Action → Q →+ Q) (a : Action) (word : List Action)
    (c : Ctx) (x : Source) :
    wordDefect next transport encode (fun c a => move c a) (a :: word) c x =
      stepDefect next transport encode (fun c a => move c a)
          (transportWord (fun a c => next c a) word c) a
          (transportWord (clockedTransport next transport) word (c, x)).2 +
        move (transportWord (fun a c => next c a) word c) a
          (wordDefect next transport encode (fun c a => move c a) word c x) := by
  simp only [wordDefect, stepDefect, defect, transportWord_cons, clockedTransport,
    clockedTransport_word_fst, map_sub]
  abel

/-- [proved-derived; formal-checked] **Vanishing step defects vanish along every word**, the
receivers and actions changing with the phase. -/
theorem wordDefect_eq_zero (next : Ctx → Action → Ctx)
    (transport : Ctx → Action → Source → Source) (encode : Ctx → Source → Q)
    (move : Ctx → Action → Q →+ Q)
    (h : ∀ c a x, stepDefect next transport encode (fun c a => move c a) c a x = 0)
    (word : List Action) (c : Ctx) (x : Source) :
    wordDefect next transport encode (fun c a => move c a) word c x = 0 := by
  induction word with
  | nil => exact wordDefect_nil next transport encode _ c x
  | cons a word ih => rw [wordDefect_cons, h, ih, map_zero, add_zero]

variable {Receiver Face : Type*}

/-- [definition] **A changing-receiver descent is a descent of the clocked lift**: decoders
`D_(c,R) E_c = ρ_(c,R)` and vanishing step defects give an `ActionDescent.Descent` of the lifted
medium, with the phase carried beside the retained value. -/
def toDescent (observe : Ctx → Receiver → Source → Face) (next : Ctx → Action → Ctx)
    (transport : Ctx → Action → Source → Source) (encode : Ctx → Source → Q)
    (D : Ctx → Receiver → Q → Face) (U : Ctx → Action → Q → Q)
    (hdecode : ∀ c receiver x, D c receiver (encode c x) = observe c receiver x)
    (hzero : ∀ c a x, stepDefect next transport encode U c a x = 0) :
    Descent (clockedObserve observe) (clockedTransport next transport) (fun (_ : Unit) _ => ())
      (fun _ p => (p.1, encode p.1 p.2)) where
  decode _ receiver p := D p.1 receiver p.2
  move _ a p := (next p.1 a, U p.1 a p.2)
  decode_square _ receiver p := hdecode p.1 receiver p.2
  move_square _ a p := Prod.ext rfl (sub_eq_zero.mp (hzero p.1 a p.2))

/-- [proved-derived; formal-checked] **Two presents a changing-receiver descent merges at a phase
share their whole admitted future from that phase**, every later receiver included. -/
theorem phaseAgreement_of_encode_eq (observe : Ctx → Receiver → Source → Face)
    (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (encode : Ctx → Source → Q) (D : Ctx → Receiver → Q → Face) (U : Ctx → Action → Q → Q)
    (hdecode : ∀ c receiver x, D c receiver (encode c x) = observe c receiver x)
    (hzero : ∀ c a x, stepDefect next transport encode U c a x = 0) {c : Ctx}
    {left right : Source} (h : encode c left = encode c right) :
    futureAgreement (clockedObserve observe) (clockedTransport next transport) (c, left)
      (c, right) :=
  (toDescent observe next transport encode D U hdecode hzero).futureAgreement_of_encode_eq
    (c := ()) (left := (c, left)) (right := (c, right))
    (show (c, encode c left) = (c, encode c right) by rw [h])

end Defect

/-! ## 3. The dormant harmonic mode against node/cell receivers -/

section Harmonic

open Matrix
open Module
open Holonics.Foundation.HodgeReceiver
open Holonics.Compression.Core.FaceMap

variable {p q r : ℕ} (C : WeightedComplex p q r)

/-- [definition] **The node/cell receivers**: node `i` reads the divergence `(δ₀ x)_i`, cell `j`
reads the flux `(d₁ x)_j`. -/
def nodeCellRead : Fin p ⊕ Fin r → Dual ℚ (Fin q → ℚ)
  | Sum.inl i => LinearMap.proj i ∘ₗ Matrix.mulVecLin C.codiff₀
  | Sum.inr j => LinearMap.proj j ∘ₗ Matrix.mulVecLin C.d₁

theorem nodeCellRead_inl (i : Fin p) (x : Fin q → ℚ) :
    nodeCellRead C (Sum.inl i) x = (C.codiff₀ *ᵥ x) i := rfl

theorem nodeCellRead_inr (j : Fin r) (x : Fin q → ℚ) :
    nodeCellRead C (Sum.inr j) x = (C.d₁ *ᵥ x) j := rfl

/-- [proved-derived; formal-checked] **The harmonic modes are what the node/cell receivers leave
unread** (`WeightedComplex.mem_harmonic_iff` read receiver by receiver). -/
theorem mem_harmonic_iff_forall_nodeCell (x : Fin q → ℚ) :
    x ∈ C.harmonic ↔ ∀ c, nodeCellRead C c x = 0 := by
  rw [C.mem_harmonic_iff]
  constructor
  · rintro ⟨h₀, h₁⟩ (i | j)
    · simp [nodeCellRead_inl, h₀]
    · simp [nodeCellRead_inr, h₁]
  · intro h
    exact ⟨funext fun i => (nodeCellRead_inl C i x).symm.trans (h (Sum.inl i)),
      funext fun j => (nodeCellRead_inr C j x).symm.trans (h (Sum.inr j))⟩

/-- [proved-derived; formal-checked] **The node/cell relevance kernel is the harmonic subspace**:
under any transports that keep the harmonic subspace, the directions no admitted future of the
node/cell receivers reads are exactly the harmonic modes. -/
theorem ker_faceMap_nodeCell {ι : Type} (T : ι → (Fin q → ℚ) →ₗ[ℚ] (Fin q → ℚ))
    (hT : ∀ a h, h ∈ C.harmonic → T a h ∈ C.harmonic) :
    LinearMap.ker (faceMap (nodeCellRead C) T) = C.harmonic := by
  apply le_antisymm
  · intro v hv
    rw [mem_harmonic_iff_forall_nodeCell]
    intro c
    exact LinearMap.mem_ker.mp (ker_faceMap_le_ker T (nodeCellRead C) c hv)
  · refine le_ker_faceMap T (nodeCellRead C) (fun (_ : Unit) _ => ()) (fun _ => C.harmonic)
      (fun _ c => ?_) (fun _ a v hv => hT a v hv) ()
    intro v hv
    exact LinearMap.mem_ker.mpr ((mem_harmonic_iff_forall_nodeCell C v).mp hv c)

/-- [proved-derived; formal-checked] **The node/cell retention releases exactly the harmonic
modes**: two edge fields share every future node/cell reading exactly when they differ by a
harmonic mode. -/
theorem futureAgreement_nodeCell_iff {ι : Type} (T : ι → (Fin q → ℚ) →ₗ[ℚ] (Fin q → ℚ))
    (hT : ∀ a h, h ∈ C.harmonic → T a h ∈ C.harmonic) (left right : Fin q → ℚ) :
    futureAgreement (fun c y => nodeCellRead C c y) (fun a y => T a y) left right ↔
      left - right ∈ C.harmonic := by
  rw [← ker_faceMap_nodeCell C T hT]
  exact (sub_mem_ker_faceMap_iff T (nodeCellRead C) left right).symm

/-- [proved-derived; formal-checked] **The exact heat step fixes the harmonic modes**:
`(1 − τ Δ) h = h` for harmonic `h`. -/
theorem heatStep_fixes_harmonic (τ : ℚ) {h : Fin q → ℚ} (hh : h ∈ C.harmonic) :
    (1 - τ • C.laplacian) *ᵥ h = h := by
  change C.laplacian *ᵥ h = 0 at hh
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hh, smul_zero, sub_zero]

theorem heatStep_mem_harmonic (τ : ℚ) {h : Fin q → ℚ} (hh : h ∈ C.harmonic) :
    (1 - τ • C.laplacian) *ᵥ h ∈ C.harmonic := by
  rw [heatStep_fixes_harmonic C τ hh]
  exact hh

/-- [proved-derived; formal-checked] **Under the heat flow the node/cell receivers release exactly
the harmonic modes**: the dormant motion persists and is never read by them. -/
theorem heat_releases_harmonic (τ : ℚ) (left right : Fin q → ℚ) :
    futureAgreement (fun c y => nodeCellRead C c y)
        (fun (_ : Unit) y => Matrix.mulVecLin (1 - τ • C.laplacian) y) left right ↔
      left - right ∈ C.harmonic :=
  futureAgreement_nodeCell_iff C (fun _ => Matrix.mulVecLin (1 - τ • C.laplacian))
    (fun _ _ hh => heatStep_mem_harmonic C τ hh) left right

end Harmonic

/-! ## 4. The later-phase separator on the hollow triangle -/

namespace Triangle

open Matrix
open Holonics.Foundation.HodgeReceiver
open Holonics.Aeon.Production

/-- [definition] The receivers by phase on the hollow triangle (`HodgeTime.HollowTriangle`): every
node/cell receiver at every phase, and the cycle receiver (`none`), the harmonic clock
`HodgeTime.reading HodgeTime.loop`, admitted from phase 1 on. -/
def phaseRead (phase : ℕ) : Option (Fin 3 ⊕ Fin 0) → (Fin 3 → ℚ) → ℚ
  | some c, x => nodeCellRead HodgeTime.HollowTriangle.complex c x
  | none, x => if phase = 0 then 0 else HodgeTime.reading HodgeTime.loop x

/-- [definition] The clock: one action, one phase. -/
def tick (phase : ℕ) (_ : Unit) : ℕ := phase + 1

/-- [definition] The exact heat step at every phase. -/
def heat (τ : ℚ) (_ : ℕ) (_ : Unit) (x : Fin 3 → ℚ) : Fin 3 → ℚ :=
  (1 - τ • HodgeTime.HollowTriangle.complex.laplacian) *ᵥ x

theorem loop_harmonic : HodgeTime.loop ∈ HodgeTime.HollowTriangle.complex.harmonic :=
  HodgeTime.HollowTriangle.hollowTriangle_winding_not_boundary_determined.1

theorem heat_loop (τ : ℚ) (c : ℕ) (a : Unit) : heat τ c a HodgeTime.loop = HodgeTime.loop :=
  heatStep_fixes_harmonic HodgeTime.HollowTriangle.complex τ loop_harmonic

theorem heat_zero (τ : ℚ) (c : ℕ) (a : Unit) : heat τ c a 0 = 0 :=
  Matrix.mulVec_zero _

/-- [proved-derived; formal-checked] **The later-phase separator.** At phase 0 every receiver
reads the loop and zero alike; the node/cell receivers alone share their whole future under the
heat flow, so the node/cell retention releases the loop; yet the minimal standing of the clocked
lift keeps the two apart, because the harmonic clock admitted at phase 1 reads `3` against `0`. -/
theorem loop_later_phase_separator (τ : ℚ) :
    (∀ receiver, phaseRead 0 receiver HodgeTime.loop = phaseRead 0 receiver 0) ∧
      futureAgreement (fun c y => nodeCellRead HodgeTime.HollowTriangle.complex c y)
        (fun (_ : Unit) y =>
          Matrix.mulVecLin (1 - τ • HodgeTime.HollowTriangle.complex.laplacian) y)
        HodgeTime.loop 0 ∧
      ¬ futureAgreement (clockedObserve phaseRead) (clockedTransport tick (heat τ))
        (0, HodgeTime.loop) (0, 0) ∧
      (minimalStanding (clockedObserve phaseRead) (clockedTransport tick (heat τ))).retain
          (0, HodgeTime.loop) ≠
        (minimalStanding (clockedObserve phaseRead) (clockedTransport tick (heat τ))).retain
          (0, 0) := by
  have hwit := HodgeTime.HollowTriangle.hollowTriangle_winding_not_boundary_determined
  have hsep : ¬ futureAgreement (clockedObserve phaseRead) (clockedTransport tick (heat τ))
      (0, HodgeTime.loop) (0, 0) := by
    intro h
    have hread := h none [()]
    have hl : transportWord (clockedTransport tick (heat τ)) [()] ((0 : ℕ), HodgeTime.loop) =
        (1, HodgeTime.loop) :=
      Prod.ext rfl (heat_loop τ 0 ())
    have h0 : transportWord (clockedTransport tick (heat τ)) [()] ((0 : ℕ), (0 : Fin 3 → ℚ)) =
        (1, 0) :=
      Prod.ext rfl (heat_zero τ 0 ())
    rw [hl, h0] at hread
    norm_num [clockedObserve, phaseRead, hwit.2.2.2.1, hwit.2.2.2.2] at hread
  refine ⟨?_, ?_, hsep, ?_⟩
  · rintro (_ | c)
    · simp [phaseRead]
    · show nodeCellRead HodgeTime.HollowTriangle.complex c HodgeTime.loop =
        nodeCellRead HodgeTime.HollowTriangle.complex c 0
      rw [(mem_harmonic_iff_forall_nodeCell HodgeTime.HollowTriangle.complex
        HodgeTime.loop).mp loop_harmonic c, map_zero]
  · exact (heat_releases_harmonic HodgeTime.HollowTriangle.complex τ HodgeTime.loop 0).mpr
      (by rw [sub_zero]; exact loop_harmonic)
  · intro h
    exact hsep ((minimalStanding_isMinimal (clockedObserve phaseRead)
      (clockedTransport tick (heat τ))).retain_eq_iff.mp h)

end Triangle

end Holonics.Foundation.ChangingReceiverRetention

end
