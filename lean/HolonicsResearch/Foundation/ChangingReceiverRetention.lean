import HolonicsResearch.Foundation.ActionDescent
import Holonics.Foundation.HodgeReceiver
import Holonics.Aeon.Production.HodgeTime
import Holonics.Transport.ChangingReceiver.Defect
import HolonicsResearch.Foundation.CarriedRelease
import Mathlib.Tactic

/-!
# Retention and release through changing receivers

Object 8 of `docs/ELEMENTARY_OBJECTS.md` takes retention relative to the admitted future. When the
admitted receivers and actions themselves change from one phase to the next, the admitted future of
a present includes receivers that are not yet listening: a direction silent now may be read later,
and a retention that releases it at the present receivers has released what a later receiver needs.
This module proves that statement in three parts (#410, "Retention and release through changing
receivers"), then admits receivers by a later action and releases the defect's remainder at a
declared grain (#410, "Receivers admitted by a later action"). It builds on
`Foundation/ActionDescent` (the continuation square), `Foundation/MinimalRetention` (the minimal
standing), `Transport/ChangingReceiver/Defect` (the signed defect), `Foundation/CarriedRelease`
(the transported residue), `Foundation/HodgeReceiver`, `Compression/Core/FaceMap` and the hollow
triangle of `Aeon/Production/HodgeTime`, and restates none of them.

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

5. **Receivers admitted by a later action** (`actedTransport`, `admittedObserve`,
   `AdmittedSeparates`, `admittedObserve_eq_iff`, `present_or_admitted_separator`,
   `clocked_admittedFuture_iff`, `Triangle.loop_admission_separator`). An action moves the context
   by what it meets in the present, `next c a x`, so which receivers are admitted is a consequence
   of the passage, not of a clock. A receiver the context does not admit returns no reading, so
   whether it is reached is part of the receipt. Two presents every admitted receiver reads alike
   either share their whole admitted future, or a nonempty word returns a separator: a receiver
   admitted at one present and not the other, or admitted at both and reading them apart. When the
   context moves by the clock alone, admission never separates and the separator is always a
   reading. On the hollow triangle a contact on the cycle admits the cycle receiver where the
   harmonic clock reads a circulation: the dormant loop and zero are read alike by every admitted
   receiver at first and wherever both are admitted along every word, yet the contact reaches the
   cycle receiver at the loop and not at zero, and the minimal standing keeps them apart.
6. **The defect released into the receivers' kernel at a declared grain** (`streamWord`,
   `defectRelease`, `wordDefect_eq_linearOrbit`, `defectRelease_conserves`,
   `observe_eq_decode_remainder`, `phaseAgreement_of_defect_mem`, `defectRelease_unitGrain`).
   Along an action stream the word defect is the exact orbit of the moves driven by the step
   defects (`CarriedRelease.linearOrbit`), so the carried release (`CarriedRelease.residueRun`)
   splits it into a released part and a remainder that sum to it exactly, whatever the declared
   release rule. When the rule releases into a subgroup `K` that every decoder leaves unread and
   every move keeps (inside the relevance kernel of the encoded medium), the released part stays in
   `K` and every receiver reads the true present as its decoder reads the moved encoding plus the
   carried remainder. A defect released whole into `K` keeps the descent: two presents whose
   encodings differ by `K` share their whole admitted future (the vanishing defect is `K = 0`). At
   the unit grain, released by whole windings with moves that keep whole windings whole, the
   remainder stays inside one grain step and the phase receiver `R → R ⧸ ℤ` reads the true encoding
   through the moved encoding and the remainder.

The computational object is the helical pair interaction read by its admitted futures: the
receivers that read a contact change with the clock or are reached by the contact itself, and
retention keeps what any later receiver of the admitted family reads. Of the winding guide's six
general objects this touches the tube (the clocked span and its words), the cell holonomy (the
harmonic circulation a cycle receiver reads), the tower thread (the defect composed through the
levels' moves) and faces and placement (the defect released by whole windings, read at the phase
receiver's face); the helix and the pair stay attached.

Consumers: the atlas rows `retention.changing-receiver-phase`,
`cell.harmonic-release-later-separator`, `retention.action-admitted-separator` and
`retention.defect-release-kernel`, and #410.

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

/-! ## 5. Receivers admitted by a later action -/

section Admitted

variable {Ctx Action Receiver Source Face : Type*}

/-- [definition] **The acted transport**: an action moves the context by what it meets in the
present (`next c a x`) and the present by the context's own transport. The clocked transport is the
case where `next` does not read the present (`actedTransport_clock`). -/
def actedTransport (next : Ctx → Action → Source → Ctx)
    (transport : Ctx → Action → Source → Source) (a : Action) (p : Ctx × Source) : Ctx × Source :=
  (next p.1 a p.2, transport p.1 a p.2)

theorem actedTransport_clock (next : Ctx → Action → Ctx)
    (transport : Ctx → Action → Source → Source) :
    actedTransport (fun c a _ => next c a) transport = clockedTransport next transport := rfl

/-- [definition] **The admitted reading**: a receiver the context admits reads the present through
the context's chart, and a receiver it does not admit returns no reading, so whether a receiver is
reached is part of the receipt. -/
def admittedObserve (admits : Ctx → Receiver → Prop) [∀ c receiver, Decidable (admits c receiver)]
    (observe : Ctx → Receiver → Source → Face) (receiver : Receiver) (p : Ctx × Source) :
    Option Face :=
  if admits p.1 receiver then some (observe p.1 receiver p.2) else none

/-- [definition] **A receiver separates two presents** when it is admitted at one and not at the
other, or admitted at both and reads them apart. -/
def AdmittedSeparates (admits : Ctx → Receiver → Prop) (observe : Ctx → Receiver → Source → Face)
    (receiver : Receiver) (p q : Ctx × Source) : Prop :=
  ¬ (admits p.1 receiver ↔ admits q.1 receiver) ∨
    (admits p.1 receiver ∧ admits q.1 receiver ∧
      observe p.1 receiver p.2 ≠ observe q.1 receiver q.2)

/-- [proved-derived; formal-checked] Two admitted readings agree exactly when the receiver is
admitted at both or at neither, and reads alike wherever it is admitted at both. -/
theorem admittedObserve_eq_iff (admits : Ctx → Receiver → Prop)
    [∀ c receiver, Decidable (admits c receiver)] (observe : Ctx → Receiver → Source → Face)
    (receiver : Receiver) (p q : Ctx × Source) :
    admittedObserve admits observe receiver p = admittedObserve admits observe receiver q ↔
      (admits p.1 receiver ↔ admits q.1 receiver) ∧
        (admits p.1 receiver → admits q.1 receiver →
          observe p.1 receiver p.2 = observe q.1 receiver q.2) := by
  unfold admittedObserve
  by_cases hp : admits p.1 receiver <;> by_cases hq : admits q.1 receiver <;> simp [hp, hq]

theorem admittedObserve_ne_iff (admits : Ctx → Receiver → Prop)
    [∀ c receiver, Decidable (admits c receiver)] (observe : Ctx → Receiver → Source → Face)
    (receiver : Receiver) (p q : Ctx × Source) :
    admittedObserve admits observe receiver p ≠ admittedObserve admits observe receiver q ↔
      AdmittedSeparates admits observe receiver p q := by
  rw [Ne, admittedObserve_eq_iff, AdmittedSeparates]
  tauto

/-- [proved-derived; formal-checked] **Release, or the separator a later action returns**: two
presents in one context that every receiver admitted there reads alike either share their whole
admitted future, or a nonempty word reaches presents that a receiver separates, by its admission
or by its reading. -/
theorem present_or_admitted_separator (admits : Ctx → Receiver → Prop)
    [∀ c receiver, Decidable (admits c receiver)] (observe : Ctx → Receiver → Source → Face)
    (next : Ctx → Action → Source → Ctx) (transport : Ctx → Action → Source → Source) (c : Ctx)
    (left right : Source)
    (present : ∀ receiver, admits c receiver → observe c receiver left = observe c receiver right) :
    futureAgreement (admittedObserve admits observe) (actedTransport next transport) (c, left)
        (c, right) ∨
      ∃ word : List Action, word ≠ [] ∧ ∃ receiver,
        AdmittedSeparates admits observe receiver
          (transportWord (actedTransport next transport) word (c, left))
          (transportWord (actedTransport next transport) word (c, right)) := by
  by_cases h : futureAgreement (admittedObserve admits observe) (actedTransport next transport)
      (c, left) (c, right)
  · exact Or.inl h
  · right
    unfold futureAgreement at h
    push Not at h
    obtain ⟨receiver, word, hne⟩ := h
    refine ⟨word, ?_, receiver, (admittedObserve_ne_iff admits observe receiver _ _).mp hne⟩
    rintro rfl
    apply hne
    rw [transportWord_nil, transportWord_nil, admittedObserve_eq_iff]
    exact ⟨Iff.rfl, fun h _ => present receiver h⟩

/-- [proved-derived; formal-checked] **Under the clock, admission never separates**: when the
context moves by the clock alone, the admitted future of two presents in one context agrees
exactly when every receiver the clock admits reads them alike, so the separator is always a
reading. -/
theorem clocked_admittedFuture_iff (admits : Ctx → Receiver → Prop)
    [∀ c receiver, Decidable (admits c receiver)] (observe : Ctx → Receiver → Source → Face)
    (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source) (c : Ctx)
    (left right : Source) :
    futureAgreement (admittedObserve admits observe)
        (actedTransport (fun c a _ => next c a) transport) (c, left) (c, right) ↔
      ∀ receiver word, admits (transportWord (fun a c => next c a) word c) receiver →
        observe (transportWord (fun a c => next c a) word c) receiver
            (transportWord (clockedTransport next transport) word (c, left)).2 =
          observe (transportWord (fun a c => next c a) word c) receiver
            (transportWord (clockedTransport next transport) word (c, right)).2 := by
  rw [actedTransport_clock]
  unfold futureAgreement
  refine forall_congr' fun receiver => forall_congr' fun word => ?_
  rw [admittedObserve_eq_iff, clockedTransport_word_fst, clockedTransport_word_fst]
  exact ⟨fun h ha => h.2 ha ha, fun h => ⟨Iff.rfl, fun ha _ => h ha⟩⟩

end Admitted

namespace Triangle

open Matrix
open Holonics.Foundation.HodgeReceiver
open Holonics.Aeon.Production

/-- [definition] The contact on the hollow triangle admits the cycle receiver where it meets a
circulation: the context records whether the cycle receiver has been reached, and the action
`true` (a contact on the cycle) reaches it exactly when the harmonic clock reads the present as
nonzero. -/
def contactNext (reached : Bool) (contact : Bool) (x : Fin 3 → ℚ) : Bool :=
  reached || (contact && decide (HodgeTime.reading HodgeTime.loop x ≠ 0))

/-- [definition] The contact moves nothing; the other action is the exact heat step. -/
def contactMove (τ : ℚ) (_ : Bool) (contact : Bool) (x : Fin 3 → ℚ) : Fin 3 → ℚ :=
  if contact then x else heat τ 0 () x

/-- [definition] The node/cell receivers are admitted in every context; the cycle receiver
(`none`) only once a contact has reached it. -/
def contactAdmits (reached : Bool) (receiver : Option (Fin 3 ⊕ Fin 0)) : Prop :=
  receiver = none → reached = true

instance (reached : Bool) (receiver : Option (Fin 3 ⊕ Fin 0)) :
    Decidable (contactAdmits reached receiver) :=
  inferInstanceAs (Decidable (receiver = none → reached = true))

/-- [definition] The readings: node/cell receivers as in `nodeCellRead`, the cycle receiver as
the harmonic clock. -/
def contactRead (_ : Bool) (receiver : Option (Fin 3 ⊕ Fin 0)) (x : Fin 3 → ℚ) : ℚ :=
  match receiver with
  | some c => nodeCellRead HodgeTime.HollowTriangle.complex c x
  | none => HodgeTime.reading HodgeTime.loop x

theorem contact_loop_word (τ : ℚ) (word : List Bool) :
    (transportWord (actedTransport contactNext (contactMove τ)) word (false, HodgeTime.loop)).2 =
      HodgeTime.loop := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    rw [transportWord_cons]
    simp only [actedTransport, contactMove, ih]
    split_ifs
    · rfl
    · exact heat_loop τ 0 ()

theorem contact_zero_word (τ : ℚ) (word : List Bool) :
    transportWord (actedTransport contactNext (contactMove τ)) word (false, 0) = (false, 0) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    rw [transportWord_cons, ih]
    have h0 := HodgeTime.HollowTriangle.hollowTriangle_winding_not_boundary_determined.2.2.2.2
    refine Prod.ext ?_ ?_
    · simp [actedTransport, contactNext, h0]
    · simp only [actedTransport, contactMove]
      split_ifs
      · rfl
      · exact heat_zero τ 0 ()

/-- [proved-derived; formal-checked] **The separator a contact returns is an admission.** At
first every admitted receiver reads the dormant loop and zero alike, and along every word every
receiver admitted at both reads them alike; yet a contact on the cycle reaches the cycle receiver
at the loop and not at zero, so the two do not share their admitted future and the minimal standing
of the acted lift keeps them apart. No clock returns this separator
(`clocked_admittedFuture_iff`). -/
theorem loop_admission_separator (τ : ℚ) :
    (∀ receiver, admittedObserve contactAdmits contactRead receiver (false, HodgeTime.loop) =
      admittedObserve contactAdmits contactRead receiver (false, 0)) ∧
      (∀ word receiver,
        contactAdmits (transportWord (actedTransport contactNext (contactMove τ)) word
            (false, HodgeTime.loop)).1 receiver →
          contactAdmits (transportWord (actedTransport contactNext (contactMove τ)) word
            (false, 0)).1 receiver →
          contactRead false receiver
              (transportWord (actedTransport contactNext (contactMove τ)) word
                (false, HodgeTime.loop)).2 =
            contactRead false receiver
              (transportWord (actedTransport contactNext (contactMove τ)) word (false, 0)).2) ∧
      ¬ (contactAdmits (transportWord (actedTransport contactNext (contactMove τ)) [true]
            (false, HodgeTime.loop)).1 none ↔
          contactAdmits (transportWord (actedTransport contactNext (contactMove τ)) [true]
            (false, 0)).1 none) ∧
      ¬ futureAgreement (admittedObserve contactAdmits contactRead)
          (actedTransport contactNext (contactMove τ)) (false, HodgeTime.loop) (false, 0) ∧
      (minimalStanding (admittedObserve contactAdmits contactRead)
          (actedTransport contactNext (contactMove τ))).retain (false, HodgeTime.loop) ≠
        (minimalStanding (admittedObserve contactAdmits contactRead)
          (actedTransport contactNext (contactMove τ))).retain (false, 0) := by
  have hwit := HodgeTime.HollowTriangle.hollowTriangle_winding_not_boundary_determined
  have hnode : ∀ c, nodeCellRead HodgeTime.HollowTriangle.complex c HodgeTime.loop =
      nodeCellRead HodgeTime.HollowTriangle.complex c 0 := fun c => by
    rw [(mem_harmonic_iff_forall_nodeCell HodgeTime.HollowTriangle.complex
      HodgeTime.loop).mp loop_harmonic c, map_zero]
  have hadmit : ¬ (contactAdmits (transportWord (actedTransport contactNext (contactMove τ))
        [true] (false, HodgeTime.loop)).1 none ↔
      contactAdmits (transportWord (actedTransport contactNext (contactMove τ)) [true]
        (false, 0)).1 none) := by
    simp [contactAdmits, actedTransport, contactNext, hwit.2.2.2.1, hwit.2.2.2.2]
  have hsep : ¬ futureAgreement (admittedObserve contactAdmits contactRead)
      (actedTransport contactNext (contactMove τ)) (false, HodgeTime.loop) (false, 0) := by
    intro h
    have := (admittedObserve_eq_iff contactAdmits contactRead none _ _).mp (h none [true])
    exact hadmit this.1
  refine ⟨?_, ?_, hadmit, hsep, ?_⟩
  · rintro (_ | c)
    · simp [admittedObserve, contactAdmits]
    · simp only [admittedObserve, contactAdmits, reduceCtorEq, IsEmpty.forall_iff, if_true]
      exact congrArg some (hnode c)
  · intro word receiver _ hr
    rw [contact_zero_word] at hr ⊢
    rw [contact_loop_word]
    cases receiver with
    | none => exact absurd (hr rfl) Bool.false_ne_true
    | some c => exact hnode c
  · intro h
    exact hsep ((minimalStanding_isMinimal (admittedObserve contactAdmits contactRead)
      (actedTransport contactNext (contactMove τ))).retain_eq_iff.mp h)

end Triangle

/-! ## 6. The defect released into the receivers' kernel at a declared grain -/

section Release

open Holonics.Aeon.Clock.Winding

variable {Ctx Action Source Q : Type*} [AddCommGroup Q]

/-- [definition] **The word of an action stream** up to step `t`, the latest action first, as
`transportWord` reads a word. -/
def streamWord (act : ℕ → Action) : ℕ → List Action
  | 0 => []
  | t + 1 => act t :: streamWord act t

/-- [definition] The phase an action stream has reached at step `k`. -/
def streamPhase (next : Ctx → Action → Ctx) (act : ℕ → Action) (c : Ctx) (k : ℕ) : Ctx :=
  transportWord (fun a c => next c a) (streamWord act k) c

/-- [definition] The present an action stream has reached at step `k`. -/
def streamState (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (act : ℕ → Action) (c : Ctx) (x : Source) (k : ℕ) : Source :=
  (transportWord (clockedTransport next transport) (streamWord act k) (c, x)).2

/-- [definition] **The defect release**: the step defects along the stream, each taken at the
phase and present reached, moved by the moves and released by the declared rule `rel` with the
remainder carried (`CarriedRelease.residueRun`). -/
def defectRelease (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (encode : Ctx → Source → Q) (move : Ctx → Action → Q →+ Q) (rel : Q → Q) (act : ℕ → Action)
    (c : Ctx) (x : Source) : ℕ → Q × Q :=
  residueRun (fun k => move (streamPhase next act c k) (act k))
    (fun k => stepDefect next transport encode (fun c a => move c a) (streamPhase next act c k)
      (act k) (streamState next transport act c x k)) rel

/-- [proved-derived; formal-checked] **The word defect is the exact orbit of the moves driven by
the step defects** (`CarriedRelease.linearOrbit`). -/
theorem wordDefect_eq_linearOrbit (next : Ctx → Action → Ctx)
    (transport : Ctx → Action → Source → Source) (encode : Ctx → Source → Q)
    (move : Ctx → Action → Q →+ Q) (act : ℕ → Action) (c : Ctx) (x : Source) (t : ℕ) :
    wordDefect next transport encode (fun c a => move c a) (streamWord act t) c x =
      linearOrbit (fun k => move (streamPhase next act c k) (act k))
        (fun k => stepDefect next transport encode (fun c a => move c a)
          (streamPhase next act c k) (act k) (streamState next transport act c x k)) t := by
  induction t with
  | zero => exact wordDefect_nil next transport encode _ c x
  | succ t ih =>
    rw [streamWord, wordDefect_cons, ih, linearOrbit, add_comm]
    rfl

/-- [proved-derived; formal-checked] **The released defect and its remainder are the word
defect**, whatever the declared release rule: nothing of the defect is lost. -/
theorem defectRelease_conserves (next : Ctx → Action → Ctx)
    (transport : Ctx → Action → Source → Source) (encode : Ctx → Source → Q)
    (move : Ctx → Action → Q →+ Q) (rel : Q → Q) (act : ℕ → Action) (c : Ctx) (x : Source)
    (t : ℕ) :
    (defectRelease next transport encode move rel act c x t).1 +
        (defectRelease next transport encode move rel act c x t).2 =
      wordDefect next transport encode (fun c a => move c a) (streamWord act t) c x := by
  rw [wordDefect_eq_linearOrbit]
  exact residueRun_conserves _ _ rel t

variable {Receiver Face : Type*} [AddCommGroup Face]

/-- [proved-derived; formal-checked] **The defect released into the receivers' kernel costs no
reading.** Let `K` be a subgroup every decoder leaves unread and every move keeps (so no admitted
future of the encoded medium reads it), and let the declared rule release into `K`. Then the
released part stays in `K`, and every receiver reads the true present after the stream as its
decoder reads the moved encoding plus the carried remainder. -/
theorem observe_eq_decode_remainder (observe : Ctx → Receiver → Source → Face)
    (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (encode : Ctx → Source → Q) (D : Ctx → Receiver → Q →+ Face) (move : Ctx → Action → Q →+ Q)
    (hdecode : ∀ c receiver x, D c receiver (encode c x) = observe c receiver x)
    (K : AddSubgroup Q) (hker : ∀ c receiver k, k ∈ K → D c receiver k = 0)
    (hkeep : ∀ c a k, k ∈ K → move c a k ∈ K) (rel : Q → Q) (hrel : ∀ y, rel y ∈ K)
    (act : ℕ → Action) (c : Ctx) (x : Source) (t : ℕ) (receiver : Receiver) :
    (defectRelease next transport encode move rel act c x t).1 ∈ K ∧
      observe (streamPhase next act c t) receiver (streamState next transport act c x t) =
        D (streamPhase next act c t) receiver
          ((transportWord (clockedTransport next (fun c a => move c a)) (streamWord act t)
              (c, encode c x)).2 +
            (defectRelease next transport encode move rel act c x t).2) := by
  have hmem : (defectRelease next transport encode move rel act c x t).1 ∈ K :=
    residueRun_fst_mem _ _ rel K hrel (fun k y hy => hkeep _ _ y hy) t
  refine ⟨hmem, ?_⟩
  have hc := defectRelease_conserves next transport encode move rel act c x t
  rw [wordDefect, clockedTransport_word_fst] at hc
  rw [← hdecode, streamState, streamPhase, eq_add_of_sub_eq' hc.symm]
  rw [map_add, map_add, hker _ _ _ hmem, zero_add, map_add]

/-- [proved-derived; formal-checked] **A defect released whole into the receivers' kernel keeps
the descent**: when every step defect lies in a subgroup that every decoder leaves unread and
every move keeps, two presents whose encodings differ by that subgroup share their whole admitted
future from their phase. The vanishing defect (`phaseAgreement_of_encode_eq`) is the case of the
zero subgroup. -/
theorem phaseAgreement_of_defect_mem (observe : Ctx → Receiver → Source → Face)
    (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (encode : Ctx → Source → Q) (D : Ctx → Receiver → Q →+ Face) (move : Ctx → Action → Q →+ Q)
    (hdecode : ∀ c receiver x, D c receiver (encode c x) = observe c receiver x)
    (K : AddSubgroup Q) (hker : ∀ c receiver k, k ∈ K → D c receiver k = 0)
    (hkeep : ∀ c a k, k ∈ K → move c a k ∈ K)
    (hδ : ∀ c a x, stepDefect next transport encode (fun c a => move c a) c a x ∈ K) {c : Ctx}
    {left right : Source} (h : encode c left - encode c right ∈ K) :
    futureAgreement (clockedObserve observe) (clockedTransport next transport) (c, left)
      (c, right) := by
  have hword : ∀ word : List Action,
      encode (transportWord (fun a c => next c a) word c)
          (transportWord (clockedTransport next transport) word (c, left)).2 -
        encode (transportWord (fun a c => next c a) word c)
          (transportWord (clockedTransport next transport) word (c, right)).2 ∈ K := by
    intro word
    induction word with
    | nil => exact h
    | cons a word ih =>
      set p := transportWord (fun a c => next c a) word c
      have hl := hδ p a (transportWord (clockedTransport next transport) word (c, left)).2
      have hr := hδ p a (transportWord (clockedTransport next transport) word (c, right)).2
      simp only [stepDefect, defect] at hl hr
      have hm := hkeep p a _ ih
      rw [map_sub] at hm
      have hsum := K.add_mem (K.sub_mem hl hr) hm
      simp only [transportWord_cons, clockedTransport, clockedTransport_word_fst]
      convert hsum using 1
      abel
  intro receiver word
  simp only [clockedObserve, clockedTransport_word_fst]
  rw [← hdecode, ← hdecode, ← sub_eq_zero, ← map_sub]
  exact hker _ _ _ (hword word)

/-- [proved-derived; formal-checked] **At the unit grain** (`CarriedRelease.residueRun_windings`):
on a line whose moves keep whole windings whole, the defect released by whole windings puts whole
windings in the phase receiver's kernel and keeps its remainder inside one grain step, and the
phase receiver `R → R ⧸ ℤ` reads the true encoding after the stream as the moved encoding plus the
remainder. A grain `g > 0` is the unit grain of `x / g`. -/
theorem defectRelease_unitGrain {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] (next : Ctx → Action → Ctx) (transport : Ctx → Action → Source → Source)
    (encode : Ctx → Source → R) (move : Ctx → Action → R →+ R)
    (hkeep : ∀ c a y, y ∈ AddSubgroup.zmultiples (1 : R) →
      move c a y ∈ AddSubgroup.zmultiples (1 : R))
    (act : ℕ → Action) (c : Ctx) (x : Source) (t : ℕ) :
    (defectRelease next transport encode move (fun y => (windings y : R)) act c x t).1 ∈
        AddSubgroup.zmultiples (1 : R) ∧
      0 ≤ (defectRelease next transport encode move (fun y => (windings y : R)) act c x t).2 ∧
      (defectRelease next transport encode move (fun y => (windings y : R)) act c x t).2 < 1 ∧
      QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : R))
          (encode (streamPhase next act c t) (streamState next transport act c x t)) =
        QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : R))
          ((transportWord (clockedTransport next (fun c a => move c a)) (streamWord act t)
              (c, encode c x)).2 +
            (defectRelease next transport encode move (fun y => (windings y : R)) act c x t).2) := by
  obtain ⟨hmem, h0, h1, -⟩ := residueRun_windings _ _ (fun k y hy => hkeep _ _ y hy) t
  refine ⟨hmem, h0, h1, ?_⟩
  exact (observe_eq_decode_remainder (fun c (_ : Unit) y => QuotientAddGroup.mk'
      (AddSubgroup.zmultiples (1 : R)) (encode c y)) next transport encode
    (fun _ _ => QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : R))) move (fun _ _ _ => rfl)
    (AddSubgroup.zmultiples (1 : R)) (fun _ _ k hk => (QuotientAddGroup.eq_zero_iff k).mpr hk)
    hkeep (fun y => (windings y : R)) (fun y => ⟨windings y, by simp⟩) act c x t ()).2

end Release

end Holonics.Foundation.ChangingReceiverRetention

end
