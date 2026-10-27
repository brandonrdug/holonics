import Holonics.HNN.Encoding
import Holonics.Compression.Core.FaceMap
import HolonicsResearch.Foundation.MinimalRetention
import Mathlib.Tactic

/-!
# Action-sufficient descent: the continuation square

Object 8 of `docs/ELEMENTARY_OBJECTS.md`: for an acting receiver the admitted future includes its
actions, and retention is the **action-sufficient** quotient, `h ∼ h'` exactly when every admitted
receiver reads alike after every admitted action word. A retention that the machine keeps running
must also *descend*: each action has to act on the retained value itself, with the encoding allowed
to change from one context to the next. Those are the decoding and continuation squares

```text
D_(c,R) E_c = ρ_R                    (decoding square, every context c and receiver R)
E_(next c a) T_a = U_(c,a) E_c       (continuation square, every context c and action a)
```

This module proves what they give and when they hold (#410, "Action-sufficient descent"). It
builds on `Foundation/Standing/Law` (`StandingLaw`, `standingLaw_exists_iff_future_factors`),
`Foundation/CausalRelevance` (`futureAgreement`, `futureAgreement_is_greatest_stable`),
`Foundation/MinimalRetention` (the Nerode machine and the linear chart), `HNN/Encoding`
(`factor_of_ker_le`, `encoding_descends_iff`), `Compression/Core/FaceMap` (the relevance kernel)
and Birth's founded forms, and restates none of them.

[proved-derived; formal-checked] What is proved.

1. **The squares descend every admitted action word** (`Descent`, `Descent.encode_word`,
   `Descent.standing`, `Descent.futureAgreement_of_encode_eq`). A descent carries decoders
   `D_(c,R)`, moves `U_(c,a)` and a context step `next`. Running the moves through the contexts
   reproduces the encoding after any word, `E_(c·w) (T_w x) = U_w (E_c x)`, so the encoding is a
   standing that reopens every future from the retained value and its context, with no source,
   no choice and no record; two presents an encoding merges share their whole admitted future.
   The minimal quotient is a descent with one context (`minimalDescent`), and so is every
   `Foundation/ReceiverHistoryCompression` (`ofHistoryCompression`), whose quotient commutes with
   the generators: descent is that object with the encoding allowed to change between contexts.
2. **When descent holds, and the separating remainder when it fails** (`nonempty_descent_iff`,
   `descent_or_separator`). Decoders and moves exist exactly when, in every context, two presents
   the encoding merges read alike under every receiver and stay merged under every action into the
   next context. Otherwise a separator is returned: a context and two merged presents that a
   receiver reads apart or an action carries apart.
3. **Sufficiency is decoding and continuing into the minimal quotient** (`futures_factor_iff`).
   A retention suffices for the admitted future exactly when every reading factors through it and
   every one-step continuation of the future-agreement class does. It need not continue into
   itself: `Control.sufficient_not_self_continuing` keeps a bit no future reads, and the action
   carries that bit into the forgotten one, so no move exists; being sufficient, it still
   continues into the minimal quotient. Descent is restored by changing the encoding at the next
   context (the continuation square's `E_(next c a)`), here to the minimal quotient.
4. **The linear chart** (`sub_mem_ker_faceMap_iff`, `ker_faceMap_le_ker`, `le_ker_faceMap`).
   Over a field, with linear transports `T_a` and receiving forms `ρ_R`, the action-sufficient
   quotient is the quotient by `Compression/Core/FaceMap`'s relevance kernel
   `𝒩 = ker F = ⋂_(w,R) ker (ρ_R T_w)`, the difference of future-sharing states; `FaceMap` proves
   that every action keeps it and that its quotient is the coarsest retention, with the actions
   descended to it. Here: it lies in every `ker ρ_R`, and every family of subspaces `P_c` with
   `P_c ≤ ker ρ_R` and `T_a P_c ≤ P_(next c a)` lies inside it; with one context, `𝒩` is the
   greatest subspace of `⋂ ker ρ_R` that every admitted action keeps, the admitted-family form of
   `Objects/RelativeCompleteness.observabilityKernel_greatest`.
5. **The linear squares and their remainder** (`linear_descent_iff`, `linear_descent_or_remainder`,
   `ker_le_ker_faceMap_of_descent`). Linear decoders and moves exist exactly when
   `ker E_c ≤ ker ρ_R` and `T_a ker E_c ≤ ker E_(next c a)`; otherwise some context holds a merged
   direction `v`, `E_c v = 0`, that a receiver reads or an action carries out of the next kernel,
   the separating direction a founding step keeps. Under the squares every `ker E_c ≤ 𝒩`. This is
   `HNN/Encoding.encoding_separator` and `encoding_descends_iff` with the encoding changing between
   contexts.
6. **Sufficient linear retentions** (`ker_le_ker_faceMap_iff`, `continues_into_minimal`).
   `ker E ≤ 𝒩` exactly when `ker E ≤ ker ρ_R` for every receiver and `T_a ker E ≤ 𝒩` for every
   action: the two-context descent `E → M` with `ker M = 𝒩`. Such an `E` has decoders
   `ρ_R = D_R E` and moves `M T_a = U_a E` into every minimal chart `M`.
7. **The founded chart** (`ker_faceMap_eq_dualCoannihilator`, `founded_reads_through`,
   `founded_restrict_eq_span`). In finite dimension `𝒩` is what Birth's founded forms leave unread,
   so each founded form reads through every sufficient retention, and so through every linear
   descent: the minimal chart is a quotient of each of them. On a reached span `R` the founded
   forms restrict to the span of the restricted readings `ρ ∘ T_w |_R`.

[open] The changing receiver/action defect, where the admitted receivers or actions themselves
change between contexts, is #410's "Retention and release through changing receivers". Here the
receivers and the actions are fixed and only the encoding changes.

The computational object is the helical pair interaction read by its admitted futures: a receiver
reads a contact after an ordered word of navigator moves, and descent is the retained machine that
keeps answering those reads as the moves arrive. Of the winding guide's six general objects this
touches the tube (contexts and words as the clocked span) and the tower thread (the decoding square
is what the next level reads); the helix, the pair, faces and placement and the cell holonomy stay
attached.

Consumers: the atlas rows `retention.action-sufficient-quotient`, `retention.continuation-square`,
`retention.linear-continuation-square` and `encoding.minimal-realization`, and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.ActionDescent

open Holonics.Foundation.Chronology
open Holonics.Foundation.CausalRelevance.NonLinear
open Holonics.Foundation.Standing
open Holonics.Foundation.MinimalRetention
open Holonics.Foundation.LineageCompression

universe u

/-! ## 1. Descent with changing encodings -/

section Abstract

variable {Ctx Action Receiver Source Retained Face : Type*}

/-- [definition] **Action-sufficient descent**: decoders `D_(c,R)` with `D_(c,R) E_c = ρ_R` and
moves `U_(c,a)` with `E_(next c a) T_a = U_(c,a) E_c`, the encoding `E_c` changing with the
context `c`. -/
structure Descent (observe : Receiver → Source → Face) (transport : Action → Source → Source)
    (next : Ctx → Action → Ctx) (encode : Ctx → Source → Retained) where
  /-- The decoder of each receiver in each context. -/
  decode : Ctx → Receiver → Retained → Face
  /-- The move each action performs on the retained value in each context. -/
  move : Ctx → Action → Retained → Retained
  /-- The decoding square `D_(c,R) E_c = ρ_R`. -/
  decode_square : ∀ c receiver x, decode c receiver (encode c x) = observe receiver x
  /-- The continuation square `E_(next c a) T_a = U_(c,a) E_c`. -/
  move_square : ∀ c a x, encode (next c a) (transport a x) = move c a (encode c x)

/-- A word moves a present and its context together, the rightmost letter first. -/
theorem transportWord_pair (transport : Action → Source → Source) (next : Ctx → Action → Ctx)
    (word : List Action) (c : Ctx) (x : Source) :
    transportWord (fun a (p : Ctx × Source) => (next p.1 a, transport a p.2)) word (c, x) =
      (transportWord (fun a c => next c a) word c, transportWord transport word x) := by
  induction word with
  | nil => rfl
  | cons _ word ih => simp only [transportWord_cons, ih]

namespace Descent

variable {observe : Receiver → Source → Face} {transport : Action → Source → Source}
  {next : Ctx → Action → Ctx} {encode : Ctx → Source → Retained}
  (D : Descent observe transport next encode)

/-- [definition] The descended move on a retained value marked with its context. -/
def pairMove (a : Action) (p : Ctx × Retained) : Ctx × Retained :=
  (next p.1 a, D.move p.1 a p.2)

/-- [proved-derived; formal-checked] **The squares descend every word**: running the moves
through the contexts reproduces the encoding after the word, `E_(c·w) (T_w x) = U_w (E_c x)`. -/
theorem encode_word (word : List Action) (c : Ctx) (x : Source) :
    transportWord D.pairMove word (c, encode c x) =
      (transportWord (fun a c => next c a) word c,
        encode (transportWord (fun a c => next c a) word c) (transportWord transport word x)) := by
  have h := generatorEquivarianceExtendsToEveryTransportWord
    (fun a (p : Ctx × Source) => (next p.1 a, transport a p.2)) D.pairMove
    (fun p => (p.1, encode p.1 p.2)) (fun a p => by simp only [pairMove, D.move_square]) word (c, x)
  rw [transportWord_pair] at h
  exact h.symm

/-- [definition] **The descended standing** from a start context `c₀`: retain `(c₀, E_(c₀) x)`,
and reopen a receiver after a word by running the moves through the contexts and decoding. -/
def standing (c₀ : Ctx) : StandingLaw Action Receiver Source (Ctx × Retained) Face where
  transport := transport
  observe := observe
  retain x := (c₀, encode c₀ x)
  reopen receiver word p :=
    D.decode (transportWord D.pairMove word p).1 receiver (transportWord D.pairMove word p).2
  sufficient receiver word x := by
    simp only [D.encode_word, D.decode_square]

/-- [proved-derived; formal-checked] **A descending encoding is action-sufficient**: two presents
it merges in any context share their whole admitted future. -/
theorem futureAgreement_of_encode_eq {c : Ctx} {left right : Source}
    (h : encode c left = encode c right) : futureAgreement observe transport left right :=
  (D.standing c).futureAgreement_of_retain_eq
    (show (c, encode c left) = (c, encode c right) by rw [h])

end Descent

/-- [definition] **One context recovers the commuting quotient**: a
`Foundation/ReceiverHistoryCompression` (present factorization and generators commuting with the
quotient, as `FaceMap.kernelHistoryCompression` for the linear relevance kernel) is a descent with
one context. -/
def ofHistoryCompression (H : ReceiverHistoryCompression Action Receiver Source Retained Face) :
    Descent H.present.receiver H.sourceTransport (fun (_ : Unit) _ => ())
      (fun _ => H.present.quotient) where
  decode _ := H.present.factor
  move _ := H.quotientTransport
  decode_square _ receiver x := H.present.exact receiver x
  move_square _ a x := H.generatorExact a x

/-- [definition] **The minimal quotient descends**: the Nerode machine of
`Foundation/MinimalRetention` is a descent with one context. -/
def minimalDescent (observe : Receiver → Source → Face) (transport : Action → Source → Source) :
    Descent observe transport (fun (_ : Unit) _ => ())
      (fun _ => Quotient.mk (futureSetoid observe transport)) where
  decode _ receiver := minimalFace observe transport receiver
  move _ a := minimalMove observe transport a
  decode_square _ _ _ := rfl
  move_square _ _ _ := rfl

/-- [proved-derived; formal-checked] **Descent holds exactly when no separator exists**: decoders
and moves exist exactly when, in every context, two presents the encoding merges read alike under
every receiver and stay merged under every action into the next context. -/
theorem nonempty_descent_iff [Nonempty Face] (observe : Receiver → Source → Face)
    (transport : Action → Source → Source) (next : Ctx → Action → Ctx)
    (encode : Ctx → Source → Retained) :
    Nonempty (Descent observe transport next encode) ↔
      ∀ c left right, encode c left = encode c right →
        (∀ receiver, observe receiver left = observe receiver right) ∧
          ∀ a, encode (next c a) (transport a left) = encode (next c a) (transport a right) := by
  constructor
  · rintro ⟨D⟩ c left right h
    refine ⟨fun receiver => ?_, fun a => ?_⟩
    · rw [← D.decode_square c receiver left, ← D.decode_square c receiver right, h]
    · rw [D.move_square, D.move_square, h]
  · intro h
    exact ⟨{
      decode := fun c receiver =>
        Function.extend (encode c) (observe receiver) fun _ => Classical.arbitrary Face
      move := fun c a =>
        Function.extend (encode c) (fun x => encode (next c a) (transport a x)) id
      decode_square := fun c receiver x =>
        Function.FactorsThrough.extend_apply (f := encode c) (g := observe receiver)
          (fun ⦃left right⦄ hlr => (h c left right hlr).1 receiver) _ x
      move_square := fun c a x =>
        (Function.FactorsThrough.extend_apply (f := encode c)
          (g := fun x => encode (next c a) (transport a x))
          (fun ⦃left right⦄ hlr => (h c left right hlr).2 a) id x).symm }⟩

/-- [proved-derived; formal-checked] **Descent, or the separating remainder**: either the squares
hold, or some context has two merged presents that a receiver reads apart or an action carries
apart. -/
theorem descent_or_separator [Nonempty Face] (observe : Receiver → Source → Face)
    (transport : Action → Source → Source) (next : Ctx → Action → Ctx)
    (encode : Ctx → Source → Retained) :
    Nonempty (Descent observe transport next encode) ∨
      ∃ c left right, encode c left = encode c right ∧
        ((∃ receiver, observe receiver left ≠ observe receiver right) ∨
          ∃ a, encode (next c a) (transport a left) ≠ encode (next c a) (transport a right)) := by
  rw [nonempty_descent_iff]
  by_cases h : ∃ c left right, encode c left = encode c right ∧
      ((∃ receiver, observe receiver left ≠ observe receiver right) ∨
        ∃ a, encode (next c a) (transport a left) ≠ encode (next c a) (transport a right))
  · exact Or.inr h
  · left
    push Not at h
    exact h

/-- [proved-derived; formal-checked] **A retention suffices exactly when it decodes and continues
into the minimal quotient**: every admitted future factors through `E` exactly when every reading
does and every one-step continuation of the future-agreement class does. -/
theorem futures_factor_iff (observe : Receiver → Source → Face)
    (transport : Action → Source → Source) (E : Source → Retained) :
    (∀ left right, E left = E right → futureAgreement observe transport left right) ↔
      (∀ left right, E left = E right →
          ∀ receiver, observe receiver left = observe receiver right) ∧
        ∀ left right, E left = E right → ∀ a,
          Quotient.mk (futureSetoid observe transport) (transport a left) =
            Quotient.mk (futureSetoid observe transport) (transport a right) := by
  constructor
  · intro h
    refine ⟨fun left right hlr receiver => h left right hlr receiver [],
      fun left right hlr a => ?_⟩
    exact Quotient.sound (futureAgreement_preserved_by_step observe transport (h left right hlr) a)
  · rintro ⟨hread, hmove⟩ left right hlr
    refine futureAgreement_is_greatest_stable observe transport
      (fun x y => E x = E y ∨ futureAgreement observe transport x y) ?_ ?_ left right (Or.inl hlr)
    · rintro x y (hxy | hxy) receiver
      · exact hread x y hxy receiver
      · exact hxy receiver []
    · rintro a x y (hxy | hxy)
      · exact Or.inr (Quotient.exact (hmove x y hxy a))
      · exact Or.inr (futureAgreement_preserved_by_step observe transport hxy a)

/-! ### A sufficient retention that does not continue into itself -/

namespace Control

/-- The receiver reads the first of three bits. -/
def readFirst (_ : Unit) (x : Bool × Bool × Bool) : Bool := x.1

/-- The one action exchanges the second and third bits. -/
def exchange (_ : Unit) (x : Bool × Bool × Bool) : Bool × Bool × Bool := (x.1, x.2.2, x.2.1)

/-- A retention that keeps the read bit and the third bit, and forgets the second. -/
def keep (x : Bool × Bool × Bool) : Bool × Bool := (x.1, x.2.2)

theorem first_transportWord (word : List Unit) (x : Bool × Bool × Bool) :
    (transportWord exchange word x).1 = x.1 := by
  induction word with
  | nil => rfl
  | cons _ word ih => exact ih

/-- [proved-derived; formal-checked] **A sufficient retention need not continue into itself**:
`keep` merges only presents with one future, yet no move `U` has `keep ∘ exchange = U ∘ keep`.
The bit it keeps is never read, and the exchange carries it into the forgotten one. -/
theorem sufficient_not_self_continuing :
    (∀ left right, keep left = keep right → futureAgreement readFirst exchange left right) ∧
      ¬ ∃ U : Bool × Bool → Bool × Bool, ∀ x, keep (exchange () x) = U (keep x) := by
  refine ⟨fun left right h receiver word => ?_, ?_⟩
  · show (transportWord exchange word left).1 = (transportWord exchange word right).1
    rw [first_transportWord, first_transportWord]
    exact congrArg Prod.fst h
  · rintro ⟨U, hU⟩
    have h1 := hU (false, false, false)
    have h2 := hU (false, true, false)
    simp only [keep, exchange] at h1 h2
    exact absurd (h2.trans h1.symm) (by decide)

end Control

end Abstract

/-! ## 2. The linear chart -/

section Linear

open Module
open Holonics.Compression.Landmark.Context.Birth
open Holonics.Compression.Core.FaceMap
open Holonics.HNN.Encoding

variable {K X ι C : Type u} [Field K] [AddCommGroup X] [Module K X] {Q Ctx : Type*}
  [AddCommGroup Q] [Module K Q]

/-- [proved-derived; formal-checked] **Future agreement is agreement modulo the relevance kernel**
`𝒩 = ker F` of the face map `F x (R, w) = ρ_R (T_w x)` (`FaceMap.kernelQuotient_eq_iff_futureAgreement`
read on differences). -/
theorem sub_mem_ker_faceMap_iff (T : ι → X →ₗ[K] X) (read : C → Dual K X) (left right : X) :
    left - right ∈ LinearMap.ker (faceMap read T) ↔
      futureAgreement (fun r y => read r y) (fun g y => T g y) left right := by
  rw [← kernelQuotient_eq_iff_futureAgreement read T left right, Submodule.mkQ_apply,
    Submodule.mkQ_apply,
    Submodule.Quotient.eq]

/-- [proved-derived; formal-checked] The relevance kernel lies in every receiver's kernel. -/
theorem ker_faceMap_le_ker (T : ι → X →ₗ[K] X) (read : C → Dual K X) (r : C) :
    LinearMap.ker (faceMap read T) ≤ LinearMap.ker (read r) := by
  intro v hv
  have h := (sub_mem_ker_faceMap_iff T read v 0).mp (by rwa [sub_zero]) r []
  rw [LinearMap.mem_ker]
  simpa using h

/-- [proved-derived; formal-checked] **Every kernel family the receivers ignore and the actions
carry lies in the relevance kernel**: if `P_c ≤ ker ρ_R` and `T_a P_c ≤ P_(next c a)`, every
`P_c ≤ 𝒩`. With one context, `𝒩` is the greatest subspace of `⋂ ker ρ_R` every admitted action
keeps (the admitted-family form of `Objects/RelativeCompleteness.observabilityKernel_greatest`). -/
theorem le_ker_faceMap (T : ι → X →ₗ[K] X) (read : C → Dual K X) (next : Ctx → ι → Ctx)
    (P : Ctx → Submodule K X) (hread : ∀ c r, P c ≤ LinearMap.ker (read r))
    (hmove : ∀ c a v, v ∈ P c → T a v ∈ P (next c a)) (c : Ctx) :
    P c ≤ LinearMap.ker (faceMap read T) := by
  intro v hv
  rw [← sub_zero v, sub_mem_ker_faceMap_iff]
  refine futureAgreement_is_greatest_stable (fun r y => read r y) (fun g y => T g y)
    (fun x y => ∃ c, x - y ∈ P c) ?_ ?_ v 0 ⟨c, by rwa [sub_zero]⟩
  · rintro x y ⟨c, hc⟩ r
    have h := LinearMap.mem_ker.mp (hread c r hc)
    rwa [map_sub, sub_eq_zero] at h
  · rintro a x y ⟨c, hc⟩
    exact ⟨next c a, by simpa only [map_sub] using hmove c a _ hc⟩

/-- [proved-derived; formal-checked] **The linear squares**: decoders `ρ_R = D_(c,R) E_c` and moves
`E_(next c a) T_a = U_(c,a) E_c` exist exactly when `ker E_c ≤ ker ρ_R` and
`T_a ker E_c ≤ ker E_(next c a)`. -/
theorem linear_descent_iff (T : ι → X →ₗ[K] X) (read : C → Dual K X) (next : Ctx → ι → Ctx)
    (E : Ctx → X →ₗ[K] Q) :
    (∃ (D : Ctx → C → Q →ₗ[K] K) (U : Ctx → ι → Q →ₗ[K] Q),
        (∀ c r, read r = D c r ∘ₗ E c) ∧ ∀ c a, E (next c a) ∘ₗ T a = U c a ∘ₗ E c) ↔
      (∀ c r, LinearMap.ker (E c) ≤ LinearMap.ker (read r)) ∧
        ∀ c a v, E c v = 0 → E (next c a) (T a v) = 0 := by
  constructor
  · rintro ⟨D, U, hD, hU⟩
    refine ⟨fun c r v hv => ?_, fun c a v hv => ?_⟩
    · rw [LinearMap.mem_ker] at hv ⊢
      rw [hD c r, LinearMap.comp_apply, hv, map_zero]
    · have h := LinearMap.congr_fun (hU c a) v
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hv, map_zero] at h
      exact h
  · rintro ⟨hread, hmove⟩
    choose D hD using fun c r => factor_of_ker_le (E c) (read r) (hread c r)
    choose U hU using fun c a => factor_of_ker_le (E c) (E (next c a) ∘ₗ T a) (by
      intro v hv
      rw [LinearMap.mem_ker] at hv
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact hmove c a v hv)
    exact ⟨D, U, hD, hU⟩

/-- [proved-derived; formal-checked] **Linear descent, or the separating remainder**: either the
squares hold in every context, or some context has a merged direction `v` (`E_c v = 0`) that a
receiver reads or an action carries out of the next kernel. -/
theorem linear_descent_or_remainder (T : ι → X →ₗ[K] X) (read : C → Dual K X)
    (next : Ctx → ι → Ctx) (E : Ctx → X →ₗ[K] Q) :
    (∃ (D : Ctx → C → Q →ₗ[K] K) (U : Ctx → ι → Q →ₗ[K] Q),
        (∀ c r, read r = D c r ∘ₗ E c) ∧ ∀ c a, E (next c a) ∘ₗ T a = U c a ∘ₗ E c) ∨
      ∃ c v, E c v = 0 ∧ ((∃ r, read r v ≠ 0) ∨ ∃ a, E (next c a) (T a v) ≠ 0) := by
  rw [linear_descent_iff]
  by_cases h : ∃ c v, E c v = 0 ∧ ((∃ r, read r v ≠ 0) ∨ ∃ a, E (next c a) (T a v) ≠ 0)
  · exact Or.inr h
  · left
    push Not at h
    exact ⟨fun c r v hv => LinearMap.mem_ker.mpr ((h c v (LinearMap.mem_ker.mp hv)).1 r),
      fun c a v hv => (h c v hv).2 a⟩

/-- [proved-derived; formal-checked] **Linear descent is action-sufficient**: under the squares
every encoding merges only directions the admitted future leaves unread, `ker E_c ≤ 𝒩`. -/
theorem ker_le_ker_faceMap_of_descent (T : ι → X →ₗ[K] X) (read : C → Dual K X)
    (next : Ctx → ι → Ctx) (E : Ctx → X →ₗ[K] Q)
    (h : (∀ c r, LinearMap.ker (E c) ≤ LinearMap.ker (read r)) ∧
      ∀ c a v, E c v = 0 → E (next c a) (T a v) = 0) (c : Ctx) :
    LinearMap.ker (E c) ≤ LinearMap.ker (faceMap read T) :=
  le_ker_faceMap T read next (fun c => LinearMap.ker (E c)) h.1
    (fun c a v hv => LinearMap.mem_ker.mpr (h.2 c a v (LinearMap.mem_ker.mp hv))) c

/-- [proved-derived; formal-checked] **A linear retention suffices exactly when it decodes and
continues into the relevance kernel**: `ker E ≤ 𝒩` iff `ker E ≤ ker ρ_R` for every receiver and
`T_a ker E ≤ 𝒩` for every action. The proof is the two-context descent `E → 𝒩`. -/
theorem ker_le_ker_faceMap_iff (T : ι → X →ₗ[K] X) (read : C → Dual K X) (E : X →ₗ[K] Q) :
    LinearMap.ker E ≤ LinearMap.ker (faceMap read T) ↔
      (∀ r, LinearMap.ker E ≤ LinearMap.ker (read r)) ∧
        ∀ a v, E v = 0 → T a v ∈ LinearMap.ker (faceMap read T) := by
  constructor
  · intro h
    exact ⟨fun r => h.trans (ker_faceMap_le_ker T read r), fun a v hv =>
      Submodule.mem_comap.mp (ker_faceMap_invariant read T a (h (LinearMap.mem_ker.mpr hv)))⟩
  · rintro ⟨hread, hmove⟩
    have key := le_ker_faceMap T read (fun (_ : Bool) (_ : ι) => true)
      (fun b => cond b (LinearMap.ker (faceMap read T)) (LinearMap.ker E))
      (fun b r => by
        cases b
        · exact hread r
        · exact ker_faceMap_le_ker T read r)
      (fun b a v hv => by
        cases b
        · exact hmove a v (LinearMap.mem_ker.mp (show v ∈ LinearMap.ker E from hv))
        · exact Submodule.mem_comap.mp (ker_faceMap_invariant read T a
            (show v ∈ LinearMap.ker (faceMap read T) from hv)))
      false
    exact key

/-- [proved-derived; formal-checked] **A sufficient retention reads and continues into every minimal
chart**: for `M` with `ker M = 𝒩` and `E` with `ker E ≤ 𝒩`, there are decoders `ρ_R = D_R E` and
moves `M T_a = U_a E`. -/
theorem continues_into_minimal {Q' : Type*} [AddCommGroup Q'] [Module K Q'] (T : ι → X →ₗ[K] X)
    (read : C → Dual K X) (M : X →ₗ[K] Q') (hM : LinearMap.ker M = LinearMap.ker (faceMap read T))
    (E : X →ₗ[K] Q) (hE : LinearMap.ker E ≤ LinearMap.ker (faceMap read T)) :
    (∀ r, ∃ D : Q →ₗ[K] K, read r = D ∘ₗ E) ∧ ∀ a, ∃ U : Q →ₗ[K] Q', M ∘ₗ T a = U ∘ₗ E := by
  obtain ⟨hread, hmove⟩ := (ker_le_ker_faceMap_iff T read E).mp hE
  refine ⟨fun r => factor_of_ker_le E (read r) (hread r),
    fun a => factor_of_ker_le E (M ∘ₗ T a) ?_⟩
  intro v hv
  have hv' := hmove a v (LinearMap.mem_ker.mp hv)
  rw [← hM, LinearMap.mem_ker] at hv'
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  exact hv'

/-! ### The founded chart -/

variable [FiniteDimensional K X]

/-- [proved-standard; formal-checked] **The relevance kernel is what the founded forms leave
unread**: `𝒩 = (founded)°`, so Birth's founded encoding is a minimal chart. -/
theorem ker_faceMap_eq_dualCoannihilator (T : ι → X →ₗ[K] X) (read : C → Dual K X) :
    LinearMap.ker (faceMap read T) =
      (founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read))).dualCoannihilator := by
  ext v
  rw [Submodule.mem_dualCoannihilator]
  have h := (sub_mem_ker_faceMap_iff T read v 0).trans (futureAgreement_iff_founded T read v 0)
  rw [sub_zero] at h
  rw [h]
  simp only [map_zero]

/-- [proved-standard; formal-checked] **Every founded form reads through every sufficient
retention**, so through every linear descent (`ker_le_ker_faceMap_of_descent`): the minimal chart is
a quotient of each of them. -/
theorem founded_reads_through (T : ι → X →ₗ[K] X) (read : C → Dual K X) (E : X →ₗ[K] Q)
    (hE : LinearMap.ker E ≤ LinearMap.ker (faceMap read T)) {φ : Dual K X}
    (hφ : φ ∈ founded (fun a => (T a).dualMap) (Submodule.span K (Set.range read))) :
    ∃ D : Q →ₗ[K] K, φ = D ∘ₗ E := by
  refine factor_of_ker_le E φ fun v hv => ?_
  have hv' := hE hv
  rw [ker_faceMap_eq_dualCoannihilator, Submodule.mem_dualCoannihilator] at hv'
  exact LinearMap.mem_ker.mpr (hv' φ hφ)

/-- [proved-standard; formal-checked] **On a reached span the founded forms restrict to the span of
the restricted readings** `ρ ∘ T_w |_R` (`MinimalRetention.founded_eq_span_wordForms` read on
`R`). -/
theorem founded_restrict_eq_span (T : ι → X →ₗ[K] X) (V₀ : Submodule K (Dual K X))
    (R : Submodule K X) :
    (founded (fun a => (T a).dualMap) V₀).map R.subtype.dualMap =
      Submodule.span K
        {ψ | ∃ ρ ∈ V₀, ∃ word : List ι, ψ = (ρ ∘ₗ wordMap T word) ∘ₗ R.subtype} := by
  rw [founded_eq_span_wordForms, Submodule.map_span]
  congr 1
  ext ψ
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨ρ, hρ, word, rfl⟩, rfl⟩
    exact ⟨ρ, hρ, word, LinearMap.dualMap_apply' _ _⟩
  · rintro ⟨ρ, hρ, word, rfl⟩
    exact ⟨_, ⟨ρ, hρ, word, rfl⟩, LinearMap.dualMap_apply' _ _⟩

end Linear

end Holonics.Foundation.ActionDescent
