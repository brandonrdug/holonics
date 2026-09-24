import Holonics.Foundation.ReceiverRelease
import Holonics.Foundation.CausalRelevance
import Holonics.Transport.ChangingReceiver
import Holonics.Foundation.RelationLadder
import Mathlib.Tactic

/-!
# Standing, memory and extinction

[definition] This owner states item **T2** of
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Its Rust counterpart
is `crates/holonic-engine/src/standing.rs`.

**Memory belongs to standing.** *Standing* is a prior relation still available to present
transport: the retained residue of the passages a lineage has undergone. A remembered face is
**generated now, not retrieved**:

```text
m_t = D_t(S_t, c_t)
```

with `S_t` the standing shaped by prior passages, `c_t` the present context and `D_t` the current
reconstruction. The original occurrence is not regenerated. A new occurrence in a related family
is constituted using the morphology the original helped form.

## What this file adds, and what it composes

Nothing here founds a second quotient, a second receiver vocabulary or a second transport engine.

* the ordered history is `Foundation/TransportWord.lean::transportWord`;
* the admitted future family and its greatest stable agreement are
  `Foundation/CausalRelevance.lean::futureAgreement` and `futureAgreement_is_greatest_stable`;
* the law that every admitted future observation factors through one quotient is
  `Foundation/ReceiverHistoryCompression.lean::ReceiverHistoryCompression.allSuccessorHistories`;
* the exact descent criterion and the insufficiency witness are
  `Foundation/Receiver.lean::receiverTransformer_exists_iff` and
  `Foundation/Receiver.lean::ReceiverInsufficiency`;
* the width of a reading over a compatible family and its tolerance are
  `Foundation/ReceiverRelease.lean::width` and `Foundation/ReceiverRelease.lean::Releasable`;
* the changing-receiver defect is `Transport/ChangingReceiver.lean::defect`;
* the typed relation scale this file's results are restated on is
  `Foundation/RelationLadder.lean::{Situation,potential,EqualPotential,WithinTolerance}` — item
  **T1** of the same plan. §6 below is that restatement and adds no content;
* a nonzero interior section with zero outward radiation — *dead to this receiver, alive inside* —
  is `Transport/WorldTube.lean::IsLawfulSilence` and
  `Transport/WorldTube.lean::nonzero_interior_section_can_lie_in_outward_radical`. That owner keeps
  the radical statement; §5 below only reads the same situation through `Extinct`.

## The four constructions

1. **Standing is any quotient sufficient for the admitted future.** AGENTS.md: *"Causal origin
   does not prescribe an event archive."* `standingLaw_exists_iff_future_factors` is that clause
   proved: a retention map carries a lawful standing **exactly when** every admitted future
   observation factors through it. Two different passage histories can leave one standing
   (`two_histories_leave_one_standing`), and two presents with one present face can carry
   different standing that a future receiver separates
   (`one_present_face_two_standings_separated_later`).

2. **Memory is a generator.** `MemoryLaw.remember` returns a `TimedFace` at the *present* time, so
   the reconstruction is not of the same type as the original's face
   (`the_remembered_face_is_a_new_occurrence`). The same standing under two contexts returns
   different faces; the same original under two later standings returns different reconstructions.
   The **fidelity law** is `faithfulAt_iff_receiver_factors_through_standing`: the reconstruction
   can agree with the original at receiver `ρ` exactly when `ρ` factors through what standing
   retained. `the_unretained_receiver_is_reconstructed_confidently_and_wrongly` is the honest
   formal content of *"it cannot confabulate without origin, but it can be wrong"* — a total
   reconstruction returning a definite face that is exactly wrong at a receiver standing did not
   retain, with the non-instance (`ReceiverInsufficiency`) constructed beside it.

3. **A receiver that keeps changing after its source stops.** The aperture chain is a refinement
   chain whose available face `ρ_t(M)` changes at every step while `M` does not; the fibre of
   sources compatible with `ρ_t(M)` is antitone; no finite step makes it a singleton; the chain's
   intersection is `{M}` only because this chain separates, and a chain with one unread coordinate
   never gets there.

4. **Effective extinction.** `Extinct` is `∀ ρ ∈ R, ∀ w ∈ G*, |ρ(T_w x) − ρ(T_w 0)| ≤ ε`, and
   `extinct_iff_release_width_inside_tolerance` proves it *is*
   `Foundation/ReceiverRelease.lean::Releasable` on the two-point family `{T_w x, T_w 0}`. It is
   monotone in the tolerance, in the receiver family and in the generator family. The exact
   instance is a damped linear system coupled to a slow medium: at horizon `3` the wave chart is
   extinct at tolerance `1/8` while the medium reads `21/64` at the *same* tolerance and never
   falls below it again — a fossil. The declared quadratic energy that left the wave chart is
   accounted for exactly in the medium plus dissipation. In the exact rational rotation nothing is
   ever extinct at any tolerance below the energy: the difference is redistributed between the two
   coordinates and never leaves.

Every carrier introduced here is `[definition]`; every theorem is `[proved-derived;
formal-checked]`; the three witnesses are `[counterexample; formal-checked]` relative to their
declared fixtures. No `axiom`, no `sorry`, no `native_decide`.
-/

namespace Holonics.Foundation.Standing

open Holonics
open Holonics.Millennium.Chronology
open Holonics.Foundation.CausalRelevance.NonLinear

/-! ## 1. Standing is the retained residue of passages -/

/-- [definition] **The complete admitted future observation of a present occurrence.** `ρ` ranges
over the declared receivers and `w` over the finite ordered histories; the face returned is what
that receiver reads after that history. This is the plan's `Pot_{G,R}(x)` written as a function,
so that *equal potential* is literally equality of two of these. -/
def causalSignature {Generator Receiver Source Face : Type*}
    (observe : Receiver → Source → Face) (transport : Generator → Source → Source)
    (source : Source) : Receiver × List Generator → Face :=
  fun request => observe request.1 (transportWord transport request.2 source)

/-- [proved-derived; formal-checked] Equal causal signature and `futureAgreement` are one
statement. The owner of the relation is `Foundation/CausalRelevance.lean`; this is the function
face of it. -/
theorem causalSignature_eq_iff_futureAgreement {Generator Receiver Source Face : Type*}
    (observe : Receiver → Source → Face) (transport : Generator → Source → Source)
    (left right : Source) :
    causalSignature observe transport left = causalSignature observe transport right ↔
      futureAgreement observe transport left right := by
  constructor
  · intro h receiver word
    exact congrFun h (receiver, word)
  · intro h
    funext request
    exact h request.1 request.2

/-- [definition] **A standing law.** `retain` is the quotient a lineage's passages leave behind and
`reopen` is the factor through which an admitted future observation is read off it. The single
obligation `sufficient` is the whole content of *"standing is sufficient for the admitted
future"*; nothing requires `retain` to be injective, and nothing requires the passage history to
be recoverable from it. -/
structure StandingLaw (Generator Receiver Source Retained Face : Type*) where
  /-- The admitted source transports. -/
  transport : Generator → Source → Source
  /-- The declared present receivers. -/
  observe : Receiver → Source → Face
  /-- The retained residue of the passages: the standing. -/
  retain : Source → Retained
  /-- The factor that reads one admitted future observation off the standing alone. -/
  reopen : Receiver → List Generator → Retained → Face
  /-- The obligation: every admitted future observation factors through the standing. -/
  sufficient : ∀ receiver word source,
    reopen receiver word (retain source) =
      observe receiver (transportWord transport word source)

namespace StandingLaw

variable {Generator Receiver Source Retained Face : Type*}

/-- [proved-derived; formal-checked] Equal standing forces every admitted future face to agree.
This is `Foundation/ReceiverHistoryCompression.lean::quotientEqForcesEverySuccessorFace` for a
retention that need not commute with the generators on the quotient. -/
theorem futureAgreement_of_retain_eq (L : StandingLaw Generator Receiver Source Retained Face)
    {left right : Source} (h : L.retain left = L.retain right) :
    futureAgreement L.observe L.transport left right := by
  intro receiver word
  rw [← L.sufficient receiver word left, ← L.sufficient receiver word right, h]

/-- [proved-derived; formal-checked] Hence equal standing forces equal causal signature. -/
theorem causalSignature_eq_of_retain_eq
    (L : StandingLaw Generator Receiver Source Retained Face)
    {left right : Source} (h : L.retain left = L.retain right) :
    causalSignature L.observe L.transport left = causalSignature L.observe L.transport right :=
  (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr (L.futureAgreement_of_retain_eq h)

/-- [proved-derived; formal-checked] A separating admitted future observation refutes the proposed
standing. The contrapositive of the law above, returned as a refusal rather than a failure. -/
theorem separating_future_refutes_the_standing
    (L : StandingLaw Generator Receiver Source Retained Face)
    {left right : Source} (receiver : Receiver) (word : List Generator)
    (separates :
      L.observe receiver (transportWord L.transport word left) ≠
        L.observe receiver (transportWord L.transport word right)) :
    L.retain left ≠ L.retain right := by
  intro h
  exact separates (L.futureAgreement_of_retain_eq h receiver word)

end StandingLaw

/-- [definition] **The canonical standing: the admitted future itself.** It retains the whole
causal signature and reopens by evaluation. Every other lawful standing is a coarsening of it. -/
def canonicalStanding {Generator Receiver Source Face : Type*}
    (observe : Receiver → Source → Face) (transport : Generator → Source → Source) :
    StandingLaw Generator Receiver Source (Receiver × List Generator → Face) Face where
  transport := transport
  observe := observe
  retain := causalSignature observe transport
  reopen := fun receiver word signature => signature (receiver, word)
  sufficient := fun _ _ _ => rfl

/-- [proved-derived; formal-checked] **Standing may be any quotient through which every admitted
future observation factors — and no other.**

AGENTS.md: *"Causal origin does not prescribe an event archive. Retain dependencies, conditions,
phase, relevant pending cuts and source distinctions in a representation sufficient for the
admitted receivers and continuation."* This is that clause as an equivalence: a retention map
carries a lawful `StandingLaw` exactly when it refines the causal signature. The history is not
recoverable, the source is not recoverable, and neither is owed.

The reopening is built classically on the image of `retain`; off that image it returns an
arbitrary face, which is why `Nonempty Face` is carried. -/
theorem standingLaw_exists_iff_future_factors
    {Generator Receiver Source Retained Face : Type*} [Nonempty Face]
    (observe : Receiver → Source → Face) (transport : Generator → Source → Source)
    (retain : Source → Retained) :
    (∃ L : StandingLaw Generator Receiver Source Retained Face,
        L.transport = transport ∧ L.observe = observe ∧ L.retain = retain) ↔
      ∀ left right, retain left = retain right →
        causalSignature observe transport left = causalSignature observe transport right := by
  classical
  constructor
  · rintro ⟨L, htransport, hobserve, hretain⟩ left right h
    subst htransport; subst hobserve; subst hretain
    exact L.causalSignature_eq_of_retain_eq h
  · intro factors
    refine ⟨{
      transport := transport
      observe := observe
      retain := retain
      reopen := fun receiver word standing =>
        if h : ∃ source, retain source = standing then
          observe receiver (transportWord transport word h.choose)
        else Classical.arbitrary Face
      sufficient := ?_ }, rfl, rfl, rfl⟩
    intro receiver word source
    have hexists : ∃ candidate, retain candidate = retain source := ⟨source, rfl⟩
    rw [dif_pos hexists]
    have hchosen : retain hexists.choose = retain source := hexists.choose_spec
    exact congrFun (factors _ _ hchosen) (receiver, word)

/-! ### A carrier on which both witnesses live

A rational pair: the first coordinate is the occurrence's own state, the second is the medium in
which a later receiver reads. Nothing in it is biographical; it is a wave and the medium it
travels through. -/

/-- [definition] The two-coordinate rational carrier. -/
abbrev Carrier : Type := ℚ × ℚ

/-- [definition] Two admitted passages: one advances the state, one deposits in the medium. -/
inductive Move
  /-- Advance the occurrence's own state by one. -/
  | advanceState
  /-- Deposit one unit in the medium. -/
  | advanceMedium
  deriving DecidableEq

/-- [definition] The exact action of the two passages. -/
def move : Move → Carrier → Carrier
  | .advanceState, (state, medium) => (state + 1, medium)
  | .advanceMedium, (state, medium) => (state, medium + 1)

/-- [definition] The declared receiver: it reads the medium and nothing else. -/
def mediumReceiver : Unit → Carrier → ℚ := fun _ carrier => carrier.2

/-- [proved-derived; formal-checked] A transport word moves the medium by exactly its count of
deposits, whatever the state coordinate does. -/
theorem medium_after_word (word : List Move) (carrier : Carrier) :
    (transportWord move word carrier).2 =
      carrier.2 + (word.countP (fun m => m == Move.advanceMedium) : ℚ) := by
  induction word with
  | nil => simp
  | cons head word ih =>
    cases head <;>
      simp [transportWord_cons, move, ih, add_comm, add_left_comm]

/-- [definition] The medium standing: the retained residue is the medium coordinate alone. It is
sufficient for the declared receiver because a deposit count is carried by the word, not by the
state. -/
def mediumStanding : StandingLaw Move Unit Carrier ℚ ℚ where
  transport := move
  observe := mediumReceiver
  retain := fun carrier => carrier.2
  reopen := fun _ word standing =>
    standing + (word.countP (fun m => m == Move.advanceMedium) : ℚ)
  sufficient := by
    intro _ word carrier
    exact (medium_after_word word carrier).symm

/-- [counterexample; formal-checked] **Two different histories leave one standing, and the two
presents are genuinely different occurrences.** One advance and two advances of the state reach
distinct presents that carry the same standing and therefore the same admitted future. Histories
need not be recoverable from standing, and the repository owes no event archive. -/
theorem two_histories_leave_one_standing :
    transportWord move [Move.advanceState] ((0 : ℚ), (0 : ℚ)) ≠
        transportWord move [Move.advanceState, Move.advanceState] ((0 : ℚ), (0 : ℚ)) ∧
      mediumStanding.retain (transportWord move [Move.advanceState] ((0 : ℚ), (0 : ℚ))) =
        mediumStanding.retain
          (transportWord move [Move.advanceState, Move.advanceState] ((0 : ℚ), (0 : ℚ))) ∧
      futureAgreement mediumReceiver move
        (transportWord move [Move.advanceState] ((0 : ℚ), (0 : ℚ)))
        (transportWord move [Move.advanceState, Move.advanceState] ((0 : ℚ), (0 : ℚ))) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [transportWord, move]
  · simp [mediumStanding, transportWord, move]
  · apply mediumStanding.futureAgreement_of_retain_eq
    simp [mediumStanding, transportWord, move]

/-- [definition] The exchange passage: the state and the medium trade places. -/
def exchange : Unit → Carrier → Carrier := fun _ carrier => (carrier.2, carrier.1)

/-- [definition] The present receiver reads the state coordinate only. -/
def stateReceiver : Unit → Carrier → ℚ := fun _ carrier => carrier.1

/-- [counterexample; formal-checked] **One present face, two standings, separated by a future
receiver.** The two presents agree at the present receiver and differ under the canonical
standing; the separator is the same receiver after one exchange. This is
`Foundation/ReceiverHistoryCompression.lean::StaticControl.aStaticCompressionCanReopenUnderOneSuccessor`
read in the standing vocabulary. -/
theorem one_present_face_two_standings_separated_later :
    stateReceiver () ((0 : ℚ), (0 : ℚ)) = stateReceiver () ((0 : ℚ), (1 : ℚ)) ∧
      stateReceiver () (transportWord exchange [()] ((0 : ℚ), (0 : ℚ))) ≠
        stateReceiver () (transportWord exchange [()] ((0 : ℚ), (1 : ℚ))) ∧
      (canonicalStanding stateReceiver exchange).retain ((0 : ℚ), (0 : ℚ)) ≠
        (canonicalStanding stateReceiver exchange).retain ((0 : ℚ), (1 : ℚ)) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [stateReceiver, transportWord, exchange]
  · intro h
    have separated := congrFun h ((), [()])
    simp [canonicalStanding, causalSignature, stateReceiver, transportWord, exchange] at separated

/-! ## 2. Memory is a generator, not a retrieval -/

/-- [definition] **A face carried at a declared time.** The time is part of the type, so a face
generated now and a face the original occurrence carried are not of the same type and cannot be
compared by `=` at all. That is the typing content of *"a later occurrence is not the earlier
one"*. -/
structure TimedFace (time : ℕ) (Value : Type*) where
  /-- The exact value the face carries. -/
  value : Value

/-- [definition] The time a face occurs at, read off its type. -/
def TimedFace.occursAt {time : ℕ} {Value : Type*} (_ : TimedFace time Value) : ℕ := time

/-- [definition] **The reconstruction `D_t`.** It is a generator: it takes the standing and the
present context and *constitutes* a face at the present time. It receives no original. -/
structure MemoryLaw (Retained Context Value : Type*) where
  /-- The present time. -/
  present : ℕ
  /-- The exact generating law `D_t(S_t, c_t)`. -/
  generate : Retained → Context → Value

/-- [definition] `m_t = D_t(S_t, c_t)`, stamped with the present time. -/
def MemoryLaw.remember {Retained Context Value : Type*}
    (law : MemoryLaw Retained Context Value) (standing : Retained) (context : Context) :
    TimedFace law.present Value :=
  ⟨law.generate standing context⟩

/-- [proved-derived; formal-checked] **The remembered face is a new occurrence.** It occurs at the
present time, not at the original's. There is no equality to the original to be had: the two lie
in different types, and the time index recovered from the type separates them. -/
theorem the_remembered_face_is_a_new_occurrence {Retained Context Value : Type*}
    (law : MemoryLaw Retained Context Value) (standing : Retained) (context : Context)
    {originalTime : ℕ} (original : TimedFace originalTime Value)
    (distinct : originalTime ≠ law.present) :
    (law.remember standing context).occursAt ≠ original.occursAt :=
  fun h => distinct h.symm

/-- [counterexample; formal-checked] **Receiver agreement after a passage is not recovery.** The
only things that can relate the original to the reconstruction are a passage `T_{u←t}` and a
receiver; and agreement at that receiver leaves the carried values different. A zero receiver
difference establishes agreement only at that receiver's declared scope — AGENTS.md. -/
theorem receiver_agreement_after_the_passage_is_not_recovery :
    ∃ (passage : TimedFace 0 (ℚ × ℚ) → TimedFace 5 (ℚ × ℚ))
      (receiver : TimedFace 5 (ℚ × ℚ) → ℚ)
      (original : TimedFace 0 (ℚ × ℚ)) (reconstructed : TimedFace 5 (ℚ × ℚ)),
      receiver (passage original) = receiver reconstructed ∧
        (passage original).value ≠ reconstructed.value := by
  refine ⟨fun face => ⟨face.value⟩, fun face => face.value.1, ⟨(1, 2)⟩, ⟨(1, 3)⟩, rfl, ?_⟩
  intro h
  have := congrArg Prod.snd h
  norm_num at this

/-- [definition] A worked reconstruction over the rationals: the standing supplies the retained
part and the present context supplies the rest. -/
def rationalMemory (present : ℕ) : MemoryLaw ℚ ℚ (ℚ × ℚ) where
  present := present
  generate := fun standing context => (standing, context)

/-- [counterexample; formal-checked] **The same standing under two contexts returns two faces.**
The reconstruction depends on the present, which is what makes it a generation and not a
retrieval. -/
theorem one_standing_two_contexts_two_faces :
    ((rationalMemory 5).remember 1 0).value ≠ ((rationalMemory 5).remember 1 1).value := by
  intro h
  have := congrArg Prod.snd h
  norm_num [rationalMemory, MemoryLaw.remember] at this

/-- [counterexample; formal-checked] **The same original under two later standings returns two
reconstructions.** The two standings are the medium standing of one original carrier after two
different intervening histories: one deposit and two. Reinterpretation is the standing changing
under later passages, not the original changing. -/
theorem one_original_two_standings_two_reconstructions :
    ((rationalMemory 5).remember
        (mediumStanding.retain (transportWord move [Move.advanceMedium] ((0 : ℚ), (0 : ℚ)))) 7).value ≠
      ((rationalMemory 5).remember
        (mediumStanding.retain
          (transportWord move [Move.advanceMedium, Move.advanceMedium] ((0 : ℚ), (0 : ℚ)))) 7).value := by
  intro h
  have := congrArg Prod.fst h
  simp [rationalMemory, MemoryLaw.remember, mediumStanding, transportWord, move] at this

/-! ### The fidelity law -/

/-- [definition] **The reconstruction is faithful at receiver `ρ`** when some reconstruction from
the standing alone returns `ρ`'s face of the transported original, for every member of the
lineage. This is `Foundation/Receiver.lean::ReceiverTransformer` with the standing as the entering
receiver. -/
def FaithfulAt {Source Retained Target Face : Type*}
    (retain : Source → Retained) (passage : Source → Target) (receiver : Target → Face) : Prop :=
  Nonempty (ReceiverTransformer retain (receiver ∘ passage))

/-- [proved-derived; formal-checked] **The fidelity law.** A faithful reconstruction at `ρ` exists
exactly when `ρ` (after the passage) factors through what standing retained. Cited, not rebuilt:
this is `Foundation/Receiver.lean::receiverTransformer_exists_iff`. -/
theorem faithfulAt_iff_receiver_factors_through_standing
    {Source Retained Target Face : Type*}
    (retain : Source → Retained) (passage : Source → Target) (receiver : Target → Face) :
    FaithfulAt retain passage receiver ↔
      ∀ left right, retain left = retain right →
        receiver (passage left) = receiver (passage right) :=
  receiverTransformer_exists_iff _ _

/-- [definition] A song carried as `(melody, timbre)`. Standing retains the melody; nothing
retains the timbre. -/
abbrev Song : Type := ℚ × ℚ

/-- [definition] The retained part of a song. -/
def melody : Song → ℚ := fun song => song.1

/-- [definition] The receiver that reads the timbre. -/
def timbre : Song → ℚ := fun song => song.2

/-- [definition] The reconstruction: the retained melody, and the present context's timbre, which
here is `0`. It is total and returns a definite face for every standing. -/
def reconstructSong (standing : ℚ) : Song := (standing, 0)

/-- [counterexample; formal-checked] The timbre is not retained: two songs with one standing
differ in it. This is `Foundation/Receiver.lean::ReceiverInsufficiency` constructed. -/
def timbreIsNotRetained : ReceiverInsufficiency melody timbre where
  left := (0, 0)
  right := (0, 1)
  sameEntering := rfl
  differentReturned := by norm_num [timbre]

/-- [counterexample; formal-checked] **A receiver standing did not retain is reconstructed
confidently and wrongly.**

* the melody is faithful — a reconstruction from the standing alone returns it exactly;
* the timbre is not faithful, and `timbreIsNotRetained` is why: no reconstruction from standing
  could return it;
* the reconstruction nevertheless returns a **definite** timbre for this original, and that face
  is exactly wrong.

This is the honest formal content of *"it cannot confabulate without origin, but it can be
wrong"*. The face is constituted and originful — the standing that produced it came from the
original — and it is incorrect at a receiver the standing does not cover. -/
theorem the_unretained_receiver_is_reconstructed_confidently_and_wrongly :
    FaithfulAt melody (id : Song → Song) melody ∧
      ¬ FaithfulAt melody (id : Song → Song) timbre ∧
      timbre (reconstructSong (melody ((0 : ℚ), (1 : ℚ)))) = 0 ∧
      timbre ((0 : ℚ), (1 : ℚ)) ≠ 0 := by
  refine ⟨⟨{ transform := fun face => face.1, exact := fun _ => rfl }⟩, ?_, rfl, ?_⟩
  · rintro ⟨transformer⟩
    exact transformer.excludesInsufficiency timbreIsNotRetained
  · norm_num [timbre]

/-! ## 3. The receiver keeps changing after the source stops -/

/-- [definition] **The aperture at step `t`.** It reads the first `t` coordinates of a source and
returns zero beyond them. The family `t ↦ aperture t` is a refinement chain: the receiver acquires
distinctions while the source does nothing at all. -/
def aperture (step : ℕ) (source : ℕ → ℚ) : ℕ → ℚ :=
  fun index => if index < step then source index else 0

/-- [proved-derived; formal-checked] A coarser aperture reads a finer aperture's face and returns
its own. This is the refinement chain's link law. -/
theorem aperture_comp_of_le {coarse fine : ℕ} (h : coarse ≤ fine) (source : ℕ → ℚ) :
    aperture coarse (aperture fine source) = aperture coarse source := by
  funext index
  by_cases hindex : index < coarse
  · have : index < fine := lt_of_lt_of_le hindex h
    simp [aperture, hindex, this]
  · simp [aperture, hindex]

/-- [proved-derived; formal-checked] **The refinement chain has zero changing-receiver defect.**
`Transport/ChangingReceiver.lean::defect` returns the signed discrepancy between a returned
receiver and a proposed coarse operation on the entering one; for the aperture chain it is
exactly zero, so the chain is a lawful changing receiver and not an approximation. -/
theorem aperture_chain_has_zero_changing_receiver_defect
    {coarse fine : ℕ} (h : coarse ≤ fine) (source : ℕ → ℚ) :
    Transport.ChangingReceiver.defect (aperture fine) (aperture coarse) (aperture coarse)
      source = 0 := by
  rw [Transport.ChangingReceiver.defect, aperture_comp_of_le h, sub_self]

/-- [definition] The fixed source. It never changes; every one of its coordinates is `1`. -/
def fixedSource : ℕ → ℚ := fun _ => 1

/-- [proved-derived; formal-checked] **The available face changes at every step while the source
does not.** `Transport/ChangingReceiver.lean` owns the general statement; this is its exact
witness with `ρ_t(M) ≠ ρ_{t+1}(M)` for every `t`. -/
theorem the_available_face_changes_while_the_source_does_not (step : ℕ) :
    aperture step fixedSource ≠ aperture (step + 1) fixedSource := by
  intro h
  have separated := congrFun h step
  simp [aperture, fixedSource] at separated

/-- [definition] **The fibre of sources compatible with what the receiver can read at step `t`.**
It is `Foundation/ReceiverAtlas.lean`'s preimage fibre for this chain. -/
def compatibleFibre (step : ℕ) (reference : ℕ → ℚ) : Set (ℕ → ℚ) :=
  { source | aperture step source = aperture step reference }

/-- [proved-derived; formal-checked] **The fibre is antitone in the step.** Understanding narrows
it and never widens it. -/
theorem compatibleFibre_antitone {coarse fine : ℕ} (h : coarse ≤ fine) (reference : ℕ → ℚ) :
    compatibleFibre fine reference ⊆ compatibleFibre coarse reference := by
  intro source hsource
  have : aperture coarse (aperture fine source) = aperture coarse (aperture fine reference) :=
    congrArg (aperture coarse) hsource
  rwa [aperture_comp_of_le h, aperture_comp_of_le h] at this

/-- [definition] A source that agrees with `fixedSource` on the first `step` coordinates and
differs at coordinate `step`. -/
def lateDeviation (step : ℕ) : ℕ → ℚ :=
  fun index => if index = step then 0 else 1

/-- [counterexample; formal-checked] **No finite step narrows the fibre to a singleton**, and
**what one step cannot separate a later step can.** For every `t` there is a source distinct from
the reference that is inside the fibre at `t` and outside it at `t + 1`. -/
theorem the_fibre_is_never_a_singleton_and_a_later_step_separates (step : ℕ) :
    lateDeviation step ∈ compatibleFibre step fixedSource ∧
      lateDeviation step ≠ fixedSource ∧
      lateDeviation step ∉ compatibleFibre (step + 1) fixedSource := by
  refine ⟨?_, ?_, ?_⟩
  · funext index
    by_cases hindex : index < step
    · have : index ≠ step := Nat.ne_of_lt hindex
      simp [aperture, lateDeviation, fixedSource, hindex, this]
    · simp [aperture, hindex]
  · intro h
    have separated := congrFun h step
    simp [lateDeviation, fixedSource] at separated
  · intro h
    have separated := congrFun h step
    simp [aperture, lateDeviation, fixedSource] at separated

/-- [counterexample; formal-checked] The step `t + 1` receiver is strictly finer than the step `t`
receiver: `Foundation/Receiver.lean::ReceiverInsufficiency` constructed on the chain. -/
def apertureInsufficiency (step : ℕ) :
    ReceiverInsufficiency (aperture step) (aperture (step + 1)) where
  left := lateDeviation step
  right := fixedSource
  sameEntering := (the_fibre_is_never_a_singleton_and_a_later_step_separates step).1
  differentReturned := (the_fibre_is_never_a_singleton_and_a_later_step_separates step).2.2

/-- [proved-derived; formal-checked] Hence no receiver-to-receiver transformer carries the coarser
face into the finer one: the later separation is new content, not a reading of the earlier face.
Cited from `Foundation/Receiver.lean::ReceiverTransformer.excludesInsufficiency`. -/
theorem no_transformer_from_the_coarser_aperture (step : ℕ) :
    IsEmpty (ReceiverTransformer (aperture step) (aperture (step + 1))) :=
  ⟨fun transformer => transformer.excludesInsufficiency (apertureInsufficiency step)⟩

/-- [proved-derived; formal-checked] **This chain separates**, so the intersection of all its
fibres is the reference alone. A singleton is reached only in the limit and only because the chain
separates. -/
theorem the_chain_separates (reference source : ℕ → ℚ)
    (agrees : ∀ step, source ∈ compatibleFibre step reference) : source = reference := by
  funext index
  have h := congrFun (agrees (index + 1)) index
  simpa [aperture] using h

/-- [definition] The same chain over a carrier with one coordinate the receivers never read. -/
def maskedAperture (step : ℕ) (source : (ℕ → ℚ) × ℚ) : ℕ → ℚ := aperture step source.1

/-- [counterexample; formal-checked] **Understanding narrows the fibre and never proves a
singleton unless the chain separates.** With one unread coordinate, two distinct sources sit in
every fibre of the chain, so the intersection is never a singleton however far the receiver
refines. -/
theorem a_non_separating_chain_never_reaches_a_singleton :
    (∀ step, maskedAperture step (fixedSource, 0) = maskedAperture step (fixedSource, 1)) ∧
      ((fixedSource, (0 : ℚ)) ≠ (fixedSource, (1 : ℚ))) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro h
  have := congrArg Prod.snd h
  norm_num at this

/-! ## 4. Effective extinction -/

/-- [definition] **Effective extinction of a perturbation `x` against a reference.** The remaining
differences can no longer affect any future face this receiver family admits:

```text
Extinct_{R,G,ε}(x | 0) :⟺ ∀ ρ ∈ R, ∀ w ∈ G*, d(ρ(T_w x), ρ(T_w 0)) ≤ ε
```

A wave has no universal death. It becomes dead *relative to a receiver family and a tolerance*,
and the same wave is separated again by a richer family. -/
def Extinct {Generator Receiver Source : Type*}
    (read : Receiver → Source → ℚ) (transport : Generator → Source → Source)
    (tolerance : ℚ) (perturbation reference : Source) : Prop :=
  ∀ receiver (word : List Generator),
    |read receiver (transportWord transport word perturbation) -
        read receiver (transportWord transport word reference)| ≤ tolerance

/-- [proved-derived; formal-checked] **The width of a reading over a two-point family is the
separation of its two faces.** Proved from the existing owner's own laws —
`Foundation/ReceiverRelease.lean::width_le_of_bounds` and `abs_sub_le_width` — so no second
diameter is founded. -/
theorem width_pair {X : Type*} [DecidableEq X] (left right : X) (read : X → ℚ)
    (hne : ({left, right} : Finset X).Nonempty) :
    ReceiverRelease.width ({left, right} : Finset X) hne read = |read left - read right| := by
  have hleft : left ∈ ({left, right} : Finset X) := Finset.mem_insert_self _ _
  have hright : right ∈ ({left, right} : Finset X) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  refine le_antisymm ?_ ?_
  · have hband :
        ReceiverRelease.width ({left, right} : Finset X) hne read ≤
          max (read left) (read right) - min (read left) (read right) := by
      refine ReceiverRelease.width_le_of_bounds hne read ?_ ?_
      · intro member hmember
        rcases Finset.mem_insert.mp hmember with rfl | hmember
        · exact min_le_left _ _
        · rw [Finset.mem_singleton.mp hmember]; exact min_le_right _ _
      · intro member hmember
        rcases Finset.mem_insert.mp hmember with rfl | hmember
        · exact le_max_left _ _
        · rw [Finset.mem_singleton.mp hmember]; exact le_max_right _ _
    rw [max_sub_min_eq_abs] at hband
    exact hband.trans_eq (abs_sub_comm _ _)
  · exact ReceiverRelease.abs_sub_le_width hne read hleft hright

/-- [proved-derived; formal-checked] **Extinction is the release owner's width inside tolerance,
read on the two-point family `{T_w x, T_w 0}`.** The identification is the deliverable: extinction
founds no new uncertainty reading, and `Foundation/ReceiverRelease.lean::Releasable` is the whole
of it. -/
theorem extinct_iff_release_width_inside_tolerance
    {Generator Receiver Source : Type*} [DecidableEq Source]
    (read : Receiver → Source → ℚ) (transport : Generator → Source → Source)
    (tolerance : ℚ) (perturbation reference : Source) :
    Extinct read transport tolerance perturbation reference ↔
      ∀ (receiver : Receiver) (word : List Generator)
        (hne : ({transportWord transport word perturbation,
          transportWord transport word reference} : Finset Source).Nonempty),
        ReceiverRelease.Releasable
          ({transportWord transport word perturbation,
            transportWord transport word reference} : Finset Source) hne (read receiver)
          tolerance := by
  constructor
  · intro h receiver word hne
    rw [ReceiverRelease.Releasable, width_pair _ _ _ hne]
    exact h receiver word
  · intro h receiver word
    have hne : ({transportWord transport word perturbation,
        transportWord transport word reference} : Finset Source).Nonempty :=
      ⟨_, Finset.mem_insert_self _ _⟩
    have := h receiver word hne
    rwa [ReceiverRelease.Releasable, width_pair _ _ _ hne] at this

/-- [proved-derived; formal-checked] Extinction is monotone in the tolerance: a larger declared
tolerance keeps an extinct perturbation extinct. -/
theorem extinct_mono_tolerance {Generator Receiver Source : Type*}
    {read : Receiver → Source → ℚ} {transport : Generator → Source → Source}
    {tolerance wider : ℚ} {perturbation reference : Source}
    (h : Extinct read transport tolerance perturbation reference) (hle : tolerance ≤ wider) :
    Extinct read transport wider perturbation reference :=
  fun receiver word => (h receiver word).trans hle

/-- [proved-derived; formal-checked] Extinction is monotone in the receiver family: any
reindexing into the declared receivers — in particular any subfamily — stays extinct. -/
theorem extinct_mono_receivers {Generator Receiver Smaller Source : Type*}
    {read : Receiver → Source → ℚ} {transport : Generator → Source → Source}
    {tolerance : ℚ} {perturbation reference : Source}
    (h : Extinct read transport tolerance perturbation reference) (into : Smaller → Receiver) :
    Extinct (fun smaller => read (into smaller)) transport tolerance perturbation reference :=
  fun receiver word => h (into receiver) word

/-- [proved-derived; formal-checked] A reindexed generator family transports every word through
the original family's words. -/
theorem transportWord_reindex {Generator Smaller Source : Type*}
    (transport : Generator → Source → Source) (into : Smaller → Generator)
    (word : List Smaller) (source : Source) :
    transportWord (fun smaller => transport (into smaller)) word source =
      transportWord transport (word.map into) source := by
  induction word with
  | nil => rfl
  | cons head word ih => simp [transportWord_cons, ih]

/-- [proved-derived; formal-checked] Extinction is monotone in the generator family: fewer
admitted passages keep an extinct perturbation extinct. -/
theorem extinct_mono_generators {Generator Smaller Receiver Source : Type*}
    {read : Receiver → Source → ℚ} {transport : Generator → Source → Source}
    {tolerance : ℚ} {perturbation reference : Source}
    (h : Extinct read transport tolerance perturbation reference) (into : Smaller → Generator) :
    Extinct read (fun smaller => transport (into smaller)) tolerance perturbation reference := by
  intro receiver word
  have reindexed := h receiver (word.map into)
  rw [← transportWord_reindex transport into word perturbation,
    ← transportWord_reindex transport into word reference] at reindexed
  exact reindexed

/-! ### The fossil: a damped wave, the medium it inscribes, and what the ledger says

The wave is `Foundation/CausalChord.lean::Linearization` with the exact state matrix

```text
A = ⎡ 1/2   0    0 ⎤     x = (a, e, m)
    ⎢  0   1/4   0 ⎥     a = amplitude, e = declared quadratic energy, m = the medium
    ⎣  0   1/4   1 ⎦
```

`a` halves, so its declared energy `e = a²` quarters; three quarters of that energy leave the wave
chart at every step, of which the medium captures a third (`1/4` of `e`) and the rest dissipates.
Every value below is an exact rational. -/

/-- [definition] The three-coordinate carrier: amplitude, declared quadratic energy, medium. -/
abbrev Fossil : Type := ℚ × ℚ × ℚ

/-- [definition] The exact step. Linear over `ℚ`; one generator. -/
def fossilStep : Unit → Fossil → Fossil
  | (), (amplitude, energy, medium) => (amplitude / 2, energy / 4, medium + energy / 4)

/-- [definition] The exact closed form of the trajectory from `(1, 1, 0)`. -/
def fossilState (step : ℕ) : Fossil :=
  ((1 / 2 : ℚ) ^ step, (1 / 4 : ℚ) ^ step, (1 - (1 / 4 : ℚ) ^ step) / 3)

/-- [definition] The exactly dissipated energy after `step` steps: two thirds of what left the
wave chart. -/
def dissipated (step : ℕ) : ℚ := 2 * (1 - (1 / 4 : ℚ) ^ step) / 3

/-- [definition] The reference the perturbation is read against: the rest state. -/
def fossilRest : Fossil := (0, 0, 0)

/-- [proved-derived; formal-checked] The closed form really is the trajectory. -/
theorem fossilState_step (step : ℕ) : fossilStep () (fossilState step) = fossilState (step + 1) := by
  simp only [fossilStep, fossilState, pow_succ, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem fossilState_zero : fossilState 0 = (1, 1, 0) := by norm_num [fossilState]

/-- [proved-derived; formal-checked] The rest state is a fixed point of the step. -/
theorem fossilStep_rest : fossilStep () fossilRest = fossilRest := by norm_num [fossilStep, fossilRest]

/-- [proved-derived; formal-checked] The declared energy coordinate is exactly the square of the
amplitude at every step, so it is not an independent fiction. -/
theorem the_energy_is_the_square_of_the_amplitude (step : ℕ) :
    (fossilState step).2.1 = (fossilState step).1 ^ 2 := by
  simp only [fossilState]
  have quarter : ((1 : ℚ) / 4) ^ step = (((1 : ℚ) / 2) ^ 2) ^ step := by norm_num
  rw [quarter, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- [proved-derived; formal-checked] Any word over the single generator advances the trajectory by
its length. -/
theorem transportWord_fossilState (word : List Unit) (step : ℕ) :
    transportWord fossilStep word (fossilState step) = fossilState (step + word.length) := by
  induction word with
  | nil => simp
  | cons head word ih =>
    cases head
    rw [transportWord_cons, ih, fossilState_step, List.length_cons]
    congr 1

/-- [proved-derived; formal-checked] And leaves the rest state where it is. -/
theorem transportWord_fossilRest (word : List Unit) :
    transportWord fossilStep word fossilRest = fossilRest := by
  induction word with
  | nil => rfl
  | cons head word ih =>
    cases head
    rw [transportWord_cons, ih, fossilStep_rest]

/-- [definition] The wave chart's receivers: the amplitude and its declared energy. -/
inductive WaveReceiver
  /-- The amplitude `a`. -/
  | amplitude
  /-- The declared quadratic energy `e`. -/
  | energy
  deriving DecidableEq

/-- [definition] The richer family adds the receiver that reads the medium. -/
inductive RicherReceiver
  /-- The amplitude `a`. -/
  | amplitude
  /-- The declared quadratic energy `e`. -/
  | energy
  /-- The medium's inscription `m`. -/
  | medium
  deriving DecidableEq

/-- [definition] The wave chart's readings. -/
def waveRead : WaveReceiver → Fossil → ℚ
  | .amplitude, state => state.1
  | .energy, state => state.2.1

/-- [definition] The richer family's readings. -/
def richerRead : RicherReceiver → Fossil → ℚ
  | .amplitude, state => state.1
  | .energy, state => state.2.1
  | .medium, state => state.2.2

/-- [proved-derived; formal-checked] A halving power never rises. -/
theorem half_pow_antitone {small large : ℕ} (h : small ≤ large) :
    (1 / 2 : ℚ) ^ large ≤ (1 / 2 : ℚ) ^ small :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- [proved-derived; formal-checked] And a quartering power never rises. -/
theorem quarter_pow_antitone {small large : ℕ} (h : small ≤ large) :
    (1 / 4 : ℚ) ^ large ≤ (1 / 4 : ℚ) ^ small :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem half_pow_nonneg (step : ℕ) : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ step := by positivity

theorem quarter_pow_nonneg (step : ℕ) : (0 : ℚ) ≤ (1 / 4 : ℚ) ^ step := by positivity

/-- [proved-derived; formal-checked] **The wave chart is extinct at horizon 3 and tolerance
`1/8`.** Every admitted future word keeps both wave readings inside the declared tolerance,
because the state matrix contracts the wave chart by `1/2` at every step and the chart is
invariant. -/
theorem the_wave_is_extinct_at_horizon_three :
    Extinct waveRead fossilStep (1 / 8) (fossilState 3) fossilRest := by
  intro receiver word
  rw [transportWord_fossilState, transportWord_fossilRest]
  cases receiver with
  | amplitude =>
    simp only [waveRead, fossilState, fossilRest, sub_zero]
    rw [abs_of_nonneg (half_pow_nonneg _)]
    calc (1 / 2 : ℚ) ^ (3 + word.length) ≤ (1 / 2 : ℚ) ^ 3 :=
          half_pow_antitone (Nat.le_add_right 3 word.length)
      _ = 1 / 8 := by norm_num
  | energy =>
    simp only [waveRead, fossilState, fossilRest, sub_zero]
    rw [abs_of_nonneg (quarter_pow_nonneg _)]
    calc (1 / 4 : ℚ) ^ (3 + word.length) ≤ (1 / 4 : ℚ) ^ 3 :=
          quarter_pow_antitone (Nat.le_add_right 3 word.length)
      _ = 1 / 64 := by norm_num
      _ ≤ 1 / 8 := by norm_num

/-- [proved-derived; formal-checked] The medium's inscription at horizon 3 is exactly `21/64`. -/
theorem the_inscription_at_horizon_three : (fossilState 3).2.2 = 21 / 64 := by
  norm_num [fossilState]

/-- [counterexample; formal-checked] **Extinct at `(R, ε)` and separated at a richer `(R', ε)`.**
The same perturbation at the same tolerance is extinct for the wave chart and separated for the
family that also reads the medium. The separator is returned: the receiver `medium` and the empty
word, at exact width `21/64 > 1/8`. A wave has no universal death. -/
theorem the_medium_separates_what_the_wave_chart_declared_extinct :
    ¬ Extinct richerRead fossilStep (1 / 8) (fossilState 3) fossilRest := by
  intro h
  have separated := h RicherReceiver.medium []
  rw [transportWord_nil, transportWord_nil] at separated
  simp only [richerRead, fossilRest, sub_zero] at separated
  rw [the_inscription_at_horizon_three] at separated
  norm_num at separated

/-- [proved-derived; formal-checked] **The fossil is durable.** Every admitted future word still
reads at least `21/64` on the medium: the inscription is a boundary record that does not decay,
not a momentarily visible residue. -/
theorem the_fossil_is_durable (word : List Unit) :
    (21 : ℚ) / 64 ≤ (transportWord fossilStep word (fossilState 3)).2.2 := by
  rw [transportWord_fossilState]
  simp only [fossilState]
  have hle : (1 / 4 : ℚ) ^ (3 + word.length) ≤ (1 / 4 : ℚ) ^ 3 :=
    quarter_pow_antitone (Nat.le_add_right 3 word.length)
  have : ((1 : ℚ) - (1 / 4 : ℚ) ^ 3) / 3 ≤ (1 - (1 / 4 : ℚ) ^ (3 + word.length)) / 3 := by
    linarith
  calc (21 : ℚ) / 64 = ((1 : ℚ) - (1 / 4 : ℚ) ^ 3) / 3 := by norm_num
    _ ≤ (1 - (1 / 4 : ℚ) ^ (3 + word.length)) / 3 := this

/-- [proved-derived; formal-checked] And it never reaches the whole of what left the wave: the
inscription stays strictly below `1/3` at every step. -/
theorem the_inscription_stays_below_its_limit (step : ℕ) : (fossilState step).2.2 < 1 / 3 := by
  simp only [fossilState]
  have hpos : (0 : ℚ) < (1 / 4 : ℚ) ^ step := by positivity
  linarith

/-- [proved-derived; formal-checked] **The declared quadratic energy that left the wave chart is
accounted for exactly.** What the wave lost equals what the medium holds plus what dissipated —
exact rational bookkeeping, with no residual term defined into existence. -/
theorem the_energy_that_left_the_wave_is_accounted_for (step : ℕ) :
    (fossilState 0).2.1 - (fossilState step).2.1 =
      (fossilState step).2.2 + dissipated step := by
  simp only [fossilState, dissipated, pow_zero]
  ring

/-- [proved-derived; formal-checked] The same ledger per step: what leaves the wave in one step is
what the medium gains plus what dissipates in that step. -/
theorem the_per_step_ledger (step : ℕ) :
    (fossilState step).2.1 - (fossilState (step + 1)).2.1 =
      ((fossilState (step + 1)).2.2 - (fossilState step).2.2) +
        (dissipated (step + 1) - dissipated step) := by
  simp only [fossilState, dissipated, pow_succ]
  ring

/-! ### The nondissipative control: at tolerance zero nothing is ever extinct

The exact `3-4-5` rational rotation is orthogonal over `ℚ`, so the declared quadratic energy is
conserved exactly. The difference is redistributed between the two coordinates and never leaves
the system. -/

/-- [definition] The rational plane. -/
abbrev Plane : Type := ℚ × ℚ

/-- [definition] The exact `3-4-5` rotation. Every entry is an exact rational and the map is
orthogonal. -/
def rotate : Unit → Plane → Plane
  | (), (first, second) => ((3 * first - 4 * second) / 5, (4 * first + 3 * second) / 5)

/-- [definition] The declared quadratic energy of the plane. -/
def planeEnergy : Plane → ℚ := fun state => state.1 ^ 2 + state.2 ^ 2

/-- [definition] The full receiver family: both coordinates and the energy. -/
inductive PlaneReceiver
  /-- The first coordinate. -/
  | first
  /-- The second coordinate. -/
  | second
  /-- The declared quadratic energy. -/
  | energy
  deriving DecidableEq

/-- [definition] Its readings. -/
def planeRead : PlaneReceiver → Plane → ℚ
  | .first, state => state.1
  | .second, state => state.2
  | .energy, state => planeEnergy state

/-- [proved-derived; formal-checked] The rotation conserves the declared energy exactly. -/
theorem rotate_preserves_energy (state : Plane) : planeEnergy (rotate () state) = planeEnergy state := by
  obtain ⟨first, second⟩ := state
  simp only [rotate, planeEnergy]
  ring

/-- [proved-derived; formal-checked] And therefore conserves it along every admitted history. -/
theorem rotate_preserves_energy_along_every_word (word : List Unit) (state : Plane) :
    planeEnergy (transportWord rotate word state) = planeEnergy state := by
  induction word with
  | nil => rfl
  | cons head word ih =>
    cases head
    rw [transportWord_cons, rotate_preserves_energy, ih]

theorem rotate_fixes_rest (word : List Unit) :
    transportWord rotate word ((0 : ℚ), (0 : ℚ)) = ((0 : ℚ), (0 : ℚ)) := by
  induction word with
  | nil => rfl
  | cons head word ih =>
    cases head
    rw [transportWord_cons, ih]
    simp [rotate]

/-- [proved-derived; formal-checked] **In the nondissipative system nothing is ever extinct for
the full receiver family, at any tolerance below the energy and from any horizon.** The energy
receiver reads the same exact value after every admitted history, so the difference is
redistributed among the coordinates and never removed. With `ε = 0` this is the statement that
nothing nonzero is ever extinct at all. -/
theorem no_horizon_releases_the_energy_receiver (horizon : ℕ) (tolerance : ℚ)
    (below : tolerance < 1) :
    ¬ Extinct planeRead rotate tolerance
        (transportWord rotate (List.replicate horizon ()) ((1 : ℚ), (0 : ℚ)))
        ((0 : ℚ), (0 : ℚ)) := by
  intro h
  have separated := h PlaneReceiver.energy []
  rw [transportWord_nil, transportWord_nil] at separated
  simp only [planeRead] at separated
  rw [rotate_preserves_energy_along_every_word] at separated
  simp only [planeEnergy] at separated
  norm_num at separated
  linarith

/-- [proved-derived; formal-checked] The `ε = 0` case, stated on its own: in the exact rotation no
nonzero state is ever extinct for the full family. -/
theorem nothing_nonzero_is_extinct_at_zero_tolerance (state : Plane)
    (alive : planeEnergy state ≠ 0) :
    ¬ Extinct planeRead rotate 0 state ((0 : ℚ), (0 : ℚ)) := by
  intro h
  have separated := h PlaneReceiver.energy []
  rw [transportWord_nil, transportWord_nil] at separated
  simp only [planeRead, planeEnergy] at separated
  norm_num at separated
  exact alive (by simpa [planeEnergy] using separated)

/-- [proved-derived; formal-checked] The redistribution, exhibited on exact numbers: from `(1, 0)`
the rotation returns `(3/5, 4/5)` and then `(-7/25, 24/25)`, and the energy is `1` at all three
stations. -/
theorem the_difference_is_redistributed_not_removed :
    rotate () ((1 : ℚ), (0 : ℚ)) = ((3 : ℚ) / 5, (4 : ℚ) / 5) ∧
      rotate () ((3 : ℚ) / 5, (4 : ℚ) / 5) = (-(7 : ℚ) / 25, (24 : ℚ) / 25) ∧
      planeEnergy ((1 : ℚ), (0 : ℚ)) = 1 ∧
      planeEnergy ((3 : ℚ) / 5, (4 : ℚ) / 5) = 1 ∧
      planeEnergy (-(7 : ℚ) / 25, (24 : ℚ) / 25) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [rotate, planeEnergy]

/-! ## 5. Dead to this receiver, alive inside

`Transport/WorldTube.lean::IsLawfulSilence` owns the statement that a nonzero interior section
whose outward restriction vanishes radiates nothing while conducting inside, and
`Transport/WorldTube.lean::nonzero_interior_section_can_lie_in_outward_radical` exhibits one. Read
through `Extinct`, that section is extinct at tolerance `0` for the outward receiver family, and
nonzero. The two statements are the same situation in two vocabularies; this file founds no second
radical. -/

/-- [definition] The interior carrier, with the outward receiver reading the first coordinate. -/
abbrev Interior : Type := ℚ × ℚ

/-- [definition] The outward receiver family: the exterior restriction, and nothing else. -/
def outwardRead : Unit → Interior → ℚ := fun _ section_ => section_.1

/-- [counterexample; formal-checked] **A nonzero interior section can be extinct at tolerance zero
for the outward receiver family.** Lawful silence is exactly extinction at the exterior receiver,
with the interior difference intact. -/
theorem lawful_silence_is_extinction_at_the_outward_receiver :
    Extinct outwardRead (fun _ : Unit => (id : Interior → Interior)) 0 ((0 : ℚ), (1 : ℚ))
        ((0 : ℚ), (0 : ℚ)) ∧
      ((0 : ℚ), (1 : ℚ)) ≠ ((0 : ℚ), (0 : ℚ)) := by
  constructor
  · intro _ word
    have hsilent : ∀ (w : List Unit) (state : Interior),
        transportWord (fun _ : Unit => (id : Interior → Interior)) w state = state := by
      intro w state
      induction w with
      | nil => rfl
      | cons head w ih => cases head; rw [transportWord_cons, ih]; rfl
    rw [hsilent, hsilent]
    simp [outwardRead]
  · intro h
    have := congrArg Prod.snd h
    norm_num at this


/-! ## 6. The same results in the relation ladder's vocabulary

[definition] `Foundation/RelationLadder.lean` — item **T1** of the same plan — places strict
occurrence identity, continuation, isomorphism, receiver equality, equal potential and tolerance
on one typed scale. Everything above was stated against the owners that file also cites, so the
join needs no new content: standing is a coarsening of its rung 5, and extinction is its rung 6
quantified over every admitted history. These four corollaries are the restatement. -/

/-- [proved-derived; formal-checked] **The causal signature is the ladder's potential.**
`Foundation/RelationLadder.lean::potential` and this file's `causalSignature` are the same
function at the same situation, so *"standing is sufficient for the admitted future"* and
*"standing refines rung 5"* are one statement. -/
theorem causalSignature_eq_potential {Generator Receiver Source Face : Type*}
    (situation : RelationLadder.Situation Generator Receiver Source Face) (source : Source) :
    causalSignature situation.observe situation.step source =
      RelationLadder.potential situation source := rfl

/-- [proved-derived; formal-checked] **Equal standing establishes rung 5 and never more.** Every
lawful standing establishes equal potential between the occurrences it identifies, and
`one_present_face_two_standings_separated_later` is the constructed case where rung 4 holds and
rung 5 does not — so standing is strictly finer than the present face. -/
theorem retain_eq_establishes_equalPotential
    {Generator Receiver Source Retained Face : Type*}
    (law : StandingLaw Generator Receiver Source Retained Face) {left right : Source}
    (h : law.retain left = law.retain right) :
    RelationLadder.EqualPotential ⟨law.observe, law.transport⟩ left right :=
  law.futureAgreement_of_retain_eq h

/-- [proved-derived; formal-checked] **Extinction is rung 6 after every admitted history.**
`Foundation/RelationLadder.lean::WithinTolerance` is the tolerance rung; extinction is that rung
holding at every declared receiver after every admitted word, and the two are the same
proposition. -/
theorem extinct_iff_withinTolerance_after_every_history
    {Generator Receiver Source : Type*}
    (read : Receiver → Source → ℚ) (transport : Generator → Source → Source)
    (tolerance : ℚ) (perturbation reference : Source) :
    Extinct read transport tolerance perturbation reference ↔
      ∀ (receiver : Receiver) (word : List Generator),
        RelationLadder.WithinTolerance (read receiver) tolerance
          (transportWord transport word perturbation)
          (transportWord transport word reference) :=
  Iff.rfl

/-- [proved-derived; formal-checked] **At tolerance zero, extinction against a reference is equal
potential with it.** The tolerance rung collapses onto rung 5 exactly at `ε = 0`, which is why
`nothing_nonzero_is_extinct_at_zero_tolerance` is the statement that the rotation's difference
never acquires the rest state's potential: it is redistributed, not removed. -/
theorem extinct_at_zero_iff_equalPotential
    {Generator Receiver Source : Type*}
    (read : Receiver → Source → ℚ) (transport : Generator → Source → Source)
    (perturbation reference : Source) :
    Extinct read transport 0 perturbation reference ↔
      RelationLadder.EqualPotential ⟨read, transport⟩ perturbation reference := by
  constructor
  · intro extinct receiver word
    have inside := extinct receiver word
    have vanishes :
        |read receiver (transportWord transport word perturbation) -
            read receiver (transportWord transport word reference)| = 0 :=
      le_antisymm inside (abs_nonneg _)
    have := abs_eq_zero.mp vanishes
    linarith
  · intro same receiver word
    have agrees : read receiver (transportWord transport word perturbation) =
        read receiver (transportWord transport word reference) := same receiver word
    rw [agrees, sub_self, abs_zero]

end Holonics.Foundation.Standing

section Audit
open Holonics.Foundation.Standing
#print axioms causalSignature_eq_iff_futureAgreement
#print axioms StandingLaw.futureAgreement_of_retain_eq
#print axioms StandingLaw.separating_future_refutes_the_standing
#print axioms standingLaw_exists_iff_future_factors
#print axioms two_histories_leave_one_standing
#print axioms one_present_face_two_standings_separated_later
#print axioms the_remembered_face_is_a_new_occurrence
#print axioms receiver_agreement_after_the_passage_is_not_recovery
#print axioms one_standing_two_contexts_two_faces
#print axioms one_original_two_standings_two_reconstructions
#print axioms faithfulAt_iff_receiver_factors_through_standing
#print axioms the_unretained_receiver_is_reconstructed_confidently_and_wrongly
#print axioms aperture_comp_of_le
#print axioms aperture_chain_has_zero_changing_receiver_defect
#print axioms the_available_face_changes_while_the_source_does_not
#print axioms compatibleFibre_antitone
#print axioms the_fibre_is_never_a_singleton_and_a_later_step_separates
#print axioms no_transformer_from_the_coarser_aperture
#print axioms the_chain_separates
#print axioms a_non_separating_chain_never_reaches_a_singleton
#print axioms width_pair
#print axioms extinct_iff_release_width_inside_tolerance
#print axioms extinct_mono_tolerance
#print axioms extinct_mono_receivers
#print axioms extinct_mono_generators
#print axioms fossilState_step
#print axioms the_energy_is_the_square_of_the_amplitude
#print axioms the_wave_is_extinct_at_horizon_three
#print axioms the_medium_separates_what_the_wave_chart_declared_extinct
#print axioms the_fossil_is_durable
#print axioms the_inscription_stays_below_its_limit
#print axioms the_energy_that_left_the_wave_is_accounted_for
#print axioms the_per_step_ledger
#print axioms rotate_preserves_energy_along_every_word
#print axioms no_horizon_releases_the_energy_receiver
#print axioms nothing_nonzero_is_extinct_at_zero_tolerance
#print axioms the_difference_is_redistributed_not_removed
#print axioms lawful_silence_is_extinction_at_the_outward_receiver
#print axioms causalSignature_eq_potential
#print axioms retain_eq_establishes_equalPotential
#print axioms extinct_iff_withinTolerance_after_every_history
#print axioms extinct_at_zero_iff_equalPotential
end Audit
