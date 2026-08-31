import ElementaryHolonics.Millennium.ReceiverIndexedCausalLengthTower

/-!
# A heterogeneous holon as a one-step causal-length tower

[definition] A source-bearing holon may have different incoming and outgoing boundary types,
whereas one `ReceiverIndexedCausalLengthTower.Tower` uses a single state type.  The lawful common
state is the stage sum `Source ⊕ Target`: source occurrences enter through `Sum.inl`, target
occurrences leave through `Sum.inr`, and neither port is identified with the other.

[definition] `StagedHistory` adds only the stationary histories required by the tower.  Their
receiver is `none`; an enacted source holon occurrence returns `some face` and has one clock tick.
Consequently the `some face` reconstruction fibre is exactly the original holon fibre.  The clock
does not manufacture a source occurrence, collapse a receiver fibre, or reinterpret a boundary
degree as elapsed time.

[proved-derived; formal-checked] The equivalences below retain the original occurrence itself.
They are the narrow compatibility joint between the heterogeneous `Holon` owner and the
receiver-indexed causal-length tower.
-/

namespace Soma.Holonics.Millennium.HolonStagedCausalLength

open Soma.Holonics
open Soma.Holonics.Millennium.HolonicClockedPantographicSwing
open Soma.Holonics.Millennium.ReceiverIndexedCausalLengthTower

universe uSource uTarget uFace uOccurrence

variable {Source : Type uSource} {Target : Type uTarget} {Face : Type uFace}

/-- [definition] The exact source holon occurrences, together with stationary histories on the
disjoint stage boundary. -/
inductive StagedHistory (holon : Holon Source Target Face)
  | stay : Source ⊕ Target → StagedHistory holon
  | enact : holon.Occurrence → StagedHistory holon

namespace StagedHistory

variable (holon : Holon Source Target Face)

/-- [definition] A stationary history remains at its stage; an enacted occurrence begins at the
source injection. -/
def source : StagedHistory holon → Source ⊕ Target
  | .stay state => state
  | .enact occurrence => Sum.inl (holon.source occurrence)

/-- [definition] A stationary history remains at its stage; an enacted occurrence ends at the
target injection. -/
def target : StagedHistory holon → Source ⊕ Target
  | .stay state => state
  | .enact occurrence => Sum.inr (holon.target occurrence)

/-- [definition] `none` is reserved for stationary histories.  Every enacted history returns the
original holon receiver face under `some`. -/
def receive : StagedHistory holon → Option Face
  | .stay _ => none
  | .enact occurrence => some (holon.receive occurrence)

/-- [definition] The staged history presentation of the source holon. -/
def addressedHistory : AddressedHistory (StagedHistory holon) (Source ⊕ Target) (Option Face) where
  source := source holon
  target := target holon
  receive := receive holon

/-- [definition] Stationary histories cost no enacted clock crossing; every original occurrence
is one elementary crossing. -/
def clockLength : StagedHistory holon → ℕ
  | .stay _ => 0
  | .enact _ => 1

/-- [definition] The single resource axis witnesses the same elementary work population. -/
def resourceWork : StagedHistory holon → Unit → ℕ
  | .stay _, _ => 0
  | .enact _, _ => 1

@[simp] theorem source_stay (state : Source ⊕ Target) :
    source holon (.stay state) = state := rfl

@[simp] theorem target_stay (state : Source ⊕ Target) :
    target holon (.stay state) = state := rfl

@[simp] theorem receive_stay (state : Source ⊕ Target) :
    receive holon (.stay state) = none := rfl

@[simp] theorem source_enact (occurrence : holon.Occurrence) :
    source holon (.enact occurrence) = Sum.inl (holon.source occurrence) := rfl

@[simp] theorem target_enact (occurrence : holon.Occurrence) :
    target holon (.enact occurrence) = Sum.inr (holon.target occurrence) := rfl

@[simp] theorem receive_enact (occurrence : holon.Occurrence) :
    receive holon (.enact occurrence) = some (holon.receive occurrence) := rfl

@[simp] theorem clockLength_stay (state : Source ⊕ Target) :
    clockLength holon (.stay state) = 0 := rfl

@[simp] theorem clockLength_enact (occurrence : holon.Occurrence) :
    clockLength holon (.enact occurrence) = 1 := rfl

@[simp] theorem resourceWork_stay (state : Source ⊕ Target) (resource : Unit) :
    resourceWork holon (.stay state) resource = 0 := rfl

@[simp] theorem resourceWork_enact (occurrence : holon.Occurrence) (resource : Unit) :
    resourceWork holon (.enact occurrence) resource = 1 := rfl

end StagedHistory

/-- [definition] Identity-rate comparison between the distinct local clock and ruler addresses. -/
def oneStepClockRuler : ClockRulerSpan Unit Unit where
  clockAddress := ()
  rulerAddress := ()
  passage :=
    { source := Sum.inl ()
      target := Sum.inr ()
      numerator := 1
      denominator := 1
      numerator_pos := by decide
      denominator_pos := by decide }
  source_exact := rfl
  target_exact := rfl
  initialResidue := ⟨0, by decide⟩

/-- [definition] The one-step causal-length tower generated by one heterogeneous holon.  The caller
supplies only the boundary coordinate; the passage clock is fixed by actual enactment. -/
def oneStepTower (holon : Holon Source Target Face)
    (boundaryLength : Source ⊕ Target → ℕ) :
    Tower (StagedHistory holon) (Source ⊕ Target) Unit Unit Unit (Option Face) Unit where
  history := StagedHistory.addressedHistory holon
  boundaryAddress := ()
  clockAddress := ()
  rulerAddress := ()
  boundaryLength := boundaryLength
  clockLength := StagedHistory.clockLength holon
  resourceWork := StagedHistory.resourceWork holon
  resourceCapacity := fun _ => 1
  resourceCapacity_pos := fun _ => by decide
  clockRuler := oneStepClockRuler
  clockAddress_exact := rfl
  rulerAddress_exact := rfl
  stay := StagedHistory.stay
  stay_source := fun _ => rfl
  stay_target := fun _ => rfl
  stay_clockLength := fun _ => rfl
  stay_resourceWork := fun _ _ => rfl

/-- [proved-derived; formal-checked] The enacted receiver reconstruction fibre is exactly the
original source-holon fibre.  The added stationary histories cannot inhabit a `some` face. -/
def enactedReconstructionFibreEquiv (holon : Holon Source Target Face)
    (boundaryLength : Source ⊕ Target → ℕ) (face : Face) :
    (oneStepTower holon boundaryLength).history.toHolon.ReconstructionFibre (some face) ≃
      holon.ReconstructionFibre face where
  toFun carried := by
    rcases carried with ⟨history, receiverExact⟩
    change StagedHistory.receive holon history = some face at receiverExact
    cases history with
    | stay state => simp [StagedHistory.receive] at receiverExact
    | enact occurrence =>
        exact ⟨occurrence, Option.some.inj receiverExact⟩
  invFun carried := ⟨StagedHistory.enact carried.1, by
    change some (holon.receive carried.1) = some face
    exact congrArg some carried.2⟩
  left_inv carried := by
    rcases carried with ⟨history, receiverExact⟩
    change StagedHistory.receive holon history = some face at receiverExact
    cases history with
    | stay state => simp [StagedHistory.receive] at receiverExact
    | enact occurrence => rfl
  right_inv carried := by
    rcases carried with ⟨occurrence, receiverExact⟩
    rfl

/-- [proved-derived; formal-checked] The `none` fibre contains exactly the stationary stage
population.  It is disjoint from every enacted receiver fibre. -/
def stationaryReconstructionFibreEquiv (holon : Holon Source Target Face)
    (boundaryLength : Source ⊕ Target → ℕ) :
    (oneStepTower holon boundaryLength).history.toHolon.ReconstructionFibre none ≃
      Source ⊕ Target where
  toFun carried := by
    rcases carried with ⟨history, receiverExact⟩
    change StagedHistory.receive holon history = none at receiverExact
    cases history with
    | stay state => exact state
    | enact occurrence => simp [StagedHistory.receive] at receiverExact
  invFun state := ⟨StagedHistory.stay state, by
    change StagedHistory.receive holon (.stay state) = none
    rfl⟩
  left_inv carried := by
    rcases carried with ⟨history, receiverExact⟩
    change StagedHistory.receive holon history = none at receiverExact
    cases history with
    | stay state => rfl
    | enact occurrence => simp [StagedHistory.receive] at receiverExact
  right_inv state := rfl

/-- [proved-derived; formal-checked] One enacted source occurrence has exactly one local clock tick
in the staged tower. -/
theorem enacted_clockLength (holon : Holon Source Target Face)
    (boundaryLength : Source ⊕ Target → ℕ) (occurrence : holon.Occurrence) :
    (oneStepTower holon boundaryLength).clockLength (StagedHistory.enact occurrence) = 1 := by
  simp [oneStepTower, StagedHistory.clockLength]

/-- [proved-derived; formal-checked] An empty source receiver fibre remains empty after the clock is
attached.  Causal length can measure an occurrence; it cannot create one. -/
theorem enactedFibre_empty_of_sourceFibre_empty (holon : Holon Source Target Face)
    (boundaryLength : Source ⊕ Target → ℕ) (face : Face)
    (sourceEmpty : ¬ Nonempty (holon.ReconstructionFibre face)) :
    ¬ Nonempty
      ((oneStepTower holon boundaryLength).history.toHolon.ReconstructionFibre (some face)) := by
  rintro ⟨carried⟩
  exact sourceEmpty ⟨enactedReconstructionFibreEquiv holon boundaryLength face carried⟩

section Audit

#print axioms enactedReconstructionFibreEquiv
#print axioms stationaryReconstructionFibreEquiv
#print axioms enacted_clockLength
#print axioms enactedFibre_empty_of_sourceFibre_empty

end Audit

end Soma.Holonics.Millennium.HolonStagedCausalLength
