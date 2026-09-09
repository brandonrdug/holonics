import ElementaryHolonics.Transport.WorldTubePotential
import ElementaryHolonics.Physics.ConstitutiveCurrentReduction

/-!
# A constitutive step carried by an addressed world-tube

The occurrence endpoint is the complete before/after state.  It therefore contains the cut, active
face, blind residual, and exact local clock; serial `ClockedSpan` composition can join only when the
whole predecessor state is the next source state.  The receiver keeps both decoded currents,
their cut and face readings, and the material/source input.  The obstruction is the actual fine-law
residual together with its zero receipt and the residual blindness receipts.

The current module is a parameter.  The commuting map certificates are the only constitutive
binding; the concrete two-face compact update and fine-law theorem are supplied by
`TwoFaceConstitutive`.
-/

noncomputable section

namespace Soma.Holonics.Physics.ConstitutiveWorldTube

open Soma.Holonics
open Soma.Holonics.Physics.TwoFaceConstitutive
open Soma.Holonics.Physics.ConstitutiveCurrentReduction
open Soma.Holonics.Transport.WorldTubePotential
open Soma.Holonics.Millennium.HolonicSensoryWorldTube

abbrev Cut := TwoFaceConstitutive.Cut
abbrev Face := TwoFaceConstitutive.Face

variable {Current : Type*} [AddCommGroup Current] [Module ℚ Current]

/-- The generic source/face/current charts consumed by the two-face law. -/
abbrev Carrier (Current : Type*) [AddCommGroup Current] [Module ℚ Current] :=
  ConstitutiveChart Current

def decode (carrier : Carrier Current) (q : Cut) (z : Face) (residual : Current) : Current :=
  decodedCurrent carrier.J carrier.D q z residual

def fineResidual (carrier : Carrier Current) (tau mu nu : ℚ)
    (before after : Current) (u : Cut) (f : Face) : Current :=
  after + tau • carrier.D (materialMap mu nu (carrier.Dt after)) -
    (before + carrier.J u + carrier.D f)

def cutReading (carrier : Carrier Current) (current : Current) : Cut := carrier.C current

def faceReading (carrier : Carrier Current) (current : Current) : Face := carrier.Dt current

theorem decode_cut (carrier : Carrier Current) (q : Cut) (z : Face) (residual : Current)
    (hCr : carrier.C residual = 0) :
    cutReading carrier (decode carrier q z residual) = q := by
  exact decodedCurrent_cut carrier.J carrier.D carrier.C q z residual
    carrier.CJ carrier.CD hCr

theorem decode_face (carrier : Carrier Current) (q : Cut) (z : Face) (residual : Current)
    (hDtr : carrier.Dt residual = 0) :
    faceReading carrier (decode carrier q z residual) =
      cutFaceCoupling q + faceMetric z := by
  exact decodedCurrent_face carrier.J carrier.D carrier.Dt q z residual
    carrier.DtJ carrier.DtD hDtr

/-- The endpoint retains cut, face, current residual, and local rational clock. -/
abbrev State (Current : Type*) := Cut × Face × Current × ℚ

structure Input where
  tau : ℚ
  mu : ℚ
  nu : ℚ
  u : Cut
  f : Face
  tau_nonneg : 0 ≤ tau
  plus_nonneg : 0 ≤ mu + nu
  minus_nonneg : 0 ≤ mu - nu

def successor (input : Input) (state : State Current) : State Current :=
  (state.1 + input.u,
    compactExplicitUpdate input.tau input.mu input.nu (state.1 + input.u) state.2.1 input.f,
    state.2.2.1, state.2.2.2 + input.tau)

structure FullFace (Current : Type*) [AddCommGroup Current] [Module ℚ Current] where
  input : Input
  before : State Current
  after : State Current
  currentBefore : Current
  currentAfter : Current
  cutBefore : Cut
  cutAfter : Cut
  faceBefore : Face
  faceAfter : Face

structure FineObstruction (carrier : Carrier Current) (input : Input) (state : State Current) where
  residual : Current
  residual_eq_state : residual = state.2.2.1
  cutBlind : carrier.C residual = 0
  faceBlind : carrier.Dt residual = 0
  fineResidual : Current
  fineResidual_eq_actual : fineResidual =
    ConstitutiveWorldTube.fineResidual carrier input.tau input.mu input.nu
      (decode carrier state.1 state.2.1 residual)
      (decode carrier (successor input state).1 (successor input state).2.1 residual)
      input.u input.f
  fineResidual_zero : fineResidual = 0

def fullFace (carrier : Carrier Current) (input : Input) (state : State Current) : FullFace Current where
  input := input
  before := state
  after := successor input state
  currentBefore := decode carrier state.1 state.2.1 state.2.2.1
  currentAfter := decode carrier (successor input state).1 (successor input state).2.1 state.2.2.1
  cutBefore := cutReading carrier (decode carrier state.1 state.2.1 state.2.2.1)
  cutAfter := cutReading carrier
    (decode carrier (successor input state).1 (successor input state).2.1 state.2.2.1)
  faceBefore := faceReading carrier (decode carrier state.1 state.2.1 state.2.2.1)
  faceAfter := faceReading carrier
    (decode carrier (successor input state).1 (successor input state).2.1 state.2.2.1)

def toClockedSpan (carrier : Carrier Current) (input : Input) (state : State Current)
    (obstruction : FineObstruction carrier input state) :
    ClockedSpan (State Current) (State Current) (ℚ × ℚ) (FullFace Current)
      (FineObstruction carrier input state) Unit where
  source _ := state
  target _ := successor input state
  clock _ := (state.2.2.2, (successor input state).2.2.2)
  receive _ := fullFace carrier input state
  obstruction _ := obstruction

theorem fullFace_cutBefore (carrier : Carrier Current) (input : Input) (state : State Current)
    (residualCut : carrier.C state.2.2.1 = 0) :
    (fullFace carrier input state).cutBefore = state.1 := by
  simpa [fullFace] using decode_cut carrier state.1 state.2.1 state.2.2.1 residualCut

theorem fullFace_cutAfter (carrier : Carrier Current) (input : Input) (state : State Current)
    (residualCut : carrier.C state.2.2.1 = 0) :
    (fullFace carrier input state).cutAfter = (successor input state).1 := by
  simpa [fullFace] using decode_cut carrier (successor input state).1 (successor input state).2.1
    state.2.2.1 residualCut

theorem fullFace_faceBefore (carrier : Carrier Current) (input : Input) (state : State Current)
    (residualFace : carrier.Dt state.2.2.1 = 0) :
    (fullFace carrier input state).faceBefore =
      cutFaceCoupling state.1 + faceMetric state.2.1 := by
  simpa [fullFace] using decode_face carrier state.1 state.2.1 state.2.2.1 residualFace

theorem fullFace_faceAfter (carrier : Carrier Current) (input : Input) (state : State Current)
    (residualFace : carrier.Dt state.2.2.1 = 0) :
    (fullFace carrier input state).faceAfter =
      cutFaceCoupling (successor input state).1 +
        faceMetric (successor input state).2.1 := by
  simpa [fullFace] using decode_face carrier (successor input state).1 (successor input state).2.1
    state.2.2.1 residualFace

/-! ## Actual two-face fine-law receipt -/

theorem actualFineResidual_zero (chart : Carrier Current) (input : Input)
    (state : State Current) (hDtr : chart.Dt state.2.2.1 = 0) :
    fineResidual chart input.tau input.mu input.nu
      (decode chart state.1 state.2.1 state.2.2.1)
      (decode chart (successor input state).1 (successor input state).2.1 state.2.2.1)
      input.u input.f = 0 := by
  unfold fineResidual
  have hcompact := compactExplicitUpdate_solves
    input.tau_nonneg input.plus_nonneg input.minus_nonneg
    state.1 input.u state.2.1 input.f
  have hfine := decodedCurrent_fineLaw_of_compact chart
    state.1 input.u state.2.1 input.f
    (compactExplicitUpdate input.tau input.mu input.nu (state.1 + input.u)
      state.2.1 input.f) state.2.2.1 hDtr hcompact
  exact sub_eq_zero.mpr hfine

def certifiedObstruction (chart : Carrier Current) (input : Input)
    (state : State Current) (hCr : chart.C state.2.2.1 = 0)
    (hDtr : chart.Dt state.2.2.1 = 0) : FineObstruction chart input state where
  residual := state.2.2.1
  residual_eq_state := rfl
  cutBlind := hCr
  faceBlind := hDtr
  fineResidual := 0
  fineResidual_eq_actual := (actualFineResidual_zero chart input state hDtr).symm
  fineResidual_zero := rfl

def actualSpan (chart : Carrier Current) (input : Input) (state : State Current)
    (hCr : chart.C state.2.2.1 = 0) (hDtr : chart.Dt state.2.2.1 = 0) :
    ClockedSpan (State Current) (State Current) (ℚ × ℚ) (FullFace Current)
      (FineObstruction chart input state) Unit :=
  toClockedSpan chart input state (certifiedObstruction chart input state hCr hDtr)

theorem successor_cutBlind (chart : Carrier Current) (input : Input) (state : State Current)
    (hCr : chart.C state.2.2.1 = 0) :
    chart.C (successor input state).2.2.1 = 0 := by
  simpa [successor] using hCr

theorem successor_faceBlind (chart : Carrier Current) (input : Input) (state : State Current)
    (hDtr : chart.Dt state.2.2.1 = 0) :
    chart.Dt (successor input state).2.2.1 = 0 := by
  simpa [successor] using hDtr

def actualTwoStepOccurrence (chart : Carrier Current)
    (first second : Input) (state : State Current)
    (hCr : chart.C state.2.2.1 = 0) (hDtr : chart.Dt state.2.2.1 = 0) :
    ((actualSpan chart second (successor first state)
      (successor_cutBlind chart first state hCr)
      (successor_faceBlind chart first state hDtr)).toPassage.comp
        (actualSpan chart first state hCr hDtr).toPassage).Fibre
      state (successor second (successor first state)) :=
  ⟨⟨(), (), rfl⟩, rfl, rfl⟩

theorem actualTwoStep_split_rejoin_completeFace
    (chart : Carrier Current) (first second : Input) (state : State Current)
    (hCr : chart.C state.2.2.1 = 0) (hDtr : chart.Dt state.2.2.1 = 0) :
    let left := actualSpan chart first state hCr hDtr
    let right := actualSpan chart second (successor first state)
      (successor_cutBlind chart first state hCr)
      (successor_faceBlind chart first state hDtr)
    (right.comp left).completeFace
      (AddressedPassage.joinCompositeFibre right.toPassage left.toPassage
        (splitRejoinEquiv right left
          (actualTwoStepOccurrence chart first second state hCr hDtr))).1 =
      (right.comp left).completeFace
        (actualTwoStepOccurrence chart first second state hCr hDtr).1 := by
  exact splitRejoin_completeFace _ _ _

/-! ## Exact split/rejoin and the three-step associator -/

theorem associator_source_target_completeFace_natural
    {X Y Z W ClockLeft ClockMiddle ClockRight FaceLeft FaceMiddle FaceRight
      ObstructionLeft ObstructionMiddle ObstructionRight LeftOccurrence MiddleOccurrence
      RightOccurrence : Type*}
    (third : ClockedSpan Z W ClockRight FaceRight ObstructionRight RightOccurrence)
    (second : ClockedSpan Y Z ClockMiddle FaceMiddle ObstructionMiddle MiddleOccurrence)
    (first : ClockedSpan X Y ClockLeft FaceLeft ObstructionLeft LeftOccurrence)
    (occurrence : (third.comp (second.comp first)).toPassage.Occurrence) :
    (third.comp (second.comp first)).source occurrence =
        ((third.comp second).comp first).source
          (associatorOccurrenceEquiv third second first occurrence) ∧
      (third.comp (second.comp first)).target occurrence =
        ((third.comp second).comp first).target
          (associatorOccurrenceEquiv third second first occurrence) ∧
      associatorFaceEquiv ClockLeft ClockMiddle ClockRight FaceLeft FaceMiddle FaceRight
          ObstructionLeft ObstructionMiddle ObstructionRight
          ((third.comp (second.comp first)).completeFace occurrence) =
        ((third.comp second).comp first).completeFace
          (associatorOccurrenceEquiv third second first occurrence) := by
  exact ⟨associator_source_natural third second first occurrence,
    associator_target_natural third second first occurrence,
    associator_completeFace_natural third second first occurrence⟩

end Soma.Holonics.Physics.ConstitutiveWorldTube

section Audit
open Soma.Holonics.Physics.ConstitutiveWorldTube
#print axioms decode_cut
#print axioms decode_face
#print axioms actualFineResidual_zero
#print axioms actualTwoStepOccurrence
#print axioms actualTwoStep_split_rejoin_completeFace
#print axioms associator_source_target_completeFace_natural
end Audit
