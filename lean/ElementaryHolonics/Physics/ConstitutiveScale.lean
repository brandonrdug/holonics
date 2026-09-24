import ElementaryHolonics.Physics.ConstitutiveWorldTube
import ElementaryHolonics.Foundation.BoundaryScalePassage
import ElementaryHolonics.Transport.ReceiverPotential

/-!
# Constitutive scale and future receiver packaging

This owner packages the existing two-face reduction as a typed receiver-relative scale passage and
as an ordered history compression for the actual `ConstitutiveWorldTube.Input` step.  The complete
current remains the source carrier; the quotient face is only `(cut, active face)`, and every
preimage fibre remains available to the receiver-potential image laws.
-/

namespace Soma.Holonics.Physics.ConstitutiveScale

open Soma.Holonics
open Soma.Holonics.Physics.TwoFaceConstitutive
open Soma.Holonics.Physics.ConstitutiveCurrentReduction
open Soma.Holonics.Physics.ConstitutiveWorldTube
open Soma.Holonics.Millennium.LineageCompression
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Transport.ReceiverPotential
open Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation

noncomputable section

abbrev Cut := TwoFaceConstitutive.Cut
abbrev Face := TwoFaceConstitutive.Face
abbrev ReducedFace := Cut × Face

variable {Current Source Target : Type*}
  [AddCommGroup Current] [Module ℚ Current]
  [AddCommGroup Source] [Module ℚ Source]
  [AddCommGroup Target] [Module ℚ Target]

/-- The linear active-face extractor, equal to the existing nonlinear-looking definition. -/
def extractedFaceLinear (chart : ConstitutiveChart Current) : Current →ₗ[ℚ] Face :=
  faceMetricInverse.comp (chart.Dt - cutFaceCoupling.comp chart.C)

theorem extractedFaceLinear_apply (chart : ConstitutiveChart Current) (current : Current) :
    extractedFaceLinear chart current = extractedFace chart current := rfl

/-- The complete reduced receiver as one linear map into the cut/face product. -/
def reducedReadLinear (chart : ConstitutiveChart Current) : Current →ₗ[ℚ] ReducedFace :=
  chart.C.prod (extractedFaceLinear chart)

theorem reducedReadLinear_apply (chart : ConstitutiveChart Current) (current : Current) :
    reducedReadLinear chart current = reducedRead chart current := rfl

/-- The decoded image map, with the residual coordinate omitted by construction. -/
def decoderLinear (chart : ConstitutiveChart Current) : ReducedFace →ₗ[ℚ] Current :=
  chart.J.comp (LinearMap.fst ℚ Cut Face) +
    chart.D.comp (LinearMap.snd ℚ Cut Face)

theorem decoderLinear_apply (chart : ConstitutiveChart Current)
    (face : ReducedFace) :
    decoderLinear chart face = decodedZero chart face.1 face.2 := by
  simp [decoderLinear, decodedZero, decodedCurrent]

theorem reducedRead_decoderLinear (chart : ConstitutiveChart Current)
    (face : ReducedFace) :
    reducedReadLinear chart (decoderLinear chart face) = face := by
  change reducedRead chart (decoderLinear chart face) = face
  rw [decoderLinear_apply]
  exact reducedRead_decodedZero chart face.1 face.2

/-- Receiver-relative transport from one constitutive carrier to another. -/
def scaleLinear (source : ConstitutiveChart Source) (target : ConstitutiveChart Target) :
    Source →ₗ[ℚ] Target :=
  (decoderLinear target).comp (reducedReadLinear source)

theorem scaleLinear_apply (source : ConstitutiveChart Source)
    (target : ConstitutiveChart Target) (current : Source) :
    scaleLinear source target current =
      reducedScaleTransport source target current := by
  change decoderLinear target (reducedReadLinear source current) = _
  rw [decoderLinear_apply]
  rfl

def scalePassage (source : ConstitutiveChart Source) (target : ConstitutiveChart Target) :
    BoundaryScalePassage ℚ Source ReducedFace Target ReducedFace where
  fineBoundary := reducedReadLinear source
  coarseBoundary := reducedReadLinear target
  interiorTransport := scaleLinear source target
  boundaryTransport := LinearMap.id
  boundary_natural := by
    apply LinearMap.ext
    intro current
    change reducedReadLinear target (decoderLinear target
      (reducedReadLinear source current)) = reducedReadLinear source current
    exact reducedRead_decoderLinear target _

theorem scalePassage_transport_boundary (source : ConstitutiveChart Source)
    (target : ConstitutiveChart Target) (current : Source) :
    (scalePassage source target).coarseBoundary
        ((scalePassage source target).interiorTransport current) =
      (scalePassage source target).boundaryTransport
        ((scalePassage source target).fineBoundary current) :=
  (scalePassage source target).transport_boundary current

/-! ## Actual Input chronology -/

def inputSourceTransport (chart : ConstitutiveChart Current) (input : Input) :
    Current → Current :=
  currentStep chart input.tau input.mu input.nu input.u input.f

def inputQuotientTransport (input : Input) : ReducedFace → ReducedFace
  | face =>
      (face.1 + input.u,
        compactExplicitUpdate input.tau input.mu input.nu
          (face.1 + input.u) face.2 input.f)

/-- The actual input family is the generator family. Each word may vary material, source, and clock
parameters; the source carrier remains the complete current, with reduced coordinates as quotient. -/
def inputHistoryCompression (chart : ConstitutiveChart Current) :
    ReceiverHistoryCompression Input Unit Current ReducedFace ReducedFace where
  present := {
    quotient := reducedRead chart
    receiver := fun _ current => reducedRead chart current
    factor := fun _ face => face
    exact := by intro _ current; rfl }
  sourceTransport := inputSourceTransport chart
  quotientTransport := fun input => inputQuotientTransport input
  generatorExact := by
    intro input current
    apply Prod.ext
    · exact currentStep_cut chart input.tau input.mu input.nu input.u input.f current
    · exact currentStep_face chart input.tau input.mu input.nu input.u input.f current

theorem input_history_word_exact (chart : ConstitutiveChart Current)
    (word : List Input) (current : Current) :
    reducedRead chart
        (transportWord (inputSourceTransport chart) word current) =
      transportWord (fun input => inputQuotientTransport input) word
        (reducedRead chart current) := by
  exact ReceiverHistoryCompression.quotientCommutesWithEveryOrderedWord
    (inputHistoryCompression chart) word current

/-- Every ordered actual input word has a singleton future face at the reduced receiver, while the
complete current preimage fibre remains the source population. -/
theorem input_future_outcomes_singleton
    (chart : ConstitutiveChart Current) (word : List Input)
    (observed : Set.range (reducedRead chart)) :
    outcomes (reducedRead chart) observed
        (reducedRead chart ∘ transportWord (inputSourceTransport chart) word) =
      {transportWord (fun input => inputQuotientTransport input) word observed.1} := by
  apply outcomes_singleton_of_factor
    (reducedRead chart) observed
    (reducedRead chart ∘ transportWord (inputSourceTransport chart) word)
    (fun face => transportWord (fun input => inputQuotientTransport input) word face)
  intro current
  exact input_history_word_exact chart word current

theorem input_all_successor_faces_factor
    (chart : ConstitutiveChart Current) (left right : Current)
    (same : reducedRead chart left = reducedRead chart right) (word : List Input) :
    reducedRead chart (transportWord (inputSourceTransport chart) word left) =
      reducedRead chart (transportWord (inputSourceTransport chart) word right) := by
  exact (inputHistoryCompression chart).quotientEqForcesEverySuccessorFace
    same () word

end

end Soma.Holonics.Physics.ConstitutiveScale

section Audit
open Soma.Holonics.Physics.ConstitutiveScale
#print axioms extractedFaceLinear_apply
#print axioms reducedRead_decoderLinear
#print axioms scalePassage_transport_boundary
#print axioms input_history_word_exact
#print axioms input_future_outcomes_singleton
#print axioms input_all_successor_faces_factor
end Audit
