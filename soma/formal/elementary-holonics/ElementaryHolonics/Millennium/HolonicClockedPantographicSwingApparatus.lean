import ElementaryHolonics.Millennium.HolonicClockedPantographicSwing
import ElementaryHolonics.Millennium.HolonicFiniteCausalAperture
import ElementaryHolonics.Millennium.PVersusNP
import Mathlib.Tactic

/-!
# Apparatus and complexity receivers for the Clocked Pantographic Swing

This file keeps CPU/GPU placement, architectural counter calibration, bounded observation, and
Turing-machine complexity outside the primitive Clocked Pantographic Swing.  A hardware
realization refines one shared semantic event body.  It may change worker population, local clock
domains, micro-occurrence fibres, and frontier shape, but it must preserve addressed boundaries,
receiver faces, obstruction lineage, and exact extent.

All introduced carriers are `[definition]`.  Every theorem is
`[proved-derived; formal-checked]`, except the explicitly named finite control, which is
`[counterexample; formal-checked]` relative to its displayed fixture.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicClockedPantographicSwingApparatus

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.HolonicSensoryWorldTube
open Soma.Holonics.Millennium.HolonicClockedPantographicSwing
open Soma.Holonics.Millennium.HolonicFiniteCausalAperture
open Soma.Holonics.Millennium.PVersusNP

/-! ## Finite placement and architectural clock domains -/

/-- [definition] One finite apparatus placement.  Co-active occurrences require distinct workers,
while local counter order is meaningful only inside a common declared clock domain. -/
structure ApparatusPlacement
    (Occurrence Worker ClockDomain : Type*) [DecidableEq Occurrence] where
  link : FiniteInteractionLink Occurrence
  worker : Occurrence → Worker
  clockDomain : Worker → ClockDomain
  counter : Occurrence → ℕ
  precedes : Occurrence → Occurrence → Prop
  sameDomainCounter_mono : ∀ {left right}, precedes left right →
    clockDomain (worker left) = clockDomain (worker right) → counter left < counter right
  coactiveWorker_injective : ∀ {face : Finset Occurrence}, face ∈ link.faces →
    Set.InjOn worker (↑face : Set Occurrence)

namespace ApparatusPlacement

variable {Occurrence Worker ClockDomain : Type*} [DecidableEq Occurrence]

/-- [proved-derived; formal-checked] A co-active independent front cannot contain more occurrences
than the worker aperture available to the placement. -/
theorem face_card_le_worker_card [Fintype Worker]
    (placement : ApparatusPlacement Occurrence Worker ClockDomain)
    {face : Finset Occurrence} (admitted : face ∈ placement.link.faces) :
    face.card ≤ Fintype.card Worker := by
  let assign : {occurrence // occurrence ∈ face} → Worker :=
    fun occurrence => placement.worker occurrence.1
  have injective : Function.Injective assign := by
    intro left right equalWorker
    apply Subtype.ext
    exact placement.coactiveWorker_injective admitted left.2 right.2 equalWorker
  simpa using Fintype.card_le_of_injective assign injective

/-- [definition] A modular hardware-counter sample retaining its wrap population. -/
structure ModularCounterSample (ClockDomain : Type*) where
  domain : ClockDomain
  modulus : ℕ
  modulus_pos : 0 < modulus
  start : Fin modulus
  finish : Fin modulus
  wraps : ℕ
  start_le_endPotential : start ≤ wraps * modulus + finish

/-- [definition] The exact unwrapped architectural counter difference. -/
def ModularCounterSample.elapsedTicks
    (sample : ModularCounterSample ClockDomain) : ℕ :=
  sample.wraps * sample.modulus + sample.finish - sample.start

/-- [proved-derived; formal-checked] Reattaching the starting phase reconstructs the exact
unwrapped end potential. -/
theorem ModularCounterSample.start_add_elapsedTicks
    (sample : ModularCounterSample ClockDomain) :
    sample.start + sample.elapsedTicks = sample.wraps * sample.modulus + sample.finish := by
  exact Nat.add_sub_of_le sample.start_le_endPotential

/-- [definition] A separately calibrated exact-seconds chart for every architectural clock domain.
It measures a run but does not generate the intrinsic semantic history. -/
structure ExteriorSecondsCalibration where
  chart : ClockDomain → ExactLocalClock ClockDomain
  chart_address : ∀ domain, (chart domain).address = domain

/-- [definition] Exact rational seconds returned after sampling a local architectural counter. -/
def exteriorSeconds
    (calibration : ExteriorSecondsCalibration (ClockDomain := ClockDomain))
    (sample : ModularCounterSample ClockDomain) : ℚ :=
  (calibration.chart sample.domain).coordinate sample.elapsedTicks

end ApparatusPlacement

/-! ## One semantic body, many reconstructible CPU/GPU micro-realizations -/

/-- [definition] The apparatus-independent event body.  Work, causal order, receiver, obstruction,
and extent are intrinsic receivers attached to the same addressed occurrence population. -/
structure SemanticEventBody
    (Source Target Face Obstruction Occurrence : Type*) where
  source : Occurrence → Source
  target : Occurrence → Target
  receive : Occurrence → Face
  obstruction : Occurrence → Obstruction
  precedes : Occurrence → Occurrence → Prop
  work : Occurrence → ℕ
  extent : Occurrence → ℕ
  extent_pos : ∀ occurrence, 0 < extent occurrence

namespace SemanticEventBody

variable {Source Target Face Obstruction SemanticOccurrence : Type*}

/-- [definition] The standing semantic holon of the event body. -/
def toHolon
    (body : SemanticEventBody Source Target Face Obstruction SemanticOccurrence) :
    Holon Source Target Face where
  Occurrence := SemanticOccurrence
  source := body.source
  target := body.target
  receive := body.receive

/-- [definition] Exact total intrinsic work on a finite semantic body. -/
def totalWork [Fintype SemanticOccurrence]
    (body : SemanticEventBody Source Target Face Obstruction SemanticOccurrence) : ℕ :=
  ∑ occurrence, body.work occurrence

end SemanticEventBody

/-- [definition] A bounded hardware realization of one fixed semantic event body.  The projection
is a refinement map from apparatus micro-occurrences to semantic occurrences. -/
structure ApparatusRealization
    {Source Target Face Obstruction SemanticOccurrence : Type*}
    (body : SemanticEventBody Source Target Face Obstruction SemanticOccurrence)
    (MicroOccurrence Worker ClockDomain : Type*)
    [DecidableEq SemanticOccurrence] [Fintype MicroOccurrence] [DecidableEq MicroOccurrence] where
  projection : MicroOccurrence → SemanticOccurrence
  microSource : MicroOccurrence → Source
  microTarget : MicroOccurrence → Target
  microReceive : MicroOccurrence → Face
  microObstruction : MicroOccurrence → Obstruction
  microExtent : MicroOccurrence → ℕ
  source_exact : ∀ micro, microSource micro = body.source (projection micro)
  target_exact : ∀ micro, microTarget micro = body.target (projection micro)
  receiver_exact : ∀ micro, microReceive micro = body.receive (projection micro)
  obstruction_exact : ∀ micro,
    microObstruction micro = body.obstruction (projection micro)
  covers : Function.Surjective projection
  extent_conserves : ∀ semantic,
    ∑ micro ∈ Finset.univ.filter (fun candidate ↦ projection candidate = semantic),
        microExtent micro = body.extent semantic
  placement : ApparatusPlacement MicroOccurrence Worker ClockDomain

namespace ApparatusRealization

variable {Source Target Face Obstruction SemanticOccurrence : Type*}
variable {body : SemanticEventBody Source Target Face Obstruction SemanticOccurrence}
variable {MicroOccurrence Worker ClockDomain : Type*}
variable [DecidableEq SemanticOccurrence] [Fintype MicroOccurrence] [DecidableEq MicroOccurrence]

/-- [definition] Every semantic event's complete apparatus reconstruction fibre. -/
def ReconstructionFibre
    (realization : ApparatusRealization body MicroOccurrence Worker ClockDomain)
    (semantic : SemanticOccurrence) : Type _ :=
  { micro : MicroOccurrence // realization.projection micro = semantic }

/-- [proved-derived; formal-checked] Every semantic event has a nonempty apparatus fibre. -/
theorem reconstructionFibre_nonempty
    (realization : ApparatusRealization body MicroOccurrence Worker ClockDomain)
    (semantic : SemanticOccurrence) :
    Nonempty (realization.ReconstructionFibre semantic) := by
  obtain ⟨micro, exact⟩ := realization.covers semantic
  exact ⟨⟨micro, exact⟩⟩

/-- [definition] The complete apparatus micro-holon. -/
def toHolon
    (realization : ApparatusRealization body MicroOccurrence Worker ClockDomain) :
    Holon Source Target Face where
  Occurrence := MicroOccurrence
  source := realization.microSource
  target := realization.microTarget
  receive := realization.microReceive

/-- [proved-derived; formal-checked] Every apparatus receiver is exactly the shared semantic
receiver at its projected occurrence. -/
theorem receiver_preserved
    (realization : ApparatusRealization body MicroOccurrence Worker ClockDomain)
    (micro : MicroOccurrence) :
    realization.microReceive micro = body.receive (realization.projection micro) :=
  realization.receiver_exact micro

end ApparatusRealization

/-- [proved-derived; formal-checked] CPU- and GPU-shaped realizations of the same body agree at the
semantic receiver whenever their micro-occurrences project to the same semantic event. -/
theorem apparatus_receiver_agreement
    {Source Target Face Obstruction SemanticOccurrence : Type*}
    {body : SemanticEventBody Source Target Face Obstruction SemanticOccurrence}
    {MicroLeft WorkerLeft DomainLeft MicroRight WorkerRight DomainRight : Type*}
    [DecidableEq SemanticOccurrence]
    [Fintype MicroLeft] [DecidableEq MicroLeft]
    [Fintype MicroRight] [DecidableEq MicroRight]
    (left : ApparatusRealization body MicroLeft WorkerLeft DomainLeft)
    (right : ApparatusRealization body MicroRight WorkerRight DomainRight)
    (leftMicro : MicroLeft) (rightMicro : MicroRight)
    (sameSemantic : left.projection leftMicro = right.projection rightMicro) :
    left.microReceive leftMicro = right.microReceive rightMicro := by
  rw [left.receiver_exact, right.receiver_exact, sameSemantic]

/-! ## Work/span/frontier and exterior observation remain different receivers -/

/-- [definition] An exact finite causal-profile receipt.  The critical path and frontier sequence
are returned objects rather than shapes inferred from elapsed seconds. -/
structure ExactCausalProfile
    {Source Target Face Obstruction Occurrence : Type*}
    (body : SemanticEventBody Source Target Face Obstruction Occurrence)
    [DecidableEq Occurrence] where
  criticalPath : List Occurrence
  criticalPath_causal : criticalPath.IsChain body.precedes
  criticalSpan : ℕ
  criticalSpan_exact : criticalSpan = (criticalPath.map body.work).sum
  frontiers : List (Finset Occurrence)

/-- [definition] Exact widths of all returned causal fronts. -/
def ExactCausalProfile.frontierWidths
    {Source Target Face Obstruction Occurrence : Type*}
    {body : SemanticEventBody Source Target Face Obstruction Occurrence}
    [DecidableEq Occurrence]
    (profile : ExactCausalProfile body) : List ℕ :=
  profile.frontiers.map Finset.card

/-- [definition] A bounded exterior observation returns every unfinished face instead of treating
the duration aperture as semantic halting. -/
structure ExteriorObservationCut
    (Occurrence Obstruction : Type*) [DecidableEq Occurrence] where
  completed : Finset Occurrence
  frontier : Finset Occurrence
  uncompleted : Finset Occurrence
  completed_frontier_disjoint : Disjoint completed frontier
  completed_uncompleted_disjoint : Disjoint completed uncompleted
  obstruction : Occurrence → Obstruction

/-! ## A finite outcome and exterior duration do not establish polynomial time -/

/-- [definition] A constant terminal receiver with an unbounded exact work ledger. -/
def constantFalseDecision (_input : Word) : Bool := false

/-- [definition] One exact work witness which grows with the complete input population. -/
def linearWorkWitness (input : Word) : ℕ := input.length + 1

/-- [counterexample; formal-checked] A two-valued deterministic terminal receiver does not bound
the work needed to reach it. -/
theorem finiteTerminalFace_does_not_bound_work (proposedBound : ℕ) :
    ∃ input : Word,
      proposedBound < linearWorkWitness input ∧ constantFalseDecision input = false := by
  refine ⟨List.replicate proposedBound false, ?_, rfl⟩
  simp [linearWorkWitness]

/-- [proved-derived; formal-checked] Binary certificate words at fixed depth still form the exact
exponential population `2 ^ depth`; a finite outcome face does not remove this search family. -/
theorem binaryCertificateWord_card (depth : ℕ) :
    Fintype.card (GeneratorWord 2 depth) = 2 ^ depth :=
  generatorWord_card 2 depth

/-- [definition] The source-specific finish line by which one clocked/holonic decider places one
decision language in `P`.  The uniform TM2 polynomial-time witness remains explicit. -/
structure UniformClockedPolynomialReceiver (language : DecisionLanguage) where
  decider : Word → Bool
  decides : Decides decider language
  tm2PolynomialTime : BooleanFunctionInPolynomialTime decider

/-- [proved-derived; formal-checked] A completed uniform clocked polynomial receiver discharges the
actual `InP` obligation for its language. -/
theorem UniformClockedPolynomialReceiver.language_inP
    {language : DecisionLanguage}
    (receiver : UniformClockedPolynomialReceiver language) : InP language :=
  ⟨receiver.decider, receiver.decides, receiver.tm2PolynomialTime⟩

section Audit

#print axioms ApparatusPlacement.face_card_le_worker_card
#print axioms ApparatusPlacement.ModularCounterSample.start_add_elapsedTicks
#print axioms ApparatusRealization.reconstructionFibre_nonempty
#print axioms ApparatusRealization.receiver_preserved
#print axioms apparatus_receiver_agreement
#print axioms finiteTerminalFace_does_not_bound_work
#print axioms binaryCertificateWord_card
#print axioms UniformClockedPolynomialReceiver.language_inP

end Audit

end Soma.Holonics.Millennium.HolonicClockedPantographicSwingApparatus
