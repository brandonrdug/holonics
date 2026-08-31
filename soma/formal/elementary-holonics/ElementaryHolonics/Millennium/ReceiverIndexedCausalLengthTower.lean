import ElementaryHolonics.Foundation.Holon
import ElementaryHolonics.Foundation.ComparisonCell
import ElementaryHolonics.Foundation.TransportLift
import ElementaryHolonics.Millennium.HolonicClockedPantographicSwing
import Mathlib.Tactic

/-!
# Receiver-indexed addressed causal length towers

This file makes the common causal-length object precise without identifying every natural-number
coordinate.  Boundary length is measured on states.  Clock length, ruler length, and resource work
are measured on complete addressed histories.  The history population is an existing `Holon`, so
serial contact retains the exact pullback occurrence and its joining equality.

A clock--ruler comparison is not an equality of quantity lines.  It is an addressed positive
rational passage whose target is the complete quotient--residue phase state.  Its reconstruction
fibre is the existing transport-lift fibre.  Parallel duration is exposed only through a receipt
carrying caller-supplied interchange and capacity-partition witnesses.

All introduced structures are `[definition]`.  Every theorem is
`[proved-derived; formal-checked]` unless its statement says otherwise.
-/

noncomputable section

namespace Soma.Holonics.Millennium.ReceiverIndexedCausalLengthTower

open Soma.Holonics
open Soma.Holonics.Foundation.Lift
open Soma.Holonics.Millennium.HolonicClockedPantographicSwing

/-! ## Boundary and passage extent lines -/

/-- [definition] A discrete extent measured on a boundary object at one exact address. -/
structure BoundaryExtent (BoundaryAddress : Type*) where
  address : BoundaryAddress
  count : ℕ

/-- [definition] A discrete directed extent measured on an enacted passage at one exact address.
Even when the coordinate equals a boundary count, this occurrence has a different type and role. -/
structure PassageExtent (PassageAddress : Type*) where
  address : PassageAddress
  count : ℕ

/-! ## Exact addressed clock--ruler comparison -/

/-- [definition] A positive addressed clock--ruler span.  The sum address prevents the source
clock and target ruler from becoming definitionally identical merely because both counts are
natural numbers.  `initialResidue` retains the section at which the comparison begins. -/
structure ClockRulerSpan (ClockAddress RulerAddress : Type*) where
  clockAddress : ClockAddress
  rulerAddress : RulerAddress
  passage : RationalClockPassage (ClockAddress ⊕ RulerAddress)
  source_exact : passage.source = Sum.inl clockAddress
  target_exact : passage.target = Sum.inr rulerAddress
  initialResidue : Fin passage.denominator

namespace ClockRulerSpan

variable {ClockAddress RulerAddress : Type*}

/-- [definition] The normalized ruler state at the comparison's declared initial section. -/
def initialState (span : ClockRulerSpan ClockAddress RulerAddress) :
    RationalClockPassage.PhaseState span.passage where
  completedTicks := 0
  residue := span.initialResidue

/-- [definition] The complete ruler state after a population of source-clock crossings. -/
def targetState (span : ClockRulerSpan ClockAddress RulerAddress) (clockTicks : ℕ) :
    RationalClockPassage.PhaseState span.passage :=
  span.passage.advanceBy span.initialState clockTicks

/-- [definition] Completed ruler cells are a receiver of the complete phase state. -/
def rulerCells (span : ClockRulerSpan ClockAddress RulerAddress) (clockTicks : ℕ) : ℕ :=
  (span.targetState clockTicks).completedTicks

/-- [definition] The within-cell phase is retained rather than rounded away. -/
def phaseResidue (span : ClockRulerSpan ClockAddress RulerAddress) (clockTicks : ℕ) :
    Fin span.passage.denominator :=
  (span.targetState clockTicks).residue

/-- [definition] Every clock-crossing population which returns one complete ruler state. -/
def ReconstructionFibre (span : ClockRulerSpan ClockAddress RulerAddress)
    (state : RationalClockPassage.PhaseState span.passage) : Type :=
  TransportLift span.targetState state

/-- [definition] Every supplied clock population inhabits the exact reconstruction fibre of its
returned ruler state. -/
def reconstructionLift (span : ClockRulerSpan ClockAddress RulerAddress) (clockTicks : ℕ) :
    span.ReconstructionFibre (span.targetState clockTicks) :=
  ofSource span.targetState clockTicks

/-- [proved-derived; formal-checked] The target state reconstructs the complete scaled potential,
including the initial phase. -/
theorem targetState_potential (span : ClockRulerSpan ClockAddress RulerAddress)
    (clockTicks : ℕ) :
    (span.targetState clockTicks).potential =
      span.initialState.potential + span.passage.numerator * clockTicks := by
  exact span.passage.potential_advanceBy span.initialState clockTicks

/-- [proved-derived; formal-checked] Serial clock populations add, while the ruler state advances
from the exact phase returned by the first population. -/
theorem targetState_add (span : ClockRulerSpan ClockAddress RulerAddress)
    (first second : ℕ) :
    span.targetState (first + second) =
      span.passage.advanceBy (span.targetState first) second := by
  exact (span.passage.advanceBy_add span.initialState first second).symm

/-- [proved-derived; formal-checked] Positive clock gearing makes the complete quotient--residue
state injective in the source crossing population. -/
theorem targetState_injective (span : ClockRulerSpan ClockAddress RulerAddress) :
    Function.Injective span.targetState := by
  intro left right equalState
  have equalPotential := congrArg RationalClockPassage.PhaseState.potential equalState
  rw [span.targetState_potential, span.targetState_potential] at equalPotential
  have equalScaled : span.passage.numerator * left = span.passage.numerator * right :=
    Nat.add_left_cancel equalPotential
  exact mul_left_cancel₀ (Nat.ne_of_gt span.passage.numerator_pos) equalScaled

/-- [proved-derived; formal-checked] Every ruler-state reconstruction fibre contains at most one
source crossing population. -/
theorem reconstructionFibre_subsingleton
    (span : ClockRulerSpan ClockAddress RulerAddress)
    (state : RationalClockPassage.PhaseState span.passage) :
    Subsingleton (span.ReconstructionFibre state) := by
  exact (subsingleton_iff_unique_source span.targetState state).2
    (fun left right leftExact rightExact =>
      span.targetState_injective (leftExact.trans rightExact.symm))

/-- [proved-derived; formal-checked] The completed ruler count and retained phase reconstruct the
complete target potential exactly. -/
theorem denominator_mul_rulerCells_add_phase
    (span : ClockRulerSpan ClockAddress RulerAddress) (clockTicks : ℕ) :
    span.passage.denominator * span.rulerCells clockTicks + span.phaseResidue clockTicks =
      span.initialState.potential + span.passage.numerator * clockTicks := by
  simpa [rulerCells, phaseResidue, RationalClockPassage.PhaseState.potential] using
    span.targetState_potential clockTicks

end ClockRulerSpan

/-! ## One receiver-indexed causal length tower -/

/-- [definition] A fixed-occurrence presentation of the existing `Holon` owner.  The separate
`History` parameter anchors the occurrence universe; `toHolon` below is the exact owner, not a
second path ontology. -/
structure AddressedHistory (History State Receiver : Type*) where
  source : History → State
  target : History → State
  receive : History → Receiver

namespace AddressedHistory

variable {History State Receiver : Type*}

/-- [definition] The exact elementary holon presented by an addressed history body. -/
def toHolon (history : AddressedHistory History State Receiver) :
    Holon State State Receiver where
  Occurrence := History
  source := history.source
  target := history.target
  receive := history.receive

/-- [definition] Serial contact is the existing pullback population with its joining equality. -/
abbrev Interaction (history : AddressedHistory History State Receiver) :=
  Holon.Interaction history.toHolon history.toHolon

/-- [definition] Cartesian co-presence retains both history occurrences without asserting
execution independence. -/
def cartesian (history : AddressedHistory History State Receiver) :=
  history.toHolon.cartesian history.toHolon

end AddressedHistory

/-- [definition] One tower level.  `history` owns complete addressed path occurrences and their
receiver faces.  Boundary size lives on states; clock length and resource work live on histories.
The ruler state is derived through `clockRuler`, so quotient and phase cannot silently separate. -/
structure Tower
    (History State BoundaryAddress ClockAddress RulerAddress Receiver Resource : Type*) where
  history : AddressedHistory History State Receiver
  boundaryAddress : BoundaryAddress
  clockAddress : ClockAddress
  rulerAddress : RulerAddress
  boundaryLength : State → ℕ
  clockLength : History → ℕ
  resourceWork : History → Resource → ℕ
  resourceCapacity : Resource → ℕ
  resourceCapacity_pos : ∀ resource, 0 < resourceCapacity resource
  clockRuler : ClockRulerSpan ClockAddress RulerAddress
  clockAddress_exact : clockRuler.clockAddress = clockAddress
  rulerAddress_exact : clockRuler.rulerAddress = rulerAddress
  stay : State → History
  stay_source : ∀ state, history.source (stay state) = state
  stay_target : ∀ state, history.target (stay state) = state
  stay_clockLength : ∀ state, clockLength (stay state) = 0
  stay_resourceWork : ∀ state resource, resourceWork (stay state) resource = 0

namespace Tower

variable {History State BoundaryAddress ClockAddress RulerAddress Receiver Resource : Type*}

/-- [definition] Serial composition remains the existing pullback passage.  Its occurrence is the
joined pair plus the exact middle-boundary equality; it is not condensed back into `History`. -/
def serialHolon
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource) :=
  tower.history.toHolon.comp tower.history.toHolon

/-- [definition] The receiver of a serial occurrence retains both ordered component faces. -/
def serialReceiver
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (joined : tower.history.Interaction) : Receiver × Receiver :=
  (tower.history.receive joined.left, tower.history.receive joined.right)

/-- [definition] Clock length of an exact pullback interaction is the ordered serial sum. -/
def serialClockLength
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (joined : tower.history.Interaction) : ℕ :=
  tower.clockLength joined.left + tower.clockLength joined.right

/-- [definition] Resource work of an exact pullback interaction retains both caused populations. -/
def serialResourceWork
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (joined : tower.history.Interaction) (resource : Resource) : ℕ :=
  tower.resourceWork joined.left resource + tower.resourceWork joined.right resource

/-- [definition] Complete ruler phase after the serial sum of two joined histories. -/
def serialRulerState
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (joined : tower.history.Interaction) :
    RationalClockPassage.PhaseState tower.clockRuler.passage :=
  tower.clockRuler.targetState (tower.serialClockLength joined)

/-- [proved-derived; formal-checked] The serial receiver reconstruction fibre is exactly the two
component fibres plus their joining equality.  No continuing-history condensation is involved. -/
def serialReconstructionFibreEquiv
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (face : Receiver × Receiver) :
    tower.serialHolon.ReconstructionFibre face ≃
      Holon.CompositeReconstructionFibre
        tower.history.toHolon tower.history.toHolon face :=
  tower.history.toHolon.compReconstructionFibreEquiv tower.history.toHolon face

/-- [proved-derived; formal-checked] Rebracketing three serial histories preserves the exact
three occurrences, both joining equalities, and the exterior source and target. -/
def serialAssociator
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource) :=
  AddressedPassage.compAssociator tower.history.toHolon.toPassage
    tower.history.toHolon.toPassage tower.history.toHolon.toPassage

/-- [proved-derived; formal-checked] The serial associator also preserves every complete
source--target reconstruction fibre; it is not merely an endpoint-count equality. -/
def serialAssociatorFibreEquiv
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (source target : State) :
    (AddressedPassage.comp tower.history.toHolon.toPassage
      (AddressedPassage.comp tower.history.toHolon.toPassage
        tower.history.toHolon.toPassage)).Fibre source target ≃
    (AddressedPassage.comp
      (AddressedPassage.comp tower.history.toHolon.toPassage
        tower.history.toHolon.toPassage)
      tower.history.toHolon.toPassage).Fibre source target :=
  AddressedPassage.fibreEquivOfPassageEquiv tower.serialAssociator source target

/-- [definition] Every complete addressed history beginning at one boundary state. -/
def CausalPotentialFibre
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (source : State) : Type _ :=
  { occurrence : History // tower.history.source occurrence = source }

/-- [definition] The complete family of boundary states of one declared size together with every
causal history beginning at each such state.  This is the family-level carrier used by complexity
receivers; it is not a single favorable history. -/
def BoundaryIndexedPotentialFamily
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (boundaryCount : ℕ) : Type _ :=
  Σ state : { state : State // tower.boundaryLength state = boundaryCount },
    tower.CausalPotentialFibre state.1

/-- [definition] The unresolved continuation population behind one returned receiver face. -/
def ReceiverReconstructionFibre
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (source : State) (face : Receiver) : Type _ :=
  { potential : tower.CausalPotentialFibre source //
      tower.history.receive potential.1 = face }

/-- [definition] Complete quotient--residue ruler state of one addressed causal history. -/
def rulerState
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (history : History) :
    RationalClockPassage.PhaseState tower.clockRuler.passage :=
  tower.clockRuler.targetState (tower.clockLength history)

/-- [definition] Completed ruler cells are a receiver shadow of `rulerState`. -/
def rulerLength
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (history : History) : ℕ :=
  (tower.rulerState history).completedTicks

/-- [definition] Addressed boundary extent; the count is not silently usable as passage time. -/
def boundaryExtent
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (state : State) : BoundaryExtent BoundaryAddress :=
  ⟨tower.boundaryAddress, tower.boundaryLength state⟩

/-- [definition] Addressed local-clock passage extent. -/
def clockExtent
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (history : History) : PassageExtent ClockAddress :=
  ⟨tower.clockAddress, tower.clockLength history⟩

/-- [definition] Addressed completed ruler-cell passage extent.  The retained phase remains in
`rulerState` and is part of its reconstruction fibre. -/
def rulerExtent
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (history : History) : PassageExtent RulerAddress :=
  ⟨tower.rulerAddress, tower.rulerLength history⟩

/-- [definition] The exact clock population behind one ruler state. -/
def ClockRulerReconstructionFibre
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (state : RationalClockPassage.PhaseState tower.clockRuler.passage) : Type :=
  tower.clockRuler.ReconstructionFibre state

/-- [proved-derived; formal-checked] The clock population of every history inhabits the complete
fibre behind its returned ruler state. -/
def clockRulerReconstructionLift
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (history : History) :
    tower.ClockRulerReconstructionFibre (tower.rulerState history) :=
  tower.clockRuler.reconstructionLift (tower.clockLength history)

/-- [definition] The stationary history is the zero-length causal potential at its boundary. -/
def stayPotential
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (state : State) : tower.CausalPotentialFibre state :=
  ⟨tower.stay state, tower.stay_source state⟩

/-- [definition] Complete joined histories extending a source-indexed causal potential. -/
def SerialCausalPotentialFibre
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (source : State) : Type _ :=
  { joined : tower.history.Interaction // tower.history.source joined.left = source }

/-- [definition] Serial extension returns the pullback occurrence itself.  No map may collapse it
into a pre-existing history population. -/
def extendPotential
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    {source : State} (left : tower.CausalPotentialFibre source) (right : History)
    (joins : tower.history.target left.1 = tower.history.source right) :
    tower.SerialCausalPotentialFibre source :=
  ⟨⟨left.1, right, joins⟩, left.2⟩

/-- [proved-derived; formal-checked] Serial histories add causal clock length. -/
theorem clockLength_serial
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (joined : tower.history.Interaction) :
    tower.serialClockLength joined =
      tower.clockLength joined.left + tower.clockLength joined.right := rfl

/-- [proved-derived; formal-checked] Ruler transport of a serial history advances from the exact
phase returned by its left history; completed-cell counts are not incorrectly added in isolation. -/
theorem rulerState_serial
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (joined : tower.history.Interaction) :
    tower.serialRulerState joined =
      tower.clockRuler.passage.advanceBy
        (tower.rulerState joined.left) (tower.clockLength joined.right) := by
  change tower.clockRuler.targetState
      (tower.clockLength joined.left + tower.clockLength joined.right) =
    tower.clockRuler.passage.advanceBy
      (tower.clockRuler.targetState (tower.clockLength joined.left))
      (tower.clockLength joined.right)
  rw [ClockRulerSpan.targetState_add]

/-- [proved-derived; formal-checked] Serial resource work adds on every addressed resource axis. -/
theorem resourceWork_serial
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (joined : tower.history.Interaction) (resource : Resource) :
    tower.serialResourceWork joined resource =
      tower.resourceWork joined.left resource + tower.resourceWork joined.right resource := rfl

/-! ## Parallel receiver requires explicit interchange and capacity witnesses -/

/-- [definition] A parallel receipt does not infer independence from co-presence.  It retains the
two possible serial orders as distinct joined histories, proves that both orders return a common
successor, preserves their two receiver faces through the swap braiding, and carries
source-specific obstruction and logical-resource equalities.  Per-resource capacity is actually
partitioned between the two branches.  Only after these obligations are supplied may the receiver
read elapsed length as `max` rather than a serial sum. -/
structure ParallelInterchangeReceipt
    (tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource)
    (left right : History)
    (Obstruction LogicalResourceState : Type*)
    (obstruction : tower.history.Interaction → Obstruction)
    (logicalResourceState : tower.history.Interaction → LogicalResourceState) where
  interchangeCell : AddressedPassage.ComparisonCell
    tower.serialHolon.toPassage tower.serialHolon.toPassage
  left_first : interchangeCell.left.left = left
  right_first : interchangeCell.right.left = right
  right_clock_preserved : tower.clockLength interchangeCell.left.right = tower.clockLength right
  left_clock_preserved : tower.clockLength interchangeCell.right.right = tower.clockLength left
  right_work_preserved : ∀ resource,
    tower.resourceWork interchangeCell.left.right resource = tower.resourceWork right resource
  left_work_preserved : ∀ resource,
    tower.resourceWork interchangeCell.right.right resource = tower.resourceWork left resource
  interchange_commutes : interchangeCell.Commutes
  receiver_braiding :
    tower.serialReceiver interchangeCell.left =
      ((tower.serialReceiver interchangeCell.right).2,
        (tower.serialReceiver interchangeCell.right).1)
  obstruction_interchange :
    obstruction interchangeCell.left = obstruction interchangeCell.right
  logicalResource_interchange :
    logicalResourceState interchangeCell.left = logicalResourceState interchangeCell.right
  leftCapacity : Resource → ℕ
  rightCapacity : Resource → ℕ
  capacity_partition : ∀ resource,
    leftCapacity resource + rightCapacity resource ≤ tower.resourceCapacity resource
  left_capacity_carries : ∀ resource,
    tower.resourceWork left resource ≤
      leftCapacity resource * max (tower.clockLength left) (tower.clockLength right)
  right_capacity_carries : ∀ resource,
    tower.resourceWork right resource ≤
      rightCapacity resource * max (tower.clockLength left) (tower.clockLength right)

namespace ParallelInterchangeReceipt

variable
    {tower : Tower History State BoundaryAddress ClockAddress RulerAddress Receiver Resource}
    {left right : History}
    {Obstruction LogicalResourceState : Type*}
    {obstruction : tower.history.Interaction → Obstruction}
    {logicalResourceState : tower.history.Interaction → LogicalResourceState}

/-- [definition] Exact paired lineage retained by the Cartesian history holon. -/
def occurrence
    (_receipt : ParallelInterchangeReceipt tower left right
      Obstruction LogicalResourceState obstruction logicalResourceState) :
    tower.history.cartesian.Occurrence :=
  (left, right)

/-- [definition] Parallel elapsed length is the larger branch length only after the receipt exists. -/
def clockLength
    (_receipt : ParallelInterchangeReceipt tower left right
      Obstruction LogicalResourceState obstruction logicalResourceState) : ℕ :=
  max (tower.clockLength left) (tower.clockLength right)

/-- [definition] Parallel work remains the sum of both caused resource populations. -/
def resourceWork
    (_receipt : ParallelInterchangeReceipt tower left right
      Obstruction LogicalResourceState obstruction logicalResourceState)
    (resource : Resource) : ℕ :=
  tower.resourceWork left resource + tower.resourceWork right resource

/-- [proved-derived; formal-checked] The admitted parallel receiver returns max span. -/
theorem clockLength_eq_max
    (receipt : ParallelInterchangeReceipt tower left right
      Obstruction LogicalResourceState obstruction logicalResourceState) :
    receipt.clockLength = max (tower.clockLength left) (tower.clockLength right) := rfl

/-- [proved-derived; formal-checked] The complete paired receiver reconstruction fibre is exactly
the product of the component fibres; parallel projection does not merge their histories. -/
def reconstructionFibreEquiv
    (_receipt : ParallelInterchangeReceipt tower left right
      Obstruction LogicalResourceState obstruction logicalResourceState)
    (face : Receiver × Receiver) :
    tower.history.cartesian.ReconstructionFibre face ≃
      tower.history.toHolon.ReconstructionFibre face.1 ×
        tower.history.toHolon.ReconstructionFibre face.2 :=
  tower.history.toHolon.cartesianReconstructionFibreEquiv tower.history.toHolon face

/-- [proved-derived; formal-checked] The supplied capacity partition carries the complete summed
work through the admitted parallel span. -/
theorem resourceWork_le_capacity_mul_clockLength
    (receipt : ParallelInterchangeReceipt tower left right
      Obstruction LogicalResourceState obstruction logicalResourceState)
    (resource : Resource) :
    receipt.resourceWork resource ≤
      tower.resourceCapacity resource * receipt.clockLength :=
  calc
    tower.resourceWork left resource + tower.resourceWork right resource ≤
        receipt.leftCapacity resource * receipt.clockLength +
          receipt.rightCapacity resource * receipt.clockLength :=
      Nat.add_le_add (receipt.left_capacity_carries resource)
        (receipt.right_capacity_carries resource)
    _ = (receipt.leftCapacity resource + receipt.rightCapacity resource) *
        receipt.clockLength := by rw [Nat.add_mul]
    _ ≤ tower.resourceCapacity resource * receipt.clockLength :=
      Nat.mul_le_mul_right receipt.clockLength (receipt.capacity_partition resource)

/-- [proved-derived; formal-checked] If every comparison cell beginning with the two proposed
branches fails exact target commutation, no parallel-interchange receipt exists.  Equal durations,
braided receiver faces, or available capacity cannot repair that higher-cell defect. -/
theorem no_receipt_of_no_commuting_cell
    (noCommutingCell :
      ∀ cell : AddressedPassage.ComparisonCell
          tower.serialHolon.toPassage tower.serialHolon.toPassage,
        cell.left.left = left → cell.right.left = right → ¬ cell.Commutes) :
    ¬ Nonempty (ParallelInterchangeReceipt tower left right
      Obstruction LogicalResourceState obstruction logicalResourceState) := by
  rintro ⟨receipt⟩
  exact noCommutingCell receipt.interchangeCell receipt.left_first receipt.right_first
    receipt.interchange_commutes

end ParallelInterchangeReceipt

end Tower

/-! ## Scale/rebase naturality and complete history fibres -/

/-- [definition] A scale passage transports states, histories, receivers, addresses, resource
axes, and every extent chart.  Each displayed square is a field rather than an inference from
equal counts.  `rulerStateTransport` acts on the complete quotient--residue state. -/
structure ScaleRebase
    {FineHistory FineState FineBoundaryAddress FineClockAddress FineRulerAddress
      FineReceiver FineResource : Type*}
    {CoarseHistory CoarseState CoarseBoundaryAddress CoarseClockAddress CoarseRulerAddress
      CoarseReceiver CoarseResource : Type*}
    (fine : Tower FineHistory FineState FineBoundaryAddress FineClockAddress FineRulerAddress
      FineReceiver FineResource)
    (coarse : Tower CoarseHistory CoarseState CoarseBoundaryAddress CoarseClockAddress CoarseRulerAddress
      CoarseReceiver CoarseResource) where
  stateTransport : FineState → CoarseState
  historyTransport : FineHistory → CoarseHistory
  receiverTransport : FineReceiver → CoarseReceiver
  boundaryAddressTransport : FineBoundaryAddress → CoarseBoundaryAddress
  clockAddressTransport : FineClockAddress → CoarseClockAddress
  rulerAddressTransport : FineRulerAddress → CoarseRulerAddress
  resourceTransport : FineResource → CoarseResource
  boundaryCountTransport : ℕ →+ ℕ
  clockCountTransport : ℕ →+ ℕ
  resourceCountTransport : ℕ →+ ℕ
  rulerStateTransport :
    RationalClockPassage.PhaseState fine.clockRuler.passage →
      RationalClockPassage.PhaseState coarse.clockRuler.passage
  boundaryAddress_natural :
    boundaryAddressTransport fine.boundaryAddress = coarse.boundaryAddress
  clockAddress_natural : clockAddressTransport fine.clockAddress = coarse.clockAddress
  rulerAddress_natural : rulerAddressTransport fine.rulerAddress = coarse.rulerAddress
  source_natural : ∀ history,
    coarse.history.source (historyTransport history) =
      stateTransport (fine.history.source history)
  target_natural : ∀ history,
    coarse.history.target (historyTransport history) =
      stateTransport (fine.history.target history)
  receiver_natural : ∀ history,
    coarse.history.receive (historyTransport history) =
      receiverTransport (fine.history.receive history)
  boundaryLength_natural : ∀ state,
    coarse.boundaryLength (stateTransport state) =
      boundaryCountTransport (fine.boundaryLength state)
  clockLength_natural : ∀ history,
    coarse.clockLength (historyTransport history) =
      clockCountTransport (fine.clockLength history)
  resourceWork_natural : ∀ history resource,
    coarse.resourceWork (historyTransport history) (resourceTransport resource) =
      resourceCountTransport (fine.resourceWork history resource)
  rulerState_natural : ∀ history,
    coarse.rulerState (historyTransport history) =
      rulerStateTransport (fine.rulerState history)
  stay_natural : ∀ state,
    historyTransport (fine.stay state) = coarse.stay (stateTransport state)

namespace ScaleRebase

variable
    {FineHistory FineState FineBoundaryAddress FineClockAddress FineRulerAddress
      FineReceiver FineResource : Type*}
    {CoarseHistory CoarseState CoarseBoundaryAddress CoarseClockAddress CoarseRulerAddress
      CoarseReceiver CoarseResource : Type*}
    {fine : Tower FineHistory FineState FineBoundaryAddress FineClockAddress FineRulerAddress
      FineReceiver FineResource}
    {coarse : Tower CoarseHistory CoarseState CoarseBoundaryAddress CoarseClockAddress CoarseRulerAddress
      CoarseReceiver CoarseResource}

/-- [definition] Identity rebase preserves every occurrence, address, extent, receiver, and exact
serial interaction. -/
def identity
    (tower : Tower FineHistory FineState FineBoundaryAddress FineClockAddress FineRulerAddress
      FineReceiver FineResource) : ScaleRebase tower tower where
  stateTransport := id
  historyTransport := id
  receiverTransport := id
  boundaryAddressTransport := id
  clockAddressTransport := id
  rulerAddressTransport := id
  resourceTransport := id
  boundaryCountTransport := AddMonoidHom.id ℕ
  clockCountTransport := AddMonoidHom.id ℕ
  resourceCountTransport := AddMonoidHom.id ℕ
  rulerStateTransport := id
  boundaryAddress_natural := rfl
  clockAddress_natural := rfl
  rulerAddress_natural := rfl
  source_natural := fun _ => rfl
  target_natural := fun _ => rfl
  receiver_natural := fun _ => rfl
  boundaryLength_natural := fun _ => rfl
  clockLength_natural := fun _ => rfl
  resourceWork_natural := fun _ _ => rfl
  rulerState_natural := fun _ => rfl
  stay_natural := fun _ => rfl

/-- [definition] Scale rebases compose in the same order as their state and history transports.
Every naturality square is retained in the composite, including complete ruler phase and serial
pullback lineage. -/
def comp
    {MiddleHistory MiddleState MiddleBoundaryAddress MiddleClockAddress MiddleRulerAddress
      MiddleReceiver MiddleResource : Type*}
    {middle : Tower MiddleHistory MiddleState MiddleBoundaryAddress MiddleClockAddress
      MiddleRulerAddress MiddleReceiver MiddleResource}
    (fineToMiddle : ScaleRebase fine middle)
    (middleToCoarse : ScaleRebase middle coarse) : ScaleRebase fine coarse where
  stateTransport := fun state => middleToCoarse.stateTransport (fineToMiddle.stateTransport state)
  historyTransport := fun history =>
    middleToCoarse.historyTransport (fineToMiddle.historyTransport history)
  receiverTransport := fun receiver =>
    middleToCoarse.receiverTransport (fineToMiddle.receiverTransport receiver)
  boundaryAddressTransport := fun address =>
    middleToCoarse.boundaryAddressTransport (fineToMiddle.boundaryAddressTransport address)
  clockAddressTransport := fun address =>
    middleToCoarse.clockAddressTransport (fineToMiddle.clockAddressTransport address)
  rulerAddressTransport := fun address =>
    middleToCoarse.rulerAddressTransport (fineToMiddle.rulerAddressTransport address)
  resourceTransport := fun resource =>
    middleToCoarse.resourceTransport (fineToMiddle.resourceTransport resource)
  boundaryCountTransport :=
    middleToCoarse.boundaryCountTransport.comp fineToMiddle.boundaryCountTransport
  clockCountTransport :=
    middleToCoarse.clockCountTransport.comp fineToMiddle.clockCountTransport
  resourceCountTransport :=
    middleToCoarse.resourceCountTransport.comp fineToMiddle.resourceCountTransport
  rulerStateTransport := fun state =>
    middleToCoarse.rulerStateTransport (fineToMiddle.rulerStateTransport state)
  boundaryAddress_natural := by
    rw [fineToMiddle.boundaryAddress_natural, middleToCoarse.boundaryAddress_natural]
  clockAddress_natural := by
    rw [fineToMiddle.clockAddress_natural, middleToCoarse.clockAddress_natural]
  rulerAddress_natural := by
    rw [fineToMiddle.rulerAddress_natural, middleToCoarse.rulerAddress_natural]
  source_natural := by
    intro history
    rw [middleToCoarse.source_natural, fineToMiddle.source_natural]
  target_natural := by
    intro history
    rw [middleToCoarse.target_natural, fineToMiddle.target_natural]
  receiver_natural := by
    intro history
    rw [middleToCoarse.receiver_natural, fineToMiddle.receiver_natural]
  boundaryLength_natural := by
    intro state
    rw [middleToCoarse.boundaryLength_natural, fineToMiddle.boundaryLength_natural]
    rfl
  clockLength_natural := by
    intro history
    rw [middleToCoarse.clockLength_natural, fineToMiddle.clockLength_natural]
    rfl
  resourceWork_natural := by
    intro history resource
    rw [middleToCoarse.resourceWork_natural, fineToMiddle.resourceWork_natural]
    rfl
  rulerState_natural := by
    intro history
    rw [middleToCoarse.rulerState_natural, fineToMiddle.rulerState_natural]
  stay_natural := by
    intro state
    rw [fineToMiddle.stay_natural, middleToCoarse.stay_natural]

/-- [proved-derived; formal-checked] Scale transport carries an exact serial pullback occurrence
to an exact serial pullback occurrence.  The joining equality is transported, not recomputed from
endpoint coincidence. -/
def transportInteraction (passage : ScaleRebase fine coarse)
    (joined : fine.history.Interaction) : coarse.history.Interaction where
  left := passage.historyTransport joined.left
  right := passage.historyTransport joined.right
  joins := by
    have targetNatural := passage.target_natural (show FineHistory from joined.left)
    have sourceNatural := passage.source_natural (show FineHistory from joined.right)
    change coarse.history.target (passage.historyTransport joined.left) =
      coarse.history.source (passage.historyTransport joined.right)
    rw [targetNatural, sourceNatural]
    exact congrArg passage.stateTransport joined.joins

@[simp] theorem transportInteraction_left (passage : ScaleRebase fine coarse)
    (joined : fine.history.Interaction) :
    (passage.transportInteraction joined).left = passage.historyTransport joined.left := rfl

@[simp] theorem transportInteraction_right (passage : ScaleRebase fine coarse)
    (joined : fine.history.Interaction) :
    (passage.transportInteraction joined).right = passage.historyTransport joined.right := rfl

/-- [proved-derived; formal-checked] Scale transport carries the complete serial causal-potential
fibre and its original boundary index. -/
def transportSerialPotential (passage : ScaleRebase fine coarse) {source : FineState}
    (potential : fine.SerialCausalPotentialFibre source) :
    coarse.SerialCausalPotentialFibre (passage.stateTransport source) :=
  ⟨passage.transportInteraction potential.1, by
    have sourceNatural := passage.source_natural
      (show FineHistory from potential.1.left)
    change coarse.history.source (passage.historyTransport potential.1.left) =
      passage.stateTransport source
    rw [sourceNatural]
    exact congrArg passage.stateTransport potential.2⟩

/-- [definition] The complete fine-history population behind one coarse history. -/
def ReconstructionFibre (passage : ScaleRebase fine coarse)
    (coarseHistory : CoarseHistory) : Type _ :=
  TransportLift passage.historyTransport coarseHistory

/-- [definition] Every transported fine history inhabits its exact coarse reconstruction fibre. -/
def reconstructionLift (passage : ScaleRebase fine coarse)
    (fineHistory : FineHistory) :
    passage.ReconstructionFibre (passage.historyTransport fineHistory) :=
  ofSource passage.historyTransport fineHistory

/-- [proved-derived; formal-checked] Reconstruction through two scales is the complete dependent
sum of an intermediate lift and a fine lift.  Composition therefore retains every collapsed
middle and fine history instead of choosing a decoder. -/
def compReconstructionFibreEquiv
    {MiddleHistory MiddleState MiddleBoundaryAddress MiddleClockAddress MiddleRulerAddress
      MiddleReceiver MiddleResource : Type*}
    {middle : Tower MiddleHistory MiddleState MiddleBoundaryAddress MiddleClockAddress
      MiddleRulerAddress MiddleReceiver MiddleResource}
    (fineToMiddle : ScaleRebase fine middle)
    (middleToCoarse : ScaleRebase middle coarse)
    (coarseHistory : CoarseHistory) :
    (fineToMiddle.comp middleToCoarse).ReconstructionFibre coarseHistory ≃
      Σ middleHistory : middleToCoarse.ReconstructionFibre coarseHistory,
        fineToMiddle.ReconstructionFibre middleHistory.1 where
  toFun fineHistory :=
    ⟨⟨fineToMiddle.historyTransport fineHistory.1, fineHistory.2⟩,
      ⟨fineHistory.1, rfl⟩⟩
  invFun histories :=
    ⟨histories.2.1, by
      change middleToCoarse.historyTransport
        (fineToMiddle.historyTransport histories.2.1) = coarseHistory
      rw [histories.2.2, histories.1.2]⟩
  left_inv fineHistory := by
    apply Subtype.ext
    rfl
  right_inv histories := by
    rcases histories with ⟨⟨middleHistory, middleExact⟩, ⟨fineHistory, fineExact⟩⟩
    cases fineExact
    rfl

/-- [proved-derived; formal-checked] A transported causal potential remains based at the
transported source state. -/
def transportPotential (passage : ScaleRebase fine coarse) {source : FineState}
    (potential : fine.CausalPotentialFibre source) :
    coarse.CausalPotentialFibre (passage.stateTransport source) :=
  ⟨passage.historyTransport potential.1, by
    rw [passage.source_natural, potential.2]⟩

/-- [proved-derived; formal-checked] A transported receiver potential lands in the corresponding
coarse receiver reconstruction fibre. -/
def transportReceiverPotential (passage : ScaleRebase fine coarse)
    {source : FineState} {face : FineReceiver}
    (potential : fine.ReceiverReconstructionFibre source face) :
    coarse.ReceiverReconstructionFibre
      (passage.stateTransport source) (passage.receiverTransport face) :=
  ⟨⟨passage.historyTransport potential.1.1, by
      rw [passage.source_natural, potential.1.2]⟩,
    by
      change coarse.history.receive (passage.historyTransport potential.1.1) =
        passage.receiverTransport face
      rw [passage.receiver_natural, potential.2]⟩

end ScaleRebase

/-! ## Finite positive and negative controls -/

namespace FiniteControl

/-- [definition] Three addressed boundary states for a nontrivial finite tower. -/
inductive State
  | source
  | middle
  | target
  deriving DecidableEq, Repr

/-- [definition] Stationary histories plus two genuinely directed histories. -/
inductive History
  | stay : State → History
  | first
  | second
  deriving DecidableEq, Repr

def source : History → State
  | .stay state => state
  | .first => .source
  | .second => .middle

def target : History → State
  | .stay state => state
  | .first => .middle
  | .second => .target

def receive : History → State := target

def clockLength : History → ℕ
  | .stay _ => 0
  | .first => 1
  | .second => 2

def resourceWork : History → Unit → ℕ
  | .stay _, _ => 0
  | .first, _ => 1
  | .second, _ => 2

/-- [definition] Identity-rate comparison between distinct clock and ruler addresses. -/
def clockRuler : ClockRulerSpan Unit Unit where
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

/-- [definition] A concrete nontrivial tower.  It contains distinct stationary, first, and second
histories and therefore prevents the general laws from being vacuous. -/
def tower : Tower History State Unit Unit Unit State Unit where
  history :=
    { source := source
      target := target
      receive := receive }
  boundaryAddress := ()
  clockAddress := ()
  rulerAddress := ()
  boundaryLength
    | .source => 1
    | .middle => 2
    | .target => 3
  clockLength := clockLength
  resourceWork := resourceWork
  resourceCapacity := fun _ => 4
  resourceCapacity_pos := fun _ => by decide
  clockRuler := clockRuler
  clockAddress_exact := rfl
  rulerAddress_exact := rfl
  stay := History.stay
  stay_source := fun _ => rfl
  stay_target := fun _ => rfl
  stay_clockLength := fun _ => rfl
  stay_resourceWork := fun _ _ => rfl

/-- [definition] The two directed histories meet at the exact middle boundary. -/
def firstThenSecond : tower.history.Interaction :=
  ⟨.first, .second, rfl⟩

/-- [proved-derived; formal-checked] The serial occurrence retains both distinct histories. -/
theorem firstThenSecond_components :
    firstThenSecond.left = .first ∧ firstThenSecond.right = .second :=
  ⟨rfl, rfl⟩

/-- [proved-derived; formal-checked] The nontrivial serial clock length is the exact sum. -/
theorem firstThenSecond_clockLength : tower.serialClockLength firstThenSecond = 3 := by
  decide

/-- [counterexample; formal-checked] Equal natural coordinates do not identify a situated
boundary extent with a situated passage extent. -/
theorem equal_count_does_not_identify_extent :
    (tower.boundaryExtent .source).count = (tower.clockExtent .first).count ∧
      (Sum.inl (tower.boundaryExtent .source) :
          BoundaryExtent Unit ⊕ PassageExtent Unit) ≠
        Sum.inr (tower.clockExtent .first) := by
  constructor
  · decide
  · simp

/-- [proved-derived; formal-checked] Identity clock gearing returns three complete ruler cells and
zero residual phase after the serial history. -/
theorem firstThenSecond_ruler :
    (tower.serialRulerState firstThenSecond).completedTicks = 3 ∧
      (tower.serialRulerState firstThenSecond).residue.val = 0 := by
  decide

/-- [definition] The first history occupies the complete source-indexed potential fibre. -/
def firstPotential : tower.CausalPotentialFibre .source :=
  ⟨.first, rfl⟩

/-- [definition] Extending by the second history returns the exact pullback occurrence. -/
def extendedPotential : tower.SerialCausalPotentialFibre .source :=
  tower.extendPotential firstPotential .second rfl

/-- [proved-derived; formal-checked] Extension did not collapse either component occurrence. -/
theorem extendedPotential_components :
    extendedPotential.1.left = .first ∧ extendedPotential.1.right = .second :=
  ⟨rfl, rfl⟩

/-- [definition] A genuine parallel receipt for two stationary, receiver-indistinguishable
histories.  Its higher cell compares the two ordered serial occurrences explicitly. -/
def stationaryParallelReceipt :
    Tower.ParallelInterchangeReceipt tower (.stay .source) (.stay .source)
      Unit Unit (fun _ => ()) (fun _ => ()) where
  interchangeCell :=
    { left := ⟨.stay .source, .stay .source, rfl⟩
      right := ⟨.stay .source, .stay .source, rfl⟩
      source_exact := rfl }
  left_first := rfl
  right_first := rfl
  right_clock_preserved := rfl
  left_clock_preserved := rfl
  right_work_preserved := fun _ => rfl
  left_work_preserved := fun _ => rfl
  interchange_commutes := rfl
  receiver_braiding := rfl
  obstruction_interchange := rfl
  logicalResource_interchange := rfl
  leftCapacity := fun _ => 0
  rightCapacity := fun _ => 0
  capacity_partition := by
    intro resource
    cases resource
    decide
  left_capacity_carries := by
    intro resource
    cases resource
    decide
  right_capacity_carries := by
    intro resource
    cases resource
    decide

/-- [proved-derived; formal-checked] The positive control returns zero parallel duration. -/
theorem stationaryParallel_clockLength : stationaryParallelReceipt.clockLength = 0 := by
  decide

/-- [proved-derived; formal-checked] Identity scale transport is inhabited on a nontrivial tower. -/
def identityScale : ScaleRebase tower tower := ScaleRebase.identity tower

/-- [definition] A half-rate ruler used to expose why quotient-only clock readings are lossy. -/
def halfRateClockRuler : ClockRulerSpan Unit Unit where
  clockAddress := ()
  rulerAddress := ()
  passage :=
    { source := Sum.inl ()
      target := Sum.inr ()
      numerator := 1
      denominator := 2
      numerator_pos := by decide
      denominator_pos := by decide }
  source_exact := rfl
  target_exact := rfl
  initialResidue := ⟨0, by decide⟩

/-- [counterexample; formal-checked] Completed ruler cells alone identify zero and one source
crossing at half rate, while the retained phase separates them. -/
theorem quotientOnly_collides_phaseSeparates :
    halfRateClockRuler.rulerCells 0 = halfRateClockRuler.rulerCells 1 ∧
      halfRateClockRuler.phaseResidue 0 ≠ halfRateClockRuler.phaseResidue 1 := by
  decide

end FiniteControl

/-! A nontrivial diamond whose two first receiver faces differ but whose complete routes commute. -/

namespace ParallelControl

inductive State
  | source
  | leftMiddle
  | rightMiddle
  | target
  deriving DecidableEq, Repr

inductive History
  | stay : State → History
  | left
  | right
  | closeLeft
  | closeRight
  deriving DecidableEq, Repr

def source : History → State
  | .stay state => state
  | .left => .source
  | .right => .source
  | .closeLeft => .leftMiddle
  | .closeRight => .rightMiddle

def target : History → State
  | .stay state => state
  | .left => .leftMiddle
  | .right => .rightMiddle
  | .closeLeft => .target
  | .closeRight => .target

/-- The second occurrence of each route returns the other branch's face, making the complete
receiver current invariant under the swap braiding. -/
def receive : History → State
  | .stay state => state
  | .left => .leftMiddle
  | .right => .rightMiddle
  | .closeLeft => .rightMiddle
  | .closeRight => .leftMiddle

def clockLength : History → ℕ
  | .stay _ => 0
  | .left | .closeRight => 2
  | .right | .closeLeft => 3

def resourceWork : History → Unit → ℕ
  | .stay _, _ => 0
  | .left, _ => 2
  | .right, _ => 3
  | .closeLeft, _ => 3
  | .closeRight, _ => 2

def tower : Tower History State Unit Unit Unit State Unit where
  history :=
    { source := source
      target := target
      receive := receive }
  boundaryAddress := ()
  clockAddress := ()
  rulerAddress := ()
  boundaryLength
    | .source => 1
    | .leftMiddle | .rightMiddle => 2
    | .target => 3
  clockLength := clockLength
  resourceWork := resourceWork
  resourceCapacity := fun _ => 2
  resourceCapacity_pos := fun _ => by decide
  clockRuler := FiniteControl.clockRuler
  clockAddress_exact := rfl
  rulerAddress_exact := rfl
  stay := History.stay
  stay_source := fun _ => rfl
  stay_target := fun _ => rfl
  stay_clockLength := fun _ => rfl
  stay_resourceWork := fun _ _ => rfl

def leftRoute : tower.history.Interaction := ⟨.left, .closeLeft, rfl⟩
def rightRoute : tower.history.Interaction := ⟨.right, .closeRight, rfl⟩

/-- [definition] The diamond is a real higher cell: both routes start at the same boundary and
return the same complete target. -/
def interchangeCell : AddressedPassage.ComparisonCell
    tower.serialHolon.toPassage tower.serialHolon.toPassage where
  left := leftRoute
  right := rightRoute
  source_exact := rfl

/-- [proved-derived; formal-checked] Distinct first receiver faces do not obstruct a genuine
braided interchange. -/
theorem first_receiver_faces_distinct : receive .left ≠ receive .right := by
  decide

/-- [definition] A nontrivial admitted parallel interaction with distinct branch durations,
distinct first receiver faces, a commuting target, braided receiver preservation, and a concrete
capacity partition. -/
def receipt : Tower.ParallelInterchangeReceipt tower .left .right
    Unit Unit (fun _ => ()) (fun _ => ()) where
  interchangeCell := interchangeCell
  left_first := rfl
  right_first := rfl
  right_clock_preserved := rfl
  left_clock_preserved := rfl
  right_work_preserved := fun _ => rfl
  left_work_preserved := fun _ => rfl
  interchange_commutes := rfl
  receiver_braiding := rfl
  obstruction_interchange := rfl
  logicalResource_interchange := rfl
  leftCapacity := fun _ => 1
  rightCapacity := fun _ => 1
  capacity_partition := by
    intro resource
    cases resource
    decide
  left_capacity_carries := by
    intro resource
    cases resource
    decide
  right_capacity_carries := by
    intro resource
    cases resource
    decide

/-- [proved-derived; formal-checked] The parallel receiver reads the larger branch span. -/
theorem receipt_clockLength : receipt.clockLength = 3 := by
  decide

/-- [proved-derived; formal-checked] The explicit partition carries both branch workloads through
the parallel span. -/
theorem receipt_resource_bound :
    receipt.resourceWork () ≤ tower.resourceCapacity () * receipt.clockLength :=
  receipt.resourceWork_le_capacity_mul_clockLength ()

/-- [definition] Co-presence with the wrong continuations returns different complete targets. -/
def noncommutingCell : AddressedPassage.ComparisonCell
    tower.serialHolon.toPassage tower.serialHolon.toPassage where
  left := ⟨.left, .stay .leftMiddle, rfl⟩
  right := ⟨.right, .stay .rightMiddle, rfl⟩
  source_exact := rfl

/-- [counterexample; formal-checked] The identity target receiver exposes the failed higher cell. -/
theorem noncommutingTargetDefect :
    noncommutingCell.ReceiverDefect State id where
  separates := by decide

/-- [counterexample; formal-checked] Equal availability and co-presence cannot promote a cell
whose complete targets differ into an interchange. -/
theorem noncommutingCell_refuses_interchange : ¬ noncommutingCell.Commutes :=
  noncommutingCell.not_commutes_of_receiverDefect noncommutingTargetDefect

end ParallelControl

section Audit

#print axioms ClockRulerSpan.targetState_potential
#print axioms ClockRulerSpan.targetState_add
#print axioms ClockRulerSpan.targetState_injective
#print axioms ClockRulerSpan.reconstructionFibre_subsingleton
#print axioms ClockRulerSpan.denominator_mul_rulerCells_add_phase
#print axioms Tower.clockLength_serial
#print axioms Tower.rulerState_serial
#print axioms Tower.resourceWork_serial
#print axioms Tower.serialReconstructionFibreEquiv
#print axioms Tower.serialAssociator
#print axioms Tower.serialAssociatorFibreEquiv
#print axioms Tower.ParallelInterchangeReceipt.clockLength_eq_max
#print axioms Tower.ParallelInterchangeReceipt.reconstructionFibreEquiv
#print axioms Tower.ParallelInterchangeReceipt.resourceWork_le_capacity_mul_clockLength
#print axioms Tower.ParallelInterchangeReceipt.no_receipt_of_no_commuting_cell
#print axioms ScaleRebase.identity
#print axioms ScaleRebase.comp
#print axioms ScaleRebase.transportInteraction
#print axioms ScaleRebase.compReconstructionFibreEquiv
#print axioms ScaleRebase.transportPotential
#print axioms ScaleRebase.transportReceiverPotential
#print axioms FiniteControl.firstThenSecond_clockLength
#print axioms FiniteControl.equal_count_does_not_identify_extent
#print axioms FiniteControl.firstThenSecond_ruler
#print axioms FiniteControl.extendedPotential_components
#print axioms FiniteControl.stationaryParallel_clockLength
#print axioms FiniteControl.quotientOnly_collides_phaseSeparates
#print axioms ParallelControl.first_receiver_faces_distinct
#print axioms ParallelControl.receipt_clockLength
#print axioms ParallelControl.receipt_resource_bound
#print axioms ParallelControl.noncommutingCell_refuses_interchange

end Audit

end Soma.Holonics.Millennium.ReceiverIndexedCausalLengthTower
