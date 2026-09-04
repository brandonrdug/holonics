import ElementaryHolonics.Millennium.HolonicSensoryWorldTube
import ElementaryHolonics.Millennium.HolonicPantographicSwingJets
import ElementaryHolonics.Millennium.HolonicComposition
import Mathlib.Tactic

/-!
# The clocked pantographic Swing

This file composes existing owners into the exact mathematical carrier requested by the clock and
relativistic-measurement synthesis.

* A tick is an oriented crossing of a declared oscillator section, not an increment authored by a
  timer callback.
* A clock ratio is transported by integer quotient and remainder.  The remainder is retained as
  within-cycle phase, so no floating accumulator is required.
* One coarse Swing retains the complete fibre of inner interaction Swings and their individual
  clock passages.
* Proper time, causal order, physical/computational work, apparatus placement, and exterior seconds
  are different receiver faces.
* Worker count may bound a simultaneously admitted independent front, but it neither identifies
  the intrinsic Swing nor bounds total work or Turing-machine complexity.

All introduced carriers are `[definition]`.  Every theorem is
`[proved-derived; formal-checked]`, except the explicitly named finite controls, which are
`[counterexample; formal-checked]` relative to the displayed fixtures.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicClockedPantographicSwing

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.HolonicSensoryWorldTube

/-! ## A physical tick is an oriented oscillator-section crossing -/

/-- [definition] A local oscillator with an addressed source, exact state transition, phase face,
and oriented Boolean section.  Periodicity and a physical constitutive law remain obligations of a
realization rather than fields silently inferred from the word `oscillator`. -/
structure SectionedOscillator
    (ClockAddress OscillatorState Phase : Type*) where
  address : ClockAddress
  advance : OscillatorState → OscillatorState
  cycleCount : OscillatorState → ℤ
  phase : OscillatorState → Phase
  sectionMark : OscillatorState → Bool

namespace SectionedOscillator

variable {ClockAddress OscillatorState Phase : Type*}

/-- [definition] One positive-direction crossing of the declared oscillator section. -/
structure Crossing
    (oscillator : SectionedOscillator ClockAddress OscillatorState Phase) where
  source : OscillatorState
  target : OscillatorState
  advances : target = oscillator.advance source
  crossesOnce : oscillator.cycleCount target = oscillator.cycleCount source + 1
  leavesSection : oscillator.sectionMark source = false
  entersSection : oscillator.sectionMark target = true

/-- [definition] The crossing population as the standing occurrence-bearing holon. -/
def crossingHolon
    (oscillator : SectionedOscillator ClockAddress OscillatorState Phase) :
    Holon OscillatorState OscillatorState Phase where
  Occurrence := oscillator.Crossing
  source crossing := crossing.source
  target crossing := crossing.target
  receive crossing := oscillator.phase crossing.target

/-- [proved-derived; formal-checked] Every admitted tick advances through the oscillator's
declared physical transition. -/
theorem crossingHolon_target
    (oscillator : SectionedOscillator ClockAddress OscillatorState Phase)
    (crossing : oscillator.crossingHolon.Occurrence) :
    oscillator.crossingHolon.target crossing =
      oscillator.advance (oscillator.crossingHolon.source crossing) :=
  crossing.advances

/-- [proved-derived; formal-checked] One admitted oriented crossing advances the exact local cycle
population by one. -/
theorem crossing_cycleCount_succ
    (oscillator : SectionedOscillator ClockAddress OscillatorState Phase)
    (crossing : oscillator.Crossing) :
    oscillator.cycleCount crossing.target = oscillator.cycleCount crossing.source + 1 :=
  crossing.crossesOnce

end SectionedOscillator

/-- [definition] The complete local cycle face.  Equal counts or phases do not identify its clock
address or the occurrence which returned it. -/
structure CycleFace (ClockAddress Phase : Type*) where
  clockAddress : ClockAddress
  crossingCount : ℤ
  phase : Phase

/-! ## Exact rational clock gearing without floating point -/

/-- [definition] An addressed positive rational clock ratio.  `numerator / denominator` is the
target-crossing rate per source crossing; the two addresses and both positive witnesses are part of
the passage. -/
structure RationalClockPassage (ClockAddress : Type*) where
  source : ClockAddress
  target : ClockAddress
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator

namespace RationalClockPassage

variable {ClockAddress : Type*}

/-- [definition] Exact rational rate as a later coordinate receiver. -/
def rate (passage : RationalClockPassage ClockAddress) : ℚ :=
  (passage.numerator : ℚ) / (passage.denominator : ℚ)

/-- [definition] The complete numerator presented to the divider after `sourceTicks`. -/
def accumulated (passage : RationalClockPassage ClockAddress)
    (initialResidue sourceTicks : ℕ) : ℕ :=
  initialResidue + passage.numerator * sourceTicks

/-- [definition] Complete target crossings returned by exact Euclidean division. -/
def targetTicks (passage : RationalClockPassage ClockAddress)
    (initialResidue sourceTicks : ℕ) : ℕ :=
  passage.accumulated initialResidue sourceTicks / passage.denominator

/-- [definition] The retained within-target-cycle phase residue. -/
def phaseResidue (passage : RationalClockPassage ClockAddress)
    (initialResidue sourceTicks : ℕ) : ℕ :=
  passage.accumulated initialResidue sourceTicks % passage.denominator

/-- [proved-derived; formal-checked] Quotient plus retained phase reconstructs the complete scaled
source population exactly. -/
theorem denominator_mul_targetTicks_add_phaseResidue
    (passage : RationalClockPassage ClockAddress)
    (initialResidue sourceTicks : ℕ) :
    passage.denominator * passage.targetTicks initialResidue sourceTicks +
        passage.phaseResidue initialResidue sourceTicks =
      initialResidue + passage.numerator * sourceTicks := by
  rw [targetTicks, phaseResidue, accumulated]
  simpa [Nat.mul_comm] using
    (Nat.div_add_mod
      (initialResidue + passage.numerator * sourceTicks) passage.denominator)

/-- [proved-derived; formal-checked] The phase fibre is always strictly inside one target cycle. -/
theorem phaseResidue_lt_denominator
    (passage : RationalClockPassage ClockAddress)
    (initialResidue sourceTicks : ℕ) :
    passage.phaseResidue initialResidue sourceTicks < passage.denominator := by
  exact Nat.mod_lt _ passage.denominator_pos

/-- [definition] The identity gear at one addressed clock. -/
def identity (address : ClockAddress) : RationalClockPassage ClockAddress where
  source := address
  target := address
  numerator := 1
  denominator := 1
  numerator_pos := by decide
  denominator_pos := by decide

/-- [proved-derived; formal-checked] The identity gear preserves every complete crossing count and
returns zero phase when it begins on the section. -/
theorem identity_targetTicks (address : ClockAddress) (sourceTicks : ℕ) :
    (identity address).targetTicks 0 sourceTicks = sourceTicks := by
  simp [identity, targetTicks, accumulated]

theorem identity_phaseResidue (address : ClockAddress) (sourceTicks : ℕ) :
    (identity address).phaseResidue 0 sourceTicks = 0 := by
  simp only [phaseResidue, accumulated, identity, zero_add, one_mul, Nat.mod_one]

/-- [definition] A quotient--residue clock state.  Completed target crossings and the bounded
within-cycle residue are stored separately, while `potential` reconstructs their exact common
integer carrier. -/
@[ext] structure PhaseState (passage : RationalClockPassage ClockAddress) where
  completedTicks : ℕ
  residue : Fin passage.denominator

/-- [definition] The exact uncollapsed integer potential represented by a phase state. -/
def PhaseState.potential {passage : RationalClockPassage ClockAddress}
    (state : PhaseState passage) : ℕ :=
  passage.denominator * state.completedTicks + state.residue

/-- [definition] Canonical quotient--residue compression of one exact integer potential. -/
def normalize (passage : RationalClockPassage ClockAddress) (potential : ℕ) :
    PhaseState passage where
  completedTicks := potential / passage.denominator
  residue := ⟨potential % passage.denominator, Nat.mod_lt _ passage.denominator_pos⟩

/-- [proved-derived; formal-checked] The canonical phase state reconstructs the exact potential it
compressed. -/
theorem potential_normalize (passage : RationalClockPassage ClockAddress) (potential : ℕ) :
    (normalize passage potential).potential = potential := by
  simpa [PhaseState.potential, normalize, Nat.mul_comm] using
    (Nat.div_add_mod potential passage.denominator)

/-- [proved-derived; formal-checked] Recompressing an already normalized quotient--residue state
does not change it. -/
theorem normalize_potential (passage : RationalClockPassage ClockAddress)
    (state : PhaseState passage) :
    normalize passage state.potential = state := by
  apply PhaseState.ext
  · simp only [normalize, PhaseState.potential]
    rw [Nat.add_comm, Nat.add_mul_div_left, Nat.div_eq_of_lt state.residue.isLt,
      Nat.zero_add]
    exact passage.denominator_pos
  · apply Fin.ext
    simp [normalize, PhaseState.potential, Nat.add_mod,
      Nat.mod_eq_of_lt state.residue.isLt]

/-- [proved-derived; formal-checked] The complete integer potential separates normalized clock
states, so quotient--residue compression retains an exact reconstruction fibre. -/
theorem phasePotential_injective (passage : RationalClockPassage ClockAddress) :
    Function.Injective (PhaseState.potential (passage := passage)) := by
  intro left right equalPotential
  rw [← normalize_potential passage left, ← normalize_potential passage right, equalPotential]

/-- [definition] Advance a clock state by an exact population of source crossings. -/
def advanceBy (passage : RationalClockPassage ClockAddress)
    (state : PhaseState passage) (sourceTicks : ℕ) : PhaseState passage :=
  normalize passage (state.potential + passage.numerator * sourceTicks)

/-- [proved-derived; formal-checked] Clock advancement conserves the complete integer potential. -/
theorem potential_advanceBy (passage : RationalClockPassage ClockAddress)
    (state : PhaseState passage) (sourceTicks : ℕ) :
    (advanceBy passage state sourceTicks).potential =
      state.potential + passage.numerator * sourceTicks := by
  exact potential_normalize _ _

/-- [proved-derived; formal-checked] Zero source crossings leave a normalized clock state fixed. -/
theorem advanceBy_zero (passage : RationalClockPassage ClockAddress)
    (state : PhaseState passage) :
    advanceBy passage state 0 = state := by
  simpa [advanceBy] using normalize_potential passage state

/-- [proved-derived; formal-checked] Chunking or parallel batching cannot change the exact clock
state: advancing by two populations serially equals advancing once by their sum. -/
theorem advanceBy_add (passage : RationalClockPassage ClockAddress)
    (state : PhaseState passage) (first second : ℕ) :
    advanceBy passage (advanceBy passage state first) second =
      advanceBy passage state (first + second) := by
  unfold advanceBy
  rw [potential_normalize]
  congr 1
  simp only [Nat.mul_add, add_assoc]

/-- [definition] A serial clock composite retains both passages and their exact joining-address
equality.  Its projection to one ratio is a receiver of this lineage-bearing object. -/
structure Composite where
  left : RationalClockPassage ClockAddress
  right : RationalClockPassage ClockAddress
  joins : left.target = right.source

/-- [definition] The exterior ratio of a retained serial clock composite. -/
def Composite.passage (composite : Composite (ClockAddress := ClockAddress)) :
    RationalClockPassage ClockAddress where
  source := composite.left.source
  target := composite.right.target
  numerator := composite.right.numerator * composite.left.numerator
  denominator := composite.right.denominator * composite.left.denominator
  numerator_pos := Nat.mul_pos composite.right.numerator_pos composite.left.numerator_pos
  denominator_pos := Nat.mul_pos composite.right.denominator_pos composite.left.denominator_pos

/-- [proved-derived; formal-checked] Serial clock passages multiply their exact rational rates. -/
theorem rate_comp (composite : Composite (ClockAddress := ClockAddress)) :
    composite.passage.rate = composite.right.rate * composite.left.rate := by
  have hld : (composite.left.denominator : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt composite.left.denominator_pos)
  have hrd : (composite.right.denominator : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt composite.right.denominator_pos)
  simp only [rate, Composite.passage, Nat.cast_mul]
  field_simp

end RationalClockPassage

/-! ## Proper-time edges and the pantographic interaction fibre -/

universe uOuter uClockAddress uInteractionOccurrence uScalar uCarrier

/-- [definition] An exact proper-time evaluator together with its invariance under a declared
group of admissible frame rebases.  A physical realization still owes that its `Frame` action is
the relevant Lorentz/frame action and that its witness is supplied by the metric/connection. -/
structure RelativisticProperTimeLaw
    (Frame Event Witness : Type*) [Group Frame]
    [MulAction Frame Event] [MulAction Frame Witness] where
  squaredInterval : Witness → Event → Event → ℚ
  invariant : ∀ (frame : Frame) (witness : Witness) (source target : Event),
    squaredInterval (frame • witness) (frame • source) (frame • target) =
      squaredInterval witness source target

/-- [definition] One exact timelike edge measured by a declared proper-time law. -/
structure DiscreteProperTimeEdge
    {Frame Event Witness : Type*} [Group Frame]
    [MulAction Frame Event] [MulAction Frame Witness]
    (law : RelativisticProperTimeLaw Frame Event Witness) where
  source : Event
  target : Event
  witness : Witness
  squaredProperTime : ℚ
  measured : squaredProperTime = law.squaredInterval witness source target
  timelike : 0 < squaredProperTime

namespace DiscreteProperTimeEdge

variable {Frame Event Witness : Type*} [Group Frame]
variable [MulAction Frame Event] [MulAction Frame Witness]
variable {law : RelativisticProperTimeLaw Frame Event Witness}

/-- [definition] Rebase a proper-time edge through one admitted frame action. -/
def rebase (frame : Frame) (edge : DiscreteProperTimeEdge law) :
    DiscreteProperTimeEdge law where
  source := frame • edge.source
  target := frame • edge.target
  witness := frame • edge.witness
  squaredProperTime := edge.squaredProperTime
  measured := by
    rw [law.invariant]
    exact edge.measured
  timelike := edge.timelike

/-- [proved-derived; formal-checked] Proper time is unchanged by every admitted frame rebase. -/
theorem squaredProperTime_rebase (frame : Frame) (edge : DiscreteProperTimeEdge law) :
    (edge.rebase frame).squaredProperTime = edge.squaredProperTime := rfl

end DiscreteProperTimeEdge

/-- [definition] One actual affine pantographic motion.  The output law retains its anchor and
scale; naming an arbitrary interaction graph a pantograph is not sufficient. -/
structure PantographicLink (Scalar Carrier : Type*)
    [CommRing Scalar] [AddCommGroup Carrier] [Module Scalar Carrier] where
  anchor : Carrier
  scale : Scalar
  input : Carrier
  output : Carrier
  output_exact : output =
    HolonicPantographicSwingJets.pantographicPoint anchor scale input

namespace PantographicLink

variable {Scalar Carrier : Type*}
variable [CommRing Scalar] [AddCommGroup Carrier] [Module Scalar Carrier]

/-- [proved-derived; formal-checked] A retained pantographic link returns its scaled displacement
about the declared anchor. -/
theorem output_sub_anchor (link : PantographicLink Scalar Carrier) :
    link.output - link.anchor = link.scale • (link.input - link.anchor) := by
  rw [link.output_exact]
  exact HolonicPantographicSwingJets.pantographicPoint_sub_anchor _ _ _

/-- [definition] A serial pair retains both link occurrences, the common-anchor witness, and the
joining equality. -/
structure Composite where
  left : PantographicLink Scalar Carrier
  right : PantographicLink Scalar Carrier
  anchor_exact : right.anchor = left.anchor
  joins : left.output = right.input

/-- [definition] The coarse pantographic receiver of a complete serial pair. -/
def Composite.link (composite : Composite (Scalar := Scalar) (Carrier := Carrier)) :
    PantographicLink Scalar Carrier where
  anchor := composite.left.anchor
  scale := composite.right.scale * composite.left.scale
  input := composite.left.input
  output := composite.right.output
  output_exact := by
    calc
      composite.right.output =
          HolonicPantographicSwingJets.pantographicPoint composite.right.anchor
            composite.right.scale composite.right.input := composite.right.output_exact
      _ = HolonicPantographicSwingJets.pantographicPoint composite.left.anchor
            composite.right.scale composite.left.output := by
          rw [composite.anchor_exact, composite.joins]
      _ = HolonicPantographicSwingJets.pantographicPoint composite.left.anchor
            composite.right.scale
            (HolonicPantographicSwingJets.pantographicPoint composite.left.anchor
              composite.left.scale composite.left.input) := by
          rw [composite.left.output_exact]
      _ = HolonicPantographicSwingJets.pantographicPoint composite.left.anchor
            (composite.right.scale * composite.left.scale) composite.left.input :=
          HolonicPantographicSwingJets.pantographicPoint_comp _ _ _ _

end PantographicLink

/-! ### The finite-pole constraint chart is a distinct projective pantograph face -/

section ProjectivePantograph

variable {Coordinate : Type*} [Field Coordinate]

/-- [definition] The generalized pantographic output in a finite-pole constraint chart.  The
parameters are input `a`, fixed point `b`, finite pole `d`, and scale `λ`.  Its affine
board-at-infinity face is the separate existing `pantographicPoint`; no limit is silently taken. -/
def projectivePantographicPoint
    (fixed pole scale input : Coordinate) : Coordinate :=
  (fixed * (input - pole) - scale * pole * (input - fixed)) /
    ((input - pole) - scale * (input - fixed))

/-- [definition] One projective pantographic occurrence retains the nonvanishing chart denominator
which makes its displayed coordinate lawful. -/
structure ProjectivePantographicLink (Coordinate : Type*) [Field Coordinate] where
  fixed : Coordinate
  pole : Coordinate
  scale : Coordinate
  input : Coordinate
  denominator_ne_zero : (input - pole) - scale * (input - fixed) ≠ 0
  output : Coordinate
  output_exact : output = projectivePantographicPoint fixed pole scale input

/-- [proved-derived; formal-checked] Scale one is the identity projective pantograph away from the
collapsed chart `fixed = pole`. -/
theorem projectivePantographicPoint_one
    (fixed pole input : Coordinate) (separated : fixed ≠ pole) :
    projectivePantographicPoint fixed pole 1 input = input := by
  unfold projectivePantographicPoint
  have denominator : (input - pole) - (input - fixed) ≠ 0 := by
    intro zero
    apply separated
    apply sub_eq_zero.mp
    linear_combination zero
  field_simp
  ring

end ProjectivePantograph

/-- [definition] The complete inner pantograph network behind coarse outer Swings.  Every inner
occurrence maps to its containing outer occurrence, carries an actual pantographic link, and owns
an exact stateful clock passage. -/
structure PantographicInteractionNetwork
    (OuterOccurrence : Type uOuter) (ClockAddress : Type uClockAddress)
    (InteractionOccurrence : Type uInteractionOccurrence)
    (Scalar : Type uScalar) (Carrier : Type uCarrier)
    [CommRing Scalar] [AddCommGroup Carrier] [Module Scalar Carrier] where
  outerOccurrence : InteractionOccurrence → OuterOccurrence
  link : InteractionOccurrence → PantographicLink Scalar Carrier
  clockPassage : InteractionOccurrence → RationalClockPassage ClockAddress
  clockState : ∀ occurrence, RationalClockPassage.PhaseState (clockPassage occurrence)
  sourceTicks : InteractionOccurrence → ℕ

namespace PantographicInteractionNetwork

variable {OuterOccurrence ClockAddress InteractionOccurrence Scalar Carrier : Type*}
variable [CommRing Scalar] [AddCommGroup Carrier] [Module Scalar Carrier]

/-- [definition] Every constituent interaction retained behind one coarse Swing occurrence. -/
def InteractionFibre
    (network : PantographicInteractionNetwork
      OuterOccurrence ClockAddress InteractionOccurrence Scalar Carrier)
    (outer : OuterOccurrence) : Type _ :=
  { occurrence : InteractionOccurrence //
    network.outerOccurrence occurrence = outer }

/-- [definition] The exact phase state after one constituent interaction. -/
def targetClockState
    (network : PantographicInteractionNetwork
      OuterOccurrence ClockAddress InteractionOccurrence Scalar Carrier)
    (occurrence : InteractionOccurrence) :
    RationalClockPassage.PhaseState (network.clockPassage occurrence) :=
  RationalClockPassage.advanceBy (network.clockPassage occurrence)
    (network.clockState occurrence) (network.sourceTicks occurrence)

/-- [definition] The network itself is an occurrence-bearing pantographic holon. -/
def toHolon
    (network : PantographicInteractionNetwork
      OuterOccurrence ClockAddress InteractionOccurrence Scalar Carrier) :
    Holon Carrier Carrier Scalar where
  Occurrence := InteractionOccurrence
  source occurrence := (network.link occurrence).input
  target occurrence := (network.link occurrence).output
  receive occurrence := (network.link occurrence).scale

/-- [proved-derived; formal-checked] Every inner pantographic interaction reconstructs its complete
scaled crossing population from the returned target count and phase residue. -/
theorem reconstruct_scaled_ticks
    (network : PantographicInteractionNetwork
      OuterOccurrence ClockAddress InteractionOccurrence Scalar Carrier)
    (occurrence : InteractionOccurrence) :
    (network.targetClockState occurrence).potential =
      (network.clockState occurrence).potential +
        (network.clockPassage occurrence).numerator * network.sourceTicks occurrence := by
  exact RationalClockPassage.potential_advanceBy _ _ _

/-- [proved-derived; formal-checked] Every network occurrence satisfies the affine pantograph law. -/
theorem target_pantographic
    (network : PantographicInteractionNetwork
      OuterOccurrence ClockAddress InteractionOccurrence Scalar Carrier)
    (occurrence : InteractionOccurrence) :
    network.toHolon.target occurrence =
      HolonicPantographicSwingJets.pantographicPoint
        (network.link occurrence).anchor (network.link occurrence).scale
        (network.toHolon.source occurrence) :=
  (network.link occurrence).output_exact

end PantographicInteractionNetwork

/-! ## The composed Clocked Pantographic Swing -/

universe uBodyState uOscillatorState uClock uPhase uFace uObstruction uOccurrence
  uInnerOccurrence uFrame uWitness uResource

/-- [definition] One coarse motion with a physical oscillator crossing, addressed span, discrete
proper-time edge, complete pantographic subinteraction fibre, and local energy/work balance. -/
structure ClockedPantographicSwing
    (Scalar : Type uScalar) (BodyState : Type uBodyState)
    (OscillatorState : Type uOscillatorState)
    (ClockAddress : Type uClock) (Phase : Type uPhase)
    (Face : Type uFace) (Obstruction : Type uObstruction)
    (Occurrence : Type uOccurrence) (InteractionOccurrence : Type uInnerOccurrence)
    (Frame : Type uFrame) (ProperTimeWitness : Type uWitness)
    (Resource : Type uResource)
    [CommRing Scalar] [AddCommGroup BodyState] [Module Scalar BodyState]
    [Group Frame] [MulAction Frame BodyState] [MulAction Frame ProperTimeWitness]
    [AddCommGroup Resource] where
  oscillator : SectionedOscillator ClockAddress OscillatorState Phase
  outer : ClockedSpan BodyState BodyState (CycleFace ClockAddress Phase)
    Face Obstruction Occurrence
  crossing : Occurrence → oscillator.Crossing
  clockAddress_exact : ∀ occurrence,
    (outer.clock occurrence).clockAddress = oscillator.address
  crossingCount_exact : ∀ occurrence,
    (outer.clock occurrence).crossingCount =
      oscillator.cycleCount (crossing occurrence).target
  phase_exact : ∀ occurrence,
    (outer.clock occurrence).phase = oscillator.phase (crossing occurrence).target
  pantograph : Occurrence → PantographicLink Scalar BodyState
  pantograph_source : ∀ occurrence,
    (pantograph occurrence).input = outer.source occurrence
  pantograph_target : ∀ occurrence,
    (pantograph occurrence).output = outer.target occurrence
  properTimeLaw : RelativisticProperTimeLaw Frame BodyState ProperTimeWitness
  properTime : Occurrence → DiscreteProperTimeEdge properTimeLaw
  properTime_source : ∀ occurrence, (properTime occurrence).source = outer.source occurrence
  properTime_target : ∀ occurrence, (properTime occurrence).target = outer.target occurrence
  network : PantographicInteractionNetwork Occurrence ClockAddress InteractionOccurrence
    Scalar BodyState
  storedBefore : Occurrence → Resource
  storedAfter : Occurrence → Resource
  boundaryFlux : Occurrence → Resource
  sourceWork : Occurrence → Resource
  dissipation : Occurrence → Resource
  localBalance : ∀ occurrence,
    storedAfter occurrence - storedBefore occurrence + boundaryFlux occurrence =
      sourceWork occurrence - dissipation occurrence

namespace ClockedPantographicSwing

variable
    {Scalar BodyState OscillatorState ClockAddress Phase Face Obstruction Occurrence
      InteractionOccurrence Frame ProperTimeWitness Resource : Type*}
    [CommRing Scalar] [AddCommGroup BodyState] [Module Scalar BodyState]
    [Group Frame] [MulAction Frame BodyState] [MulAction Frame ProperTimeWitness]
    [AddCommGroup Resource]

/-- [definition] The complete coarse receiver face retains clock, returned face, and obstruction. -/
def toHolon
    (swing : ClockedPantographicSwing Scalar BodyState OscillatorState ClockAddress Phase
      Face Obstruction Occurrence InteractionOccurrence Frame ProperTimeWitness Resource) :
    Holon BodyState BodyState (CycleFace ClockAddress Phase × Face × Obstruction) where
  Occurrence := Occurrence
  source := swing.outer.source
  target := swing.outer.target
  receive occurrence := swing.outer.completeFace occurrence

/-- [proved-derived; formal-checked] The clock is an actual oscillator transition, kept distinct
from the body motion it measures. -/
theorem clockCrossing_advances
    (swing : ClockedPantographicSwing Scalar BodyState OscillatorState ClockAddress Phase
      Face Obstruction Occurrence InteractionOccurrence Frame ProperTimeWitness Resource)
    (occurrence : Occurrence) :
    (swing.crossing occurrence).target =
      swing.oscillator.advance (swing.crossing occurrence).source :=
  (swing.crossing occurrence).advances

/-- [proved-derived; formal-checked] The measured body performs the retained affine pantographic
motion; it is not identified with the oscillator hardware state. -/
theorem bodyTarget_pantographic
    (swing : ClockedPantographicSwing Scalar BodyState OscillatorState ClockAddress Phase
      Face Obstruction Occurrence InteractionOccurrence Frame ProperTimeWitness Resource)
    (occurrence : Occurrence) :
    swing.outer.target occurrence =
      HolonicPantographicSwingJets.pantographicPoint
        (swing.pantograph occurrence).anchor (swing.pantograph occurrence).scale
        (swing.outer.source occurrence) := by
  rw [← swing.pantograph_target occurrence, (swing.pantograph occurrence).output_exact,
    swing.pantograph_source occurrence]

/-- [proved-derived; formal-checked] The displayed count is coupled to the oscillator crossing. -/
theorem crossingCount_eq_oscillator
    (swing : ClockedPantographicSwing Scalar BodyState OscillatorState ClockAddress Phase
      Face Obstruction Occurrence InteractionOccurrence Frame ProperTimeWitness Resource)
    (occurrence : Occurrence) :
    (swing.outer.clock occurrence).crossingCount =
      swing.oscillator.cycleCount (swing.crossing occurrence).target :=
  swing.crossingCount_exact occurrence

/-- [proved-derived; formal-checked] The displayed cycle count is one greater than the source
count of the physical crossing which produced it. -/
theorem crossingCount_eq_source_add_one
    (swing : ClockedPantographicSwing Scalar BodyState OscillatorState ClockAddress Phase
      Face Obstruction Occurrence InteractionOccurrence Frame ProperTimeWitness Resource)
    (occurrence : Occurrence) :
    (swing.outer.clock occurrence).crossingCount =
      swing.oscillator.cycleCount (swing.crossing occurrence).source + 1 := by
  rw [swing.crossingCount_exact occurrence, (swing.crossing occurrence).crossesOnce]

/-- [proved-derived; formal-checked] The complete resource return is the declared local balance;
parallel placement may not replace it by elapsed seconds or worker count. -/
theorem resource_balance
    (swing : ClockedPantographicSwing Scalar BodyState OscillatorState ClockAddress Phase
      Face Obstruction Occurrence InteractionOccurrence Frame ProperTimeWitness Resource)
    (occurrence : Occurrence) :
    swing.storedAfter occurrence - swing.storedBefore occurrence + swing.boundaryFlux occurrence =
      swing.sourceWork occurrence - swing.dissipation occurrence :=
  swing.localBalance occurrence

end ClockedPantographicSwing

/-! ## Clock holonomy reuses the retained addressed-route owner -/

/-- [definition] A clock-route comparison is exactly the existing addressed connection
comparison.  Both route occurrences and both connection transports remain present. -/
abbrev ClockRouteComparison (Fibre Source Target : Type*)
    (left right : AddressedPassage Source Target) :=
  HolonicComposition.AddressedConnectionComparison Fibre left right

/-- [definition] Clock holonomy is the existing returned curvature of the two retained routes. -/
def ClockRouteComparison.returnedHolonomy
    {Fibre Source Target : Type*} {left right : AddressedPassage Source Target}
    (comparison : ClockRouteComparison Fibre Source Target left right) : Equiv.Perm Fibre :=
  comparison.returnedCurvature

/-- [proved-derived; formal-checked] The clock holonomy is trivial exactly when the two complete
route transports agree. -/
theorem ClockRouteComparison.returnedHolonomy_eq_one_iff
    {Fibre Source Target : Type*} {left right : AddressedPassage Source Target}
    (comparison : ClockRouteComparison Fibre Source Target left right) :
    comparison.returnedHolonomy = 1 ↔
      comparison.rightTransport = comparison.leftTransport :=
  comparison.returnedCurvature_eq_one_iff

section Audit

#print axioms SectionedOscillator.crossingHolon_target
#print axioms SectionedOscillator.crossing_cycleCount_succ
#print axioms RationalClockPassage.denominator_mul_targetTicks_add_phaseResidue
#print axioms RationalClockPassage.phaseResidue_lt_denominator
#print axioms RationalClockPassage.identity_targetTicks
#print axioms RationalClockPassage.identity_phaseResidue
#print axioms RationalClockPassage.potential_normalize
#print axioms RationalClockPassage.normalize_potential
#print axioms RationalClockPassage.phasePotential_injective
#print axioms RationalClockPassage.potential_advanceBy
#print axioms RationalClockPassage.advanceBy_zero
#print axioms RationalClockPassage.advanceBy_add
#print axioms RationalClockPassage.rate_comp
#print axioms PantographicLink.output_sub_anchor
#print axioms projectivePantographicPoint_one
#print axioms DiscreteProperTimeEdge.squaredProperTime_rebase
#print axioms PantographicInteractionNetwork.reconstruct_scaled_ticks
#print axioms PantographicInteractionNetwork.target_pantographic
#print axioms ClockedPantographicSwing.clockCrossing_advances
#print axioms ClockedPantographicSwing.bodyTarget_pantographic
#print axioms ClockedPantographicSwing.crossingCount_eq_oscillator
#print axioms ClockedPantographicSwing.crossingCount_eq_source_add_one
#print axioms ClockedPantographicSwing.resource_balance
#print axioms ClockRouteComparison.returnedHolonomy_eq_one_iff

end Audit

end Soma.Holonics.Millennium.HolonicClockedPantographicSwing
