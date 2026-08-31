import ElementaryHolonics.Millennium.HolonicClockedPantographicSwingApparatus
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic

/-!
# Exact causal-flux time for the Clocked Pantographic Swing

This file composes the existing algorithmic-event, receiver-current, apparatus, and rational-clock
owners.  The computation does not read an exterior timer in order to decide that time passed.
Instead, an apparatus realization supplies exact resource current per local oscillator crossing;
a feasible causal schedule returns an apparatus-local makespan; and a positive rational clock
passage transports that makespan into an observer chart while retaining quotient and phase.

The construction keeps three claims distinct.

* Resource demand divided by capacity is a necessary local-time bound.
* A feasible schedule is an attained local duration.
* The least feasible schedule is the intrinsic duration of the declared unfolding/apparatus pair.

An affine clock-rate passage is not silently identified with a Lorentz transformation.  The final
section gives an exact rational two-coordinate boost, proves interval preservation, and shows that
one-dimensional clock scaling is its restriction to a rest world-line.

All introduced carriers are `[definition]`.  Every theorem is
`[proved-derived; formal-checked]` unless its statement says otherwise.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicCausalFluxTime

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.HolonicClockedPantographicSwing
open Soma.Holonics.Millennium.HolonicClockedPantographicSwingApparatus

/-! ## Exact resource current before any exterior clock chart -/

/-- [definition] One addressed resource-current coordinate.  `capacityPerTick` is a constitutive
apparatus declaration in units of the named resource per crossing of the named local clock. -/
structure AddressedResourceCurrent (Resource Unit ClockAddress : Type*) where
  resource : Resource
  unit : Unit
  clockAddress : ClockAddress
  demand : ℕ
  demand_pos : 0 < demand
  capacityPerTick : ℕ
  capacity_pos : 0 < capacityPerTick
  characteristicLatency : ℕ
  latency_pos : 0 < characteristicLatency

namespace AddressedResourceCurrent

variable {Resource Unit ClockAddress : Type*}

/-- [definition] The least complete local crossing population able to carry the demand. -/
def serviceRounds
    (current : AddressedResourceCurrent Resource Unit ClockAddress) : ℕ :=
  current.demand ⌈/⌉ current.capacityPerTick

/-- [definition] Exact unused capacity retained behind the ceiling receiver. -/
def boundaryResidual
    (current : AddressedResourceCurrent Resource Unit ClockAddress) : ℕ :=
  current.capacityPerTick * current.serviceRounds - current.demand

/-- [definition] Receiver-current chronology: uncongested latency plus dilation by the complete
service-round population. -/
def localTicks
    (current : AddressedResourceCurrent Resource Unit ClockAddress) : ℕ :=
  current.characteristicLatency + current.serviceRounds - 1

/-- [proved-derived; formal-checked] The returned service-round population carries all demand. -/
theorem demand_le_capacity_mul_serviceRounds
    (current : AddressedResourceCurrent Resource Unit ClockAddress) :
    current.demand ≤ current.capacityPerTick * current.serviceRounds := by
  exact (ceilDiv_le_iff_le_mul current.capacity_pos).1 le_rfl

/-- [proved-derived; formal-checked] Demand and retained residual exactly reconstruct the complete
capacity presented by the service rounds. -/
theorem demand_add_boundaryResidual
    (current : AddressedResourceCurrent Resource Unit ClockAddress) :
    current.demand + current.boundaryResidual =
      current.capacityPerTick * current.serviceRounds := by
  exact Nat.add_sub_of_le current.demand_le_capacity_mul_serviceRounds

/-- [proved-derived; formal-checked] No smaller local crossing population can carry the demand. -/
theorem serviceRounds_le_of_demand_le
    (current : AddressedResourceCurrent Resource Unit ClockAddress)
    (candidate : ℕ)
    (carries : current.demand ≤ current.capacityPerTick * candidate) :
    current.serviceRounds ≤ candidate := by
  exact (ceilDiv_le_iff_le_mul current.capacity_pos).2 carries

/-- [proved-derived; formal-checked] Positive characteristic latency makes the local duration the
characteristic latency plus exactly the service dilation `rounds - 1`. -/
theorem localTicks_eq
    (current : AddressedResourceCurrent Resource Unit ClockAddress) :
    current.localTicks =
      current.characteristicLatency + (current.serviceRounds - 1) := by
  have rounds_pos : 0 < current.serviceRounds := by
    by_contra not_pos
    have rounds_zero : current.serviceRounds = 0 := Nat.eq_zero_of_not_pos not_pos
    have carried := current.demand_le_capacity_mul_serviceRounds
    rw [rounds_zero, Nat.mul_zero] at carried
    exact (Nat.ne_of_gt current.demand_pos) (Nat.eq_zero_of_le_zero carried)
  unfold localTicks
  exact Nat.add_sub_assoc (Nat.succ_le_iff.mpr rounds_pos) current.characteristicLatency

end AddressedResourceCurrent

/-! ## A complete feasible schedule of an algorithmic causal unfolding -/

/-- [definition] An addressed finite algorithmic unfolding.  Resource demands are coordinates of
each occurrence; `precedes` and `transportLatency` retain the causal edges that constrain starts. -/
structure AlgorithmicCausalUnfolding
    (Occurrence Resource ClockAddress : Type*) where
  clockAddress : ClockAddress
  precedes : Occurrence → Occurrence → Prop
  demand : Occurrence → Resource → ℕ
  intrinsicLatency : Occurrence → ℕ
  intrinsicLatency_pos : ∀ occurrence, 0 < intrinsicLatency occurrence
  transportLatency : Occurrence → Occurrence → ℕ

/-- [definition] An apparatus law gives every resource coordinate an exact unit and positive
capacity per crossing of the unfolding's local clock. -/
structure ApparatusServiceLaw
    (Resource Unit ClockAddress : Type*) where
  clockAddress : ClockAddress
  unit : Resource → Unit
  capacityPerTick : Resource → ℕ
  capacity_pos : ∀ resource, 0 < capacityPerTick resource

/-- [definition] A feasible schedule is the missing constitutive join from an algorithmic
unfolding to local time.  `service occurrence resource tick` is physical/computational current,
not a score.  Exact demand return, resource capacity, inactivity outside the event interval,
causal transport, and an attained completion frontier are all retained. -/
structure FeasibleCausalFluxSchedule
    {Occurrence Resource ClockAddress Unit : Type*}
    [Fintype Occurrence] [DecidableEq Occurrence]
    (unfolding : AlgorithmicCausalUnfolding Occurrence Resource ClockAddress)
    (law : ApparatusServiceLaw Resource Unit ClockAddress) where
  clock_exact : law.clockAddress = unfolding.clockAddress
  horizon : ℕ
  start : Occurrence → ℕ
  finish : Occurrence → ℕ
  service : Occurrence → Resource → ℕ → ℕ
  interval_pos : ∀ occurrence, start occurrence < finish occurrence
  latency_carried : ∀ occurrence,
    start occurrence + unfolding.intrinsicLatency occurrence ≤ finish occurrence
  finishes_within_horizon : ∀ occurrence, finish occurrence ≤ horizon
  horizon_attained : ∃ occurrence, finish occurrence = horizon
  causal : ∀ {before after}, unfolding.precedes before after →
    finish before + unfolding.transportLatency before after ≤ start after
  inactive : ∀ occurrence resource tick,
    tick < start occurrence ∨ finish occurrence ≤ tick →
      service occurrence resource tick = 0
  demand_exact : ∀ occurrence resource,
    (Finset.sum (Finset.range horizon)
      (fun tick => service occurrence resource tick)) =
      unfolding.demand occurrence resource
  capacity : ∀ resource tick, tick < horizon →
    (Finset.sum Finset.univ
      (fun occurrence => service occurrence resource tick)) ≤ law.capacityPerTick resource

/-- [definition] The apparatus-local time required by the declared unfolding is an attained
feasible schedule together with a proof that no feasible schedule has a smaller makespan. -/
structure ExactCausalFluxTime
    {Occurrence Resource ClockAddress Unit : Type*}
    [Fintype Occurrence] [DecidableEq Occurrence]
    (unfolding : AlgorithmicCausalUnfolding Occurrence Resource ClockAddress)
    (law : ApparatusServiceLaw Resource Unit ClockAddress) where
  attained : FeasibleCausalFluxSchedule unfolding law
  least : ∀ candidate : FeasibleCausalFluxSchedule unfolding law,
    attained.horizon ≤ candidate.horizon

namespace AlgorithmicCausalUnfolding

variable {Occurrence Resource ClockAddress : Type*}

/-- [definition] Exact demand crossing one resource coordinate over the whole unfolding. -/
def totalDemand [Fintype Occurrence]
    (unfolding : AlgorithmicCausalUnfolding Occurrence Resource ClockAddress)
    (resource : Resource) : ℕ :=
  ∑ occurrence, unfolding.demand occurrence resource

/-- [definition] Aggregate resource-current lower bound in local clock crossings. -/
def resourceLowerBound [Fintype Occurrence]
    {Unit : Type*}
    (unfolding : AlgorithmicCausalUnfolding Occurrence Resource ClockAddress)
    (law : ApparatusServiceLaw Resource Unit ClockAddress)
    (resource : Resource) : ℕ :=
  unfolding.totalDemand resource ⌈/⌉ law.capacityPerTick resource

end AlgorithmicCausalUnfolding

namespace FeasibleCausalFluxSchedule

variable {Occurrence Resource ClockAddress Unit : Type*}
variable [Fintype Occurrence] [DecidableEq Occurrence]
variable {unfolding : AlgorithmicCausalUnfolding Occurrence Resource ClockAddress}
variable {law : ApparatusServiceLaw Resource Unit ClockAddress}

/-- [proved-derived; formal-checked] The complete current delivered to one resource coordinate
cannot exceed its per-tick capacity times the attained horizon. -/
theorem totalDemand_le_capacity_mul_horizon
    (schedule : FeasibleCausalFluxSchedule unfolding law) (resource : Resource) :
    unfolding.totalDemand resource ≤ law.capacityPerTick resource * schedule.horizon := by
  calc
    unfolding.totalDemand resource =
        ∑ occurrence,
          Finset.sum (Finset.range schedule.horizon)
            (fun tick => schedule.service occurrence resource tick) := by
      unfold AlgorithmicCausalUnfolding.totalDemand
      apply Finset.sum_congr rfl
      intro occurrence _
      exact (schedule.demand_exact occurrence resource).symm
    _ = Finset.sum (Finset.range schedule.horizon)
          (fun tick => Finset.sum Finset.univ
            (fun occurrence => schedule.service occurrence resource tick)) := by
      exact Finset.sum_comm
    _ ≤ Finset.sum (Finset.range schedule.horizon)
          (fun _tick => law.capacityPerTick resource) := by
      apply Finset.sum_le_sum
      intro tick tick_mem
      exact schedule.capacity resource tick (Finset.mem_range.mp tick_mem)
    _ = law.capacityPerTick resource * schedule.horizon := by
      simp [Nat.mul_comm]

/-- [proved-derived; formal-checked] Every feasible schedule lies beyond the aggregate
resource-current ceiling bound. -/
theorem resourceLowerBound_le_horizon
    (schedule : FeasibleCausalFluxSchedule unfolding law) (resource : Resource) :
    unfolding.resourceLowerBound law resource ≤ schedule.horizon := by
  exact (ceilDiv_le_iff_le_mul (law.capacity_pos resource)).2
    (schedule.totalDemand_le_capacity_mul_horizon resource)

end FeasibleCausalFluxSchedule

/-! ### Causal-path transport is a separate local-time constraint -/

/-- [definition] An indexed causal path cannot forget either endpoint or any edge witness. -/
inductive CausalPath
    {Occurrence Resource ClockAddress : Type*}
    (unfolding : AlgorithmicCausalUnfolding Occurrence Resource ClockAddress) :
    Occurrence → Occurrence → Type _
  | stay (occurrence : Occurrence) : CausalPath unfolding occurrence occurrence
  | step {first next last : Occurrence} :
      unfolding.precedes first next →
      CausalPath unfolding next last →
      CausalPath unfolding first last

namespace CausalPath

variable {Occurrence Resource ClockAddress : Type*}
variable {unfolding : AlgorithmicCausalUnfolding Occurrence Resource ClockAddress}

/-- [definition] Intrinsic occurrence latencies and edge-transport latencies accumulated along an
addressed causal path. -/
def requiredTicks {first last : Occurrence} :
    CausalPath unfolding first last → ℕ
  | .stay occurrence => unfolding.intrinsicLatency occurrence
  | .step (first := first) (next := next) edge tail =>
      unfolding.intrinsicLatency first + unfolding.transportLatency first next +
        tail.requiredTicks

variable {Unit : Type*}
variable [Fintype Occurrence] [DecidableEq Occurrence]
variable {law : ApparatusServiceLaw Resource Unit ClockAddress}

/-- [proved-derived; formal-checked] Every path's caused local duration lies inside every feasible
schedule's interval from the path source to its target. -/
theorem start_add_requiredTicks_le_finish
    (schedule : FeasibleCausalFluxSchedule unfolding law)
    {first last : Occurrence} (path : CausalPath unfolding first last) :
    schedule.start first + path.requiredTicks ≤ schedule.finish last := by
  induction path with
  | stay occurrence =>
      exact schedule.latency_carried occurrence
  | @step first next last edge tail inductionHypothesis =>
      have first_service := schedule.latency_carried first
      have transported := schedule.causal edge
      simp only [requiredTicks]
      omega

/-- [proved-derived; formal-checked] Every addressed causal path is a lower bound on the complete
apparatus-local makespan. -/
theorem requiredTicks_le_horizon
    (schedule : FeasibleCausalFluxSchedule unfolding law)
    {first last : Occurrence} (path : CausalPath unfolding first last) :
    path.requiredTicks ≤ schedule.horizon := by
  have path_inside := path.start_add_requiredTicks_le_finish schedule
  have target_inside := schedule.finishes_within_horizon last
  omega

end CausalPath

/-! ## Ratio transport from local causal time to observer time -/

/-- [definition] Exact rational observer duration returned by a positive addressed clock passage.
The offset of an affine coordinate chart cancels on durations, so only the rate acts here. -/
def observerDuration
    {ClockAddress : Type*}
    (passage : RationalClockPassage ClockAddress) (localTicks : ℕ) : ℚ :=
  passage.rate * localTicks

/-- [proved-derived; formal-checked] Whole observer ticks plus the retained within-tick phase are
exactly the rational-rate image of the local crossing population. -/
theorem observerDuration_eq_targetTicks_add_phase
    {ClockAddress : Type*}
    (passage : RationalClockPassage ClockAddress) (localTicks : ℕ) :
    observerDuration passage localTicks =
      passage.targetTicks 0 localTicks +
        (passage.phaseResidue 0 localTicks : ℚ) / passage.denominator := by
  have denominator_ne_zero : (passage.denominator : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt passage.denominator_pos)
  have reconstruct :=
    passage.denominator_mul_targetTicks_add_phaseResidue 0 localTicks
  simp only [zero_add] at reconstruct
  unfold observerDuration RationalClockPassage.rate
  field_simp
  exact_mod_cast reconstruct.symm

/-- [proved-derived; formal-checked] A positive clock passage preserves every local duration
inequality. -/
theorem observerDuration_mono
    {ClockAddress : Type*}
    (passage : RationalClockPassage ClockAddress)
    {lower upper : ℕ} (ordered : lower ≤ upper) :
    observerDuration passage lower ≤ observerDuration passage upper := by
  unfold observerDuration
  gcongr
  unfold RationalClockPassage.rate
  exact le_of_lt (div_pos (by exact_mod_cast passage.numerator_pos)
    (by exact_mod_cast passage.denominator_pos))

/-- [definition] A positive affine clock chart between addressed one-dimensional clock faces. -/
structure PositiveAffineClockChart (ClockAddress : Type*) where
  source : ClockAddress
  target : ClockAddress
  offset : ℚ
  scale : ℚ
  scale_pos : 0 < scale

namespace PositiveAffineClockChart

variable {ClockAddress : Type*}

/-- [definition] Coordinate transport includes the conventional origin displacement. -/
def coordinate (chart : PositiveAffineClockChart ClockAddress) (sourceTime : ℚ) : ℚ :=
  chart.offset + chart.scale * sourceTime

/-- [definition] Duration transport is independent of the coordinate origin. -/
def duration (chart : PositiveAffineClockChart ClockAddress) (sourceDuration : ℚ) : ℚ :=
  chart.scale * sourceDuration

/-- [definition] Serial chart transport retains the affine semidirect-product law. -/
def comp (right left : PositiveAffineClockChart ClockAddress)
    (_joins : left.target = right.source) : PositiveAffineClockChart ClockAddress where
  source := left.source
  target := right.target
  offset := right.offset + right.scale * left.offset
  scale := right.scale * left.scale
  scale_pos := mul_pos right.scale_pos left.scale_pos

/-- [proved-derived; formal-checked] Serial affine clock transport composes exactly. -/
theorem coordinate_comp (right left : PositiveAffineClockChart ClockAddress)
    (joins : left.target = right.source) (sourceTime : ℚ) :
    (comp right left joins).coordinate sourceTime =
      right.coordinate (left.coordinate sourceTime) := by
  simp [coordinate, comp]
  ring

/-- [proved-derived; formal-checked] Origin offsets cancel when two coordinates are differenced. -/
theorem coordinate_sub_coordinate
    (chart : PositiveAffineClockChart ClockAddress) (finish start : ℚ) :
    chart.coordinate finish - chart.coordinate start = chart.duration (finish - start) := by
  simp [coordinate, duration]
  ring

/-- [definition] The affine duration chart presented by an exact rational crossing passage. -/
def ofPassage (passage : RationalClockPassage ClockAddress) :
    PositiveAffineClockChart ClockAddress where
  source := passage.source
  target := passage.target
  offset := 0
  scale := passage.rate
  scale_pos := by
    unfold RationalClockPassage.rate
    exact div_pos (by exact_mod_cast passage.numerator_pos)
      (by exact_mod_cast passage.denominator_pos)

/-- [proved-derived; formal-checked] The affine receiver of a rational passage returns the same
exact observer duration. -/
theorem ofPassage_duration
    (passage : RationalClockPassage ClockAddress) (localTicks : ℕ) :
    (ofPassage passage).duration localTicks = observerDuration passage localTicks := by
  rfl

end PositiveAffineClockChart

/-- [definition] Complete causal-flux-to-observer-time passage.  The local makespan is caused by
the unfolding/apparatus pair; the clock passage merely rebases its returned duration. -/
structure ClockedCausalFluxTranslation
    {Occurrence Resource ClockAddress Unit : Type*}
    [Fintype Occurrence] [DecidableEq Occurrence]
    (unfolding : AlgorithmicCausalUnfolding Occurrence Resource ClockAddress)
    (law : ApparatusServiceLaw Resource Unit ClockAddress) where
  localTime : ExactCausalFluxTime unfolding law
  clockPassage : RationalClockPassage ClockAddress
  clock_source_exact : clockPassage.source = unfolding.clockAddress

namespace ClockedCausalFluxTranslation

variable {Occurrence Resource ClockAddress Unit : Type*}
variable [Fintype Occurrence] [DecidableEq Occurrence]
variable {unfolding : AlgorithmicCausalUnfolding Occurrence Resource ClockAddress}
variable {law : ApparatusServiceLaw Resource Unit ClockAddress}

/-- [definition] The exact observer-coordinate duration of the least feasible local unfolding. -/
def duration (translation : ClockedCausalFluxTranslation unfolding law) : ℚ :=
  observerDuration translation.clockPassage translation.localTime.attained.horizon

/-- [proved-derived; formal-checked] The observer duration retains whole observer ticks and the
complete quotient--residue reconstruction fibre. -/
theorem duration_eq_targetTicks_add_phase
    (translation : ClockedCausalFluxTranslation unfolding law) :
    translation.duration =
      translation.clockPassage.targetTicks 0 translation.localTime.attained.horizon +
        (translation.clockPassage.phaseResidue 0 translation.localTime.attained.horizon : ℚ) /
          translation.clockPassage.denominator := by
  exact observerDuration_eq_targetTicks_add_phase _ _

end ClockedCausalFluxTranslation

/-! ## Exact bounded application to the 96-occurrence query-work body -/

/-- [definition] The three exact query-work classes returned by the bounded 96-occurrence body. -/
def primaryQueryWork : Fin 3 → ℕ
  | 0 => 1283
  | 1 => 1143
  | 2 => 99

/-- [proved-derived; formal-checked] Thirty-two occurrences of each returned work class carry
exactly 80,800 query-current units. -/
theorem primaryQueryWork_total :
    32 * (∑ kind, primaryQueryWork kind) = 80800 := by
  decide

/-- [definition] The explicit 24-worker attainable abstract duration: sixteen workers carry
`1283+1143+1143`, while eight carry `1283+1283+4*99`. -/
def primaryTwentyFourWorkerWitnessTicks : ℕ := 3569

/-- [proved-derived; formal-checked] The two worker-load classes conserve all 80,800 units. -/
theorem primaryTwentyFourWorkerWitness_conserves :
    16 * (1283 + 1143 + 1143) + 8 * (1283 + 1283 + 4 * 99) = 80800 := by
  norm_num

/-- [proved-derived; formal-checked] Every worker in the displayed load construction finishes by
local crossing 3,569. -/
theorem primaryTwentyFourWorkerWitness_loads :
    1283 + 1143 + 1143 = primaryTwentyFourWorkerWitnessTicks ∧
      1283 + 1283 + 4 * 99 ≤ primaryTwentyFourWorkerWitnessTicks := by
  norm_num [primaryTwentyFourWorkerWitnessTicks]

/-- [definition] One exact calibration witness from local query-current ticks to observer
nanoseconds.  It is deliberately a passage parameter, not a universal hardware law. -/
def primaryOneWorkerNanosecondPassage : RationalClockPassage String where
  source := "query-current"
  target := "observer-nanosecond"
  numerator := 31159853
  denominator := 40400
  numerator_pos := by decide
  denominator_pos := by decide

/-- [proved-derived; formal-checked] Applying the declared clock ratio translates the attainable
24-worker abstract duration into an exact rational observer duration. -/
theorem primaryTwentyFourWorker_observerDuration :
    observerDuration primaryOneWorkerNanosecondPassage
      primaryTwentyFourWorkerWitnessTicks =
        (3569 : ℚ) * 31159853 / 40400 := by
  norm_num [observerDuration, primaryOneWorkerNanosecondPassage,
    RationalClockPassage.rate, primaryTwentyFourWorkerWitnessTicks]

/-- [proved-derived; formal-checked] The same translation returns 2,752,710 complete observer
nanoseconds and the exact phase residue 31,357/40,400 of the next nanosecond. -/
theorem primaryTwentyFourWorker_observerPhase :
    primaryOneWorkerNanosecondPassage.targetTicks 0
        primaryTwentyFourWorkerWitnessTicks = 2752710 ∧
      primaryOneWorkerNanosecondPassage.phaseResidue 0
        primaryTwentyFourWorkerWitnessTicks = 31357 := by
  decide

/-! ## The precise Lorentz relation: a two-coordinate invariant, not a clock-rate metaphor -/

/-- [definition] A rationally parameterized 1+1 boost.  `parameterSq_lt_one` keeps the rational
chart away from its lightlike pole. -/
structure RationalLorentzBoost where
  parameter : ℚ
  parameterSq_lt_one : parameter ^ 2 < 1

namespace RationalLorentzBoost

/-- [definition] Rational Lorentz time coefficient. -/
def gamma (boost : RationalLorentzBoost) : ℚ :=
  (1 + boost.parameter ^ 2) / (1 - boost.parameter ^ 2)

/-- [definition] Rational Lorentz time--space mixing coefficient. -/
def mix (boost : RationalLorentzBoost) : ℚ :=
  (2 * boost.parameter) / (1 - boost.parameter ^ 2)

/-- [definition] Boosted time coordinate. -/
def time (boost : RationalLorentzBoost) (t x : ℚ) : ℚ :=
  boost.gamma * t - boost.mix * x

/-- [definition] Boosted space coordinate. -/
def space (boost : RationalLorentzBoost) (t x : ℚ) : ℚ :=
  boost.gamma * x - boost.mix * t

/-- [proved-derived; formal-checked] The exact rational boost preserves the 1+1 Minkowski
interval. -/
theorem preserves_interval (boost : RationalLorentzBoost) (t x : ℚ) :
    boost.time t x ^ 2 - boost.space t x ^ 2 = t ^ 2 - x ^ 2 := by
  have denominator_ne_zero : 1 - boost.parameter ^ 2 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr boost.parameterSq_lt_one)
  unfold time space gamma mix
  field_simp
  ring

/-- [proved-derived; formal-checked] On the rest world-line, the full boost restricts to positive
one-dimensional clock scaling; away from rest, the spatial cross-term remains. -/
theorem time_on_rest_worldline (boost : RationalLorentzBoost) (properTime : ℚ) :
    boost.time properTime 0 = boost.gamma * properTime := by
  simp [time]

end RationalLorentzBoost

section Audit

#print axioms AddressedResourceCurrent.demand_add_boundaryResidual
#print axioms AddressedResourceCurrent.serviceRounds_le_of_demand_le
#print axioms FeasibleCausalFluxSchedule.totalDemand_le_capacity_mul_horizon
#print axioms FeasibleCausalFluxSchedule.resourceLowerBound_le_horizon
#print axioms CausalPath.requiredTicks_le_horizon
#print axioms observerDuration_eq_targetTicks_add_phase
#print axioms observerDuration_mono
#print axioms PositiveAffineClockChart.coordinate_comp
#print axioms ClockedCausalFluxTranslation.duration_eq_targetTicks_add_phase
#print axioms primaryQueryWork_total
#print axioms primaryTwentyFourWorkerWitness_conserves
#print axioms primaryTwentyFourWorker_observerDuration
#print axioms primaryTwentyFourWorker_observerPhase
#print axioms RationalLorentzBoost.preserves_interval

end Audit

end Soma.Holonics.Millennium.HolonicCausalFluxTime
