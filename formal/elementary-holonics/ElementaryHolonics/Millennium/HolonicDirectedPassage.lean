import ElementaryHolonics.Millennium.HolonicDifferenceCalculus
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Directed holonic passage: local current, defect, loop return, and reconstruction

An addressed current need not initially be an endpoint difference.  Its failure to compose across
one intermediate occurrence is retained as a `compositionDefect`.  Along every finite addressed
path, the sum of local currents is exactly the exterior current plus the sum of those defects.
Consequently a closed-path return is precisely the accumulated defect ledger.  State-induced
currents form the exact subfamily in which every defect vanishes.

The index type is arbitrary.  Time approaching a terminal face, lattice refinement, increasing
height, expanding contours, prime-local passages, and chart refinement enter through their own
filters.  `HasNullCurrentAlong course state` says that the receiver-valued state is Cauchy along
the declared course.  In a complete separated receiver this reconstructs one unique returned
value.  Reindexing, pairing receivers, and uniformly continuous receiver changes preserve the
law.

Truth status: introduced carriers are `[definition]`; every theorem below is
`[proved-derived; formal-checked]`, relative to Mathlib's additive, filter, and
complete-uniform-space laws.  No source-specific constitutive current is asserted to satisfy the
null-current hypothesis here.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Soma.Holonics.Millennium.HolonicDirectedPassage

/-! ## Addressed currents and the exact defect ledger -/

variable {Index G : Type*} [AddCommGroup G]

/-- [definition] A local current between addressed occurrences, normalized on a stationary
occurrence.  It may retain route dependence and therefore need not yet be an endpoint difference.
-/
structure AddressedCurrent (Index G : Type*) [AddCommGroup G] where
  current : Index → Index → G
  self_current : ∀ occurrence, current occurrence occurrence = 0

namespace AddressedCurrent

/-- Two addressed-current ledgers are equal when all addressed local currents are equal. -/
@[ext] theorem ext {left right : AddressedCurrent Index G}
    (h : left.current = right.current) : left = right := by
  cases left
  cases right
  cases h
  rfl

/-- [definition] The current induced by a receiver-valued state. -/
def fromState (state : Index → G) : AddressedCurrent Index G where
  current source target := state target - state source
  self_current occurrence := sub_self (state occurrence)

@[simp] theorem fromState_current (state : Index → G) (source target : Index) :
    (fromState state).current source target = state target - state source := rfl

/-- [definition] The returned remainder when two local currents are fused through one chart
boundary. -/
def compositionDefect (ledger : AddressedCurrent Index G) (source middle target : Index) : G :=
  ledger.current source middle + ledger.current middle target - ledger.current source target

/-- [proved-derived; formal-checked] A state-induced current has no composition defect. -/
@[simp] theorem fromState_compositionDefect
    (state : Index → G) (source middle target : Index) :
    (fromState state).compositionDefect source middle target = 0 := by
  simp [compositionDefect]

/-- [definition] The complete local-current population along a finite addressed path. -/
def pathCurrent (ledger : AddressedCurrent Index G) (address : ℕ → Index) (pieces : ℕ) : G :=
  ∑ piece ∈ Finset.range pieces,
    ledger.current (address piece) (address (piece + 1))

/-- [definition] Every fusion remainder along the same finite path, retained at its address. -/
def pathDefect (ledger : AddressedCurrent Index G) (address : ℕ → Index) (pieces : ℕ) : G :=
  ∑ piece ∈ Finset.range pieces,
    ledger.compositionDefect (address 0) (address piece) (address (piece + 1))

/-- [proved-derived; formal-checked] **THE DIRECTED LOCAL-TO-GLOBAL LEDGER.**  The complete sum
of local currents is the exterior current plus exactly the accumulated chart-composition defects.
No defect is discarded and no limiting argument is involved. -/
theorem finitePathCurrent_eq_exterior_add_defects
    (ledger : AddressedCurrent Index G) (address : ℕ → Index) (pieces : ℕ) :
    ledger.pathCurrent address pieces =
      ledger.current (address 0) (address pieces) + ledger.pathDefect address pieces := by
  induction pieces with
  | zero => simp [pathCurrent, pathDefect, ledger.self_current]
  | succ pieces ih =>
      simp only [pathCurrent, pathDefect, Finset.sum_range_succ] at ih ⊢
      rw [ih]
      simp [compositionDefect]
      abel

/-- [proved-derived; formal-checked] On a closed addressed path, the holonomy/loop return is
exactly the accumulated composition-defect population. -/
theorem closedPathCurrent_eq_defects
    (ledger : AddressedCurrent Index G) (address : ℕ → Index) (pieces : ℕ)
    (closed : address pieces = address 0) :
    ledger.pathCurrent address pieces = ledger.pathDefect address pieces := by
  rw [ledger.finitePathCurrent_eq_exterior_add_defects, closed, ledger.self_current, zero_add]

/-- [definition] Exact composition means that every three-face gluing returns zero remainder. -/
def ComposesExactly (ledger : AddressedCurrent Index G) : Prop :=
  ∀ source middle target, ledger.compositionDefect source middle target = 0

/-- [proved-derived; formal-checked] State-induced currents compose exactly. -/
theorem fromState_composesExactly (state : Index → G) :
    (fromState state).ComposesExactly := by
  intro source middle target
  exact fromState_compositionDefect state source middle target

/-! ## Receiver transport of the complete ledger -/

/-- [definition] An additive receiver transports every addressed local current. -/
def map {H : Type*} [AddCommGroup H] (receiver : G →+ H)
    (ledger : AddressedCurrent Index G) : AddressedCurrent Index H where
  current source target := receiver (ledger.current source target)
  self_current occurrence := by simp [ledger.self_current]

@[simp] theorem map_current {H : Type*} [AddCommGroup H] (receiver : G →+ H)
    (ledger : AddressedCurrent Index G) (source target : Index) :
    (ledger.map receiver).current source target = receiver (ledger.current source target) := rfl

/-- [proved-derived; formal-checked] Receiver transport commutes with the returned composition
defect; it cannot use a different chart for the exterior current and the fusion remainder. -/
theorem map_compositionDefect {H : Type*} [AddCommGroup H] (receiver : G →+ H)
    (ledger : AddressedCurrent Index G) (source middle target : Index) :
    (ledger.map receiver).compositionDefect source middle target =
      receiver (ledger.compositionDefect source middle target) := by
  simp [compositionDefect]

/-- [proved-derived; formal-checked] Receiver transport commutes with the complete local-current
population. -/
theorem map_pathCurrent {H : Type*} [AddCommGroup H] (receiver : G →+ H)
    (ledger : AddressedCurrent Index G) (address : ℕ → Index) (pieces : ℕ) :
    (ledger.map receiver).pathCurrent address pieces =
      receiver (ledger.pathCurrent address pieces) := by
  simp [pathCurrent, map_sum]

/-- [proved-derived; formal-checked] Receiver transport commutes with the complete defect
population. -/
theorem map_pathDefect {H : Type*} [AddCommGroup H] (receiver : G →+ H)
    (ledger : AddressedCurrent Index G) (address : ℕ → Index) (pieces : ℕ) :
    (ledger.map receiver).pathDefect address pieces =
      receiver (ledger.pathDefect address pieces) := by
  simp [pathDefect, map_compositionDefect, map_sum]

/-- [proved-derived; formal-checked] Mapping a state-induced current is the same ledger as first
mapping the state and then forming its returned differences. -/
theorem map_fromState {H : Type*} [AddCommGroup H] (receiver : G →+ H)
    (state : Index → G) :
    (fromState state).map receiver = fromState (receiver ∘ state) := by
  ext source target
  simp [Function.comp_def]

/-- [proved-derived; formal-checked] When the complete defect family vanishes, every finite local
population reconstructs its one exterior current. -/
theorem pathCurrent_eq_exterior_of_composesExactly
    (ledger : AddressedCurrent Index G) (hExact : ledger.ComposesExactly)
    (address : ℕ → Index) (pieces : ℕ) :
    ledger.pathCurrent address pieces = ledger.current (address 0) (address pieces) := by
  rw [ledger.finitePathCurrent_eq_exterior_add_defects]
  suffices ledger.pathDefect address pieces = 0 by rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro piece hpiece
  exact hExact (address 0) (address piece) (address (piece + 1))

end AddressedCurrent

/-! ## Filter-directed null current and reconstruction -/

/-- [definition] A receiver state has null current along a declared directed course precisely
when its transported filter is Cauchy. -/
def HasNullCurrentAlong {X : Type*} [UniformSpace X]
    {Index : Type*} (course : Filter Index) (state : Index → X) : Prop :=
  Cauchy (course.map state)

/-- [proved-derived; formal-checked] In a normed additive receiver, filter-directed nullity is
exactly eventual pairwise vanishing of the oriented receiver differences. -/
theorem hasNullCurrentAlong_iff_eventually_current
    {X : Type*} [NormedAddCommGroup X] {Index : Type*}
    {course : Filter Index} [NeBot course] {state : Index → X} :
    HasNullCurrentAlong course state ↔
      ∀ ε > 0, ∃ tail ∈ course,
        ∀ source ∈ tail, ∀ target ∈ tail,
          ‖state target - state source‖ < ε := by
  constructor
  · intro nullCurrent ε hε
    rcases (Metric.cauchy_iff.mp nullCurrent).2 ε hε with ⟨values, hvalues, hclose⟩
    refine ⟨state ⁻¹' values, hvalues, ?_⟩
    intro source hsource target htarget
    simpa [dist_eq_norm, norm_sub_rev] using
      hclose (state source) hsource (state target) htarget
  · intro vanishes
    apply Metric.cauchy_iff.mpr
    constructor
    · infer_instance
    · intro ε hε
      rcases vanishes ε hε with ⟨tail, htail, hclose⟩
      refine ⟨state '' tail, ?_, ?_⟩
      · change state ⁻¹' (state '' tail) ∈ course
        filter_upwards [htail] with occurrence hoccurrence
        exact ⟨occurrence, hoccurrence, rfl⟩
      · rintro _ ⟨source, hsource, rfl⟩ _ ⟨target, htarget, rfl⟩
        simpa [dist_eq_norm, norm_sub_rev] using hclose source hsource target htarget

/-- [proved-derived; formal-checked] A returned value forces null current along the same course. -/
theorem hasNullCurrentAlong_of_tendsto
    {X : Type*} [UniformSpace X] {Index : Type*}
    {course : Filter Index} [NeBot course] {state : Index → X} {returned : X}
    (returnLaw : Tendsto state course (nhds returned)) :
    HasNullCurrentAlong course state :=
  returnLaw.cauchy_map

/-- [proved-derived; formal-checked] Completeness reconstructs a returned value from a null
current along any directed course. -/
theorem exists_return_of_hasNullCurrentAlong
    {X : Type*} [UniformSpace X] [CompleteSpace X] {Index : Type*}
    {course : Filter Index} [NeBot course] {state : Index → X}
    (nullCurrent : HasNullCurrentAlong course state) :
    ∃ returned, Tendsto state course (nhds returned) :=
  cauchy_map_iff_exists_tendsto.mp nullCurrent

/-- [proved-derived; formal-checked] A separated receiver assigns at most one returned value to
one nontrivial directed course. -/
theorem directedReturn_unique
    {X : Type*} [UniformSpace X] [T2Space X] {Index : Type*}
    {course : Filter Index} [NeBot course] {state : Index → X} {left right : X}
    (leftReturned : Tendsto state course (nhds left))
    (rightReturned : Tendsto state course (nhds right)) :
    left = right :=
  tendsto_nhds_unique leftReturned rightReturned

/-- [proved-derived; formal-checked] Null current is equivalent to one unique reconstructed value
in every complete separated receiver. -/
theorem hasNullCurrentAlong_iff_existsUnique_return
    {X : Type*} [UniformSpace X] [CompleteSpace X] [T2Space X] {Index : Type*}
    {course : Filter Index} [NeBot course] {state : Index → X} :
    HasNullCurrentAlong course state ↔
      ∃! returned, Tendsto state course (nhds returned) := by
  constructor
  · intro nullCurrent
    rcases exists_return_of_hasNullCurrentAlong nullCurrent with ⟨returned, returnLaw⟩
    exact ⟨returned, returnLaw, fun other otherReturned ↦
      directedReturn_unique otherReturned returnLaw⟩
  · rintro ⟨returned, returnLaw, _unique⟩
    exact hasNullCurrentAlong_of_tendsto returnLaw

/-! ## Exact coherent histories and the loop-holonomy boundary -/

universe u

/-- [definition] A sequential local-witness system retains the witness type at every depth and
the exact fine-to-coarse restriction.  `restrict_surjective` is the constitutive extension law:
every admitted occurrence at one depth has an admitted successor at the next depth. -/
structure SuccessorWitnessSystem where
  Fibre : ℕ → Type u
  restrict : ∀ depth, Fibre (depth + 1) → Fibre depth
  baseNonempty : Nonempty (Fibre 0)
  restrict_surjective : ∀ depth, Function.Surjective (restrict depth)

/-- [definition] A coherent section is a complete oriented history, not a population of unrelated
local witnesses: every successor restricts to the witness that actually preceded it. -/
structure SuccessorWitnessSystem.CoherentSection
    (system : SuccessorWitnessSystem) where
  witness : ∀ depth, system.Fibre depth
  compatible : ∀ depth,
    system.restrict depth (witness (depth + 1)) = witness depth

namespace SuccessorWitnessSystem

/-- [proved-derived; formal-checked] Recursively choose one successor of the already chosen local
occurrence.  The construction therefore retains one lineage through every scale rather than
choosing each inhabited fibre independently. -/
noncomputable def coherentWitness (system : SuccessorWitnessSystem) :
    (depth : ℕ) → system.Fibre depth
  | 0 => Classical.choice system.baseNonempty
  | depth + 1 => Classical.choose
      (system.restrict_surjective depth (coherentWitness system depth))

/-- [proved-derived; formal-checked] Every recursive successor returns exactly to its chosen
predecessor. -/
theorem coherentWitness_compatible (system : SuccessorWitnessSystem) (depth : ℕ) :
    system.restrict depth (system.coherentWitness (depth + 1)) =
      system.coherentWitness depth := by
  exact Classical.choose_spec
    (system.restrict_surjective depth (system.coherentWitness depth))

/-- [proved-derived; formal-checked] A base occurrence plus surjective successor restriction
constructs a complete coherent history through all natural-number depths. -/
noncomputable def coherentSection (system : SuccessorWitnessSystem) :
    system.CoherentSection where
  witness := system.coherentWitness
  compatible := system.coherentWitness_compatible

/-- [proved-derived; formal-checked] The exact sequential local-to-global passage.  This theorem is
restricted to the acyclic successor course; cyclic or multiply-related index geometries owe their
own holonomy/equalization law. -/
theorem nonempty_coherentSection (system : SuccessorWitnessSystem) :
    Nonempty system.CoherentSection :=
  ⟨system.coherentSection⟩

end SuccessorWitnessSystem

/-- [definition] The smallest nontrivial orientation reversal on a two-state fibre. -/
def boolFlip (value : Bool) : Bool := !value

/-- [proved-derived; formal-checked] Local orientation reversal is itself a bijective transport. -/
theorem boolFlip_surjective : Function.Surjective boolFlip := by
  intro value
  exact ⟨!value, by cases value <;> rfl⟩

/-- [definition] A section around the one-step reversal loop would have to be fixed by its loop
return. -/
structure BoolFlipCoherent where
  witness : Bool
  compatible : boolFlip witness = witness

/-- [counterexample; formal-checked] Bijective local transport and inhabited local fibres do not
produce a global section around a loop: nonzero holonomy has no fixed occurrence here.  Thus the
acyclic theorem above cannot be promoted to arbitrary index geometry without an exact loop-return
condition. -/
theorem boolFlipCoherent_isEmpty : IsEmpty BoolFlipCoherent := by
  constructor
  rintro ⟨witness, compatible⟩
  cases witness <;> simp [boolFlip] at compatible

/-- [proved-derived; formal-checked] A cofinal/restricting reindexing preserves null current. -/
theorem HasNullCurrentAlong.reindex
    {X : Type*} [UniformSpace X] {Index Reindex : Type*}
    {course : Filter Index} {reindexedCourse : Filter Reindex} [NeBot reindexedCourse]
    {state : Index → X} {reindex : Reindex → Index}
    (nullCurrent : HasNullCurrentAlong course state)
    (cofinal : Tendsto reindex reindexedCourse course) :
    HasNullCurrentAlong reindexedCourse (state ∘ reindex) := by
  have restricted : Cauchy ((reindexedCourse.map reindex).map state) :=
    nullCurrent.mono (Filter.map_mono cofinal)
  change Cauchy (reindexedCourse.map (state ∘ reindex))
  simpa [Filter.map_map, Function.comp_def] using restricted

/-- [proved-derived; formal-checked] A uniformly continuous receiver chart transports null
current without deleting the source course. -/
theorem HasNullCurrentAlong.map
    {X Y : Type*} [UniformSpace X] [UniformSpace Y] {Index : Type*}
    {course : Filter Index} {state : Index → X}
    (nullCurrent : HasNullCurrentAlong course state)
    {receiver : X → Y} (continuous : UniformContinuous receiver) :
    HasNullCurrentAlong course (receiver ∘ state) := by
  have returned := Cauchy.map nullCurrent continuous
  change Cauchy (course.map (receiver ∘ state))
  simpa [Filter.map_map, Function.comp_def] using returned

/-- [proved-derived; formal-checked] Two null receiver currents pair into one product current;
neither branch is discarded. -/
theorem hasNullCurrentAlong_pair
    {X Y : Type*} [UniformSpace X] [UniformSpace Y] {Index : Type*}
    {course : Filter Index} {left : Index → X} {right : Index → Y}
    (leftNull : HasNullCurrentAlong course left)
    (rightNull : HasNullCurrentAlong course right) :
    HasNullCurrentAlong course (fun occurrence ↦ (left occurrence, right occurrence)) := by
  change Cauchy (course.map (fun occurrence ↦ (left occurrence, right occurrence)))
  rw [cauchy_prod_iff]
  constructor
  · change Cauchy (course.map left)
    exact leftNull
  · change Cauchy (course.map right)
    exact rightNull

/-- [proved-derived; formal-checked] The increasing natural-number course is exactly the usual
Cauchy-sequence receiver. -/
theorem hasNullCurrentAlong_atTop_iff_cauchySeq
    {X : Type*} [UniformSpace X] {state : ℕ → X} :
    HasNullCurrentAlong atTop state ↔ CauchySeq state :=
  Iff.rfl

section Audit

#print axioms AddressedCurrent.finitePathCurrent_eq_exterior_add_defects
#print axioms AddressedCurrent.closedPathCurrent_eq_defects
#print axioms AddressedCurrent.pathCurrent_eq_exterior_of_composesExactly
#print axioms AddressedCurrent.map_compositionDefect
#print axioms AddressedCurrent.map_pathCurrent
#print axioms AddressedCurrent.map_pathDefect
#print axioms AddressedCurrent.map_fromState
#print axioms hasNullCurrentAlong_iff_eventually_current
#print axioms hasNullCurrentAlong_iff_existsUnique_return
#print axioms SuccessorWitnessSystem.nonempty_coherentSection
#print axioms boolFlipCoherent_isEmpty
#print axioms HasNullCurrentAlong.reindex
#print axioms HasNullCurrentAlong.map
#print axioms hasNullCurrentAlong_pair

end Audit

end Soma.Holonics.Millennium.HolonicDirectedPassage
