import ElementaryHolonics.Foundation.CoordinateSubsetReceiver
import ElementaryHolonics.Foundation.OrderedWordChain
import ElementaryHolonics.Millennium.Aperture
import ElementaryHolonics.Millennium.AthenaReceiverHistory
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Finite causal aperture

This file separates five populations which a finite generator count does not identify:

* [definition] `N` addressed causal generators;
* [proved-derived] `N ^ depth` ordered generator words at one fixed depth;
* [proved-derived] `Nat.choose N arity` unordered supports of one fixed interaction arity;
* [conditional] a finite local particle population, which additionally requires a finite
  slot/packing certificate;
* [conditional] a finite dynamically closed outcome quotient, which may classify an infinite or
  continuous microscopic carrier without asserting that carrier finite.

[counterexample; formal-checked] A nonempty finite generator family alone does not bound particle
occupancy: arbitrarily many particle occurrences may carry the same generator address.  Nor does
finite one-step branching make the complete future orbit finite: one generator can repeatedly
advance a natural-number state.

[proved-derived; formal-checked] The finite configuration formulas in this file are therefore
receiver theorems, not claims that relativity, a lattice, cross-entropy, or the number eleven by
itself supplies a physical ultraviolet cutoff.  A finite outcome atlas is instead supplied by a
declared complete receiver/history quotient whose generator law descends every ordered successor
word.  Relativistic compatibility, group selection laws, conservation, boundary conditions, and
constitutive equations enter through the passages which found that quotient.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicFiniteCausalAperture

open Soma.Holonics
open Soma.Holonics.Millennium.AthenaReceiverHistory
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.LineageCompression

/-! ## Fixed-depth and fixed-arity populations -/

/-- [definition] One addressed generator word of an exact chronological depth. -/
abbrev GeneratorWord (generatorCount depth : ℕ) :=
  OrderedWordChain.Word (Fin generatorCount) depth

/-- [proved-derived; formal-checked] A finite alphabet of `N` generators has exactly `N ^ depth`
ordered words of one fixed depth.  This does not count all words of unbounded depth. -/
theorem generatorWord_card (generatorCount depth : ℕ) :
    Fintype.card (GeneratorWord generatorCount depth) = generatorCount ^ depth := by
  simp [GeneratorWord, OrderedWordChain.Word, Fintype.card_fun]

/-- [definition] One generator word whose exact depth lies in the declared finite horizon
`0, ..., horizon`. -/
abbrev BoundedGeneratorWord (generatorCount horizon : ℕ) :=
  Σ depth : Fin (horizon + 1), GeneratorWord generatorCount depth

/-- [proved-derived; formal-checked] The complete lineage population through a finite horizon is
the finite geometric prefix `Σ_(depth = 0)^horizon N ^ depth`.  Relations can collapse endpoint
images, but do not erase this addressed word population. -/
theorem boundedGeneratorWord_card (generatorCount horizon : ℕ) :
    Fintype.card (BoundedGeneratorWord generatorCount horizon) =
      ∑ depth : Fin (horizon + 1), generatorCount ^ (depth : ℕ) := by
  simp [BoundedGeneratorWord, generatorWord_card]

/-- [definition] One unordered support of distinct generators at a fixed interaction arity. -/
abbrev GeneratorSupport (generatorCount arity : ℕ) :=
  {support : Finset (Fin generatorCount) // support.card = arity}

/-- [proved-standard; formal-checked] The unordered arity-`k` supports of `N` generators are counted
by the binomial coefficient `Nat.choose N k`. -/
theorem generatorSupport_card (generatorCount arity : ℕ) :
    Fintype.card (GeneratorSupport generatorCount arity) =
      Nat.choose generatorCount arity := by
  simpa [GeneratorSupport] using
    (Fintype.card_finset_len (alpha := Fin generatorCount) arity)

/-- [definition] One unordered pairwise generator channel. -/
abbrev PairGeneratorChannel (generatorCount : ℕ) :=
  GeneratorSupport generatorCount 2

/-- [proved-derived; formal-checked] `N` generators expose `Nat.choose N 2` unordered pair channels. -/
theorem pairGeneratorChannel_card (generatorCount : ℕ) :
    Fintype.card (PairGeneratorChannel generatorCount) = Nat.choose generatorCount 2 := by
  exact generatorSupport_card generatorCount 2

/-- [proved-standard; formal-checked] Erasing chronology and multiplicity all the way down to an
unordered support gives `2 ^ N` possible generator subsets. -/
theorem allGeneratorSupports_card (generatorCount : ℕ) :
    Fintype.card (Finset (Fin generatorCount)) = 2 ^ generatorCount := by
  simpa using (Fintype.card_finset (alpha := Fin generatorCount))

/-- [proved-derived; formal-checked] Four generator directions have six unordered pair faces. -/
theorem fourGeneratorPairChannel_card :
    Fintype.card (PairGeneratorChannel 4) = 6 := by
  rw [pairGeneratorChannel_card]
  decide

/-- [proved-derived; formal-checked] Substituting eleven generator addresses yields fifty-five
unordered pair faces.  This arithmetic statement does not identify the addresses with spacetime
dimensions, supercharges, particles, or force species. -/
theorem elevenGeneratorPairChannel_card :
    Fintype.card (PairGeneratorChannel 11) = 55 := by
  rw [pairGeneratorChannel_card]
  decide

/-- [proved-derived; formal-checked] Eleven generator addresses have 2048 unordered subset faces
after chronology and repetition have been lawfully forgotten. -/
theorem elevenGeneratorSubset_card :
    Fintype.card (Finset (Fin 11)) = 2048 := by
  norm_num [allGeneratorSupports_card]

/-! ## Finite generators do not bound occupancy or complete history -/

/-- [definition] Assign every particle occurrence to the same available generator address. -/
def constantGeneratorAssignment {generatorCount : ℕ} (nonempty : 0 < generatorCount)
    (particleCount : ℕ) : Fin particleCount → Fin generatorCount :=
  fun _ => ⟨0, nonempty⟩

/-- [counterexample; formal-checked] For every proposed particle bound and every nonempty finite
generator family, there is a strictly larger finite particle population carrying generator
addresses.  Consequently no occupancy ceiling is a function of `generatorCount` alone. -/
theorem finiteGenerators_do_not_bound_particlePopulation
    (generatorCount proposedBound : ℕ) (nonempty : 0 < generatorCount) :
    proposedBound < Fintype.card (Fin (proposedBound + 1)) ∧
      Nonempty (Fin (proposedBound + 1) → Fin generatorCount) := by
  constructor
  · simp
  · exact ⟨constantGeneratorAssignment nonempty (proposedBound + 1)⟩

/-- [definition] One generator repeatedly advances a natural-number state. -/
def oneGeneratorOrbit : ℕ → ℕ
  | 0 => 0
  | depth + 1 => oneGeneratorOrbit depth + 1

/-- [proved-derived; formal-checked] The one-generator orbit retains its full chronological depth. -/
@[simp] theorem oneGeneratorOrbit_eq (depth : ℕ) : oneGeneratorOrbit depth = depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [oneGeneratorOrbit, inductionHypothesis]

/-- [counterexample; formal-checked] A one-generator system can have infinitely many
lineage-distinct states; finite immediate branching does not imply a finite complete orbit. -/
theorem finiteBranching_does_not_force_finiteOrbit :
    Function.Injective oneGeneratorOrbit := by
  intro left right equalOrbit
  simpa using equalOrbit

/-! ## A finite outcome quotient does not require finite microscopic state -/

/-- [definition] The realized outcome population is the image of the complete causal quotient.
The microscopic carrier remains unrestricted: it need not carry a `Finite` or `Fintype` instance. -/
abbrev RealizedOutcome
    {Generator Receiver Source Quotient Face : Type*}
    (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face) :=
  Set.range C.present.quotient

/-- [definition] One microscopic occurrence after one arbitrary admitted ordered history, read only
through the complete causal quotient. -/
def successorOutcome
    {Generator Receiver Source Quotient Face : Type*}
    (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face) :
    Source × List Generator → Quotient
  | (source, word) => C.present.quotient (transportWord C.sourceTransport word source)

/-- [definition] The population of all quotient outcomes reached from all microscopic occurrences
through all finite admitted ordered histories.  The history population itself need not be finite. -/
abbrev SuccessorOutcomePopulation
    {Generator Receiver Source Quotient Face : Type*}
    (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face) :=
  Set.range (successorOutcome C)

/-- [conditional; formal-checked] If one causally constrained ecology supplies a complete
receiver/history quotient into a finite outcome type, its realized causal outcome population is
bounded by that finite type even when the microscopic source carrier is infinite or continuous. -/
theorem realizedOutcome_natCard_le
    {Generator Receiver Source Quotient Face : Type*} [Fintype Quotient]
    (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face) :
    Nat.card (RealizedOutcome C) ≤ Fintype.card Quotient := by
  letI : Finite (RealizedOutcome C) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (RealizedOutcome C) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- [proved-derived; formal-checked] Allowing every finite ordered microscopic history does not
enlarge the outcome population beyond the quotient image: an evolved microstate is still a source
occurrence, and the empty history realizes every present quotient face. -/
theorem successorOutcomePopulation_eq_realizedOutcome
    {Generator Receiver Source Quotient Face : Type*}
    (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face) :
    SuccessorOutcomePopulation C = RealizedOutcome C := by
  ext quotient
  constructor
  · rintro ⟨⟨source, word⟩, rfl⟩
    exact ⟨transportWord C.sourceTransport word source, rfl⟩
  · rintro ⟨source, rfl⟩
    exact ⟨(source, []), rfl⟩

/-- [conditional; formal-checked] A finite complete quotient therefore bounds the complete
successor-outcome population over an unrestricted microscopic source and an unbounded population
of finite histories. -/
theorem successorOutcome_natCard_le
    {Generator Receiver Source Quotient Face : Type*} [Fintype Quotient]
    (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face) :
    Nat.card (SuccessorOutcomePopulation C) ≤ Fintype.card Quotient := by
  rw [successorOutcomePopulation_eq_realizedOutcome]
  exact realizedOutcome_natCard_le C

/-- [conditional; formal-checked] The local generator law carries the finite quotient through an
arbitrary ordered history.  Thus "after any amount of time" is paid for by dynamic closure, not by
placing a finite horizon on microscopic histories. -/
theorem finiteOutcome_commutesWithEveryOrderedHistory
    {Generator Receiver Source Quotient Face : Type*} [Fintype Quotient]
    (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face)
    (word : List Generator) (source : Source) :
    C.present.quotient (transportWord C.sourceTransport word source) =
      transportWord C.quotientTransport word (C.present.quotient source) :=
  C.toReceiverHistoryCompression.quotientCommutesWithEveryOrderedWord word source

/-- [conditional; formal-checked] The successor outcome is computable entirely on the finite
quotient after the initial microscopic occurrence has crossed the quotient port. -/
theorem successorOutcome_eq_descended
    {Generator Receiver Source Quotient Face : Type*} [Fintype Quotient]
    (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face)
    (word : List Generator) (source : Source) :
    successorOutcome C (source, word) =
      transportWord C.quotientTransport word (C.present.quotient source) :=
  C.toReceiverHistoryCompression.quotientCommutesWithEveryOrderedWord word source

/-- [conditional; formal-checked] Every declared receiver after every ordered history factors
through the same finite outcome face.  Equal quotient faces therefore remain indistinguishable for
the entire admitted future family, while the complete microscopic reconstruction fibre is retained. -/
theorem finiteOutcome_exactForEveryReceiverHistory
    {Generator Receiver Source Quotient Face : Type*} [Fintype Quotient]
    (C : CompleteReceiverHistoryQuotient Generator Receiver Source Quotient Face)
    (receiver : Receiver) (word : List Generator) (source : Source) :
    C.present.receiver receiver (transportWord C.sourceTransport word source) =
      C.toReceiverHistoryCompression.futureFactor (receiver, word)
        (C.present.quotient source) :=
  (C.toReceiverHistoryCompression.allSuccessorHistories.exact (receiver, word) source).symm

namespace InfiniteMicroscopicTwoOutcomeControl

/-- [definition] An infinite microscopic successor chain alternates between two receiver outcomes. -/
def outcome : ℕ → Bool
  | 0 => false
  | depth + 1 => !(outcome depth)

/-- [definition] The complete quotient has an infinite microscopic carrier `ℕ`, two outcome faces,
one successor generator, and exact closure under the Boolean flip. -/
def ecology : CompleteReceiverHistoryQuotient Unit Unit ℕ Bool Bool where
  toReceiverHistoryCompression :=
    { present :=
        { quotient := outcome
          receiver := fun _ source => outcome source
          factor := fun _ quotient => quotient
          exact := fun _ _ => rfl }
      sourceTransport := fun _ source => source + 1
      quotientTransport := fun _ quotient => !quotient
      generatorExact := fun _ _ => rfl }
  complete := by
    intro left right equalFuture
    exact equalFuture () []

/-- [proved-standard; formal-checked] The microscopic source carrier used by this control is
infinite. -/
theorem microscopicSource_infinite : Infinite ℕ := inferInstance

/-- [proved-derived; formal-checked] The microscopic carrier is not collapsed injectively: distinct
states zero and two occupy the same retained outcome fibre. -/
theorem distinctMicroscopicStates_shareOutcome :
    (0 : ℕ) ≠ 2 ∧ ecology.present.quotient 0 = ecology.present.quotient 2 := by
  decide

/-- [proved-derived; formal-checked] The same ecology has exactly two available outcome faces. -/
theorem outcome_card : Fintype.card Bool = 2 := by
  decide

/-- [proved-derived; formal-checked] Despite its infinite microscopic successor orbit, the quotient
remains closed in the same two-outcome atlas through every finite ordered history. -/
theorem everyHistory_remainsInTwoOutcomeAtlas (word : List Unit) (source : ℕ) :
    ecology.present.quotient (transportWord ecology.sourceTransport word source) =
      transportWord ecology.quotientTransport word (ecology.present.quotient source) :=
  ecology.toReceiverHistoryCompression.quotientCommutesWithEveryOrderedWord word source

/-- [proved-derived; formal-checked] In this control, quotient equality is exactly equality of the
complete receiver/history signature, not merely agreement at one observation time. -/
theorem outcomeEq_iff_completeCausalSignatureEq {left right : ℕ} :
    ecology.present.quotient left = ecology.present.quotient right ↔
      ecology.causalSignature left = ecology.causalSignature right :=
  ecology.quotientEq_iff_causalSignatureEq

end InfiniteMicroscopicTwoOutcomeControl

/-! ## The local interaction link -/

/-- [definition] A finite receiver-, region-, and scale-indexed interaction link.  Its vertices
are situated candidate occurrences and its faces are the populations admitted to interact
jointly.  A physical realization must carry the event/region, scale or energy aperture, incidence,
orientation, constitutive law, conservation, and resource testimony used to build `faces`. -/
structure FiniteInteractionLink (Occurrence : Type*) [DecidableEq Occurrence] where
  faces : Finset (Finset Occurrence)

/-- [definition] The local concurrency capacity is the largest admitted face cardinality, with
zero returned for an empty face population. -/
def FiniteInteractionLink.concurrencyCapacity
    {Occurrence : Type*} [DecidableEq Occurrence]
    (link : FiniteInteractionLink Occurrence) : ℕ :=
  link.faces.sup Finset.card

/-- [proved-derived; formal-checked] Every admitted interaction population is bounded by the
declared link's concurrency capacity. -/
theorem FiniteInteractionLink.face_card_le_concurrencyCapacity
    {Occurrence : Type*} [DecidableEq Occurrence]
    (link : FiniteInteractionLink Occurrence) {face : Finset Occurrence}
    (admitted : face ∈ link.faces) :
    face.card ≤ link.concurrencyCapacity := by
  exact Finset.le_sup (f := Finset.card) admitted

/-- [definition] A flag receipt says that many-body admissibility is completely determined by
pair admissibility.  Without this extra law the link remains a genuine hypergraph/cellular link:
all pairs may be admitted while a triple is obstructed by frustration, conservation, anomaly, or
resource testimony. -/
def FiniteInteractionLink.IsPairwiseComplete
    {Occurrence : Type*} [DecidableEq Occurrence]
    (link : FiniteInteractionLink Occurrence) : Prop :=
  ∀ face : Finset Occurrence,
    face ∈ link.faces ↔
      ∀ pair ∈ face.powersetCard 2, pair ∈ link.faces

/-! ## The missing physical input: a finite resolved local capacity -/

/-- [definition] A finite local packing certificate is an injective placement of particle
occurrences into declared receiver-distinguishable slots.  Geometry, exclusion, an energy cutoff,
or another physical law must supply the slots and the injection in any realization. -/
structure ResolvedLocalPacking (Particle Slot : Type*) [Finite Slot] where
  slot : Particle → Slot
  separated : Function.Injective slot

/-- [conditional; formal-checked] Injection into finite receiver slots supplies, rather than
presupposes, finiteness of the particle population. -/
theorem particle_finite_of_resolvedPacking
    {Particle Slot : Type*} [Finite Slot]
    (packing : ResolvedLocalPacking Particle Slot) :
    Finite Particle :=
  Finite.of_injective packing.slot packing.separated

/-- [conditional; formal-checked] A resolved packing bounds particle occupancy by the number of
available slots. -/
theorem particle_natCard_le_slot_card
    {Particle Slot : Type*} [Fintype Slot]
    (packing : ResolvedLocalPacking Particle Slot) :
    Nat.card Particle ≤ Fintype.card Slot := by
  letI : Finite Particle := particle_finite_of_resolvedPacking packing
  letI : Fintype Particle := Fintype.ofFinite Particle
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective packing.slot packing.separated

/-- [definition] One receiver-distinguishable slot consists of a generator-family address and a
finite within-family capacity address. -/
abbrev FamilyCapacitySlot (generatorCount capacityPerGenerator : ℕ) :=
  Fin generatorCount × Fin capacityPerGenerator

/-- [conditional; formal-checked] If co-present particles inject into `N × capacity` addressed
slots, their population is at most `N * capacity`.  The injection is the retained packing or
exclusion hypothesis missing from a bare generator count. -/
theorem localParticle_card_le_familyCapacity
    {Particle : Type*}
    {generatorCount capacityPerGenerator : ℕ}
    (packing : ResolvedLocalPacking Particle
      (FamilyCapacitySlot generatorCount capacityPerGenerator)) :
    Nat.card Particle ≤ generatorCount * capacityPerGenerator := by
  simpa [FamilyCapacitySlot] using particle_natCard_le_slot_card packing

/-! ## Pairwise local configurations after capacity has been supplied -/

/-- [definition] Unordered pairs of a fixed finite particle aperture. -/
abbrev ParticlePairChannel (particleCount : ℕ) := GeneratorSupport particleCount 2

/-- [definition] Unordered pairs from an arbitrary finite particle aperture. -/
abbrev ParticlePair (Particle : Type*) :=
  {support : Finset Particle // support.card = 2}

/-- [definition] A pair is admitted when its two oriented readings both pass the declared family
coupling relation.  The relation can carry relativistic, group-representation, or constitutive
selection testimony supplied by a realization. -/
def PairCompatible
    {Particle Family : Type*} [Fintype Particle] [DecidableEq Particle]
    (family : Particle → Family) (coupled : Family → Family → Bool)
    (pair : ParticlePair Particle) : Prop :=
  ∀ left ∈ pair.1, ∀ right ∈ pair.1, left ≠ right →
    coupled (family left) (family right) = true

/-- [definition] The subtype of particle pairs retained by the declared coupling law. -/
abbrev AdmissibleParticlePair
    {Particle Family : Type*} [Fintype Particle] [DecidableEq Particle]
    (family : Particle → Family) (coupled : Family → Family → Bool) :=
  {pair : ParticlePair Particle // PairCompatible family coupled pair}

/-- [conditional; formal-checked] Family and relativistic compatibility can only remove pair
occurrences from the complete local pair aperture. -/
theorem admissibleParticlePair_card_le
    {Particle Family : Type*} [Fintype Particle] [DecidableEq Particle]
    (family : Particle → Family) (coupled : Family → Family → Bool) :
    Nat.card (AdmissibleParticlePair family coupled) ≤
      Nat.choose (Fintype.card Particle) 2 := by
  classical
  letI : Finite (AdmissibleParticlePair family coupled) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (AdmissibleParticlePair family coupled) := Fintype.ofFinite _
  calc
    Nat.card (AdmissibleParticlePair family coupled) =
        Fintype.card (AdmissibleParticlePair family coupled) :=
      Nat.card_eq_fintype_card
    _ ≤
        Fintype.card (ParticlePair Particle) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = Nat.choose (Fintype.card Particle) 2 := by
      simpa [ParticlePair] using (Fintype.card_finset_len (alpha := Particle) 2)

/-- [definition] A pair occurrence decorated by an unordered pairwise generator-family channel. -/
abbrev DecoratedPairChannel (particleCount generatorCount : ℕ) :=
  ParticlePairChannel particleCount × PairGeneratorChannel generatorCount

/-- [proved-derived; formal-checked] The ambient decorated pair population is the product of the
particle-pair and generator-pair populations.  Compatibility and group selection laws may retain a
subtype of this population; they do not increase it. -/
theorem decoratedPairChannel_card (particleCount generatorCount : ℕ) :
    Fintype.card (DecoratedPairChannel particleCount generatorCount) =
      Nat.choose particleCount 2 * Nat.choose generatorCount 2 := by
  simp [DecoratedPairChannel, ParticlePairChannel, PairGeneratorChannel,
    generatorSupport_card]

/-- [definition] One finite-alphabet receiver value on every decorated pair channel. -/
abbrev PairwiseLocalConfiguration
    (particleCount generatorCount : ℕ) (ChannelState : Type*) :=
  DecoratedPairChannel particleCount generatorCount → ChannelState

/-- [conditional; formal-checked] Once particle capacity and a finite channel-state alphabet are
declared, the ambient pairwise configuration population is finite with the exact displayed
cardinality.  Physical compatibility laws define subtypes and can only reduce this population. -/
theorem pairwiseLocalConfiguration_card
    (particleCount generatorCount : ℕ) (ChannelState : Type*) [Fintype ChannelState] :
    Fintype.card (PairwiseLocalConfiguration particleCount generatorCount ChannelState) =
      Fintype.card ChannelState ^
        (Nat.choose particleCount 2 * Nat.choose generatorCount 2) := by
  rw [Fintype.card_fun, decoratedPairChannel_card]

/-! ## Separating receivers -/

/-- [conditional; formal-checked] A finite family of finite-alphabet readings which separates a
finite configuration population supplies the aperture bound `|X| ≤ |Y| ^ |F|`. -/
theorem finiteSeparatingReceiver_boundsConfiguration
    {Configuration Reading : Type*}
    [Fintype Configuration] [Fintype Reading]
    [DecidableEq Configuration] [DecidableEq Reading]
    (family : Finset (Configuration → Reading))
    (separates : ∀ left right : Configuration,
      Separation.collapseOf (↑family : Set (Configuration → Reading)) left right →
        left = right) :
    Fintype.card Configuration ≤ Fintype.card Reading ^ family.card :=
  Aperture.theSeparatingFamilyIsLargeEnough family separates

section Audit

#print axioms generatorWord_card
#print axioms boundedGeneratorWord_card
#print axioms generatorSupport_card
#print axioms pairGeneratorChannel_card
#print axioms allGeneratorSupports_card
#print axioms fourGeneratorPairChannel_card
#print axioms elevenGeneratorPairChannel_card
#print axioms elevenGeneratorSubset_card
#print axioms finiteGenerators_do_not_bound_particlePopulation
#print axioms finiteBranching_does_not_force_finiteOrbit
#print axioms realizedOutcome_natCard_le
#print axioms successorOutcomePopulation_eq_realizedOutcome
#print axioms successorOutcome_natCard_le
#print axioms finiteOutcome_commutesWithEveryOrderedHistory
#print axioms successorOutcome_eq_descended
#print axioms finiteOutcome_exactForEveryReceiverHistory
#print axioms InfiniteMicroscopicTwoOutcomeControl.microscopicSource_infinite
#print axioms InfiniteMicroscopicTwoOutcomeControl.distinctMicroscopicStates_shareOutcome
#print axioms InfiniteMicroscopicTwoOutcomeControl.outcome_card
#print axioms InfiniteMicroscopicTwoOutcomeControl.everyHistory_remainsInTwoOutcomeAtlas
#print axioms InfiniteMicroscopicTwoOutcomeControl.outcomeEq_iff_completeCausalSignatureEq
#print axioms FiniteInteractionLink.face_card_le_concurrencyCapacity
#print axioms particle_finite_of_resolvedPacking
#print axioms particle_natCard_le_slot_card
#print axioms localParticle_card_le_familyCapacity
#print axioms admissibleParticlePair_card_le
#print axioms decoratedPairChannel_card
#print axioms pairwiseLocalConfiguration_card
#print axioms finiteSeparatingReceiver_boundsConfiguration

end Audit

end Soma.Holonics.Millennium.HolonicFiniteCausalAperture
