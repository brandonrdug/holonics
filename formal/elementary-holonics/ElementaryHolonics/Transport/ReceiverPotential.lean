import ElementaryHolonics.Foundation.Receiver
import ElementaryHolonics.Foundation.TransportWord
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-!
# Compatible potential is the future image of a retained receiver fibre

[definition] The existing `receiverPreimageFibre` supplies the source population, on an actually
observed entering face. `outcomes` is its image through an admitted future receiver. A future
receiver may include an ordered transport word; no new transition engine is introduced.

[proved-derived] Additional observation refines that image; a source rebase transports it
exactly; receiver-relative tolerance can justify an explicitly requested consequence while the
source remains plural. The reference in a distance bound is a receiver reference, not a chosen
source or an automatic generation policy. These laws impose no universal certainty gate.
-/

namespace Soma.Holonics.Transport.ReceiverPotential

open Soma.Holonics

/-- The complete future faces of the existing compatible-source fibre. -/
def outcomes {Source Observation Result : Type*}
    (entering : Source → Observation) (observed : Set.range entering)
    (future : Source → Result) : Set Result :=
  Set.range (fun source : receiverPreimageFibre entering observed ↦ future source.1)

/-- This is the existing receiver-to-receiver relation, with its admitted entering face fixed. -/
theorem mem_outcomes_iff {Source Observation Result : Type*}
    (entering : Source → Observation) (observed : Set.range entering)
    (future : Source → Result) (result : Result) :
    result ∈ outcomes entering observed future ↔
      receiverToReceiverRelation entering future observed.1 result := by
  constructor
  · rintro ⟨⟨source, hsource⟩, hfuture⟩
    exact ⟨source, hsource, hfuture⟩
  · rintro ⟨source, hsource, hfuture⟩
    exact ⟨⟨source, hsource⟩, hfuture⟩

/-- An actual observation has a nonempty future image, without constructing an inverse. -/
theorem outcomes_nonempty {Source Observation Result : Type*}
    (entering : Source → Observation) (observed : Set.range entering)
    (future : Source → Result) : (outcomes entering observed future).Nonempty := by
  obtain ⟨source, hsource⟩ := observed.2
  exact ⟨future source, ⟨⟨source, hsource⟩, rfl⟩⟩

/-- A later receiver acts on the entire admitted future image. -/
theorem outcomes_map {Source Observation Result Reading : Type*}
    (entering : Source → Observation) (observed : Set.range entering)
    (future : Source → Result) (receiver : Result → Reading) :
    outcomes entering observed (receiver ∘ future) =
      receiver '' outcomes entering observed future := by
  ext reading
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨future source.1, ⟨source, rfl⟩, rfl⟩
  · rintro ⟨result, ⟨source, rfl⟩, rfl⟩
    exact ⟨source, rfl⟩

/-- An explicit factor determines one future face for the whole fibre, without determining a
unique source. This is the constructive special case of the existing transformer criterion. -/
theorem outcomes_singleton_of_factor {Source Observation Result : Type*}
    (entering : Source → Observation) (observed : Set.range entering)
    (future : Source → Result) (factor : Observation → Result)
    (factors : ∀ source, future source = factor (entering source)) :
    outcomes entering observed future = {factor observed.1} := by
  ext result
  constructor
  · rintro ⟨source, rfl⟩
    simp [factors, source.2]
  · intro hresult
    obtain ⟨source, hsource⟩ := observed.2
    exact ⟨⟨source, hsource⟩, by simpa [factors, hsource] using hresult.symm⟩

/-- Forget the additional reading while retaining proof of an actually observed first face. -/
def forgetAdditional {Source Observation Additional : Type*}
    (entering : Source → Observation) (additional : Source → Additional)
    (observed : Set.range (fun source ↦ (entering source, additional source))) :
    Set.range entering :=
  ⟨observed.1.1, by
    obtain ⟨source, hsource⟩ := observed.2
    exact ⟨source, congrArg Prod.fst hsource⟩⟩

/-- Refining an observation removes only incompatible sources and their future faces. -/
theorem additional_observation_refines {Source Observation Additional Result : Type*}
    (entering : Source → Observation) (additional : Source → Additional)
    (observed : Set.range (fun source ↦ (entering source, additional source)))
    (future : Source → Result) :
    outcomes (fun source ↦ (entering source, additional source)) observed future ⊆
      outcomes entering (forgetAdditional entering additional observed) future := by
  rintro result ⟨source, hresult⟩
  exact ⟨⟨source.1, congrArg Prod.fst source.2⟩, hresult⟩

/-- The same observed value in a source chart transported by an explicit equivalence. -/
def rebaseObservation {Source Target Observation : Type*}
    (rebase : Source ≃ Target) (entering : Source → Observation)
    (observed : Set.range entering) : Set.range (entering ∘ rebase.symm) :=
  ⟨observed.1, by
    obtain ⟨source, hsource⟩ := observed.2
    exact ⟨rebase source, by simpa using hsource⟩⟩

/-- Recharting both observation and future receiver transports the complete potential exactly. -/
theorem outcomes_rebase {Source Target Observation Result : Type*}
    (rebase : Source ≃ Target) (entering : Source → Observation)
    (observed : Set.range entering) (future : Source → Result) :
    outcomes (entering ∘ rebase.symm) (rebaseObservation rebase entering observed)
      (future ∘ rebase.symm) = outcomes entering observed future := by
  ext result
  constructor
  · rintro ⟨source, hresult⟩
    exact ⟨⟨rebase.symm source.1, source.2⟩, hresult⟩
  · rintro ⟨source, hresult⟩
    refine ⟨⟨rebase source.1, ?_⟩, ?_⟩
    · simpa [rebaseObservation] using source.2
    · simpa using hresult

section Tolerance

variable {Source Observation Result Reading : Type*}
  [PseudoMetricSpace Result] [PseudoMetricSpace Reading]

/-- A declared Lipschitz receiver transports a bound on the whole compatible future family. -/
theorem bounded_outcomes_transport
    (entering : Source → Observation) (observed : Set.range entering)
    (future : Source → Result) (receiver : Result → Reading)
    (reference : Result) (tolerance gain : ℝ) (gain_nonnegative : 0 ≤ gain)
    (bounded : ∀ result ∈ outcomes entering observed future,
      dist result reference ≤ tolerance)
    (transport_bound : ∀ left right,
      dist (receiver left) (receiver right) ≤ gain * dist left right) :
    ∀ reading ∈ outcomes entering observed (receiver ∘ future),
      dist reading (receiver reference) ≤ gain * tolerance := by
  rintro reading ⟨source, rfl⟩
  exact (transport_bound _ _).trans
    (mul_le_mul_of_nonneg_left (bounded _ ⟨source, rfl⟩) gain_nonnegative)

/-- A receiver ball wholly inside an admitted consequence region suffices for every compatible
source. This proves that particular use without selecting a source from the fibre. -/
theorem bounded_outcomes_suffice
    (entering : Source → Observation) (observed : Set.range entering)
    (future : Source → Result) (reference : Result) (tolerance : ℝ)
    (admitted : Set Result)
    (bounded : ∀ result ∈ outcomes entering observed future,
      dist result reference ≤ tolerance)
    (inside : ∀ result, dist result reference ≤ tolerance → result ∈ admitted) :
    outcomes entering observed future ⊆ admitted := by
  intro result hresult
  exact inside result (bounded result hresult)

/-- Every pair of compatible future faces lies within twice the declared reference tolerance. -/
theorem compatible_outcomes_pairwise_bound
    (entering : Source → Observation) (observed : Set.range entering)
    (future : Source → Result) (reference : Result) (tolerance : ℝ)
    (bounded : ∀ result ∈ outcomes entering observed future,
      dist result reference ≤ tolerance)
    {left right : Result} (hleft : left ∈ outcomes entering observed future)
    (hright : right ∈ outcomes entering observed future) :
    dist left right ≤ 2 * tolerance := by
  calc
    dist left right ≤ dist left reference + dist reference right := dist_triangle _ _ _
    _ ≤ tolerance + tolerance := by
      rw [dist_comm reference right]
      exact add_le_add (bounded _ hleft) (bounded _ hright)
    _ = 2 * tolerance := by ring

end Tolerance

/-- Shrinking bounds on complete future families force every supplied compatible readout
sequence to converge at this receiver. The source carriers and observations may change at
every cut; no source selection or singleton source-fibre conclusion is constructed. -/
theorem future_observations_converge
    {Source Observation : ℕ → Type*} {Result : Type*} [PseudoMetricSpace Result]
    (entering : ∀ n, Source n → Observation n)
    (observed : ∀ n, Set.range (entering n)) (future : ∀ n, Source n → Result)
    (reference : Result) (tolerance : ℕ → ℝ)
    (shrinks : Filter.Tendsto tolerance Filter.atTop (nhds 0))
    (bounded : ∀ n result, result ∈ outcomes (entering n) (observed n) (future n) →
      dist result reference ≤ tolerance n)
    (readout : ℕ → Result)
    (compatible : ∀ n, readout n ∈ outcomes (entering n) (observed n) (future n)) :
    Filter.Tendsto readout Filter.atTop (nhds reference) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ bounded n _ (compatible n)) shrinks

/-- The future may be the standing ordered transport word followed by any declared receiver. -/
def historyOutcomes {Source Observation Generator Result : Type*}
    (entering : Source → Observation) (observed : Set.range entering)
    (transport : Generator → Source → Source) (word : List Generator)
    (receiver : Source → Result) : Set Result :=
  outcomes entering observed (receiver ∘ Millennium.Chronology.transportWord transport word)

/-- The same productive generators expressed through a declared source equivalence. -/
def rebaseTransport {Source Target Generator : Type*} (rebase : Source ≃ Target)
    (transport : Generator → Source → Source) (generator : Generator) : Target → Target :=
  rebase ∘ transport generator ∘ rebase.symm

/-- Rebase transports the complete compatible future family through every admitted ordered
history. All source, observation and generator maps travel together. -/
theorem historyOutcomes_rebase {Source Target Observation Generator Result : Type*}
    (rebase : Source ≃ Target) (entering : Source → Observation)
    (observed : Set.range entering) (transport : Generator → Source → Source)
    (word : List Generator) (receiver : Source → Result) :
    historyOutcomes (entering ∘ rebase.symm) (rebaseObservation rebase entering observed)
      (rebaseTransport rebase transport) word (receiver ∘ rebase.symm) =
      historyOutcomes entering observed transport word receiver := by
  have natural := Millennium.Chronology.generatorEquivarianceExtendsToEveryTransportWord
    (rebaseTransport rebase transport) transport rebase.symm
    (by intros; simp [rebaseTransport]) word
  have hfunction :
      (receiver ∘ rebase.symm) ∘
          Millennium.Chronology.transportWord (rebaseTransport rebase transport) word =
        (receiver ∘ Millennium.Chronology.transportWord transport word) ∘ rebase.symm := by
    funext target
    exact congrArg receiver (natural target)
  unfold historyOutcomes
  rw [hfunction, outcomes_rebase]

end Soma.Holonics.Transport.ReceiverPotential

section Audit
open Soma.Holonics.Transport.ReceiverPotential
#print axioms mem_outcomes_iff
#print axioms outcomes_nonempty
#print axioms outcomes_map
#print axioms outcomes_singleton_of_factor
#print axioms additional_observation_refines
#print axioms outcomes_rebase
#print axioms bounded_outcomes_transport
#print axioms bounded_outcomes_suffice
#print axioms compatible_outcomes_pairwise_bound
#print axioms future_observations_converge
#print axioms historyOutcomes_rebase
end Audit
