import Holonics.Foundation.CausalRelevance

/-! [agent-inferred] This existing law block has an independent consumer.
Its canonical namespace and every statement/proof are preserved exactly;
the aggregate owner imports it once. Import factoring excludes unrelated
constitutions/witnesses at the fixed one-core, 17-second, 2^32-byte RSS gate. -/

noncomputable section

namespace Holonics.Foundation.Standing

open Holonics
open Holonics.Foundation.Chronology
open Holonics.Foundation.CausalRelevance.NonLinear

/-! ## 1. Standing is the retained residue of passages -/

/-- [definition] **The complete admitted future observation of a present occurrence.** `ρ` ranges
over the declared receivers and `w` over the finite ordered histories; the face returned is what
that receiver reads after that history. This is the plan's `Pot_{G,R}(x)` written as a function,
so that *equal potential* is literally equality of two of these. -/
def causalSignature {Generator Receiver Source Face : Type*}
    (observe : Receiver → Source → Face) (transport : Generator → Source → Source)
    (source : Source) : Receiver × List Generator → Face :=
  fun request => observe request.1 (transportWord transport request.2 source)

/-- [proved-derived; formal-checked] Equal causal signature and `futureAgreement` are one
statement. The owner of the relation is `Foundation/CausalRelevance.lean`; this is the function
face of it. -/
theorem causalSignature_eq_iff_futureAgreement {Generator Receiver Source Face : Type*}
    (observe : Receiver → Source → Face) (transport : Generator → Source → Source)
    (left right : Source) :
    causalSignature observe transport left = causalSignature observe transport right ↔
      futureAgreement observe transport left right := by
  constructor
  · intro h receiver word
    exact congrFun h (receiver, word)
  · intro h
    funext request
    exact h request.1 request.2

/-- [definition] **A standing law.** `retain` is the quotient a lineage's passages leave behind and
`reopen` is the factor through which an admitted future observation is read off it. The single
obligation `sufficient` is the whole content of *"standing is sufficient for the admitted
future"*; nothing requires `retain` to be injective, and nothing requires the passage history to
be recoverable from it. -/
structure StandingLaw (Generator Receiver Source Retained Face : Type*) where
  /-- The admitted source transports. -/
  transport : Generator → Source → Source
  /-- The declared present receivers. -/
  observe : Receiver → Source → Face
  /-- The retained residue of the passages: the standing. -/
  retain : Source → Retained
  /-- The factor that reads one admitted future observation off the standing alone. -/
  reopen : Receiver → List Generator → Retained → Face
  /-- The obligation: every admitted future observation factors through the standing. -/
  sufficient : ∀ receiver word source,
    reopen receiver word (retain source) =
      observe receiver (transportWord transport word source)

namespace StandingLaw

variable {Generator Receiver Source Retained Face : Type*}

/-- [proved-derived; formal-checked] Equal standing forces every admitted future face to agree.
This is `Foundation/ReceiverHistoryCompression.lean::quotientEqForcesEverySuccessorFace` for a
retention that need not commute with the generators on the quotient. -/
theorem futureAgreement_of_retain_eq (L : StandingLaw Generator Receiver Source Retained Face)
    {left right : Source} (h : L.retain left = L.retain right) :
    futureAgreement L.observe L.transport left right := by
  intro receiver word
  rw [← L.sufficient receiver word left, ← L.sufficient receiver word right, h]

/-- [proved-derived; formal-checked] Hence equal standing forces equal causal signature. -/
theorem causalSignature_eq_of_retain_eq
    (L : StandingLaw Generator Receiver Source Retained Face)
    {left right : Source} (h : L.retain left = L.retain right) :
    causalSignature L.observe L.transport left = causalSignature L.observe L.transport right :=
  (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr (L.futureAgreement_of_retain_eq h)

/-- [proved-derived; formal-checked] A separating admitted future observation refutes the proposed
standing. The contrapositive of the law above, returned as a refusal rather than a failure. -/
theorem separating_future_refutes_the_standing
    (L : StandingLaw Generator Receiver Source Retained Face)
    {left right : Source} (receiver : Receiver) (word : List Generator)
    (separates :
      L.observe receiver (transportWord L.transport word left) ≠
        L.observe receiver (transportWord L.transport word right)) :
    L.retain left ≠ L.retain right := by
  intro h
  exact separates (L.futureAgreement_of_retain_eq h receiver word)

end StandingLaw

/-- [definition] **The canonical standing: the admitted future itself.** It retains the whole
causal signature and reopens by evaluation. Every other lawful standing is a coarsening of it. -/
def canonicalStanding {Generator Receiver Source Face : Type*}
    (observe : Receiver → Source → Face) (transport : Generator → Source → Source) :
    StandingLaw Generator Receiver Source (Receiver × List Generator → Face) Face where
  transport := transport
  observe := observe
  retain := causalSignature observe transport
  reopen := fun receiver word signature => signature (receiver, word)
  sufficient := fun _ _ _ => rfl

/-- [proved-derived; formal-checked] **Standing may be any quotient through which every admitted
future observation factors — and no other.**

AGENTS.md: *"Causal origin does not prescribe an event archive. Retain dependencies, conditions,
phase, relevant pending cuts and source distinctions in a representation sufficient for the
admitted receivers and continuation."* This is that clause as an equivalence: a retention map
carries a lawful `StandingLaw` exactly when it refines the causal signature. The history is not
recoverable, the source is not recoverable, and neither is owed.

The reopening is built classically on the image of `retain`; off that image it returns an
arbitrary face, which is why `Nonempty Face` is carried. -/
theorem standingLaw_exists_iff_future_factors
    {Generator Receiver Source Retained Face : Type*} [Nonempty Face]
    (observe : Receiver → Source → Face) (transport : Generator → Source → Source)
    (retain : Source → Retained) :
    (∃ L : StandingLaw Generator Receiver Source Retained Face,
        L.transport = transport ∧ L.observe = observe ∧ L.retain = retain) ↔
      ∀ left right, retain left = retain right →
        causalSignature observe transport left = causalSignature observe transport right := by
  classical
  constructor
  · rintro ⟨L, htransport, hobserve, hretain⟩ left right h
    subst htransport; subst hobserve; subst hretain
    exact L.causalSignature_eq_of_retain_eq h
  · intro factors
    refine ⟨{
      transport := transport
      observe := observe
      retain := retain
      reopen := fun receiver word standing =>
        if h : ∃ source, retain source = standing then
          observe receiver (transportWord transport word h.choose)
        else Classical.arbitrary Face
      sufficient := ?_ }, rfl, rfl, rfl⟩
    intro receiver word source
    have hexists : ∃ candidate, retain candidate = retain source := ⟨source, rfl⟩
    rw [dif_pos hexists]
    have hchosen : retain hexists.choose = retain source := hexists.choose_spec
    exact congrFun (factors _ _ hchosen) (receiver, word)

/-- [proved-derived; formal-checked] **`statistical_sufficiency_gives_standing`.** A statistic `T`
through which every admitted future face factors (`observe ρ x = face ρ (T x)`), and through which
every admitted transport descends (`T (g x) = ḡ (T x)`), is a standing: the lawful `StandingLaw`
retains `T` and reopens `(ρ, w)` by reading `face ρ` after the descended word `w̄`
(`Chronology.generatorEquivarianceExtendsToEveryTransportWord`). This is the `←` direction of
`standingLaw_exists_iff_future_factors` with its reopening made explicit, so it needs neither a
choice nor an inhabited face type. Sufficiency for a declared statistical family certifies a
standing only through these two hypotheses: a later contact that `T` does not factor, or a
transport that does not descend, refutes it (`StandingLaw.separating_future_refutes_the_standing`).
The finite candidate family's posterior is the statistical instance
(`NavigatorInference.sufficient_statistic_is_standing`). -/
theorem statistical_sufficiency_gives_standing
    {Generator Receiver Source Statistic Face : Type*}
    (observe : Receiver → Source → Face) (transport : Generator → Source → Source)
    (statistic : Source → Statistic) (face : Receiver → Statistic → Face)
    (descend : Generator → Statistic → Statistic)
    (factors : ∀ receiver source, observe receiver source = face receiver (statistic source))
    (descends : ∀ generator source,
      statistic (transport generator source) = descend generator (statistic source)) :
    ∃ L : StandingLaw Generator Receiver Source Statistic Face,
      L.transport = transport ∧ L.observe = observe ∧ L.retain = statistic ∧
        ∀ receiver word standing,
          L.reopen receiver word standing = face receiver (transportWord descend word standing) := by
  refine ⟨{
    transport := transport
    observe := observe
    retain := statistic
    reopen := fun receiver word standing => face receiver (transportWord descend word standing)
    sufficient := fun receiver word source => ?_ }, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  rw [factors, generatorEquivarianceExtendsToEveryTransportWord transport descend statistic
    descends word source]


end Holonics.Foundation.Standing
