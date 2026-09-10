import ElementaryHolonics.Computation.HolonicNeuralEcology
import ElementaryHolonics.Computation.NativeMorphologyVariant
import ElementaryHolonics.Computation.HolonicIntelligenceLifecycle
import ElementaryHolonics.Millennium.ReceiverHistory
import Mathlib.Tactic

/-!
# The excitation-founded quotient

Soulkiller is founded by excitation, not copied from weights.  Over one finite local-current
ecology with rested morphology, a declared family names the occurrences presented, the receivers
that read them, and the ordered histories they are driven through.  The causal signature of an
occurrence is its complete receiver face after every declared history; two occurrences are one
native state exactly when their signatures agree.  The cone of an occurrence at a receiver is the
population of sites whose withdrawal changes the face — founded by intervention on the excited
current, never by a magnitude — and the extent of a lift is the union of the cones the family
excited; every receiver outside it is insufficiency.

Two laws are stated about the cone and they are not the same law.  `IsCone` is universal over
every disjoint population: it is monotone upward (`isCone_mono`), so a superset of a cone is a
cone and unions of cones compose (`isCone_union`), and no finite population of withdrawals
discharges it.  `IsConeUnder` quantifies instead over a declared population of withdrawals, in the
idiom every other obligation in this tree uses; a declared family founds `FoundedCone` under
exactly those withdrawals, and that cone is sound with no further hypothesis
(`isConeUnder_foundedCone`).  `Control.empty_not_isCone` exhibits the gap between the two: with no
declared withdrawal the empty set is `IsConeUnder` while it is not `IsCone`.

A productive return carries a faithful local section lift whose source is the family's occurrence
type and whose native identity is exactly the family's signature quotient.  That obligation is
necessary and **not** sufficient: `identityLift` inhabits `FaithfulLocalSectionLift`, and
`manifestationReturn` inhabits `ExcitationFoundedReturn` over any family that separates its own
occurrences, so this type does not refuse a manifestation.  What is owed and open is the decoder
cost `Millennium/LineageCompression.lean` already names — "a codec compression additionally owes
an exterior presentation and decoder cost".

Formal owners composed: `FiniteLocalCurrentEcology` (the excited body),
`Foundation.Receiver.Compression` (the family quotient), `CompleteReceiverHistoryQuotient` (the
all-history quotient, with its signature theorems inherited), `FaithfulLocalSectionLift` and
`DismantlingReturn` (the return).
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicExcitationFoundedQuotient

open scoped Classical
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.LineageCompression
open Soma.Holonics.Millennium.ReceiverHistory
open Soma.Holonics.Computation.HolonicNeuralEcology

universe uS uC uM uG uR uF uO

variable {Site : Type uS} {Carrier : Type uC} {Morphology : Type uM}
  {Generator : Type uG} {Receiver : Type uR} {Face : Type uF}
  [Fintype Site] [AddCommMonoid Carrier]
  (N : FiniteLocalCurrentEcology Site Carrier Morphology Generator Receiver Face)

/-! ## The causal signature of an excited state -/

/-- The complete receiver face of one presented state after one ordered history at one rest. -/
def signature (morphology : Morphology) (state : Site → Carrier)
    (receiver : Receiver) (history : List Generator) : Face :=
  N.observe receiver (N.inferWord morphology history state)

@[simp] theorem signature_nil (morphology : Morphology) (state : Site → Carrier)
    (receiver : Receiver) :
    signature N morphology state receiver [] = N.observe receiver state := rfl

/-- Driving the state by one generator is reading the signature at the extended history. -/
theorem signature_step (morphology : Morphology) (state : Site → Carrier)
    (generator : Generator) (receiver : Receiver) (history : List Generator) :
    signature N morphology (N.step morphology generator state) receiver history =
      signature N morphology state receiver (history ++ [generator]) := by
  unfold signature
  rw [N.inferWord_append]
  rfl

/-! ## The all-history quotient is a complete receiver-history quotient -/

/-- Two states are one native state when every receiver agrees after every ordered history. -/
def allHistorySetoid (morphology : Morphology) : Setoid (Site → Carrier) where
  r left right := ∀ receiver history,
    signature N morphology left receiver history = signature N morphology right receiver history
  iseqv := by
    refine ⟨fun _ _ _ => rfl, fun h receiver history => (h receiver history).symm,
      fun h₁ h₂ receiver history => (h₁ receiver history).trans (h₂ receiver history)⟩

/-- The native state of one presented state. -/
abbrev NativeState (morphology : Morphology) : Type _ :=
  Quotient (allHistorySetoid N morphology)

/-- The quotient transport by one generator is well defined because the signature extends. -/
def nativeStep (morphology : Morphology) (generator : Generator) :
    NativeState N morphology → NativeState N morphology :=
  Quotient.map (N.step morphology generator) (by
    intro left right h receiver history
    rw [signature_step, signature_step]
    exact h receiver (history ++ [generator]))

/-- The excitation-founded quotient of every ordered history, as a complete receiver-history
quotient: its signature theorems are inherited, not re-proved. -/
def allHistoryQuotient (morphology : Morphology) :
    CompleteReceiverHistoryQuotient Generator Receiver (Site → Carrier)
      (NativeState N morphology) Face where
  present :=
    { quotient := Quotient.mk (allHistorySetoid N morphology)
      receiver := N.observe
      factor := fun receiver =>
        Quotient.lift (fun state => N.observe receiver state) (by
          intro left right h
          exact h receiver [])
      exact := by
        intro receiver state
        rfl }
  sourceTransport := N.step morphology
  quotientTransport := nativeStep N morphology
  generatorExact := by
    intro generator state
    rfl
  complete := by
    intro left right h
    exact Quotient.sound (fun receiver history => h receiver history)

/-- Inherited: native equality is exactly equality of the complete causal signatures. -/
theorem nativeEq_iff_signatureEq (morphology : Morphology) (left right : Site → Carrier) :
    (allHistoryQuotient N morphology).present.quotient left =
        (allHistoryQuotient N morphology).present.quotient right ↔
      (allHistoryQuotient N morphology).causalSignature left =
        (allHistoryQuotient N morphology).causalSignature right :=
  (allHistoryQuotient N morphology).quotientEq_iff_causalSignatureEq

/-- Inherited: unequal native states return an explicit separating receiver and history. -/
theorem nativeNe_returnsSeparatingHistory (morphology : Morphology)
    (left right : Site → Carrier)
    (h : (allHistoryQuotient N morphology).present.quotient left ≠
      (allHistoryQuotient N morphology).present.quotient right) :
    ∃ receiver history,
      signature N morphology left receiver history ≠
        signature N morphology right receiver history :=
  (allHistoryQuotient N morphology).quotientNe_returnsSeparatingReceiverHistory h

/-! ## A declared family and its quotient -/

/-- A declared family: the occurrences presented, the receivers reading them, and the ordered
histories they are driven through.  An application declares it; nothing here selects answers. -/
structure DeclaredFamily (Occurrence : Type uO) where
  present : Occurrence → (Site → Carrier)
  receivers : Set Receiver
  histories : Set (List Generator)

variable {Occurrence : Type uO}

namespace DeclaredFamily

variable (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
  (Generator := Generator) (Receiver := Receiver) Occurrence)

/-- The declared receiver/history pairs the family exposes its occurrences to. -/
def Exposure : Type _ :=
  { pair : Receiver × List Generator // pair.1 ∈ family.receivers ∧ pair.2 ∈ family.histories }

/-- Two occurrences are identified when every declared exposure returns equal faces. -/
def Identified (morphology : Morphology) (left right : Occurrence) : Prop :=
  ∀ exposure : family.Exposure,
    signature N morphology (family.present left) exposure.1.1 exposure.1.2 =
      signature N morphology (family.present right) exposure.1.1 exposure.1.2

/-- Identification over the declared family is an equivalence. -/
def familySetoid (morphology : Morphology) : Setoid Occurrence where
  r := family.Identified N morphology
  iseqv := by
    refine ⟨fun _ _ => rfl, fun h exposure => (h exposure).symm,
      fun h₁ h₂ exposure => (h₁ exposure).trans (h₂ exposure)⟩

/-- The class of an occurrence: the recurring structure the family revealed. -/
abbrev Class (morphology : Morphology) : Type _ :=
  Quotient (family.familySetoid N morphology)

/-- The family quotient is exact for every declared exposure: identified occurrences return equal
faces at every declared receiver after every declared history. -/
def familyCompression (morphology : Morphology) :
    Soma.Holonics.Compression family.Exposure Occurrence (family.Class N morphology) Face where
  quotient := Quotient.mk (family.familySetoid N morphology)
  receiver := fun exposure occurrence =>
    signature N morphology (family.present occurrence) exposure.1.1 exposure.1.2
  factor := fun exposure =>
    Quotient.lift
      (fun occurrence =>
        signature N morphology (family.present occurrence) exposure.1.1 exposure.1.2)
      (fun _ _ h => h exposure)
  exact := by
    intro exposure occurrence
    rfl

/-- Identified occurrences have equal faces on every declared exposure. -/
theorem identified_faces_eq (morphology : Morphology) {left right : Occurrence}
    (h : family.Identified N morphology left right) (exposure : family.Exposure) :
    signature N morphology (family.present left) exposure.1.1 exposure.1.2 =
      signature N morphology (family.present right) exposure.1.1 exposure.1.2 :=
  h exposure

/-- One separating declared exposure reopens a proposed identification. -/
theorem separatingExposure_reopens (morphology : Morphology) {left right : Occurrence}
    (exposure : family.Exposure)
    (separates :
      signature N morphology (family.present left) exposure.1.1 exposure.1.2 ≠
        signature N morphology (family.present right) exposure.1.1 exposure.1.2) :
    ¬ family.Identified N morphology left right :=
  fun h => separates (h exposure)

/-- Identification over a declared family is coarser than native equality: the all-history
quotient identifies only what every exposure identifies. -/
theorem identified_of_nativeEq (morphology : Morphology) {left right : Occurrence}
    (h : (allHistoryQuotient N morphology).present.quotient (family.present left) =
      (allHistoryQuotient N morphology).present.quotient (family.present right)) :
    family.Identified N morphology left right := by
  intro exposure
  exact Quotient.exact h exposure.1.1 exposure.1.2

/-! ### Saturation: an enlargement that reopens no class -/

/-- One declared family enlarges another when it presents the same occurrences and its declared
receivers and histories include the first's.  Nothing here counts classes, exposures, or
occurrences: the enlargement is an inclusion of declarations, not a size. -/
structure Enlarges (small large : DeclaredFamily (Site := Site) (Carrier := Carrier)
    (Generator := Generator) (Receiver := Receiver) Occurrence) : Prop where
  /-- The two families present the same occurrences. -/
  present : large.present = small.present
  /-- Every receiver the small family declares the large family declares. -/
  receivers : small.receivers ⊆ large.receivers
  /-- Every history the small family declares the large family declares. -/
  histories : small.histories ⊆ large.histories

/-- Identification is antitone in the declaration: what a larger family identifies, the smaller
family identifies too, because every exposure of the smaller is an exposure of the larger.  This
direction is unconditional — enlarging a family can only separate. -/
theorem identified_of_identified_enlargement
    {small large : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence}
    (enlarges : Enlarges small large) (morphology : Morphology) {left right : Occurrence}
    (identified : large.Identified N morphology left right) :
    small.Identified N morphology left right := by
  intro exposure
  have carried := identified
    ⟨exposure.1, enlarges.receivers exposure.2.1, enlarges.histories exposure.2.2⟩
  rw [enlarges.present] at carried
  exact carried

/-- A family is saturated inside an enlargement when the enlargement reopens no class: every pair
the small family identified the large family still identifies.  The converse always holds
(`identified_of_identified_enlargement`), so saturation is exactly the statement that the two
declarations carry one and the same identification.  No count of classes, exposures, or sites
appears; a scalar score is not this property. -/
def Saturated (small large : DeclaredFamily (Site := Site) (Carrier := Carrier)
    (Generator := Generator) (Receiver := Receiver) Occurrence) (morphology : Morphology) : Prop :=
  ∀ left right : Occurrence,
    small.Identified N morphology left right → large.Identified N morphology left right

/-- Under saturation the two families identify exactly the same pairs. -/
theorem saturated_iff_identified
    {small large : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence}
    (enlarges : Enlarges small large) {morphology : Morphology}
    (saturated : Saturated N small large morphology) (left right : Occurrence) :
    small.Identified N morphology left right ↔ large.Identified N morphology left right :=
  ⟨saturated left right, identified_of_identified_enlargement N enlarges morphology⟩

/-- Saturation preserves the equivalence: the two family setoids are the same relation, so no
class is reopened and none is merged. -/
theorem saturated_familySetoid_eq
    {small large : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence}
    (enlarges : Enlarges small large) {morphology : Morphology}
    (saturated : Saturated N small large morphology) :
    (small.familySetoid N morphology).r = (large.familySetoid N morphology).r := by
  funext left right
  exact propext (saturated_iff_identified N enlarges saturated left right)

end DeclaredFamily

/-! ## The cone, founded by intervention -/

/-- Withdraw a population of sites from a presented state: the intervention. -/
def withdraw (population : Set Site) (state : Site → Carrier) : Site → Carrier :=
  fun site => if site ∈ population then 0 else state site

omit [Fintype Site] in
@[simp] theorem withdraw_empty (state : Site → Carrier) : withdraw (∅ : Set Site) state = state := by
  funext site
  simp [withdraw]

/-- A cone at one receiver and history: withdrawing any population disjoint from it leaves the
face unchanged.  Soundness of the cone is exactly the outside-unchanged law. -/
def IsCone (morphology : Morphology) (state : Site → Carrier) (receiver : Receiver)
    (history : List Generator) (cone : Set Site) : Prop :=
  ∀ population : Set Site, Disjoint population cone →
    signature N morphology (withdraw population state) receiver history =
      signature N morphology state receiver history

/-- The complete site population is always a cone. -/
theorem isCone_univ (morphology : Morphology) (state : Site → Carrier) (receiver : Receiver)
    (history : List Generator) :
    IsCone N morphology state receiver history Set.univ := by
  intro population disjoint
  have empty : population = ∅ := by
    rw [Set.disjoint_univ] at disjoint
    exact disjoint
  rw [empty, withdraw_empty]

/-- A cone stays a cone when enlarged: `IsCone` is monotone upward.  A population disjoint from
the larger cone is disjoint from the smaller one, so the smaller cone's law already answers it.
This is why `isCone_univ` is degenerate, why a least cone need not exist (the predicate is closed
under union but not under intersection), and why a cone claim carries content only through a
minimality statement this file does not make. -/
theorem isCone_mono (morphology : Morphology) (state : Site → Carrier) (receiver : Receiver)
    (history : List Generator) {cone enlarged : Set Site} (sub : cone ⊆ enlarged)
    (isCone : IsCone N morphology state receiver history cone) :
    IsCone N morphology state receiver history enlarged :=
  fun population disjoint =>
    isCone population (Set.disjoint_of_subset_right sub disjoint)

set_option linter.unusedVariables false in
/-- The union of two cones at the same state, receiver, and history is a cone.  The right-hand
hypothesis is deliberately unused: `isCone_mono` already enlarges a cone by an arbitrary
population, so one side alone carries the union.  The two-sided form is stated because
composition of cones is what the campaign uses, and because it makes the consequence explicit —
a measured union that fails to be a cone refutes its *members*, never the union operation. -/
theorem isCone_union (morphology : Morphology) (state : Site → Carrier) (receiver : Receiver)
    (history : List Generator) {left right : Set Site}
    (isLeft : IsCone N morphology state receiver history left)
    (isRight : IsCone N morphology state receiver history right) :
    IsCone N morphology state receiver history (left ∪ right) :=
  isCone_mono N morphology state receiver history Set.subset_union_left isLeft

/-- A site is load-bearing when its own withdrawal changes the face. -/
def LoadBearing (morphology : Morphology) (state : Site → Carrier) (receiver : Receiver)
    (history : List Generator) (site : Site) : Prop :=
  signature N morphology (withdraw {site} state) receiver history ≠
    signature N morphology state receiver history

/-- Every cone contains every load-bearing site: a cone that omitted one would have to leave the
face unchanged under that site's withdrawal. -/
theorem loadBearing_mem_of_isCone (morphology : Morphology) (state : Site → Carrier)
    (receiver : Receiver) (history : List Generator) {cone : Set Site}
    (isCone : IsCone N morphology state receiver history cone) {site : Site}
    (bearing : LoadBearing N morphology state receiver history site) :
    site ∈ cone := by
  by_contra outside
  apply bearing
  apply isCone
  exact Set.disjoint_singleton_left.mpr outside

/-! ### The declared-withdrawal cone

`IsCone` quantifies over every population of sites disjoint from the cone.  That is the one place
this line quantifies over an unbounded lattice, and it is the one obligation a finite intervention
cannot discharge: finitely many sufficient withdrawals are not a universal.  Everywhere else this
tree quantifies obligations over a declared finite family — `declaredProbes` in
`NativeTransportScaffold`, `family.receivers` and `family.histories` above.  The cone is restated
in that idiom below: the family declares the withdrawals it exposes its occurrences to, and the
cone is what those withdrawals found. -/

/-- A cone sound under a declared population of withdrawals: withdrawing any *declared* population
disjoint from the cone leaves the face unchanged.  This is the obligation an intervention actually
discharges, one declared withdrawal at a time. -/
def IsConeUnder (declared : Set (Set Site)) (morphology : Morphology) (state : Site → Carrier)
    (receiver : Receiver) (history : List Generator) (cone : Set Site) : Prop :=
  ∀ population ∈ declared, Disjoint population cone →
    signature N morphology (withdraw population state) receiver history =
      signature N morphology state receiver history

/-- The universal cone is sound under every declaration.  The converse fails: see
`Control.empty_not_isCone`. -/
theorem isConeUnder_of_isCone (declared : Set (Set Site)) (morphology : Morphology)
    (state : Site → Carrier) (receiver : Receiver) (history : List Generator) {cone : Set Site}
    (isCone : IsCone N morphology state receiver history cone) :
    IsConeUnder N declared morphology state receiver history cone :=
  fun population _ disjoint => isCone population disjoint

/-- The declared cone is monotone upward in the cone, exactly as `IsCone` is. -/
theorem isConeUnder_mono (declared : Set (Set Site)) (morphology : Morphology)
    (state : Site → Carrier) (receiver : Receiver) (history : List Generator)
    {cone enlarged : Set Site} (sub : cone ⊆ enlarged)
    (isCone : IsConeUnder N declared morphology state receiver history cone) :
    IsConeUnder N declared morphology state receiver history enlarged :=
  fun population mem disjoint =>
    isCone population mem (Set.disjoint_of_subset_right sub disjoint)

/-- The declared cone is antitone in the declaration: soundness under more declared withdrawals is
soundness under fewer.  Enlarging the declared withdrawals is therefore what reopens a cone, and a
reading of a cone means nothing without the declaration it was taken under. -/
theorem isConeUnder_mono_declared {declared enlarged : Set (Set Site)} (sub : declared ⊆ enlarged)
    (morphology : Morphology) (state : Site → Carrier) (receiver : Receiver)
    (history : List Generator) {cone : Set Site}
    (isCone : IsConeUnder N enlarged morphology state receiver history cone) :
    IsConeUnder N declared morphology state receiver history cone :=
  fun population mem disjoint => isCone population (sub mem) disjoint

/-- The declared withdrawals that changed the face. -/
def ChangingWithdrawals (declared : Set (Set Site)) (morphology : Morphology)
    (state : Site → Carrier) (receiver : Receiver) (history : List Generator) : Set (Set Site) :=
  {population ∈ declared |
    signature N morphology (withdraw population state) receiver history ≠
      signature N morphology state receiver history}

/-- The cone a declared family of withdrawals founds: the union of exactly those declared
populations whose withdrawal changes the face. -/
def FoundedCone (declared : Set (Set Site)) (morphology : Morphology) (state : Site → Carrier)
    (receiver : Receiver) (history : List Generator) : Set Site :=
  ⋃₀ ChangingWithdrawals N declared morphology state receiver history

/-- The founded cone is sound under the withdrawals that founded it, with **no** hypothesis at all
— in particular the declared populations need not be pairwise disjoint.  A declared population
that changes the face is contained in the founded cone, so if it is also disjoint from that cone
it is empty, and the empty withdrawal changes nothing (`withdraw_empty`).  The two cases are
therefore the same case, and the law holds outright.

This is the exact strength a card intervention carries, and all of it: soundness *under the
declared withdrawals*, never the `IsCone` universal. -/
theorem isConeUnder_foundedCone (declared : Set (Set Site)) (morphology : Morphology)
    (state : Site → Carrier) (receiver : Receiver) (history : List Generator) :
    IsConeUnder N declared morphology state receiver history
      (FoundedCone N declared morphology state receiver history) := by
  intro population mem disjoint
  by_contra changes
  have inChanging :
      population ∈ ChangingWithdrawals N declared morphology state receiver history :=
    ⟨mem, changes⟩
  have sub : population ⊆ FoundedCone N declared morphology state receiver history :=
    Set.subset_sUnion_of_mem inChanging
  have empty : population = ∅ := by
    ext site
    simp only [Set.mem_empty_iff_false, iff_false]
    intro inPopulation
    exact (Set.disjoint_left.mp disjoint) inPopulation (sub inPopulation)
  rw [empty, withdraw_empty] at changes
  exact changes rfl

/-- A declaration with no withdrawal founds no cone. -/
@[simp] theorem foundedCone_emptyDeclared (morphology : Morphology) (state : Site → Carrier)
    (receiver : Receiver) (history : List Generator) :
    FoundedCone N (∅ : Set (Set Site)) morphology state receiver history = ∅ := by
  simp [FoundedCone, ChangingWithdrawals]

/-- Every declared withdrawal that changes the face meets every cone sound under that declaration.
This is the declared analogue of `loadBearing_mem_of_isCone`, and it is the whole of what a joint
withdrawal establishes: it places load *inside* a cone, it does not locate that load at a site. -/
theorem changingWithdrawal_meets_isConeUnder (declared : Set (Set Site)) (morphology : Morphology)
    (state : Site → Carrier) (receiver : Receiver) (history : List Generator) {cone : Set Site}
    (isCone : IsConeUnder N declared morphology state receiver history cone)
    {population : Set Site} (mem : population ∈ declared)
    (changes : signature N morphology (withdraw population state) receiver history ≠
      signature N morphology state receiver history) :
    ¬ Disjoint population cone :=
  fun disjoint => changes (isCone population mem disjoint)

/-- The extent of a family's lift: the union of the cones the family excited. -/
def DeclaredFamily.extent (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
    (Generator := Generator) (Receiver := Receiver) Occurrence)
    (cone : Occurrence → family.Exposure → Set Site) : Set Site :=
  ⋃ occurrence, ⋃ exposure, cone occurrence exposure

/-- The insufficiency of a family's lift: what no declared exposure made load-bearing. -/
def DeclaredFamily.insufficiency (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
    (Generator := Generator) (Receiver := Receiver) Occurrence)
    (cone : Occurrence → family.Exposure → Set Site) : Set Site :=
  (family.extent cone)ᶜ

/-- Withdrawing any population inside the insufficiency leaves every declared face of every
occurrence unchanged: nothing the family sees lives there.  "You can only lift what you infer." -/
theorem DeclaredFamily.withdraw_insufficiency_unchanged (morphology : Morphology)
    (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence)
    (cone : Occurrence → family.Exposure → Set Site)
    (sound : ∀ occurrence exposure,
      IsCone N morphology (family.present occurrence) exposure.1.1 exposure.1.2
        (cone occurrence exposure))
    (population : Set Site) (inside : population ⊆ family.insufficiency cone)
    (occurrence : Occurrence) (exposure : family.Exposure) :
    signature N morphology (withdraw population (family.present occurrence))
        exposure.1.1 exposure.1.2 =
      signature N morphology (family.present occurrence) exposure.1.1 exposure.1.2 := by
  apply sound occurrence exposure
  rw [Set.disjoint_left]
  intro site inPopulation inCone
  have inExtent : site ∈ family.extent cone := by
    exact Set.mem_iUnion.mpr ⟨occurrence, Set.mem_iUnion.mpr ⟨exposure, inCone⟩⟩
  exact (inside inPopulation) inExtent

/-- The declared-withdrawal form of the same law, and the one an intervention can actually
discharge: withdrawing a *declared* population inside the insufficiency leaves every declared face
of every occurrence unchanged.  "You can only lift what you infer", bounded by what the family
declared it would try. -/
theorem DeclaredFamily.withdraw_declared_insufficiency_unchanged (declared : Set (Set Site))
    (morphology : Morphology)
    (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence)
    (cone : Occurrence → family.Exposure → Set Site)
    (sound : ∀ occurrence exposure,
      IsConeUnder N declared morphology (family.present occurrence) exposure.1.1 exposure.1.2
        (cone occurrence exposure))
    (population : Set Site) (mem : population ∈ declared)
    (inside : population ⊆ family.insufficiency cone)
    (occurrence : Occurrence) (exposure : family.Exposure) :
    signature N morphology (withdraw population (family.present occurrence))
        exposure.1.1 exposure.1.2 =
      signature N morphology (family.present occurrence) exposure.1.1 exposure.1.2 := by
  apply sound occurrence exposure population mem
  rw [Set.disjoint_left]
  intro site inPopulation inCone
  have inExtent : site ∈ family.extent cone :=
    Set.mem_iUnion.mpr ⟨occurrence, Set.mem_iUnion.mpr ⟨exposure, inCone⟩⟩
  exact (inside inPopulation) inExtent

/-- A family that declares no withdrawal founds an empty extent: it lifts nothing. -/
theorem DeclaredFamily.extent_foundedCone_emptyDeclared (morphology : Morphology)
    (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence) :
    family.extent (fun occurrence exposure =>
        FoundedCone N (∅ : Set (Set Site)) morphology (family.present occurrence)
          exposure.1.1 exposure.1.2) = (∅ : Set Site) := by
  simp [DeclaredFamily.extent]

/-- …and its insufficiency is the complete site population.  Every site is outside what the family
excited, because the family excited nothing.  Note that the soundness obligation
`IsConeUnder ∅ …` is discharged vacuously, so an empty declaration inhabits every return type
below while founding no cone at all: soundness under a declaration is not evidence of a lift. -/
theorem DeclaredFamily.insufficiency_foundedCone_emptyDeclared (morphology : Morphology)
    (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence) :
    family.insufficiency (fun occurrence exposure =>
        FoundedCone N (∅ : Set (Set Site)) morphology (family.present occurrence)
          exposure.1.1 exposure.1.2) = (Set.univ : Set Site) := by
  rw [DeclaredFamily.insufficiency, DeclaredFamily.extent_foundedCone_emptyDeclared,
    Set.compl_empty]

/-! ## The productive return carries a faithful lift on the family -/

universe uCode uNative uCold uInsufficiency

/-- The identity lift: `Source = Code = Native`, nothing encoded, nothing stored elsewhere,
residual zero, quotient the identity, incidence carried across unchanged.  Every field of
`FaithfulLocalSectionLift` is discharged by `rfl`.

It exists to exhibit, rather than hide, what that type does not refuse.  A manifestation — the
resident foreign operator copied with its names removed — inhabits `FaithfulLocalSectionLift`:
nothing bounds `residual`, nothing forbids `quotient = id`, nothing requires `Code` to be smaller
than `Source`.  The obligation that would refuse it is the decoder cost the tree already names in
`Millennium/LineageCompression.lean` — "a codec compression additionally owes an exterior
presentation and decoder cost" — and it is open. -/
def identityLift {Native : Type uNative} [AddCommGroup Native]
    (transport : Generator → Native → Native) (read : Receiver → Native → Face)
    (incidence : Native → Native → Prop) :
    Soma.Holonics.Computation.NativeMorphologyVariant.FaithfulLocalSectionLift
      Native Native Native Generator Receiver Face where
  foreign :=
    { encode := id
      sourceValue := id
      storedValue := id
      residual := fun _ => 0
      reconstructs := fun source => (add_zero source).symm }
  history :=
    { present :=
        { quotient := id
          receiver := read
          factor := read
          exact := fun _ _ => rfl }
      sourceTransport := transport
      quotientTransport := transport
      generatorExact := fun _ _ => rfl }
  quotientIsStored := fun _ => rfl
  sourceIncidence := incidence
  nativeIncidence := incidence
  incidenceExact := fun _ _ => Iff.rfl

/-- The identity lift collapses nothing: its quotient is the identity.  Inhabiting
`FaithfulLocalSectionLift` therefore proves no compression, no condensation, and no rebase. -/
theorem identityLift_quotient_eq_id {Native : Type uNative} [AddCommGroup Native]
    (transport : Generator → Native → Native) (read : Receiver → Native → Face)
    (incidence : Native → Native → Prop) :
    (identityLift transport read incidence).history.present.quotient = id := rfl

/-- A Soulkiller return **on one declared family**.

The productive lane is a `FaithfulLocalSectionLift` whose `Source` is the family's `Occurrence`
type, and `quotientIsFamilyQuotient` says its native identity is exactly the family's signature
quotient — the lane is the class ecology of the declared family and nothing else
(`classes_embed_in_native`, `lane_quotient_eq_iff_family_quotient_eq`).  The return also carries
the withdrawals the family declared, the cone each exposure founded, and the soundness of those
cones under exactly those declared withdrawals: `IsConeUnder`, never the universal `IsCone`,
because a finite intervention discharges the first and cannot discharge the second.

What the tie does refuse: an identity lane cannot inhabit this type over a family that identifies
two distinct occurrences, since `quotientIsFamilyQuotient` would then force those occurrences
equal.  What it does not refuse: `manifestationReturn` inhabits it from `identityLift`, an empty
declaration of withdrawals and the empty cone assignment, over any family that separates its own
occurrences.  Inhabiting this type is therefore necessary and **not** sufficient for a founded
return; the obligation that would close the gap is the decoder cost named above, and it is
open. -/
structure ExcitationFoundedReturn
    (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence)
    (morphology : Morphology) (declared : Set (Set Site))
    (Code : Type uCode) (Native : Type uNative)
    (ColdWitness : Type uCold) (Insufficiency : Type uInsufficiency)
    [AddCommGroup Native] where
  returned :
    Soma.Holonics.Computation.HolonicIntelligence.DismantlingReturn
      (Soma.Holonics.Computation.NativeMorphologyVariant.FaithfulLocalSectionLift
        Occurrence Code Native Generator Receiver Face)
      ColdWitness Insufficiency
  /-- The cone each occurrence founded at each declared exposure. -/
  cone : Occurrence → family.Exposure → Set Site
  /-- Every such cone is sound under exactly the withdrawals the family declared. -/
  coneSound : ∀ occurrence exposure,
    IsConeUnder N declared morphology (family.present occurrence)
      exposure.1.1 exposure.1.2 (cone occurrence exposure)
  /-- The productive lane's native identity is the family's signature quotient. -/
  quotientIsFamilyQuotient : ∀ left right : Occurrence,
    returned.productive.history.present.quotient left =
        returned.productive.history.present.quotient right ↔
      family.Identified N morphology left right

namespace ExcitationFoundedReturn

variable {Code : Type uCode} {Native : Type uNative}
  {ColdWitness : Type uCold} {Insufficiency : Type uInsufficiency} [AddCommGroup Native]
  {family : DeclaredFamily (Site := Site) (Carrier := Carrier)
    (Generator := Generator) (Receiver := Receiver) Occurrence}
  {morphology : Morphology} {declared : Set (Set Site)}
  (soulkiller : ExcitationFoundedReturn N family morphology declared
    Code Native ColdWitness Insufficiency)

/-- The productive lane descends every ordered generator word exactly. -/
theorem productive_everyGeneratorWordExact (word : List Generator) (occurrence : Occurrence) :
    soulkiller.returned.productive.history.present.quotient
        (transportWord soulkiller.returned.productive.history.sourceTransport word occurrence) =
      transportWord soulkiller.returned.productive.history.quotientTransport word
        (soulkiller.returned.productive.history.present.quotient occurrence) :=
  soulkiller.returned.productive.everyGeneratorWordExact word occurrence

/-- Cold ancestry cannot change what the productive lane admits: inherited from the boundary. -/
theorem admitted_replaceColdWitness {Admitted : Type*}
    (admission : Soma.Holonics.Computation.HolonicIntelligence.ProductiveAdmission
      (Soma.Holonics.Computation.NativeMorphologyVariant.FaithfulLocalSectionLift
        Occurrence Code Native Generator Receiver Face) Admitted)
    (witness : ColdWitness) :
    (soulkiller.returned.replaceColdWitness witness).admitted admission =
      soulkiller.returned.admitted admission :=
  Soma.Holonics.Computation.HolonicIntelligence.DismantlingReturn.admitted_replaceColdWitness
    admission soulkiller.returned witness

/-- The lane's native identity, stated against the family's own `Compression`: two occurrences
have the same native presentation exactly when `familyCompression` sends them to one class. -/
theorem lane_quotient_eq_iff_family_quotient_eq (left right : Occurrence) :
    soulkiller.returned.productive.history.present.quotient left =
        soulkiller.returned.productive.history.present.quotient right ↔
      (family.familyCompression N morphology).quotient left =
        (family.familyCompression N morphology).quotient right := by
  rw [soulkiller.quotientIsFamilyQuotient]
  exact ⟨fun identified => Quotient.sound identified, fun equal => Quotient.exact equal⟩

/-- The family's classes embed in the lane's native presentation and the embedding commutes with
the class map.  This is the exact sense in which the productive lane *is* the class ecology of the
declared family: no class is merged (injectivity) and no occurrence is presented twice. -/
theorem classes_embed_in_native :
    ∃ embed : family.Class N morphology → Native,
      Function.Injective embed ∧
        ∀ occurrence : Occurrence,
          embed (Quotient.mk (family.familySetoid N morphology) occurrence) =
            soulkiller.returned.productive.history.present.quotient occurrence := by
  refine ⟨Quotient.lift
      (fun occurrence => soulkiller.returned.productive.history.present.quotient occurrence)
      (fun left right identified =>
        (soulkiller.quotientIsFamilyQuotient left right).mpr identified),
    ?_, fun _ => rfl⟩
  intro left right equal
  obtain ⟨leftOccurrence, rfl⟩ := Quotient.exists_rep left
  obtain ⟨rightOccurrence, rfl⟩ := Quotient.exists_rep right
  exact Quotient.sound
    ((soulkiller.quotientIsFamilyQuotient leftOccurrence rightOccurrence).mp equal)

/-- The extent of this return: the union of the cones its declared withdrawals founded. -/
def extent : Set Site := family.extent soulkiller.cone

/-- The insufficiency of this return: every site outside that extent. -/
def insufficiency : Set Site := family.insufficiency soulkiller.cone

/-- Withdrawing a declared population inside this return's insufficiency leaves every declared
face of every occurrence unchanged, at exactly the bound the declaration carries. -/
theorem withdraw_insufficiency_unchanged (population : Set Site) (mem : population ∈ declared)
    (inside : population ⊆ soulkiller.insufficiency)
    (occurrence : Occurrence) (exposure : family.Exposure) :
    signature N morphology (withdraw population (family.present occurrence))
        exposure.1.1 exposure.1.2 =
      signature N morphology (family.present occurrence) exposure.1.1 exposure.1.2 :=
  DeclaredFamily.withdraw_declared_insufficiency_unchanged N declared morphology family
    soulkiller.cone soulkiller.coneSound population mem inside occurrence exposure

end ExcitationFoundedReturn

/-- A manifestation inhabits the return type.

Over any declared family that separates its own occurrences, the identity lift, a declaration of
no withdrawals, and the empty cone assignment discharge every field of `ExcitationFoundedReturn`.
Nothing is excited, no cone is founded, the extent is empty and the insufficiency is the whole
site population (`manifestationReturn_extent_empty`,
`manifestationReturn_insufficiency_univ`).

This replaces the former docstring of this owner, which asserted that "a manifestation — a copied
realization with no lift — has no productive lane of this type and does not inhabit it".  That
assertion was false and was discharged by no theorem.  The exclusion is an open obligation, and
exhibiting its failure here is the honest form of the claim. -/
def manifestationReturn [AddCommGroup Occurrence]
    (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence)
    (morphology : Morphology)
    {ColdWitness : Type uCold} {Insufficiency : Type uInsufficiency}
    (transport : Generator → Occurrence → Occurrence) (read : Receiver → Occurrence → Face)
    (incidence : Occurrence → Occurrence → Prop)
    (coldWitness : ColdWitness) (insufficiency : Insufficiency)
    (separates : ∀ left right : Occurrence,
      family.Identified N morphology left right → left = right) :
    ExcitationFoundedReturn N family morphology (∅ : Set (Set Site))
      Occurrence Occurrence ColdWitness Insufficiency where
  returned :=
    { productive := identityLift transport read incidence
      coldWitness := coldWitness
      insufficiency := insufficiency }
  cone := fun _ _ => ∅
  coneSound := fun _ _ population mem => absurd mem (Set.notMem_empty population)
  quotientIsFamilyQuotient := by
    intro left right
    constructor
    · intro equal
      have same : left = right := equal
      subst same
      exact fun _ => rfl
    · intro identified
      exact separates left right identified

/-- The manifestation return excites nothing: its extent is empty. -/
theorem manifestationReturn_extent_empty [AddCommGroup Occurrence]
    (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence)
    (morphology : Morphology)
    {ColdWitness : Type uCold} {Insufficiency : Type uInsufficiency}
    (transport : Generator → Occurrence → Occurrence) (read : Receiver → Occurrence → Face)
    (incidence : Occurrence → Occurrence → Prop)
    (coldWitness : ColdWitness) (insufficiency : Insufficiency)
    (separates : ∀ left right : Occurrence,
      family.Identified N morphology left right → left = right) :
    (manifestationReturn N family morphology transport read incidence coldWitness insufficiency
      separates).extent = (∅ : Set Site) := by
  simp [ExcitationFoundedReturn.extent, DeclaredFamily.extent, manifestationReturn]

/-- …and its insufficiency is the complete site population. -/
theorem manifestationReturn_insufficiency_univ [AddCommGroup Occurrence]
    (family : DeclaredFamily (Site := Site) (Carrier := Carrier)
      (Generator := Generator) (Receiver := Receiver) Occurrence)
    (morphology : Morphology)
    {ColdWitness : Type uCold} {Insufficiency : Type uInsufficiency}
    (transport : Generator → Occurrence → Occurrence) (read : Receiver → Occurrence → Face)
    (incidence : Occurrence → Occurrence → Prop)
    (coldWitness : ColdWitness) (insufficiency : Insufficiency)
    (separates : ∀ left right : Occurrence,
      family.Identified N morphology left right → left = right) :
    (manifestationReturn N family morphology transport read incidence coldWitness insufficiency
      separates).insufficiency = (Set.univ : Set Site) := by
  rw [ExcitationFoundedReturn.insufficiency, DeclaredFamily.insufficiency]
  rw [show (manifestationReturn N family morphology transport read incidence coldWitness
      insufficiency separates).cone = fun _ _ => (∅ : Set Site) from rfl]
  simp [DeclaredFamily.extent]

/-! ## Control: one presented state, two histories, two different cones

This control uses **one** presented state, not two occurrences.  Its content is that the cone is
not a function of the presented magnitudes: `presented` carries the value `3` at both sites, and
the same state has cone `{0}` under the history `[false]` and cone `{1}` under the history
`[true]`.  A magnitude ranking of the presented state therefore cannot determine a cone.  It says
nothing about two occurrences, and nothing about which cone is minimal. -/

namespace Control

/-- Two sites, integer carriers.  Generator `false` conducts site 0 to site 0; generator `true`
conducts site 1 to site 0.  The receiver reads site 0. -/
def ecology : FiniteLocalCurrentEcology (Fin 2) ℤ Unit Bool Unit ℤ where
  localCurrent _ generator state target source :=
    if target = 0 ∧ source = (if generator then 1 else 0) then state source else 0
  reaction _ _ _ _ current := current
  observe _ state := state 0

/-- The presented state has equal magnitude at both sites. -/
def presented : Fin 2 → ℤ := fun _ => 3

theorem signature_false : signature ecology () presented () [false] = 3 := by
  decide

theorem signature_true : signature ecology () presented () [true] = 3 := by
  decide

/-- Under the history `[false]`, site 0 is load-bearing and site 1 is not. -/
theorem site0_bearing_under_false : LoadBearing ecology () presented () [false] 0 := by
  simp [LoadBearing, signature, FiniteLocalCurrentEcology.inferWord, transportWord, ecology,
    FiniteLocalCurrentEcology.step, FiniteLocalCurrentEcology.aggregateCurrent, withdraw, presented]

theorem site1_inert_under_false : ¬ LoadBearing ecology () presented () [false] 1 := by
  simp [LoadBearing, signature, FiniteLocalCurrentEcology.inferWord, transportWord, ecology,
    FiniteLocalCurrentEcology.step, FiniteLocalCurrentEcology.aggregateCurrent, withdraw, presented]

/-- Under the history `[true]`, site 1 is load-bearing and site 0 is not. -/
theorem site1_bearing_under_true : LoadBearing ecology () presented () [true] 1 := by
  simp [LoadBearing, signature, FiniteLocalCurrentEcology.inferWord, transportWord, ecology,
    FiniteLocalCurrentEcology.step, FiniteLocalCurrentEcology.aggregateCurrent, withdraw, presented]

theorem site0_inert_under_true : ¬ LoadBearing ecology () presented () [true] 0 := by
  simp [LoadBearing, signature, FiniteLocalCurrentEcology.inferWord, transportWord, ecology,
    FiniteLocalCurrentEcology.step, FiniteLocalCurrentEcology.aggregateCurrent, withdraw, presented]

/-- One presented state whose equal magnitudes have different cones under two declared histories:
no magnitude ranking of the presented state determines the cone.  `{0}` is a cone under `[false]`
and `{1}` a cone under `[true]`.  Both are discharged by exhausting `Set (Fin 2)`, which is
possible here and is exactly what a resident operator's site population forbids. -/
theorem cone_false : IsCone ecology () presented () [false] {0} := by
  intro population disjoint
  have notMem : (0 : Fin 2) ∉ population := Set.disjoint_singleton_right.mp disjoint
  simp [signature, FiniteLocalCurrentEcology.inferWord, transportWord, ecology,
    FiniteLocalCurrentEcology.step, FiniteLocalCurrentEcology.aggregateCurrent, withdraw,
    presented, notMem]

theorem cone_true : IsCone ecology () presented () [true] {1} := by
  intro population disjoint
  have notMem : (1 : Fin 2) ∉ population := Set.disjoint_singleton_right.mp disjoint
  simp [signature, FiniteLocalCurrentEcology.inferWord, transportWord, ecology,
    FiniteLocalCurrentEcology.step, FiniteLocalCurrentEcology.aggregateCurrent, withdraw,
    presented, notMem]

/-- With no declared withdrawal, the empty set is sound: `IsConeUnder ∅` is vacuous. -/
theorem emptyDeclared_isConeUnder_empty :
    IsConeUnder ecology (∅ : Set (Set (Fin 2))) () presented () [false] (∅ : Set (Fin 2)) :=
  fun population mem => absurd mem (Set.notMem_empty population)

/-- …while the empty set is **not** an `IsCone` cone at the same state, receiver, and history,
because site 0 is load-bearing.  The two propositions are therefore different propositions, and
soundness under a declaration is not soundness over every population.  This is the exact gap a
finite intervention falls into when its sufficient withdrawals are graded as a universal. -/
theorem empty_not_isCone :
    ¬ IsCone ecology () presented () [false] (∅ : Set (Fin 2)) := by
  intro isCone
  exact site0_bearing_under_false (isCone {0} (by simp))

end Control

end Soma.Holonics.Computation.HolonicExcitationFoundedQuotient

#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.nativeEq_iff_signatureEq
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.loadBearing_mem_of_isCone
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.DeclaredFamily.withdraw_insufficiency_unchanged
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.Control.cone_false
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.isCone_mono
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.isCone_union
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.isConeUnder_of_isCone
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.isConeUnder_mono
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.isConeUnder_mono_declared
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.isConeUnder_foundedCone
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.foundedCone_emptyDeclared
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.changingWithdrawal_meets_isConeUnder
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.DeclaredFamily.withdraw_declared_insufficiency_unchanged
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.DeclaredFamily.extent_foundedCone_emptyDeclared
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.DeclaredFamily.insufficiency_foundedCone_emptyDeclared
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.DeclaredFamily.identified_of_identified_enlargement
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.DeclaredFamily.saturated_iff_identified
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.DeclaredFamily.saturated_familySetoid_eq
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.identityLift_quotient_eq_id
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.ExcitationFoundedReturn.lane_quotient_eq_iff_family_quotient_eq
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.ExcitationFoundedReturn.classes_embed_in_native
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.ExcitationFoundedReturn.withdraw_insufficiency_unchanged
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.manifestationReturn_extent_empty
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.manifestationReturn_insufficiency_univ
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.Control.emptyDeclared_isConeUnder_empty
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.Control.empty_not_isCone
