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
excited; every receiver outside it is insufficiency.  A productive return must carry a faithful
local section lift on the family; a manifestation carries none.

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

/-! ## The productive return carries a faithful lift on the family -/

universe uSource uCode uNative uCold uInsufficiency

/-- A Soulkiller return: a dismantling return whose productive lane is a faithful local section
lift.  A manifestation — a copied realization with no lift — has no productive lane of this type
and does not inhabit it. -/
structure ExcitationFoundedReturn
    (Source : Type uSource) (Code : Type uCode) (Native : Type uNative)
    (ColdWitness : Type uCold) (Insufficiency : Type uInsufficiency)
    [AddCommGroup Native] where
  returned :
    Soma.Holonics.Computation.HolonicIntelligence.DismantlingReturn
      (Soma.Holonics.Computation.NativeMorphologyVariant.FaithfulLocalSectionLift
        Source Code Native Generator Receiver Face)
      ColdWitness Insufficiency

namespace ExcitationFoundedReturn

variable {Source : Type uSource} {Code : Type uCode} {Native : Type uNative}
  {ColdWitness : Type uCold} {Insufficiency : Type uInsufficiency} [AddCommGroup Native]
  (soulkiller : ExcitationFoundedReturn (Generator := Generator) (Receiver := Receiver)
    (Face := Face) Source Code Native ColdWitness Insufficiency)

/-- The productive lane descends every ordered generator word exactly. -/
theorem productive_everyGeneratorWordExact (word : List Generator) (source : Source) :
    soulkiller.returned.productive.history.present.quotient
        (transportWord soulkiller.returned.productive.history.sourceTransport word source) =
      transportWord soulkiller.returned.productive.history.quotientTransport word
        (soulkiller.returned.productive.history.present.quotient source) :=
  soulkiller.returned.productive.everyGeneratorWordExact word source

/-- Cold ancestry cannot change what the productive lane admits: inherited from the boundary. -/
theorem admitted_replaceColdWitness {Admitted : Type*}
    (admission : Soma.Holonics.Computation.HolonicIntelligence.ProductiveAdmission
      (Soma.Holonics.Computation.NativeMorphologyVariant.FaithfulLocalSectionLift
        Source Code Native Generator Receiver Face) Admitted)
    (witness : ColdWitness) :
    (soulkiller.returned.replaceColdWitness witness).admitted admission =
      soulkiller.returned.admitted admission :=
  Soma.Holonics.Computation.HolonicIntelligence.DismantlingReturn.admitted_replaceColdWitness
    admission soulkiller.returned witness

end ExcitationFoundedReturn

/-! ## Control: equal magnitudes, different cones -/

namespace Control

/-- Two sites, integer carriers.  Generator `false` conducts site 0 to site 0; generator `true`
conducts site 1 to site 0.  The receiver reads site 0. -/
def ecology : FiniteLocalCurrentEcology (Fin 2) ℤ Unit Bool Unit ℤ where
  localCurrent _ generator state target source :=
    if target = 0 ∧ source = (if generator then 1 else 0) then state source else 0
  reaction _ _ _ current := current
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

/-- The same presented magnitudes have different cones under different histories: no magnitude
ranking of the presented state determines the cone.  `{0}` is a cone under `[false]` and `{1}` a
cone under `[true]`. -/
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

end Control

end Soma.Holonics.Computation.HolonicExcitationFoundedQuotient

#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.nativeEq_iff_signatureEq
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.loadBearing_mem_of_isCone
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.DeclaredFamily.withdraw_insufficiency_unchanged
#print axioms Soma.Holonics.Computation.HolonicExcitationFoundedQuotient.Control.cone_false
