import ElementaryHolonics.Computation.ExactForeignWeight
import ElementaryHolonics.Computation.HolonicCultivationCharts
import ElementaryHolonics.Computation.HolonicNeuralEcology
import ElementaryHolonics.Computation.NativeTransportScaffold
import ElementaryHolonics.Millennium.LineageCompression
import Mathlib.Tactic

/-!
# Faithful local lifts, morphology variants, and exact export lenses

This owner is the neutral MVF0 foundation.  It does not make a foreign tensor architecture, file
format, version label, or inference configuration into native topology.  A productive local lift
owes incidence, generator, receiver, and preimage-fibre exactness.  Cultivation is supported
on a returned causal cone.  Variant manifests are derived testimony.  Export is exact only for the
receiver/history family whose conduct round-trips.
-/

noncomputable section

namespace Soma.Holonics.Computation.NativeMorphologyVariant

/-! ## Faithful local section lift -/

/-- One finite local presentation of a foreign section into native transport.

The source and native incidences remain explicit.  Generator and receiver conduct must descend
through `quotient`; merely retaining the exact source codewords does not prove these equations.
-/
structure FaithfulLocalSectionLift
    (Source Code Native Generator Receiver Face : Type*) [AddCommGroup Native] where
  foreign :
    Soma.Holonics.Computation.HolonicIntelligence.ExactForeignWeightPassage Source Code Native
  history :
    Soma.Holonics.Millennium.LineageCompression.ReceiverHistoryCompression
      Generator Receiver Source Native Face
  quotientIsStored : ∀ source,
    history.present.quotient source = foreign.storedValue (foreign.encode source)
  sourceIncidence : Source → Source → Prop
  nativeIncidence : Native → Native → Prop
  incidenceExact : ∀ left right,
    sourceIncidence left right ↔
      nativeIncidence (history.present.quotient left) (history.present.quotient right)

namespace FaithfulLocalSectionLift

variable {Source Code Native Generator Receiver Face : Type*} [AddCommGroup Native]
    (lift : FaithfulLocalSectionLift Source Code Native Generator Receiver Face)

/-- The complete source population collapsed to one native presentation. -/
def preimageFibre (native : Native) : Type _ :=
  lift.history.preimageFibre native

/-- Every source occurrence remains in the fibre of its own presented native state. -/
theorem source_mem_preimageFibre (source : Source) :
    ∃ retained : lift.preimageFibre (lift.history.present.quotient source),
      retained.1 = source :=
  ⟨⟨source, rfl⟩, rfl⟩

/-- Ordered foreign conduct descends through the same local lift for every admitted generator word. -/
theorem everyGeneratorWordExact (word : List Generator) (source : Source) :
    lift.history.present.quotient
        (Soma.Holonics.Millennium.Chronology.transportWord
          lift.history.sourceTransport word source) =
      Soma.Holonics.Millennium.Chronology.transportWord
        lift.history.quotientTransport word (lift.history.present.quotient source) :=
  lift.history.quotientCommutesWithEveryOrderedWord word source

/-- Exact stored-value reconstruction and receiver/history exactness are separate obligations
returned together by a faithful lift. -/
theorem storedValue_and_everyReceiverHistoryExact (source : Source)
    (receiver : Receiver) (word : List Generator) :
    lift.foreign.storedValue (lift.foreign.encode source) + lift.foreign.residual source =
        lift.foreign.sourceValue source ∧
      lift.history.present.receiver receiver
          (Soma.Holonics.Millennium.Chronology.transportWord
            lift.history.sourceTransport word source) =
        lift.history.futureFactor (receiver, word) (lift.history.present.quotient source) := by
  constructor
  · exact lift.foreign.exact_reconstruction source
  · exact (lift.history.allSuccessorHistories.exact (receiver, word) source).symm

end FaithfulLocalSectionLift

/-- A collision exposed by one receiver prevents any receiver-exact descent through the proposed
section projection.  This is the formal obstruction carried by the coarse alternating-sum control. -/
theorem separatingReceiver_obstructs_descent
    {Source Native Receiver Face : Type*}
    (quotient : Source → Native) (sourceObserve : Receiver → Source → Face)
    {left right : Source} (collapsed : quotient left = quotient right)
    (separated : ∃ receiver, sourceObserve receiver left ≠ sourceObserve receiver right) :
    ¬ ∃ nativeObserve : Receiver → Native → Face,
      ∀ receiver source,
        nativeObserve receiver (quotient source) = sourceObserve receiver source := by
  rintro ⟨nativeObserve, exact⟩
  obtain ⟨receiver, separates⟩ := separated
  apply separates
  calc
    sourceObserve receiver left = nativeObserve receiver (quotient left) :=
      (exact receiver left).symm
    _ = nativeObserve receiver (quotient right) := congrArg (nativeObserve receiver) collapsed
    _ = sourceObserve receiver right := exact receiver right

/-! ## Causal-cone cultivation -/

/-- One returned local morphology change with source-detached remount, ablation, and restoration.

`localFace` is the native anatomical face at one site.  `outsideUnchanged` prevents a local return
from silently rewriting inactive morphology.  The conduct receiver may still be global; locality
is exactly the supplied causal cone, not a promise of constant work.
-/
structure LocalCausalConeCultivation
    (Site Morphology LocalFace Difference Delta Probe Face RestIdentity Occurrence : Type*) where
  passage :
    Soma.Holonics.Computation.HolonicIntelligence.CultivationPassage
      Morphology Difference Delta Probe Face RestIdentity Occurrence
  causalCone : Delta → Set Site
  probeSite : Probe → Site
  localFace : Morphology → Site → LocalFace
  outsideUnchanged : ∀ site,
    site ∉ causalCone (passage.causalAdjoint passage.returnedDifference) →
      localFace passage.successor site = localFace passage.predecessor site
  outsideConductUnchanged : ∀ probe,
    probeSite probe ∉ causalCone (passage.causalAdjoint passage.returnedDifference) →
      passage.conduct passage.successor probe = passage.conduct passage.predecessor probe
  restore : Morphology → Morphology
  restorationExact : restore passage.predecessor = passage.successor

namespace LocalCausalConeCultivation

variable {Site Morphology LocalFace Difference Delta Probe Face RestIdentity Occurrence : Type*}
    (cultivation : LocalCausalConeCultivation Site Morphology LocalFace Difference Delta Probe Face
      RestIdentity Occurrence)

theorem everyOutsideSiteUnchanged (site : Site)
    (outside : site ∉ cultivation.causalCone
      (cultivation.passage.causalAdjoint cultivation.passage.returnedDifference)) :
    cultivation.localFace cultivation.passage.successor site =
      cultivation.localFace cultivation.passage.predecessor site :=
  cultivation.outsideUnchanged site outside

theorem change_survives_remount_and_targeted_ablation :
    cultivation.passage.remount
        (cultivation.passage.rest cultivation.passage.successor) =
        cultivation.passage.successor ∧
      cultivation.passage.conduct cultivation.passage.successor
          cultivation.passage.witnessProbe ≠
        cultivation.passage.conduct cultivation.passage.predecessor
          cultivation.passage.witnessProbe ∧
      cultivation.passage.withdraw cultivation.passage.returnedDifference
          cultivation.passage.successor = cultivation.passage.predecessor ∧
      cultivation.restore
          (cultivation.passage.withdraw cultivation.passage.returnedDifference
            cultivation.passage.successor) = cultivation.passage.successor := by
  rw [cultivation.passage.withdrawalExact]
  exact ⟨cultivation.passage.remountExact, cultivation.passage.changedLaterConduct,
    rfl, cultivation.restorationExact⟩

/-- The probe whose later conduct changed must meet the returned causal cone. -/
theorem changedProbe_meets_causalCone :
    cultivation.probeSite cultivation.passage.witnessProbe ∈
      cultivation.causalCone
        (cultivation.passage.causalAdjoint cultivation.passage.returnedDifference) := by
  by_contra outside
  apply cultivation.passage.changedLaterConduct
  exact cultivation.outsideConductUnchanged cultivation.passage.witnessProbe outside

end LocalCausalConeCultivation

/-! ## Descriptive variant and physically separated package testimony -/

/-- Four independent version axes beside anatomy derived from the rested body. -/
structure MorphologyVariantManifest
    (SchemaVersion MorphologyLineage ReceiverCapability Realization Anatomy : Type*) where
  schemaVersion : SchemaVersion
  morphologyLineage : MorphologyLineage
  receiverCapability : ReceiverCapability
  realization : Realization
  anatomy : Anatomy

namespace MorphologyVariantManifest

variable {SchemaVersion MorphologyLineage ReceiverCapability Realization Anatomy : Type*}

/-- Re-encoding or changing apparatus testimony cannot silently change morphology lineage,
receiver capability, or derived anatomy. -/
def reencode
    (manifest : MorphologyVariantManifest SchemaVersion MorphologyLineage ReceiverCapability
      Realization Anatomy)
    (schemaVersion : SchemaVersion) (realization : Realization) :
    MorphologyVariantManifest SchemaVersion MorphologyLineage ReceiverCapability Realization
      Anatomy where
  schemaVersion := schemaVersion
  morphologyLineage := manifest.morphologyLineage
  receiverCapability := manifest.receiverCapability
  realization := realization
  anatomy := manifest.anatomy

@[simp] theorem reencode_capability
    (manifest : MorphologyVariantManifest SchemaVersion MorphologyLineage ReceiverCapability
      Realization Anatomy)
    (schemaVersion : SchemaVersion) (realization : Realization) :
    (manifest.reencode schemaVersion realization).receiverCapability =
      manifest.receiverCapability := rfl

@[simp] theorem reencode_anatomy
    (manifest : MorphologyVariantManifest SchemaVersion MorphologyLineage ReceiverCapability
      Realization Anatomy)
    (schemaVersion : SchemaVersion) (realization : Realization) :
    (manifest.reencode schemaVersion realization).anatomy = manifest.anatomy := rfl

end MorphologyVariantManifest

/-- Exterior package lanes over one hot morphology.  They do not become the runtime topology. -/
structure VariantPackageSeparation
    (Manifest Hot Testimony Evaluation Apparatus Export : Type*) where
  manifest : Manifest
  hot : Hot
  testimony : Testimony
  evaluation : Evaluation
  apparatus : Apparatus
  exports : List Export

namespace VariantPackageSeparation

variable {Manifest Hot Testimony Evaluation Apparatus Export : Type*}

def replaceApparatus
    (package : VariantPackageSeparation Manifest Hot Testimony Evaluation Apparatus Export)
    (apparatus : Apparatus) (exports : List Export) :
    VariantPackageSeparation Manifest Hot Testimony Evaluation Apparatus Export where
  manifest := package.manifest
  hot := package.hot
  testimony := package.testimony
  evaluation := package.evaluation
  apparatus := apparatus
  exports := exports

@[simp] theorem replaceApparatus_hot
    (package : VariantPackageSeparation Manifest Hot Testimony Evaluation Apparatus Export)
    (apparatus : Apparatus) (exports : List Export) :
    (package.replaceApparatus apparatus exports).hot = package.hot := rfl

@[simp] theorem replaceApparatus_testimony
    (package : VariantPackageSeparation Manifest Hot Testimony Evaluation Apparatus Export)
    (apparatus : Apparatus) (exports : List Export) :
    (package.replaceApparatus apparatus exports).testimony = package.testimony := rfl

end VariantPackageSeparation

/-! ## Exact, projected, and refused export lenses -/

/-- An exterior export whose re-imported conduct agrees for every declared query/receiver. -/
structure ExactExportLens (Native Export Query Receiver Face : Type*) where
  present : Native → Export
  importProjection : Export → Native
  nativeConduct : Native → Query → Receiver → Face
  importedConduct : Native → Query → Receiver → Face
  roundTripExact : ∀ native query receiver,
    importedConduct (importProjection (present native)) query receiver =
      nativeConduct native query receiver

namespace ExactExportLens

variable {Native Export Query Receiver Face : Type*}
    (lens : ExactExportLens Native Export Query Receiver Face)

theorem everyDeclaredReceiverHistoryRoundTrips
    (native : Native) (query : Query) (receiver : Receiver) :
    lens.importedConduct (lens.importProjection (lens.present native)) query receiver =
      lens.nativeConduct native query receiver :=
  lens.roundTripExact native query receiver

end ExactExportLens

/-- A projected export retains the exact pair and receiver/history which reopen its quotient. -/
structure ProjectedExportWitness (Native Export Query Receiver Face : Type*) where
  project : Native → Export
  nativeConduct : Native → Query → Receiver → Face
  left : Native
  right : Native
  collapsed : project left = project right
  separatingQuery : Query
  separatingReceiver : Receiver
  separates :
    nativeConduct left separatingQuery separatingReceiver ≠
      nativeConduct right separatingQuery separatingReceiver

namespace ProjectedExportWitness

variable {Native Export Query Receiver Face : Type*}
    (witness : ProjectedExportWitness Native Export Query Receiver Face)

/-- A richer receiver/history separator prevents promotion of a projected export to an exact one. -/
theorem richerReceiver_reopens_export :
    ¬ ∃ exportedConduct : Export → Query → Receiver → Face,
      ∀ native query receiver,
        exportedConduct (witness.project native) query receiver =
          witness.nativeConduct native query receiver := by
  rintro ⟨exportedConduct, exact⟩
  apply witness.separates
  calc
    witness.nativeConduct witness.left witness.separatingQuery witness.separatingReceiver =
        exportedConduct (witness.project witness.left) witness.separatingQuery
          witness.separatingReceiver :=
      (exact witness.left witness.separatingQuery witness.separatingReceiver).symm
    _ = exportedConduct (witness.project witness.right) witness.separatingQuery
          witness.separatingReceiver :=
      congrArg
        (fun exported ↦ exportedConduct exported witness.separatingQuery
          witness.separatingReceiver)
        witness.collapsed
    _ = witness.nativeConduct witness.right witness.separatingQuery
          witness.separatingReceiver :=
      exact witness.right witness.separatingQuery witness.separatingReceiver

end ProjectedExportWitness

inductive ExportDisposition (Exact Projected Refusal : Type*) where
  | exact : Exact → ExportDisposition Exact Projected Refusal
  | projected : Projected → ExportDisposition Exact Projected Refusal
  | refused : Refusal → ExportDisposition Exact Projected Refusal

/-! ## Configuration-indexed evaluation and cross-codec resonance -/

/-- A complete inference configuration.  Its fields are kept distinct so one result cannot be
silently promoted across aperture, receiver, world-return, codec, or apparatus. -/
structure InferenceConfiguration
    (Variant Ingress Occurrence Receiver Continuation WorldReturn Emission Apparatus
      StochasticCurrent : Type*) where
  variant : Variant
  ingress : Ingress
  occurrence : Occurrence
  receiver : Receiver
  continuation : Continuation
  worldReturn : WorldReturn
  emission : Emission
  apparatus : Apparatus
  stochasticCurrent : StochasticCurrent

/-- One claim and the exact configuration at which it was returned. -/
structure InferenceConfigurationClaim (Configuration Result : Type*) where
  evaluate : Configuration → Result
  configuration : Configuration
  result : Result
  exact : result = evaluate configuration

namespace InferenceConfigurationClaim

variable {Configuration Result : Type*}
    (claim : InferenceConfigurationClaim Configuration Result)

/-- If another configuration has a separated result, the current claim proves no equality there. -/
theorem separatedConfiguration_not_proved
    (other : Configuration) (separated : claim.evaluate other ≠ claim.result) :
    claim.result ≠ claim.evaluate other := by
  exact Ne.symm separated

end InferenceConfigurationClaim

/-- Perfect cross-codec resonance is equality over every admitted receiver and successor history,
not equality of one terminal surface. -/
structure CrossCodecResonance
    (Occurrence History Receiver Face : Type*) where
  left : Occurrence
  right : Occurrence
  conduct : Occurrence → History → Receiver → Face
  everyHistoryExact : ∀ history receiver,
    conduct left history receiver = conduct right history receiver

namespace CrossCodecResonance

variable {Occurrence History Receiver Face : Type*}
    (resonance : CrossCodecResonance Occurrence History Receiver Face)

theorem receiverHistoryExact (history : History) (receiver : Receiver) :
    resonance.conduct resonance.left history receiver =
      resonance.conduct resonance.right history receiver :=
  resonance.everyHistoryExact history receiver

end CrossCodecResonance

/-! ## Finite firing controls -/

namespace Control

/-- A one-value projection collapses two source sections which a receiver distinguishes. -/
theorem constantSectionProjection_not_faithful :
    ¬ ∃ nativeObserve : Unit → Unit → Bool,
      ∀ receiver source,
        nativeObserve receiver ((fun _ : Bool ↦ ()) source) = source := by
  apply separatingReceiver_obstructs_descent
    (quotient := fun _ : Bool ↦ ()) (sourceObserve := fun _ source ↦ source)
    (left := false) (right := true)
  · rfl
  · exact ⟨(), by decide⟩

/-- The standing lifecycle owner instantiated by a genuinely later two-site return. -/
def twoSiteCultivationPassage :
    Soma.Holonics.Computation.HolonicIntelligence.CultivationPassage
      (Fin 2 → ℕ) Unit Unit (Fin 2) ℕ Unit (Fin 2) where
  predecessor := fun _ ↦ 0
  emittedOccurrence := 0
  returnedOccurrence := 1
  precedes left right := left ≠ right
  precedesIrreflexive occurrence := by simp
  returnIsLater := by decide
  difference _ _ := ()
  returnedDifference := ()
  returnedDifferenceExact := rfl
  causalAdjoint _ := ()
  applyDelta _ _ := fun site ↦ if site = 0 then 1 else 0
  successor := fun site ↦ if site = 0 then 1 else 0
  successorIsReturn := rfl
  morphologyChanged := by
    intro equality
    have atZero := congrFun equality 0
    simp at atZero
  conduct morphology probe := morphology probe
  witnessProbe := 0
  changedLaterConduct := by simp
  rest _ := ()
  remount _ := fun site ↦ if site = 0 then 1 else 0
  remountExact := rfl
  withdraw _ _ := fun _ ↦ 0
  withdrawalExact := rfl

/-- One exact local return changes site zero and leaves the disjoint site unchanged. -/
def twoSiteLocalCultivation :
    LocalCausalConeCultivation (Fin 2) (Fin 2 → ℕ) ℕ Unit Unit (Fin 2) ℕ Unit
      (Fin 2) where
  passage := twoSiteCultivationPassage
  causalCone _ := {0}
  probeSite := _root_.id
  localFace morphology site := morphology site
  outsideUnchanged site outside := by
    simp only [Set.mem_singleton_iff] at outside
    change (if site = 0 then 1 else 0) = 0
    simp [outside]
  outsideConductUnchanged probe outside := by
    have separated : probe ≠ 0 := by
      simpa only [Set.mem_singleton_iff, id_eq] using outside
    change (if probe = 0 then 1 else 0) = 0
    simp [separated]
  restore _ := fun site ↦ if site = 0 then 1 else 0
  restorationExact := rfl

theorem twoSiteLocalCultivation_preserves_outside :
    twoSiteLocalCultivation.localFace twoSiteLocalCultivation.passage.successor 1 =
      twoSiteLocalCultivation.localFace twoSiteLocalCultivation.passage.predecessor 1 := by
  apply twoSiteLocalCultivation.everyOutsideSiteUnchanged 1
  change (1 : Fin 2) ≠ 0
  decide

theorem twoSiteLocalCultivation_changedProbe_meets_cone :
    twoSiteLocalCultivation.probeSite twoSiteLocalCultivation.passage.witnessProbe ∈
      twoSiteLocalCultivation.causalCone
        (twoSiteLocalCultivation.passage.causalAdjoint
          twoSiteLocalCultivation.passage.returnedDifference) :=
  twoSiteLocalCultivation.changedProbe_meets_causalCone

/-- Re-encoding a manifest changes neither demonstrated capability nor derived anatomy. -/
def manifestControl : MorphologyVariantManifest Nat Nat Bool Unit (Nat × Nat) where
  schemaVersion := 1
  morphologyLineage := 7
  receiverCapability := true
  realization := ()
  anatomy := (3, 2)

theorem manifest_version_is_not_capability :
    (manifestControl.reencode 99 ()).receiverCapability = manifestControl.receiverCapability ∧
      (manifestControl.reencode 99 ()).anatomy = manifestControl.anatomy := by
  exact ⟨rfl, rfl⟩

/-- The identity exterior presentation is exact for every declared query/receiver. -/
def identityExportControl : ExactExportLens ℕ ℕ Unit Unit ℕ where
  present := _root_.id
  importProjection := _root_.id
  nativeConduct native _ _ := native
  importedConduct native _ _ := native
  roundTripExact _ _ _ := rfl

theorem identityExportControl_roundTrips (native : ℕ) :
    identityExportControl.importedConduct
        (identityExportControl.importProjection (identityExportControl.present native)) () () =
      identityExportControl.nativeConduct native () () :=
  identityExportControl.everyDeclaredReceiverHistoryRoundTrips native () ()

/-- Boolean parity is a projected export: a richer Boolean receiver reopens its two-member fibre. -/
def projectedControl : ProjectedExportWitness Bool Unit Unit Unit Bool where
  project _ := ()
  nativeConduct native _ _ := native
  left := false
  right := true
  collapsed := rfl
  separatingQuery := ()
  separatingReceiver := ()
  separates := by decide

theorem projectedControl_reopens :
    ¬ ∃ exportedConduct : Unit → Unit → Unit → Bool,
      ∀ native query receiver,
        exportedConduct (projectedControl.project native) query receiver =
          projectedControl.nativeConduct native query receiver :=
  projectedControl.richerReceiver_reopens_export

/-- A result at `false` does not assert the separated result at configuration `true`. -/
def configurationControl : InferenceConfigurationClaim Bool Bool where
  evaluate := _root_.id
  configuration := false
  result := false
  exact := rfl

theorem one_configuration_does_not_prove_another :
    configurationControl.result ≠ configurationControl.evaluate true := by
  exact configurationControl.separatedConfiguration_not_proved true (by decide)

end Control

section Audit

#print axioms FaithfulLocalSectionLift.everyGeneratorWordExact
#print axioms FaithfulLocalSectionLift.storedValue_and_everyReceiverHistoryExact
#print axioms separatingReceiver_obstructs_descent
#print axioms LocalCausalConeCultivation.everyOutsideSiteUnchanged
#print axioms LocalCausalConeCultivation.change_survives_remount_and_targeted_ablation
#print axioms LocalCausalConeCultivation.changedProbe_meets_causalCone
#print axioms MorphologyVariantManifest.reencode_capability
#print axioms VariantPackageSeparation.replaceApparatus_hot
#print axioms ExactExportLens.everyDeclaredReceiverHistoryRoundTrips
#print axioms ProjectedExportWitness.richerReceiver_reopens_export
#print axioms InferenceConfigurationClaim.separatedConfiguration_not_proved
#print axioms CrossCodecResonance.receiverHistoryExact
#print axioms Control.constantSectionProjection_not_faithful
#print axioms Control.twoSiteLocalCultivation_preserves_outside
#print axioms Control.twoSiteLocalCultivation_changedProbe_meets_cone
#print axioms Control.manifest_version_is_not_capability
#print axioms Control.identityExportControl_roundTrips
#print axioms Control.projectedControl_reopens
#print axioms Control.one_configuration_does_not_prove_another

end Audit

end Soma.Holonics.Computation.NativeMorphologyVariant
