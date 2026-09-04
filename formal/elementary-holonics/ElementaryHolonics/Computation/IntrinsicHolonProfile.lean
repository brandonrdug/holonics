import ElementaryHolonics.Foundation.Holon
import Mathlib.Tactic

/-!
# Intrinsic profiles for native holons

A native holon is classified by the caused relations it carries.  Source model names, tensor
paths, codec labels, and construction-campaign names are deliberately absent.  Dimension faces
are indexed by their role so that equal displayed natural numbers do not identify topological,
carrier, receiver, reconstruction, or apparatus dimensions.
-/

namespace Soma.Holonics.Computation.HolonicIntelligence

/-- Distinct dimension species carried by an intrinsic holon profile. -/
inductive DimensionKind where
  | topologicalDegree
  | incidenceRank
  | incidenceNullity
  | cycleRank
  | carrierRank
  | exteriorDegree
  | representationRank
  | generatorExtent
  | receiverExtent
  | reconstructionExtent
  | scaleExtent
  | apparatusWork
  deriving DecidableEq, Repr

/-- One situated dimension face.  The index is load-bearing and prevents silent identification. -/
structure Dimension (kind : DimensionKind) where
  value : ℕ
  deriving DecidableEq, Repr

/-- The non-conflated finite dimension faces currently required by the framework. -/
structure IntrinsicHolonDimensions where
  topologicalDegree : Dimension .topologicalDegree
  incidenceRank : Dimension .incidenceRank
  incidenceNullity : Dimension .incidenceNullity
  cycleRank : Dimension .cycleRank
  carrierRank : Dimension .carrierRank
  exteriorDegree : Dimension .exteriorDegree
  representationRank : Dimension .representationRank
  generatorExtent : Dimension .generatorExtent
  receiverExtent : Dimension .receiverExtent
  reconstructionExtent : Dimension .reconstructionExtent
  scaleExtent : Dimension .scaleExtent
  apparatusWork : Dimension .apparatusWork
  deriving DecidableEq, Repr

/-- Equal displayed coordinates remain two separately typed dimension faces. -/
def equalCoordinateDimensionControl (coordinate : ℕ) :
    Dimension .topologicalDegree × Dimension .carrierRank :=
  (⟨coordinate⟩, ⟨coordinate⟩)

@[simp] theorem equalCoordinateDimensionControl_values (coordinate : ℕ) :
    (equalCoordinateDimensionControl coordinate).1.value = coordinate ∧
      (equalCoordinateDimensionControl coordinate).2.value = coordinate := by
  exact ⟨rfl, rfl⟩

universe uOccurrence uBoundary uIncidence uCarrier uTransport uConstitutive uChronology
  uReceiver uMorphology uReconstruction uOpen

/--
The intrinsic, architecture-neutral profile of one situated holon occurrence.

Every facet is already an owner-local type.  This profile joins those owners without flattening
them into names, scalar counts, or one universal dimension.
-/
structure IntrinsicHolonProfile
    (Occurrence : Type uOccurrence)
    (Boundary : Type uBoundary) (Incidence : Type uIncidence)
    (Carrier : Type uCarrier) (Transport : Type uTransport)
    (Constitutive : Type uConstitutive) (Chronology : Type uChronology)
    (Receiver : Type uReceiver) (Morphology : Type uMorphology)
    (Reconstruction : Type uReconstruction) (OpenObligation : Type uOpen) where
  occurrence : Occurrence
  dimensions : IntrinsicHolonDimensions
  boundary : Boundary
  incidence : Incidence
  carrier : Carrier
  transport : Transport
  constitutive : Constitutive
  chronology : Chronology
  receiver : Receiver
  morphology : Morphology
  reconstruction : Reconstruction
  openObligations : List OpenObligation

universe uContactOccurrence uCurrent uSite

/--
A contact schedule is an exterior chart over current-indexed incidence.  Fixed and dynamically
founded contacts share one type; neither becomes the native ontology merely by being scheduled.
-/
structure ContactScheduleChart
    (Occurrence : Type uContactOccurrence) (Current : Type uCurrent) (Site : Type uSite) where
  contacts : Occurrence → Current → Site → Site → Prop

namespace ContactScheduleChart

variable {Occurrence : Type uContactOccurrence} {Current : Type uCurrent} {Site : Type uSite}
  (chart : ContactScheduleChart Occurrence Current Site)

/-- A fixed contact chart is independent of the contemporary current. -/
def IsFixed : Prop :=
  ∃ relation : Occurrence → Site → Site → Prop,
    ∀ occurrence current source target,
      chart.contacts occurrence current source target = relation occurrence source target

/-- A current-founded chart has one addressed contact whose incidence changes with current. -/
def IsCurrentFounded : Prop :=
  ∃ left right occurrence source target,
    chart.contacts occurrence left source target ≠
      chart.contacts occurrence right source target

/-- One current-visible contact change is an exact obstruction to a fixed schedule. -/
theorem currentFounded_not_fixed (founded : chart.IsCurrentFounded) : ¬ chart.IsFixed := by
  rintro ⟨relation, fixed⟩
  obtain ⟨left, right, occurrence, source, target, separates⟩ := founded
  apply separates
  rw [fixed occurrence left source target, fixed occurrence right source target]

end ContactScheduleChart

section Audit

#print axioms equalCoordinateDimensionControl_values
#print axioms ContactScheduleChart.currentFounded_not_fixed

end Audit

end Soma.Holonics.Computation.HolonicIntelligence
