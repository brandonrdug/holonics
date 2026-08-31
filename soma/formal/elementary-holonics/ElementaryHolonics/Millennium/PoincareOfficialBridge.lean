import ElementaryHolonics.Millennium.PoincareConjecture

/-!
# The Perelman finish line for the Poincaré theorem

**[definition]** This file leaves the existing Poincaré terminal proposition unchanged and
separates two construction targets: build a Ricci-flow-with-surgery trace carrying the metric,
curvature, entropy, noncollapsing, canonical-neighbourhood, local-finiteness, and extinction data;
then prove the topological reconstruction theorem from such a trace.

**[open]** The current Mathlib manifold library has no Ricci-flow or surgery owner.

**[definition]** The trace below is a typed finish-line interface and does not admit the
repository's finite rational `Ricci.lean` fixture as an instance without a separately founded
transport.

**[proved-derived; formal-checked]** The closing theorem returns literally the existing
`ThePoincareConjecture` proposition and stores no homeomorphism in the analytic trace.
-/

noncomputable section

namespace Soma.Holonics.Millennium.PoincareOfficialBridge

open Set
open Soma.Holonics.Millennium.PoincareConjecture

universe u

/-- [definition] The two-sphere which appears as the cross-section of a surgery neck. -/
abbrev SphereTwo : Set (EuclideanSpace ℝ (Fin 3)) :=
  Metric.sphere 0 1

/-- [project-postulate] One topology-bearing surgery event.  The cut locus is an actual subspace
homeomorphic to `S²`; the retained and discarded regions are explicit populations of the source
before-region, not unnamed changes to a scalar time trace. -/
structure SurgeryEvent (M : Type u) [TopologicalSpace M] where
  time : ℝ
  time_nonneg : 0 ≤ time
  beforeRegion : Set M
  neckSphere : Set M
  retainedRegion : Set M
  discardedRegion : Set M
  neckHomeomorph : Nonempty (neckSphere ≃ₜ SphereTwo)
  neck_subset_before : neckSphere ⊆ beforeRegion
  retained_subset_before : retainedRegion ⊆ beforeRegion
  discarded_subset_before : discardedRegion ⊆ beforeRegion
  retained_disjoint_neck : Disjoint retainedRegion neckSphere
  retained_disjoint_discarded : Disjoint retainedRegion discardedRegion
  neck_disjoint_discarded : Disjoint neckSphere discardedRegion
  reconstructsBefore :
    beforeRegion = retainedRegion ∪ neckSphere ∪ discardedRegion

/-- [definition] The time receiver of a typed surgery-event population. -/
def surgeryEventTimes {M : Type u} [TopologicalSpace M]
    (events : ℕ → Option (SurgeryEvent M)) : Set ℝ :=
  {t | ∃ (n : ℕ) (event : SurgeryEvent M), events n = some event ∧ event.time = t}

/-- [project-postulate] A typed Perelman analytic trace on one topological three-manifold.  Tensor
values are retained in three-dimensional chart coordinates until Mathlib supplies an intrinsic
Ricci-flow owner; the topology-agreement field prevents the distance family from floating free of
the source manifold. -/
structure RicciFlowSurgeryCertificate (M : Type u) [TopologicalSpace M] where
  regularTime : Set ℝ
  initialRegular : 0 ∈ regularTime
  distance : ℝ → M → M → ℝ
  distance_nonneg : ∀ {t}, t ∈ regularTime → ∀ x y, 0 ≤ distance t x y
  distance_self : ∀ {t}, t ∈ regularTime → ∀ x, distance t x x = 0
  distance_separates : ∀ {t}, t ∈ regularTime → ∀ {x y},
    distance t x y = 0 → x = y
  distance_symm : ∀ {t}, t ∈ regularTime → ∀ x y,
    distance t x y = distance t y x
  distance_triangle : ∀ {t}, t ∈ regularTime → ∀ x y z,
    distance t x z ≤ distance t x y + distance t y z
  inducesSourceTopology : ∀ {t}, t ∈ regularTime → ∀ U : Set M,
    IsOpen U ↔
      ∀ x ∈ U, ∃ epsilon : ℝ, 0 < epsilon ∧
        ∀ y, distance t x y < epsilon → y ∈ U
  metricTimeDerivative : ℝ → M → EuclideanThree → EuclideanThree → ℝ
  ricciTensor : ℝ → M → EuclideanThree → EuclideanThree → ℝ
  ricciEquation : ∀ {t}, t ∈ regularTime → ∀ x v w,
    metricTimeDerivative t x v w = -2 * ricciTensor t x v w
  scalarCurvature : ℝ → M → ℝ
  perelmanEntropy : ℝ → ℝ
  entropyMonotone : ∀ {s t}, s ∈ regularTime → t ∈ regularTime →
    s ≤ t → perelmanEntropy s ≤ perelmanEntropy t
  reducedVolume : ℝ → ℝ
  reducedVolume_nonneg : ∀ {t}, t ∈ regularTime → 0 ≤ reducedVolume t
  reducedVolume_antitone : ∀ {s t}, s ∈ regularTime → t ∈ regularTime →
    s ≤ t → reducedVolume t ≤ reducedVolume s
  surgeryEvent : ℕ → Option (SurgeryEvent M)
  survivingRegion : ℕ → Set M
  survivingRegion_initial : survivingRegion 0 = Set.univ
  eventReadsCurrentRegion : ∀ {n : ℕ} {event : SurgeryEvent M},
    surgeryEvent n = some event → event.beforeRegion = survivingRegion n
  survivingRegion_afterEvent : ∀ {n : ℕ} {event : SurgeryEvent M},
    surgeryEvent n = some event → survivingRegion (n + 1) = event.retainedRegion
  survivingRegion_withoutEvent : ∀ {n : ℕ},
    surgeryEvent n = none → survivingRegion (n + 1) = survivingRegion n
  eventsChronological : ∀ {m n : ℕ} {first second : SurgeryEvent M},
    surgeryEvent m = some first → surgeryEvent n = some second →
      m < n → first.time < second.time
  discardedNeverReturns : ∀ {n : ℕ} {event : SurgeryEvent M},
    surgeryEvent n = some event → ∀ m, n < m →
      Disjoint (survivingRegion m) event.discardedRegion
  surgeryOccursOnBoundary : surgeryEventTimes surgeryEvent ⊆ closure regularTime
  surgeriesLocallyFinite : ∀ T : ℝ,
    (surgeryEventTimes surgeryEvent ∩ Icc 0 T).Finite
  localVolume : ℝ → M → ℝ → ℝ
  noncollapseConstant : ℝ
  noncollapseConstant_pos : 0 < noncollapseConstant
  noLocalCollapse : ∀ {t}, t ∈ regularTime → ∀ x r,
    0 < r → scalarCurvature t x ≤ 1 / r ^ 2 →
      noncollapseConstant * r ^ 3 ≤ localVolume t x r
  canonicalNeighborhoodScale : ℝ
  canonicalNeighborhoodScale_pos : 0 < canonicalNeighborhoodScale
  canonicalNeighborhoodError : ℕ → ℝ
  canonicalNeighborhoodComplete : ∀ epsilon : ℝ, 0 < epsilon →
    ∃ N : ℕ, ∀ n, N ≤ n → canonicalNeighborhoodError n < epsilon
  highCurvatureHasCanonicalNeighborhood : ∀ {t}, t ∈ regularTime → ∀ x,
    canonicalNeighborhoodScale ≤ scalarCurvature t x →
      ∃ n : ℕ, canonicalNeighborhoodError n < 1
  extinctionTime : ℝ
  extinctionTime_pos : 0 < extinctionTime
  finiteExtinction : regularTime ⊆ Iio extinctionTime

/-- [project-postulate] The geometric construction obligation for every source manifold in the
exact Poincaré quantifier family. -/
def HasPerelmanConstruction : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (RicciFlowSurgeryCertificate M)

/-- [project-postulate] The source-specific reconstruction theorem: finite extinction of an
admitted Perelman trace, with all retained surgery and noncollapsing testimony, forces the source
manifold to be the three-sphere.  This is separate from constructing the analytic trace. -/
def PerelmanReconstructionLaw : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M],
      RicciFlowSurgeryCertificate M → Nonempty (M ≃ₜ SphereThree)

/-- [project-postulate] The complete Poincaré finish line, split at the analytic/topological
boundary.  Neither field is the terminal theorem itself. -/
structure PerelmanFinishLine : Prop where
  construct : HasPerelmanConstruction.{u}
  reconstruct : PerelmanReconstructionLaw.{u}

/-- [proved-derived; formal-checked] A completed Perelman construction and reconstruction law
returns the exact existing topological Poincaré proposition. -/
theorem thePoincareConjecture_of_finishLine (finish : PerelmanFinishLine.{u}) :
    ThePoincareConjecture.{u} := by
  intro M _ _ _ _ _
  obtain ⟨trace⟩ := finish.construct M
  exact finish.reconstruct M trace

section Audit

#print axioms thePoincareConjecture_of_finishLine

end Audit

end Soma.Holonics.Millennium.PoincareOfficialBridge
