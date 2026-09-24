import Holonics.Foundation.ContinuingTower
import Holonics.Foundation.CausalChord

/-!
# Capability, local chart and receiver atlas: an embedding is an atlas of placements

[definition] This file deposits item **C6** of
`docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md`: `Capability`, `LocalChart` with
transition maps on overlaps, and `ReceiverAtlas`.

The thesis it formalizes: **an embedding is an atlas of placements whose content is its transition
maps, not one global vector.** The three statements that make it exact are all below —
`ChartCocycle.placementEquiv` recovers the classical case where every transition is invertible and
the cocycle holds, `theEmbeddingIsNotOneVector` exhibits an atlas with every chart inhabited and no
coherent placement at all, and `AtlasIndistinguishable` says what one atlas can and cannot separate.

## What is *supplied* and what is *conferred*

[definition] A metric, a smooth structure, analytic data or an identified scaling family is
**supplied** to an object, never conferred by its geometry. `docs/canon/TABLET_THE_MANIFOLD.md` §16
states the classical form — every geometry is a *reduction of the structure group*, so `GL(n)` is no
structure at all and `O(n)` is a supplied metric — and `docs/HOLON.md` states the project form: "A
gradient, metric, mass, distribution, tensor rank or reversible decoder is additional mathematical
structure. Requiring every Holon to contain all of them confuses the general object with a physical
chart." `Capability` is that clause as a type: `no_operation_from_the_carrier_alone` proves the
carrier supplies no operation by itself, and `operation_is_supplied_not_conferred` proves that two
different admissible parameters over *one* carrier give two different operations, so no function of
the carrier could have produced either.

## The transition is the wave-1 `Transition`, not an isomorphism

[definition] `ChartTransition` carries a `Foundation/ContinuingTower.lean::Transition`: lossy, with
its residual, and **not** assumed invertible. The cocycle condition on triple overlaps is therefore
stated with residuals (`Cocycle`, `CocycleDefect`), and its failure is returned as content —
`AtlasGluing` is the atlas's instance of C1's `unique | plural | obstructed` trichotomy, and
`atlasGluing_total` makes it total.

## Rust counterpart

[definition] The paired executable owner is `crates/holonic-engine/src/receiver_atlas.rs`. Its
types carry the same names — `Capability`, `SuppliedCapability`, `LocalChart`, `ChartTransition`,
`ReceiverAtlas`, `CoherentPlacement`, `AtlasGluing`, `CocycleDefect` — over exact arithmetic
(`num_bigint::BigInt`, `relational_geometry::Rat`), with every theorem below mirrored as a test and
with the protein atlas of `grain_tower.rs` as the instantiated atlas. Each Rust item names the
declaration here that it realizes.

## What this file does not do

[definition] It founds no cost enrichment: that is item **C5** and its owner is
`Foundation/PresentationCost.lean`. It founds no bridge vocabulary: that is item **C7** and its
owner is `Foundation/Bridge.lean`. It states no milestone.
-/

namespace Holonics.Foundation.Atlas

open Holonics
open Holonics.Foundation.ContinuingTower

universe u v w

/-! ## C6 (a) — `Capability`: a structure is supplied, never conferred -/

/-- [definition] The four kinds of structure the canon names as supplied rather than conferred.
`docs/canon/TABLET_THE_MANIFOLD.md` §16 for the metric and the smooth/complex structures, §19 for
analytic data, and `docs/HNN_FORMULA.md` for the scaling family ("fractal dimension belongs to an
identified scale family, not to tensor rank"). -/
inductive CapabilityKind
  /-- Lengths and angles: an `O(n)` or `CO(n)` reduction. -/
  | metric
  /-- Differentiation: a smooth structure, or a discrete cochain complex with `d`. -/
  | smoothStructure
  /-- Continuation: a germ and a path. -/
  | analyticData
  /-- Scaling exponents: an identified contraction family. -/
  | scalingFamily
  deriving DecidableEq, Repr

/-- [definition] A **capability** on a carrier: the parameters that would constitute it, the law
those parameters must satisfy, the value its operation returns, the operation that becomes
available once the law is discharged, and the identities the operation then obeys.

The operation is binary because a situated reading is always a comparison — AGENTS.md's "difference
is the only thing that is real"; a unary reading ignores its second argument. Nothing in this
structure can be built from `Carrier` alone, which is the whole point:
`no_operation_from_the_carrier_alone`.

Rust counterpart: `crates/holonic-engine/src/receiver_atlas.rs::Capability`. -/
structure Capability (Carrier : Type u) where
  /-- Which supplied structure this is. -/
  kind : CapabilityKind
  /-- What must be supplied. -/
  Parameters : Type v
  /-- The law the supplied parameters must satisfy — `J² = -I`, positive definiteness, and so on. -/
  admits : Parameters → Prop
  /-- What the operation returns. -/
  Value : Type v
  /-- The operation that becomes available exactly when the law is discharged. -/
  operations : ∀ p, admits p → Carrier → Carrier → Value
  /-- The identities the operation then obeys. -/
  laws : ∀ p, admits p → Prop

/-- [definition] The operation type a capability makes available. -/
abbrev Capability.Operation {Carrier : Type u} (C : Capability.{u, v} Carrier) : Type _ :=
  Carrier → Carrier → C.Value

/-- [definition] A **constituted** capability: the parameters actually supplied, the discharge of
the admission law, and the discharge of the identities. Without this witness there is no operation.

Rust counterpart: `receiver_atlas.rs::SuppliedCapability`'s witness fields. -/
structure Constituted {Carrier : Type u} (C : Capability.{u, v} Carrier) where
  /-- What was supplied. -/
  parameter : C.Parameters
  /-- That it is admissible. -/
  admitted : C.admits parameter
  /-- That the identities hold. -/
  lawful : C.laws parameter admitted

/-- [definition] The operation a constituted capability makes available. -/
def Constituted.operation {Carrier : Type u} {C : Capability.{u, v} Carrier}
    (s : Constituted C) : C.Operation :=
  C.operations s.parameter s.admitted

/-- [definition] A capability together with its witness, packaged for a chart to carry.

Rust counterpart: `receiver_atlas.rs::SuppliedCapability`. -/
structure SuppliedCapability (Carrier : Type u) where
  /-- The declared capability. -/
  capability : Capability.{u, v} Carrier
  /-- The witness that constitutes it. -/
  witness : Constituted capability

/-- [definition] The operation a supplied capability makes available. -/
def SuppliedCapability.operation {Carrier : Type u}
    (s : SuppliedCapability.{u, v} Carrier) : s.capability.Operation :=
  s.witness.operation

/-- [definition] The empty capability: nothing is admissible and the operation returns a value of
an empty type. It exists to refuse the claim that a carrier confers an operation. -/
def emptyCapability : Capability.{0, 0} PUnit where
  kind := .metric
  Parameters := Empty
  admits := fun p => p.elim
  Value := Empty
  operations := fun p => p.elim
  laws := fun p => p.elim

/-- [proved-derived; formal-checked] **A carrier supplies no operation.** There is no function
producing an operation from a carrier and a capability declaration alone; the witness is the empty
capability on `PUnit`. This is `docs/HOLON.md`'s "calling a vector a Holon does not supply those
properties" as a theorem. -/
theorem no_operation_from_the_carrier_alone :
    ¬ Nonempty (∀ (Carrier : Type) (C : Capability.{0, 0} Carrier), C.Operation) := by
  rintro ⟨h⟩
  exact (h PUnit emptyCapability PUnit.unit PUnit.unit).elim

/-- [definition] A weighted square metric on the exact integer plane. The parameters are two
strictly positive integer weights; the law is their positivity; the operation is the exact weighted
square distance; and the identity is that a point is at distance zero from itself.

No float participates: the carrier, the parameters and the value are `ℤ`. -/
def weightedSquareMetric : Capability.{0, 0} (ℤ × ℤ) where
  kind := .metric
  Parameters := ℤ × ℤ
  admits := fun w => 0 < w.1 ∧ 0 < w.2
  Value := ℤ
  operations := fun w _ x y => w.1 * (x.1 - y.1) ^ 2 + w.2 * (x.2 - y.2) ^ 2
  laws := fun w _ => ∀ x : ℤ × ℤ, w.1 * (x.1 - x.1) ^ 2 + w.2 * (x.2 - x.2) ^ 2 = 0

/-- [definition] The isotropic witness. -/
def isotropicWitness : Constituted weightedSquareMetric where
  parameter := (1, 1)
  admitted := ⟨one_pos, one_pos⟩
  lawful := by intro x; simp

/-- [definition] A second, anisotropic witness on the *same* carrier and the *same* capability. -/
def anisotropicWitness : Constituted weightedSquareMetric where
  parameter := (1, 2)
  admitted := ⟨one_pos, two_pos⟩
  lawful := by intro x; simp

/-- [counterexample; formal-checked] **The operation is supplied, not conferred.** One carrier, one
capability, two admissible parameter values, two different operations. No function of the carrier
alone could have produced either of them, so a metric on `ℤ × ℤ` is data a caller deposits and never
a consequence of the carrier's geometry. -/
theorem operation_is_supplied_not_conferred :
    isotropicWitness.operation ≠ anisotropicWitness.operation := by
  intro h
  have := congrFun (congrFun h (0, 0)) (0, 1)
  simp [Constituted.operation, weightedSquareMetric, isotropicWitness, anisotropicWitness] at this

/-! ## C6 (b) — `LocalChart` -/

/-- [definition] A **local chart**: where it reads, what it returns, the retained preimage it never
drops, and the structure — if any — that was supplied to its coordinate.

A chart with `metric = none` has placement and incidence and **no angles**: asking it for the
operation returns `none` by `reading_none_of_metric_none`, which is the type-level refusal the
doctrine demands rather than a zero.

Rust counterpart: `crates/holonic-engine/src/receiver_atlas.rs::LocalChart`. -/
structure LocalChart (X : Type u) where
  /-- Where this chart reads at all. -/
  Region : Set X
  /-- The face type of this receiver. -/
  Coordinate : Type v
  /-- The receiver on its own domain. -/
  place : Region → Coordinate
  /-- The retained preimage, never dropped. -/
  fibre : Coordinate → Set X
  /-- Every placed occurrence is retained in the fibre of its own coordinate. -/
  fibre_exact : ∀ x : Region, (x : X) ∈ fibre (place x)
  /-- The structure supplied to this chart's coordinate, if any. `none` is the ordinary case. -/
  metric : Option (SuppliedCapability.{v, v} Coordinate)

namespace LocalChart

variable {X : Type u}

/-- [definition] The occurrences this chart actually places at one coordinate. -/
def preimageFibre (c : LocalChart.{u, v} X) (z : c.Coordinate) : Set X :=
  {x | ∃ h : x ∈ c.Region, c.place ⟨x, h⟩ = z}

/-- [proved-derived; formal-checked] The declared fibre retains the whole preimage. A chart may
retain more than it placed, never less: the population behind a face is not droppable. -/
theorem preimageFibre_subset_fibre (c : LocalChart.{u, v} X) (z : c.Coordinate) :
    c.preimageFibre z ⊆ c.fibre z := by
  rintro x ⟨h, rfl⟩
  exact c.fibre_exact ⟨x, h⟩

/-- [definition] The reading this chart's supplied structure makes available, together with the
type of its value. A chart with no supplied structure has no reading. -/
def reading (c : LocalChart.{u, v} X) :
    Option ((V : Type v) × (c.Coordinate → c.Coordinate → V)) :=
  c.metric.map fun s => ⟨s.capability.Value, s.operation⟩

/-- [proved-derived; formal-checked] **Asking a capability-less chart for a reading returns
nothing.** Not a zero, not a default: `none`. -/
theorem reading_none_of_metric_none (c : LocalChart.{u, v} X) (h : c.metric = none) :
    c.reading = none := by
  simp [reading, h]

/-- [proved-derived; formal-checked] And a chart whose structure was supplied has one. -/
theorem reading_isSome_of_metric_isSome (c : LocalChart.{u, v} X) (h : c.metric.isSome) :
    c.reading.isSome := by
  cases hm : c.metric with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some s => simp [reading, hm]

end LocalChart

/-! ## C6 (c) — the cocycle, stated with residuals

The transition between two charts is the wave-1 `Transition`: lossy, carrying the part of the source
it does not transport. So the cocycle condition on a triple overlap is a statement about the
*transported faces*, and its failure is a genuine disagreement between two routes — holonomy — and
not a loss, because `Transition.reopen_apply` makes each route reopen its own source exactly. -/

/-- [definition] The **cocycle condition** on a triple of transitions: the routed face agrees with
the direct one. Stated on `apply`, because that is what a transition transports; the residuals are
compared separately and `residual_is_not_determined_by_the_face_map` shows they must be.

Rust counterpart: `receiver_atlas.rs::cocycle_holds`. -/
def Cocycle {A : Type u} {B : Type v} {C : Type w}
    (ab : Transition A B) (bc : Transition B C) (ac : Transition A C) : Prop :=
  ∀ x, (Transition.comp bc ab).apply x = ac.apply x

/-- [definition] A **cocycle defect**: one source at which the two routes disagree, carrying both
transported faces. This is the obstruction returned as content; it is not an error and it is not
resolved by choosing a route.

Rust counterpart: `receiver_atlas.rs::CocycleDefect`. -/
structure CocycleDefect {A : Type u} {B : Type v} {C : Type w}
    (ab : Transition A B) (bc : Transition B C) (ac : Transition A C) where
  /-- Where the routes disagree. -/
  source : A
  /-- What the composite route transports. -/
  routed : C
  /-- What the declared direct transition transports. -/
  direct : C
  /-- The routed face is the composite's. -/
  routed_eq : routed = (Transition.comp bc ab).apply source
  /-- The direct face is the direct transition's. -/
  direct_eq : direct = ac.apply source
  /-- And they differ. -/
  differ : routed ≠ direct

namespace CocycleDefect

variable {A : Type u} {B : Type v} {C : Type w}
variable {ab : Transition A B} {bc : Transition B C} {ac : Transition A C}

/-- [definition] What the composite route retained: the pair of component residuals, in the order
they were dropped (`Transition.comp_residual`). -/
def routedResidual (d : CocycleDefect ab bc ac) : (Transition.comp bc ab).Residual :=
  (Transition.comp bc ab).residual d.source

/-- [definition] What the direct route retained. -/
def directResidual (d : CocycleDefect ab bc ac) : ac.Residual :=
  ac.residual d.source

/-- [proved-derived; formal-checked] The composite route reopens the source exactly. -/
theorem routed_reopens (d : CocycleDefect ab bc ac) :
    (Transition.comp bc ab).reopen d.routed d.routedResidual = d.source := by
  rw [d.routed_eq]
  exact (Transition.comp bc ab).reopen_apply d.source

/-- [proved-derived; formal-checked] The direct route reopens the source exactly. -/
theorem direct_reopens (d : CocycleDefect ab bc ac) :
    ac.reopen d.direct d.directResidual = d.source := by
  rw [d.direct_eq]
  exact ac.reopen_apply d.source

/-- [proved-derived; formal-checked] **A cocycle defect is holonomy, not loss.** Both routes reopen
the same source with no remainder, so neither dropped anything it failed to record; what differs is
only the face each route presents. `docs/canon/TABLET_THE_MANIFOLD.md` §15's row "a coercion whose
result depends on the path taken — holonomy" is exactly this. -/
theorem defect_is_holonomy_not_loss (d : CocycleDefect ab bc ac) :
    (Transition.comp bc ab).reopen d.routed d.routedResidual = d.source ∧
      ac.reopen d.direct d.directResidual = d.source :=
  ⟨d.routed_reopens, d.direct_reopens⟩

end CocycleDefect

/-- [proved-derived; formal-checked] The cocycle holds exactly when there is no defect. The
obstruction population and the law are one object. -/
theorem cocycle_iff_isEmpty_defect {A : Type u} {B : Type v} {C : Type w}
    (ab : Transition A B) (bc : Transition B C) (ac : Transition A C) :
    Cocycle ab bc ac ↔ IsEmpty (CocycleDefect ab bc ac) := by
  constructor
  · intro h
    refine ⟨fun d => d.differ ?_⟩
    rw [d.routed_eq, d.direct_eq]
    exact h d.source
  · intro h x
    by_contra hne
    exact h.false
      { source := x, routed := (Transition.comp bc ab).apply x, direct := ac.apply x,
        routed_eq := rfl, direct_eq := rfl, differ := hne }

/-- [proved-derived; formal-checked] The cocycle **does** hold for the canonical lossy grain:
coarsening by `2` and then by `3` transports the same face as coarsening by `6`, although the two
routes retain entirely different residuals — a pair `(x / 2 % 3, x % 2)` against `x % 6`.
`residual_is_not_determined_by_the_face_map` is the general statement; this is its instance on the
grain. -/
theorem coarseGrain_cocycle : Cocycle (coarseGrain 2) (coarseGrain 3) (coarseGrain 6) := by
  intro x
  show x / 2 / 3 = x / 6
  rw [Nat.div_div_eq_div_mul]

/-- [counterexample; formal-checked] And it fails for a grain that is not a factorization: `5` does
not refine into `2` then `3`, and `x = 5` is the witness. The defect is returned whole. -/
def coarseGrainDefect : CocycleDefect (coarseGrain 2) (coarseGrain 3) (coarseGrain 5) where
  source := 5
  routed := 0
  direct := 1
  routed_eq := by decide
  direct_eq := by decide
  differ := by decide

/-- [counterexample; formal-checked] Hence that triple does not satisfy the cocycle. -/
theorem coarseGrain_not_cocycle :
    ¬ Cocycle (coarseGrain 2) (coarseGrain 3) (coarseGrain 5) := by
  intro h
  exact ((cocycle_iff_isEmpty_defect _ _ _).mp h).false coarseGrainDefect

/-! ## C6 (d) — `ChartTransition` on an overlap -/

/-- [definition] A **chart transition**: a transition between two charts' coordinates, defined on
their overlap and agreeing with both charts' own placements there. It is not assumed invertible; it
carries the residual its `Transition` carries.

Rust counterpart: `crates/holonic-engine/src/receiver_atlas.rs::ChartTransition`. -/
structure ChartTransition {X : Type u} (A B : LocalChart.{u, v} X) where
  /-- Where both charts read. -/
  overlap : Set X
  /-- The overlap lies in the source chart's region. -/
  overlap_left : overlap ⊆ A.Region
  /-- And in the target chart's region. -/
  overlap_right : overlap ⊆ B.Region
  /-- The lossy chart map, with its retained residual. -/
  transition : Transition.{v, v, v} A.Coordinate B.Coordinate
  /-- On the overlap it is exactly the target chart's own placement. -/
  natural : ∀ (x : X) (h : x ∈ overlap),
    transition.apply (A.place ⟨x, overlap_left h⟩) = B.place ⟨x, overlap_right h⟩

namespace ChartTransition

variable {X : Type u} {A B : LocalChart.{u, v} X}

/-- [proved-derived; formal-checked] The transition's residual reopens the source coordinate
exactly. Cited from `Transition.reopen_apply`, not reproved. -/
theorem residual_reopens (t : ChartTransition A B) (z : A.Coordinate) :
    t.transition.reopen (t.transition.apply z) (t.transition.residual z) = z :=
  t.transition.reopen_apply z

/-- [proved-derived; formal-checked] Every later, finer receiver on the source chart factors
through the target face paired with the residual. Cited from
`Transition.laterReceiverFactors`. -/
theorem later_receiver_factors (t : ChartTransition A B) {Fine : Type*}
    (finer : A.Coordinate → Fine) :
    ∃ recover : B.Coordinate → t.transition.Residual → Fine,
      ∀ z, recover (t.transition.apply z) (t.transition.residual z) = finer z :=
  t.transition.laterReceiverFactors finer

end ChartTransition

/-! ## C6 (e) — `ReceiverAtlas` and its coherent placements -/

/-- [definition] A **receiver atlas**: the charts an object actually admits, together with the
transitions it actually declares between them. A `none` transition is an undiscovered relation, not
a denial — `docs/canon/TABLET_THE_CHART.md` §10.1: "A chart with no declared relation to another
chart is not wrong; it is incomparable, and the type says so."

The cost of a transition belongs to item **C5** (`Foundation/PresentationCost.lean`) and is
deliberately not a field here.

Rust counterpart: `crates/holonic-engine/src/receiver_atlas.rs::ReceiverAtlas`. -/
structure ReceiverAtlas (X : Type u) where
  /-- The index of charts. -/
  Chart : Type v
  /-- The chart at each index. -/
  chart : Chart → LocalChart.{u, v} X
  /-- The declared transition between two charts, when there is one. -/
  transition : ∀ a b : Chart, Option (ChartTransition (chart a) (chart b))

/-- [definition] A **coherent placement** of an atlas: one coordinate at every chart, agreeing
under every transition the atlas declares. This is what "the embedding is one global vector" would
mean, and `theEmbeddingIsNotOneVector` shows it can fail to exist while every chart is inhabited.

Rust counterpart: `receiver_atlas.rs::CoherentPlacement`. -/
structure CoherentPlacement {X : Type u} (A : ReceiverAtlas.{u, v} X) where
  /-- The coordinate presented at each chart. -/
  value : ∀ c : A.Chart, (A.chart c).Coordinate
  /-- Every declared transition carries one to the next. -/
  coherent : ∀ (a b : A.Chart) (t : ChartTransition (A.chart a) (A.chart b)),
    A.transition a b = some t → t.transition.apply (value a) = value b

/-- [proved-derived; formal-checked] A coherent placement is determined by its values: the
coherence field is a `Prop`. -/
theorem CoherentPlacement.ext {X : Type u} {A : ReceiverAtlas.{u, v} X}
    {v w : CoherentPlacement A} (h : v.value = w.value) : v = w := by
  cases v; cases w; simp_all

/-- [definition] The three lawful returns of an attempted global placement, for an atlas. This is
`Foundation/ContinuingTower.lean::Tower.GluingResult` at the atlas index: the same trichotomy, and
a cocycle failure lands in `obstructed` rather than raising an error.

Rust counterpart: `receiver_atlas.rs::AtlasGluing`. -/
inductive AtlasGluing {X : Type u} (A : ReceiverAtlas.{u, v} X) : Prop
  /-- Exactly one global placement. -/
  | unique (h : Nonempty (CoherentPlacement A)) (hs : Subsingleton (CoherentPlacement A))
  /-- Several; the plurality is the content and is not collapsed. -/
  | plural (h : Nonempty (CoherentPlacement A)) (hp : ¬ Subsingleton (CoherentPlacement A))
  /-- None, although every chart may be inhabited. -/
  | obstructed (h : IsEmpty (CoherentPlacement A))

/-- [proved-derived; formal-checked] The atlas trichotomy is total, exactly as
`Tower.gluingResult_total` is. -/
theorem atlasGluing_total {X : Type u} (A : ReceiverAtlas.{u, v} X) : AtlasGluing A := by
  classical
  by_cases h : Nonempty (CoherentPlacement A)
  · by_cases hs : Subsingleton (CoherentPlacement A)
    · exact .unique h hs
    · exact .plural h hs
  · exact .obstructed (not_nonempty_iff.mp h)

/-- [proved-derived; formal-checked] **A cocycle defect is returned as content.** If the two routes
`a → b → c` and `a → c` disagree at a coordinate, then no coherent placement presents that
coordinate at `a`. The defect is not an error: it removes exactly the placements it refutes and
leaves the rest. -/
theorem no_coherentPlacement_through_defect {X : Type u} (A : ReceiverAtlas.{u, v} X)
    {a b c : A.Chart}
    {tab : ChartTransition (A.chart a) (A.chart b)}
    {tbc : ChartTransition (A.chart b) (A.chart c)}
    {tac : ChartTransition (A.chart a) (A.chart c)}
    (hab : A.transition a b = some tab) (hbc : A.transition b c = some tbc)
    (hac : A.transition a c = some tac)
    (d : CocycleDefect tab.transition tbc.transition tac.transition)
    (v : CoherentPlacement A) : v.value a ≠ d.source := by
  intro hv
  refine d.differ ?_
  rw [d.routed_eq, d.direct_eq, ← hv]
  show tbc.transition.apply (tab.transition.apply (v.value a)) = tac.transition.apply (v.value a)
  rw [v.coherent a b tab hab, v.coherent b c tbc hbc, v.coherent a c tac hac]

/-- [proved-derived; formal-checked] And when the defect covers every coordinate of the source
chart, the atlas is `obstructed`. A total cocycle failure is returned through the trichotomy and
never as an exception. -/
theorem atlasGluing_obstructed_of_total_defect {X : Type u} (A : ReceiverAtlas.{u, v} X)
    {a b c : A.Chart}
    {tab : ChartTransition (A.chart a) (A.chart b)}
    {tbc : ChartTransition (A.chart b) (A.chart c)}
    {tac : ChartTransition (A.chart a) (A.chart c)}
    (hab : A.transition a b = some tab) (hbc : A.transition b c = some tbc)
    (hac : A.transition a c = some tac)
    (total : ∀ z : (A.chart a).Coordinate,
      ∃ d : CocycleDefect tab.transition tbc.transition tac.transition, d.source = z) :
    AtlasGluing A := by
  refine .obstructed ⟨fun v => ?_⟩
  obtain ⟨d, hd⟩ := total (v.value a)
  exact no_coherentPlacement_through_defect A hab hbc hac d v hd.symm

/-! ## C6 (f) — the classical case: invertible transitions plus the cocycle glue -/

/-- [definition] An atlas whose charts are **pairwise linked by invertible transitions satisfying
the cocycle**. This is the classical atlas: every transition map is a legal cast in both directions
and the coercion diamond commutes (`docs/canon/TABLET_THE_MANIFOLD.md` §15).

Rust counterpart: `receiver_atlas.rs::ChartCocycle`. -/
structure ChartCocycle {X : Type u} (A : ReceiverAtlas.{u, v} X) where
  /-- The transition between every ordered pair of charts. -/
  link : ∀ a b : A.Chart, ChartTransition (A.chart a) (A.chart b)
  /-- Each one is the atlas's own declared transition. -/
  declared : ∀ a b, A.transition a b = some (link a b)
  /-- Each transported map is a bijection: the cast is legal in both directions. -/
  bijective : ∀ a b, Function.Bijective (link a b).transition.apply
  /-- And the coercion diamond commutes on triples. -/
  cocycle : ∀ (a b c : A.Chart) (z : (A.chart a).Coordinate),
    (link b c).transition.apply ((link a b).transition.apply z) = (link a c).transition.apply z

namespace ChartCocycle

variable {X : Type u} {A : ReceiverAtlas.{u, v} X}

/-- [proved-derived; formal-checked] The self-link is the identity. It is not assumed: the cocycle
plus injectivity force it. -/
theorem self_id (K : ChartCocycle A) (a : A.Chart) (z : (A.chart a).Coordinate) :
    (K.link a a).transition.apply z = z :=
  (K.bijective a a).1 (K.cocycle a a a z)

/-- [proved-derived; formal-checked] **An atlas with all-invertible transitions and the cocycle law
glues to a global coordinate.** The coherent placements of such an atlas are in bijection with the
coordinate of any single chart: one chart's reading determines every other, which is exactly the
classical statement that a compatible atlas has one global coordinate.

`placementEquiv` is the recovery of the classical case, and everything below it — the obstructed
atlas, the residual, the incomparable charts — is what happens when its hypotheses fail. -/
def placementEquiv (K : ChartCocycle A) (c₀ : A.Chart) :
    CoherentPlacement A ≃ (A.chart c₀).Coordinate where
  toFun v := v.value c₀
  invFun z :=
    { value := fun c => (K.link c₀ c).transition.apply z
      coherent := by
        intro a b t ht
        have htb : t = K.link a b :=
          (Option.some_injective _ ((K.declared a b).symm.trans ht)).symm
        subst htb
        exact K.cocycle c₀ a b z }
  left_inv v := by
    refine CoherentPlacement.ext ?_
    funext c
    exact v.coherent c₀ c (K.link c₀ c) (K.declared c₀ c)
  right_inv z := K.self_id c₀ z

/-- [proved-derived; formal-checked] Hence such an atlas is never obstructed once one chart has a
coordinate: the global placement exists. -/
theorem nonempty_placement (K : ChartCocycle A) (c₀ : A.Chart)
    (h : Nonempty (A.chart c₀).Coordinate) : Nonempty (CoherentPlacement A) :=
  ⟨(K.placementEquiv c₀).symm h.some⟩

end ChartCocycle

/-! ## C6 (g) — an atlas that admits **no** global chart

This is the formal statement that the embedding cannot be one vector. The carrier is inhabited,
every chart reads a nonempty region, every chart's coordinate type is inhabited, every transition
is a lawful `Transition` with its residual — and there is no coherent placement at all.

It is the shift tower's Mittag-Leffler failure (`shiftTower_obstructed`) in atlas form, and the
tie is formal: `shiftAtlasSection` carries a coherent placement of the atlas to a compatible section
of `shiftTower`, so the atlas's emptiness is the tower's, cited and not reproved. -/

namespace ShiftAtlas

/-- [definition] Chart `n` reads the tail `{x | n ≤ x}` of `ℕ` in the coordinate "distance past
`n`". Every chart has a nonempty region and an inhabited coordinate; no structure is supplied, so
`metric = none`. -/
def tailChart (n : ℕ) : LocalChart.{0, 0} ℕ where
  Region := {x | n ≤ x}
  Coordinate := ℕ
  place := fun x => (x : ℕ) - n
  fibre := fun z => {x | n ≤ x ∧ x - n = z}
  fibre_exact := fun x => ⟨x.2, rfl⟩
  metric := none

/-- [proved-derived; formal-checked] Every chart reads a nonempty region. -/
theorem tailChart_region_nonempty (n : ℕ) : (n : ℕ) ∈ (tailChart n).Region := le_refl n

/-- [proved-derived; formal-checked] Every chart's coordinate type is inhabited. -/
theorem tailChart_coordinate_nonempty (n : ℕ) : Nonempty (tailChart n).Coordinate := by
  show Nonempty ℕ
  exact ⟨0⟩

/-- [definition] The transition from chart `a` to chart `b`: re-base the offset. It transports
`y ↦ (y + a) - b` — injective when `a ≥ b` and genuinely lossy when `a < b`, where the truncation
`min (y + a) b` is the retained residual. -/
def tailTransition (a b : ℕ) : Transition ℕ ℕ where
  Residual := ℕ
  apply := fun y => (y + a) - b
  residual := fun y => min (y + a) b
  reopen := fun t r => (t + r) - a
  reopen_apply := by intro y; omega

/-- [definition] The chart transition it presents, natural on the overlap `{x | max a b ≤ x}`. -/
def tailChartTransition (a b : ℕ) : ChartTransition (tailChart a) (tailChart b) where
  overlap := {x | max a b ≤ x}
  overlap_left := fun _ h => le_trans (le_max_left a b) h
  overlap_right := fun _ h => le_trans (le_max_right a b) h
  transition := tailTransition a b
  natural := by
    intro x h
    have ha : a ≤ x := le_trans (le_max_left a b) h
    show (x - a + a) - b = x - b
    omega

/-- [definition] **The shift atlas.** Every chart of it is inhabited and every pair of charts is
linked by a lawful transition. -/
def shiftAtlas : ReceiverAtlas.{0, 0} ℕ where
  Chart := ℕ
  chart := tailChart
  transition := fun a b => some (tailChartTransition a b)

/-- [definition] Read a shift-atlas coordinate as the natural number it is. -/
abbrev shiftValue (v : CoherentPlacement shiftAtlas) (n : ℕ) : ℕ := v.value n

/-- [proved-derived; formal-checked] A coherent placement of the shift atlas is a compatible
section of `shiftTower`. The atlas's global-placement question and C1's global-section question are
one question. -/
def shiftAtlasSection (v : CoherentPlacement shiftAtlas) : shiftTower.CompatibleSection where
  witness := fun n => shiftValue v n
  compatible := by
    intro i j h
    have hc : (shiftValue v j + j) - i = shiftValue v i :=
      v.coherent j i (tailChartTransition j i) rfl
    show shiftValue v j + (j - i) = shiftValue v i
    omega

/-- [counterexample; formal-checked] **The embedding is not one vector.** Every chart of
`shiftAtlas` reads a nonempty region with an inhabited coordinate, every transition is lawful and
carries its residual, and there is no coherent placement at all: no single global coordinate
reading is consistent with the atlas's own transitions.

This is `shiftTower_obstructed` — the Mittag-Leffler failure — cited through `shiftAtlasSection`
rather than reproved. -/
theorem theEmbeddingIsNotOneVector : IsEmpty (CoherentPlacement shiftAtlas) :=
  ⟨fun v => shiftTower_obstructed.false (shiftAtlasSection v)⟩

/-- [proved-derived; formal-checked] So the atlas returns `obstructed` through the trichotomy, and
never an error. -/
theorem shiftAtlas_gluing : AtlasGluing shiftAtlas :=
  .obstructed theEmbeddingIsNotOneVector

/-- [proved-derived; formal-checked] The hypothesis of `ChartCocycle.placementEquiv` that fails: the
shift atlas's transitions are not all bijective. At `a = 0, b = 1` the map `y ↦ y - 1` merges `0`
and `1`, and the residual is exactly what separates them. -/
theorem shiftAtlas_not_invertible : ¬ Function.Injective (tailTransition 0 1).apply := by
  intro h
  have hz : (tailTransition 0 1).apply 0 = (tailTransition 0 1).apply 1 := by
    show (0 + 0) - 1 = (1 + 0) - 1
    decide
  exact absurd (h hz) (by decide)

/-- [proved-derived; formal-checked] And the residual separates exactly what the face merged. -/
theorem shiftAtlas_residual_separates :
    (tailTransition 0 1).residual 0 ≠ (tailTransition 0 1).residual 1 := by
  intro h
  have hbad : (0 : ℕ) = 1 := h
  exact absurd hbad (by decide)

end ShiftAtlas

/-! ## C6 (h) — comparison by common refinement, and where it is undefined -/

/-- [definition] The refinement comparison of two charts: "refine to a common upper bound and
restrict back". It is available exactly when the two charts have a common refinement in the chart
index order.

Rust counterpart: `receiver_atlas.rs::comparable_by_refinement`. -/
def ComparableByRefinement {Index : Type*} [Preorder Index] (a b : Index) : Prop :=
  ∃ k, a ≤ k ∧ b ≤ k

/-- [proved-derived; formal-checked] **The refinement comparison is undefined between the two
incomparable charts.** `twoCharts_no_common_refinement` says there is no common upper bound at all,
so the route "refine and restrict back" does not merely lack a proof — it does not exist.
`swapMigration` is the declared passage that crosses that gap, and
`swapMigration_not_factorsThroughRefinement` proves it is not the refinement route in disguise. -/
theorem twoCharts_comparison_undefined :
    ¬ ComparableByRefinement TwoCharts.left TwoCharts.right :=
  twoCharts_no_common_refinement

/-- [definition] One chart of `R` reads every chart of `A`: `R` **refines** `A`. The refining
chart's region covers the refined one's, and its coordinate determines the refined reading.

Rust counterpart: `receiver_atlas.rs::AtlasRefinement`. -/
structure AtlasRefinement {X : Type u} (R A : ReceiverAtlas.{u, v} X) where
  /-- Which chart of `R` reads each chart of `A`. -/
  toChart : A.Chart → R.Chart
  /-- It reads at least as widely. -/
  covers : ∀ c, (A.chart c).Region ⊆ (R.chart (toChart c)).Region
  /-- And its coordinate determines the coarse reading. -/
  read : ∀ c, (R.chart (toChart c)).Coordinate → (A.chart c).Coordinate
  /-- Exactly. -/
  reads : ∀ (c : A.Chart) (x : X) (h : x ∈ (A.chart c).Region),
    read c ((R.chart (toChart c)).place ⟨x, covers c h⟩) = (A.chart c).place ⟨x, h⟩

/-- [definition] Two atlases are **equivalent under common refinement** when some atlas refines
both. Where no common refinement exists the comparison is undefined, not false. -/
def EquivalentUnderRefinement {X : Type u} (A B : ReceiverAtlas.{u, v} X) : Prop :=
  ∃ R : ReceiverAtlas.{u, v} X, Nonempty (AtlasRefinement R A) ∧ Nonempty (AtlasRefinement R B)

/-- [proved-derived; formal-checked] Every atlas refines itself, so the comparison is reflexive
where it is defined at all. -/
def AtlasRefinement.refl {X : Type u} (A : ReceiverAtlas.{u, v} X) : AtlasRefinement A A where
  toChart := id
  covers := fun _ => subset_refl _
  read := fun _ => id
  reads := fun _ _ _ => rfl

/-- [definition] Two occurrences are **indistinguishable to an atlas** when every chart that reads
both returns the same coordinate for them.

Rust counterpart: `receiver_atlas.rs::atlas_indistinguishable`. -/
def AtlasIndistinguishable {X : Type u} (A : ReceiverAtlas.{u, v} X) (x y : X) : Prop :=
  ∀ (c : A.Chart) (hx : x ∈ (A.chart c).Region) (hy : y ∈ (A.chart c).Region),
    (A.chart c).place ⟨x, hx⟩ = (A.chart c).place ⟨y, hy⟩

/-- [proved-derived; formal-checked] **Two objects agreeing on every chart of an atlas are
indistinguishable to that atlas.** Every receiver read off one of its charts identifies them: there
is no reading the atlas supplies that separates them. -/
theorem indistinguishable_factors {X : Type u} {A : ReceiverAtlas.{u, v} X} {x y : X}
    (h : AtlasIndistinguishable A x y) {F : Type*} (c : A.Chart)
    (hx : x ∈ (A.chart c).Region) (hy : y ∈ (A.chart c).Region)
    (g : (A.chart c).Coordinate → F) :
    g ((A.chart c).place ⟨x, hx⟩) = g ((A.chart c).place ⟨y, hy⟩) :=
  congrArg g (h c hx hy)

/-- [proved-derived; formal-checked] **And every declared transition still agrees on them.** The
statement "agreeing on every chart *and* on every transition" is not two conditions: agreement on
the charts already forces agreement of every transported face, because a transition is natural over
the placements. -/
theorem indistinguishable_transports {X : Type u} {A : ReceiverAtlas.{u, v} X} {x y : X}
    (h : AtlasIndistinguishable A x y) {a b : A.Chart}
    (t : ChartTransition (A.chart a) (A.chart b))
    (hx : x ∈ t.overlap) (hy : y ∈ t.overlap) :
    t.transition.apply ((A.chart a).place ⟨x, t.overlap_left hx⟩) =
      t.transition.apply ((A.chart a).place ⟨y, t.overlap_left hy⟩) :=
  congrArg t.transition.apply (h a (t.overlap_left hx) (t.overlap_left hy))

/-- [proved-derived; formal-checked] **A finer atlas may reopen the collapse.** What a refining
atlas cannot separate, the refined one cannot separate either; so every separation belongs to the
finer atlas, and a coarse atlas's verdict of indistinguishability is never a verdict about the
object. -/
theorem indistinguishable_of_refinement {X : Type u} {R A : ReceiverAtlas.{u, v} X}
    (ρ : AtlasRefinement R A) {x y : X} (h : AtlasIndistinguishable R x y) :
    AtlasIndistinguishable A x y := by
  intro c hx hy
  rw [← ρ.reads c x hx, ← ρ.reads c y hy]
  exact congrArg (ρ.read c) (h (ρ.toChart c) (ρ.covers c hx) (ρ.covers c hy))

/-! ### The separation is real: a coarse atlas that cannot see, and a richer one that can -/

namespace SeparatingAtlas

/-- [definition] The blind chart on `Bool`: it reads everywhere and returns one coordinate. -/
def blindChart : LocalChart.{0, 0} Bool where
  Region := Set.univ
  Coordinate := PUnit
  place := fun _ => PUnit.unit
  fibre := fun _ => Set.univ
  fibre_exact := fun _ => trivial
  metric := none

/-- [definition] The faithful chart on `Bool`: it reads everywhere and returns the occurrence. -/
def faithfulChart : LocalChart.{0, 0} Bool where
  Region := Set.univ
  Coordinate := Bool
  place := fun x => (x : Bool)
  fibre := fun z => {x | x = z}
  fibre_exact := fun _ => rfl
  metric := none

/-- [definition] The coarse atlas: one blind chart. -/
def coarseAtlas : ReceiverAtlas.{0, 0} Bool where
  Chart := PUnit
  chart := fun _ => blindChart
  transition := fun _ _ => none

/-- [definition] The richer atlas: the blind chart and the faithful one. -/
def richAtlas : ReceiverAtlas.{0, 0} Bool where
  Chart := Bool
  chart := fun b => match b with
    | true => faithfulChart
    | false => blindChart
  transition := fun _ _ => none

/-- [proved-derived; formal-checked] The coarse atlas cannot separate `false` from `true`. -/
theorem coarse_cannot_separate : AtlasIndistinguishable coarseAtlas false true := by
  intro _ _ _
  rfl

/-- [counterexample; formal-checked] The richer atlas does. A coarse atlas's verdict of
indistinguishability is a fact about that atlas and never about the object. -/
theorem rich_separates : ¬ AtlasIndistinguishable richAtlas false true := by
  intro h
  have hbad : false = true := h true trivial trivial
  exact absurd hbad (by decide)

/-- [counterexample; formal-checked] And the refusal is exactly `Foundation/Receiver.lean`'s
insufficiency witness: the blind reading identifies two occurrences that the faithful reading
separates, so no receiver-to-receiver transformer carries one into the other. -/
def blindInsufficiency : ReceiverInsufficiency (fun _ : Bool => PUnit.unit) (fun x : Bool => x) where
  left := false
  right := true
  sameEntering := rfl
  differentReturned := by decide

/-- [proved-derived; formal-checked] Hence there is no functional transformer from the blind chart's
reading to the faithful one. Cited from `ReceiverTransformer.excludesInsufficiency`. -/
theorem no_transformer_from_the_blind_chart :
    IsEmpty (ReceiverTransformer (fun _ : Bool => PUnit.unit) (fun x : Bool => x)) :=
  ⟨fun t => t.excludesInsufficiency blindInsufficiency⟩

end SeparatingAtlas


/-! ## R7 — the separating atlas theorem

[definition] **For a declared bounded class, any two inequivalent objects admit some probe,
receiver and time at which their responses differ.** That is a property of an atlas *and* of a
class, never of the objects alone, so it is stated here as `Separates` — a predicate on an atlas —
and both a positive instance and a negative one are exhibited below.

The positive instance is `fullProbeAtlas_separates`: the full coordinate probe atlas over the
exact linear systems of bounded dimension `n` separates them at **time one**, for every `n`. This
is the `Fin n` generalization of `Foundation/CausalChord.lean`'s
`full_atlas_determines_the_operator_fin_two`, and it is sharper than that statement's route: the
adjugate cofactor expansion is not needed at all once the atlas is read through the Markov
parameters `C A^k B` rather than through `adj(sI − A)`.

[established-bounded] **The finding.** The classical `2n` bound of realization theory is *not*
about the full coordinate atlas. With `B = C = I` the `k = 1` Markov parameter is `A` itself, so
time one suffices at every dimension. The `2n` bound belongs to the **declared-port** case, where
`B` and `C` are given and the question is whether the visible response determines the minimal
realization up to similarity. What this file proves about that case is
`markov_truncation`: two generators that already share a characteristic polynomial and whose
Markov parameters agree at every time below `n` agree at every time — the Cayley–Hamilton
truncation, with the sharper bound `n`. The full declared-port statement at `2n`, without the
shared-characteristic hypothesis, is stated as the open `MarkovTwoNSuffices` and is **not** proved:
it needs the Hankel-matrix rank argument and the Kalman decomposition, neither of which is here.
-/

/-- [definition] An atlas **separates** a declared class when no two distinct members of that class
are indistinguishable to it. This is R7's statement type.

Rust counterpart: `receiver_atlas.rs::ReceiverAtlas::is_separating` and `SeparatingVerdict`. -/
def Separates {X : Type u} (A : ReceiverAtlas.{u, v} X) (declaredClass : Set X) : Prop :=
  ∀ x ∈ declaredClass, ∀ y ∈ declaredClass, AtlasIndistinguishable A x y → x = y

/-- [proved-derived; formal-checked] A separating atlas stays separating on a smaller declared
class: the class is part of the statement and shrinking it never costs separation. -/
theorem Separates.mono {X : Type u} {A : ReceiverAtlas.{u, v} X} {C D : Set X}
    (h : Separates A D) (hCD : C ⊆ D) : Separates A C :=
  fun x hx y hy hxy => h x (hCD hx) y (hCD hy) hxy

/-- [proved-derived; formal-checked] And a **refining** atlas separates whatever the refined one
does: `indistinguishable_of_refinement` run forwards. Adding charts never loses a separation. -/
theorem Separates.of_refinement {X : Type u} {R A : ReceiverAtlas.{u, v} X} {C : Set X}
    (ρ : AtlasRefinement R A) (h : Separates A C) : Separates R C :=
  fun x hx y hy hxy => h x hx y hy (indistinguishable_of_refinement ρ hxy)

namespace SeparatingAtlas

/-! ### (a) The exact linear systems of bounded dimension, under the full probe atlas -/

section LinearClass

open Holonics.Foundation.CausalChord Matrix Polynomial

variable {K : Type} [Field K] {n m p : ℕ}

/-- [definition] The `k`-th **Markov parameter** `C A^k B`: the exact response of the plan's
`x_{t+1} = A x_t + B u_t`, `y = C x` to a unit impulse, read at time `k`. It is the coefficient
family of the transfer object, and it is what a probe/receiver/time triple actually reads. -/
def markov (C : Matrix (Fin p) (Fin n) K) (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin m) K) (k : ℕ) : Matrix (Fin p) (Fin m) K :=
  C * A ^ k * B

/-- [definition] The Markov parameters of a `Foundation/CausalChord.lean::Linearization`. -/
def linearizationMarkov (L : Linearization K n m p) (k : ℕ) : Matrix (Fin p) (Fin m) K :=
  markov L.readout L.state L.excitation k

/-- [proved-derived; formal-checked] **The identity probe reads the operator at time one, at every
dimension.** With `B = C = I` — every coordinate excited and every coordinate observed — the `k = 1`
Markov parameter *is* `A`. This is the `Fin n` case of the plan's
`full_atlas_determines_the_operator_fin_two`, proved for all `n` with no cofactor expansion. -/
theorem identity_probe_determines_the_operator {A A' : Matrix (Fin n) (Fin n) K}
    (h : markov (1 : Matrix (Fin n) (Fin n) K) A (1 : Matrix (Fin n) (Fin n) K) 1
        = markov (1 : Matrix (Fin n) (Fin n) K) A' (1 : Matrix (Fin n) (Fin n) K) 1) :
    A = A' := by
  simpa [markov] using h

/-- [definition] The chart of the full probe atlas at excitation coordinate `i`, readout coordinate
`j` and time `k`: it reads every system of the declared dimension, and returns the exact scalar
`(A^k) j i` — the response of readout `j` to an impulse at excitation `i`, `k` steps later. -/
def probeChart (K : Type) [Field K] (n : ℕ) (i j : Fin n) (k : ℕ) :
    LocalChart.{0, 0} (Matrix (Fin n) (Fin n) K) where
  Region := Set.univ
  Coordinate := K
  place := fun A => (A.1 ^ k) j i
  fibre := fun z => {A | (A ^ k) j i = z}
  fibre_exact := fun _ => rfl
  metric := none

/-- [definition] **The full probe atlas** over the exact linear systems of a declared bounded
dimension: every excitation coordinate against every readout coordinate at every time. No
transition is declared between two of its charts — those relations are undiscovered, and the atlas
says so by carrying `none` rather than by inventing one. -/
def fullProbeAtlas (K : Type) [Field K] (n : ℕ) :
    ReceiverAtlas.{0, 0} (Matrix (Fin n) (Fin n) K) where
  Chart := Fin n × Fin n × ℕ
  chart := fun c => probeChart K n c.1 c.2.1 c.2.2
  transition := fun _ _ => none

/-- [proved-derived; formal-checked] **R7(a): the full probe atlas separates the whole declared
class, at every dimension.** Two systems of the declared bounded dimension that no probe, readout
and time tells apart are equal. The separating time is `1`; the atlas needs no more.

This generalizes `Foundation/CausalChord.lean::full_atlas_determines_the_operator_fin_two` from
`Fin 2` to `Fin n`, and it does so through the Markov parameters rather than through the adjugate,
which is why the degree-`n − 2` cofactor expansion that statement's name records as missing is not
needed. -/
theorem fullProbeAtlas_separates (K : Type) [Field K] (n : ℕ) :
    Separates (fullProbeAtlas K n) Set.univ := by
  intro A _ B _ h
  ext i j
  have := h (j, i, 1) (Set.mem_univ A) (Set.mem_univ B)
  simpa [fullProbeAtlas, probeChart, pow_one] using this

/-! ### The Cayley–Hamilton truncation of the declared-port atlas -/

/-- [proved-derived; formal-checked] **Cayley–Hamilton, as a truncation.** Every power of a
generator is the evaluation at that generator of the remainder of `X^k` modulo its characteristic
polynomial — a polynomial of degree strictly below the dimension. Nothing above time `n − 1` is new
information about `A` itself. -/
theorem pow_eq_aeval_modByMonic_charpoly (A : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    A ^ k = Polynomial.aeval A (((Polynomial.X : K[X]) ^ k) %ₘ A.charpoly) := by
  have key : Polynomial.aeval A ((((Polynomial.X : K[X]) ^ k) %ₘ A.charpoly)
        + A.charpoly * (((Polynomial.X : K[X]) ^ k) /ₘ A.charpoly))
      = Polynomial.aeval A ((Polynomial.X : K[X]) ^ k) := by
    rw [Polynomial.modByMonic_add_div ((Polynomial.X : K[X]) ^ k) A.charpoly]
  rw [map_add, map_mul, Matrix.aeval_self_charpoly, zero_mul, add_zero] at key
  rw [key]
  simp

/-- [proved-derived; formal-checked] The truncated remainder has degree strictly below the declared
dimension. -/
theorem natDegree_modByMonic_charpoly_lt (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hn : 0 < n) :
    (((Polynomial.X : K[X]) ^ k) %ₘ A.charpoly).natDegree < n := by
  rcases eq_or_ne (((Polynomial.X : K[X]) ^ k) %ₘ A.charpoly) 0 with h0 | h0
  · rw [h0]; simpa using hn
  · have hlt := Polynomial.degree_modByMonic_lt ((Polynomial.X : K[X]) ^ k) A.charpoly_monic
    rw [A.charpoly_degree_eq_dim] at hlt
    exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by simpa using hlt)

/-- [proved-derived; formal-checked] **The Cayley–Hamilton truncation of the Markov atlas.** Two
generators that share a characteristic polynomial and whose declared-port responses agree at every
time below the dimension agree at *every* time. The bound is `n`, not `2 n`: the shared
characteristic polynomial is what buys the sharper bound, and `MarkovTwoNSuffices` below is the
statement without it. -/
theorem markov_truncation {A A' : Matrix (Fin n) (Fin n) K}
    (hchar : A.charpoly = A'.charpoly)
    (C : Matrix (Fin p) (Fin n) K) (B : Matrix (Fin n) (Fin m) K)
    (h : ∀ k, k < n → markov C A B k = markov C A' B k) :
    ∀ k, markov C A B k = markov C A' B k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro k
    have : A = A' := by ext i; exact i.elim0
    rw [this]
  intro k
  have expand : ∀ (M : Matrix (Fin n) (Fin n) K) (r : K[X]), r.natDegree < n →
      C * Polynomial.aeval M r * B
        = ∑ i ∈ Finset.range n, r.coeff i • (C * M ^ i * B) := by
    intro M r hr
    rw [Polynomial.aeval_eq_sum_range' hr, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mul_smul, Matrix.smul_mul]
  have hdeg := natDegree_modByMonic_charpoly_lt A k hn
  have hA : A ^ k = Polynomial.aeval A (((Polynomial.X : K[X]) ^ k) %ₘ A.charpoly) :=
    pow_eq_aeval_modByMonic_charpoly A k
  have hA' : A' ^ k = Polynomial.aeval A' (((Polynomial.X : K[X]) ^ k) %ₘ A.charpoly) := by
    rw [hchar]; exact pow_eq_aeval_modByMonic_charpoly A' k
  simp only [markov] at h ⊢
  rw [hA, hA', expand A _ hdeg, expand A' _ hdeg]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Finset.mem_range.mp hi)]

/-- [definition] **Open.** The declared-port statement of realization theory at its classical bound:
the first `2 n` Markov parameters of two systems of dimension at most `n` determine every later
one — equivalently, two atlas-indistinguishable systems have similar minimal realizations. It is
stated here as a `Prop` and **not proved**: it needs the rank of the block Hankel matrix of the
Markov parameters and the Kalman controllable/observable decomposition, and neither is in this
file. `markov_truncation` is what *is* proved, under the extra hypothesis of a shared
characteristic polynomial and with the sharper bound `n`. -/
def MarkovTwoNSuffices (K : Type) [Field K] (n : ℕ) : Prop :=
  ∀ (m p : ℕ) (L L' : Linearization K n m p),
    (∀ k, k < 2 * n → linearizationMarkov L k = linearizationMarkov L' k) →
      ∀ k, linearizationMarkov L k = linearizationMarkov L' k

end LinearClass

/-! ### (b) The finite complexes, under the R3 + R5 atlas: **not** separating

[established-bounded; measured] The declared class is the finite one-dimensional complexes on six
occurrences with seven contacts, and the declared atlas is the one R3 and R5 actually supply for
such a complex with no configuration: the grade-0 and grade-1 Hodge spectra under the unit metric,
the integral Betti numbers with torsion, and the persistence of the dimension filtration. The
reading below is the one `crates/holonic-engine/src/receiver_atlas/tests.rs` computes exactly for
the two Laplacian-cospectral non-isomorphic graphs of
`causal_chord.rs::cospectral_graphs_are_separated_by_the_response_atlas`:

* `A`: contacts `(0,2) (0,3) (0,4) (0,5) (1,4) (1,5) (2,3)`, degree sequence `(4,2,2,2,2,2)`;
* `B`: contacts `(0,2) (0,4) (0,5) (1,2) (1,4) (1,5) (2,3)`, degree sequence `(3,3,3,2,2,1)`.

They are **not** isomorphic — the degree sequences differ — and the whole R3 + R5 atlas returns the
same reading for both. The grade-1 agreement is not a coincidence: for a one-dimensional complex
`Δ₁ = d₀ d₀*` and `Δ₀ = d₀* d₀` share every nonzero eigenvalue with multiplicity, so the grade-1
spectrum adds exactly `X^{E − V}` to the grade-0 one and no information at all. The signs alternate
because `Δ₀` is positive semidefinite; the plan's `s⁶ + 14s⁵ + 73s⁴ + 176s³ + 192s² + 72s` is the
same polynomial read on the *negative* Laplacian `A = −L` that R1 probes.

The literals here are the measured Rust readings, carried as declared data; what is *proved* here
is the logical content — that this atlas identifies two objects a richer receiver separates. -/

/-- [definition] The declared R3 + R5 reading of a finite one-dimensional complex: what the two
receivers together actually return when no configuration is supplied. Coefficients are ascending
and exact. -/
structure SpectralTopologicalReading where
  /-- Grade-0 cell count. -/
  occurrences : ℕ
  /-- Grade-1 cell count. -/
  contacts : ℕ
  /-- The characteristic polynomial of `Δ₀` under the unit metric, ascending. -/
  gradeZeroSpectrum : List ℚ
  /-- The characteristic polynomial of `Δ₁` under the unit metric, ascending. -/
  gradeOneSpectrum : List ℚ
  /-- The integral Betti numbers, by grade. -/
  betti : List ℕ
  /-- The integral torsion, by grade. -/
  torsion : List ℕ
  /-- The persistence **diagram** of the dimension filtration: the multiset of exact
  `(grade, birth, death)` *values*, `none` for an essential class. The reduction's cell *positions*
  are deliberately not recorded — every occurrence enters at `0` and every contact at `1`, so the
  order's tie-break is an artifact, and the two complexes' pair positions differ while their
  diagrams agree exactly. -/
  persistence : List (ℕ × ℚ × Option ℚ)
  deriving DecidableEq

/-- [established-bounded; measured] The R3 + R5 reading of the first graph, as
`receiver_atlas/tests.rs::the_spectral_and_topological_atlas_cannot_separate_them` measures it. -/
def firstGraphReading : SpectralTopologicalReading where
  occurrences := 6
  contacts := 7
  gradeZeroSpectrum := [0, -72, 192, -176, 73, -14, 1]
  gradeOneSpectrum := [0, 0, -72, 192, -176, 73, -14, 1]
  betti := [1, 2]
  torsion := []
  persistence :=
    [(0, 0, none), (0, 0, some 1), (0, 0, some 1), (0, 0, some 1), (0, 0, some 1),
      (0, 0, some 1), (1, 1, none), (1, 1, none)]

/-- [established-bounded; measured] And of the second, which is not isomorphic to the first. -/
def secondGraphReading : SpectralTopologicalReading where
  occurrences := 6
  contacts := 7
  gradeZeroSpectrum := [0, -72, 192, -176, 73, -14, 1]
  gradeOneSpectrum := [0, 0, -72, 192, -176, 73, -14, 1]
  betti := [1, 2]
  torsion := []
  persistence :=
    [(0, 0, none), (0, 0, some 1), (0, 0, some 1), (0, 0, some 1), (0, 0, some 1),
      (0, 0, some 1), (1, 1, none), (1, 1, none)]

/-- [proved-derived; formal-checked] The two readings are equal. -/
theorem readings_agree : firstGraphReading = secondGraphReading := by
  decide

/-- [definition] The declared class: the two graphs, named by a `Bool`. -/
def graphOf : Bool → SpectralTopologicalReading
  | false => firstGraphReading
  | true => secondGraphReading

/-- [definition] The R1 driving-point response at occurrence `0`, as the ascending coefficient list
of the numerator of `H(s)` that
`causal_chord.rs::cospectral_graphs_are_separated_by_the_response_atlas` measures exactly. -/
def drivingPointNumerator : Bool → List ℚ
  | false => [12, 46, 62, 37, 10, 1]
  | true => [12, 52, 73, 43, 11, 1]

/-- [counterexample; formal-checked] **R7(b): the R3 + R5 atlas is not separating, and that is the
result.** The coarse reading identifies two objects the R1 driving-point response separates, so the
insufficiency is an exact `Foundation/Receiver.lean::ReceiverInsufficiency` witness: it states which
receiver is missing rather than asserting that the objects are the same. -/
def spectralTopologicalInsufficiency :
    Holonics.ReceiverInsufficiency graphOf drivingPointNumerator where
  left := false
  right := true
  sameEntering := by decide
  differentReturned := by decide

/-- [proved-derived; formal-checked] Hence no receiver-to-receiver transformer carries the R3 + R5
reading into the R1 response: the richer receiver is not recoverable from the coarser one, and the
atlas has to admit it as a chart of its own. -/
theorem no_transformer_from_the_spectral_topological_reading :
    IsEmpty (Holonics.ReceiverTransformer graphOf drivingPointNumerator) :=
  ⟨fun t => t.excludesInsufficiency spectralTopologicalInsufficiency⟩

end SeparatingAtlas

/-! ## The contracts that make an atlas credible, as typed laws on a receiver -/

/-- [definition] **Rebase equivariance**: the reading is unchanged by a declared change of chart. A
receiver that fails this reads the coordinates and not the current.

Rust counterpart: `receiver_atlas.rs::AtlasContract::RebaseEquivariance`. -/
def RebaseEquivariant {X G V : Type*} (act : G → X → X) (R : X → V) : Prop :=
  ∀ g x, R (act g x) = R x

/-- [definition] **Source accountability**: every returned component is indexed by the source and
the transport path that produced it, so the reading is recoverable from its named parts and no
component is anonymous.

Rust counterpart: `receiver_atlas.rs::AtlasContract::SourceAccountability`. -/
def SourceAccountable {X S V : Type*} (R : X → V) (component : X → S → V) (recombine : (S → V) → V) :
    Prop :=
  ∀ x, recombine (component x) = R x

/-- [definition] **Declaration independence**: the reading does not depend on a supplied structure
that the doctrine says it must not — R3's harmonic dimension is the worked case, and it must not
depend on which positive metric was supplied.

Rust counterpart: `receiver_atlas.rs::AtlasContract::DeclarationIndependence`, whose R3 row is
recomputed by `receiver_atlas.rs::verify_r3_metric_free_harmonic_dimension`. It is a *different*
contract from `RebaseEquivariant`: a change of chart and a change of supplied structure are two
statements, and R3 discharges the second and not the first. -/
def DeclarationIndependent {D X V : Type*} (R : D → X → V) : Prop :=
  ∀ d d' x, R d x = R d' x

/-- [proved-derived; formal-checked] **R1 satisfies rebase equivariance, in Lean.** The causal
chord's transfer object is invariant under the chart change `(A, B, C) ↦ (T A T⁻¹, T B, C T⁻¹)`,
which is `Foundation/CausalChord.lean::rebase_transfer`. This is the one contract of the five that
is already a kernel-checked theorem; the rest are verified executably in
`receiver_atlas.rs::contract_ledger` and the ones that are neither are named `Unproved` there. -/
theorem causalChord_is_rebase_equivariant (K : Type) [Field K] (n m p : ℕ) :
    RebaseEquivariant
      (fun (T : (Matrix (Fin n) (Fin n) K)ˣ)
        (L : Holonics.Foundation.CausalChord.Linearization K n m p) =>
          Holonics.Foundation.CausalChord.Linearization.rebase T L)
      Holonics.Foundation.CausalChord.Linearization.transfer :=
  fun T L => Holonics.Foundation.CausalChord.Linearization.rebase_transfer T L


end Holonics.Foundation.Atlas

section Audit
open Holonics.Foundation.Atlas

#print axioms no_operation_from_the_carrier_alone
#print axioms operation_is_supplied_not_conferred
#print axioms LocalChart.preimageFibre_subset_fibre
#print axioms LocalChart.reading_none_of_metric_none
#print axioms LocalChart.reading_isSome_of_metric_isSome
#print axioms cocycle_iff_isEmpty_defect
#print axioms CocycleDefect.routed_reopens
#print axioms CocycleDefect.direct_reopens
#print axioms CocycleDefect.defect_is_holonomy_not_loss
#print axioms coarseGrain_cocycle
#print axioms coarseGrainDefect
#print axioms coarseGrain_not_cocycle
#print axioms ChartTransition.residual_reopens
#print axioms ChartTransition.later_receiver_factors
#print axioms CoherentPlacement.ext
#print axioms atlasGluing_total
#print axioms no_coherentPlacement_through_defect
#print axioms atlasGluing_obstructed_of_total_defect
#print axioms ChartCocycle.self_id
#print axioms ChartCocycle.placementEquiv
#print axioms ChartCocycle.nonempty_placement
#print axioms ShiftAtlas.tailChart_region_nonempty
#print axioms ShiftAtlas.tailChart_coordinate_nonempty
#print axioms ShiftAtlas.shiftAtlasSection
#print axioms ShiftAtlas.theEmbeddingIsNotOneVector
#print axioms ShiftAtlas.shiftAtlas_gluing
#print axioms ShiftAtlas.shiftAtlas_not_invertible
#print axioms ShiftAtlas.shiftAtlas_residual_separates
#print axioms twoCharts_comparison_undefined
#print axioms AtlasRefinement.refl
#print axioms indistinguishable_factors
#print axioms indistinguishable_transports
#print axioms indistinguishable_of_refinement
#print axioms SeparatingAtlas.coarse_cannot_separate
#print axioms SeparatingAtlas.rich_separates
#print axioms SeparatingAtlas.no_transformer_from_the_blind_chart
#print axioms Separates.mono
#print axioms Separates.of_refinement
#print axioms SeparatingAtlas.identity_probe_determines_the_operator
#print axioms SeparatingAtlas.fullProbeAtlas_separates
#print axioms SeparatingAtlas.pow_eq_aeval_modByMonic_charpoly
#print axioms SeparatingAtlas.natDegree_modByMonic_charpoly_lt
#print axioms SeparatingAtlas.markov_truncation
#print axioms SeparatingAtlas.readings_agree
#print axioms SeparatingAtlas.spectralTopologicalInsufficiency
#print axioms SeparatingAtlas.no_transformer_from_the_spectral_topological_reading
#print axioms causalChord_is_rebase_equivariant
end Audit
