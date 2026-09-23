import ElementaryHolonics.Foundation.Holon
import ElementaryHolonics.Foundation.Receiver
import ElementaryHolonics.Foundation.SectionResidual
import ElementaryHolonics.Foundation.ReceiverHistoryCompression
import ElementaryHolonics.Foundation.GluingPassage
import ElementaryHolonics.Millennium.HolonicDirectedPassage

/-!
# The continuing tower and the non-invertible transition that carries its residual

[definition] This file deposits the carrier named in
`docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md` items **C1**, **C3** and **C4**:
a `Tower` of faces over a refinement preorder, its `CompatibleSection`s, the `ObservationFibre`
behind one materialized face, the three lawful returns `GluingResult`, the `MaterializedFace` that
carries its lineage, the `ComputableTower` that materializes faces from one state, and the
`Transition` between charts that need not be invertible and carries the residual it does not
transport.

## Rust counterpart

[definition] The paired executable owner is `crates/holonic-core/src/restriction/tower.rs` (the Holon
core's restriction facet; `crates/holonic-engine/src/continuing_tower.rs` re-exports it). Its
types carry the same names — `Tower`, `CompatibleSection`, `ObservationFibre`, `GluingResult`,
`MaterializedFace`, `ComputableTower`, `Transition` — over exact arithmetic
(`relational_geometry::Rat`, `num_bigint::BigInt`), with `restrict_refl` and `restrict_trans`
returned as checked receipts rather than assumed, and with the `padicTower`, `shiftTower` and
`coarseGrain` witnesses below mirrored as unit tests. Each Rust item names the declaration here that
it realizes; the correspondence is bidirectional and is the deliverable.

## How this joins the families already owned

[established-bounded; source-inspected] This is **not** a parallel family.

* `Millennium/HolonicDirectedPassage.lean:260-306`'s `SuccessorWitnessSystem` owns the *existence*
  law: inhabited base plus surjective adjacent restriction constructs a coherent history through
  all depths. A `Tower` over `ℕ` restricts along every `i ≤ j`, not only `n ≤ n + 1`; the two are
  joined by `Tower.compatible_of_adjacent` (adjacent compatibility already implies compatibility at
  every gap) and `Tower.nonempty_compatibleSection_of_surjectiveAdjacent`, which *calls*
  `SuccessorWitnessSystem.nonempty_coherentSection` instead of reproving it.
* `Foundation/GluingPassage.lean` owns the generic `GluingPassage` and its *obstruction
  population*; `Millennium/Gluing.lean` keeps additive and named research passages.
  `Tower.gluingPassage` presents a tower at one chart as that passage, and
  `Tower.carried_iff_observationFibre` identifies its `Carried` predicate with inhabitation of the
  `ObservationFibre`. `Tower.obstruction_nonempty_iff` is therefore the tower's obstruction read
  through the existing owner, and `shiftTower_not_glues` is discharged by
  `GluingPassage.not_glues_iff_obstruction_nonempty`.
* `Millennium/HolonicDirectedPassage.lean:311-330`'s `boolFlipCoherent_isEmpty` owns the *loop*
  obstruction. `Tower.restrict_self_eq_id` shows a tower cannot carry it: `restrict_refl` forces
  every one-chart restriction to be the identity, and `restrict_roundTrip` forces every index loop
  to be coherent. `boolFlipSelfLoop_isEmpty` therefore *cites* that owner rather than building a
  second obstruction.
* `Foundation/Holon.lean:88-89`'s `PreimageFibre` owns the *retained population behind one face*.
  **C3 holds definitionally**: `Tower.observationFibre_eq_preimageFibre` is `rfl`.
* `Foundation/Receiver.lean:132-178`'s descent criterion and `ReceiverInsufficiency` own the
  *coarse-to-fine* question; `Tower.chartReceiverTransformer_iff` is that criterion at two charts.
* `Foundation/SectionResidual.lean:17-34` owns the *linear* residual;
  `Transition.ofLinearSection` exhibits it as one instance of the general transition, so the linear
  restriction is dropped rather than duplicated.
* `Foundation/ReceiverHistoryCompression.lean:43-45`'s `generatorExact` owns the *dynamic* law;
  `Transition.toReceiverHistoryCompression` builds that owner from an equivariant transition, and
  `Transition.apply_transportWord` is its every-ordered-word consequence, not a new induction.

## The first physical consumer

[definition] `Foundation/GrainRestriction.lean` instantiates `Tower` and `Transition` at the grain
axis `component ⊑ residue ⊑ atom` of a physical presentation, with
`crates/holonic-engine/src/grain_tower.rs` as its executable owner. It adds no carrier machinery: it
*uses* `restrictTransition`, `reopen_apply`, `laterReceiverFactors` and `residual_separates`, and it
settles, against `Foundation/AperturedGradedComplex.lean`'s open class, that a residual and an
undecided reading are two objects (`open_admission_is_not_a_residual`,
`grain_residual_and_open_class_are_two_objects`).

## The tube this tower is the transverse section of

[established-bounded; formal-checked] A `Tower` is one axis of a two-axis object. `Transport/`
`ContinuingTube.lean` joins it to `Transport/WorldTube.lean`'s `ClockedSpan`: a **tube** is a family
of towers along a longitudinal station axis, the tower is its transverse cross-sectional ladder, and
the one law joining the axes is that longitudinal transport and transverse restriction commute —
which is `Migration.naturality` with the identity index map (`ChartwiseMigration` is proved there to
be exactly a `Migration` that `StaysAtItsChart`). That file also fixes **wormhole** as
`Migration.ConnectsIncomparableCharts` on the two-axis object, proves a tube's own passages never
are, and extends `restrict_roundTrip` to the longitudinal axis: neither axis of a functorial tube
carries holonomy, so the loop obstruction stays with `Foundation/ReceiverAtlas.lean::CocycleDefect`.
Nothing in this file is changed by that join; it composes what is here.

## C2 and the `Migration` functor

[definition] This file also carries item **C2** and the `Migration` half of item **C4**.
`padicSectionEquiv` proves `ℤ_[p] ≃ Tower.CompatibleSection` in both directions through Mathlib's
`PadicInt.toZModPow` and `PadicInt.ofIntSeq`, and `padicFibreEquiv`/`padicFibre_card` prove the
*exact* splitting: the fibre over a level-`m` face is in bijection with `ZMod (p ^ k)` at level
`m + k`, so one refinement step splits it into exactly `p` cosets of
`RingHom.ker (PadicInt.toZModPow (n+1))`, and `padic_sameFace_iff_sub_mem_ker` identifies the fibre
with a coset of `Ideal.span {p ^ n}` using Mathlib's `PadicInt.ker_toZModPow`. `Migration` is the
functor of index categories with its natural transformation on faces; `rebaseMigration` exhibits
`Foundation/Holon.lean`'s `Rebase` as the invertible instance rather than founding a second notion,
and `ResidualMigration.ofTransitionFamily`/`ResidualMigration.transition` prove that a residual
migration is exactly an index functor together with a family of `Transition`s satisfying naturality.

[definition] Two further separations are proved about `Migration`, because a tower on its own cannot
express either. **Non-factoring:** a tower's passage follows refinement and nothing else, so between
incomparable charts it has none, and a common refinement supplies none either — a span is not a map.
`Migration.ConnectsIncomparableCharts` names the migrations that cross that gap;
`Migration.FactorsThroughRefinement` names the ones that do not, and
`not_factorsThroughRefinement_of_connectsIncomparableCharts` separates them. `swapMigration` over
`twoCharts_no_common_refinement`'s discrete index has the property, and `rebaseMigration` and
`padicHalfMigration` do not — so the condition is neither vacuous nor universal.
**Traversability:** `ResidualMigration.traversability_is_the_residual` proves that the reverse
passage from the migrated face alone exists exactly when the component is injective, and that the
retained residual restores it exactly otherwise. `Migration.CostBoundedByRefinementRoute` states the
shape of the cost comparison over a caller-supplied ordered cost; `Foundation/PresentationCost.lean`
owns C5, proves that shape caller-decided (`costBoundedByRefinementRoute_is_caller_decided`) and
discharges it over every `CostedTower` (`costBoundedByRefinementRoute_of_route`). Costed towers
exist: `PresentationCost.padicCostedTower` puts the receipts its own restrictions determine on
`padicTower`, `unitCostedTower` is the minimal one, and
`costBoundedByRefinementRoute_padic` is the comparison discharged at `padicHalfMigration` with
neither side supplied by a caller. The law is not automatic either —
`PresentationCost.no_costedTower_with_squaredGapReceipt` is a receipt assignment no costed tower
can carry.

[definition] `Foundation/ReceiverCodeCost.lean:100-126`'s `serial_boundary_balance` owns item
**C5**'s additivity law — serial code costs add with the endpoint potentials cancelling at the
joined boundary. It is cited, never rebuilt here; this file deposits no cost law of its own beyond
`ComputableTower.cost`.

[definition] What this file does **not** do: it states no milestone and schedules nothing.
-/

namespace Soma.Holonics.Foundation.ContinuingTower

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.Chronology
open Soma.Holonics.Millennium.HolonicDirectedPassage
open Soma.Holonics.Millennium.LineageCompression

universe u v w

/-! ## C1 — the tower -/

/-- [definition] A **tower**: a family of faces over a refinement preorder together with the
restriction that carries a finer face to the coarser one it presents.

`Index` is the index of apertures, grains, charts, precisions and environments; `Face i` is what is
actually presented at index `i`; `restrict` is the only transport, and it is directed from finer to
coarser. `restrict_refl` and `restrict_trans` are the two laws — no face is the object, and the
object is exactly this family plus these laws.

Rust counterpart: `crates/holonic-core/src/restriction/tower.rs::Tower`. -/
structure Tower (Index : Type u) [Preorder Index] where
  /-- The face actually presented at one index. -/
  Face : Index → Type v
  /-- Carry a finer face to the coarser index it refines. -/
  restrict : ∀ {i j : Index}, i ≤ j → Face j → Face i
  /-- Restricting to the same index changes nothing. -/
  restrict_refl : ∀ (i : Index) (x : Face i), restrict (le_refl i) x = x
  /-- Restricting twice is restricting once along the composite refinement. -/
  restrict_trans : ∀ {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k) (x : Face k),
    restrict hij (restrict hjk x) = restrict (le_trans hij hjk) x

namespace Tower

variable {Index : Type u} [Preorder Index] (T : Tower.{u, v} Index)

/-- [definition] `Refines i j` is the index order read in its construction sense: `j` refines `i`,
so a face at `j` restricts to a face at `i`. The Rust owner carries this relation explicitly
because it has no preorder class to lean on. -/
abbrev Refines (i j : Index) : Prop := i ≤ j

/-- [definition] A **compatible section**: one witness at every index, agreeing under every
restriction. This is the continuing object itself, not any one of its faces.

Rust counterpart: `continuing_tower.rs::CompatibleSection`. -/
structure CompatibleSection where
  /-- The face this object presents at each index. -/
  witness : ∀ i, T.Face i
  /-- Every coarser face is the restriction of every finer one. -/
  compatible : ∀ {i j : Index} (h : i ≤ j), T.restrict h (witness j) = witness i

/-- [definition] The **observation fibre** behind one actually materialized face: every compatible
section that presents exactly that face at that chart. A plural fibre is the ordinary case.

Rust counterpart: `continuing_tower.rs::ObservationFibre`. -/
def ObservationFibre (i : Index) (face : T.Face i) : Type _ :=
  { s : T.CompatibleSection // s.witness i = face }

/-- [definition] The three lawful returns of an attempted global section. A tower whose levels are
all inhabited may still admit no coherent section; that obstruction is returned, never resolved by
choosing a representative.

Rust counterpart: `continuing_tower.rs::GluingResult`. -/
inductive GluingResult : Prop
  /-- Exactly one continuing object. -/
  | unique (h : Nonempty T.CompatibleSection) (hs : Subsingleton T.CompatibleSection)
  /-- Several continuing objects; the plurality is the content and is not collapsed. -/
  | plural (h : Nonempty T.CompatibleSection) (hp : ¬ Subsingleton T.CompatibleSection)
  /-- No continuing object at all, although every level may be inhabited. -/
  | obstructed (h : IsEmpty T.CompatibleSection)

/-- [proved-derived; formal-checked] Every tower lands in exactly one arm: the trichotomy is total.
-/
theorem gluingResult_total : T.GluingResult := by
  classical
  by_cases h : Nonempty T.CompatibleSection
  · by_cases hs : Subsingleton T.CompatibleSection
    · exact .unique h hs
    · exact .plural h hs
  · exact .obstructed (not_nonempty_iff.mp h)

/-- [definition] A **materialized face** carries its chart, the face, and the lineage of continuing
objects behind it. A face without its observation fibre is not admitted.

Rust counterpart: `continuing_tower.rs::MaterializedFace`. -/
structure MaterializedFace where
  /-- Where the face was read. -/
  chart : Index
  /-- What was read. -/
  face : T.Face chart
  /-- The retained population behind it. -/
  lineage : T.ObservationFibre chart face

/-- [proved-derived; formal-checked] A tower's one-chart restriction is the identity. Proof
irrelevance makes every `h : i ≤ i` the reflexive one, so `restrict_refl` already decides it. -/
theorem restrict_self_eq_id {i : Index} (h : i ≤ i) (x : T.Face i) : T.restrict h x = x :=
  T.restrict_refl i x

/-- [proved-derived; formal-checked] Every loop in the index preorder is automatically coherent:
a round trip is the identity. The tower carrier therefore *cannot* express loop holonomy, which is
why the loop obstruction stays with its existing owner. -/
theorem restrict_roundTrip {i j : Index} (hij : i ≤ j) (hji : j ≤ i) (x : T.Face i) :
    T.restrict hij (T.restrict hji x) = x := by
  rw [T.restrict_trans hij hji x]
  exact T.restrict_refl i x

end Tower

/-- [definition] A **computable tower**: one state from which every chart's face is materialized on
demand, together with the law that materialization commutes with restriction, and the work the
materialization costs.

Rust counterpart: `continuing_tower.rs::ComputableTower`. -/
structure ComputableTower (Index : Type u) [Preorder Index] extends Tower.{u, v} Index where
  /-- The retained state the faces are generated from. -/
  State : Type u
  /-- Generate the face at one chart. -/
  materialize : State → ∀ i, Face i
  /-- Demand-driven generation agrees with restriction: no chart is privileged. -/
  materialize_compatible : ∀ (s : State) {i j : Index} (h : i ≤ j),
    restrict h (materialize s j) = materialize s i
  /-- The declared work of materializing one chart. -/
  cost : State → Index → ℕ

/-- [proved-derived; formal-checked] A computable tower supplies a compatible section for every
state: generation from a state is one continuing object, not a family of unrelated faces.

Rust counterpart: `continuing_tower.rs::ComputableTower::section`. -/
def ComputableTower.section {Index : Type u} [Preorder Index]
    (C : ComputableTower.{u, v} Index) (s : C.State) : C.toTower.CompatibleSection where
  witness := C.materialize s
  compatible := fun h => C.materialize_compatible s h

/-! ## C1 — the join to `SuccessorWitnessSystem`

The existing owner restricts only along `n ≤ n + 1`. These two declarations show that is no loss
for a tower over `ℕ`, and then call it. -/

namespace Tower

variable {Index : Type u} [Preorder Index] (T : Tower.{u, v} Index)

/-- [proved-derived; formal-checked] Adjacent compatibility already implies compatibility at every
gap. This is the exact statement that `SuccessorWitnessSystem.CoherentSection` and
`Tower.CompatibleSection` are the same obligation over `ℕ`. -/
theorem compatible_of_adjacent (T : Tower.{0, v} ℕ) (w : ∀ n, T.Face n)
    (hadj : ∀ n, T.restrict (Nat.le_succ n) (w (n + 1)) = w n) :
    ∀ {i j : ℕ} (h : i ≤ j), T.restrict h (w j) = w i := by
  intro i j h
  induction j, h using Nat.le_induction with
  | base => exact T.restrict_refl i (w i)
  | succ n hn ih =>
    calc T.restrict (Nat.le_succ_of_le hn) (w (n + 1))
        = T.restrict hn (T.restrict (Nat.le_succ n) (w (n + 1))) :=
          (T.restrict_trans hn (Nat.le_succ n) (w (n + 1))).symm
      _ = T.restrict hn (w n) := by rw [hadj n]
      _ = w i := ih

/-- [proved-derived; formal-checked] An inhabited base and surjective adjacent restrictions give a
tower over `ℕ` a compatible section. The construction is
`Millennium/HolonicDirectedPassage.lean`'s `SuccessorWitnessSystem.nonempty_coherentSection`; only
the gap-filling is new. -/
theorem nonempty_compatibleSection_of_surjectiveAdjacent (T : Tower.{0, v} ℕ)
    (hbase : Nonempty (T.Face 0))
    (hsurj : ∀ n, Function.Surjective fun x : T.Face (n + 1) => T.restrict (Nat.le_succ n) x) :
    Nonempty T.CompatibleSection := by
  let system : SuccessorWitnessSystem.{v} :=
    { Fibre := T.Face
      restrict := fun n x => T.restrict (Nat.le_succ n) x
      baseNonempty := hbase
      restrict_surjective := hsurj }
  obtain ⟨coherent⟩ := system.nonempty_coherentSection
  exact ⟨{ witness := coherent.witness
           compatible := T.compatible_of_adjacent coherent.witness coherent.compatible }⟩

/-! ## C1 — the join to `GluingPassage` -/

/-- [definition] A tower read at one chart as a generic gluing passage: the
candidates are the faces actually available at that chart, the realizers are the continuing objects,
and realization is materialization. Local admissibility at a single chart is total — an actual face
is locally admissible by construction — so the whole content sits in the obstruction population. -/
def gluingPassage (i : Index) : GluingPassage.{v, max u v} where
  Candidate := T.Face i
  Realizer := T.CompatibleSection
  realize := fun s => s.witness i
  LocallyAdmissible := fun _ => True
  realized_is_admissible := fun _ => trivial

/-- [proved-derived; formal-checked] `GluingPassage.Carried` at a chart is exactly inhabitation of
the tower's observation fibre. The two vocabularies name one object. -/
theorem carried_iff_observationFibre (i : Index) (c : T.Face i) :
    (T.gluingPassage i).Carried c ↔ Nonempty (T.ObservationFibre i c) := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨⟨s, hs⟩⟩
  · rintro ⟨⟨s, hs⟩⟩
    exact ⟨s, hs⟩

/-- [proved-derived; formal-checked] The passage glues at a chart exactly when every face there has
an inhabited observation fibre. -/
theorem gluingPassage_glues_iff (i : Index) :
    (T.gluingPassage i).Glues ↔ ∀ c : T.Face i, Nonempty (T.ObservationFibre i c) := by
  constructor
  · intro h c
    exact (T.carried_iff_observationFibre i c).mp (h c trivial)
  · intro h c _
    exact (T.carried_iff_observationFibre i c).mpr (h c)

/-- [proved-derived; formal-checked] The obstruction population at a chart is inhabited exactly
when some face there has an empty observation fibre. The tower's obstruction is the existing
`GluingPassage.Obstruction`, not a second object. -/
theorem obstruction_nonempty_iff (i : Index) :
    Nonempty (T.gluingPassage i).Obstruction ↔ ∃ c : T.Face i, IsEmpty (T.ObservationFibre i c) := by
  constructor
  · rintro ⟨⟨c, _, hnc⟩⟩
    exact ⟨c, not_nonempty_iff.mp fun h => hnc ((T.carried_iff_observationFibre i c).mpr h)⟩
  · rintro ⟨c, hc⟩
    exact ⟨⟨c, trivial, fun hcar => hc.false ((T.carried_iff_observationFibre i c).mp hcar).some⟩⟩

end Tower

/-! ## C3 — the observation fibre *is* the preimage fibre

`Foundation/Holon.lean:88-89` already owns "every occurrence retained behind one returned receiver
face". The restrict-to-chart receiver is the holon whose occurrence population is the continuing
objects and whose returned face is the materialized one. The identification is definitional. -/

namespace Tower

variable {Index : Type u} [Preorder Index] (T : Tower.{u, v} Index)

/-- [definition] The restrict-to-chart receiver as an elementary holon: the occurrence population is
the tower's continuing objects, the outgoing port and the returned face are both the face
materialized at that chart. -/
def chartHolon (i : Index) : Holon.{0, v, v, max u v} Unit (T.Face i) (T.Face i) where
  Occurrence := T.CompatibleSection
  source := fun _ => ()
  target := fun s => s.witness i
  receive := fun s => s.witness i

/-- [proved-derived; formal-checked] **C3.** The tower's observation fibre and the repository's
existing preimage fibre are the same type, definitionally. There is no discrepancy to document and
no identification to force: `rfl` discharges it. -/
theorem observationFibre_eq_preimageFibre (i : Index) (face : T.Face i) :
    T.ObservationFibre i face = (T.chartHolon i).PreimageFibre face := rfl

/-- [proved-derived; formal-checked] The same identification as a transport, for callers that need
a map rather than an equality of types. -/
def observationFibreEquivPreimageFibre (i : Index) (face : T.Face i) :
    T.ObservationFibre i face ≃ (T.chartHolon i).PreimageFibre face :=
  Equiv.refl _

/-- [proved-derived; formal-checked] `Foundation/Receiver.lean`'s descent criterion at two charts:
the coarse chart determines the fine chart exactly when it never merges two continuing objects that
the fine chart separates. -/
theorem chartReceiverTransformer_iff (i j : Index) :
    Nonempty (ReceiverTransformer (fun s : T.CompatibleSection => s.witness i)
      (fun s : T.CompatibleSection => s.witness j)) ↔
      ∀ s t : T.CompatibleSection, s.witness i = t.witness i → s.witness j = t.witness j :=
  receiverTransformer_exists_iff _ _

end Tower

/-! ## C4 — the non-invertible transition that carries its residual

Every formal chart map deposited before this file is invertible. A `Transition` is not: it carries
the part of the source it does not transport, as data, together with the reopening that uses it. -/

/-- [definition] A **transition** between charts that need not be invertible, carrying its residual.

`apply` is what the transition transports. `residual` is what it does not: the part of the source
the target face no longer sees. `reopen` is the executable reconstruction, and `reopen_apply` is the
law that makes the residual *exactly* the dropped part — not an upper bound, not a score.

Outside the image of `apply`, `reopen` returns whatever the constructor supplies; only presented
pairs `(apply x, residual x)` carry the law, in the same sense as
`Foundation/Receiver.lean`'s `ReceiverTransformer` domain.

Rust counterpart: `crates/holonic-core/src/restriction/tower.rs::Transition`. -/
structure Transition (Source : Type u) (Target : Type v) where
  /-- The part of the source the transition does not transport. -/
  Residual : Type w
  /-- What the transition transports. -/
  apply : Source → Target
  /-- What it drops, retained. -/
  residual : Source → Residual
  /-- Reconstruct a source from a transported face and the retained residual. -/
  reopen : Target → Residual → Source
  /-- The transported face together with the residual is exactly the source. -/
  reopen_apply : ∀ x, reopen (apply x) (residual x) = x

namespace Transition

variable {Source : Type u} {Middle : Type v} {Target : Type w}

/-- [proved-derived; formal-checked] The pair `(apply, residual)` is faithful: nothing is lost that
is not in the residual. -/
theorem apply_residual_injective (f : Transition Source Target) {x y : Source}
    (ha : f.apply x = f.apply y) (hr : f.residual x = f.residual y) : x = y := by
  have hx := f.reopen_apply x
  rw [ha, hr, f.reopen_apply y] at hx
  exact hx.symm

/-- [proved-derived; formal-checked] **The residual is exactly what a later finer receiver can
reopen (sufficiency).** *Every* later receiver on the source factors through the transported face
paired with the residual. -/
theorem laterReceiverFactors (f : Transition Source Target) {Fine : Type*} (finer : Source → Fine) :
    ∃ recover : Target → f.Residual → Fine, ∀ x, recover (f.apply x) (f.residual x) = finer x :=
  ⟨fun t r => finer (f.reopen t r), fun x => congrArg finer (f.reopen_apply x)⟩

/-- [proved-derived; formal-checked] **The residual is exactly what a later finer receiver can
reopen (necessity).** Any distinction a later receiver makes that the transported face has lost is
carried by the residual. -/
theorem residual_separates (f : Transition Source Target) {Fine : Type*} (finer : Source → Fine)
    {x y : Source} (hsame : f.apply x = f.apply y) (hdiff : finer x ≠ finer y) :
    f.residual x ≠ f.residual y := by
  intro hr
  exact hdiff (congrArg finer (f.apply_residual_injective hsame hr))

/-- [proved-derived; formal-checked] `Foundation/Receiver.lean`'s insufficiency witness is exactly a
residual difference: the transition's own record of what it dropped refutes it. -/
theorem residual_separates_insufficiency (f : Transition Source Target) {Fine : Type*}
    {finer : Source → Fine} (witness : ReceiverInsufficiency f.apply finer) :
    f.residual witness.left ≠ f.residual witness.right :=
  f.residual_separates finer witness.sameEntering witness.differentReturned

/-! ### An invertible transition has zero residual -/

/-- [definition] An invertible chart map read as a transition. The residual is `PUnit`: there is
nothing left over. -/
def ofEquiv (e : Source ≃ Target) : Transition Source Target where
  Residual := PUnit
  apply := e
  residual := fun _ => PUnit.unit
  reopen := fun t _ => e.symm t
  reopen_apply := fun x => e.symm_apply_apply x

/-- [proved-derived; formal-checked] An invertible transition has zero residual. -/
theorem ofEquiv_residual_subsingleton (e : Source ≃ Target) :
    Subsingleton (ofEquiv e).Residual :=
  ⟨fun _ _ => rfl⟩

/-- [proved-derived; formal-checked] The converse direction: zero residual forces the transported
map to be injective, so nothing was dropped. -/
theorem injective_of_subsingleton_residual (f : Transition Source Target)
    (h : Subsingleton f.Residual) : Function.Injective f.apply :=
  fun _ _ hxy => f.apply_residual_injective hxy (h.elim _ _)

/-- [proved-derived; formal-checked] Zero residual plus surjectivity is invertibility: the two
descriptions of "loses nothing" agree. -/
noncomputable def equivOfSubsingletonResidual (f : Transition Source Target)
    (h : Subsingleton f.Residual) (hs : Function.Surjective f.apply) : Source ≃ Target :=
  Equiv.ofBijective f.apply ⟨f.injective_of_subsingleton_residual h, hs⟩

/-- [definition] Any injective chart map carries a zero residual, so "invertible" is not needed:
injectivity is the exact condition for a `PUnit` residual. -/
noncomputable def ofInjective [Nonempty Source] (g : Source → Target)
    (hg : Function.Injective g) : Transition Source Target where
  Residual := PUnit
  apply := g
  residual := fun _ => PUnit.unit
  reopen := fun t _ => Function.invFun g t
  reopen_apply := fun x => Function.leftInverse_invFun hg x

/-! ### Composition composes residuals -/

/-- [definition] Composition of transitions. The composite residual is the pair: what the second
transition dropped about the already-transported face, and what the first dropped. Reopening runs
backwards through both.

Rust counterpart: `continuing_tower.rs::Transition::compose`. -/
def comp (second : Transition Middle Target) (first : Transition Source Middle) :
    Transition Source Target where
  Residual := second.Residual × first.Residual
  apply := fun x => second.apply (first.apply x)
  residual := fun x => (second.residual (first.apply x), first.residual x)
  reopen := fun t r => first.reopen (second.reopen t r.1) r.2
  reopen_apply := fun x => by
    show first.reopen (second.reopen (second.apply (first.apply x))
      (second.residual (first.apply x))) (first.residual x) = x
    rw [second.reopen_apply, first.reopen_apply]

@[simp] theorem comp_apply (second : Transition Middle Target) (first : Transition Source Middle)
    (x : Source) : (comp second first).apply x = second.apply (first.apply x) := rfl

/-- [proved-derived; formal-checked] **Composition composes residuals.** The composite's residual is
exactly the two component residuals, in the order they were dropped. -/
@[simp] theorem comp_residual (second : Transition Middle Target)
    (first : Transition Source Middle) (x : Source) :
    (comp second first).residual x = (second.residual (first.apply x), first.residual x) := rfl

/-- [proved-derived; formal-checked] Composing two zero-residual transitions drops nothing. -/
theorem comp_residual_subsingleton (second : Transition Middle Target)
    (first : Transition Source Middle)
    (hs : Subsingleton second.Residual) (hf : Subsingleton first.Residual) :
    Subsingleton (comp second first).Residual := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  rw [hs.elim a₁ b₁, hf.elim a₂ b₂]

/-- [proved-derived; formal-checked] Composition is associative on the transported face. -/
theorem comp_assoc_apply {Target' : Type*} (third : Transition Target Target')
    (second : Transition Middle Target) (first : Transition Source Middle) (x : Source) :
    (comp (comp third second) first).apply x = (comp third (comp second first)).apply x := rfl

/-- [proved-derived; formal-checked] Composition is associative on the residual, up to the
reassociation of the pair, and the reassociation carries the residual itself. -/
def compAssocResidualEquiv {Target' : Type*} (third : Transition Target Target')
    (second : Transition Middle Target) (first : Transition Source Middle) :
    (comp (comp third second) first).Residual ≃ (comp third (comp second first)).Residual :=
  Equiv.prodAssoc third.Residual second.Residual first.Residual

theorem compAssocResidualEquiv_residual {Target' : Type*} (third : Transition Target Target')
    (second : Transition Middle Target) (first : Transition Source Middle) (x : Source) :
    compAssocResidualEquiv third second first ((comp (comp third second) first).residual x) =
      (comp third (comp second first)).residual x := rfl

/-! ### The linear owner is one instance

`Foundation/SectionResidual.lean` proves the same reconstruction for a linear receiver with a chosen
section. Its `source_reconstructs` *is* `reopen_apply`; the transition drops the linearity and the
`ℝ`-module structure and keeps the law. -/

/-- [definition] `Foundation/SectionResidual.lean`'s linear receiver plus a chosen section is a
transition whose residual is the receiver-blind remainder. -/
def ofLinearSection {E Q : Type*} [AddCommGroup E] [AddCommGroup Q] [Module ℝ E] [Module ℝ Q]
    (q : E →ₗ[ℝ] Q) (s : SectionResidual.Section q) : Transition E Q where
  Residual := E
  apply := q
  residual := SectionResidual.remainder s
  reopen := fun a r => s.value a + r
  reopen_apply := SectionResidual.source_reconstructs s

/-- [proved-derived; formal-checked] The residual of the linear instance is receiver-blind, which is
`SectionResidual.receiver_remainder_zero` restated on the transition. -/
theorem ofLinearSection_residual_receiverBlind {E Q : Type*} [AddCommGroup E] [AddCommGroup Q]
    [Module ℝ E] [Module ℝ Q] (q : E →ₗ[ℝ] Q) (s : SectionResidual.Section q) (x : E) :
    q ((ofLinearSection q s).residual x) = 0 :=
  SectionResidual.receiver_remainder_zero s x

/-! ### The dynamic law is the existing owner

`Foundation/ReceiverHistoryCompression.lean:43-45` owns `generatorExact`. An equivariant transition
*is* such a compression, so its every-ordered-word law is inherited, not reproved. -/

/-- [definition] An equivariant transition presented as the existing receiver/history compression,
with the transition's own transported face as both the quotient and the receiver. -/
def toReceiverHistoryCompression {Generator : Type*} (f : Transition Source Target)
    (sourceTransport : Generator → Source → Source)
    (targetTransport : Generator → Target → Target)
    (equivariant : ∀ g x, f.apply (sourceTransport g x) = targetTransport g (f.apply x)) :
    ReceiverHistoryCompression Generator Unit Source Target Target where
  present :=
    { quotient := f.apply
      receiver := fun _ => f.apply
      factor := fun _ => id
      exact := fun _ _ => rfl }
  sourceTransport := sourceTransport
  quotientTransport := targetTransport
  generatorExact := equivariant

/-- [proved-derived; formal-checked] An equivariant transition transports every ordered, possibly
noncommuting generator word. The proof is
`ReceiverHistoryCompression.quotientCommutesWithEveryOrderedWord`; no second induction is
introduced. -/
theorem apply_transportWord {Generator : Type*} (f : Transition Source Target)
    (sourceTransport : Generator → Source → Source)
    (targetTransport : Generator → Target → Target)
    (equivariant : ∀ g x, f.apply (sourceTransport g x) = targetTransport g (f.apply x))
    (word : List Generator) (x : Source) :
    f.apply (transportWord sourceTransport word x) =
      transportWord targetTransport word (f.apply x) :=
  (f.toReceiverHistoryCompression sourceTransport targetTransport
    equivariant).quotientCommutesWithEveryOrderedWord word x

/-- [proved-derived; formal-checked] The residual survives the dynamics: after any ordered word, the
transported face together with the residual still reopens the exact transported source. -/
theorem residual_reopens_after_word {Generator : Type*} (f : Transition Source Target)
    (sourceTransport : Generator → Source → Source)
    (targetTransport : Generator → Target → Target)
    (equivariant : ∀ g x, f.apply (sourceTransport g x) = targetTransport g (f.apply x))
    (word : List Generator) (x : Source) :
    f.reopen (transportWord targetTransport word (f.apply x))
        (f.residual (transportWord sourceTransport word x)) =
      transportWord sourceTransport word x := by
  rw [← f.apply_transportWord sourceTransport targetTransport equivariant word x]
  exact f.reopen_apply _

end Transition

/-! ### The tower's own restrictions are the canonical non-invertible transitions -/

namespace Tower

variable {Index : Type u} [Preorder Index] (T : Tower.{u, v} Index)

/-- [definition] A tower restriction presented as a transition. The residual must be *supplied*: the
tower's laws say what restriction preserves, never what it drops, so the dropped part is data a
caller deposits and not something the tower can synthesize.

Rust counterpart: `continuing_tower.rs::Tower::restrict_transition`. -/
def restrictTransition {i j : Index} (h : i ≤ j) (Residual : Type w)
    (residual : T.Face j → Residual) (reopen : T.Face i → Residual → T.Face j)
    (reopen_apply : ∀ x, reopen (T.restrict h x) (residual x) = x) :
    Transition (T.Face j) (T.Face i) where
  Residual := Residual
  apply := T.restrict h
  residual := residual
  reopen := reopen
  reopen_apply := reopen_apply

/-- [proved-derived; formal-checked] Composing the transitions of `i ≤ j` and `j ≤ k` transports
along the composite refinement and pairs the two residuals. This is `restrict_trans` read through
`Transition.comp`. -/
theorem restrictTransition_comp_apply {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k)
    {R₁ R₂ : Type w}
    (r₁ : T.Face j → R₁) (o₁ : T.Face i → R₁ → T.Face j)
    (l₁ : ∀ x, o₁ (T.restrict hij x) (r₁ x) = x)
    (r₂ : T.Face k → R₂) (o₂ : T.Face j → R₂ → T.Face k)
    (l₂ : ∀ x, o₂ (T.restrict hjk x) (r₂ x) = x)
    (x : T.Face k) :
    (Transition.comp (T.restrictTransition hij R₁ r₁ o₁ l₁)
        (T.restrictTransition hjk R₂ r₂ o₂ l₂)).apply x =
      T.restrict (le_trans hij hjk) x :=
  T.restrict_trans hij hjk x

/-- [proved-derived; formal-checked] **The residual is what the finer chart reopens, inside the
tower.** A continuing object's coarse materialized face together with the restriction's residual
returns its fine face exactly. -/
theorem section_witness_reopened {i j : Index} (h : i ≤ j)
    (tr : Transition (T.Face j) (T.Face i)) (happly : ∀ x, tr.apply x = T.restrict h x)
    (s : T.CompatibleSection) :
    tr.reopen (s.witness i) (tr.residual (s.witness j)) = s.witness j := by
  have hx := tr.reopen_apply (s.witness j)
  rw [happly, s.compatible h] at hx
  exact hx

end Tower

/-! ## The witnesses

`unique`, `plural` and `obstructed` each receive an inhabitant, and the non-invertible transition
receives a concrete coarse-graining instance whose composition law is discharged exactly. -/

/-- [definition] The trivial tower: one face everywhere, restriction the identity. -/
def unitTower : Tower.{0, 0} ℕ where
  Face := fun _ => Unit
  restrict := fun _ x => x
  restrict_refl := fun _ _ => rfl
  restrict_trans := fun _ _ _ => rfl

/-- [proved-derived; formal-checked] The `unique` arm is inhabited. -/
theorem unitTower_gluing : unitTower.GluingResult :=
  .unique ⟨{ witness := fun _ => (), compatible := fun _ => rfl }⟩
    ⟨by
      rintro ⟨w₁, c₁⟩ ⟨w₂, c₂⟩
      have hw : w₁ = w₂ := funext fun _ => rfl
      subst hw
      rfl⟩

/-! ### The `plural` witness: `ℤ/p^n` under the cast maps -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- [definition] The `ℤ/p^n` tower under the canonical cast maps. -/
def padicTower : Tower.{0, 0} ℕ where
  Face := fun n => ZMod (p ^ n)
  restrict := fun {m _} h x => ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) x
  restrict_refl := by
    intro n x
    simp
  restrict_trans := by
    intro i j k hij hjk x
    show ZMod.castHom (pow_dvd_pow p hij) (ZMod (p ^ i))
        (ZMod.castHom (pow_dvd_pow p hjk) (ZMod (p ^ j)) x) =
      ZMod.castHom (pow_dvd_pow p (le_trans hij hjk)) (ZMod (p ^ i)) x
    rw [← RingHom.comp_apply, ZMod.castHom_comp]

omit [Fact p.Prime] in
/-- [proved-derived; formal-checked] Every restriction is surjective: every level is inhabited over
every coarser face. -/
theorem padicTower_restrict_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective fun x : ZMod (p ^ n) => (padicTower p).restrict h x :=
  ZMod.ringHom_surjective _

/-- [proved-derived; formal-checked] Every `p`-adic integer is a compatible section. -/
noncomputable def padicSection (a : ℤ_[p]) : (padicTower p).CompatibleSection where
  witness := fun n => PadicInt.toZModPow n a
  compatible := by
    intro m n h
    have := congrArg (fun f => f a) (PadicInt.zmod_cast_comp_toZModPow (p := p) m n h)
    simpa [padicTower] using this

/-- [proved-derived; formal-checked] The sections of `0` and `1` already separate at chart `1`. -/
theorem padicSection_zero_ne_one_at_one :
    (padicSection p 0).witness 1 ≠ (padicSection p 1).witness 1 := by
  show PadicInt.toZModPow (p := p) 1 0 ≠ PadicInt.toZModPow (p := p) 1 1
  rw [map_zero, map_one]
  have : Nontrivial (ZMod (p ^ 1)) :=
    ZMod.nontrivial_iff.mpr (by simpa using (Fact.out : p.Prime).ne_one)
  exact zero_ne_one

/-- [proved-derived; formal-checked] The tower is plural: distinct compatible sections exist. -/
theorem padicTower_plural : ¬ Subsingleton (padicTower p).CompatibleSection := by
  intro hsub
  exact padicSection_zero_ne_one_at_one p
    (congrArg (fun s : (padicTower p).CompatibleSection => s.witness 1)
      (Subsingleton.elim (padicSection p 0) (padicSection p 1)))

/-- [proved-derived; formal-checked] The `plural` arm is inhabited. -/
theorem padicTower_gluing : (padicTower p).GluingResult :=
  .plural ⟨padicSection p 0⟩ (padicTower_plural p)

omit [Fact p.Prime] in
/-- [proved-derived; formal-checked] The same conclusion through the existing
`SuccessorWitnessSystem` owner, with no `p`-adic input: an inhabited base and surjective adjacent
restrictions already force a section. -/
theorem padicTower_nonempty_via_successorWitness :
    Nonempty (padicTower p).CompatibleSection :=
  Tower.nonempty_compatibleSection_of_surjectiveAdjacent (padicTower p)
    ⟨(0 : ZMod (p ^ 0))⟩ fun n => padicTower_restrict_surjective p (Nat.le_succ n)

/-- [definition] `Foundation/Receiver.lean`'s insufficiency witness at two charts of the `ℤ/p^n`
tower: charts `0` and `1` merge and separate the same pair of continuing objects. -/
noncomputable def padicChartInsufficiency :
    ReceiverInsufficiency (fun s : (padicTower p).CompatibleSection => s.witness 0)
      (fun s : (padicTower p).CompatibleSection => s.witness 1) where
  left := padicSection p 0
  right := padicSection p 1
  sameEntering := by
    have : Subsingleton ((padicTower p).Face 0) := by
      change Subsingleton (ZMod (p ^ 0))
      rw [pow_zero]
      infer_instance
    exact Subsingleton.elim _ _
  differentReturned := padicSection_zero_ne_one_at_one p

end Padic

/-! ### The `obstructed` witness: every level inhabited, no coherent section -/

/-- [definition] Faces `ℕ` at every depth; restriction adds the depth difference. Mittag-Leffler
fails: the restrictions are not surjective, and their images shrink without limit. -/
def shiftTower : Tower.{0, 0} ℕ where
  Face := fun _ => ℕ
  restrict := fun {m n} _ x => x + (n - m)
  restrict_refl := by
    intro n x
    simp
  restrict_trans := by
    intro i j k hij hjk x
    show x + (k - j) + (j - i) = x + (k - i)
    omega

/-- [proved-derived; formal-checked] Every level is inhabited. -/
theorem shiftTower_face_nonempty (n : ℕ) : Nonempty (shiftTower.Face n) := ⟨(0 : ℕ)⟩

/-- [definition] Read a shift-tower face as the natural number it is. -/
abbrev shiftFaceNat (n : ℕ) (x : shiftTower.Face n) : ℕ := x

/-- [counterexample; formal-checked] No compatible section: the base witness would have to exceed
every natural number. -/
theorem shiftTower_obstructed : IsEmpty shiftTower.CompatibleSection := by
  constructor
  intro s
  have key : ∀ n : ℕ, shiftFaceNat n (s.witness n) + n = shiftFaceNat 0 (s.witness 0) := by
    intro n
    have h := s.compatible (Nat.zero_le n)
    change shiftFaceNat n (s.witness n) + (n - 0) = shiftFaceNat 0 (s.witness 0) at h
    simpa using h
  have := key (shiftFaceNat 0 (s.witness 0) + 1)
  omega

/-- [proved-derived; formal-checked] The `obstructed` arm is inhabited. -/
theorem shiftTower_gluing : shiftTower.GluingResult := .obstructed shiftTower_obstructed

/-- [counterexample; formal-checked] The exact hypothesis that fails: adjacent restriction is not
surjective, so `SuccessorWitnessSystem` does not apply. -/
theorem shiftTower_adjacent_not_surjective (n : ℕ) :
    ¬ Function.Surjective fun x : shiftTower.Face (n + 1) =>
        shiftTower.restrict (Nat.le_succ n) x := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (0 : ℕ)
  have hx' : shiftFaceNat (n + 1) x + (n + 1 - n) = 0 := hx
  omega

/-- [proved-derived; formal-checked] The generic gluing obstruction population is
inhabited at every chart of the shift tower. -/
theorem shiftTower_obstruction_nonempty (i : ℕ) :
    Nonempty (shiftTower.gluingPassage i).Obstruction :=
  (shiftTower.obstruction_nonempty_iff i).mpr
    ⟨(0 : ℕ), ⟨fun x => shiftTower_obstructed.false x.1⟩⟩

/-- [proved-derived; formal-checked] Hence the passage does not glue, discharged by the existing
`GluingPassage.not_glues_iff_obstruction_nonempty`. -/
theorem shiftTower_not_glues (i : ℕ) : ¬ (shiftTower.gluingPassage i).Glues :=
  (GluingPassage.not_glues_iff_obstruction_nonempty _).mpr (shiftTower_obstruction_nonempty i)

/-! ### The loop obstruction stays with its existing owner -/

/-- [counterexample; formal-checked] The fixed-point population of the smallest nonidentity
self-transport is empty. This is `Millennium/HolonicDirectedPassage.lean:326-330`'s
`boolFlipCoherent_isEmpty`, cited rather than rebuilt; `Tower.restrict_self_eq_id` shows no tower
can carry that self-transport in the first place. -/
theorem boolFlipSelfLoop_isEmpty : IsEmpty { w : Bool // boolFlip w = w } :=
  ⟨fun w => boolFlipCoherent_isEmpty.false ⟨w.1, w.2⟩⟩

/-! ### A concrete non-invertible transition: exact coarse graining -/

/-- [definition] Coarse graining by `m`: transport the quotient, retain the remainder. This is the
smallest transition that is genuinely non-invertible and genuinely reopenable.

Rust counterpart: `continuing_tower.rs::coarse_grain`. -/
def coarseGrain (m : ℕ) : Transition ℕ ℕ where
  Residual := ℕ
  apply := fun x => x / m
  residual := fun x => x % m
  reopen := fun q r => m * q + r
  reopen_apply := fun x => Nat.div_add_mod x m

/-- [proved-derived; formal-checked] Coarse graining by `m > 1` is not injective, so its residual is
not subsingleton: the transition is genuinely lossy. -/
theorem coarseGrain_not_injective {m : ℕ} (hm : 1 < m) :
    ¬ Function.Injective (coarseGrain m).apply := by
  intro hinj
  have h0 : (coarseGrain m).apply 0 = (coarseGrain m).apply 1 := by
    show (0 : ℕ) / m = 1 / m
    rw [Nat.zero_div, Nat.div_eq_of_lt hm]
  exact absurd (hinj h0) (by omega)

/-- [proved-derived; formal-checked] Composing two coarse grainings transports along the product.
-/
theorem coarseGrain_comp_apply (m n x : ℕ) :
    (Transition.comp (coarseGrain m) (coarseGrain n)).apply x = (coarseGrain (n * m)).apply x :=
  Nat.div_div_eq_div_mul x n m

/-- [proved-derived; formal-checked] The residual of one coarse graining is the remainder. -/
theorem coarseGrain_residual (m x : ℕ) : (coarseGrain m).residual x = x % m := rfl

/-- [proved-derived; formal-checked] **Composition composes residuals.** The composite's residual is
exactly the pair: what the second grain dropped about the already-transported face, and what the
first dropped. -/
theorem coarseGrain_comp_residual_pair (m n x : ℕ) :
    (Transition.comp (coarseGrain m) (coarseGrain n)).residual x = (x / n % m, x % n) := rfl

/-- [proved-derived; formal-checked] **The paired residual reassembles the single one, exactly.**
The composite of two coarse grainings loses neither more nor less than the one-step coarse graining
by the product it equals under `coarseGrain_comp_apply`. -/
theorem coarseGrain_comp_residual_reassembles {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (x : ℕ) :
    n * (x / n % m) + x % n = x % (n * m) := by
  have hb : x / n % m < m := Nat.mod_lt _ hm
  have hc : x % n < n := Nat.mod_lt _ hn
  have hlt : n * (x / n % m) + x % n < n * m := by
    have hstep : n * (x / n % m + 1) ≤ n * m := Nat.mul_le_mul (Nat.le_refl n) hb
    have hexp : n * (x / n % m + 1) = n * (x / n % m) + n := by ring
    omega
  have hx : n * m * (x / (n * m)) + (n * (x / n % m) + x % n) = x := by
    have hdiv : x / (n * m) = x / n / m := (Nat.div_div_eq_div_mul x n m).symm
    rw [hdiv]
    calc n * m * (x / n / m) + (n * (x / n % m) + x % n)
        = n * (m * (x / n / m) + x / n % m) + x % n := by ring
      _ = n * (x / n) + x % n := by rw [Nat.div_add_mod]
      _ = x := Nat.div_add_mod x n
  calc n * (x / n % m) + x % n
      = (n * m * (x / (n * m)) + (n * (x / n % m) + x % n)) % (n * m) := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    _ = x % (n * m) := by rw [hx]

/-- [proved-derived; formal-checked] The coarse grainings of a tower's restriction: the shift tower
restricts by adding, which is injective, so it is an invertible-on-its-image transition with a
`PUnit` residual — while coarse graining is not. The two live in one family. -/
theorem shiftTower_restrict_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective fun x : shiftTower.Face n => shiftTower.restrict h x := by
  intro a b hab
  have hab' : shiftFaceNat n a + (n - m) = shiftFaceNat n b + (n - m) := hab
  have hab'' : shiftFaceNat n a = shiftFaceNat n b := by omega
  exact hab''

/-- [definition] The `ℤ/4` versus `ℤ/2 ⊕ ℤ/2` control: a codimension-one face does not determine the
module it was read from. A face is a receiver reading and never the identity of its source. -/
theorem theOrderFaceDoesNotDetermineTheModule :
    Nat.card (ZMod 4) = Nat.card (ZMod 2 × ZMod 2) ∧
      IsEmpty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  refine ⟨by simp, ⟨fun e => ?_⟩⟩
  have hz : ∀ x : ZMod 2 × ZMod 2, (2 : ℕ) • x = 0 := by decide
  have h : e ((2 : ℕ) • (1 : ZMod 4)) = e 0 := by
    rw [map_nsmul, hz, map_zero]
  have h' : (2 : ℕ) • (1 : ZMod 4) = 0 := e.injective h
  exact absurd h' (by decide)

/-! ## C2 — the canonical non-Archimedean instance

[definition] `padicTower` above is the `plural` witness only. This section discharges carrier item
**C2** of `docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md`:

* both directions of `ℤ_[p] ≃ Tower.CompatibleSection`, through Mathlib's `PadicInt.toZModPow`
  and `PadicInt.ofIntSeq` rather than a rebuilt inverse limit; and
* the **exact** fibre splitting: the fibre of the `level m + k → level m` restriction over one
  level-`m` face is in bijection with `ZMod (p ^ k)`, so the adjacent step splits into exactly `p`
  cosets of `ker (PadicInt.toZModPow (n+1))` inside the coset of `ker (PadicInt.toZModPow n)`.
  The count is `p ^ k` on the nose — an equality of `Nat.card`, not an asymptotic statement.

Rust counterpart: `crates/holonic-core/src/restriction/tower.rs::{FibreSplitting,
ResidueTower::split_fibre, ResidueTower::coset_count, ResidueTower::coset_count_bits}`.
-/

namespace Tower

/-- [proved-derived; formal-checked] Two continuing objects presenting the same face at every chart
are one object: the compatibility field is a `Prop` and carries no data. -/
theorem CompatibleSection.ext {Index : Type u} [Preorder Index] {T : Tower.{u, v} Index}
    {s t : T.CompatibleSection} (h : ∀ i, s.witness i = t.witness i) : s = t := by
  obtain ⟨ws, hs⟩ := s
  obtain ⟨wt, ht⟩ := t
  have hw : ws = wt := funext h
  subst hw
  rfl

end Tower

section PadicC2

variable (p : ℕ) [Fact p.Prime]

/-! ### Both directions of `ℤ_[p] ≃ CompatibleSection` -/

/-- [definition] The integer sequence a continuing object of the `ℤ/p^n` tower reads off: the
canonical representative of the face it presents at each level. -/
def padicSectionSeq (s : (padicTower p).CompatibleSection) (n : ℕ) : ℤ :=
  ((s.witness n : ZMod (p ^ n)).val : ℤ)

/-- [proved-derived; formal-checked] Consecutive representatives differ by a multiple of `p ^ n`.
This is exactly the hypothesis `PadicInt.ofIntSeq` needs, and it is the compatibility field of the
section — nothing further is assumed. -/
theorem padicSectionSeq_dvd (s : (padicTower p).CompatibleSection) (i : ℕ) :
    (p : ℤ) ^ i ∣ padicSectionSeq p s (i + 1) - padicSectionSeq p s i := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcomp : ZMod.castHom (pow_dvd_pow p (Nat.le_succ i)) (ZMod (p ^ i)) (s.witness (i + 1))
      = s.witness i := s.compatible (Nat.le_succ i)
  have h1 : ((padicSectionSeq p s (i + 1) : ℤ) : ZMod (p ^ i))
      = ZMod.castHom (pow_dvd_pow p (Nat.le_succ i)) (ZMod (p ^ i)) (s.witness (i + 1)) := by
    simp only [padicSectionSeq, Int.cast_natCast]
    exact ZMod.natCast_val _
  have h2 : ((padicSectionSeq p s i : ℤ) : ZMod (p ^ i)) = s.witness i := by
    simp only [padicSectionSeq, Int.cast_natCast]
    exact ZMod.natCast_rightInverse _
  have hcast : ((padicSectionSeq p s i : ℤ) : ZMod (p ^ i))
      = ((padicSectionSeq p s (i + 1) : ℤ) : ZMod (p ^ i)) := by
    rw [h1, h2, hcomp]
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ i)).mp hcast
  simpa using hdvd

/-- [proved-derived; formal-checked] **C2, the reverse direction.** Every continuing object of the
`ℤ/p^n` tower *is* a `p`-adic integer. The construction is Mathlib's `PadicInt.ofIntSeq`; this file
supplies only the divisibility the section already carries. -/
noncomputable def padicOfSection (s : (padicTower p).CompatibleSection) : ℤ_[p] :=
  PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (padicSectionSeq p s) p (padicSectionSeq_dvd p s))

/-- [proved-derived; formal-checked] That `p`-adic integer presents exactly the section's face at
every chart. -/
theorem toZModPow_padicOfSection (s : (padicTower p).CompatibleSection) (n : ℕ) :
    PadicInt.toZModPow n (padicOfSection p s) = s.witness n := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [padicOfSection,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (padicSectionSeq p s) p (padicSectionSeq_dvd p s)]
  simp only [padicSectionSeq, Int.cast_natCast]
  exact ZMod.natCast_rightInverse _

/-- [proved-derived; formal-checked] **C2.** The continuing objects of the `ℤ/p^n` tower are
*exactly* the `p`-adic integers. Forward is `padicSection` (`PadicInt.toZModPow` at every level),
reverse is `padicOfSection`; `PadicInt.ext_of_toZModPow` closes one round trip and
`Tower.CompatibleSection.ext` the other. -/
noncomputable def padicSectionEquiv : ℤ_[p] ≃ (padicTower p).CompatibleSection where
  toFun := padicSection p
  invFun := padicOfSection p
  left_inv := fun a => PadicInt.ext_of_toZModPow.mp fun n => by
    rw [toZModPow_padicOfSection]
    rfl
  right_inv := fun s => Tower.CompatibleSection.ext fun n => toZModPow_padicOfSection p s n

/-- [proved-derived; formal-checked] The forward direction is injective on its own: two `p`-adic
integers presenting the same face at every chart are equal. This is the tower reading of
`PadicInt.ext_of_toZModPow`. -/
theorem padicSection_injective : Function.Injective (padicSection p) :=
  (padicSectionEquiv p).injective

/-- [proved-derived; formal-checked] Every chart of the tower is actually reached: `toZModPow` is
surjective at every level, with the natural-number representative as the witness. -/
theorem padic_toZModPow_surjective (n : ℕ) :
    Function.Surjective (PadicInt.toZModPow (p := p) n) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro x
  refine ⟨((x.val : ℕ) : ℤ_[p]), ?_⟩
  rw [map_natCast]
  exact ZMod.natCast_rightInverse x

/-! ### The exact fibre splitting -/

/-- [definition] The exact digit block a level-`m + k` face carries above its level-`m`
restriction: the coset index of the splitting.

Rust counterpart: `continuing_tower.rs::FibreSplitting::coset_index`. -/
def padicDigitGap (m k : ℕ) (x : ZMod (p ^ (m + k))) : ZMod (p ^ k) :=
  ((x.val / p ^ m : ℕ) : ZMod (p ^ k))

/-- [definition] Reopen a level-`m + k` face from its level-`m` restriction and its digit block.

Rust counterpart: `continuing_tower.rs::FibreSplitting::representative`. -/
def padicReopenGap (m k : ℕ) (face : ZMod (p ^ m)) (d : ZMod (p ^ k)) : ZMod (p ^ (m + k)) :=
  ((face.val + d.val * p ^ m : ℕ) : ZMod (p ^ (m + k)))

/-- [proved-derived; formal-checked] The reopened face's canonical representative is exactly
`face.val + d.val * p ^ m`: the digit block sits above the retained low block with no carry. -/
theorem padicReopenGap_val (m k : ℕ) (face : ZMod (p ^ m)) (d : ZMod (p ^ k)) :
    (padicReopenGap p m k face d).val = face.val + d.val * p ^ m := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hface : face.val < p ^ m := ZMod.val_lt face
  have hd : d.val < p ^ k := ZMod.val_lt d
  have hbound : face.val + d.val * p ^ m < p ^ (m + k) := by
    have h1 : d.val + 1 ≤ p ^ k := hd
    calc face.val + d.val * p ^ m
        < p ^ m + d.val * p ^ m := by omega
      _ = (d.val + 1) * p ^ m := by ring
      _ ≤ p ^ k * p ^ m := Nat.mul_le_mul h1 (Nat.le_refl (p ^ m))
      _ = p ^ (m + k) := by rw [← pow_add, Nat.add_comm]
  exact ZMod.val_cast_of_lt hbound

/-- [proved-derived; formal-checked] Every reopened face really does restrict back to the face it
was reopened from. -/
theorem padicRestrict_reopenGap (m k : ℕ) (face : ZMod (p ^ m)) (d : ZMod (p ^ k)) :
    (padicTower p).restrict (Nat.le_add_right m k) (padicReopenGap p m k face d) = face := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  show ZMod.castHom (pow_dvd_pow p (Nat.le_add_right m k)) (ZMod (p ^ m))
      (padicReopenGap p m k face d) = face
  rw [padicReopenGap, map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero,
    add_zero, ZMod.natCast_val, ZMod.cast_id]

/-- [proved-derived; formal-checked] The digit of a reopened face is the digit it was reopened
with: the coset index is recovered exactly. -/
theorem padicDigitGap_reopenGap (m k : ℕ) (face : ZMod (p ^ m)) (d : ZMod (p ^ k)) :
    padicDigitGap p m k (padicReopenGap p m k face d) = d := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hface : face.val < p ^ m := ZMod.val_lt face
  have hpm : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  rw [padicDigitGap, padicReopenGap_val, Nat.add_mul_div_right _ _ hpm,
    Nat.div_eq_of_lt hface, Nat.zero_add]
  exact ZMod.natCast_rightInverse d

/-- [proved-derived; formal-checked] **`reopen_apply` at the canonical non-Archimedean instance.**
The restricted face together with the digit block is exactly the level-`m + k` face. -/
theorem padicReopenGap_restrict (m k : ℕ) (x : ZMod (p ^ (m + k))) :
    padicReopenGap p m k ((padicTower p).restrict (Nat.le_add_right m k) x)
      (padicDigitGap p m k x) = x := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpm : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
  have hxlt : x.val < p ^ (m + k) := ZMod.val_lt x
  have hres : ((padicTower p).restrict (Nat.le_add_right m k) x).val = x.val % p ^ m := by
    show (ZMod.castHom (pow_dvd_pow p (Nat.le_add_right m k)) (ZMod (p ^ m)) x).val = x.val % p ^ m
    rw [ZMod.castHom_apply, ← ZMod.natCast_val x, ZMod.val_natCast]
  have hdigitlt : x.val / p ^ m < p ^ k := by
    rw [Nat.div_lt_iff_lt_mul hpm]
    calc x.val < p ^ (m + k) := hxlt
      _ = p ^ k * p ^ m := by rw [← pow_add, Nat.add_comm]
  have hdig : (padicDigitGap p m k x).val = x.val / p ^ m := by
    rw [padicDigitGap]
    exact ZMod.val_cast_of_lt hdigitlt
  show ((((padicTower p).restrict (Nat.le_add_right m k) x).val
      + (padicDigitGap p m k x).val * p ^ m : ℕ) : ZMod (p ^ (m + k))) = x
  rw [hres, hdig, Nat.mod_add_div' x.val (p ^ m)]
  exact ZMod.natCast_rightInverse x

/-- [proved-derived; formal-checked] **C2, the exact fibre splitting.** The fibre of the
`level m + k → level m` restriction over one level-`m` face is in *exact* bijection with
`ZMod (p ^ k)` — the digit block the restriction dropped. The bijection is executable in both
directions: `padicDigitGap` reads the coset index off a face, `padicReopenGap` builds the
representative back. -/
def padicFibreEquiv (m k : ℕ) (face : ZMod (p ^ m)) :
    { x : ZMod (p ^ (m + k)) //
        (padicTower p).restrict (Nat.le_add_right m k) x = face } ≃ ZMod (p ^ k) where
  toFun x := padicDigitGap p m k x.1
  invFun d := ⟨padicReopenGap p m k face d, padicRestrict_reopenGap p m k face d⟩
  left_inv := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    show padicReopenGap p m k face (padicDigitGap p m k x) = x
    rw [← hx]
    exact padicReopenGap_restrict p m k x
  right_inv d := padicDigitGap_reopenGap p m k face d

/-- [proved-derived; formal-checked] The count is **exact**: the fibre over a level-`m` face has
exactly `p ^ k` elements at level `m + k`. -/
theorem padicFibre_card (m k : ℕ) (face : ZMod (p ^ m)) :
    Nat.card { x : ZMod (p ^ (m + k)) //
        (padicTower p).restrict (Nat.le_add_right m k) x = face } = p ^ k := by
  rw [Nat.card_congr (padicFibreEquiv p m k face), Nat.card_zmod]

/-- [proved-derived; formal-checked] **Exactly `p` cosets at the next level.** One refinement step
splits the fibre into exactly `p` classes — an equality, not an asymptotic count. -/
theorem padicAdjacentFibre_card (n : ℕ) (face : ZMod (p ^ n)) :
    Nat.card { x : ZMod (p ^ (n + 1)) //
        (padicTower p).restrict (Nat.le_succ n) x = face } = p := by
  simpa using padicFibre_card p n 1 face

/-- [proved-derived; formal-checked] The fibre over a level-`n` face *is* a coset of
`RingHom.ker (PadicInt.toZModPow n) = Ideal.span {p ^ n}`: two continuing objects present the same
level-`n` face exactly when they differ by an element of that kernel. Mathlib's
`PadicInt.ker_toZModPow` supplies the kernel; nothing is rebuilt. -/
theorem padic_sameFace_iff_sub_mem_ker (n : ℕ) (a b : ℤ_[p]) :
    PadicInt.toZModPow n a = PadicInt.toZModPow n b ↔
      a - b ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
  rw [← PadicInt.ker_toZModPow n, RingHom.mem_ker, map_sub, sub_eq_zero]

/-- [proved-derived; formal-checked] **A coarse equality is reopened by the finer receiver, and the
count is exact.** The continuing objects behind one level-`n` face reach exactly `p` faces at level
`n + 1`, and every one of those `p` faces is actually reached by a continuing object — so the
splitting is a statement about the observation fibre, not only about the finite quotients. -/
theorem padicObservationFibre_reaches_exactly_p (n : ℕ) (face : ZMod (p ^ n)) :
    Nat.card { x : ZMod (p ^ (n + 1)) //
        (padicTower p).restrict (Nat.le_succ n) x = face } = p ∧
      ∀ x : ZMod (p ^ (n + 1)), (padicTower p).restrict (Nat.le_succ n) x = face →
        ∃ s : (padicTower p).ObservationFibre n face, s.1.witness (n + 1) = x := by
  refine ⟨padicAdjacentFibre_card p n face, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := padic_toZModPow_surjective p (n + 1) x
  have hw1 : (padicSection p a).witness (n + 1) = x := ha
  have hwn : (padicSection p a).witness n = face := by
    have hc := (padicSection p a).compatible (Nat.le_succ n)
    rw [hw1] at hc
    exact hc.symm.trans hx
  exact ⟨⟨padicSection p a, hwn⟩, hw1⟩

/-- [definition] The `ℤ/p^(m+k) → ℤ/p^m` restriction as a `Transition` whose residual is exactly
the digit block of the splitting. C2's coset index and C4's residual are one object, not two.

Rust counterpart: `continuing_tower.rs::ResidueTower::restriction_residual` together with
`FibreSplitting`. -/
def padicRestrictTransition (m k : ℕ) : Transition (ZMod (p ^ (m + k))) (ZMod (p ^ m)) :=
  (padicTower p).restrictTransition (Nat.le_add_right m k) (ZMod (p ^ k))
    (padicDigitGap p m k) (padicReopenGap p m k) (padicReopenGap_restrict p m k)

/-- [proved-derived; formal-checked] Its residual is the coset index of the splitting, by `rfl`. -/
theorem padicRestrictTransition_residual (m k : ℕ) (x : ZMod (p ^ (m + k))) :
    (padicRestrictTransition p m k).residual x = padicDigitGap p m k x := rfl

/-- [proved-derived; formal-checked] The residual is a *complete* invariant of the fibre: inside one
fibre, equal residuals force equal faces. `Transition.residual_separates` is therefore sharp at the
canonical non-Archimedean instance — the residual loses nothing the fine chart saw. -/
theorem padicRestrictTransition_residual_complete (m k : ℕ) (face : ZMod (p ^ m))
    {x y : ZMod (p ^ (m + k))}
    (hx : (padicTower p).restrict (Nat.le_add_right m k) x = face)
    (hy : (padicTower p).restrict (Nat.le_add_right m k) y = face)
    (hd : (padicRestrictTransition p m k).residual x
      = (padicRestrictTransition p m k).residual y) : x = y :=
  congrArg Subtype.val
    ((padicFibreEquiv p m k face).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hd)

end PadicC2

/-! ## C4 — `Migration`: a functor of index categories with a natural transformation on faces

[definition] `Transition` above is the non-invertible chart map **at one chart**. `Migration` is the
structure one level up: it changes the whole chart family. A tower is a presheaf on its index
preorder, and a migration from `S` to `T` is a functor `u` of index categories together with a
natural transformation `u^* S ⇒ T` on faces. The index map runs `IndexT → IndexS` — for each chart
of the *new* family, which chart of the *old* family it reads — which is the direction schema
history actually needs and the direction in which a saved object can be carried forward.

Naturality is the whole content and is stated and proved below. Migrations compose, composition is
associative, and the identity migration is a two-sided unit; all three hold by `rfl`.

Rust counterpart: `crates/holonic-core/src/restriction/tower.rs::{Migration, ResidualMigration,
check_migration_naturality, carry_section, ComposedMigration, IdentityMigration, HalvingMigration}`.
-/

universe u₂ v₂ u₃ v₃

/-- [definition] A **migration** from tower `S` to tower `T`: a functor of index categories
together with a natural transformation on faces.

Rust counterpart: `continuing_tower.rs::Migration`, whose `naturality` is checked and returned as
a `NaturalityReceipt` or refused as a `MigrationRefusal`. -/
structure Migration {IndexS : Type u} [Preorder IndexS] {IndexT : Type u₂} [Preorder IndexT]
    (S : Tower.{u, v} IndexS) (T : Tower.{u₂, v₂} IndexT) where
  /-- Which chart of the source family a target chart reads. -/
  index : IndexT → IndexS
  /-- The index map is a functor of index categories: it preserves refinement. -/
  index_mono : ∀ {i j : IndexT}, i ≤ j → index i ≤ index j
  /-- The natural transformation on faces: one component per target chart. -/
  face : ∀ j : IndexT, S.Face (index j) → T.Face j
  /-- **Naturality.** Restricting after migrating is migrating after restricting. This is the whole
  content of the structure: without it a family of face maps carries no relation between charts. -/
  naturality : ∀ {i j : IndexT} (h : i ≤ j) (x : S.Face (index j)),
    T.restrict h (face j x) = face i (S.restrict (index_mono h) x)

namespace Migration

variable {IndexS : Type u} [Preorder IndexS] {IndexT : Type u₂} [Preorder IndexT]
variable {S : Tower.{u, v} IndexS} {T : Tower.{u₂, v₂} IndexT}

/-- [definition] The identity migration of a tower. -/
def identity {Index : Type u} [Preorder Index] (T : Tower.{u, v} Index) : Migration T T where
  index := _root_.id
  index_mono h := h
  face _ x := x
  naturality _ _ := rfl

/-- [definition] Composition of migrations: `second` after `first`. The index maps compose in the
opposite order, as they must for a contravariant index.

Rust counterpart: `continuing_tower.rs::ComposedMigration`. -/
def comp {IndexU : Type u₃} [Preorder IndexU] {U : Tower.{u₃, v₃} IndexU}
    (second : Migration T U) (first : Migration S T) : Migration S U where
  index := first.index ∘ second.index
  index_mono h := first.index_mono (second.index_mono h)
  face k x := second.face k (first.face (second.index k) x)
  naturality h x := by
    rw [second.naturality h, first.naturality]

/-- [proved-derived; formal-checked] Composition is associative. -/
theorem comp_assoc {IndexU : Type u₃} [Preorder IndexU] {U : Tower.{u₃, v₃} IndexU}
    {IndexV : Type u₃} [Preorder IndexV] {V : Tower.{u₃, v₃} IndexV}
    (third : Migration U V) (second : Migration T U) (first : Migration S T) :
    comp (comp third second) first = comp third (comp second first) := rfl

/-- [proved-derived; formal-checked] The identity migration is a right unit. -/
theorem comp_identity (M : Migration S T) : comp M (identity S) = M := rfl

/-- [proved-derived; formal-checked] The identity migration is a left unit. -/
theorem identity_comp (M : Migration S T) : comp (identity T) M = M := rfl

/-- [proved-derived; formal-checked] **A migration carries a continuing object.** This is the
consuming operation: an object saved under the chart family `S` is *read* under the chart family
`T`, and what comes back is again one continuing object, not a family of unrelated faces. The proof
is naturality followed by the source section's own compatibility — nothing else is used.

Rust counterpart: `continuing_tower.rs::carry_section`. -/
def carrySection (M : Migration S T) (s : S.CompatibleSection) : T.CompatibleSection where
  witness j := M.face j (s.witness (M.index j))
  compatible h := by rw [M.naturality h, s.compatible]

/-- [proved-derived; formal-checked] Carrying is functorial: a schema *history* — a chain of
migrations — may be replayed step by step or composed first, with the same result. -/
theorem carrySection_comp {IndexU : Type u₃} [Preorder IndexU] {U : Tower.{u₃, v₃} IndexU}
    (second : Migration T U) (first : Migration S T) (s : S.CompatibleSection) :
    (comp second first).carrySection s = second.carrySection (first.carrySection s) := rfl

/-- [proved-derived; formal-checked] The identity migration changes no continuing object. -/
theorem carrySection_identity (s : S.CompatibleSection) :
    (identity S).carrySection s = s := rfl

/-- [proved-derived; formal-checked] The face a carried object presents is the migrated face. -/
theorem carrySection_witness (M : Migration S T) (s : S.CompatibleSection) (j : IndexT) :
    (M.carrySection s).witness j = M.face j (s.witness (M.index j)) := rfl

/-- [definition] A migration carries the observation fibre forward: every continuing object behind
the source face is carried to one behind the migrated face. The fibre may collapse — that is what a
lossy migration does — and the collapse is exactly what a residual reopens. -/
def carryObservationFibre (M : Migration S T) (j : IndexT) (face : S.Face (M.index j)) :
    S.ObservationFibre (M.index j) face → T.ObservationFibre j (M.face j face) :=
  fun s => ⟨M.carrySection s.1, congrArg (M.face j) s.2⟩

end Migration

/-! ### `Holon.Rebase` is the invertible instance

[established-bounded; formal-checked] `Foundation/Holon.lean:91-125` already owns the invertible
chart change: `Rebase` transports the complete holon diagram — occurrence population and all three
oriented ports — through commuting squares, and `Rebase.preimageFibreEquiv` carries the whole fibre.
It is *not* founded again here. What is shown is that it **is** a `Migration`, once the holon
diagram is presented as the tower it already is: the three oriented ports are three coarse charts,
the occurrence population is the one fine chart above them, and the three `_natural` fields of
`Rebase` are exactly the three nonreflexive instances of `Migration.naturality`.

The one bookkeeping discrepancy, recorded rather than hidden: `Tower.Face : Index → Type v` puts
every face of one tower in a single universe, while `Holon.{u,v,w,x}` allows four. The presentation
below is therefore stated for a holon whose four types share a universe. No mathematical content is
lost — a `Rebase` between such holons still relates two *different* universes — and nothing else
about `Rebase` fails to fit. -/

/-- [definition] The index of a holon's own diagram: the three oriented ports it presents, each
refined by the occurrence population that carries them. The poset has height two, which is why
`restrict_trans` below is automatic. -/
inductive DiagramIndex
  | sourcePort
  | targetPort
  | facePort
  | occurrence
  deriving DecidableEq, Repr

namespace DiagramIndex

/-- [definition] `i ⊑ j` exactly when `i` and `j` are the same chart, or `j` is the occurrence
population that carries every port. -/
protected def Le (i j : DiagramIndex) : Prop := i = j ∨ j = occurrence

instance : Preorder DiagramIndex where
  le := DiagramIndex.Le
  le_refl _ := Or.inl rfl
  le_trans i j k hij hjk := by
    rcases hij with rfl | rfl
    · exact hjk
    · refine Or.inr ?_
      rcases hjk with h | h
      · exact h.symm
      · exact h

theorem le_iff {i j : DiagramIndex} : i ≤ j ↔ (i = j ∨ j = occurrence) := Iff.rfl

instance decidableLe (i j : DiagramIndex) : Decidable (i ≤ j) :=
  decidable_of_iff _ le_iff.symm

/-- [proved-derived; formal-checked] Two distinct charts, neither of which is the occurrence
population, are unrelated. -/
theorem not_le_of_ne {i j : DiagramIndex} (hne : i ≠ j) (hj : j ≠ occurrence) : ¬ (i ≤ j) := by
  rintro (h | h)
  · exact hne h
  · exact hj h

end DiagramIndex

/-- [definition] The faces of a holon's diagram tower. -/
def diagramFace {Src Tgt Fce : Type v} (H : Holon.{v, v, v, v} Src Tgt Fce) :
    DiagramIndex → Type v
  | .sourcePort => Src
  | .targetPort => Tgt
  | .facePort => Fce
  | .occurrence => H.Occurrence

/-- [definition] Restriction in a holon's diagram tower: the occurrence population restricts to
each of the three oriented ports it presents through that port's own map, and every other admitted
refinement is the identity. -/
def diagramRestrict {Src Tgt Fce : Type v} (H : Holon.{v, v, v, v} Src Tgt Fce) :
    ∀ (i j : DiagramIndex), i ≤ j → diagramFace H j → diagramFace H i
  | .sourcePort, .occurrence, _ => H.source
  | .targetPort, .occurrence, _ => H.target
  | .facePort, .occurrence, _ => H.receive
  | .occurrence, .occurrence, _ => fun x => x
  | .sourcePort, .sourcePort, _ => fun x => x
  | .targetPort, .targetPort, _ => fun x => x
  | .facePort, .facePort, _ => fun x => x
  | .sourcePort, .targetPort, h => absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))
  | .sourcePort, .facePort, h => absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))
  | .targetPort, .sourcePort, h => absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))
  | .targetPort, .facePort, h => absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))
  | .facePort, .sourcePort, h => absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))
  | .facePort, .targetPort, h => absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))
  | .occurrence, .sourcePort, h => absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))
  | .occurrence, .targetPort, h => absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))
  | .occurrence, .facePort, h => absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))

/-- [definition] A holon presented as a `Tower` over its own diagram index. This founds nothing: the
faces and the restrictions are the holon's existing types and maps. -/
def diagramTower {Src Tgt Fce : Type v} (H : Holon.{v, v, v, v} Src Tgt Fce) :
    Tower.{0, v} DiagramIndex where
  Face := diagramFace H
  restrict {i j} h x := diagramRestrict H i j h x
  restrict_refl := by
    intro i x
    cases i <;> rfl
  restrict_trans := by
    intro i j k hij hjk x
    cases i <;> cases j <;> cases k <;>
      first
        | rfl
        | exact absurd hij (DiagramIndex.not_le_of_ne (by decide) (by decide))
        | exact absurd hjk (DiagramIndex.not_le_of_ne (by decide) (by decide))

/-- [proved-derived; formal-checked] The continuing objects of a holon's diagram tower are exactly
its occurrences: a compatible section is one occurrence together with the three faces it already
presents. The tower adds no population. -/
def diagramTowerSectionEquiv {Src Tgt Fce : Type v} (H : Holon.{v, v, v, v} Src Tgt Fce) :
    (diagramTower H).CompatibleSection ≃ H.Occurrence where
  toFun s := s.witness .occurrence
  invFun o :=
    { witness := fun i => diagramRestrict H i .occurrence (Or.inr rfl) o
      compatible := fun h => (diagramTower H).restrict_trans h (Or.inr rfl) o }
  left_inv s := Tower.CompatibleSection.ext fun _ => s.compatible (Or.inr rfl)
  right_inv _ := rfl

section RebaseMigration

variable {Src Tgt Fce : Type v} {Src' Tgt' Fce' : Type v₂}
variable {left : Holon.{v, v, v, v} Src Tgt Fce} {right : Holon.{v₂, v₂, v₂, v₂} Src' Tgt' Fce'}

/-- [definition] The four component equivalences of a `Rebase`, read as one family over the diagram
index. -/
def rebaseFaceEquiv (R : Holon.Rebase left right) :
    ∀ j : DiagramIndex, (diagramTower left).Face j ≃ (diagramTower right).Face j
  | .sourcePort => R.sourceEquiv
  | .targetPort => R.targetEquiv
  | .facePort => R.faceEquiv
  | .occurrence => R.occurrenceEquiv

/-- [proved-derived; formal-checked] **`Holon.Rebase` is a `Migration`.** Its index map is the
identity, its face components are the four equivalences it already carries, and its three
`_natural` fields are exactly the three nonreflexive instances of `Migration.naturality`. Nothing
is founded again and nothing is left over. -/
def rebaseMigration (R : Holon.Rebase left right) :
    Migration (diagramTower left) (diagramTower right) where
  index := _root_.id
  index_mono h := h
  face j := rebaseFaceEquiv R j
  naturality := by
    intro i j h x
    cases i <;> cases j <;>
      first
        | rfl
        | exact (R.source_natural x).symm
        | exact (R.target_natural x).symm
        | exact (R.receive_natural x).symm
        | exact absurd h (DiagramIndex.not_le_of_ne (by decide) (by decide))

/-- [definition] One component of the rebase migration read as a `Transition`: it is an
equivalence, so `Transition.ofEquiv` applies. -/
def rebaseMigrationTransition (R : Holon.Rebase left right) (j : DiagramIndex) :
    Transition ((diagramTower left).Face j) ((diagramTower right).Face j) :=
  Transition.ofEquiv (rebaseFaceEquiv R j)

/-- [proved-derived; formal-checked] **The rebase migration is the invertible instance: its residual
is zero at every chart.** This is `Transition.ofEquiv_residual_subsingleton` at each component. -/
theorem rebaseMigration_residual_subsingleton (R : Holon.Rebase left right) (j : DiagramIndex) :
    Subsingleton (rebaseMigrationTransition R j).Residual :=
  Transition.ofEquiv_residual_subsingleton _

/-- [proved-derived; formal-checked] The transition components really are the migration's face
components. -/
theorem rebaseMigration_face_eq (R : Holon.Rebase left right) (j : DiagramIndex)
    (x : (diagramTower left).Face j) :
    (rebaseMigration R).face j x = (rebaseMigrationTransition R j).apply x := rfl

/-- [proved-derived; formal-checked] **`Migration.carryObservationFibre` at the rebase migration is
`Holon.Rebase.preimageFibreEquiv`.** Both carry the same occurrence, by `rfl`: the migration does
not found a second transport of the retained population. -/
theorem rebaseMigration_carryObservationFibre_occurrence (R : Holon.Rebase left right) (f : Fce)
    (s : (diagramTower left).ObservationFibre .facePort f) :
    ((rebaseMigration R).carryObservationFibre .facePort f s).1.witness .occurrence
      = R.occurrenceEquiv (s.1.witness .occurrence) := rfl

/-- [proved-derived; formal-checked] The other side of the same identification: `preimageFibreEquiv`
transports by the occurrence equivalence, by `rfl`. Together with the previous theorem this is the
statement that the two are one transport. -/
theorem rebase_preimageFibreEquiv_occurrence (R : Holon.Rebase left right) (f : Fce)
    (o : left.PreimageFibre f) :
    (R.preimageFibreEquiv f o).1 = R.occurrenceEquiv o.1 := rfl

end RebaseMigration

/-! ### The precise relation between `Migration` and `Transition`

[proved-derived; formal-checked] The question "is a `Migration` a family of `Transition`s satisfying
naturality, or strictly more?" has a two-sided answer, and both sides are proved below.

* A bare `Migration` is **strictly less** than a family of transitions: its face maps do not
  determine a residual. `residual_is_not_determined_by_the_face_map` exhibits one face map carrying
  two genuinely different residuals — the exact remainder and the tautological one. This is the
  same reason `Tower.restrictTransition` takes its residual as an argument.
* A bare family of `Transition`s is **strictly less** than a migration: it carries no index functor
  and states no relation between charts. `naturality_is_genuine_content` exhibits a family that
  satisfies every `Transition` law at every index and still fails naturality.
* `ResidualMigration` is exactly the conjunction, and the two presentations are the *same data*:
  `ResidualMigration.ofTransitionFamily` and `ResidualMigration.transition` are mutually inverse by
  `rfl` in both directions. So: **a `ResidualMigration` is precisely an index functor together with
  a family of `Transition`s whose transported maps satisfy naturality** — nothing more and nothing
  less. -/

/-- [definition] Every map is a transition with the **tautological** residual: retain the whole
source. Its existence is why a migration's face maps never determine a residual. -/
def Transition.tautological {Source : Type u} {Target : Type v} (g : Source → Target) :
    Transition Source Target where
  Residual := Source
  apply := g
  residual := _root_.id
  reopen _ r := r
  reopen_apply _ := rfl

/-- [counterexample; formal-checked] One face map, two genuinely different residuals: the exact
remainder merges `4` and `0`, the tautological residual separates them, and both transport the same
face. The residual is therefore data a caller deposits, never a consequence of the face map. -/
theorem residual_is_not_determined_by_the_face_map :
    (∀ x, (coarseGrain 4).apply x = (Transition.tautological fun y : ℕ => y / 4).apply x) ∧
      (coarseGrain 4).residual 4 = (coarseGrain 4).residual 0 ∧
      (Transition.tautological fun y : ℕ => y / 4).residual 4 ≠
        (Transition.tautological fun y : ℕ => y / 4).residual 0 := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · show (4 : ℕ) % 4 = 0 % 4
    rfl
  · show (4 : ℕ) ≠ 0
    omega

/-- [counterexample; formal-checked] A face family that is a perfectly good `Transition` at every
index — `fun x => x + 1` and the identity are both injective, so both have zero residual — and still
fails naturality between charts `0` and `1` of the shift tower. Naturality is genuine content, not
bookkeeping. -/
theorem naturality_is_genuine_content :
    ∃ (g₀ g₁ : ℕ → ℕ) (x : ℕ), Function.Injective g₀ ∧ Function.Injective g₁ ∧
      shiftTower.restrict (Nat.zero_le 1) (g₁ x)
        ≠ g₀ (shiftTower.restrict (Nat.zero_le 1) x) := by
  refine ⟨_root_.id, fun y => y + 1, 0, fun _ _ h => h, fun _ _ h => by simpa using h, ?_⟩
  intro hcontra
  have hbad : (2 : ℕ) = 1 := hcontra
  omega

/-- [definition] A **residual migration**: a migration together with what each of its face maps
drops, and the executable reopening that uses it. The residual is *supplied*, exactly as in
`Tower.restrictTransition`: naturality says what a migration preserves, never what it drops.

Rust counterpart: `continuing_tower.rs::ResidualMigration`. -/
structure ResidualMigration {IndexS : Type u} [Preorder IndexS] {IndexT : Type u₂} [Preorder IndexT]
    (S : Tower.{u, v} IndexS) (T : Tower.{u₂, v₂} IndexT) extends Migration S T where
  /-- What the face map at one target chart does not transport. -/
  Residual : IndexT → Type w
  /-- What it drops, retained. -/
  residual : ∀ j : IndexT, S.Face (index j) → Residual j
  /-- Reconstruct the source face from the migrated face and the retained residual. -/
  reopen : ∀ j : IndexT, T.Face j → Residual j → S.Face (index j)
  /-- The migrated face together with the residual is exactly the source face. -/
  reopen_apply : ∀ (j : IndexT) (x : S.Face (index j)),
    reopen j (face j x) (residual j x) = x

namespace ResidualMigration

variable {IndexS : Type u} [Preorder IndexS] {IndexT : Type u₂} [Preorder IndexT]
variable {S : Tower.{u, v} IndexS} {T : Tower.{u₂, v₂} IndexT}

/-- [proved-derived; formal-checked] Each chart of a residual migration **is** a `Transition` in the
sense of C4, with the same `reopen_apply` law. -/
def transition (M : ResidualMigration S T) (j : IndexT) :
    Transition (S.Face (M.index j)) (T.Face j) where
  Residual := M.Residual j
  apply := M.face j
  residual := M.residual j
  reopen := M.reopen j
  reopen_apply := M.reopen_apply j

/-- [proved-derived; formal-checked] Conversely, an index functor together with a family of
`Transition`s whose transported maps satisfy naturality **is** a residual migration. Nothing else is
needed. -/
def ofTransitionFamily (index : IndexT → IndexS)
    (index_mono : ∀ {i j : IndexT}, i ≤ j → index i ≤ index j)
    (f : ∀ j : IndexT, Transition (S.Face (index j)) (T.Face j))
    (naturality : ∀ {i j : IndexT} (h : i ≤ j) (x : S.Face (index j)),
      T.restrict h ((f j).apply x) = (f i).apply (S.restrict (index_mono h) x)) :
    ResidualMigration S T where
  index := index
  index_mono := index_mono
  face j := (f j).apply
  naturality := naturality
  Residual j := (f j).Residual
  residual j := (f j).residual
  reopen j := (f j).reopen
  reopen_apply j := (f j).reopen_apply

/-- [proved-derived; formal-checked] One direction of the round trip, by `rfl`. -/
theorem transition_ofTransitionFamily (index : IndexT → IndexS)
    (index_mono : ∀ {i j : IndexT}, i ≤ j → index i ≤ index j)
    (f : ∀ j : IndexT, Transition (S.Face (index j)) (T.Face j))
    (naturality : ∀ {i j : IndexT} (h : i ≤ j) (x : S.Face (index j)),
      T.restrict h ((f j).apply x) = (f i).apply (S.restrict (index_mono h) x)) (j : IndexT) :
    (ofTransitionFamily index index_mono f naturality).transition j = f j := rfl

/-- [proved-derived; formal-checked] The other direction of the round trip, by `rfl`. A residual
migration and an index functor with a natural family of transitions are the **same data**. -/
theorem ofTransitionFamily_transition (M : ResidualMigration S T) :
    ofTransitionFamily M.index M.index_mono M.transition M.naturality = M := rfl

/-- [proved-derived; formal-checked] **The two routes around the naturality square transport the
same face.** -/
theorem square_routes_agree (M : ResidualMigration S T) {i j : IndexT} (h : i ≤ j)
    (restrS : Transition (S.Face (M.index j)) (S.Face (M.index i)))
    (hS : ∀ x, restrS.apply x = S.restrict (M.index_mono h) x)
    (restrT : Transition (T.Face j) (T.Face i))
    (hT : ∀ y, restrT.apply y = T.restrict h y)
    (x : S.Face (M.index j)) :
    (Transition.comp restrT (M.transition j)).apply x
      = (Transition.comp (M.transition i) restrS).apply x := by
  show restrT.apply (M.face j x) = M.face i (restrS.apply x)
  rw [hT, hS]
  exact M.naturality h x

/-- [proved-derived; formal-checked] **Either retained residual pair reopens the source exactly.**
This is the schema-history and lossy-codec statement in full: an object saved under the chart family
`S` at chart `index j`, read under the chart family `T` at the coarser chart `i`, presents one
transported face; restricting-then-migrating and migrating-then-restricting retain *different*
residual pairs, and each of them reconstructs the original source face with no remainder. A reader
that kept either pair has lost nothing. -/
theorem square_either_route_reopens (M : ResidualMigration S T) {i j : IndexT}
    (h : i ≤ j)
    (restrS : Transition (S.Face (M.index j)) (S.Face (M.index i)))
    (hS : ∀ x, restrS.apply x = S.restrict (M.index_mono h) x)
    (restrT : Transition (T.Face j) (T.Face i))
    (hT : ∀ y, restrT.apply y = T.restrict h y)
    (x : S.Face (M.index j)) :
    (Transition.comp restrT (M.transition j)).reopen (T.restrict h (M.face j x))
        ((Transition.comp restrT (M.transition j)).residual x) = x ∧
      (Transition.comp (M.transition i) restrS).reopen (T.restrict h (M.face j x))
        ((Transition.comp (M.transition i) restrS).residual x) = x := by
  have h1 : (Transition.comp restrT (M.transition j)).apply x = T.restrict h (M.face j x) := by
    show restrT.apply (M.face j x) = _
    rw [hT]
  have h2 : (Transition.comp (M.transition i) restrS).apply x = T.restrict h (M.face j x) := by
    rw [← h1]
    exact (M.square_routes_agree h restrS hS restrT hT x).symm
  constructor
  · rw [← h1]
    exact (Transition.comp restrT (M.transition j)).reopen_apply x
  · rw [← h2]
    exact (Transition.comp (M.transition i) restrS).reopen_apply x

end ResidualMigration

/-! ### Where a migration goes that the tower cannot: the non-factoring condition

[definition] Inside one tower, passage follows refinement and nothing else. `Tower.restrict` is
typed `i ≤ j → Face j → Face i`, so between two **incomparable** charts there is no passage at all —
and a common refinement does not supply one either, because a span `Face i ← Face k → Face j` is not
a map `Face i → Face j`; the leg into `k` runs against the restriction. Together with
`Tower.restrict_self_eq_id` and `Tower.restrict_roundTrip` — which already show a tower cannot carry
a loop — this fixes what a single tower is: passage along its own order, and nothing else.

A `Migration` need not respect that. The predicates below separate the migrations that add no
passage from the ones that do, and the separation is decided by the **index map alone**. -/

namespace Migration

variable {Index : Type u} [Preorder Index] {S : Tower.{u, v} Index} {T : Tower.{u, v₂} Index}

/-- [definition] A migration **stays at its chart** when its index map is the identity: it reads
exactly the chart it writes and relates no two charts at all. -/
def StaysAtItsChart (M : Migration S T) : Prop := ∀ j, M.index j = j

/-- [definition] A migration **follows refinement** when every chart it reads already refines the
chart it writes. Its components then have the same domain and codomain as the tower's own
restrictions, so they *could* be that passage. -/
def FollowsRefinement (M : Migration S T) : Prop := ∀ j, j ≤ M.index j

/-- [definition] A migration **connects incomparable charts** when some chart it reads is
incomparable with the chart it writes. Neither tower's restriction offers any passage between such a
pair, and a common refinement supplies none either, so at that chart the migration is passage the
towers do not have. This is the non-factoring condition. -/
def ConnectsIncomparableCharts (M : Migration S T) : Prop :=
  ∃ j, ¬ (j ≤ M.index j) ∧ ¬ (M.index j ≤ j)

/-- [definition] A migration of one tower into itself **factors through refinement** when it follows
refinement *and* every component is that tower's own restriction along it. Such a migration is
exactly the composite "read the finer chart, restrict back down": it adds nothing the tower did not
already own. -/
structure FactorsThroughRefinement {Index : Type u} [Preorder Index] {T : Tower.{u, v} Index}
    (M : Migration T T) : Prop where
  /-- Every chart read refines the chart written. -/
  refines : ∀ j, j ≤ M.index j
  /-- Every component is the tower's own restriction along that refinement. -/
  isRestriction : ∀ j x, M.face j x = T.restrict (refines j) x

/-- [proved-derived; formal-checked] Staying at its chart implies following refinement. -/
theorem followsRefinement_of_staysAtItsChart {M : Migration S T} (h : M.StaysAtItsChart) :
    M.FollowsRefinement := fun j => (h j).ge

/-- [proved-derived; formal-checked] A migration that stays at its chart connects no incomparable
charts: it relates each chart only to itself. -/
theorem not_connectsIncomparableCharts_of_staysAtItsChart {M : Migration S T}
    (h : M.StaysAtItsChart) : ¬ M.ConnectsIncomparableCharts := by
  rintro ⟨j, hne, -⟩
  exact hne ((h j).ge)

/-- [proved-derived; formal-checked] Following refinement already excludes the non-factoring
condition: the two are contradictory at the level of the index map alone. -/
theorem not_connectsIncomparableCharts_of_followsRefinement
    {Index : Type u} [Preorder Index] {S : Tower.{u, v} Index} {T : Tower.{u, v₂} Index}
    {M : Migration S T} (h : M.FollowsRefinement) : ¬ M.ConnectsIncomparableCharts := by
  rintro ⟨j, hne, -⟩
  exact hne (h j)

/-- [proved-derived; formal-checked] **The non-factoring theorem.** A migration that connects
incomparable charts does not factor through refinement — there is no refinement for it to factor
through. -/
theorem not_factorsThroughRefinement_of_connectsIncomparableCharts
    {Index : Type u} [Preorder Index] {T : Tower.{u, v} Index} {M : Migration T T}
    (h : M.ConnectsIncomparableCharts) : ¬ M.FactorsThroughRefinement := by
  rintro ⟨refines, -⟩
  obtain ⟨j, hne, -⟩ := h
  exact hne (refines j)

/-- [proved-derived; formal-checked] The identity migration factors through refinement, with the
reflexive refinement and `Tower.restrict_refl`. -/
theorem identity_factorsThroughRefinement {Index : Type u} [Preorder Index]
    (T : Tower.{u, v} Index) : (Migration.identity T).FactorsThroughRefinement where
  refines j := le_refl j
  isRestriction j x := (T.restrict_refl j x).symm

end Migration

/-! #### A migration that connects incomparable charts, and an index with no common refinement -/

/-- [definition] Two charts with no refinement between them: the discrete order on a two-element
index. Nothing refines both, so the two charts have no common refinement at all. -/
inductive TwoCharts
  | left
  | right
  deriving DecidableEq, Repr

instance : Preorder TwoCharts where
  le i j := i = j
  le_refl _ := rfl
  le_trans _ _ _ hij hjk := hij.trans hjk

/-- [proved-derived; formal-checked] The two charts have **no common refinement at all**. A
migration between them is therefore the only passage there is; there is no "refine to a common upper
bound and restrict back" route to compare it with, not merely an unproved one. -/
theorem twoCharts_no_common_refinement :
    ¬ ∃ k : TwoCharts, TwoCharts.left ≤ k ∧ TwoCharts.right ≤ k := by
  rintro ⟨k, hl, hr⟩
  exact TwoCharts.noConfusion ((hl : TwoCharts.left = k).trans (hr : TwoCharts.right = k).symm)

/-- [definition] One face type at both charts of that index; the only admitted restriction is the
identity at each chart. -/
def twoChartTower (X : Type v) : Tower.{0, v} TwoCharts where
  Face _ := X
  restrict _ x := x
  restrict_refl _ _ := rfl
  restrict_trans _ _ _ := rfl

/-- [definition] The migration that reads the *other* chart at every chart. Its index map is
monotone (vacuously, since the order is discrete) and its naturality squares are all reflexive, so
it is a lawful `Migration` — and it supplies a passage between two charts that the tower itself
relates in no way whatsoever. -/
def swapMigration (X : Type v) : Migration (twoChartTower X) (twoChartTower X) where
  index
    | .left => .right
    | .right => .left
  index_mono := by
    intro i j h
    have hij : i = j := h
    subst hij
    rfl
  face _ x := x
  naturality _ _ := rfl

/-- [counterexample; formal-checked] It connects incomparable charts. -/
theorem swapMigration_connectsIncomparableCharts (X : Type v) :
    (swapMigration X).ConnectsIncomparableCharts := by
  refine ⟨TwoCharts.left, ?_, ?_⟩
  · intro h
    exact TwoCharts.noConfusion (h : TwoCharts.left = TwoCharts.right)
  · intro h
    exact TwoCharts.noConfusion (h : TwoCharts.right = TwoCharts.left)

/-- [counterexample; formal-checked] Hence it does not factor through refinement. **Some migration
has the non-factoring property, so the property is not vacuous.** -/
theorem swapMigration_not_factorsThroughRefinement (X : Type v) :
    ¬ (swapMigration X).FactorsThroughRefinement :=
  Migration.not_factorsThroughRefinement_of_connectsIncomparableCharts
    (swapMigration_connectsIncomparableCharts X)

/-- [proved-derived; formal-checked] **`Rebase` factors trivially.** Its index map is the identity,
so it stays at its chart, follows refinement, and connects no incomparable charts. The invertible
instance adds no passage: it relabels the charts it already had. -/
theorem rebaseMigration_staysAtItsChart {Src Tgt Fce : Type v} {Src' Tgt' Fce' : Type v₂}
    {left : Holon.{v, v, v, v} Src Tgt Fce} {right : Holon.{v₂, v₂, v₂, v₂} Src' Tgt' Fce'}
    (R : Holon.Rebase left right) : (rebaseMigration R).StaysAtItsChart := fun _ => rfl

/-- [proved-derived; formal-checked] And therefore it is not a non-factoring migration. -/
theorem rebaseMigration_not_connectsIncomparableCharts {Src Tgt Fce : Type v}
    {Src' Tgt' Fce' : Type v₂}
    {left : Holon.{v, v, v, v} Src Tgt Fce} {right : Holon.{v₂, v₂, v₂, v₂} Src' Tgt' Fce'}
    (R : Holon.Rebase left right) : ¬ (rebaseMigration R).ConnectsIncomparableCharts :=
  Migration.not_connectsIncomparableCharts_of_staysAtItsChart (rebaseMigration_staysAtItsChart R)

/-! ### The reverse passage is exactly the retained residual

[definition] A migration's component carries a face forward. Whether anything comes back is a
separate question, and the answer is decided by the residual and by nothing else. -/

namespace Migration

variable {IndexS : Type u} [Preorder IndexS] {IndexT : Type u₂} [Preorder IndexT]
variable {S : Tower.{u, v} IndexS} {T : Tower.{u₂, v₂} IndexT}

/-- [definition] A **reverse passage from the migrated face alone** at one chart: a map back that
returns the source face with nothing else retained. -/
def ReversePassage (M : Migration S T) (j : IndexT) : Prop :=
  ∃ back : T.Face j → S.Face (M.index j), ∀ x, back (M.face j x) = x

/-- [proved-derived; formal-checked] A reverse passage from the face alone forces the component to
be injective: it can have merged nothing. -/
theorem injective_of_reversePassage (M : Migration S T) {j : IndexT} (h : M.ReversePassage j) :
    Function.Injective (M.face j) := by
  obtain ⟨back, hback⟩ := h
  intro a b hab
  rw [← hback a, ← hback b, hab]

/-- [proved-derived; formal-checked] And conversely, an injective component already has one. -/
theorem reversePassage_of_injective (M : Migration S T) {j : IndexT}
    [Nonempty (S.Face (M.index j))] (h : Function.Injective (M.face j)) : M.ReversePassage j :=
  ⟨Function.invFun (M.face j), Function.leftInverse_invFun h⟩

/-- [proved-derived; formal-checked] **A lossy component is one-way.** If the component merges two
source faces there is no reverse passage from the migrated face alone: you coarse-grain across and
do not return. -/
theorem not_reversePassage_of_not_injective (M : Migration S T) {j : IndexT}
    (h : ¬ Function.Injective (M.face j)) : ¬ M.ReversePassage j :=
  fun hr => h (M.injective_of_reversePassage hr)

end Migration

namespace ResidualMigration

variable {IndexS : Type u} [Preorder IndexS] {IndexT : Type u₂} [Preorder IndexT]
variable {S : Tower.{u, v} IndexS} {T : Tower.{u₂, v₂} IndexT}

/-- [proved-derived; formal-checked] **Retaining the residual makes the passage two-way**, lossy
component or not. This is `reopen_apply` read as a reverse passage, and it is exact — the source
face is returned, not approximated. -/
theorem residual_reverse_passage (M : ResidualMigration S T) (j : IndexT)
    (x : S.Face (M.index j)) : M.reopen j (M.face j x) (M.residual j x) = x :=
  M.reopen_apply j x

/-- [proved-derived; formal-checked] A residual that carries no information is a residual that was
not needed: the component is already injective and the passage was already two-way from the face
alone. -/
theorem injective_of_subsingleton_residual (M : ResidualMigration S T) (j : IndexT)
    (h : Subsingleton (M.Residual j)) : Function.Injective (M.face j) :=
  (M.transition j).injective_of_subsingleton_residual h

/-- [proved-derived; formal-checked] **Traversability is the residual.** At one chart, the passage
is two-way *from the migrated face alone* exactly when the component is injective — equivalently,
exactly when the residual could have been dropped. When it is not injective, the retained residual
is what restores the reverse passage, and it restores it exactly.

This is the sharp form of the relation between `Migration` and `Transition`: a `Migration` carries
the forward passage and the naturality that ties its charts together; a `Transition` at each chart
adds precisely the return. Neither contains the other, and `ResidualMigration` is the conjunction —
see `ofTransitionFamily_transition`, which is the `rfl` proof that it is exactly that. -/
theorem traversability_is_the_residual (M : ResidualMigration S T) (j : IndexT)
    [Nonempty (S.Face (M.index j))] :
    (M.toMigration.ReversePassage j ↔ Function.Injective (M.face j)) ∧
      ∀ x, M.reopen j (M.face j x) (M.residual j x) = x :=
  ⟨⟨fun h => M.toMigration.injective_of_reversePassage h,
      fun h => M.toMigration.reversePassage_of_injective h⟩,
    M.reopen_apply j⟩

end ResidualMigration

/-! ### The cost comparison's shape

[definition] Carrier item **C5** — the cost enrichment — is owned by
`Foundation/PresentationCost.lean`, not here: `ComputableTower.cost` is a declared `ℕ` and
`Foundation/ReceiverCodeCost.lean:100-126`'s `serial_boundary_balance` owns the additivity law C5
instantiates. This file states only the shape of the comparison over an ordered cost supplied by
the caller. `PresentationCost.costBoundedByRefinementRoute_is_caller_decided` proves that shape
carries no content by itself — one migration and one migration cost are bounded under one route
cost and unbounded under another — and `costBoundedByRefinementRoute_of_route` discharges it over
every `CostedTower` for every migration that `FactorsThroughRefinement`.

What that discharge is worth is fixed by the supply of costed towers, and that supply is exhibited
there rather than assumed: `PresentationCost.padicCostedTower` is this file's `padicTower` with the
receipt each restriction determines (digit gap, and `codeBits` of `padicRestrictTransition`'s own
residual fibre), `unitCostedTower` is the minimal instance, and
`PresentationCost.costBoundedByRefinementRoute_padic` is the comparison discharged at
`padicHalfMigration` with neither side supplied by a caller. The tower's law is a condition and not
a corollary of `serial_boundary_balance`: `serial_boundary_balance` gives the two-step *total*, and
`PresentationCost.no_costedTower_with_squaredGapReceipt` exhibits a receipt assignment whose direct
restriction exceeds that total, so no costed tower carries it.

For a migration that connects incomparable charts the comparison is undefined: by
`twoCharts_no_common_refinement` there may be no refinement route at all
(`PresentationCost.swapMigration_route_isEmpty`), so the right-hand cost has nothing to measure. -/

/-- [definition] The open cost comparison between a migration and the "refine to a common chart,
then restrict back" route, over a caller-supplied ordered cost. Discharged over a concrete cost in
`Foundation/PresentationCost.lean`. -/
def Migration.CostBoundedByRefinementRoute {IndexS : Type u} [Preorder IndexS]
    {IndexT : Type u₂} [Preorder IndexT] {S : Tower.{u, v} IndexS} {T : Tower.{u₂, v₂} IndexT}
    {W : Type w} [Preorder W] (M : Migration S T)
    (migrationCost refinementRouteCost : ∀ j : IndexT, S.Face (M.index j) → W) : Prop :=
  ∀ (j : IndexT) (x : S.Face (M.index j)), migrationCost j x ≤ refinementRouteCost j x

/-! ### A concrete non-invertible migration on the canonical instance -/

section PadicMigration

variable (p : ℕ) [Fact p.Prime]

/-- [definition] **A lossy schema migration.** The new chart family reads level `j` of the old
family at level `j + j` and keeps only the low half; the digit block it drops is the residual, and
C2's `padicReopenGap` is the executable reopening. Every face map is genuinely non-invertible, and
the migration is still a migration: naturality is `Tower.restrict_trans`.

Rust counterpart: `continuing_tower.rs::HalvingMigration`. -/
def padicHalfMigration : ResidualMigration (padicTower p) (padicTower p) where
  index j := j + j
  index_mono h := Nat.add_le_add h h
  face j x := (padicTower p).restrict (Nat.le_add_right j j) x
  naturality h x := by
    rw [(padicTower p).restrict_trans, (padicTower p).restrict_trans]
  Residual j := ZMod (p ^ j)
  residual j x := padicDigitGap p j j x
  reopen j f d := padicReopenGap p j j f d
  reopen_apply j x := padicReopenGap_restrict p j j x

/-- [proved-derived; formal-checked] Each chart of that migration is exactly C2's restriction
transition, by `rfl`: the migration's residual and the splitting's coset index are one object. -/
theorem padicHalfMigration_transition (j : ℕ) :
    (padicHalfMigration p).transition j = padicRestrictTransition p j j := rfl

/-- [proved-derived; formal-checked] **The continuing object survives the lossy migration.** Every
face map of `padicHalfMigration` drops `p ^ j` cosets, and yet the `p`-adic integer saved under the
old chart family is read back as *the same* `p`-adic integer under the new one. The object is the
carrier; the faces are not. -/
theorem padicHalfMigration_carrySection (a : ℤ_[p]) :
    (padicHalfMigration p).toMigration.carrySection (padicSection p a) = padicSection p a :=
  Tower.CompatibleSection.ext fun j => (padicSection p a).compatible (Nat.le_add_right j j)

/-- [proved-derived; formal-checked] And the migration really is lossy at every positive chart: its
residual merges the `p ^ j` faces of one fibre, which is C2's exact splitting read as C4's residual.
-/
theorem padicHalfMigration_face_fibre_card (j : ℕ) (f : ZMod (p ^ j)) :
    Nat.card { x : ZMod (p ^ (j + j)) // (padicHalfMigration p).face j x = f } = p ^ j :=
  padicFibre_card p j j f

/-- [proved-derived; formal-checked] **The lossy schema migration still factors through
refinement.** Its index map only ever goes to a finer chart and its components *are* the tower's own
restrictions, so it adds no passage: it is a move along the tower, not across it. Lossiness and
non-factoring are independent properties. -/
theorem padicHalfMigration_factorsThroughRefinement :
    (padicHalfMigration p).toMigration.FactorsThroughRefinement where
  refines j := Nat.le_add_right j j
  isRestriction _ _ := rfl

/-- [proved-derived; formal-checked] Its component at a positive chart is not injective: C2's
splitting merges exactly `p ^ j` faces there. -/
theorem padicHalfMigration_face_not_injective (j : ℕ) (hj : 0 < j) :
    ¬ Function.Injective ((padicHalfMigration p).face j) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpow : 1 < p ^ j := by
    calc 1 < p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ j := Nat.pow_le_pow_right (by omega) hj
  have : Nontrivial (ZMod (p ^ j)) := ZMod.nontrivial_iff.mpr (by omega)
  intro hinj
  have h01 : padicReopenGap p j j 0 0 = padicReopenGap p j j 0 1 := by
    apply hinj
    show (padicTower p).restrict (Nat.le_add_right j j) (padicReopenGap p j j 0 0)
      = (padicTower p).restrict (Nat.le_add_right j j) (padicReopenGap p j j 0 1)
    rw [padicRestrict_reopenGap, padicRestrict_reopenGap]
  have hdig := congrArg (padicDigitGap p j j) h01
  rw [padicDigitGap_reopenGap, padicDigitGap_reopenGap] at hdig
  exact zero_ne_one hdig

/-- [counterexample; formal-checked] **So the migrated face alone is one-way at every positive
chart**: nothing carries it back. -/
theorem padicHalfMigration_no_reverse_passage (j : ℕ) (hj : 0 < j) :
    ¬ (padicHalfMigration p).toMigration.ReversePassage j :=
  Migration.not_reversePassage_of_not_injective _ (padicHalfMigration_face_not_injective p j hj)

/-- [proved-derived; formal-checked] **And the retained residual restores it, exactly.** The same
chart at which no reverse passage exists from the face alone is reopened with no remainder once the
digit block is kept. Traversability is the residual. -/
theorem padicHalfMigration_residual_restores_the_reverse_passage (j : ℕ)
    (x : ZMod (p ^ (j + j))) :
    (padicHalfMigration p).reopen j ((padicHalfMigration p).face j x)
      ((padicHalfMigration p).residual j x) = x :=
  (padicHalfMigration p).reopen_apply j x

end PadicMigration

end Soma.Holonics.Foundation.ContinuingTower

section Audit
open Soma.Holonics.Foundation.ContinuingTower

#print axioms Tower.gluingResult_total
#print axioms Tower.restrict_self_eq_id
#print axioms Tower.restrict_roundTrip
#print axioms ComputableTower.section
#print axioms Tower.compatible_of_adjacent
#print axioms Tower.nonempty_compatibleSection_of_surjectiveAdjacent
#print axioms Tower.carried_iff_observationFibre
#print axioms Tower.gluingPassage_glues_iff
#print axioms Tower.obstruction_nonempty_iff
#print axioms Tower.observationFibre_eq_preimageFibre
#print axioms Tower.observationFibreEquivPreimageFibre
#print axioms Tower.chartReceiverTransformer_iff
#print axioms Transition.apply_residual_injective
#print axioms Transition.laterReceiverFactors
#print axioms Transition.residual_separates
#print axioms Transition.residual_separates_insufficiency
#print axioms Transition.ofEquiv_residual_subsingleton
#print axioms Transition.injective_of_subsingleton_residual
#print axioms Transition.equivOfSubsingletonResidual
#print axioms Transition.ofInjective
#print axioms Transition.comp_apply
#print axioms Transition.comp_residual
#print axioms Transition.comp_residual_subsingleton
#print axioms Transition.comp_assoc_apply
#print axioms Transition.compAssocResidualEquiv
#print axioms Transition.compAssocResidualEquiv_residual
#print axioms Transition.ofLinearSection
#print axioms Transition.ofLinearSection_residual_receiverBlind
#print axioms Transition.toReceiverHistoryCompression
#print axioms Transition.apply_transportWord
#print axioms Transition.residual_reopens_after_word
#print axioms Tower.restrictTransition
#print axioms Tower.restrictTransition_comp_apply
#print axioms Tower.section_witness_reopened
#print axioms unitTower_gluing
#print axioms padicTower_restrict_surjective
#print axioms padicSection
#print axioms padicSection_zero_ne_one_at_one
#print axioms padicTower_plural
#print axioms padicTower_gluing
#print axioms padicTower_nonempty_via_successorWitness
#print axioms padicChartInsufficiency
#print axioms shiftTower_face_nonempty
#print axioms shiftTower_obstructed
#print axioms shiftTower_gluing
#print axioms shiftTower_adjacent_not_surjective
#print axioms shiftTower_obstruction_nonempty
#print axioms shiftTower_not_glues
#print axioms boolFlipSelfLoop_isEmpty
#print axioms coarseGrain_not_injective
#print axioms coarseGrain_comp_apply
#print axioms coarseGrain_residual
#print axioms coarseGrain_comp_residual_pair
#print axioms coarseGrain_comp_residual_reassembles
#print axioms shiftTower_restrict_injective
#print axioms theOrderFaceDoesNotDetermineTheModule
#print axioms Tower.CompatibleSection.ext
#print axioms padicSectionSeq_dvd
#print axioms padicOfSection
#print axioms toZModPow_padicOfSection
#print axioms padicSectionEquiv
#print axioms padicSection_injective
#print axioms padic_toZModPow_surjective
#print axioms padicReopenGap_val
#print axioms padicRestrict_reopenGap
#print axioms padicDigitGap_reopenGap
#print axioms padicReopenGap_restrict
#print axioms padicFibreEquiv
#print axioms padicFibre_card
#print axioms padicAdjacentFibre_card
#print axioms padic_sameFace_iff_sub_mem_ker
#print axioms padicObservationFibre_reaches_exactly_p
#print axioms padicRestrictTransition
#print axioms padicRestrictTransition_residual
#print axioms padicRestrictTransition_residual_complete
#print axioms Migration.identity
#print axioms Migration.comp
#print axioms Migration.comp_assoc
#print axioms Migration.comp_identity
#print axioms Migration.identity_comp
#print axioms Migration.carrySection
#print axioms Migration.carrySection_comp
#print axioms Migration.carrySection_identity
#print axioms Migration.carrySection_witness
#print axioms Migration.carryObservationFibre
#print axioms DiagramIndex.not_le_of_ne
#print axioms diagramTower
#print axioms diagramTowerSectionEquiv
#print axioms rebaseFaceEquiv
#print axioms rebaseMigration
#print axioms rebaseMigrationTransition
#print axioms rebaseMigration_residual_subsingleton
#print axioms rebaseMigration_face_eq
#print axioms rebaseMigration_carryObservationFibre_occurrence
#print axioms rebase_preimageFibreEquiv_occurrence
#print axioms Transition.tautological
#print axioms residual_is_not_determined_by_the_face_map
#print axioms naturality_is_genuine_content
#print axioms ResidualMigration.transition
#print axioms ResidualMigration.ofTransitionFamily
#print axioms ResidualMigration.transition_ofTransitionFamily
#print axioms ResidualMigration.ofTransitionFamily_transition
#print axioms ResidualMigration.square_routes_agree
#print axioms ResidualMigration.square_either_route_reopens
#print axioms padicHalfMigration
#print axioms padicHalfMigration_transition
#print axioms padicHalfMigration_carrySection
#print axioms padicHalfMigration_face_fibre_card
#print axioms Migration.followsRefinement_of_staysAtItsChart
#print axioms Migration.not_connectsIncomparableCharts_of_staysAtItsChart
#print axioms Migration.not_connectsIncomparableCharts_of_followsRefinement
#print axioms Migration.not_factorsThroughRefinement_of_connectsIncomparableCharts
#print axioms Migration.identity_factorsThroughRefinement
#print axioms twoCharts_no_common_refinement
#print axioms twoChartTower
#print axioms swapMigration
#print axioms swapMigration_connectsIncomparableCharts
#print axioms swapMigration_not_factorsThroughRefinement
#print axioms rebaseMigration_staysAtItsChart
#print axioms rebaseMigration_not_connectsIncomparableCharts
#print axioms Migration.injective_of_reversePassage
#print axioms Migration.reversePassage_of_injective
#print axioms Migration.not_reversePassage_of_not_injective
#print axioms ResidualMigration.residual_reverse_passage
#print axioms ResidualMigration.injective_of_subsingleton_residual
#print axioms ResidualMigration.traversability_is_the_residual
#print axioms padicHalfMigration_factorsThroughRefinement
#print axioms padicHalfMigration_face_not_injective
#print axioms padicHalfMigration_no_reverse_passage
#print axioms padicHalfMigration_residual_restores_the_reverse_passage
#print axioms Migration.StaysAtItsChart
#print axioms Migration.FollowsRefinement
#print axioms Migration.ConnectsIncomparableCharts
#print axioms Migration.FactorsThroughRefinement
#print axioms Migration.ReversePassage
#print axioms Migration.CostBoundedByRefinementRoute
end Audit
