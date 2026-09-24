import Holonics.Transport.WorldTube
import Holonics.Foundation.ContinuingTower
import Holonics.Foundation.BoundaryScalePassage
import Holonics.Foundation.GrainRestriction
import Holonics.Foundation.ReceiverAtlas
import Holonics.Foundation.ReceiverRelease

/-!
# The continuing tube: a tower is the transverse section of a tube, and a wormhole is exact

[definition] This file is the **join** between two families the repository already owned and never
connected: the *tube* family of `Transport/WorldTube.lean` and the *tower* family of
`Foundation/ContinuingTower.lean`. It founds no third carrier. Every law below is either one of
those owners' laws instantiated at the join, or a statement about how the two axes meet.

## What a tube is, in this repository's own terms

[established-bounded; source-inspected] A tube has **two axes**, and the repository owns one apiece.

* The **longitudinal** axis is `Transport/WorldTube.lean`'s `ClockedSpan`: an addressed occurrence
  population with both boundary maps, an exact local-clock face, a returned receiver face and an
  obstruction. Serial contact is the existing pullback join (`ClockedSpan.comp`), re-cutting a
  joined world-line changes only its presentation
  (`ClockedSpan.split_rejoin_preserves_completeFace`, `ClockedSpan.resegmentation_natural`), and a
  missing joining equality is an open gap with no joined occurrence
  (`ClockedSpan.openGap_has_no_joined_occurrence`). `WorldTube` adds the interior current, the
  outward receiver, lawful silence, the world return and the cultivated rest that descends through
  every finite ordered successor word.
* The **transverse** axis is `Foundation/ContinuingTower.lean`'s `Tower`: the faces presented at
  each aperture/grain/chart/precision of one index, with `restrict` the only transport and
  `restrict_refl`/`restrict_trans` its two laws.

[definition] **A `Tower` is therefore one chart of a tube — its cross-sectional ladder — and not a
separate object.** "Tower" is inherited Iwasawa vocabulary for exactly that ladder, and the Iwasawa
tower keeps the name as the instance it names: `padicTower` is the cross-section whose refinement
branches `p`-adically (`padicFibre_card = p ^ k`), whose branching is a `p`-ary tree, and whose end
is `ℤ_[p]` (`padicSectionEquiv`). A tube is a tower *stretched along a longitudinal axis*; a
staircase between two grains is a move **along the transverse axis**, and a passage between two
stations is a move **along the longitudinal axis**.

## The law that joins them

[proved-derived; formal-checked] The two axes are joined by exactly one law: **longitudinal
transport and transverse restriction commute**. That law is not new — it *is*
`Foundation/ContinuingTower.lean::Migration.naturality` with the index map the identity, and
`ChartwiseMigration` below is proved to be precisely a `Migration` that `StaysAtItsChart`
(`toMigration_staysAtItsChart`, `ofStationaryMigration`, `ofStationaryMigration_toMigration_face`).
A `Tube` is then a preorder-indexed family of towers with those migrations between
stations, and `Tube.square` is the commuting square.

[proved-derived; formal-checked] Where the square **fails**, the failure is the content and is
returned whole: `SquareVerdict` is `commutes | defect`, `squareVerdict_total` makes it total, and
`grainSquareDefect` is a real instance — the contact receiver does not commute with the grain
selection, which is `Foundation/GrainRestriction.lean::equal_aperture_is_not_lawful` and, on the M5
deposit, the measured 301 against 1,397 `Inside` readings recorded in that file's header.

## The wormhole, made exact

[definition] `research/records/2026-07-26_THE_TUBE_CARRIES_THE_EXTERIOR_FACE_THE_DISTANT_FIELD_RETURNS_THROUGH_REBASE.md:222`
fixes what a wormhole owes: "a founded throat joining two actual mouths", with both transports, a
loop holonomy `Ω_loop`, a source deed and a transport cost — never zero-cost transport and never a
hidden pointer. `docs/canon/TABLET_THE_CHART.md:263` fixes what it *is*: "passage through a chart
where the answer is one step, when in the source chart it is not reachable at all."

[definition] Both readings name one already-owned predicate. A tube's own passages are its
longitudinal transports composed with transverse restrictions, and every one of those **follows
refinement** (`refinementRoute_followsRefinement`). A passage that does not is one whose index map
crosses to a chart the tube's order does not relate — `Migration.ConnectsIncomparableCharts`. So:

* `Wormhole` is a passage between two stations that connects incomparable charts;
* `transport_is_not_a_wormhole` and `refinementRoute_is_not_a_wormhole` prove a tube's own passages
  never are;
* `swapWormhole` is one, over `twoCharts_no_common_refinement`'s index, where there is no common
  refinement to compare against — the comparison is undefined, not false;
* traversability is settled by `ResidualMigration.traversability_is_the_residual`, cited not
  reproved, and lossiness is **independent** of being a wormhole:
  `lossiness_is_independent_of_being_a_wormhole` inhabits all four cells, with `padicHalfMigration`
  lossy-and-not-a-wormhole and `lossySwapMigration` both.

## Holonomy, and where non-orientability actually lives

[proved-derived; formal-checked] `Tower.restrict_roundTrip` already shows the **transverse** axis
carries no holonomy: every index round trip is the identity. `transport_roundTrip` proves the same
of the **longitudinal** axis of a tube presented as a functor of its station preorder. So a strictly
functorial tube is no more able to express a loop obstruction than a tower is, and
`tube_circuit_has_no_defect` states it.

[proved-derived; formal-checked] Holonomy therefore lives in a *declared circuit* whose composite is
not the identity on the nose — which is the atlas, not the tube: `ChartwiseMigration.cocycleDefect` builds
`Foundation/ReceiverAtlas.lean::CocycleDefect` from a circuit defect, so
`CocycleDefect.defect_is_holonomy_not_loss` is the statement that both routes reopen their own
source exactly and only the presented face differs. `flipCircuit` is the smallest instance, and
`flipCircuit_carries_no_invariant_end` proves the continuing objects that survive it are empty —
which is `Millennium/HolonicDirectedPassage.lean::boolFlipCoherent_isEmpty` read on a tube closed on
itself. Interlinked toroidal modes are tubes closed on themselves; they are not towers.
`Millennium/HolonicClockedPantographicSwing.lean::ClockRouteComparison.returnedHolonomy_eq_one_iff`
owns the clock-route form of the same fact and is cited, not rebuilt.

## What the existing tube owners already prove, that the carrier should have cited

[established-bounded; source-inspected] `Transport/WorldTubePotential.lean` already proves
`boundaryScale_boundary_image_natural` and `boundaryScale_comp_boundary_image_natural` — the forward
family image law of a `BoundaryScalePassage`, with no inverse assumed. This file adds the missing
structural identification rather than another image law:
**`boundaryScalePassage_is_a_chartwise_migration`** exhibits a `BoundaryScalePassage` as a
`ChartwiseMigration` between two enclosure towers, whose single nonreflexive naturality square *is*
its `boundary_natural` field. The staircase between two grains is therefore a migration of towers,
never a wormhole (`boundaryScale_staircase_is_not_a_wormhole`).

[proved-derived; formal-checked] And the precise relation the plan left unstated: a
`BoundaryScalePassage` is **not** a `Transition`. Its own data determines no residual —
`residual_is_not_determined_by_the_face_map` is the general reason — and
`projectionScalePassage_no_reverse_passage` exhibits a concrete scale passage whose transported face
alone never returns. Supplying the residual at each chart makes it a `ResidualMigration`
(`boundaryScaleResidualMigration`), and then the return is exactly
`ResidualMigration.traversability_is_the_residual`. That is the difference between the two
staircases the repository owns: `BoundaryScalePassage` supplies none and is a migration;
`GrainRestriction.selectionTransition` supplies one and is a transition.

## Rust counterpart

[definition] The paired executable owners are `crates/holonic-core/src/restriction/tube.rs` (the
carrier law, re-exported at `crates/holonic-engine/src/continuing_tube.rs`) and that engine file
(its receiver layers):
`StationedTower`, `check_commuting_square` returning `SquareVerdict::Commutes | ::Defect` with its
witness, `wormhole_receipt`, `check_circuit_holonomy`, and `LossySwapMigration`, tested on the
`p`-adic tower, on `grain_tower.rs`'s measured non-commuting square, and on a closed circuit with
holonomy. `crates/holonic-engine/src/tube.rs::ReceiverTube` is the *physical* realization of the
same two axes — core receiver, transverse section, horizon as the link of the star, and
`presentation_holonomy` as the composite of its longitudinal presentation word — and is cited there.

[definition] What this file does **not** do: it renames nothing, it states no milestone, and it
edits no owner. It founds `ChartwiseMigration`, `Tube`, `SquareVerdict`, `Wormhole`,
`Circuit` and the enclosure tower; everything else is a citation.
-/

namespace Holonics.Transport.ContinuingTube

open Holonics
open Holonics.Foundation.ContinuingTower
open Holonics.Millennium.HolonicSensoryWorldTube
open Holonics.Millennium.HolonicGranularBoundaryRadiation

universe u v v₂ w uS

/-! ## The transverse-preserving step

A tube's longitudinal transport must not move the aperture it reads at. That is exactly a
`Migration` whose index map is the identity, and the following structure carries it with the index
map fixed by construction so that no cast is needed. -/

/-- [definition] A **chartwise migration**: a family of face maps between two towers over one index,
one per chart, satisfying the commuting square with each tower's own restriction.

`naturality` is the whole content and it is the join's only law: restricting after transporting is
transporting after restricting. It is `Foundation/ContinuingTower.lean::Migration.naturality` with
the index map the identity, and `toMigration`/`ofStationaryMigration` prove the two are the same
data.

Rust counterpart: `crates/holonic-core/src/restriction/tube.rs::StationedTower::transport`, whose
square is checked by `check_commuting_square`. -/
structure ChartwiseMigration {Index : Type u} [Preorder Index] (S T : Tower.{u, v} Index) where
  /-- The component at one chart. -/
  face : ∀ i : Index, S.Face i → T.Face i
  /-- **The commuting square.** Restricting after transporting is transporting after restricting. -/
  naturality : ∀ {i j : Index} (h : i ≤ j) (x : S.Face j),
    T.restrict h (face j x) = face i (S.restrict h x)

namespace ChartwiseMigration

variable {Index : Type u} [Preorder Index] {S T U : Tower.{u, v} Index}

/-- [definition] A chartwise migration read as a `Migration` with the identity index map. -/
def toMigration (M : ChartwiseMigration S T) : Migration S T where
  index := _root_.id
  index_mono h := h
  face j := M.face j
  naturality h x := M.naturality h x

/-- [proved-derived; formal-checked] It stays at its chart, by construction. -/
theorem toMigration_staysAtItsChart (M : ChartwiseMigration S T) :
    M.toMigration.StaysAtItsChart := fun _ => rfl

/-- [proved-derived; formal-checked] And therefore connects no incomparable charts: a tube's own
transverse-preserving transport is never a wormhole. -/
theorem toMigration_not_connectsIncomparableCharts (M : ChartwiseMigration S T) :
    ¬ M.toMigration.ConnectsIncomparableCharts :=
  Migration.not_connectsIncomparableCharts_of_staysAtItsChart M.toMigration_staysAtItsChart

/-- [definition] Conversely, a migration that stays at its chart **is** a chartwise migration. The
source face is first carried along the index equality by the source tower's own restriction, which
is the identity there. -/
def ofStationaryMigration (M : Migration S T) (hid : ∀ j, M.index j = j) :
    ChartwiseMigration S T where
  face j x := M.face j (S.restrict (le_of_eq (hid j)) x)
  naturality := by
    intro i j h x
    rw [M.naturality h, S.restrict_trans (M.index_mono h) (le_of_eq (hid j)) x,
      S.restrict_trans (le_of_eq (hid i)) h x]

/-- [proved-derived; formal-checked] The round trip on components: reading a stationary migration as
a chartwise one changes no component, because the index restriction it inserts is a one-chart
restriction and `Tower.restrict_refl` makes that the identity. -/
theorem ofStationaryMigration_face (M : Migration S T) (hid : ∀ j, M.index j = j) (j : Index)
    (x : S.Face j) :
    (ofStationaryMigration M hid).face j x = M.face j (S.restrict (le_of_eq (hid j)) x) := rfl

/-- [proved-derived; formal-checked] And the other round trip is definitional. -/
theorem ofStationaryMigration_toMigration_face (M : ChartwiseMigration S T) (j : Index)
    (x : S.Face j) :
    (ofStationaryMigration M.toMigration M.toMigration_staysAtItsChart).face j x
      = M.face j (S.restrict (le_refl j) x) := rfl

/-- [definition] The identity chartwise migration. -/
protected def id (T : Tower.{u, v} Index) : ChartwiseMigration T T where
  face _ x := x
  naturality _ _ := rfl

/-- [definition] Composition of chartwise migrations, chart by chart. -/
protected def comp (second : ChartwiseMigration T U) (first : ChartwiseMigration S T) :
    ChartwiseMigration S U where
  face i x := second.face i (first.face i x)
  naturality h x := by rw [second.naturality h, first.naturality h]

@[simp] theorem comp_face (second : ChartwiseMigration T U) (first : ChartwiseMigration S T)
    (i : Index) (x : S.Face i) :
    (ChartwiseMigration.comp second first).face i x = second.face i (first.face i x) := rfl

/-- [proved-derived; formal-checked] Chartwise composition **is** `Migration.comp`: the two axes'
composition laws agree where both are defined, and nothing is founded again. -/
theorem comp_toMigration (second : ChartwiseMigration T U) (first : ChartwiseMigration S T) :
    (ChartwiseMigration.comp second first).toMigration
      = Migration.comp second.toMigration first.toMigration := rfl

/-- [definition] A chartwise migration carries a continuing object, by
`Migration.carrySection` — not by a second transport. -/
def carrySection (M : ChartwiseMigration S T) (s : S.CompatibleSection) : T.CompatibleSection :=
  M.toMigration.carrySection s

@[simp] theorem carrySection_witness (M : ChartwiseMigration S T) (s : S.CompatibleSection)
    (i : Index) : (M.carrySection s).witness i = M.face i (s.witness i) := rfl

end ChartwiseMigration

/-! ### The square is genuine content

`naturality_is_genuine_content` already exhibits a face family that is a lawful `Transition` at
every chart and still fails the square. The same fact, stated as the failure of a *family* rather
than of one pair, is what a tube's law actually excludes. -/

/-- [counterexample; formal-checked] A face family over the shift tower that is not a chartwise
migration: shifting by the chart index fails the square between charts `0` and `1`. This is
`Foundation/ContinuingTower.lean::naturality_is_genuine_content` restated for the family. -/
theorem square_is_genuine_content :
    ∃ (g : ℕ → ℕ → ℕ) (i j : ℕ) (h : i ≤ j) (x : ℕ),
      shiftTower.restrict h (g j x) ≠ g i (shiftTower.restrict h x) := by
  refine ⟨fun i x => x + i, 0, 1, Nat.zero_le 1, 0, ?_⟩
  intro hcontra
  have hbad : (2 : ℕ) = 1 := hcontra
  omega

/-! ## The two-axis object -/

/-- [definition] A **continuing tube**: a family of towers over a longitudinal station order,
together with the chartwise migration that transports each station's cross-section to a later one,
and the two functor laws.

`station s` is the **transverse section** at station `s` — its index is the aperture/grain/precision
ladder and its `restrict` is the coarsening of that section. `transport` is the **longitudinal**
passage. `Tube.square` is the one law that joins them, and it is
`ChartwiseMigration.naturality`.

Rust counterpart: `crates/holonic-core/src/restriction/tube.rs::StationedTower`. -/
structure Tube.{us, ui, uf} (Station : Type us) [Preorder Station] (Index : Type ui)
    [Preorder Index] where
  /-- The transverse section at one station. -/
  station : Station → Tower.{ui, uf} Index
  /-- The longitudinal transport along one admitted step, chart by chart. -/
  transport : ∀ {s t : Station}, s ≤ t → ChartwiseMigration (station s) (station t)
  /-- Transporting to the same station changes nothing. -/
  transport_refl : ∀ (s : Station) (i : Index) (x : (station s).Face i),
    (transport (le_refl s)).face i x = x
  /-- Transporting twice is transporting once along the composite step. -/
  transport_trans : ∀ {s t r : Station} (hst : s ≤ t) (htr : t ≤ r) (i : Index)
      (x : (station s).Face i),
    (transport htr).face i ((transport hst).face i x) = (transport (le_trans hst htr)).face i x

namespace Tube

variable {Station : Type uS} [Preorder Station] {Index : Type u} [Preorder Index]
variable (tube : Tube.{uS, u, v} Station Index)

/-- [proved-derived; formal-checked] **The two-axis commuting square.** Restricting the transverse
section after a longitudinal step is the same as taking the step after restricting. This is the
whole law of the join, and it is `Migration.naturality`. -/
theorem square {s t : Station} (hst : s ≤ t) {i j : Index} (h : i ≤ j)
    (x : (tube.station s).Face j) :
    (tube.station t).restrict h ((tube.transport hst).face j x)
      = (tube.transport hst).face i ((tube.station s).restrict h x) :=
  (tube.transport hst).naturality h x

/-- [proved-derived; formal-checked] **A tube presented as a functor of its station order carries no
longitudinal holonomy**, exactly as `Tower.restrict_roundTrip` shows its transverse ladder carries
none: a station round trip is the identity at every chart. -/
theorem transport_roundTrip {s t : Station} (hst : s ≤ t) (hts : t ≤ s) (i : Index)
    (x : (tube.station s).Face i) :
    (tube.transport hts).face i ((tube.transport hst).face i x) = x := by
  rw [tube.transport_trans hst hts i x]
  exact tube.transport_refl s i x

/-- [proved-derived; formal-checked] Composition along the longitudinal axis is independent of how
the station chain is cut; composition along the transverse axis is independent of how the refinement
chain is cut; and re-cutting a joined world-line changes only its presentation. The three are one
statement — *composition does not depend on segmentation* — on the two axes and on the span. The
third is `ClockedSpan.split_rejoin_preserves_completeFace`, cited at `clockedSpan_split_rejoin`
below. -/
theorem segmentation_is_immaterial {s t r : Station} (hst : s ≤ t) (htr : t ≤ r)
    {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k) (x : (tube.station s).Face k) :
    (tube.transport htr).face k ((tube.transport hst).face k x)
        = (tube.transport (le_trans hst htr)).face k x ∧
      (tube.station s).restrict hij ((tube.station s).restrict hjk x)
        = (tube.station s).restrict (le_trans hij hjk) x :=
  ⟨tube.transport_trans hst htr k x, (tube.station s).restrict_trans hij hjk x⟩

/-! ### The end of a tube -/

/-- [definition] The **end** of a tube at one station: the continuing objects of its transverse
section. No face is the object; the compatible section is. -/
def End (s : Station) : Type _ := (tube.station s).CompatibleSection

/-- [definition] Longitudinal transport of an end. This is `Migration.carrySection`, not a second
transport. -/
def carryEnd {s t : Station} (h : s ≤ t) (e : tube.End s) : tube.End t :=
  (tube.transport h).carrySection e

@[simp] theorem carryEnd_witness {s t : Station} (h : s ≤ t) (e : tube.End s) (i : Index) :
    (tube.carryEnd h e).witness i = (tube.transport h).face i (e.witness i) := rfl

/-- [proved-derived; formal-checked] The end is carried functorially: the identity step changes no
continuing object. -/
theorem carryEnd_refl (s : Station) (e : tube.End s) : tube.carryEnd (le_refl s) e = e :=
  Tower.CompatibleSection.ext fun i => tube.transport_refl s i (e.witness i)

/-- [proved-derived; formal-checked] And two steps compose. -/
theorem carryEnd_trans {s t r : Station} (hst : s ≤ t) (htr : t ≤ r) (e : tube.End s) :
    tube.carryEnd htr (tube.carryEnd hst e) = tube.carryEnd (le_trans hst htr) e :=
  Tower.CompatibleSection.ext fun i => tube.transport_trans hst htr i (e.witness i)

/-! ### The tube's own passages -/

/-- [definition] A **refinement route** of a tube: refine the chart by a monotone `r` with
`j ≤ r j`, take the longitudinal step there, and restrict back. These, together with the
longitudinal transports themselves, are every passage the tube owns. -/
def refinementRoute {s t : Station} (hst : s ≤ t) (r : Index → Index)
    (r_mono : ∀ {i j : Index}, i ≤ j → r i ≤ r j) (r_refines : ∀ j : Index, j ≤ r j) :
    Migration (tube.station s) (tube.station t) where
  index := r
  index_mono := r_mono
  face j x := (tube.station t).restrict (r_refines j) ((tube.transport hst).face (r j) x)
  naturality := by
    intro i j h x
    rw [(tube.station t).restrict_trans h (r_refines j),
      ← (tube.transport hst).naturality (r_mono h) x,
      (tube.station t).restrict_trans (r_refines i) (r_mono h)]

/-- [proved-derived; formal-checked] Every refinement route follows refinement. -/
theorem refinementRoute_followsRefinement {s t : Station} (hst : s ≤ t) (r : Index → Index)
    (r_mono : ∀ {i j : Index}, i ≤ j → r i ≤ r j) (r_refines : ∀ j : Index, j ≤ r j) :
    (tube.refinementRoute hst r r_mono r_refines).FollowsRefinement := r_refines

end Tube

/-! ## The wormhole -/

/-- [definition] A **wormhole** on a tube: a passage between two stations whose index map crosses to
a chart the tube's order does not relate to the chart it writes. Neither station's transverse ladder
offers a passage there, and a common refinement supplies none either — a span is not a map — so the
passage is one the tube itself does not have.

The two recorded readings agree on this predicate. `docs/canon/TABLET_THE_CHART.md:263`: "passage
through a chart where the answer is one step, when in the source chart it is not reachable at all."
`research/records/2026-07-26_THE_TUBE_CARRIES_THE_EXTERIOR_FACE_THE_DISTANT_FIELD_RETURNS_THROUGH_REBASE.md:222`:
a founded throat joining two actual mouths, owing both transports, a loop holonomy and a transport
cost — never zero-cost transport. The mouths are `source` and `target`; the reverse transport and
its cost are the separate obligations of `ResidualMigration` and
`Foundation/PresentationCost.lean`, and `PresentationCost.swapMigration_route_isEmpty` records that
for a wormhole the refinement-route cost has nothing to measure.

Rust counterpart: `crates/holonic-core/src/restriction/tube.rs::wormhole_receipt`. -/
structure Wormhole {Station : Type uS} [Preorder Station] {Index : Type u} [Preorder Index]
    (tube : Tube.{uS, u, v} Station Index) (source target : Station) where
  /-- The passage itself. -/
  passage : Migration (tube.station source) (tube.station target)
  /-- It crosses charts the tube does not relate: this is the non-factoring condition. -/
  crosses : passage.ConnectsIncomparableCharts

namespace Wormhole

variable {Station : Type uS} [Preorder Station] {Index : Type u} [Preorder Index]
variable {tube : Tube.{uS, u, v} Station Index}

/-- [proved-derived; formal-checked] A wormhole does not factor through refinement — there is no
refinement for it to factor through. Cited from
`not_factorsThroughRefinement_of_connectsIncomparableCharts`. -/
theorem not_factorsThroughRefinement {s : Station}
    (w : Wormhole tube s s) : ¬ w.passage.FactorsThroughRefinement :=
  Migration.not_factorsThroughRefinement_of_connectsIncomparableCharts w.crosses

end Wormhole

namespace Tube

variable {Station : Type uS} [Preorder Station] {Index : Type u} [Preorder Index]
variable (tube : Tube.{uS, u, v} Station Index)

/-- [proved-derived; formal-checked] **A tube's own longitudinal transport is never a wormhole.** -/
theorem transport_is_not_a_wormhole {s t : Station} (hst : s ≤ t) :
    ¬ (tube.transport hst).toMigration.ConnectsIncomparableCharts :=
  (tube.transport hst).toMigration_not_connectsIncomparableCharts

/-- [proved-derived; formal-checked] **Nor is any of its refinement routes.** Together with the
previous theorem this is the exact statement that a wormhole is passage the tube does not own. -/
theorem refinementRoute_is_not_a_wormhole {s t : Station} (hst : s ≤ t) (r : Index → Index)
    (r_mono : ∀ {i j : Index}, i ≤ j → r i ≤ r j) (r_refines : ∀ j : Index, j ≤ r j) :
    ¬ (tube.refinementRoute hst r r_mono r_refines).ConnectsIncomparableCharts :=
  Migration.not_connectsIncomparableCharts_of_followsRefinement
    (tube.refinementRoute_followsRefinement hst r r_mono r_refines)

end Tube

/-! ## The constant tube, and the witnesses -/

/-- [definition] The **constant tube**: one transverse section at every station, transported by the
identity. It is the tube a tower already is when nothing moves along the longitudinal axis. -/
def constantTube (Station : Type uS) [Preorder Station] {Index : Type u} [Preorder Index]
    (T : Tower.{u, v} Index) : Tube.{uS, u, v} Station Index where
  station _ := T
  transport _ := ChartwiseMigration.id T
  transport_refl _ _ _ := rfl
  transport_trans _ _ _ _ := rfl

/-- [definition] The constant-face tower over any index: one face type at every chart, with the
identity restriction. `Foundation/ContinuingTower.lean::twoChartTower` is exactly this over its
two-chart discrete index, as `twoChartTower_is_constantFaceTower` records. -/
def constantFaceTower (Index : Type u) [Preorder Index] (X : Type v) : Tower.{u, v} Index where
  Face _ := X
  restrict _ x := x
  restrict_refl _ _ := rfl
  restrict_trans _ _ _ := rfl

/-- [proved-derived; formal-checked] The existing two-chart witness is that constant tower; no
second family is founded. -/
theorem twoChartTower_is_constantFaceTower (X : Type v) :
    twoChartTower X = constantFaceTower TwoCharts X := rfl

/-- [definition] The tube whose stations all carry the two-chart tower. `swapMigration` is a passage
between any two of its stations. -/
def twoChartTube (Station : Type uS) [Preorder Station] (X : Type v) :
    Tube.{uS, 0, v} Station TwoCharts :=
  constantTube Station (twoChartTower X)

/-- [counterexample; formal-checked] **A wormhole exists.** `swapMigration` reads the other chart at
every chart of an index with no common refinement at all
(`twoCharts_no_common_refinement`), so it is a passage between two mouths of the tube that the tube
relates in no way whatsoever. -/
def swapWormhole (Station : Type uS) [Preorder Station] (X : Type v) (s t : Station) :
    Wormhole (twoChartTube Station X) s t where
  passage := swapMigration X
  crosses := swapMigration_connectsIncomparableCharts X

/-! ### Lossiness and being a wormhole are independent

`padicHalfMigration` is lossy and is not a wormhole. `swapMigration` is a wormhole and is not lossy.
The remaining two cells are inhabited below and by the identity migration. -/

/-- [definition] A **lossy wormhole**: the swap of the two incomparable charts, carrying the halved
face and retaining the dropped bit as its residual. Its naturality squares are all reflexive because
the index is discrete, so it is a lawful `ResidualMigration`.

Rust counterpart: `continuing_tube.rs::LossySwapMigration`. -/
def lossySwapMigration : ResidualMigration (twoChartTower ℕ) (twoChartTower ℕ) where
  index
    | .left => .right
    | .right => .left
  index_mono := by
    intro i j h
    have hij : i = j := h
    subst hij
    rfl
  face := fun _ (x : ℕ) => (x / 2 : ℕ)
  naturality _ _ := rfl
  Residual _ := ℕ
  residual := fun _ (x : ℕ) => (x % 2 : ℕ)
  reopen := fun _ (q : ℕ) (r : ℕ) => (2 * q + r : ℕ)
  reopen_apply := fun _ (x : ℕ) => Nat.div_add_mod x 2

/-- [counterexample; formal-checked] It is a wormhole. -/
theorem lossySwapMigration_connectsIncomparableCharts :
    lossySwapMigration.toMigration.ConnectsIncomparableCharts := by
  refine ⟨TwoCharts.left, ?_, ?_⟩
  · intro h
    exact TwoCharts.noConfusion (h : TwoCharts.left = TwoCharts.right)
  · intro h
    exact TwoCharts.noConfusion (h : TwoCharts.right = TwoCharts.left)

/-- [counterexample; formal-checked] And it is lossy: it merges `0` and `1`. -/
theorem lossySwapMigration_face_not_injective :
    ¬ Function.Injective (lossySwapMigration.face TwoCharts.left) := by
  intro hinj
  have h : lossySwapMigration.face TwoCharts.left (0 : ℕ)
      = lossySwapMigration.face TwoCharts.left (1 : ℕ) := by
    show (0 : ℕ) / 2 = 1 / 2
    norm_num
  have h01 : (0 : ℕ) = 1 := hinj h
  omega

/-- [proved-derived; formal-checked] **A lossy wormhole is one-way from the migrated face alone.**
Cited from `Migration.not_reversePassage_of_not_injective`. -/
theorem lossySwapMigration_no_reverse_passage :
    ¬ lossySwapMigration.toMigration.ReversePassage TwoCharts.left :=
  Migration.not_reversePassage_of_not_injective _ lossySwapMigration_face_not_injective

/-- [proved-derived; formal-checked] **And the retained residual restores it exactly.** This is
`ResidualMigration.traversability_is_the_residual` at a wormhole: traversability is decided by the
residual and by nothing else, and being a wormhole decides nothing about it. -/
theorem lossySwapMigration_residual_restores_the_reverse_passage (c : TwoCharts) (x : ℕ) :
    lossySwapMigration.reopen c (lossySwapMigration.face c x)
      (lossySwapMigration.residual c x) = x :=
  lossySwapMigration.reopen_apply c x

/-- [proved-derived; formal-checked] **Lossiness is independent of being a wormhole**: all four
cells are inhabited. The lossy-and-not-a-wormhole cell is `padicHalfMigration`, which factors
through refinement (`padicHalfMigration_factorsThroughRefinement`) while merging exactly `p ^ j`
faces; the wormhole-and-not-lossy cell is `swapMigration`; the lossy wormhole is
`lossySwapMigration`; and the identity migration is neither. -/
theorem lossiness_is_independent_of_being_a_wormhole (p : ℕ) [Fact p.Prime] :
    (lossySwapMigration.toMigration.ConnectsIncomparableCharts ∧
        ¬ Function.Injective (lossySwapMigration.face TwoCharts.left)) ∧
      ((swapMigration ℕ).ConnectsIncomparableCharts ∧
        Function.Injective ((swapMigration ℕ).face TwoCharts.left)) ∧
      (¬ (padicHalfMigration p).toMigration.ConnectsIncomparableCharts ∧
        ¬ Function.Injective ((padicHalfMigration p).face 1)) ∧
      (¬ (Migration.identity (padicTower p)).ConnectsIncomparableCharts ∧
        Function.Injective ((Migration.identity (padicTower p)).face 1)) := by
  refine ⟨⟨lossySwapMigration_connectsIncomparableCharts,
      lossySwapMigration_face_not_injective⟩,
    ⟨swapMigration_connectsIncomparableCharts ℕ, fun _ _ h => h⟩, ⟨?_, ?_⟩, ⟨?_, fun _ _ h => h⟩⟩
  · exact Migration.not_connectsIncomparableCharts_of_followsRefinement
      (padicHalfMigration_factorsThroughRefinement p).refines
  · exact padicHalfMigration_face_not_injective p 1 (by omega)
  · exact Migration.not_connectsIncomparableCharts_of_staysAtItsChart fun _ => rfl

/-! ## Longitudinal circuits, holonomy, and where non-orientability lives -/

/-- [definition] A **circuit** at one station: a chartwise migration of that station's transverse
section into itself, read as a closed longitudinal loop. -/
abbrev Circuit {Index : Type u} [Preorder Index] (T : Tower.{u, v} Index) :=
  ChartwiseMigration T T

/-- [definition] A circuit has a **defect** — nontrivial holonomy — when its composite is not the
identity at some chart and some face. -/
def ChartwiseMigration.HasDefect {Index : Type u} [Preorder Index] {T : Tower.{u, v} Index}
    (c : Circuit T) : Prop :=
  ∃ (i : Index) (x : T.Face i), c.face i x ≠ x

/-- [proved-derived; formal-checked] **A tube's own closed circuit has no defect.** A station round
trip composes to the identity, exactly as `Tower.restrict_roundTrip` makes every index round trip
the identity. Neither axis of a functorial tube can carry holonomy; that is why non-orientability is
a *declared* circuit and not a tube law. -/
theorem tube_circuit_has_no_defect {Station : Type uS} [Preorder Station] {Index : Type u}
    [Preorder Index] (tube : Tube.{uS, u, v} Station Index) {s t : Station}
    (hst : s ≤ t) (hts : t ≤ s) :
    ¬ (ChartwiseMigration.comp (tube.transport hts) (tube.transport hst)).HasDefect := by
  rintro ⟨i, x, hx⟩
  exact hx (tube.transport_roundTrip hst hts i x)

/-- [definition] A circuit defect presented as `Foundation/ReceiverAtlas.lean::CocycleDefect`: the
routed face is what the circuit returns, the direct face is the identity chart transition, and they
differ. Nothing is founded — the atlas already owns the obstruction. -/
def ChartwiseMigration.cocycleDefect {Index : Type u} [Preorder Index] {T : Tower.{u, v} Index}
    (c : Circuit T) {i : Index} {x : T.Face i} (hx : c.face i x ≠ x) :
    Holonics.Foundation.Atlas.CocycleDefect
      (Transition.tautological (c.face i))
      (Transition.ofEquiv (Equiv.refl (T.Face i)))
      (Transition.ofEquiv (Equiv.refl (T.Face i))) where
  source := x
  routed := c.face i x
  direct := x
  routed_eq := rfl
  direct_eq := rfl
  differ := hx

/-- [proved-derived; formal-checked] **A circuit defect is holonomy, not loss.** Both routes reopen
the same source with no remainder; only the face each presents differs. Cited from
`CocycleDefect.defect_is_holonomy_not_loss`. -/
theorem circuit_defect_is_holonomy_not_loss {Index : Type u} [Preorder Index]
    {T : Tower.{u, v} Index} (c : Circuit T) {i : Index} {x : T.Face i} (hx : c.face i x ≠ x) :
    (Transition.comp (Transition.ofEquiv (Equiv.refl (T.Face i)))
        (Transition.tautological (c.face i))).reopen (c.cocycleDefect hx).routed
        (c.cocycleDefect hx).routedResidual = x ∧
      (Transition.ofEquiv (Equiv.refl (T.Face i))).reopen (c.cocycleDefect hx).direct
        (c.cocycleDefect hx).directResidual = x :=
  (c.cocycleDefect hx).defect_is_holonomy_not_loss

/-- [definition] The smallest circuit with nontrivial holonomy: the Boolean flip on a constant
transverse section. Its composite is `Millennium/HolonicDirectedPassage.lean::boolFlip`. -/
def flipCircuit : Circuit (twoChartTower Bool) where
  face _ b := !b
  naturality _ _ := rfl

/-- [counterexample; formal-checked] It has a defect. -/
theorem flipCircuit_hasDefect : flipCircuit.HasDefect :=
  ⟨TwoCharts.left, (false : Bool), fun h => Bool.noConfusion h⟩

/-- [counterexample; formal-checked] **A tube closed on itself with nontrivial holonomy carries no
continuing object that survives the circuit.** This is
`Millennium/HolonicDirectedPassage.lean::boolFlipCoherent_isEmpty` read on the tube, through
`Foundation/ContinuingTower.lean::boolFlipSelfLoop_isEmpty`; the obstruction stays with its existing
owner and is not rebuilt. Non-orientability lives here — on a longitudinal axis closed on itself —
and never in the transverse ladder, which `Tower.restrict_roundTrip` already excludes. -/
theorem flipCircuit_carries_no_invariant_end :
    IsEmpty { e : (twoChartTower Bool).CompatibleSection // flipCircuit.carrySection e = e } := by
  constructor
  rintro ⟨e, he⟩
  have hw : flipCircuit.face TwoCharts.left (e.witness TwoCharts.left) = e.witness TwoCharts.left :=
    congrArg (fun s : (twoChartTower Bool).CompatibleSection => s.witness TwoCharts.left) he
  exact boolFlipSelfLoop_isEmpty.false ⟨e.witness TwoCharts.left, hw⟩

/-! ## The branching cross-section: the `p`-adic tube -/

/-- [definition] The tube whose transverse section at every station is the `ℤ/p^n` tower. -/
def padicTube (p : ℕ) [Fact p.Prime] (Station : Type uS) [Preorder Station] :
    Tube.{uS, 0, 0} Station ℕ :=
  constantTube Station (padicTower p)

/-- [proved-derived; formal-checked] **The tube's end is the tower's compatible-section space, and
at the canonical non-Archimedean instance it is `ℤ_[p]`.** Cited from `padicSectionEquiv`; nothing
is reproved. -/
noncomputable def padicTube_end_equiv (p : ℕ) [Fact p.Prime] (Station : Type uS) [Preorder Station]
    (s : Station) : ℤ_[p] ≃ (padicTube p Station).End s :=
  padicSectionEquiv p

/-- [proved-derived; formal-checked] **The cross-section branches exactly `p ^ k` ways over `k`
refinement steps.** Cited from `padicFibre_card`: the transverse sections of the `p`-adic tube form
a `p`-ary tree, and the count is an equality, not an asymptotic. -/
theorem padicTube_crossSection_branching (p : ℕ) [Fact p.Prime] (Station : Type uS)
    [Preorder Station] (s : Station) (m k : ℕ) (face : ZMod (p ^ m)) :
    Nat.card { x : ZMod (p ^ (m + k)) //
        ((padicTube p Station).station s).restrict (Nat.le_add_right m k) x = face } = p ^ k :=
  padicFibre_card p m k face

/-- [proved-derived; formal-checked] One refinement step branches into exactly `p`. Cited from
`padicAdjacentFibre_card`. -/
theorem padicTube_adjacent_branching (p : ℕ) [Fact p.Prime] (Station : Type uS) [Preorder Station]
    (s : Station) (n : ℕ) (face : ZMod (p ^ n)) :
    Nat.card { x : ZMod (p ^ (n + 1)) //
        ((padicTube p Station).station s).restrict (Nat.le_succ n) x = face } = p :=
  padicAdjacentFibre_card p n face

/-- [proved-derived; formal-checked] The longitudinal transport of the `p`-adic tube carries every
end unchanged: the branching is entirely transverse. -/
theorem padicTube_carryEnd (p : ℕ) [Fact p.Prime] (Station : Type uS) [Preorder Station]
    {s t : Station} (h : s ≤ t) (e : (padicTube p Station).End s) :
    (padicTube p Station).carryEnd h e = e :=
  Tower.CompatibleSection.ext fun _ => rfl

/-! ## The longitudinal axis is the clocked span -/

/-- [definition] One longitudinal occurrence of a tube at one chart: an admitted station step
together with the face it carries. -/
structure LongitudinalOccurrence {Station : Type uS} [Preorder Station] {Index : Type u}
    [Preorder Index] (tube : Tube.{uS, u, v} Station Index) (chart : Index) where
  /-- The mouth the occurrence leaves. -/
  earlier : Station
  /-- The mouth it arrives at. -/
  later : Station
  /-- The admitted step between them. -/
  step : earlier ≤ later
  /-- The transverse face it carries. -/
  carried : (tube.station earlier).Face chart

namespace Tube

variable {Station : Type uS} [Preorder Station] {Index : Type u} [Preorder Index]
variable (tube : Tube.{uS, u, v} Station Index)

/-- [definition] The face type of the tube's longitudinal span: a face together with the station
that presents it. A face without its station is not admitted. -/
def StationFace (chart : Index) : Type _ := Σ s : Station, (tube.station s).Face chart

/-- [definition] **A tube's longitudinal axis is a `ClockedSpan`.** The occurrences are its admitted
steps, the two boundary maps are the two mouths, the clock face is the arrival station and the
returned receiver face is the transported transverse face. The tube's own transport carries no
obstruction, which is why the obstruction slot is `PUnit` here — the defect arms are
`SquareVerdict.defect` and `ChartwiseMigration.cocycleDefect`, which are separate objects. -/
def clockedSpan (chart : Index) :
    ClockedSpan Station Station Station (tube.StationFace chart) PUnit
      (LongitudinalOccurrence tube chart) where
  source o := o.earlier
  target o := o.later
  clock o := o.later
  receive o := ⟨o.later, (tube.transport o.step).face chart o.carried⟩
  obstruction _ := PUnit.unit

/-- [proved-derived; formal-checked] **Re-cutting the tube's world-line changes only its
presentation.** Cited from `ClockedSpan.split_rejoin_preserves_completeFace`; this is the
longitudinal counterpart of `Tower.restrict_trans` on the transverse axis. -/
theorem clockedSpan_split_rejoin (chart : Index) {source target : Station}
    (carried : (AddressedPassage.comp (tube.clockedSpan chart).toPassage
      (tube.clockedSpan chart).toPassage).Fibre source target) :
    ((tube.clockedSpan chart).comp (tube.clockedSpan chart)).completeFace
        (AddressedPassage.joinCompositeFibre (tube.clockedSpan chart).toPassage
          (tube.clockedSpan chart).toPassage
          (AddressedPassage.splitCompositeFibre (tube.clockedSpan chart).toPassage
            (tube.clockedSpan chart).toPassage carried)).1
      = ((tube.clockedSpan chart).comp (tube.clockedSpan chart)).completeFace carried.1 :=
  ClockedSpan.split_rejoin_preserves_completeFace _ _ carried

/-- [proved-derived; formal-checked] **An open gap in the tube has no joined occurrence.** A tube is
not repaired by re-segmentation. Cited from `ClockedSpan.openGap_has_no_joined_occurrence`. -/
theorem clockedSpan_openGap_has_no_joined_occurrence (chart : Index)
    (gap : ClockedSpan.HasOpenGap (tube.clockedSpan chart) (tube.clockedSpan chart)) :
    IsEmpty (AddressedPassage.Join (tube.clockedSpan chart).toPassage
      (tube.clockedSpan chart).toPassage) :=
  ClockedSpan.openGap_has_no_joined_occurrence _ _ gap

end Tube

/-! ## Where the square fails, the failure is the content -/

/-- [definition] The two-axis square at one refinement, read as an object: either the commuting law
or a witnessed defect carrying both routes' faces. A defect is returned, never repaired by choosing
a route.

Rust counterpart: `continuing_tube.rs::SquareVerdict`. -/
inductive SquareVerdict {Index : Type u} [Preorder Index] {S T : Tower.{u, v} Index}
    (f : ∀ i : Index, S.Face i → T.Face i) (i j : Index) (h : i ≤ j) : Type (max u v)
  /-- The square commutes on every face at the finer chart. -/
  | commutes (law : ∀ x : S.Face j, T.restrict h (f j x) = f i (S.restrict h x))
  /-- One face at which the two routes disagree, carrying both. -/
  | defect (x : S.Face j) (transportedThenRestricted restrictedThenTransported : T.Face i)
      (routeLeft : transportedThenRestricted = T.restrict h (f j x))
      (routeRight : restrictedThenTransported = f i (S.restrict h x))
      (differ : transportedThenRestricted ≠ restrictedThenTransported)

/-- [proved-derived; formal-checked] The verdict is total: every face family lands in exactly one
arm. -/
theorem squareVerdict_total {Index : Type u} [Preorder Index] {S T : Tower.{u, v} Index}
    (f : ∀ i : Index, S.Face i → T.Face i) (i j : Index) (h : i ≤ j) :
    Nonempty (SquareVerdict f i j h) := by
  classical
  by_cases hlaw : ∀ x : S.Face j, T.restrict h (f j x) = f i (S.restrict h x)
  · exact ⟨.commutes hlaw⟩
  · obtain ⟨x, hx⟩ := not_forall.mp hlaw
    exact ⟨.defect x _ _ rfl rfl hx⟩

/-- [proved-derived; formal-checked] A chartwise migration is exactly a family whose every square
commutes. -/
def ChartwiseMigration.squareVerdict {Index : Type u} [Preorder Index] {S T : Tower.{u, v} Index}
    (M : ChartwiseMigration S T) (i j : Index) (h : i ≤ j) : SquareVerdict M.face i j h :=
  .commutes fun x => M.naturality h x

/-! ### The grain instance: the contact receiver does not commute with the selection

`Foundation/GrainRestriction.lean` owns the physical fact. Over the M5 deposit, at an equal 8 Å
aperture, the alpha-carbon receiver returns 301 `Inside` where the complete atom-grain restriction
returns 1,397, with 0 in the other direction. The 0 is `selection_inside_implies_fine_inside`; the
1,096 is `equal_aperture_is_not_lawful`. Below, the same fact is the `defect` arm of the two-axis
square. -/

section GrainSquare

open Holonics.Foundation.GrainRestriction
open Holonics.Foundation.AperturedGradedComplex

/-- [definition] The cells at each grain of the smallest presentation that separates the two
readings: one residue cell carrying two atom cells, of which one is the declared representative. -/
def grainCell : Grain → Type
  | .component => Unit
  | .residue => Unit
  | .atom => Bool

/-- [definition] The declared selection: the coarse cell's representative atom is `false`. This is
the receiver `crates/holonic-life/examples/m5/cif.rs::REPRESENTATIVE` enacts by discarding every
non-`CA` row. -/
def grainSel : ∀ {i j : Grain}, i ≤ j → grainCell i → grainCell j
  | .component, .component, _ => _root_.id
  | .component, .residue, _ => fun _ => ()
  | .component, .atom, _ => fun _ => false
  | .residue, .residue, _ => _root_.id
  | .residue, .atom, _ => fun _ => false
  | .atom, .atom, _ => _root_.id
  | .residue, .component, h => absurd h (by decide)
  | .atom, .component, h => absurd h (by decide)
  | .atom, .residue, h => absurd h (by decide)

theorem grainSel_refl : ∀ (i : Grain) (x : grainCell i), grainSel (le_refl i) x = x := by
  intro i x
  cases i <;> rfl

theorem grainSel_trans : ∀ {i j k : Grain} (hij : i ≤ j) (hjk : j ≤ k) (x : grainCell i),
    grainSel hjk (grainSel hij x) = grainSel (le_trans hij hjk) x := by
  intro i j k hij hjk x
  cases i <;> cases j <;> cases k <;>
    first
      | rfl
      | exact absurd hij (by decide)

/-- [definition] The grain tower of that presentation, built by
`Foundation/GrainRestriction.lean::selectionTower`. -/
def grainSelectionTower : Tower.{0, 0} Grain :=
  selectionTower grainCell grainSel grainSel_refl grainSel_trans

/-- [definition] The **contact receiver** at each grain: whether this grain's face carries any
contact at all. It is the census reading `GrainFace::inside` asked as a predicate. -/
def grainContactReading : ∀ g : Grain, grainSelectionTower.Face g →
    (constantFaceTower Grain Prop).Face g :=
  fun g φ => ∃ a b : grainCell g, φ a b = ContactClass.inside

theorem grain_residue_le_atom : Grain.residue ≤ Grain.atom := by decide

/-- [counterexample; formal-checked] **The two-axis square fails at the grain.** The fine face
carries a contact between two unselected atoms; restricting first destroys it, reading first does
not. This is `equal_aperture_is_not_lawful` as a square, and on the M5 deposit it is the measured
1,096 fine-only `Inside` pairs. -/
theorem grainSquare_fails :
    (constantFaceTower Grain Prop).restrict grain_residue_le_atom
        (grainContactReading Grain.atom twoCellFace)
      ≠ grainContactReading Grain.residue
        (grainSelectionTower.restrict grain_residue_le_atom twoCellFace) := by
  intro heq
  have hfine : (constantFaceTower Grain Prop).restrict grain_residue_le_atom
      (grainContactReading Grain.atom twoCellFace) := ⟨true, true, rfl⟩
  rw [heq] at hfine
  obtain ⟨a, b, hab⟩ := hfine
  exact ContactClass.noConfusion hab

/-- [counterexample; formal-checked] The failure returned as the `defect` arm, with both routes'
faces retained. -/
def grainSquareDefect :
    SquareVerdict grainContactReading Grain.residue Grain.atom grain_residue_le_atom :=
  .defect twoCellFace _ _ rfl rfl grainSquare_fails

/-- [proved-derived; formal-checked] And the defect is not a loss: the grain selection's own
residual reopens the fine face exactly. `grain_residual_reopens_the_source` is cited, not reproved —
what the square loses is agreement between two routes, which is holonomy, and not information. -/
theorem grainSquare_defect_is_not_a_loss (π : Bool → Unit) (sel : Unit → Bool)
    (φ : Bool → Bool → ContactClass) :
    (selectionTransition π sel).reopen ((selectionTransition π sel).apply φ)
      ((selectionTransition π sel).residual φ) = φ :=
  grain_residual_reopens_the_source π sel φ

end GrainSquare

/-! ## The staircase between two grains: `BoundaryScalePassage` against `Transition` -/

/-- [definition] The two-chart enclosure index: an interior section refines the boundary current it
presents. This is the axis `Foundation/BoundaryScalePassage.lean` transports along. -/
inductive Enclosure
  /-- The boundary current. -/
  | boundary
  /-- The interior section that presents it. -/
  | interior
  deriving DecidableEq, Repr

namespace Enclosure

/-- [definition] `i ⊑ j` exactly when the two are the same chart, or `j` is the interior that
presents every boundary. -/
protected def Le (i j : Enclosure) : Prop := i = j ∨ j = interior

instance : Preorder Enclosure where
  le := Enclosure.Le
  le_refl _ := Or.inl rfl
  le_trans i j k hij hjk := by
    rcases hij with rfl | rfl
    · exact hjk
    · refine Or.inr ?_
      rcases hjk with h | h
      · exact h.symm
      · exact h

theorem boundary_le_interior : Enclosure.boundary ≤ Enclosure.interior := Or.inr rfl

theorem interior_not_le_boundary : ¬ (Enclosure.interior ≤ Enclosure.boundary) := by
  rintro (h | h) <;> exact Enclosure.noConfusion h

end Enclosure

/-- [definition] The faces of one enclosure tower. -/
def enclosureFace (Interior Boundary : Type v) : Enclosure → Type v
  | .boundary => Boundary
  | .interior => Interior

/-- [definition] Its restriction: the interior section restricts to the boundary current it forms,
and every other admitted refinement is the identity. -/
def enclosureRestrict {Interior Boundary : Type v} (form : Interior → Boundary) :
    ∀ (i j : Enclosure), i ≤ j → enclosureFace Interior Boundary j → enclosureFace Interior Boundary i
  | .boundary, .interior, _ => form
  | .boundary, .boundary, _ => fun x => x
  | .interior, .interior, _ => fun x => x
  | .interior, .boundary, h => absurd h Enclosure.interior_not_le_boundary

/-- [definition] The **enclosure tower**: one interior section, one boundary current, and boundary
formation as the only restriction. It founds nothing — the faces and the map are the ones a
`BoundaryScalePassage` already carries. -/
def enclosureTower {Interior Boundary : Type v} (form : Interior → Boundary) :
    Tower.{0, v} Enclosure where
  Face := enclosureFace Interior Boundary
  restrict {i j} h x := enclosureRestrict form i j h x
  restrict_refl := by
    intro i x
    cases i <;> rfl
  restrict_trans := by
    intro i j k hij hjk x
    cases i <;> cases j <;> cases k <;>
      first
        | rfl
        | exact absurd hij Enclosure.interior_not_le_boundary
        | exact absurd hjk Enclosure.interior_not_le_boundary

section BoundaryScale

variable {Scalar : Type w} [Semiring Scalar]
variable {FineInterior FineBoundary CoarseInterior CoarseBoundary : Type v}
variable [AddCommMonoid FineInterior] [Module Scalar FineInterior]
variable [AddCommMonoid FineBoundary] [Module Scalar FineBoundary]
variable [AddCommMonoid CoarseInterior] [Module Scalar CoarseInterior]
variable [AddCommMonoid CoarseBoundary] [Module Scalar CoarseBoundary]

/-- [proved-derived; formal-checked] **A `BoundaryScalePassage` is a chartwise migration between two
enclosure towers**, and its `boundary_natural` field *is* the single nonreflexive naturality square.
The staircase between two grains — between atoms and molecules, between planets — is therefore a
move along the transverse axis of the tube, carried by the machinery the carrier already owns, and
not a second kind of passage.

The one bookkeeping discrepancy, recorded rather than hidden, is the same one `rebaseMigration`
records: `Tower.Face : Index → Type v` puts a tower's faces in one universe, so the four module
types are stated in one universe here. No mathematical content is lost. -/
def boundaryScaleMigration
    (P : BoundaryScalePassage Scalar FineInterior FineBoundary CoarseInterior CoarseBoundary) :
    ChartwiseMigration (enclosureTower (Interior := FineInterior) (Boundary := FineBoundary)
        P.fineBoundary)
      (enclosureTower (Interior := CoarseInterior) (Boundary := CoarseBoundary)
        P.coarseBoundary) where
  face
    | .boundary => P.boundaryTransport
    | .interior => P.interiorTransport
  naturality := by
    intro i j h x
    cases i <;> cases j
    · rfl
    · exact P.transport_boundary x
    · exact absurd h Enclosure.interior_not_le_boundary
    · rfl

/-- [proved-derived; formal-checked] It stays at its chart. -/
theorem boundaryScaleMigration_staysAtItsChart
    (P : BoundaryScalePassage Scalar FineInterior FineBoundary CoarseInterior CoarseBoundary) :
    (boundaryScaleMigration P).toMigration.StaysAtItsChart := fun _ => rfl

/-- [proved-derived; formal-checked] **The scale staircase is never a wormhole.** It reads exactly
the chart it writes; the passage between two grains runs along the tube, never across it. -/
theorem boundaryScale_staircase_is_not_a_wormhole
    (P : BoundaryScalePassage Scalar FineInterior FineBoundary CoarseInterior CoarseBoundary) :
    ¬ (boundaryScaleMigration P).toMigration.ConnectsIncomparableCharts :=
  (boundaryScaleMigration P).toMigration_not_connectsIncomparableCharts

/-- [definition] The staircase with a **supplied** residual at each enclosure chart. The passage's
own data determines none — `residual_is_not_determined_by_the_face_map` is the general reason — so
the residual is deposited by a caller here exactly as in `Tower.restrictTransition`, and the result
is a `ResidualMigration` by `ResidualMigration.ofTransitionFamily`. -/
def boundaryScaleResidualMigration
    (P : BoundaryScalePassage Scalar FineInterior FineBoundary CoarseInterior CoarseBoundary)
    (Residual : Enclosure → Type v)
    (residual : ∀ j : Enclosure,
      (enclosureTower (Interior := FineInterior) (Boundary := FineBoundary) P.fineBoundary).Face j →
        Residual j)
    (reopen : ∀ j : Enclosure,
      (enclosureTower (Interior := CoarseInterior) (Boundary := CoarseBoundary)
          P.coarseBoundary).Face j → Residual j →
        (enclosureTower (Interior := FineInterior) (Boundary := FineBoundary)
          P.fineBoundary).Face j)
    (reopen_apply : ∀ (j : Enclosure)
      (x : (enclosureTower (Interior := FineInterior) (Boundary := FineBoundary)
          P.fineBoundary).Face j),
      reopen j ((boundaryScaleMigration P).face j x) (residual j x) = x) :
    ResidualMigration
      (enclosureTower (Interior := FineInterior) (Boundary := FineBoundary) P.fineBoundary)
      (enclosureTower (Interior := CoarseInterior) (Boundary := CoarseBoundary)
        P.coarseBoundary) :=
  ResidualMigration.ofTransitionFamily _root_.id (fun h => h)
    (fun j =>
      { Residual := Residual j
        apply := (boundaryScaleMigration P).face j
        residual := residual j
        reopen := reopen j
        reopen_apply := reopen_apply j })
    (fun h x => (boundaryScaleMigration P).naturality h x)

end BoundaryScale

/-- [definition] A concrete scale passage whose interior transport merges two fine interiors: the
coarse interior keeps only the first coordinate. Every field is exact and integral. -/
def projectionScalePassage : BoundaryScalePassage ℤ (ℤ × ℤ) ℤ ℤ ℤ where
  fineBoundary := LinearMap.fst ℤ ℤ ℤ
  coarseBoundary := LinearMap.id
  interiorTransport := LinearMap.fst ℤ ℤ ℤ
  boundaryTransport := LinearMap.id
  boundary_natural := rfl

/-- [counterexample; formal-checked] Its interior component is not injective. -/
theorem projectionScalePassage_interior_not_injective :
    ¬ Function.Injective ((boundaryScaleMigration projectionScalePassage).face
      Enclosure.interior) := by
  intro hinj
  have h : (boundaryScaleMigration projectionScalePassage).face Enclosure.interior
        ((0, 0) : ℤ × ℤ)
      = (boundaryScaleMigration projectionScalePassage).face Enclosure.interior
        ((0, 1) : ℤ × ℤ) := rfl
  have hpair : ((0, 0) : ℤ × ℤ) = ((0, 1) : ℤ × ℤ) := hinj h
  have hsnd : (0 : ℤ) = 1 := congrArg Prod.snd hpair
  exact absurd hsnd (by decide)

/-- [counterexample; formal-checked] **So a `BoundaryScalePassage` is not a `Transition`.** There is
no reverse passage from the transported face alone: the staircase between two grains is genuinely
lossy, and the residual — supplied, never derived — is what makes it two-way. That is exactly
`ResidualMigration.traversability_is_the_residual`, and it is the precise difference between this
staircase and `GrainRestriction.selectionTransition`, which supplies its residual and is a
transition. -/
theorem projectionScalePassage_no_reverse_passage :
    ¬ (boundaryScaleMigration projectionScalePassage).toMigration.ReversePassage
      Enclosure.interior :=
  Migration.not_reversePassage_of_not_injective _ projectionScalePassage_interior_not_injective

/-! ## T5 — the observer, its two-axis horizon, and curvature as a function of distance

[definition] Item **T5** of
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. The horizon's two
coordinates, the chain distance that measures both axes and the asymmetry between looking toward the
coarse and looking toward the fine are `Foundation/ReceiverRelease.lean`'s
(`Horizon`, `ChainDistanceAtMost`, `looking_toward_the_coarse_is_determined_and_toward_the_fine_is_plural`).
What is added here is what those coordinates measure **on a tube**: which squares and circuits an
observer at `(station, chart)` can see, and therefore what its defect profile reads.

[proved-derived; formal-checked] Four statements, and none of them is a restatement of the square law
above.

* `tube_profile_is_flat_at_every_horizon` — a `Tube`'s profile is identically zero, because
  `Tube.square` holds at every pair of charts and `tube_circuit_has_no_defect` at every circuit.
  Curvature is therefore a property of **declared** circuits and non-commuting families, exactly as
  this file already proved for the one-axis case.
* `visibleSquare_shift` — two observers read the *same* region at horizons that differ by their own
  chain distance. This is the exact relation between two grains' profiles, and it is
  `chainDistance_trans`, the triangle inequality, and nothing else.
* `flat_near_curved_far` — an exact declared tube whose every square commutes at every horizon,
  whose circuit inside longitudinal distance `1` returns the identity, and whose circuit reaching
  distance `2` does not. Locally a sharp lattice, globally curved.
* `the_fine_observer_sees_at_one_step_what_the_coarse_one_sees_at_three` — an exact five-chart
  ladder with one failing square at its top: the observer at the finest chart reads the defect at
  `k = 1` and the observer three cover steps below it reads nothing until `k = 3`. Which is which
  depends on the observer's grain.

[proved-derived; formal-checked] And the profile is a **reading**: `receiver_defect_is_a_structural_defect`
proves a receiver can only lose a defect, never invent one, and `ladderReceiverInsufficiency`
exhibits a poorer receiver that reads flat exactly what a richer one separates —
`Foundation/Receiver.lean::ReceiverInsufficiency`, cited and not rebuilt.

Rust counterpart: `crates/holonic-engine/src/continuing_tube.rs::{Observer, HorizonDeclaration,
horizon_reach, two_axis_width, DefectProfile, defect_profile, CrossRankPassage,
classify_cross_rank, plan_routes, PresentationTube}`. -/

open Holonics.Foundation.ReceiverRelease

/-- [definition] **An observer**: a station and a chart. `receiver_release`'s width reads at `h`
steps of `Φ`, which says where along the tube the reading happens and not at which grain; an
observer is both.

Rust counterpart: `continuing_tube.rs::Observer`. -/
structure ObserverAt (Station : Type us) (Index : Type u) where
  /-- Where along the tube it stands. -/
  station : Station
  /-- Which chart of the transverse section it reads at. -/
  chart : Index

/-- [definition] `j` **strictly refines** `i` when the order relates them one way only. -/
def StrictlyRefines {Index : Type u} [Preorder Index] (i j : Index) : Prop := i ≤ j ∧ ¬ (j ≤ i)

/-- [definition] `j` **covers** `i` inside a declared aperture: it strictly refines it and no
declared chart lies strictly between. One cover is one step of the index ladder.

[definition] This, and not bare comparability, is the adjacency the executable index distance walks
(`continuing_tube.rs::index_distance`), and the reason is exact: on a linearly ordered index every
pair of charts is comparable, so the comparability adjacency would put every chart one step away and
no ladder of grains would have a length at all. The distance is therefore relative to the declared
aperture and says so — adding an intermediate grain lengthens the chain through it, which is what a
finer ladder *is*. -/
def CoveredBy {Index : Type u} [Preorder Index] (aperture : Index → Prop) (i j : Index) : Prop :=
  StrictlyRefines i j ∧ ¬ ∃ m, aperture m ∧ StrictlyRefines i m ∧ StrictlyRefines m j

/-- [definition] The undirected cover adjacency: one step of the ladder, in either direction. -/
def CoverAdjacent {Index : Type u} [Preorder Index] (aperture : Index → Prop) (i j : Index) : Prop :=
  CoveredBy aperture i j ∨ CoveredBy aperture j i

/-- [proved-derived; formal-checked] It is symmetric, which is why the index distance it measures is
symmetric (`chainDistance_symm`): one step toward the fine and one step toward the coarse are one
step. -/
theorem coverAdjacent_symm {Index : Type u} [Preorder Index] (aperture : Index → Prop)
    (i j : Index) : CoverAdjacent aperture i j → CoverAdjacent aperture j i := Or.symm

/-- [proved-derived; formal-checked] And a cover step is a comparability, so a cover chain is a
chain of comparable charts. -/
theorem coverAdjacent_comparable {Index : Type u} [Preorder Index] {aperture : Index → Prop}
    {i j : Index} (h : CoverAdjacent aperture i j) : Comparable i j := by
  rcases h with ⟨⟨hle, _⟩, _⟩ | ⟨⟨hle, _⟩, _⟩
  · exact Or.inl hle
  · exact Or.inr hle

/-- [definition] **The square at a step `(s, t)` between charts `i ≤ j` is visible to an observer at
horizon `H`** when both stations lie within `H.longitudinal` steps of the observer's station and both
charts within `H.index` steps of its chart, in the chain distance of the declared adjacencies. The
same `ChainDistanceAtMost` measures both axes: that is Brandon's statement that both are distance
into the horizon, carried in the type. -/
def VisibleSquare {Station : Type us} {Index : Type u}
    (stationAdj : Station → Station → Prop) (chartAdj : Index → Index → Prop)
    (obs : ObserverAt Station Index) (H : Horizon) (s t : Station) (i j : Index) : Prop :=
  ChainDistanceAtMost stationAdj H.longitudinal obs.station s ∧
    ChainDistanceAtMost stationAdj H.longitudinal obs.station t ∧
      ChainDistanceAtMost chartAdj H.index obs.chart i ∧
        ChainDistanceAtMost chartAdj H.index obs.chart j

/-- [proved-derived; formal-checked] **Two observers read the same region at horizons that differ by
their own distance.** Whatever the first observer sees inside `(h, k)`, an observer `dS` steps away
along the tube and `dI` steps away through the index sees inside `(dS + h, dI + k)`. This is the
exact relation between two grains' defect profiles: it is the triangle inequality and nothing else,
and it is why one observer reads a defect at `k = 1` that another does not reach until `k = 3`. -/
theorem visibleSquare_shift {Station : Type us} {Index : Type u}
    {stationAdj : Station → Station → Prop} {chartAdj : Index → Index → Prop}
    {near far : ObserverAt Station Index} {H : Horizon} {dS dI : ℕ} {s t : Station} {i j : Index}
    (hstation : ChainDistanceAtMost stationAdj dS far.station near.station)
    (hchart : ChainDistanceAtMost chartAdj dI far.chart near.chart)
    (hvis : VisibleSquare stationAdj chartAdj near H s t i j) :
    VisibleSquare stationAdj chartAdj far ⟨dS + H.longitudinal, dI + H.index⟩ s t i j :=
  ⟨chainDistance_trans hstation hvis.1, chainDistance_trans hstation hvis.2.1,
    chainDistance_trans hchart hvis.2.2.1, chainDistance_trans hchart hvis.2.2.2⟩

/-- [definition] **A declared tube**: a family of towers over a station type with a chartwise
migration for every ordered pair of stations, and **no functor law**. The difference from `Tube` is
the whole point: a declared family need not be functorial, so its circuits can carry holonomy while
every one of its squares commutes.

The executable `StationedTower` is weaker still, and the gap is stated rather than elided: it
carries **no** naturality field, and `check_commuting_square` is precisely the operation that asks
for one. `profileFlat_of_chartwise` is therefore a statement about families that *are* chartwise
migrations; the ladder tube of `continuing_tube/tests.rs` is a declared family that is not one, and
its square fails.

Rust counterpart: `continuing_tube.rs::StationedTower`, with its square checked and never assumed. -/
structure DeclaredTube.{us', ui', uf'} (Station : Type us') (Index : Type ui') [Preorder Index] where
  /-- The transverse section at one station. -/
  station : Station → Tower.{ui', uf'} Index
  /-- The declared step from one station to another. -/
  step : ∀ s t : Station, ChartwiseMigration (station s) (station t)

namespace DeclaredTube

variable {Station : Type us} {Index : Type u} [Preorder Index]

/-- [definition] The **profile is flat** at an observer's horizon when every visible square
commutes. -/
def ProfileFlat (tube : DeclaredTube.{us, u, v} Station Index)
    (stationAdj : Station → Station → Prop) (chartAdj : Index → Index → Prop)
    (obs : ObserverAt Station Index) (H : Horizon) : Prop :=
  ∀ {s t : Station} {i j : Index} (h : i ≤ j),
    VisibleSquare stationAdj chartAdj obs H s t i j →
      ∀ x : (tube.station s).Face j,
        (tube.station t).restrict h ((tube.step s t).face j x)
          = (tube.step s t).face i ((tube.station s).restrict h x)

/-- [proved-derived; formal-checked] **Every square of a declared tube whose steps are chartwise
migrations commutes, at every observer and every horizon.** The transverse axis carries no curvature
of its own; what a declared family can carry is longitudinal holonomy, and `flat_near_curved_far`
below exhibits exactly that. -/
theorem profileFlat_of_chartwise (tube : DeclaredTube.{us, u, v} Station Index)
    (stationAdj : Station → Station → Prop) (chartAdj : Index → Index → Prop)
    (obs : ObserverAt Station Index) (H : Horizon) :
    tube.ProfileFlat stationAdj chartAdj obs H :=
  fun h _ x => (tube.step _ _).naturality h x

end DeclaredTube

/-- [proved-derived; formal-checked] **A `Tube`'s defect profile is identically zero at every
observer and every horizon.** Its squares are `Tube.square` and its circuits are
`tube_circuit_has_no_defect`; a functorial tube has nothing for a profile to read. Curvature
therefore belongs to a declared circuit and a declared non-commuting family, which is what this file
already proved of the one-axis case and is not weakened here. -/
theorem tube_profile_is_flat_at_every_horizon {Station : Type uS} [Preorder Station]
    {Index : Type u} [Preorder Index] (tube : Tube.{uS, u, v} Station Index)
    (stationAdj : Station → Station → Prop) (chartAdj : Index → Index → Prop)
    (obs : ObserverAt Station Index) (H : Horizon) {s t : Station} (hst : s ≤ t) {i j : Index}
    (h : i ≤ j) (_visible : VisibleSquare stationAdj chartAdj obs H s t i j)
    (x : (tube.station s).Face j) :
    (tube.station t).restrict h ((tube.transport hst).face j x)
      = (tube.transport hst).face i ((tube.station s).restrict h x) :=
  tube.square hst h x

/-! ### Flat near, curved far -/

/-- [definition] The declared step of the three-station cycle: the identity everywhere except the
closing step `2 → 0`, which is the Boolean flip. Every step is a chartwise migration, so every
square commutes; the composite around the closed word `0 → 1 → 2 → 0` is the flip. -/
def cycleStep : Fin 3 → Fin 3 → Circuit (twoChartTower Bool) := fun s t =>
  if s = 2 ∧ t = 0 then flipCircuit else ChartwiseMigration.id _

/-- [definition] The cycle as a declared tube: one transverse section at every station, and a
declared step that is not functorial. -/
def cycleTube : DeclaredTube.{0, 0, 0} (Fin 3) TwoCharts where
  station _ := twoChartTower Bool
  step := cycleStep

/-- [definition] The closed word `0 → 1 → 0`, which stays inside longitudinal distance `1` of
station `0`. -/
def cycleShortCircuit : Circuit (twoChartTower Bool) :=
  ChartwiseMigration.comp (cycleStep 1 0) (cycleStep 0 1)

/-- [definition] The closed word `0 → 1 → 2 → 0`, which reaches station `2` — longitudinal distance
`2` from the observer at station `0`. -/
def cycleLongCircuit : Circuit (twoChartTower Bool) :=
  ChartwiseMigration.comp (cycleStep 2 0)
    (ChartwiseMigration.comp (cycleStep 1 2) (cycleStep 0 1))

theorem cycleStep_zero_one : cycleStep 0 1 = ChartwiseMigration.id _ := by
  simp [cycleStep]

theorem cycleStep_one_zero : cycleStep 1 0 = ChartwiseMigration.id _ := by
  simp [cycleStep]

theorem cycleStep_one_two : cycleStep 1 2 = ChartwiseMigration.id _ := by
  simp [cycleStep]

theorem cycleStep_two_zero : cycleStep 2 0 = flipCircuit := by
  simp [cycleStep]

/-- [proved-derived; formal-checked] The near circuit returns every face: inside `(1, k)` of the
observer at station `0` the tube is a sharp lattice. -/
theorem cycleShortCircuit_has_no_defect : ¬ cycleShortCircuit.HasDefect := by
  rintro ⟨i, x, hx⟩
  exact hx (by simp [cycleShortCircuit, cycleStep_zero_one, cycleStep_one_zero,
    ChartwiseMigration.id])

/-- [counterexample; formal-checked] The far circuit does not: at longitudinal distance `2` the same
tube carries holonomy. -/
theorem cycleLongCircuit_hasDefect : cycleLongCircuit.HasDefect := by
  refine ⟨TwoCharts.left, false, ?_⟩
  intro hcontra
  simp [cycleLongCircuit, cycleStep_zero_one, cycleStep_one_two, cycleStep_two_zero,
    ChartwiseMigration.id, ChartwiseMigration.comp, flipCircuit] at hcontra

/-- [counterexample; formal-checked] **Flat near, curved far.** One exact declared tube: every
square commutes at every observer and every horizon, the closed circuit that stays within
longitudinal distance `1` returns the identity, and the closed circuit that reaches distance `2`
does not. Locally a sharp lattice; globally curved. The curvature is in the declared longitudinal
family and never in the transverse ladder, which `Tower.restrict_roundTrip` excludes. -/
theorem flat_near_curved_far :
    (∀ (stationAdj : Fin 3 → Fin 3 → Prop) (chartAdj : TwoCharts → TwoCharts → Prop)
        (obs : ObserverAt (Fin 3) TwoCharts) (H : Horizon),
      cycleTube.ProfileFlat stationAdj chartAdj obs H) ∧
      ¬ cycleShortCircuit.HasDefect ∧ cycleLongCircuit.HasDefect :=
  ⟨fun stationAdj chartAdj obs H =>
      DeclaredTube.profileFlat_of_chartwise cycleTube stationAdj chartAdj obs H,
    cycleShortCircuit_has_no_defect, cycleLongCircuit_hasDefect⟩

/-! ### Which is which depends on the observer's grain -/

/-- [definition] The ladder index: one Boolean face at every chart of `ℕ`, with the identity
restriction. Its cover adjacency is `|i − j| = 1`, so the ladder has a length and a grain three
steps below another is three steps into its horizon. -/
def ladderTower : Tower.{0, 0} ℕ := constantFaceTower ℕ Bool

/-- [definition] The declared family on it: the identity at every chart but chart `4`, where it is
the Boolean flip. Its square with the restriction fails exactly at the pairs that carry chart `4`. -/
def ladderStep : ∀ i : ℕ, ladderTower.Face i → ladderTower.Face i :=
  fun i b => if i = 4 then !b else b

/-- [definition] The whole index as the declared aperture. -/
def wholeAperture : ℕ → Prop := fun _ => True

/-- [proved-derived; formal-checked] A cover of the ladder is a step of exactly one. -/
theorem ladder_coveredBy_iff (i j : ℕ) : CoveredBy wholeAperture i j ↔ i + 1 = j := by
  constructor
  · rintro ⟨⟨hij, hji⟩, hmid⟩
    by_contra hne
    exact hmid ⟨i + 1, trivial, ⟨by omega, by omega⟩, by omega, by omega⟩
  · rintro rfl
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rintro ⟨m, -, ⟨h1, h2⟩, h3, h4⟩
    omega

/-- [proved-derived; formal-checked] So one step of the index horizon is one grain, in either
direction. -/
theorem ladder_coverAdjacent_iff (i j : ℕ) :
    CoverAdjacent wholeAperture i j ↔ (i + 1 = j ∨ j + 1 = i) := by
  constructor
  · rintro (h | h)
    · exact Or.inl ((ladder_coveredBy_iff i j).mp h)
    · exact Or.inr ((ladder_coveredBy_iff j i).mp h)
  · rintro (h | h)
    · exact Or.inl ((ladder_coveredBy_iff i j).mpr h)
    · exact Or.inr ((ladder_coveredBy_iff j i).mpr h)

/-- [proved-derived; formal-checked] **A chain of `k` cover steps joins charts whose ranks differ by
at most `k`.** This is what makes the index distance a distance rather than a bound, and it is what
lets a coarse observer's horizon be proved *too small* rather than merely not exhibited. -/
theorem ladder_chain_rank_bound {k i j : ℕ}
    (h : ChainDistanceAtMost (CoverAdjacent wholeAperture) k i j) :
    i ≤ j + k ∧ j ≤ i + k := by
  induction h with
  | here k i => omega
  | step first _ ih =>
      have hstep := (ladder_coverAdjacent_iff _ _).mp first
      omega

/-- [proved-derived; formal-checked] At chart `4` the declared step is the flip. -/
theorem ladderStep_at_four (b : Bool) : ladderStep 4 b = !b := rfl

/-- [proved-derived; formal-checked] And at every other chart it is the identity. -/
theorem ladderStep_below {i : ℕ} (hi : i ≠ 4) (b : Bool) : ladderStep i b = b := if_neg hi

/-- [counterexample; formal-checked] The failing square of the ladder: between chart `4` and any
coarser chart, restricting after the step is not the step after restricting. -/
theorem ladderSquare_fails_at_the_top (i : ℕ) (hi : i ≠ 4) (hle : i ≤ 4) :
    ladderTower.restrict hle (ladderStep 4 false)
      ≠ ladderStep i (ladderTower.restrict hle false) := by
  show (true : Bool) ≠ ladderStep i false
  rw [ladderStep_below hi]
  exact fun hcontra => Bool.noConfusion hcontra

/-- [proved-derived; formal-checked] And every square whose two charts avoid chart `4` commutes: the
defect is at that one rung of the ladder and nowhere else. -/
theorem ladderSquare_commutes_below {i j : ℕ} (hi : i ≠ 4) (hj : j ≠ 4) (hle : i ≤ j) (x : Bool) :
    ladderTower.restrict hle (ladderStep j x) = ladderStep i (ladderTower.restrict hle x) := by
  show ladderStep j x = ladderStep i x
  rw [ladderStep_below hi, ladderStep_below hj]

/-- [proved-derived; formal-checked] **Which is which depends on the observer's grain.** The same
region of the same ladder: the observer at chart `4` has the failing square inside its horizon at
`k = 1`; the observer at chart `1`, three cover steps below it, cannot reach chart `4` at `k = 2` at
all and reaches it at `k = 3`. Their two profiles of one region differ, and `visibleSquare_shift`
relates them exactly by the observers' own index distance. -/
theorem the_fine_observer_sees_at_one_step_what_the_coarse_one_sees_at_three :
    ChainDistanceAtMost (CoverAdjacent wholeAperture) 1 4 3 ∧
      ¬ ChainDistanceAtMost (CoverAdjacent wholeAperture) 2 1 4 ∧
        ChainDistanceAtMost (CoverAdjacent wholeAperture) 3 1 4 ∧
          (ladderTower.restrict (show (3 : ℕ) ≤ 4 by omega) (ladderStep 4 false)
            ≠ ladderStep 3 (ladderTower.restrict (show (3 : ℕ) ≤ 4 by omega) false)) := by
  refine ⟨?_, ?_, ?_, ladderSquare_fails_at_the_top 3 (by omega) (by omega)⟩
  · exact ChainDistanceAtMost.step (j := 3) (by rw [ladder_coverAdjacent_iff]; omega)
      (.here 0 3)
  · intro hcontra
    have := ladder_chain_rank_bound hcontra
    omega
  · exact ChainDistanceAtMost.step (j := 2) (by rw [ladder_coverAdjacent_iff]; omega)
      (ChainDistanceAtMost.step (j := 3) (by rw [ladder_coverAdjacent_iff]; omega)
        (ChainDistanceAtMost.step (j := 4) (by rw [ladder_coverAdjacent_iff]; omega)
          (.here 0 4)))

/-! ### The profile is a receiver reading -/

/-- [proved-derived; formal-checked] **A receiver can only lose a defect, never invent one.** If a
receiver separates the two routes of a square then the two routes' faces already differ; the
converse fails, and the witness is below. -/
theorem receiver_defect_is_a_structural_defect {Face : Type u} (R : Face → ℚ) {a b : Face}
    (h : R a ≠ R b) : a ≠ b := fun hab => h (hab ▸ rfl)

/-- [definition] The poorer receiver of the ladder's failing square: it reads both routes alike. -/
def poorLadderReading : Bool → ℚ := fun _ => 0

/-- [definition] The richer one: it separates them exactly. -/
def richLadderReading : Bool → ℚ := fun b => if b then 1 else 0

/-- [counterexample; formal-checked] **A poorer receiver reads flat what a richer one reads as
curved.** The two routes of the ladder's top square return different faces; the poor receiver's
discrepancy between them is `0` and the rich receiver's is `1`. The defect profile is therefore a
reading of the region and not its identity. -/
theorem a_poorer_receiver_reads_the_defect_flat :
    ladderStep 4 false ≠ false ∧
      poorLadderReading (ladderStep 4 false) = poorLadderReading false ∧
        richLadderReading (ladderStep 4 false) ≠ richLadderReading false := by
  refine ⟨fun hcontra => Bool.noConfusion hcontra, rfl, ?_⟩
  show (1 : ℚ) ≠ 0
  norm_num

/-- [counterexample; formal-checked] And the reason no reading of the poor receiver could have
recovered the defect: `Foundation/Receiver.lean::ReceiverInsufficiency`, cited and not rebuilt. -/
def ladderReceiverInsufficiency :
    Holonics.ReceiverInsufficiency poorLadderReading richLadderReading where
  left := ladderStep 4 false
  right := false
  sameEntering := rfl
  differentReturned := by
    show (1 : ℚ) ≠ 0
    norm_num

/-- [proved-derived; formal-checked] Hence no receiver-to-receiver transformer carries the poor
reading back to the rich one: a profile read flat cannot be un-flattened by reading it harder. -/
theorem no_transformer_from_the_flat_reading :
    IsEmpty (Holonics.ReceiverTransformer poorLadderReading richLadderReading) :=
  ⟨fun t => t.excludesInsufficiency ladderReceiverInsufficiency⟩

/-! ### Passages across ranks, and what each kind costs -/

/-- [proved-derived; formal-checked] **A descending chain is the tube's own passage.** Every step is
a restriction, so the composite follows refinement and is not a wormhole — cited from
`Tube.refinementRoute_is_not_a_wormhole`, which is this file's own. An observer whose index horizon
contains the chain sees it. -/
theorem descending_chain_is_the_tubes_own {Station : Type uS} [Preorder Station] {Index : Type u}
    [Preorder Index] (tube : Tube.{uS, u, v} Station Index) {s t : Station} (hst : s ≤ t)
    (r : Index → Index) (r_mono : ∀ {i j : Index}, i ≤ j → r i ≤ r j)
    (r_refines : ∀ j : Index, j ≤ r j) :
    ¬ (tube.refinementRoute hst r r_mono r_refines).ConnectsIncomparableCharts :=
  tube.refinementRoute_is_not_a_wormhole hst r r_mono r_refines

/-- [proved-derived; formal-checked] **A rising step needs the retained residual**, and with it the
fine face returns exactly. This is `ResidualMigration.traversability_is_the_residual` at one step of
the ladder, cited through `reopen_apply` and not reproved: looking toward the fine is a fibre, and a
route that rises pays for it by retaining what the restriction dropped. -/
theorem rising_step_needs_the_retained_residual {Index : Type u} [Preorder Index]
    {S T : Tower.{u, v} Index} (M : ResidualMigration S T) (j : Index) (x : S.Face (M.index j)) :
    M.reopen j (M.face j x) (M.residual j x) = x :=
  M.reopen_apply j x

/-- [counterexample; formal-checked] **And where no chain of comparable charts exists at all, the
passage is a wormhole** — `swapWormhole`, over an index with no common refinement. The three kinds
are therefore inhabited and distinguished: the tube's own composite, the passage a retained residual
buys, and the passage the tube does not have. -/
theorem the_three_kinds_of_cross_rank_passage (Station : Type uS) [Preorder Station] (X : Type v)
    (s t : Station) :
    (swapWormhole Station X s t).passage.ConnectsIncomparableCharts :=
  (swapWormhole Station X s t).crosses

end Holonics.Transport.ContinuingTube

section Audit
open Holonics.Transport.ContinuingTube

#print axioms ChartwiseMigration.toMigration
#print axioms ChartwiseMigration.toMigration_staysAtItsChart
#print axioms ChartwiseMigration.toMigration_not_connectsIncomparableCharts
#print axioms ChartwiseMigration.ofStationaryMigration
#print axioms ChartwiseMigration.ofStationaryMigration_face
#print axioms ChartwiseMigration.ofStationaryMigration_toMigration_face
#print axioms ChartwiseMigration.comp_face
#print axioms ChartwiseMigration.comp_toMigration
#print axioms ChartwiseMigration.carrySection_witness
#print axioms square_is_genuine_content
#print axioms Tube.square
#print axioms Tube.transport_roundTrip
#print axioms Tube.segmentation_is_immaterial
#print axioms Tube.carryEnd_refl
#print axioms Tube.carryEnd_trans
#print axioms Tube.refinementRoute
#print axioms Tube.refinementRoute_followsRefinement
#print axioms Tube.transport_is_not_a_wormhole
#print axioms Tube.refinementRoute_is_not_a_wormhole
#print axioms Wormhole.not_factorsThroughRefinement
#print axioms constantTube
#print axioms constantFaceTower
#print axioms twoChartTower_is_constantFaceTower
#print axioms swapWormhole
#print axioms lossySwapMigration
#print axioms lossySwapMigration_connectsIncomparableCharts
#print axioms lossySwapMigration_face_not_injective
#print axioms lossySwapMigration_no_reverse_passage
#print axioms lossySwapMigration_residual_restores_the_reverse_passage
#print axioms lossiness_is_independent_of_being_a_wormhole
#print axioms tube_circuit_has_no_defect
#print axioms ChartwiseMigration.cocycleDefect
#print axioms circuit_defect_is_holonomy_not_loss
#print axioms flipCircuit_hasDefect
#print axioms flipCircuit_carries_no_invariant_end
#print axioms padicTube_end_equiv
#print axioms padicTube_crossSection_branching
#print axioms padicTube_adjacent_branching
#print axioms padicTube_carryEnd
#print axioms Tube.clockedSpan
#print axioms Tube.clockedSpan_split_rejoin
#print axioms Tube.clockedSpan_openGap_has_no_joined_occurrence
#print axioms squareVerdict_total
#print axioms ChartwiseMigration.squareVerdict
#print axioms grainSquare_fails
#print axioms grainSquareDefect
#print axioms grainSquare_defect_is_not_a_loss
#print axioms enclosureTower
#print axioms boundaryScaleMigration
#print axioms boundaryScaleMigration_staysAtItsChart
#print axioms boundaryScale_staircase_is_not_a_wormhole
#print axioms boundaryScaleResidualMigration
#print axioms projectionScalePassage_interior_not_injective
#print axioms projectionScalePassage_no_reverse_passage
#print axioms visibleSquare_shift
#print axioms DeclaredTube.profileFlat_of_chartwise
#print axioms tube_profile_is_flat_at_every_horizon
#print axioms coverAdjacent_symm
#print axioms coverAdjacent_comparable
#print axioms cycleShortCircuit_has_no_defect
#print axioms cycleLongCircuit_hasDefect
#print axioms flat_near_curved_far
#print axioms ladder_coverAdjacent_iff
#print axioms ladder_chain_rank_bound
#print axioms ladderSquare_fails_at_the_top
#print axioms ladderSquare_commutes_below
#print axioms the_fine_observer_sees_at_one_step_what_the_coarse_one_sees_at_three
#print axioms receiver_defect_is_a_structural_defect
#print axioms a_poorer_receiver_reads_the_defect_flat
#print axioms ladderReceiverInsufficiency
#print axioms no_transformer_from_the_flat_reading
#print axioms descending_chain_is_the_tubes_own
#print axioms rising_step_needs_the_retained_residual
#print axioms the_three_kinds_of_cross_rank_passage

end Audit
