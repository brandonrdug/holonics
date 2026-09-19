# The continuing object is the shared carrier

[definition] This is a construction contract, not a competing order. [THE_ROADMAP](THE_ROADMAP.md)
remains the sole milestone order and [CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md) the sole
current position. This document states the formalization intentions for the carrier that HNN,
Athena, the mathematical applications and the biological ecologies all instantiate. It schedules
no milestone of its own; its items are discharged inside the increments that consume them.

## The object

[definition] A Holon is a typed, computable family of situated presentations:

```text
H = (I, X, G, R, P, L, W)
```

`I` an index of apertures, grains, charts, precisions and environments; `X : I^op -> C` the faces
over that index together with their restriction maps; `G` the generators and their ordered
passages; `R` the receiver family; `P` the presentation/codec family; `L` causal lineage; `W` the
cost enrichment. Its established mathematical core is a pro-object carrying a locality axis, a
dependent face type, a coalgebraic continuation, a path category of generators and a cost
enrichment. No single face is the object, and no materialized face is admitted without its
receiver, lineage, decoder, residual and cost.

[definition] The three lawful returns of an attempted global section are `unique`, `plural` and
`obstructed`. A tower whose levels are all inhabited may still admit no coherent section; that
obstruction is the object's content and is returned, never resolved by choosing a representative.

[established-bounded; formal-checked; implemented-exact] **The index has two axes, and a tower is
one of them.** A *tube* is a family of towers along a longitudinal station axis: the transverse
section at each station is a `Tower` — the aperture/grain/precision ladder, whose `restrict` is the
coarsening of that section — and the longitudinal passage is the transport between stations. A tower
is therefore one chart of a tube, its cross-sectional ladder, and "tower" names that ladder in the
Iwasawa instance exactly as it does elsewhere: the transverse sections of `padicTower` branch
`p`-adically into a `p`-ary tree (`padicFibre_card = p ^ k`, an equality), and the tube's **end** is
its compatible-section space, `padicTube_end_equiv : ℤ_[p] ≃ End`. The one law joining the axes is
that longitudinal transport and transverse restriction **commute**, and that law is not new:
`ChartwiseMigration` is proved to be exactly a `Migration` that `StaysAtItsChart`, so the square *is*
`Migration.naturality`. A staircase between two grains — between atoms and molecules, between
planets — is a move along the transverse axis; a passage between two stations is a move along the
longitudinal one. The paired owners are
[`Transport/ContinuingTube.lean`](../../formal/elementary-holonics/ElementaryHolonics/Transport/ContinuingTube.lean)
and [`continuing_tube.rs`](../../crates/holonic-engine/src/continuing_tube.rs), each citing the
other by declaration, and step 2 of
[THE_REALITY_OF_DIFFERENCE_IN_CONSTRUCTION](THE_REALITY_OF_DIFFERENCE_IN_CONSTRUCTION.md#2-swing-restriction-and-the-same-potential-across-tube-charts--returned-foundation)
consumes them.

[definition] **A wormhole is exact, and it is the non-factoring condition on that two-axis object.**
A wormhole is a passage between two stations whose index map crosses to a chart the tube's order does
not relate — `Migration.ConnectsIncomparableCharts`, decided by the index map alone. A tube's own
passages are its longitudinal transports and its refinement routes, and **none of them is one**
(`transport_is_not_a_wormhole`, `refinementRoute_is_not_a_wormhole`); `swapWormhole` over
`twoCharts_no_common_refinement`'s index is one, where there is no common refinement to compare
against and the comparison is therefore undefined rather than false. The definition answers both
records: `docs/canon/TABLET_THE_CHART.md:263` reads a wormhole as "passage through a chart where the
answer is one step, when in the source chart it is not reachable at all", and
`research/records/2026-07-26_THE_TUBE_CARRIES_THE_EXTERIOR_FACE_THE_DISTANT_FIELD_RETURNS_THROUGH_REBASE.md:222`
requires a founded throat joining two actual mouths, owing both transports, a loop holonomy and a
transport cost rather than zero-cost transport — the mouths are the two stations, the reverse
transport is `ResidualMigration.reopen`, and the cost is C5's, which
`PresentationCost.swapMigration_route_isEmpty` records as having no refinement route to measure.
Traversability is `ResidualMigration.traversability_is_the_residual`, cited not reproved, and it is
**independent** of being a wormhole: `lossiness_is_independent_of_being_a_wormhole` inhabits all four
cells, with `padicHalfMigration` lossy and not a wormhole, `swapMigration` a wormhole and not lossy,
and `lossySwapMigration` both.

[established-bounded; formal-checked; implemented-exact] **Where the two-axis square fails, the
failure is the content.** `SquareVerdict` is `commutes | defect` and `squareVerdict_total` makes it
total; `grainSquareDefect` is a real instance — the contact receiver does not commute with the grain
selection, which is `GrainRestriction.equal_aperture_is_not_lawful`, and whose physical reading is
the census `grain_tower.rs` measures on the M5 deposit (301 `Inside` against 1,397 at an equal 8 Å
aperture, 0 in the other direction), cited here rather than re-measured. The defect is not a loss:
`grainSquare_defect_is_not_a_loss` cites `grain_residual_reopens_the_source`, so what the two routes
lose is agreement and not information. `check_commuting_square` returns the same verdict with its
witness over `grain_tower.rs`'s own `GrainFace` and `GrainSelection`, and refuses a declared chart
aperture, face population or work product above its ceiling with checked arithmetic.

## What the repository already owns

[established-bounded; source-inspected] The restriction axis is
[`Foundation/BoundaryScalePassage.lean:16-94`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/BoundaryScalePassage.lean):
one commuting square `coarseBoundary . interiorTransport = boundaryTransport . fineBoundary`, and
composition of passages when middle boundaries agree. It owns the linear restriction law and says
nothing about how grains are founded.

[proved-derived; formal-checked] That commuting square is a migration's.
`Transport/ContinuingTube.lean::boundaryScaleMigration` exhibits a `BoundaryScalePassage` as a
`ChartwiseMigration` between two enclosure towers over `boundary ⊑ interior`, whose single
nonreflexive naturality square **is** its `boundary_natural` field; the scale staircase therefore
stays at its chart and is never a wormhole. It is **not** a `Transition`: its own data determines no
residual — `residual_is_not_determined_by_the_face_map` is the general reason — and
`projectionScalePassage_no_reverse_passage` exhibits a concrete scale passage whose transported face
alone never returns. Supplying the residual at each chart makes it a `ResidualMigration`
(`boundaryScaleResidualMigration`), and then the return is
`ResidualMigration.traversability_is_the_residual`. That is the exact difference between the two
staircases the repository owns: `BoundaryScalePassage` supplies no residual and is a migration, while
`GrainRestriction.selectionTransition` supplies one and is a transition.

[established-bounded; source-inspected] The **longitudinal** axis is owned too, and the carrier is
built on it rather than beside it.
[`Transport/WorldTube.lean`](../../formal/elementary-holonics/ElementaryHolonics/Transport/WorldTube.lean)
carries `ExactLocalClock` with its addressed passage, and `ClockedSpan` — an occurrence population
with both boundary maps, an exact local-clock face, a returned receiver face and an obstruction —
whose serial contact is the existing pullback join, whose re-segmentation changes only the
presentation (`split_rejoin_preserves_completeFace`, `resegmentation_natural`) and whose missing
joining equality is an open gap with no joined occurrence (`openGap_has_no_joined_occurrence`);
`WorldTube` adds the interior current, the `outwardRadical`, lawful silence, the world return and the
cultivated rest that descends through every finite ordered successor word.
`Transport/WorldTubePotential.lean` carries the split/rejoin `Equiv`, the associator, the invariance
of `historyOutcomes` under both, and the `BoundaryScalePassage` family-image laws.
`Millennium/HolonicClockedPantographicSwing.lean::ClockRouteComparison.returnedHolonomy_eq_one_iff`
owns clock-route holonomy; `Foundation/FractalPacking.lean` owns a branching cross-section as exact
rational cells with separated siblings and retained ordered addresses;
`Millennium/HolonicSensoryWorldTube.lean` is a historical import path for the `Transport` owner and
adds nothing. On the executable side
[`tube.rs::ReceiverTube`](../../crates/holonic-engine/src/tube.rs) is the physical realization of the
same two axes — core receiver, transverse section, horizon as the link of the receiver's simplicial
star, exact projective attachment, and `presentation_holonomy` as the composite of its longitudinal
presentation word — and `crates/holonic-life/src/exchange_world_tube/` is the record-incidence
instance. `Transport/ContinuingTube.lean` composes these owners; it founds no third carrier.

[established-bounded; source-inspected] The dynamic law is
[`Foundation/ReceiverHistoryCompression.lean:33-146`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverHistoryCompression.lean):
`q . T_g = U_g . q` on generators extends to every ordered word without enumerating histories, a
separating successor refutes a proposed quotient, and `:30-31` explicitly disclaims decoder cost.
`Foundation/Receiver.lean:94` carries the static `D . E = rho` with its preimage fibre and
insufficiency witness. These two are the whole of Holonic Encoding's formal surface.

[established-bounded; source-inspected] The future-stable quotient is
`Foundation/CausalRelevance.lean:48-297`: generator-invariant, present-blind, greatest among such,
with a separator returned on inequality. `Transport/ReceiverPotential.lean:25-228` transports the
whole compatible family through every word and refines it by observation.
`Foundation/Holon.lean:88-125` rebases the complete fibre rather than relabelling outputs.
`Millennium/Gluing.lean:32-164` carries the obstruction population;
`Millennium/HolonicDirectedPassage.lean:260-330` already contains the non-orientability model as
`boolFlipCoherent_isEmpty`, and `:303` the only tower existence theorem in the repository.

[established-bounded; source-inspected] The arithmetic tower is local only.
`Millennium/NormRelation.lean:120-261` proves the Euler-factor identity in any integral domain
with unramified and ramified readings and coprime layer composition; its relative-orbit step sits
at `:256` as an unused `Prop`, gap located at `:60-70`. `Millennium/SelmerCalculus.lean:54-146`
defines `Sel = intersection of r_i^-1(L_i)` with the obstruction vanishing exactly when local
admission implies global realization. `Millennium/FamilyFace.lean` varies the curve, not the field.

## Formalization intentions

[established-bounded; formal-checked; implemented-exact] **C1, C2, C3 and C4 are returned.** The paired
owners are [`Foundation/ContinuingTower.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/ContinuingTower.lean)
and [`continuing_tower.rs`](../../crates/holonic-engine/src/continuing_tower.rs), each citing the
other by declaration. C3 holds definitionally: `observationFibre_eq_preimageFibre` is `rfl`, so the
restrict-to-chart receiver's preimage fibre is the observation fibre rather than merely equivalent
to it. C4's `Transition` carries `Residual`, `apply`, `residual` and an executable `reopen` with
`reopen_apply : reopen (apply x) (residual x) = x`; composition composes residuals, `ofLinearSection`
exhibits `SectionResidual.source_reconstructs` as that same field rather than duplicating it, and
`toReceiverHistoryCompression` inherits the every-ordered-word law instead of re-inducting it. Its
first physical consumer is the grain restriction in
[the biological ecology](THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md).

[proved-derived; formal-checked] Neither axis of a functorial tube can express a loop obstruction.
On the transverse ladder, `restrict_refl` with proof irrelevance forces `restrict h` to be the
identity at every reflexive step and `restrict_trans` forces every index round trip to be the
identity; on the longitudinal axis, `Tube.transport_roundTrip` and `tube_circuit_has_no_defect` force
the same of every station round trip. Non-orientability is therefore a **declared circuit** whose
composite is not the identity, and its owner is the atlas rather than the tower or the tube:
`ChartwiseMigration.cocycleDefect` builds `Foundation/ReceiverAtlas.lean::CocycleDefect` from such a circuit, and
`defect_is_holonomy_not_loss` proves both routes still reopen their own source exactly, so what
differs is the presented face. `flipCircuit_carries_no_invariant_end` is the smallest instance — a
tube closed on itself with nontrivial holonomy carries no continuing object that survives the circuit
— and it cites the existing `boolFlipCoherent_isEmpty` rather than rebuilding it. Interlinked
toroidal modes are tubes closed on themselves; they are not towers.

[established-bounded; formal-checked; implemented-exact] **C2 and the `Migration` functor are
returned.** `padicSectionEquiv` proves `Z_p ~ CompatibleSection` in both directions — forward through
`PadicInt.toZModPow`, reverse through `PadicInt.ofIntSeq` from the section's own compatibility — and
`padicFibreEquiv`/`padicFibre_card` prove the exact splitting: the fibre over a level-`m` face is in
bijection with `ZMod (p^k)` at level `m + k`, so `Nat.card` of it is `p^k` on the nose and one
refinement step splits it into exactly `p` cosets of `ker toZModPow`, with
`padic_sameFace_iff_sub_mem_ker` identifying the fibre as a coset through Mathlib's
`PadicInt.ker_toZModPow`. C2's coset index *is* C4's residual: `padicRestrictTransition` is
`Tower.restrictTransition` with `padicDigitGap` as its residual. `Migration` is the functor of index
categories with its natural transformation on faces, with composition, associativity and a two-sided
identity by `rfl`, and `carrySection`/`carrySection_comp` as the schema-history operation.

[proved-derived; formal-checked] `Holon.Rebase` **fits** as the invertible `Migration` and is not
founded again: `rebaseMigration` presents a holon's own diagram as a height-two tower over
`{sourcePort, targetPort, facePort} ⊑ occurrence` and exhibits `Rebase`'s four equivalences as the
components of a migration with identity index. The one bookkeeping discrepancy is recorded in the
source: `Tower.Face : Index -> Type v` puts a tower's faces in one universe while `Holon.{u,v,w,x}`
allows four, so the presentation is stated for a holon whose four types share a universe; no
mathematical content is lost. `ReceiverCodeCost.serial_boundary_balance` owns C5's additivity law and
is cited, never rebuilt; `Migration.CostBoundedByRefinementRoute` states the cost comparison over an
abstract ordered cost and founds no cost enrichment there. C5 below now discharges that comparison
over a concrete `CostVector` wherever a refinement route exists, and proves it caller-decided as
originally stated, and `ContinuingTower.lean` now cites `Foundation/PresentationCost.lean` for that
discharge at both places it raises the comparison. Only the definition's own name still reads "the
open cost comparison"; its docstring names the file that discharges it.

[proved-derived; formal-checked] Two separations about `Migration` that a tower cannot express are
also proved. A tower's passage is typed `i <= j -> Face j -> Face i`, so between incomparable charts
it has none, and a common refinement supplies none either because a span is not a map:
`Migration.ConnectsIncomparableCharts` names the migrations that cross that gap, decided by the index
map alone, and `not_factorsThroughRefinement_of_connectsIncomparableCharts` separates them from the
ones that are the tower's own restriction family. `swapMigration` over `twoCharts_no_common_refinement`'s
discrete index has the property; `rebaseMigration` and the lossy `padicHalfMigration` do not, so
lossiness and non-factoring are independent. And
`ResidualMigration.traversability_is_the_residual` proves that the reverse passage from the migrated
face alone exists exactly when the component is injective, with the retained residual restoring it
exactly otherwise.

[definition] **C1 — Deposit the tower.** `Foundation/ContinuingTower.lean`: `Tower`,
`CompatibleSection`, `ObservationFibre`, `GluingResult`, `MaterializedFace`, `ComputableTower`,
with the trichotomy total. Join it to `SuccessorWitnessSystem` and `GluingPassage.Obstruction`
rather than founding a parallel family.

[definition] **C2 — The canonical non-Archimedean instance.** `Z/p^n` with surjective restrictions,
`Z_p` sections through `PadicInt.toZModPow`, both directions of `Z_p ~ CompatibleSection`, and the
exact fibre splitting into `p` cosets of `ker toZModPow`. Beside it, a tower with every level
inhabited and no coherent section, so that `plural` and `obstructed` both have witnesses.

[definition] **C3 — Identify the fibres.** `ObservationFibre ~ Holon.PreimageFibre` for the
restrict-to-chart receiver, so the tower's fibre and the repository's existing preimage fibre are
one object rather than two vocabularies.

[definition] **C4 — The non-invertible transition.** Every formal chart map in the repository was
invertible. A `Transition` carrying a residual, and a `Migration` as a functor of index categories
with a natural transformation, are required before lossy codecs, schema history or coarse graining
can be stated at the same grade as the invertible rebase. Both are now deposited; `Migration`'s
consuming case is an object saved under one chart family and read under another, and
`ResidualMigration.square_either_route_reopens` states it exactly: one transported face, two
different retained residual pairs, each reopening the source with no remainder.

[established-bounded; formal-checked; implemented-exact] **C5 — Cost as a receipt — is returned.**
The paired owners are
[`Foundation/PresentationCost.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/PresentationCost.lean)
and [`presentation_cost.rs`](../../crates/holonic-engine/src/presentation_cost.rs), each citing the
other by declaration. A `CostReceipt` carries the five exact natural coordinates `bytes`,
`decodeWork`, `updateWork`, `certificateWork`, `residual`, and **each coordinate carries the
`Provenance` that produced it** — measured by a named instrument, derived from measured counts by a
written rule, or explicitly declared by an exterior party and marked *not accounted*. There is no
constructor that takes a number without one. The representation objective
`C(P;q) = a*bytes + b*decodeWork + c*updateWork + d*certificateWork + e*residual` is
`Weighting.objective`: one receiver of the receipt, never the identity of a presentation.
`ReceiverCodeCost.serial_boundary_balance` owns additivity and is cited at `serial_receipt_balance`,
which instantiates it at a one-occurrence holon over the chart type so the middle potential cancels
through that theorem's own `Holon.Interaction`; `CostReceipt.compose` is the definition it licenses,
and additivity is not re-proved.

[proved-derived; formal-checked] The frontier is the object and the scalar score is not. Dominance
is the product partial order (`Pi.partialOrder`, cited) and is antisymmetric **on the cost vector
only**: `dominates_antisymm_vector` returns vector equality, and
`dominates_antisymm_fails_on_receipts` exhibits a measured 12 and a supplier's declared 12 as one
cost vector and two receipts. The frontier of a finite nonempty family is a nonempty dominating
antichain (`frontier_nonempty`, `exists_frontier_dominating`, `frontier_isAntichain`). Every
strictly positive weighting's minimizer lies on it (`minimizer_isFrontierPoint`) and **the converse
is false**: `unsupported_not_minimizer` exhibits a frontier point strictly above the chord between
two others that no nonnegative weighting putting weight on either varying axis ever selects. A
linear receiver sees only the lower convex hull; the frontier is the antichain, and the two differ —
that is the formal reason a scalar score cannot stand in for the frontier.
`frontier_reparameterization_invariant` proves the frontier survives a strictly monotone change of
unit on each coordinate, while `scalar_minimizer_not_reparameterization_invariant` flips the scalar
minimizer between two permanently incomparable presentations under exactly such a change. Kolmogorov
minimality is incomputable and **no minimal encoding is asserted**; `frontier_has_no_least_point` is
the formal replacement — in general no member of a frontier is below all the others, so "the optimal
presentation" names nothing at a receiver weighing more than one axis. On the residual axis,
`Transition.comp`'s pairing is cited rather than rebuilt: the residual fibre multiplies under
composition, so its code size is subadditive (`codeBits_residual_comp_le`) and strictly so at
`codeBits_residual_comp_lt_witness` — `CostReceipt.compose` is an honest upper bound on the
composite's own residual coordinate, not its value.

[proved-derived; formal-checked] `Migration.CostBoundedByRefinementRoute` is **discharged where it
holds and shown contentless as it was stated**, which changes this document's own earlier sentence
that it merely "states the cost comparison and leaves it open". As written it takes the route cost as
an arbitrary caller-supplied function, and `costBoundedByRefinementRoute_is_caller_decided` proves
that one fixed migration with one fixed migration cost admits a route cost making it true and another
making it false: the `Prop` records a choice of the caller, not a property of the migration. Its
corrected form is a theorem about a `CostedTower` — a tower whose restrictions carry receipts and
satisfy `route_dominates` — and `costBoundedByRefinementRoute_of_route` discharges the comparison
over the concrete `CostVector` for every migration that factors through refinement, by that law and
nothing else. Where the migration connects incomparable charts there is no route at all:
`swapMigration_route_isEmpty` returns `IsEmpty (RefinementRoute ...)` at every chart, by citing
`twoCharts_no_common_refinement`.

[proved-derived; formal-checked] **Costed towers exist, `route_dominates` is derived at them, and it
is not automatic.** An earlier form of this paragraph called `route_dominates` "the subadditive
reading of `serial_boundary_balance`" while no `CostedTower` had been built; both halves are now
corrected. Two instances are constructed: `padicCostedTower`, which puts on `padicTower` the receipt
each restriction itself determines — the chart gap in base-`p` digits, and `codeBits` of the exact
residual fibre `padicRestrictTransition` retains — and `unitCostedTower`, the minimal one on
`unitTower`. `costBoundedByRefinementRoute_padic` is the comparison discharged at the first of them
against `padicHalfMigration`, with neither side supplied by a caller. Which law discharges the
tower's own field is **axis-dependent, and `serial_boundary_balance` is not all of it**:
`serial_receipt_balance` gives the two-step *total* as `CostReceipt.compose`
(`padicCostedTower_serial_balance`), and the comparison of the direct receipt against that total is
exact additivity of the digit gap on `bytes`/`decodeWork`/`updateWork`
(`padicCostedTower_route_equality_on_step_axes`), one saved header on `certificateWork`, strictly at
every triple (`padicCostedTower_route_strict_at_certificateWork`), and on `residual` **not**
`serial_boundary_balance` at all but `codeBits` subadditivity — code sizes do not add — which at
these transitions is `codeBits_residual_comp_le` applied to the tower's own restriction transitions
(`padicCostedTower_residual_eq_comp`, `padicCostedTower_route_residual_is_codeBits_comp`), strict at
`padicCostedTower_route_strict_at_residual`. The field is a real condition and not a decoration:
`squaredGapReceipt` is a well-formed receipt assignment billing the square of the chart gap, and
`no_costedTower_with_squaredGapReceipt` proves no `CostedTower` over any ℕ-indexed tower can carry
it, since its own law at charts `0 ≤ 1 ≤ 2` would read `4 ≤ 2`. Rust mirror:
`presentation_cost::CostedResidueTower`, whose `route_comparison` builds both sides of the
comparison from the tower's own `ResidueTower::split_fibre` rather than from caller-supplied
receipts, with `squared_gap_receipt` as the assignment that fails it.

[established-bounded; measured] One real measurement is wired. `presentation_cost::m5_presentations`
produces three receipts for one object — the
`(label_asym_id, label_seq_id, label_comp_id, label_atom_id, x, y, z)` table of
`ptxv2-free-rbx1-seed2.cif`, 1667 atom rows of which 204 are alpha carbons — with every byte count
measured from the file by `measure_atom_site_block` and every identifier count measured through
`physical_intake::mmcif::StructurePresentation`. The three measured cost vectors, in axis order
`(bytes, decodeWork, updateWork, certificateWork, residual)`, are

* the deposited mmCIF `_atom_site` block as text — `(167192, 167192, 166700, 178861, 0)`;
* the scaled-integer wire at the resident decimal grain, `AtomOccurrence::projected_wire` on every
  atom — `(96438, 21423, 57, 33092, 0)`, the zero residual **measured** as the sum over distinct
  wire rows of `code_bits` of the object rows landing on it, so the projection is injective on this
  deposit rather than assumed to be;
* the alpha-carbon restriction, `grain_tower::GrainSelection` on that wire — `(11832, 2652, 58,
  4080, 676848)`, the residual being the dropped atom records in bits, which is exactly what
  `Transition::reopen` needs to return the source.

The wire **strictly dominates** the deposited text on every axis; the alpha-carbon restriction is
**Pareto-incomparable** with both, cheapest in bytes and the only presentation owing residual bits.
The measured frontier is therefore two points and the deposited text is off it; a byte-weighted
receiver selects the restriction and a residual-weighted receiver selects the wire — the same
non-substitutability the formal counterexample states, on real data.

[established-bounded; formal-checked; implemented-exact] **C6 — Capability, chart and atlas — is
returned.** The paired owners are
[`Foundation/ReceiverAtlas.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverAtlas.lean)
and [`receiver_atlas.rs`](../../crates/holonic-engine/src/receiver_atlas.rs), each citing the other
by declaration. `Capability` carries `kind`, `Parameters`, `admits`, `Value`, `operations` and
`laws`, and the doctrine is a theorem rather than a slogan:
`no_operation_from_the_carrier_alone` refutes any uniform function from a carrier and a capability
declaration to an operation, and `operation_is_supplied_not_conferred` exhibits one carrier, one
capability and two admissible integer weightings with two different operations — so no function of
the geometry produced either. `LocalChart` carries `Region`, `Coordinate`, `place`, `fibre`,
`fibre_exact` and `metric : Option (SuppliedCapability Coordinate)`; `preimageFibre_subset_fibre`
proves the population behind a face is retained, and `reading_none_of_metric_none` makes asking a
capability-less chart for an angle return `none` rather than a zero.

[proved-derived; formal-checked] **An embedding is an atlas of placements whose content is its
transition maps, not one global vector.** `ChartTransition` carries C4's `Transition` — lossy, with
its residual, not assumed invertible — so the cocycle on triple overlaps is stated with residuals:
`CocycleDefect` carries both routes' transported faces, `defect_is_holonomy_not_loss` proves each
route still reopens its own source with no remainder, and `cocycle_iff_isEmpty_defect` identifies
the law with the emptiness of its obstruction population. The failure is returned through the
`unique | plural | obstructed` trichotomy — `AtlasGluing`, total by `atlasGluing_total`, with
`no_coherentPlacement_through_defect` and `atlasGluing_obstructed_of_total_defect` — and never as an
error. The classical case is recovered exactly: `ChartCocycle.placementEquiv` proves that an atlas
whose transitions are all bijective and satisfy the cocycle has `CoherentPlacement ≃` the coordinate
of **any one chart**, with the identity link derived from the cocycle rather than assumed. And
`ShiftAtlas.theEmbeddingIsNotOneVector` exhibits an atlas over a nonempty carrier in which every
chart reads a nonempty region into an inhabited coordinate, every transition is lawful and carries
its residual, and there is **no** coherent placement at all — cited from `shiftTower_obstructed`
through `shiftAtlasSection` rather than reproved. `twoCharts_comparison_undefined` cites
`twoCharts_no_common_refinement` for the comparison that is *undefined* rather than false, which is
the gap `swapMigration` crosses and `swapMigration_not_factorsThroughRefinement` separates from the
refinement route. `AtlasIndistinguishable` with `indistinguishable_factors`,
`indistinguishable_transports` and `indistinguishable_of_refinement` is the separating statement:
agreement on every chart already forces agreement of every transported face, and what a refining
atlas cannot separate the refined one cannot either — so a coarse atlas's verdict is a fact about
that atlas and never about the object.

[established-bounded; implemented-exact] The Rust owner instantiates the atlas on the protein with
five charts — `sequence`, `allAtomFrames`, `alphaCarbonGrain`, `contactComplex`, `rigidityReading` —
over the existing owners' types (`grain_tower::GrainFace`, `GrainPair`, `GrainSelection`;
`rigidity_receiver::MaxwellCount` read from an exact rational Jacobian). The alpha-carbon selection
is a **real lossy transition** between two of them and the round trip through its residual is tested
exact; the contact complex forgets the `Open` class and retains it whole, so `Open` is never
rounded. Two relations are deliberately **undeclared** — nothing leaves `sequence` and nothing
reaches `rigidityReading` — and the atlas says so by carrying no entry. The rigidity chart reads
only the presentations that supplied a configuration: a reading that was not supplied is absent,
never zero.

[open] One finding that narrows the plan's wording. At the level of whole atlases over one carrier a
common refinement always exists, by taking the union of the two chart families, so
`EquivalentUnderRefinement` is not the place where the comparison fails. The comparison that is
genuinely **undefined** is the chart-index one — "refine to a common upper bound and restrict back"
— and that is what `twoCharts_no_common_refinement` refuses. `AtlasRefinement` and
`EquivalentUnderRefinement` are deposited with `AtlasRefinement.refl` and
`indistinguishable_of_refinement`; the union construction that would make the atlas-level comparison
total is **not** built, because nothing consumes it yet.

[established-bounded; formal-checked; implemented-exact] **C7 — Bridges — is returned.** The paired
owners are
[`Foundation/Bridge.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/Bridge.lean)
and [`bridge.rs`](../../crates/holonic-engine/src/bridge.rs), each citing the other by declaration.
The eight statuses are one inductive `BridgeStatus`, and `BridgeStatus.entails` is a genuine partial
order — `entails_refl`, `entails_trans`, `entails_antisymm`, all decided over the finite carrier.
`Bridge` carries `status`, `passage : Option Transition` (so a map arrives with the residual it does
not transport), the preserved diagram, and exactly one `EpistemicGrade`; its `passage_of_map` field
makes the status a typed claim, so `equivalence` cannot be declared without supplying the passage.

[proved-derived; formal-checked] **The order is not total, and each non-implication carries a real
witness.** A shared receiver face and an actual map are incomparable, and
`sharedReceiverFace_supplies_no_map` gives the witness through `Receiver.lean`'s
`ReceiverTransformer.excludesInsufficiency`: a blind reading identifies what a faithful reading
separates, so no map of the shared face returns the faithful one. An actual map need not preserve
structure, and the witness is `naturality_is_genuine_content`, cited rather than rebuilt: two
injective face maps, each a lawful `Transition` with zero residual, whose square with the tower's own
restriction fails to commute. An equivalence does not give a natural family — the witness is an
`Equiv` of `ℤ` whose square with a doubling restriction does not commute — and
`speculativeAnalogy_is_off_the_order` proves the eighth status entails nothing and is entailed by
nothing, so it is not a weak connection but a candidate. `statusMeet` is the greatest lower bound
(`statusMeet_lower`, `statusMeet_greatest`), meeting the two incomparable pairs at `coPresence` and
`structurePreservingMap` respectively, and refusing to compose through a speculative analogy at all.
`Bridge.comp` takes that meet together with `composeGrade` and composes the residuals through
`Transition.comp`, so the composite's residual is exactly the pair of component residuals;
`comp_at_meet` and `composedBridge_status_grade` state it. `ProposedBridge` carries required
hypotheses, supporting receivers, counterexamples and a falsifier, and promotion is by type:
`counterexample_blocks_promotion`, `false_hypothesis_blocks_promotion` and
`missing_passage_blocks_promotion` each return `IsEmpty (Promotion …)`.

[established-bounded; implemented-exact] Four bridges that really exist in the tree are
instantiated: `rebaseBridge` (equivalence, `provedDerived`, subsingleton residual) over
`Holon.Rebase`'s face equivalence; `padicHalfBridge` (lossy structure-preserving map,
`provedDerived`) over `padicHalfMigration`'s chart transition, with
`padicHalfBridge_is_not_an_equivalence` citing the exact `p^j` fibre; `grainBridge` (lossy
structure-preserving map, `establishedBounded`) over `GrainRestriction.selectionTransition`, whose
preserved claim is discharged by `grain_residual_reopens_the_source`; and
`proteinEmbeddingProposal`, one honest `ProposedBridge` at `speculativeAnalogy` status and
`interpretation` grade, whose three required hypotheses are written out — that the contact face
separates distinct contact complexes, that the candidate map carries the contact face to the
embedding face exactly, and that the candidate map is injective — with a falsifier that can fire.

[open] One finding that the plan's wording did not anticipate.
[EPISTEMIC_GRADES](../canon/EPISTEMIC_GRADES.md) declares **no ordering among its eleven truth-status
grades**, so "the meet of the grade" has no canonical meaning. `composeGrade` therefore does not rank
them: it reads each grade's declared `SupportLevel` — a receiver face of the grade, stated as a
declared reading and not as canon — and returns the weaker, refusing `counterexample` and
`historical` outright because a refutation is not a link and preserved provenance does not govern
construction. That reading is symmetric, idempotent and associative (`composeGrade_comm`,
`composeGrade_self`, `composeGrade_assoc`) and never claims more support than either link
(`composeGrade_support_le`). If a canonical grade order is ever declared, this reading is the single
place to replace.

[established-bounded; formal-checked; implemented-exact] **C8 — The Iwasawa tower — is returned.**
The paired owners are
[`Foundation/IwasawaTower.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/IwasawaTower.lean)
and [`iwasawa_tower.rs`](../../crates/holonic-engine/src/iwasawa_tower.rs), each citing the other by
declaration. The blocker is discharged in both halves.
`theCyclotomicPolynomialIsIrreducibleOverTheCoprimeLevel` proves that for coprime `m` and `n` the
`n`-th cyclotomic polynomial **is** irreducible over `Q(zeta_m)`, by the tower law rather than a new
irreducibility argument — `IsCyclotomicExtension.finrank` twice over `Q` with `Nat.totient_mul`
gives `[Q(zeta_mn) : Q(zeta_m)] = phi(n)`, the minimal polynomial of `zeta_n` over `Q(zeta_m)`
divides `cyclotomic n` and already carries that degree, and `eq_of_monic_of_dvd_of_natDegree_le`
closes it; `theCoprimeIrreducibilityIsNotVacuous` instantiates the hypotheses on `Q ⊆ Q(zeta_m) ⊆
Q(zeta_m)(zeta_n)` so the statement is not vacuous. `NormRelation`'s
`TheRelativeOrbitFillsTheCoprimeLevel` is then proved outright as
`theRelativeOrbitFillsTheCoprimeLevel`, and that file's own paragraph is corrected in place.

[open] **Two findings that change this item's own route.** First, the `Prop` `NormRelation` left
open does **not** need the relative irreducibility this document named as its blocker: `Q(zeta_m,
zeta_l)` is already a cyclotomic extension of level `m l` over `Q`, where
`cyclotomic.irreducible_rat` applies with no relative statement, and the required automorphism is
the unit of `(Z/ml)^x` that the Chinese remainder theorem builds from `1 mod m` and `a mod l`. The
relative irreducibility is proved anyway because the Euler system's horizontal composition wants the
sharper object. Second, that irreducibility is **not** available to the vertical tower and cannot
be: the layers of the `Z_p`-tower are `Q(zeta_{p^{k+1}})/Q(zeta_{p^k})`, totally ramified of degree
`p`, and `theRamifiedLayerCyclotomicIsReducible` proves `cyclotomic (p^(k+1))` is *reducible* over
`Q(zeta_{p^k})` for every `(p, k) != (2, 1)` with `k >= 1`. The vertical layer degree is
`thePPowerLayerHasDegreeP`, which needs neither coprimality nor irreducibility over the base. The
relative-irreducibility step belongs to the horizontal Euler-system direction; the tower's own step
is the degree.

[proved-derived; formal-checked] **`Gamma` is not rebuilt and an Iwasawa module is a `Tower`.**
`gammaSectionEquiv` is `ContinuingTower.padicSectionEquiv` cited, not a second inverse limit.
`Lambda` is `PowerSeries Z_[p]` in the difference coordinate `T = gamma - 1`, and `omegaPoly p n =
(1 + T)^(p^n) - 1` is built as a polynomial so its shape is theorems rather than description:
`omegaPoly_monic`, `omegaPoly_natDegree = p^n`, `omegaPoly_isDistinguished` (constant term zero,
every strictly lower coefficient divisible by `p`, through `Nat.Prime.dvd_choose_pow`),
`omegaPoly_dvd_succ` and `omega_dvd_of_le` for the divisibility chain, and `omegaQuotient_finrank :
finrank Z_[p] (Z_p[T]/(omega_n)) = p^n` through `AdjoinRoot.powerBasis'`. `omegaGroupRingEquiv`
proves `Z_p[T]/(omega_n) ~ Z_p[gamma]/(gamma^{p^n} - 1)` as `Z_p`-algebras through the substitution
`gamma = 1 + T` and its inverse, so the finite level **is** the group ring of `Gamma/Gamma_n ~
Z/p^n`; that is the sharpest honest form of `Lambda/omega_n ~ Z_p[Z/p^n]` here, and the power-series
form of the same quotient is Weierstrass division, cited and not proved. `quotientTower` makes
**any** antitone filtration of a module a `Tower` in C1's sense,
`quotientTowerSection_injective_iff` proves the section map is injective **exactly** when the
filtration is separated, and completeness is carried as the hypothesis `QuotientTowerComplete`
rather than asserted; `omegaTower` is the instance at `N n = omega_n M`.

[proved-derived; formal-checked] **The control residuals are retained, not demanded to vanish.**
`SelmerTowerData` lifts `Millennium/SelmerCalculus.lean`'s `selmer` levelwise at exactly that file's
level of abstraction — abstract additive groups with an abstract receiver family, no Galois
cohomology of an elliptic curve constructed and none claimed — with restriction up the tower,
corestriction down it and `cores_res` the degree law; the `Tower` is built from corestriction,
because that is the map typed finer-to-coarser. `ControlData` carries the control map into the
declared `Gamma_n`-invariants together with its `kernel` and `cokernel`, `ControlData.transition`
presents it as a C4 `Transition` whose retained residual **is** the control kernel
(`transitionOfHom`), `cokernel_subsingleton_iff` makes the retained cokernel load-bearing, and
`control_bijective_iff_residuals` proves the control map is an isomorphism onto the invariants
exactly when both residuals vanish. Neither is assumed: `theControlKernelAndCokernelAreBothRetained`
exhibits a family where the kernel is nonzero and the invariants contain a class the level does not
reach.

[counterexample; formal-checked] **The characteristic face is conditional, and blind above
codimension one.** `StructureData` is a hypothesis structure carrying the elementary module and the
pseudo-isomorphism with its two finite residuals; there is no `axiom` and no `sorry` in the file,
and the counterexamples are **unconditional** because they construct the datum rather than assume
it. `theCharacteristicFaceDoesNotDetermineTheModule` gives `Lambda/(T^2)` against `Lambda/(T) +
Lambda/(T)`: the same face `(T^2)`, and no isomorphism, because `T` annihilates the second and not
the first — the same separation `ContinuingTower.theOrderFaceDoesNotDetermineTheModule` makes for
`Z/4` against `Z/2 + Z/2`, now over `Lambda`. `thePseudoNullResidueIsInvisibleToTheFace` gives a
nonzero finite module annihilated by both `p` and `T` whose characteristic face is the unit ideal.
`WeierstrassData` carries the distinguished factorization as data with `omegaWeierstrassData` a
constructed instance and `weierstrassData_isEmpty_at_zero` a constructed non-instance; the growth
law `|M/omega_n M| = p^(mu p^n + lambda n + nu)` is `TheGrowthLaw`, stated as an open `Prop` with
finite coinvariants, an eventual starting level and integer `nu`. The finite-coinvariant
hypothesis is essential: `Lambda/(T)` is the native refusal control. The general classical
form uses `omega_n/omega_n0` relatively prime to the characteristic ideal; see
[Sharifi, Theorem 2.4.7](https://www.math.ucla.edu/~sharifi/notes/iwasawa-ch02.html), alongside
Iwasawa (1959) and Washington Thm 13.13. These are growth exponents; no instance of this global
law is proved here. `TheMainConjecture` is the open `Prop` `char_Lambda(X) = (L_p)`:
receiver-exactness, the equality of two codimension-one faces, and
`theMainConjectureIsNotSourceIdentity` proves that is not source identity by exhibiting one `L_p`
satisfying it for two non-isomorphic modules. No proof of the main conjecture is claimed anywhere.

[established-bounded; implemented-exact] **The Rust owner is the finite computable shadow, and it
measured two things the plan did not anticipate.** `iwasawa_tower.rs` computes `omega_n` as exact
`BigInt` binomials, verifies `omega_n | omega_(n+1)` by exact polynomial division, builds the
relation matrix of `M/omega_n M` over the basis `1, T, ..., T^(p^n - 1)` and reads the finite
abelian group off `rebase_invariants::smith_normal_form` — it founds no second Smith normal form and
no second tower vocabulary, since `IwasawaTower` is an instance of `continuing_tower::Tower` and
`OmegaRestriction` an instance of `continuing_tower::Transition` whose residual is the exact
quotient. 47 tests pass; there is no `f32`, `f64` or float literal in the module, which one of the
tests checks against the file's own text, and every entry point whose work is sized by a caller's
declaration refuses above a named bound before it allocates — the relation matrix's `(k p^n) x p^n`
area, the ring degree, the ring power and the growth fit's base level, each with a negative test
that fires it.

First finding: at `p = 3` the counterexample pair `M1 = Lambda/(f^2)` against `M2 = Lambda/(f) +
Lambda/(f)` with `f = T - p` has **equal order and different type at every level** — `n = 0`:
`Z/3^2` against `Z/3 + Z/3`, both of order `3^2`; `n = 1`: `Z/3 + Z/3^3` against `Z/3^2 + Z/3^2`,
both `3^4`; `n = 2`: `Z/3^2 + Z/3^4` against `Z/3^3 + Z/3^3`, both `3^6`. The measured `M1` type is
`[n, n+2]` and **not** the cyclic `Z/p^(2(n+1))` a guess would give, because `d_1 = gcd(omega_n(p),
omega_n'(p))` with `v_p(omega_n(p)) = n+1` and `v_p(omega_n'(p)) = n`. `Lambda/(p, T)` returns order
`p` at every level against a unit characteristic face. Second finding: the `n_0` of the cited growth
theorem is not decoration. The measured exponents at `p = 3` are `T - p: (mu, lambda, nu) = (0, 1,
1)`, `p: (1, 0, 0)`, `p^2: (2, 0, 0)`, `(T-p)(T-p^2): (0, 2, 3)`, `(p, T): (0, 0, 1)`, each solved
exactly over three consecutive levels and **verified against a fourth**; but at `p = 2`, `f = T - 2`
the measured `e = [1, 3, 4, 5, 6]` admits no admissible fit from base level `0` — the exact solution
there is `mu = -1` — and only from base level `1` does it return `(0, 1, 2)`. The owner also
**reports** the prime-to-`p` part of each invariant factor rather than refusing it (at `p = 3`, `n =
1`, `f = T - 3` the integral factor is `63 = 3^2 * 7`), because a refusal would reject the flagship
example at every level; the typed refusal is kept for the case that is genuinely not a finite
`Z_p`-module.

## What the carrier must not become

[definition] The tower is not a scheduler, a census or a second engine. A characteristic face, a
spectrum, a score or a digest is a receiver reading and never the identity of its source. Equal
faces do not establish equal sources; a richer receiver may reopen any collapse the carrier
admitted. Horizontal families that vary the object and vertical towers that refine the environment
around one object are independently typed axes and are never both called scale.

## Consumers

[definition] The receiver atlas is specified in
[THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT](THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md);
the environment-indexed physical instance in
[THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER](THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md);
the device realization in
[THE_EXACT_DEVICE_LAW_IS_CONSTRUCTED](THE_EXACT_DEVICE_LAW_IS_CONSTRUCTED.md). Athena consumes the
carrier through the existing native specification; this document adds no milestone to that order.
