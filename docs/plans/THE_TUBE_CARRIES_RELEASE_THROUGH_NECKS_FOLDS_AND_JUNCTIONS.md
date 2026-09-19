# The tube carries release through necks, folds and junctions

[definition] This is a construction contract subordinate to [THE_ROADMAP](THE_ROADMAP.md). It
extends the [shared carrier](THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md) and its
[receiver atlas](THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md) from a static object and its
readings to **generalized transport**: when a tube conducts, why, what is invariant at the places
where it pinches, folds or joins, and what relation a later occurrence bears to an earlier one. It
adds no milestone. Each item is discharged inside the increment that consumes it, composes the
owners named beside it, and founds a new owner only for the concrete absent object it names.

## The governing statements

[project-postulate] Brandon, September 18: prediction is figuring out **when tubes will transport
and why**. The same holds for neural data, where the axon network and its modulation organize the
macroscopic picture, and for any navigation — a Rubik's cube, a chess game, an observer on Earth
reading the stars and planning travel, where the map dictates the plan. Tubes run over time; towers
and lattices are what one instantaneous frame shows; which of these is seen depends on the
observer's grain. The problem is generalized transport intelligence.

[project-postulate] **Identity belongs to an occurrence. Persistence belongs to lineage. Sameness
belongs to a receiver. Potential belongs to a family of future interactions. Memory belongs to
standing.** Nothing has to survive for two occurrences to be literally identical, because if
anything has changed — time, place, environment, observer relation, internal state — they are not
the same occurrence. `4` and `2^2` differ in `Expression` and agree under `eval`; the equality
belongs to the scalar receiver and does not ascend to identify the formulations. A later occurrence
is not the earlier one; the relationship between them is the object of study.

[definition] Generation is a tube whose cross-section changes. With `T_g` a swing, edit or
transport and `C_k` a newly admitted constraint,

```text
F_{k+1} = T_{g_k}(F_k) ∩ C_k
```

is longitudinal transport followed by transverse restriction. The cross-section may shrink to a
closed neck, a pinhole, or widen again. **Release** is the station at which the section has
collapsed to a point at the receiver's grain while remaining plural inside:
`∀ a a' ∈ F_k, π_B(a) ~ π_B(a')`. That is `receiver_release`'s width-zero condition, and the
lawful returns other than release are the ones that owner already types.

## What is already owned

[established-bounded; formal-checked; implemented-exact] The two-axis object is
[`Transport/ContinuingTube.lean`](../../formal/elementary-holonics/ElementaryHolonics/Transport/ContinuingTube.lean)
and [`continuing_tube.rs`](../../crates/holonic-engine/src/continuing_tube.rs): longitudinal
`ClockedSpan` from `Transport/WorldTube.lean`, transverse `Tower`, the commuting square as
`Migration.naturality`, `Wormhole`, circuit holonomy on declared circuits, and the p-adic tube whose
end is `Z_p`. Width, release, `Ask` and the coarser release are
[`receiver_release`](../../crates/holonic-engine/src/receiver_release.rs). Exact Laurent data at a
pole, half-plane counts and the resolvent are [`causal_chord`](../../crates/holonic-engine/src/causal_chord.rs);
the constraint Jacobian, its motions and self-stress are
[`rigidity_receiver`](../../crates/holonic-engine/src/rigidity_receiver.rs); exact linking is
[`topological_receiver`](../../crates/holonic-engine/src/topological_receiver.rs); growth exponents
at a pinch are [`iwasawa_tower`](../../crates/holonic-engine/src/iwasawa_tower.rs).

[established-bounded; formal-checked] The relation vocabulary is largely owned and unjoined.
`Foundation/Lineage.lean` owns the addressed passage, its fibre and
`theSameRelationCanHideDifferentOccurrencePopulations`. `Foundation/CausalRelevance.lean` owns
future agreement under admitted generators and receivers and proves it the greatest stable present
agreement (`futureAgreement_is_greatest_stable`), with a separator returned on inequality.
`Foundation/ReceiverHistoryCompression.lean` owns the quotient through which every admitted future
observation factors. `Transport/ChangingReceiver.lean` owns a receiver that changes while its source
does not. `Foundation/Bridge.lean` owns a strength order on eight statuses with counterexamples.
The single typed scale that places these together with its implications and non-implications proved
is `Foundation/RelationLadder.lean` / `relation_ladder.rs`, returned as T1 below.

[established-bounded; source-inspected] Junctions are owned in several places:
[the junction is a half-twist](../../research/records/2026-08-16_THE_JUNCTION_IS_A_HALF_TWIST_AND_A_MODULUS_IS_WHAT_A_DECLARED_QUOTIENT_RETAINS.md)
(Möbius shorts: two crosscaps, `chi = -1`, one boundary), `contact_gluing::OrientationReading`,
`gluing.rs`, `HingeGluing::Reversing`, `Millennium/{Gluing,Seam,RealizerJoints}.lean`,
`JointReceiverDescent`, and the operative field junction under `native_ecology/`. Higher differences
are owned by `Foundation/HigherDifference{Transport,Annihilator,ScaleDescent}.lean`, and the
critical vorticity rate, stretching comb and finite-time files under `Millennium/NavierStokes*`.

## Intentions

[established-bounded; formal-checked; implemented-exact] **T1 — The relation ladder. Returned.**
Owners: [`Foundation/RelationLadder.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/RelationLadder.lean)
(namespace `Soma.Holonics.Foundation.RelationLadder`) and
[`relation_ladder.rs`](../../crates/holonic-engine/src/relation_ladder.rs) with
`relation_ladder/tests.rs`. One typed scale over the owners above, in the manner of `Bridge.lean`'s
status order: strict occurrence identity `x = y` within one situated type; continuation `x ⇝ y`
(`AddressedPassage.Fibre`); structure-preserving isomorphism `x ≅ y` (`SituationAuto`, which is
`Holon.Rebase` with the situation's generator square and receiver triangle as its ports); receiver
equivalence `x ~_ρ y` (`ReceiverEq`); equal potential `x ~_{G,R} y`, which **is**
`CausalRelevance.futureAgreement` and is named, not redefined; and tolerance `x ≈_{ρ,ε} y`, which is
`ReceiverRelease.width` on `{x, y}` inside a declared tolerance (`withinTolerance_of_width_le`).
`Rung.entails` is proved a genuine partial order and not total, `rungMeet` its total meet, and
`no_rung_below_identity_entails_identity` with `noRungBelowIdentityAscendsToIdentity` is the
headline in both its forms — the declared order and five constructed witnesses. Every failing
implication carries a construction: `receiverEqualityWithoutEqualPotential` (the three-step example,
cited), `equalPotentialWithoutIsomorphism`, `isomorphismWithoutIdentity`,
`continuationWithoutAnyEqualFace` (`translationPassage`, cited),
`lossyContinuationIsNotAnIsomorphism`, `toleranceIsNotTransitive`. `equalPotentialAntitone` proves
that enlarging `(G, R)` refines the class and `separatorRefutesEqualPotential` that one `(w, ρ)`
refutes it. Each of the 31 audited declarations depends only on `propext`, `Classical.choice` and
`Quot.sound` — several on fewer and three on none — and none on `sorryAx`. The Rust owner is the executable equivalent: `Rung`, `rung_meet`,
`Situation::declare`, `classify`, `Separator`, `PotentialVerdict`, `ContinuationVerdict`, with 42
tests and exact `BigUint`/`BigRational` throughout. `Expression` against `eval` is the first worked
instance and two enactments of one song — a family of admissible enactments and transformations
under a musical receiver, separated by a richer one — is the second.

[established-bounded] Four findings from building it, each changing the item as the paragraph above
first stated it.
**(1) The rungs are relative to three different things, so they are not one linear scale.** Rung 1
is absolute; rungs 3–6 are relative to the declared `(G, R)`; rung 2 is relative to a declared
*lineage* and is therefore incomparable with rungs 4, 5 and 6 (`entails_is_not_total`,
`equalPotentialWithoutAGeneratorContinuation`). The order needs a seventh bottom rung,
`noRelation`, for the meet to be total, and the Rust `Classification` reports the continuation
beside the identity chain rather than inside it. **(2) "Isomorphism implies equal potential" is only
true with the equivariance carried inside the isomorphism, and each half is separately necessary**:
`receiverEquivarianceIsNecessary` drops the receiver triangle and `generatorEquivarianceIsNecessary`
drops the generator square, each exhibiting a bijection carrying `x` to `y` whose potentials differ.
**(3) Which rung holds for `4` and `2^2` is a fact about the declared generator family, not about
the pair**: under a family that only post-composes `eval` they have equal potential
(`postcomposeFamilyGivesEqualPotential`); one construction generator separates them
(`bumpExponentSeparatesThem`). **(4) A bounded search can never establish rung 5.**
`PotentialVerdict::NotSeparatedWithinBound` carries the bound it ran under and is never reported as
equal potential; the one sound executable route to rung 5 is an equivariance check over a probe the
caller declares to be the whole carrier, and a probe that is not stays a probe.

[established-bounded; formal-checked; implemented-exact] **T2 — Standing, memory and extinction.
Returned.** Owners:
[`Foundation/Standing.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/Standing.lean)
(namespace `Soma.Holonics.Foundation.Standing`) and
[`standing.rs`](../../crates/holonic-engine/src/standing.rs) with `standing/tests.rs`.

**Standing is the retained residue of passages, and it may be any quotient sufficient for the
admitted future.** `standingLaw_exists_iff_future_factors` proves that as an equivalence, which is the clause
AGENTS.md states — *"causal origin does not prescribe an event archive"* — as a theorem: a retention map
carries a lawful `StandingLaw` **exactly when** every admitted future observation factors through
it. `two_histories_leave_one_standing` exhibits two distinct presents reached by different
histories with one standing, and `one_present_face_two_standings_separated_later` two presents
agreeing at the present receiver whose standing a future receiver separates — the separator is
returned. `causalSignature` **is** T1's `RelationLadder.potential`
(`causalSignature_eq_potential`), and equal standing establishes rung 5
(`retain_eq_establishes_equalPotential`); nothing here founds a second quotient or a second scale.

**Memory is a generator.** `MemoryLaw.remember` returns a `TimedFace` at the present time, whose
time is part of the *type*, so `the_remembered_face_is_a_new_occurrence` is a statement the typing
makes rather than a convention; `receiver_agreement_after_the_passage_is_not_recovery` shows that
the passage and a receiver are all that relate the two, and that agreement at that receiver leaves
the carried values different. The same standing under two contexts returns two faces; the same
original under two later standings returns two reconstructions. The **fidelity law** is
`faithfulAt_iff_receiver_factors_through_standing`, which is `receiverTransformer_exists_iff` at
the retention map, cited not rebuilt. Its counterexample,
`the_unretained_receiver_is_reconstructed_confidently_and_wrongly`, is the honest formal content of
*"it cannot confabulate without origin, but it can be wrong"*: the retained face is exactly right,
the unretained one is returned **definitely** and is exactly wrong, and the constructed
`ReceiverInsufficiency` is why no reconstruction could have done better.

**The receiver keeps changing after the source stops.** The aperture chain has zero
`ChangingReceiver.defect` at every pair of steps; with `M` fixed its available face changes at
every step; the compatible fibre is antitone; no finite step makes it a singleton; the
intersection is `{M}` only because this chain separates, and
`a_non_separating_chain_never_reaches_a_singleton` shows one unread coordinate keeps it plural
forever. `apertureInsufficiency` and `no_transformer_from_the_coarser_aperture` are the separator
owners cited: a later separation is new content, not a reading of the earlier face.

**Effective extinction** is `Extinct`, and `extinct_iff_release_width_inside_tolerance` proves it
*is* `ReceiverRelease.Releasable` on the two-point family `{T_w x, T_w 0}` — `width_pair` is the
only new lemma and it is proved from that owner's own `width_le_of_bounds` and `abs_sub_le_width`.
It is monotone in the tolerance, the receiver family and the generator family, it is T1's rung 6
after every admitted history, and at `ε = 0` it coincides with rung 5
(`extinct_at_zero_iff_equalPotential`). `lawful_silence_is_extinction_at_the_outward_receiver`
reads `WorldTube.IsLawfulSilence` in this vocabulary: a nonzero section extinct at the outward
receiver is *dead to this receiver, alive inside*. The exact instance is a damped linear wave
`(a, e, m)` with `a ↦ a/2`, `e ↦ e/4`, `m ↦ m + e/4`: `e_t = a_t²` is proved, at horizon 3 the
wave chart is extinct at tolerance `1/8`, the medium reads exactly `21/64` at the **same**
tolerance and `the_fossil_is_durable` shows it never falls below that again while staying strictly
below `1/3`, and `the_energy_that_left_the_wave_is_accounted_for` closes the ledger exactly in
medium plus dissipation. In the exact `3-4-5` rational rotation the declared quadratic energy is
invariant along every word, so `no_horizon_releases_the_energy_receiver` and
`nothing_nonzero_is_extinct_at_zero_tolerance`: the difference is redistributed between the
coordinates and never leaves. Each of the 42 audited declarations depends only on `propext`,
`Classical.choice` and `Quot.sound` — five on none — and none on `sorryAx`. The Rust owner is the
executable equivalent with 37 tests, exact `BigRational` throughout and no float anywhere.

[established-bounded] Four findings from building it, each changing the item as the paragraph above
first stated it. **(1) Taken literally over every word, `Extinct` is never satisfied by a decaying
wave read from its origin**, because the supremum sits at the empty word. The object that carries
the intended meaning is extinction *of the present occurrence*, `Extinct(T^h x | 0)`: the horizon
belongs inside the perturbation, not inside the quantifier. Every fossil result is stated that way.
**(2) A bounded word search can only refute extinction; affirming it needs a certificate.** This is
T1's finding (4) again at a different rung. `ExtinctionVerdict` therefore has three values, and the
sound executable route to `Extinct` is a **checked** `ContractionCertificate`: a declared coordinate
chart proved invariant under every generator, an exact rational factor `λ ≤ 1` bounding every chart
row, and an exact gain for each reading, which together bound every word at once. A receiver that
reads outside the certified chart does not get an extinction verdict; the fall-through names it.
**(3) "Extinct at `(R, ε)` and separated at a richer `(R', ε')`" holds at the *same* `ε`.** The
plan allowed a wider tolerance and the exact instance does not need one — the enrichment is
entirely in the receiver family, which is the sharper statement and the one now proved. **(4) The
declared quadratic energy must be carried as its own coordinate for the system to stay exactly
linear and the ledger to be a theorem rather than a definition.** `e` quarters linearly because `a`
halves; `e_t = a_t²` is then proved by induction rather than assumed; and the medium/dissipation
split closes exactly over the rationals. A linear system plus a quadratic form does not by itself
give an exact rational energy ledger.

[established-bounded; formal-checked; implemented-exact] **T3 — Release over an edited artifact
family. Returned.** Owners:
[`Transport/ArtifactRelease.lean`](../../formal/elementary-holonics/ElementaryHolonics/Transport/ArtifactRelease.lean)
(namespace `Soma.Holonics.Transport.ArtifactRelease`) and
[`artifact_release.rs`](../../crates/holonic-engine/src/artifact_release.rs) with
`artifact_release/tests.rs`.

**The edited family is literally a tube.** `regionTower` / `RegionTower` is the transverse ladder —
the face at a region is the assignment on it and `restrict` **is** `π_B` — and `rotationTube` /
`RevisionCircuit` is the longitudinal axis. `F_{k+1} = T_{g_k}(F_k) ∩ C_k` is `step` (single-valued)
and `stepMulti` (a swing with sub-swings), with `stepMulti_singleton` identifying the first as the
second's one-branch case. The visible draft is one member and never the state. **The section shrinks
and widens:** `restriction_never_widens` is `receiver_release`'s `width_mono` at the constraint,
cited; `width_is_not_monotone_along_edits` is the other half by instance — the name swing carries one
artifact to two admitted ones and the name region's width goes from `0` to `1`. Release is
`ReceiverRelease.width` at a region (`releasable_iff_every_coordinate_width_is_zero`), and the
executable `ArtifactFamily::region_width` **is** `width_enumerated` at a `RegionReading`. T5's
two-axis `Horizon` is adopted for the transverse coordinate: `indexDistance` /
`ArtifactFamily::index_distance` is a region's distance through the ladder, it is the `k` a horizon
must declare, `region_width_at` computes the diameter with T5's own `width_over_readings`, and a
horizon declaring another `k` is refused by name.

**The revision cycle is a declared circuit.** `the_rotation_tube_carries_no_holonomy` cites
`tube_circuit_has_no_defect` at the rotation tube, so draft–observe–revise is a *declared*
`ChartwiseMigration` of the region tower into itself; "the intentions cancel" is
`check_circuit_holonomy` returning `HolonomyVerdict::Identity` at the declared receivers and nothing
weaker. `CircuitOutcome` types the three outcomes — **progress** (the receiver face changed, rung 2),
**neutral rechart** (the artifact differs and the declared receivers do not see it, rung 4) and
**revision loop** (`StopReplaying{route_class, residual}`, needing the returned visible face, a
nonzero periplus residual `(P − I)x` *and* a route class repeated inside a declared bound) — beside
`NoDefectWithinBound`, which affirms nothing:
`no_defect_on_a_declared_face_is_not_cancellation` exhibits one circuit returning a declared face and
moving an undeclared one. The typed disposition composes `ReleaseReturn` whole and adds only
`Reframe` (a `RequiredChartChange` returned as a migration requirement) and `Refuse` (a
`CausalObstruction`: an empty preimage fibre or an obstructed transport); `dispositionOf` is a
function of the family and the receivers, and `no_candidate_carries_the_disposition` exhibits one
artifact in two families whose dispositions differ, so no member of the candidate set carries it and
no `NONE` competes under a normalization. The two media are typed differently with no coercion:
`EditableDraft` revises any position, `IrrevocableUtterance` has no operation that changes its
committed boundary, and `no_sequence_of_corrections_retracts` is *speech cannot retract, only
correct* as a theorem. **Tori:** `windingCircuit` rotates two independent regions by the exact
rational angles `1/3` and `1/4` of a turn inside `ZMod 12`; the two circuits commute, compose to the
joint one, and `(3, 0) ≠ (0, 0)` is a nontrivial winding whose visible face returns — the phases are
the finite `Z/3 × Z/4` exactly. The entangled pair does **not** span a torus: the commutator of the
position-0 rotation and the shear is exactly the translation `y ↦ y − 1`, a lawful declared circuit
with nontrivial holonomy. That the artifact is *embedded on interlinked tori* is graded
`interpretation`; what is proved is finite and exact. Each of the 46 audited Lean declarations
depends only on `propext`, `Classical.choice` and `Quot.sound` — four on none — and none on
`sorryAx`. The Rust owner is the executable equivalent with 82 tests, exact `u32` token codes,
`BigInt` windings, `BigUint` cardinalities and `BigRational` widths, and no float anywhere.

[established-bounded] Four findings from building it, each changing the item as the paragraph above
first stated it. **(1) Over a family, an edit supported off a released region cannot change its face
at all, so a reopening is always an *emptying*.** The plan wrote "a revision loop is a nontrivial
defect with no receiver change" as though a later edit elsewhere could rewrite a released face;
`an_edit_supported_off_a_released_region_cannot_change_its_face` proves it cannot, because
intersecting with a constraint only removes members and a transport that misses `B` commutes with
`π_B`. So `reopening_from_outside_is_an_emptying`: after such a step the family is empty or the face
stands, and `the_name_edit_empties_the_family` is the exact instance — the `Hermes` pivot leaves
`T_g(F) ∩ C = ∅` at the pronoun released as *it*. The resolution requires an edit supported **on**
the region (`the_correction_restores_the_family`), which is exactly the correction, and for an
irrevocable medium that correction is an appended passage. **(2) "Independent versus entangled" is
three different relations and the plan's single sentence conflates them.** Commuting on the family
(`commutator_verdict`), chartwise locality (the two-axis square: `the_entangled_edit_is_not_chartwise`
proves an edit reading a position it does not write admits no `ChartwiseMigration`, and
`check_commuting_square` returns the defect at the region that cannot see its trigger) and constraint
entanglement are independent. Brandon's own pair is separated only by the third:
`commuting_does_not_separate_the_independent_from_the_entangled` shows `dog → cat` and `is → why` are
both positionwise substitutions at distinct slots, so both commute and both are chartwise — the
admitted role constraint is what keeps one family and empties the other. **(3) `PluralFibre` is not
composable here and is cited as the analogue instead.** `physical_occurrence::PluralFibre`'s carrier
is a population of `SituatedFamily` readings of **one** situated object over one distance aperture,
addressing the same contact pairs; its `partition` into unanimous / separating / open-carrying
contacts is exactly the shape of a region reading over an artifact family, but the family T3 needs is
a family of *artifacts*, not of readings of one occurrence. The composition the item actually needs
is `receiver_release::{CompatibleFamily, width_enumerated}`, which this owner uses. The concrete
absent object, if the analogy is ever to be one type, is a plural family generic in its coordinate
address; it is **not** founded here, because a fourth permanent public family for one task is the
drift the contract forbids. **(4) Release over a family needs the transverse axis as a second
coordinate, not a second width.** A region is a point of T5's index axis, and the pair `(h, k)` is a
product order: `the_two_horizon_coordinates_are_not_one_scale` records that `(2, 0)` and `(0, 2)` are
incomparable, so "how far into the horizon a release was taken" is a pair — how many edits, and how
coarse the receiver's region — and never a number.

[definition] **T4 — Knot friction and edit torque.** An artifact's kept receivers define a
constraint complex. `ker J_keep` is the free edits, an empty compensating family is an obstructed
edit, self-stress support is entanglement, `J* r` is the edit torque, and the rethreading work
`W_knot(g | A) = inf ‖δ‖` over compensations preserving the kept faces is a
`presentation_cost::CostReceipt`. This is `rigidity_receiver` applied to an artifact; it founds no
second Jacobian.

[established-bounded; formal-checked; implemented-exact] **T5 — The two-axis horizon. Returned.**
Owners, extended in place:
[`Foundation/ReceiverRelease.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverRelease.lean)
and [`receiver_release.rs`](../../crates/holonic-engine/src/receiver_release.rs) carry the horizon
itself; [`Transport/ContinuingTube.lean`](../../formal/elementary-holonics/ElementaryHolonics/Transport/ContinuingTube.lean)
and [`continuing_tube.rs`](../../crates/holonic-engine/src/continuing_tube.rs) carry what it measures
on a tube. No third carrier is founded.

**The observer is a station and a chart, and the horizon is a pair `(h, k)`.** `Horizon` is the two
coordinates with both ceilings checked at its constructor and its wire route; `ChainDistanceAtMost`
is one distance notion serving **both** axes, proved symmetric (`chainDistance_symm`), transitive
(`chainDistance_trans`) and unchanged by the order dual (`chainDistance_orderDual`) — that is the
exact sense in which refining `k` steps below the observer and coarsening `k` above it are one
notion. `twoAxisWidth` is `width` over what the horizon reaches, monotone in each coordinate through
`width_mono`, and at `k = 0` it **is** the width this repository already owned
(`twoAxisWidth_at_index_zero_is_the_longitudinal_width`), so every theorem of `w_R(h)` is that case
and none is restated. The executable side is `Observer`, `HorizonDeclaration`, `index_distance`,
`horizon_reach` and `two_axis_width`, with the reach's coarse entries `Determined` and its fine
entries `FibreMember`.

**Curvature is the defect as a function of distance, and it is a reading.** `defect_profile` asks
every square inside `(h, k)` through the owner's own `check_commuting_square` — one square at a time,
so the count is of squares and not of the first failure — and every declared circuit inside it
through `check_circuit_holonomy`. It returns the non-commuting count, every witness whole with both
routes' faces, the circuit holonomies, the exact maximal discrepancy the declared receiver reads
between two routes, and the `RelationLadder` rung the two routes stand on: `ReceiverEqual` when the
receiver identifies them, `WithinTolerance` inside a declared tolerance, `NoRelation` beyond it —
never `Identity`, which a defect excludes. `flat_near_curved_far` is an exact tube whose every square
commutes at every horizon, whose circuit inside longitudinal distance `1` returns the identity and
whose circuit reaching distance `2` does not;
`the_fine_observer_sees_at_one_step_what_the_coarse_one_sees_at_three` is the five-chart ladder whose
one failing square the finest observer reads at `k = 1` and an observer three covers below cannot
reach at `k = 2` and reads at `k = 3`; `visibleSquare_shift` is the exact relation between the two,
and it is the triangle inequality. `tube_profile_is_flat_at_every_horizon` is the functorial case:
a `Tube`'s profile is identically zero, so curvature belongs to declared circuits and declared
non-commuting families, as this contract already held. `receiver_defect_is_a_structural_defect` with
`ladderReceiverInsufficiency` is the reading clause: a receiver can only lose a defect, never invent
one, and a poorer one reads flat what a richer one separates.

**Passages across ranks are classified and routes are enumerated, never ranked.**
`classify_cross_rank` decides the three kinds exactly — a descending chain is the tube's own
composite (`descending_chain_is_the_tubes_own`), a chain that must rise is traversable exactly when
the residual is retained (`rising_step_needs_the_retained_residual`, which is
`ResidualMigration.traversability_is_the_residual` cited), and no chain at all is a `Wormhole`.
`plan_routes` enumerates every route inside a declared bound with its receipt: the residuals each
reopening must retain, the squares it crossed with whether each commuted, and the face it delivers.
Two routes to one address across a non-commuting square return two faces and the plan returns both;
`RouteSet::ranked_by` is a declared receiver applied to the returned structure afterwards, and the
library supplies none.

**The real instance.** `PresentationTube` composes `GrainReadingTube` over the three M5 RBX1
presentations: six stations `(presentation, reading)`, the atom↔residue grain tower as the transverse
section, the alpha-carbon selection as the within-presentation step and the target presentation's own
measured face as the between-presentation one. At `k = 0` neither the atom observer nor the residue
observer has a second chart inside its horizon, so **neither reads any square at all**; at `k = 1`
the atom observer reads `1` of `1` squares non-commuting and the residue observer `1` of `3`. The
two routes of that square are the coarse and the fine reading, and their exact discrepancies are
`239`, `307` and `550` over the three presentations — the measured `1,096` of `1,397` fine contacts
against the `301` the alpha-carbon receiver sees, as the profile's own content and not as a new
number. 39 tests on the tube owner and 35 on the release owner, exact `BigUint`/`Rat`/`BigInt`
throughout, no float anywhere. Every audited Lean declaration depends only on `propext`,
`Classical.choice` and `Quot.sound` — several on none — and none on `sorryAx`.

[established-bounded] Six findings from building it, each changing the item as the paragraph above
first stated it. **(1) The two coordinates are a product order and not one scale.** `(2, 0)` and
`(0, 2)` are incomparable horizons (`horizonWithin_is_not_total`), so "distance into the horizon" is
a pair; `Horizon` therefore carries no `Ord` and monotonicity is stated in the product order.
**(2) The index distance needs the cover relation, and it is relative to the declared aperture.**
Bare comparability makes every chart of a linearly ordered index one step away — atom would be
adjacent to component — so the ladder would have no length. The executable distance walks *covers*
inside the declared chart list, and adding an intermediate grain lengthens the chain through it. The
aperture is part of the reading and travels in the receipt. **(3) The symmetry is in the distance
and the asymmetry is in the reading, exactly.** A tower's only transport is `restrict` and it runs
one way: toward the coarse the observer reads one determined **face**, whose own width is zero at
every receiver, and toward the fine it reads the **fibre**, whose width is the fibre's diameter.
Both directions are far; they are far in dual ways, and that is the precise content of the plan's
symmetry clause. **(4) In the real instance the curvature is entirely on the grain axis.** The
within-presentation grain square fails and the between-presentation environment square commutes,
because the environment transport is constant in its source and a `GrainTower`'s coarse face *is*
the restriction of its atom face. **(5) `physical_occurrence::Passage` does not type-check as this
tube's longitudinal transport, and what it contributes is its law.** Its `Transition::apply` is
constant in the source's classes, and that constancy is exactly what the cross-presentation transport
implements; the face types differ (`OccurrenceFace` over a `physical_constraint_complex` against
`GrainFace` over `GrainPair`s), no adapter exists in this repository, and founding one would be a
second carrier for a law already available. **(6) A profile must distinguish "read and flat" from
"not read".** A square asked with no declared face at its finer chart compares nothing, and counting
it as commuting would manufacture flatness; `squares_with_no_declared_face` is its own count, and a
bounded route search returns `NoRouteWithinBound` or `MoreRoutesThanDeclared` — never "unreachable",
and never a truncated enumeration presented as complete.

[definition] **T6 — Neck invariants.** A neck is a station where the section's width tends to zero.
Its invariants as a point are already computed by separate owners and are not yet one reading: the
residue and Laurent data at a pole, the holonomy of a circuit around it, the branching count and
growth exponents at the pinch, the linking of the tubes that meet there, and the characteristic
face. A prime is a neck carrying its own p-adic tube. On the fluid side the analyticity-strip width
`δ(t)` of complex Euler is a pinching cross-section; vorticity-direction coherence is why most
candidate singularities are causally cut off before they complete; helicity is the linking of
vortex tubes and changes only at reconnection, a neck where topology changes. A whip is the same
law in one dimension: conserved flux through a shrinking section drives the speed up until the
medium's causal limit cuts it off as a shock. The contemporary, causally intersected blow-up is the
object, not the classical unbounded one.

[definition] **T7 — Folds, cuts and junctions under one law.** A fold is a reflection `R = 2P − I`
across a crease applied to one side; a bounce is that fold read in the trajectory; a collision is
the contact law between the layers the fold stacks. Unfolding at a tolerance is the fold catastrophe.
A fold preserves intrinsic curvature and homology and is reversible exactly when its side-bit
residual is retained, so `k` folds are the dyadic tube with `2^k` layers; a cut changes the complex
and is a passage that breaks bonds; a plastic crease is a residual dissipated. A crease pattern is a
hinge framework and is read by `rigidity_receiver`; the protein backbone is rigid origami of a
one-dimensional linkage with `(φ, ψ)` hinges, the Ramachandran region being the crease angles
collisions allow. A **junction law** is one typed object: the tangential part continuous, the normal
part jumping, the jump being the source that lives on the joint — Kirchhoff's node law as the kernel
of the boundary operator, the electromagnetic boundary conditions and Snell refraction,
Rankine–Hugoniot, the Israel junction conditions, Plateau's laws, Kawasaki at a vertex. Valence,
Euler characteristic contribution and an orientation bit complete it: the pair of pants and the
Möbius shorts both contribute `chi = −1` and differ in orientability. It is composed over the
existing gluing owners.

[definition] **T8 — The jet tower and compression as a staircase.** The jet ladder `J^0 ← J^1 ← …`
is a `Tower` whose restriction forgets the top derivative; every consistent jet sequence has a
smooth section, so gluing is plural and only analytic sections glue uniquely. An event's **order**
is the lowest derivative that jumps at the observer's grain, and it is grain-relative: a narrow bump
in the `n`th derivative reads one order lower at a coarser grain. Compression descends to the order
`k` at which the signal is sparse, stores the events and `k` boundary constants, and reopens by
`k`-fold integration — a `Transition` whose residual is the boundary jet, with a cost receipt.
`T = γ − 1` is the difference operator and Mahler's expansion makes `Λ = Z_p[[T]]` this staircase
p-adically. Join to `HigherDifference*`; exact over rationals by finite differences.

## Carried from the four returned plans

[definition] Biological: **B8** is returned as `design_selection` on `RelationLadder`'s equal
potential; **B9** evaluation discipline, **B10** cost cascade and receipts, and the physicochemical
receiver of B7 remain. Receivers: a per-eigenvalue refinement owner on `ExactHodgeSpectrum`, and
`MarkovTwoNSuffices`. Device: a second device ring of signed 128-bit words with the engine's carrier
refusal, a per-region operator family and a base-pointer registry; **D4** stays an intention.
Carrier: Weierstrass division for the power-series form of `Λ/(ω_n)`.

[established-bounded; measured] The shared-section realization of the field reaction and reflection
that the [construction state](../../CONSTRUCTION_STATE.md) names as active is the engine-side
consumer D3's migration map was written against. Its section reader agrees with its per-row reader
on the card; adopting the generated triple there is the next device increment.

## Order

[definition] The order of what remains here, the wave shape and the rules that settle recurring
choices are stated once, in [THE_ROADMAP](THE_ROADMAP.md#position-of-the-five-contracts). T1, T2 and T3
are returned and every later item states its results on `RelationLadder`'s rungs. T3 went with T5,
whose two-axis horizon it adopts for the region ladder; T4 with T7, which share the rigidity owner;
T6 with T8, which share the pole and higher-difference owners.
