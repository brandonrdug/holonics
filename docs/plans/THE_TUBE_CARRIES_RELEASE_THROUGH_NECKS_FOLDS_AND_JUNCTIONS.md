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

[definition] **T3 — Release over an edited artifact family.** Compose `receiver_release`,
`continuing_tube` and `physical_occurrence::PluralFibre` into the generation law above. The
draft–observe–revise cycle is a **declared circuit**: a functorial tube has no holonomy, so the
cycle on an embedding of interlinked tori is a circuit with a cocycle defect. "The intentions
cancel" is the circuit's holonomy being the identity at the receiver; a revision loop is a
nontrivial defect with no receiver change, and the periplus `P = RF` with residual `(P − I)x` is its
reading. The typed disposition is the existing release return; no `NONE` candidate competes under a
normalization.

[definition] **T4 — Knot friction and edit torque.** An artifact's kept receivers define a
constraint complex. `ker J_keep` is the free edits, an empty compensating family is an obstructed
edit, self-stress support is entanglement, `J* r` is the edit torque, and the rethreading work
`W_knot(g | A) = inf ‖δ‖` over compensations preserving the kept faces is a
`presentation_cost::CostReceipt`. This is `rigidity_receiver` applied to an artifact; it founds no
second Jacobian.

[definition] **T5 — The two-axis horizon.** `receiver_release`'s horizon is longitudinal only.
Extend it to the transverse axis, so that distance into the horizon is distance in the tower's index
in either direction: zooming from orbit to an organism is as far into the horizon as looking out to
the stars. The observer-relative cocycle defect as a function of index distance is the curvature
reading — squares between nearby grains commute and read as a sharp lattice, circuits reaching far
in grain show defect and read as curved, and which is which depends on the observer's grain. The
measured non-commutation of the atom-to-residue square is its first real instance. Tubes across
ranks that no single grain exhibits are `Wormhole`s or passages with a retained residual.

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
choices are stated once, in [THE_ROADMAP](THE_ROADMAP.md#position-of-the-five-contracts). T1 and T2
are returned and every later item states its results on `RelationLadder`'s rungs. T3 goes with T5,
since release over a family needs the two-axis horizon; T4 with T7, which share the rigidity owner;
T6 with T8, which share the pole and higher-difference owners.
