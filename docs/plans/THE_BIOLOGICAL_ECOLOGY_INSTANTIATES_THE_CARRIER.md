# The biological ecology instantiates the carrier

[definition] This is a construction contract subordinate to [THE_ROADMAP](THE_ROADMAP.md). It
states the engineering intentions for the environment-indexed physical instance of the carrier
defined in [THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER](THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md),
read through the receivers of
[THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT](THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md).

## Why this instance

[project-postulate] Further protein/biology construction is deferred by Brandon's latest
post-Wave-10 request. This contract retains its scientific material and shared library obligations;
the live roadmap now prioritizes elementary Holonics and HNN/Athena. It does not schedule new
predictions, response runs or receiver tuning.

[historical] Protein structures were selected as a rich scientific application of the
[general embedding object](THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md#the-general-embedding-and-its-consuming-composition).
They bring sequence, spatial frames, contact incidence, spectral/topological response, environment
and atom/residue/domain grains into one demanding construction. Their complexity lets defects in
several shared operations become visible together. This is why Brandon selected them; it is not
an exclusivity theorem about which kinds of object can carry these relations.

[definition] The general object remains the continuing Holon with its interacting faces, material,
currents and receiving atlas. Protein-specific sequences and file formats are application charts.
The same contact, restriction, variation, response and encoding laws contribute to HNN/Athena
and other scientific applications wherever their hypotheses and units apply. Other applications
can also carry environments, physical receiving apparatus and testable grain relations.

[definition] The competition is a convenient external comparison surface. The scientific work
compares explicit constructions against structure data, independent calculations/predictors and,
when supplied, physical measurements. These establish their respective scopes: an exact identity,
a computational model comparison and an assay are different evidence about one application.
RNA, DNA/chromatin, viral, cancer and neurochemical examples below retain wider research intentions;
they are not an automatic queue of prerequisites for the general embedding or Athena.

## Current application return and its shared consumers

[established-bounded; source-inspected] B0–B10 supply intake, grains, occurrences, contact/constraint
families, passages, receiver analyses, design/evaluation interfaces and cost receipts. The M5
structures have exercised the shared library through actual all-atom/contact, modal, rigidity,
topological and physicochemical readings. The returned constructors do not alone close the whole
design application. The installed-predictor/design and later measured-RBX1 comparisons have
returned at their declared receiver scopes. The full receiver-family evaluation and
physicochemical interface-gluing obligations remain, with application continuation deferred;
generic mathematical improvements stay attached to their shared owners.

[open] The dynamic join consumes the same source configuration and environment through active
contact faces and material evolution. T4's exact constrained edit response and T7's junction
balance are available inputs; the
[contact-to-variation composition](THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md#the-general-embedding-and-its-consuming-composition)
specifies how relative motion, traction, dissipation and receiving differentials join them.
This physical instance supplies demanding tests for that reusable operation. Its input and
constitutive calibration must remain attached when the result is read through another receiver.

## The object

[definition] For an environment `eta`:

```text
B_eta(t) = ( Omega, K_eta(t), q(t), Theta_eta(t), a(t), j(t), R_eta, Gamma_eta, lineage )
```

an addressed occurrence population, a changing incidence complex, a configuration, an
environment-dependent constitutive law, a stored quantity with its oriented current, a receiver
family, a compatible continuation fibre and causal lineage. The field part satisfies a balance law
`d_t a + div j = r_eta(a,q)`; configuration evolves by `q' = F(q,a,u)`; and discrete events change
the topology or material itself, `(K,Theta)_{t+} = Phi_e((K,Theta)_{t-})`. A base pair forming, a
ligand binding, a channel opening, a mutation founding a clone and a receptor internalizing are all
instances of the last law. This hybrid of continuous transport and discrete incidence change is
more faithful than either a static graph or one monolithic differential equation.

[definition] Incompleteness here does not require infinitely many causal factors. A receiver whose
preimage contains exactly two sources is already incomplete. The fibre may be finite, infinite,
implicit or empty.

## What is already owned

[established-bounded; source-inspected] The exact geometric receiver is
[`physical_constraint_complex.rs`](../../crates/holonic-engine/src/physical_constraint_complex.rs):
`DistanceAperture::classify` classifies a contact from an exact squared-distance interval against
an aperture as inside, outside or open, with overlap remaining open rather than rounded into a
decision; `found`'s chain steps and `found_faces_over` found one- and two-cells only from admitted
incidence; `ConstraintFace::boundary` carries the alternating algebraic boundary;
`cross_presentation_fibre` returns the fibre and the shortest separator. It is genuinely
protein-agnostic.

[definition; implemented-exact] A complex carrying several founded families — a second aperture, a
second declared separation, a second component pair — is a **family of complexes** and not one
complex over the union of their contacts. `found_faces_over` therefore asks the 2-cell law of each
founding against *that founding's own* admitted contacts, and records each founding's 2-cell
population beside it in `family_faces`, readable with `PhysicalConstraintComplex::family_faces` and
`two_chain_boundary_of_family`. The 2-cell population is a set of vertex triples: a triple two
foundings both reach carries one cell, minted once, whose boundary is added once, so a second
founding on the same pair neither duplicates a 2-cell nor doubles a `two_chain_boundary`
coefficient. `contact_edges` remains the complex-wide 1-skeleton that
`physical_constraint_grading` grades a member over; that module replays the face law in
presentation order with its own duplicate-triple guard. `∂∘∂ = 0` is asserted after multi-founding,
on the whole two-chain and on each family's own. The `Deserialize` route is gated through a
`TryFrom` that re-checks structural coherence — ids in range, every face's edges standing, the
carried boundary equal to the one recomputed from the faces, `∂∘∂ = 0`, no vertex triple carrying
two faces, the per-family populations aligned — so a remounted complex is testimony that a coherent
complex of this shape was serialized. It is **not** testimony that each reading's class is the
class `DistanceAperture::classify` returns on the carried coordinates: only the two founders audit
that, and the material audit must be re-enacted from the presentation to be claimed again.
`within_component_pair_count` declares the domain `k ≥ 2`, the founders' own, and answers `None`
below it: the Lean family `withinComponentPairs n 0` carries the whole diagonal
(`withinComponentPairs_zero_contains_the_diagonal`), so at `k = 0` it is not a family of unordered
pairs and `C(n + 1, 2)` is not a pair count. `exact_value::ieee754::{decode_binary16_bits, decode_binary32_bits,
decode_binary64_bits}` decode binary16, binary32 and binary64 words to exact dyadics.
Exact rank, kernel, image and cokernel are at `exact_linear.rs:761,770,796,814`. Exact Pareto
non-domination is generic at `resident_section/geometry.rs:309`.

## Engineering intentions

[definition] **B0 — Grain restriction with a commuting receipt. Returned.** Intake in the example
driver selects alpha carbons at
[`m5/cif.rs::REPRESENTATIVE`](../../crates/holonic-life/examples/m5/cif.rs), so
no atom-grain face is founded there and the restriction is asserted by the act of selection rather
than constructed. The library owners are now
[`grain_tower.rs`](../../crates/holonic-engine/src/grain_tower.rs) and
[`Foundation/GrainRestriction.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/GrainRestriction.lean),
built on the carrier's `Tower` and `Transition`.

[established-bounded; implemented-exact; measured] Over the same 70,632 pairs at an equal 8 Å
aperture, coarse-inside implies fine-inside with zero exceptions, and 1,096 of 1,397 fine contacts —
78.45 per cent — are invisible to the coarse receiver. With coarse-only zero, fine-only is forced to
equal fine minus coarse per family, and the fixture asserts that identity so it cannot drift. The
open class does not transport: exactly one open reading at each grain, at different pairs, with no
pair open at both. One is coarse-open and fine-inside, the other coarse-outside and fine-open, so
refinement both decides and opens.

[established-bounded; measured] `ApertureRelation` carries the three lawful values with no default:
an inflated coarse aperture with its witness exhibited, declared independence, or native atom grain
refusing on disagreement. The equal-aperture relation is asserted to refuse. The inflation attained
on these three structures is 34.155 Å, 4.2694 times the fine aperture, and it is forced by a
predictor defect rather than by chemistry: five C-terminal residues of the Protenix predictions
carry a stray terminal oxygen, one of them 27.6 Å from its own alpha carbon, while the next-largest
grain radius is 7.31 Å and the designed structure has no outlier. Restricted to residues whose
measured radius is within the fine aperture, the requirement is 2.0898 times and retains 1,366 of
1,397 contacts. Both figures are properties of these three occurrences, not general constants. An
all-atom intake surfaces a predictor defect that an alpha-carbon intake structurally cannot see.

[proved-derived] The grain residual and the open class are two objects, not one. A residual is the
retained complement of `apply` and is a function of the source, with `reopen_apply` returning that
source exactly; an open reading belongs to the target face and is not a function of the source,
since two resolutions disagree on one presentation. Retaining a residual removes the loss; nothing
retained on the grain axis closes an open reading, which is closed only by a narrower interval or by
an exterior declaration that enlarges the source. They are two coordinates of one index — content
dropped along grain, content undecided along precision — and `restrict` has no component along
precision, which is the mechanism behind the measured non-transport of the open class.

[definition] **B1 — The graded-complex adapter. Returned.** `GradedCausalComplex::found_cell` at
`algebraic.rs:314` was reachable from no contact complex, so exact homology, the sheaf Hodge
Laplacian and the exact spectrum — all three of which already existed and worked — had no physical
consumer. The library owners are now
[`physical_constraint_grading.rs`](../../crates/holonic-engine/src/physical_constraint_grading.rs)
and
[`Foundation/AperturedGradedComplex.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/AperturedGradedComplex.lean).

[established-bounded; implemented-exact; formal-checked] The adapter does not return a complex. It
returns a *family*, `ConstraintComplexFamily`, indexed by the resolutions of the open set, of exact
cardinality `2^n` as a `BigUint`, with the open set itself retained — each open contact carrying its
exact interval, its aperture and its addressed pair. Two members are built eagerly because they
bound the family in the inclusion order of 1-cells: `refusing`, whose incidence is exactly the
presented complex's own, and `admitting`. Any other member is named by a declared `OpenResolution`
that must name every open contact exactly once and name nothing else; there is no default, no
majority rule and no fallthrough. `enumerate_family` takes an explicit bound and returns
`OpenFamilyTooWide` rather than exponentiating quietly, and an open set at least as wide as a
`usize` refuses before the shift is taken. `∂∘∂ = 0` holds for every member with no hypothesis on
the aperture, the interval or the resolution — `constraint_boundary_squared` and
`constraint_d_comp_d`, elaborated with no `sorryAx`.

[established-bounded; implemented-exact; formal-checked] The adapter reads **both** contact
population laws, because the contact law itself is one law. `ContactFamilyKind::Cross` is the
family of two distinct components; `ContactFamilyKind::WithinComponent` is the intra-chain family
of one component's own chain, the unordered pairs `i < j` whose positions differ by at least a
caller-declared sequence separation `k`, founded by
`PhysicalConstraintComplex::found_within_component_contact_family`. Its exact population is
`C(n − k + 1, 2)` (`withinComponentPairs_card`), it is disjoint from every cross family that
mentions the component (`withinPairs_disjoint_crossPairs`), and its `Open` readings are carried
into `ConstraintComplexFamily` exactly as a cross family's are. `k` has **no default** and below
`2` it is refused by name: separation one is the presented chain's own covalent step, which is a
`polygonal_edges` one-cell of every member whatever the aperture says. That covalent class is
`EdgeProvenance::Polygonal`, so an admitted intra-chain contact `(i, j)` closes the chain segment
between its endpoints into a `1`-cycle of `j − i + 1` one-cells in every member that admits it, and
the cycle module of that segment is free of rank one (`backboneContactCycle_is_cycle`,
`segment_cycles_are_multiples`). The only adjustment the diagonal needs is in the two-cell law: a
junction coinciding with its own chain step's endpoint founds no triangle and is skipped.

[established-bounded; measured] **The open class is not a nuisance at the topological receiver; it
changes the answer.** Over a presentation with two open contacts the four members return Betti
vectors `[2,1,0]`, `[1,1,0]`, `[1,1,0]` and `[1,2,0]` through Smith normal form over `BigInt`, with
Euler characteristic `1` for the refusing member and `−1` for the admitting one, checked against the
cell Euler characteristic and invariant under all four pivot rules. Resolving an open contact by a
default would therefore have changed the reported homology of the presentation. `dim ker Δ_k`, read
over `Q` by exact rank through `sheaf_diffusion`, agrees with those Betti numbers through a code
path that shares nothing with Smith normal form. The exactness survives at the spectrum: the
refusing member's grade-zero Hodge Laplacian is completely rational with eigenvalues `0², 1, 2, 3²,
4, 5`, while the admitting member's is not — six of its eight eigenvalues stay in an unresolved
polynomial factor that is retained rather than approximated.

[definition] **B2 — Library intake with all-atom retention. Returned, and the example driver is
migrated onto it.** Every CIF, npy, mount and mesh adapter lived under an example driver
([`m5/cif.rs`](../../crates/holonic-life/examples/m5/cif.rs)) or inside a test module
(`grain_tower/tests.rs::read_all_atoms`) and was reachable from no library; the constraint complex
had no library consumer. The duplicated example readers are now deleted: `m5/cif.rs` and
`m5/npy.rs` retain only the receiver's own alpha-carbon selection and sequence binding, and the M5
deed returns its recorded `contacts=70632, shared=40` and shortest separator unchanged through the
library path. The library owners are now
[`physical_intake.rs`](../../crates/holonic-engine/src/physical_intake.rs) with its `mmcif`, `numpy`
and `deflate` submodules, and
[`Foundation/ExteriorIntake.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/ExteriorIntake.lean).

[established-bounded; implemented-exact; measured] Intake retains every `_atom_site` row — atom and
residue labels, chain, element, alternate location, the three coordinate tokens, and the
`occupancy` and `B_iso_or_equiv` columns where a presentation carries them, with the format's `.`
and `?` cells read as absent — admits
`<f2`, `<f4` and `<f8` uncertainty words through the exact decoders
`exact_value::ieee754::decode_binary{16,32,64}_bits`, and reads a `.npz` container directly rather
than a pre-extracted
directory. The four M5 cross families reproduce through the library path exactly — 70,632 pairs,
fine-inside 1,397, coarse-inside 301, fine-only 1,096, coarse-only 0, per family 239 / 307 / 215 /
335, required coarse aperture squared `116656202097359145/10^14` — so that table now has two
independent readers agreeing rather than one reader asserted twice.

[definition] The coordinate discipline the library owns is **per token**: a written coordinate's
enclosure is its own last decimal place, and the scaled integer wire is a separately declared,
always-outward projection. Both prior readers derived one decimal count for a whole family and
re-expressed every token on it at parse time, so an atom's enclosure depended on how many digits an
unrelated atom elsewhere in the file was written with. `projection_contains_source` and
`widening_never_flips_a_decision` make the resident wire a safe coarsening with a stated law: it can
open a decided contact and can never reverse one.

[established-bounded; implemented-exact; formal-checked] An occurrence cannot be founded without its
environment index. `AddressedUncertainty::found` is the only constructor and takes the index by
value; in Lean the array's index type *is* the token population. An external predictor emits only
the uncertainty array — the Boltz-2 run at `.local/boltz-smoke/…/pae_test_model_0.npz` writes one
`<f4` member and nothing else — and it is refused with all ten absent environment arrays named at
once, then admitted once a caller declares the index with a stated ground that travels with it.

[definition] **B3 — Environment index and typed occurrences. Returned.** A prediction against one
target file must not silently become a claim about every biologically relevant form. The library
owners are [`physical_occurrence.rs`](../../crates/holonic-engine/src/physical_occurrence.rs) and
[`Foundation/PhysicalOccurrence.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean),
built on top of the presented `EnvironmentIndex` that B2 already refuses to found an occurrence
without.

[established-bounded; implemented-exact; formal-checked] The eight axes — species and homolog,
target conformation, oligomeric state, pH with its protonation assumption, membrane or soluble
context, cofactors and ligands, assay format, and intended and unintended partners — are a closed
list, and each is a typed `Coordinate` that is either declared **with a ground** or explicitly
undeclared **with a reason**. Both constructors refuse an empty string, neither they nor any
coordinate carrier has a `Default`, and `Environment::found` refuses unless every axis is present
exactly once with its value filed under the axis it belongs to. An `Occurrence` is a structure face
situated at one environment index: one constructor taking the environment by value, and a total
accessor. In Lean it is the dependent pair `Σ e, Face e`, so the environment is a projection and an
occurrence without one is not a well-typed value.

[proved-derived; formal-checked] The central law is that a reading taken at `e` is a claim at `e`
only. `compare_here` returns `EnvironmentsDiffer` carrying the complete disagreement set unless the
two claims sit at the same environment value. Carrying a claim from `e` to `e'` needs a supplied
`EnvironmentPassage`, whose `declare` refuses any divergent axis the declaration does not account
for, and which is a `continuing_tower::Transition` whose residual **is** the environment the claim
was read at; `check_reopen` returns `reopen(apply(x), residual(x)) = x` as a receipt and
`separating_residuals` exhibits the two environments still telling apart two claims the transport
merged. Environments are the *vertical* index: `EnvironmentTower` instantiates
`continuing_tower::Tower` on the refinement order of declared-axis sets, with `restrict_refl` and
`restrict_trans` checked over a declared aperture, and `EnvironmentRestriction` carrying the dropped
declarations and their grounds as its residual. Varying the object at one environment is the
separately typed `HorizontalFamily`; neither constructor admits the other's population, and only a
`VerticalFamily` can produce an environment-dependent status.

[definition] **A finding that sharpens the plan.** Agreement requires a declaration on both sides,
so two coordinates that are both undeclared do *not* agree: nothing licenses the claim that two runs
which recorded no pH were at the same pH. The consequence is that an environment does not agree with
itself at an undeclared axis, and `Environment::disagreement` against itself returns exactly the
undeclared axes. Comparison at one site is therefore identity of the environment *value*, not
coordinate-wise agreement; both relations are available and they are deliberately different, and a
passage across two environments that are silent on the same axis must still name that silence.

[established-bounded; measured] The three M5 RBX1 presentations are three occurrences at three
environment indices. The designed structure carries no uncertainty array at all, so its presented
index is declared with a stated ground, while the two Protenix runs read theirs from their own
`.npz`. Designed against free diverges in target conformation, assay format, pH and solvent context;
designed against the CUL1-bound prediction adds the oligomeric state. Comparing their 10,368
alpha-carbon pairs with no passage is the typed refusal naming exactly those axes; with a passage
that accounts for all four, the comparison returns 10,338 agreeing and 30 separating pairs, and the
environment the claim was read at comes back as the passage's own residual rather than being
dropped. Neither release records a pH or a solvent context anywhere, and those two axes are named as
undeclared rather than filled in.

[definition] **B4 — Contact status and dynamic families. Returned.** A contact edge is not a
boolean. Same owners as B3.

[established-bounded; implemented-exact; formal-checked] `ContactStatus` carries six states with six
different evidence requirements. `static_status` is the only function in the owner from a static
structure to a status: its image is exactly `{Formed, Excluded, Open}`, it attains all three through
the exact interval law, and the Lean owner shows it reaches none of the other three
(`static_law_reaches_exactly_three`). `Open` is derived from the exact interval contact law and
carries both the aperture and the interval, so nothing downstream must return to the complex to
re-decide it. **`KineticallyInaccessible` cannot be derived from a static structure and the owner
says so by type**: it carries an `ExteriorDeclaration` whose fields are private, whose `declare`
refuses an empty statement or an unnamed apparatus, and which does not derive `Deserialize` —
a remount would be a second constructor bypassing that check. `EnvironmentDependent` is the return
of `VerticalFamily::status_across` on one ordered pair read across occurrences at different
environment indices.

[definition] **The exclusion is a declared valence at one site**, chosen and stated here: a site of
declared valence `k` cannot carry more than `k` formed contacts at once, so `formed > k` is a
competition and `formed ≤ k` is not, on exact integer counts. Steric exclusion under the exact
distance law between two partners of the same site is a *different* exclusion with different
evidence, and this owner deliberately neither computes it nor blends it in. Open contenders at the
site are retained apart from the formed ones in `SiteOccupancy::open` and are never counted: an
undecided reading neither creates nor dissolves a competition.

[established-bounded; measured] Over the 10,368 alpha-carbon pairs of the binder against RBX1, the
three presentations agree `Formed` on 38, agree `Excluded` on 10,288, and read 42 differently. Those
42 are environment-dependent by derivation on real data, with each of the three occurrences placed
by the class it read there. Exactly one of the 42 has an undecided reading somewhere — the single
pair the designed presentation leaves `Open` at the 8 Å aperture — and the derivation places it
rather than resolving it.

[established-bounded; measured] **Directional uncertainty is retained per ordered pair and never
symmetrized**, and the released data says why. Of the free prediction's `<f2` array at extent 207,
21,094 of 21,321 unordered pairs carry two different cells; of the CUL1-bound array at extent 573,
163,345 of 163,878; and of the Boltz-2 `<f4` array at extent 330, **all** 54,285. On the founded
contact family itself, 10,314 of the 10,368 addressed pairs carry two different directional
readings. The owner exposes no mean, minimum, maximum or any other symmetric summary of a pair;
`DirectionalUncertainty::transposed` is an involution that exhibits the asymmetry, and the Lean
owner states what any symmetrizing function costs — it identifies two readings the predictor kept
apart (`symmetrization_merges_a_distinguishable_pair`).

[definition] **B5 — Plural fibres and separator sets. Returned.** Several predictors, seeds and
environments produce a population of faces over one candidate. Agreement narrows the fibre and does
not prove realization, and the return is an n-way fibre with the *complete* separator structure
rather than the single shortest witness `physical_constraint_complex::cross_presentation_fibre`
returns. The owners are
[`physical_occurrence/plural_fibre.rs`](../../crates/holonic-engine/src/physical_occurrence/plural_fibre.rs)
and the **B5** section of
[`Foundation/PhysicalOccurrence.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean).
They are B3/B4's owner extended, not a new one: the population is a population of `SituatedFamily`,
and `PluralFibre::from_vertical` and `from_horizontal` compose the two families that owner already
carries.

[established-bounded; implemented-exact; formal-checked] **The concretely absent type was the join
of the two indices.** `VerticalFamily` refuses two members at one environment; `HorizontalFamily`
refuses two members at two environments; the B5 population — two Protenix seeds at one environment
beside a designed structure at another — is admitted by neither, and `PluralFibre` is that join
restricted to one object at one aperture. The receiver is one contact family at one aperture, and a
member read against another aperture is refused by name, because separation at one aperture says
nothing at another. `separator_between` returns every contact at which two members read different
*decided* classes; `partition` sorts the addressed contacts into unanimous-formed,
unanimous-excluded, separating and open-carrying, and `is_a_partition` checks that the four are
disjoint and exhaust. The central law holds in both languages: unanimity gives
`R`-indistinguishability (`separatorSet_eq_nil_iff_indistinguishable`) and never equality of sources
(`agreement_does_not_prove_realization`, whose Rust face is the **uninhabited** `RealizationProof`,
so `UnanimityReceipt::realization_proof` is `None` by type); adding a member can only shrink or
preserve the unanimous set (`unanimous_antitone`, whose nonemptiness hypothesis is why a fibre of
fewer than two faces is refused); and one separating contact refutes a proposed merge
(`one_separating_contact_refutes_the_merge`). `#print axioms` on the B5 theorems returns only
`propext` and `Quot.sound`, with no `sorryAx`.

[established-bounded; implemented-exact] **The minimal separating sets are exact under a declared
bound.** A receiver that distinguishes every member is exactly a hitting set of the pairwise
separator sets, and the smallest one is a minimum hitting set — NP-hard in general, so
`minimal_separating_sets` takes a `HittingSetBound` with a stated ground and bounds its whole search
**before** allocating or recursing. The search is iterative deepening — one bounded branching tree
per cardinality `c = 1..=depth` — so the node count that must fit under the declared ceiling is the
sum over the rounds, `Σ_{c=1}^{depth} Σ_{i=0}^{c} b^i` at branching factor `b`, computed as a
`BigUint`; bounding one depth-`depth` tree instead undercounts the work, at `b = 1` by a factor of
about `depth/2`. A declaration above the ceiling returns `HittingSetSearchTooWide`, carrying the
summed count and how many rounds it covers, rather than approximating. Within the bound it
returns *every* minimum-cardinality receiver, never a representative. Two returns are named rather
than encoded as an empty answer: `Unseparable`, when a member pair has an empty separator set and
therefore no receiver at all distinguishes them, and `NoSeparatingSetWithinCardinality`. Lean proves
the reduction correct at the level the search rests on — `hittingSet_separates_all`,
`minimum_hittingSet_separates_all`, `minimum_no_smaller` and
`no_hittingSet_of_empty_separator_set`.

[definition] **A finding that sharpens the plan: openness is a property of a reading at a member,
not a global veto on a contact.** A contact one member leaves open is open-carrying in the family
partition and enters no separator set of a pair that reads it open — but two *other* members may
both have decided it, and it then separates them. Such a contact can therefore appear in a minimum
separating receiver while appearing in no separator set of any pair it is undecided for. Discarding
it wholesale would throw away a real distinction; counting it where it is open would resolve an
undecided reading. The owner does neither, and the worked fixture exhibits exactly this contact.

[established-bounded; measured] The three M5 RBX1 presentations are one plural fibre over 10,368
alpha-carbon contacts: 38 unanimously formed, 10,288 unanimously excluded, 41 separating and 1
open-carrying — the single reading the designed presentation leaves open at the 8 Å aperture, which
is carried and counted on neither side. The pairwise separator sets, as (agreeing, separating,
open-carrying), are designed against free `(10338, 29, 1)`, designed against CUL1-bound
`(10337, 30, 1)` and free against CUL1-bound `(10344, 24, 0)`. **No single contact separates all
three presentations** — a decided reading takes two values, so two of any three agree at every
contact — and the minimum separating receiver therefore has two contacts, with **564** distinct
witnesses, all of them returned. The Boltz-2 smoke prediction under `.local/boltz-smoke/` is **not**
a presentation of RBX1: its input is a single 330-monomer chain against the M5 object's 96-monomer
binder and 108-monomer target, so it is used only as a hostile input, and the fibre's object check
is what refuses it.

[definition] **B6 — Passages. Returned.** `(K,Theta)_{t+} = Phi_e((K,Theta)_{t-})` as a first-class
typed event, so that environment change, binding, protonation and mutation are passages carrying
receipts rather than reparameterizations. The owners are
[`physical_occurrence/passage.rs`](../../crates/holonic-engine/src/physical_occurrence/passage.rs)
and the **B6** section of
[`Foundation/PhysicalOccurrence.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean).
The three vertical events are built **on** B3's `EnvironmentPassage`, which already refuses a
transport leaving a divergent axis unaccounted; a `Passage` adds the two occurrences, the exact
delta in `K`, the residual and the cost receipt that type does not carry.

[established-bounded; implemented-exact; formal-checked] **Vertical and horizontal are two types
with no coercion.** The axis is a sealed type parameter: `Passage<Vertical>` carries environment
change, binding and protonation, `Passage<Horizontal>` carries mutation, no `From`, `Into`, `Deref`
or trait object relates them, and `then` composes within one axis by its own signature. In Lean the
axis is an index of `TypedPassage` and the separation is a theorem rather than a naming convention:
`no_vertical_passage_carries_a_mutation` and
`no_horizontal_passage_carries_an_environment_change`. Each constructor checks its own evidence
rather than accepting the label — a binding refuses unless the named partner really enters the
oligomeric state and retains the exact copy difference; a protonation refuses an acidity axis that
did not move and refuses to rest on an undeclared one; a mutation refuses an environment that also
moved, a change of the target component, an indel, and a site the sequences do not actually differ
at. A chain mixing the two axes is deliberately **not** typed as either: it is two passages, and
the owner says so by refusal rather than offering a coercion.

[established-bounded; implemented-exact; formal-checked] `ConstraintDelta` is the complete
per-contact class transition computed from the two complexes, with `formed`, `broken`, `opened`,
`closed`, `retained` and the full three-by-three `census` as projections of it, so no two readings
can disagree. Composition is exact and associative (`Delta.comp_assoc`, by `rfl`), refuses contact
by contact where two deltas do not meet, and collapses a class that moves away and back into a
retention rather than counting it twice. Serial composition retains the **joining occurrence** as a
whole value — AGENTS.md's addressed-span rule, so equal endpoints do not preserve lineage by
themselves — and is associative as an equality of passages, because the step list is concatenated
and the composite delta and `presentation_cost::CostReceipt` are left folds over that one list. A
passage is a `continuing_tower::Transition`: it retains the whole source face as its residual,
`check_reopen` returns `reopen(apply(x), residual(x)) = x`, and `reverse_passage` returns
`ReversePassageReceipt::OnlyWithTheResidual` naming the two merged faces. Lean's
`ClassAction.traversability_is_the_residual` proves the sharp form — the reverse exists from the
transported face alone **exactly** when the action is injective at every contact, and the retained
residual restores the source exactly either way — instantiating
`ContinuingTower.ResidualMigration.traversability_is_the_residual`.

[established-bounded; measured] The M5 exhibition is free RBX1 to CUL1-bound RBX1 as a binding of
CUL1 with exactly one added copy. Its exact contact delta over the 10,368 addressed pairs breaks 19
alpha-carbon contacts and forms 5, retaining 40 formed and 10,304 excluded, with **nothing opening
and nothing closing**: both Protenix presentations decide every addressed pair at the 8 Å aperture,
so the whole change is a decided rearrangement of the interface. The environment delta moves target
conformation, oligomeric state, assay format and the two axes neither release declares, and retains
species, cofactors and partners. The cost receipt is accounted on every axis with no floating point:
10,368 decode steps, 24 update steps, 10,368 certificate steps and a residual of 16,433 bits, the
exact `code_bits` of the class fibre `3^10368`. That exponentiation is guarded by a declared
`EXACT_CLASS_FIBRE_CEILING` with a typed refusal above it, never a truncated exponent.

[definition] **B7 — Rigidity, topological, spectral and physicochemical receivers.** These are
specified in the receiver atlas. The rigidity half is **returned**:
[`rigidity_receiver.rs`](../../crates/holonic-engine/src/rigidity_receiver.rs) and
[`Foundation/RigidityReceiver.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/RigidityReceiver.lean)
own `J_eta = D F_eta(q)`, `ker J_eta` as the infinitesimal motions, `ker J_eta^T` as the self-stress,
the trivial motions measured rather than assumed, rigid clusters and contact-removal sensitivity,
with the open class carried as a family exactly as `physical_constraint_grading` carries it.

[established-bounded; formal-checked; implemented-exact] The topological half is **returned** as
well: [`topological_receiver.rs`](../../crates/holonic-engine/src/topological_receiver.rs) and
[`Foundation/TopologicalReceiver.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/TopologicalReceiver.lean)
own persistence over the exact squared-distance aperture filtration — components, cycles, cavities
and contact-community persistence, with exact rational birth and death values, over `ℚ` and over a
declared `𝔽_p` whose primality is *decided* within `MODULUS_BIT_CEILING` (64 bits) and refused
above it, and with the integral torsion read beside the field reading so field-dependence is
visible — together with the Gauss linking number as an exact integer under a declared rational
projection, degenerate projections refused by name rather than perturbed, and the projected writhe
returned per direction with no invariance claimed. Backbone loops closed by contacts are the
curves; an `Open` order comparison keeps the reading plural exactly as `physical_constraint_grading`
keeps the incidence plural; and where no cycle, no link or no embedding stands, the return is a
typed `NoCycle` / `NoLink` / `NoEmbedding` refusal and never a zero. The work is admitted before it
is done: `ApertureFiltration::found` takes a declared `cell_bound` checked at the occurrence
population, at the `n(n−1)/2` candidate-pair count and at every founded cell, and `persistence`
takes a declared `work_bound`, each refused by name rather than run unbounded. On the authenticated
release the designed RBX1 window carries five contact loops and two persistent cycles, the free
prediction two loops, and the CUL1-bound prediction none — which the receiver refuses rather than
reports as zero. The loop contacts now come from the presentation's own within-component family
through `presented_contact_loops`, with the filtration reading held to agreement and a
disagreement returned as a typed refusal preferring neither source; on the three M5 windows the two
readings agree exactly. R3's spectral/Hodge receiver has since returned as `hodge_receiver` and
`Foundation/HodgeReceiver.lean`; per-eigenvalue refinement on `ExactHodgeSpectrum` remains open,
as recorded in the live roadmap.

[established-bounded; formal-checked; implemented-exact; measured] The **physicochemical half is
returned**: [`physicochemical_receiver.rs`](../../crates/holonic-engine/src/physicochemical_receiver.rs)
and
[`Foundation/PhysicochemicalReceiver.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicochemicalReceiver.lean)
own residue-class contact composition per family, hydrogen-bond **candidates**, steric overlaps, a
burial **proxy** with an exact half-sphere exposure beside it, exact interface counts and rational
ratios, and a declared finite electrostatic model carried as an exact enclosure. It founds no unit
algebra: `quantity.rs` already owns `BaseUnits`, `Dimension`, `Quantity` and `Cast`, and the one
composition this receiver adds is `UnitedInterval` — the *enclosure*-valued quantity, which
`Quantity` is not, because every magnitude here is an interval. Adding two unlike dimensions is a
typed refusal naming both. Converting an `e² Å⁻¹` reading into an energy is a `quantity::Cast` the
caller supplies, and the chart change comes back as a `CastApplication` rather than happening
silently.

[established-bounded; implemented-exact] **No table is built in.** Residue classes, formal charges
at a declared protonation, hydrogen-bond donor and acceptor heavy atoms, van der Waals radii and
the dielectric are each an exterior declaration carrying a `TableGround` — a named source and a
stated scope, both refused empty — and the whole `ParameterTables` travels by value into every
reading exactly as `physical_intake::EnvironmentIndex` travels into an occurrence. The owner ships
*named* declarations the caller chooses among and supplies no default; a residue or element outside
a table's scope is refused by name and never filed under a fallback class or radius. Two readings
taken under different tables are **not comparable**: `compare_across_tables` refuses naming both
sets unless a `TablePassage` is supplied, and that constructor refuses any residue the two tables
class differently and the declaration does not account for — the same no-silent-transport law
`EnvironmentPassage` enforces across environments. The two shipped class tables differ at exactly
one residue, histidine, and that difference *is* a pH claim.

[established-bounded; measured] **A finding that is the receiver's primary result on the release.**
A charged-state reading is a claim about a protonation state, so it needs a declared pH.
`protonation_basis` returns `AcidityUndeclared` naming the axis and carrying the environment's own
stated reason, and **all three M5 occurrences leave that axis undeclared** — "no pH and no
protonation assumption is recorded anywhere in this release". The truthful primary return on the
mounted data is therefore the refusal, and every charged reading below is obtained only through
`ProtonationBasis::DeclaredAssumption`, whose ground travels into the reading and is checkable in
it.

[established-bounded; implemented-exact; formal-checked] **The exact readings and their laws.**
Every distance question goes through `DistanceAperture::classify`, so an undecided reading stays
undecided: a composition over a family carrying `Open` contacts is a **family of readings** between
`refusing_bound` and `admitting_bound`, and `admitting = refusing + open` at every class pair
(`admitting_eq_refusing_add_open`). Compositions are additive over disjoint families
(`composition_additive_of_disjoint`), so an interface and a within-component fold decompose
exactly. Every reading is invariant under a map preserving the pairwise separations and the
declared class (`composition_invariant_under_isometry`) and under a class-preserving relabelling of
the addresses (`composition_invariant_under_relabelling`). Hydrogen bonds are **candidates** and
there is no `HydrogenBond` type at all: `candidate_ignores_hydrogen_geometry` and
`two_geometries_one_candidate_reading` prove the reading cannot tell two geometries apart that
differ only in where a hydrogen sits. There is no solvent-accessible surface area anywhere, because
a rolling-probe area is a numerical integral: what is offered is an exact integer neighbour count
named a proxy, and `half_sphere_exposure`, the exact count of neighbours on each side of the plane
through a site normal to a declared reference direction, with the sites the interval arithmetic
cannot place carried apart. `1/r` is irrational for a rational `r²` and is carried as an exact
enclosure from `exact_value::AlgebraicRoot::reciprocal_square_root`'s Sturm certificate;
`invEnclosure_contains` states the certificate in purely rational hypotheses and
`invEnclosure_narrows` the monotone narrowing. The electrostatic model's approximations travel in
the reading: point charges at the declared sites, one uniform declared permittivity, no solvent, no
ions, no polarization, and the declared pair population as the model's own cutoff.

[established-bounded; implemented-exact] **A finding that sharpens the plan: a rotation of a
coordinate box is not a coordinate box.** A translation by an exact rational vector acts exactly on
an interval coordinate box, so translation invariance holds on every presentation. A rotation maps
an axis-aligned box to a set that is not axis-aligned, and re-enclosing it would widen the
presentation into a different occurrence — so `RigidMotion::act` **refuses** a rotation of a box
with width by name, and the full rigid-motion law is stated at point configurations, which is the
same domain `rigidity_receiver::ExactConfiguration::from_presented` admits. The rotation itself is
the composed Pythagorean `R_z(3/5,4/5)·R_x(5/13,12/13)`, and `RigidMotion::declare` checks
`RᵀR = I` entry by entry over `Q` before a motion exists.

[established-bounded; measured] **On the release, at the alpha-carbon interface.** Over the 10,368
addressed pairs at 8 Å the admitted totals are **64 / 59 / 45** with **1 / 0 / 0** open, which are
B8's recorded figures reached through this receiver's own founding of the family. The class composition separates all three
presentations: hydrophobic–hydrophobic **7 / 6 / 3**, polar–polar **0 / 0 / 2**, hydrophobic–polar
**8 / 7 / 3**, aromatic–hydrophobic **6 / 7 / 4**. The exact rational hydrophobic fractions are
`7/64`, `6/59` and `3/45`; no scalar stands for the interface and every ratio carries the two
counts it came from. **The charge receiver alone does not separate them**: salt-bridge candidates
are `3 / 3 / 3` and like-charge contacts `1 / 1 / 1` on all three. On `relation_ladder`'s rungs the
three presentations are pairwise **`NoRelation`** at this receiver family — the composition and the
electrostatic enclosure are separators, so rung 4 `ReceiverEqual` is refuted for every pair, and a
refuted rung 4 says nothing about rungs 1, 2 or 3. The designed presentation carries
the release's single open reading, so its composition is genuinely a family and the other two are
determinate. Under the declared protonation the electrostatic enclosure over the binder's 14,928
addressed pairs — 1,458 of them contributing — separates all three as **disjoint** rational
intervals in `e² Å⁻¹` at a declared relative permittivity of 4: approximately
`[−0.645630, −0.624647]` for the designed structure, `[−0.608259, −0.608211]` for the free
prediction and `[−0.568766, −0.568726]` for the CUL1-bound one, each an exact rational endpoint
rendered. The designed structure's enclosure
is **four hundred times wider** than either prediction's, and the reason is R5's finding in a second
receiver: its coordinates are deposited to three decimals and theirs to six, so the deposited
precision, not the chemistry, sets the width of the reading.

[established-bounded; measured] **A finding on the five-residue window where the combinatorial
receivers run out.** At the same declared five N-terminal RBX1 residues R3, R4 and R5 are blind on
and only R1 separates, the **combinatorial half of this receiver is blind for the same reason** —
the two predictions carry the same seven alpha-carbon contacts over the same residues, so the
composition is identical — and its **charge reading is blind for a second, independent reason**:
the window is `MET ALA ALA ALA MET`, which carries no formally charged residue at all, so the
Coulomb sum over it is exactly zero for all three and separates nothing. What does separate the
two predictions there is the **atom-grain burial proxy**, which reads heavy-atom geometry rather
than the alpha-carbon contact set: summed per residue against the whole two-chain presentation it
is `493 / 254 / 152 / 229 / 379` for the designed structure, `59 / 88 / 110 / 132 / 175` for the
free prediction and `66 / 90 / 117 / 137 / 179` for the CUL1-bound one. Hydrogen-bond candidates
there are `2 / 3 / 3` and steric overlaps `1 / 0 / 0`, which separate the designed structure from
both predictions and not the two predictions from each other. Stated on `relation_ladder`'s rungs:
at the window's *combinatorial* receiver family the two predictions are **`ReceiverEqual`** and the
designed structure is `NoRelation` against both, while at the window's *atom-grain* family all three
are pairwise `NoRelation`. Rung 4 at one declared receiver family is not rung 4 at another, which is
the atlas thesis measured inside one receiver.

[established-bounded; measured] **What this receiver does and does not surface of the wave-1
predictor defect.** At a declared two-angstrom radius a carbonyl oxygen bonded to its own carbonyl
carbon carries exactly one neighbour. Both of the designed structure's chain-terminal carbonyl
oxygens do; **three of the two predictions' four carry none** — no atom at all within two
angstroms, which for a heavy-atom model is no bonded partner. The fourth, the free prediction's
RBX1 terminus, sits 21.8 Å from its own alpha carbon and still lands beside something, and the
receiver says so rather than claiming the detection. The **steric reading is blind to the defect as
a defect**: of the three unbonded oxygens it reports exactly one, and reports it as an *overlap*
with whatever the stray atom landed beside rather than as a broken bond, while the CUL1-bound
prediction's two appear in no overlap at all. A reading of atoms that are too close cannot see an
atom that is too far. The reading that surfaces every one of them is the intra-residue covalent
radius, which `grain_tower`'s measured grain radius already owns as B0's inflation witness; this
receiver does not duplicate it.

[established-bounded; implemented-exact] **The contract rows are registered and recomputed.**
`receiver_atlas::ledger_entries` now carries thirty rows over five receivers, and `B7phys`'s three
`Satisfied` rows are computed at every call by real verifier functions against this owner's own
public worked witness: rebase equivariance under the exact rational rigid motion, source
accountability (the per-class-pair counts sum to the admitted total, the three classes exhaust the
population, and every candidate and every overlap names two standing sites and carries an exact
interval re-derived from the presentation's coordinates), and energy balance (the electrostatic
enclosure over a population is **exactly** the sum of its enclosures over a declared partition, with
no widening). Declaration independence is **Failed**, because the declared table decides the reading
and the owner ships the two tables that exhibit it; the gluing law with interface coupling and
stability away from bifurcation are **Unproved** with the absent object named in each.

[established-bounded; measured] **The intra-chain reading of the three M5 RBX1 presentations, at
8 Å.** Over the whole 108-residue chain the population is `C(106,2) = 5,565` pairs at `k = 3` and
`C(105,2) = 5,460` at `k = 4`; contacts are 224 / 214 / 175 at `k = 3` and 159 / 160 / 138 at
`k = 4` for the designed structure, the free prediction and the CUL1-bound prediction. **No pair is
`Open`** — at the declared centres or at the deposited enclosures — because a last-place-wide
coordinate box moves a squared distance by parts in a thousand and no intra-chain pair sits that
close to `64`. The open class is therefore empty on this object at this aperture, which is a
measurement and not an absence of the mechanism: the plural family is exercised on synthetic
material where a pair does straddle.

[established-bounded; measured] On the **same 24-residue RBX1 window** `rigidity_receiver` and
`hodge_receiver` were measured on in wave 3, with the intra-chain family founded at the owner and
carried through `rigidity_family` and `hodge_member` unchanged: at `k = 2` — the separation that
admits exactly the pairs the wave-3 fixtures built by hand — 47 / 36 / 27 contacts, 70 / 59 / 50
one-cells, 44 / 28 / 10 two-cells, `β = [1,9,6] / [1,14,6] / [1,17,0]`, and `rank J`,
`dim ker J`, `dim ker Jᵀ` of `62/10/8`, `53/19/6`, `50/22/0`. **Those three rigidity triples are
the wave-3 recorded numbers exactly**, so the owner-founded family is the same constraint set the
wave-3 window built by hand, and no recorded number changes. The one-cell counts `70/59/50` are
likewise wave-3's; the two-cell counts are **not** comparable, because wave 3's `79/56/32` and its
`b₂ = 32/20/5` were read on a **clique complex** built in the test, while `44/28/10` is the
constraint owner's own two-cell law — one chain step and two admitted contacts to the same
junction. At the declared separations the reading moves: `k = 3` gives 25 / 14 / 5 contacts,
`β = [1,10,1] / [1,2,0] / [1,5]`, `48/24/0`, `37/35/0`, `28/44/0`; `k = 4` gives 11 / 6 / 0
contacts, `β = [1,6,0] / [1,6] / [1,0]`, `34/38/0`, `29/43/0`, `23/49/0`. `dim ker Δ₁` under the
unit metric and the free condition equals `b₁` at every one of those readings, computed through a
path that shares nothing with the Smith normal form. Excluding the covalent neighbours costs every
presentation its self-stress: `dim ker Jᵀ` is `8 / 6 / 0` at `k = 2` and `0` everywhere at `k ≥ 3`.

[established-bounded; measured] **How the designed structure differs.** Inside the window it
carries the most intra-chain contacts at every separation (47/25/11 against 36/14/6 and 27/5/0) and
is the only one of the three still founding two-cells at `k = 4`. Over the whole chain that
ordering does not survive: at `k = 4` the free prediction carries 160 intra-chain contacts against
the designed structure's 159, so the designed structure's excess is local to the measured window
and is not a property of the chain. The CUL1-bound prediction is the sparsest at every separation
and every scope, and is the one that returns `NoCycle` rather than a zero.

[definition] **B8 — Selection and design equivalence. Returned.** Hard constraints first, then
Pareto filtering, then worst-environment ranking, then quality-diversity, then structural
clustering, with any scalar retained as one receiver and never as the identity of a candidate. Two
designs may be merged only when every declared receiver, environment and admitted future
transformation agrees; one separating future receiver refutes the collapse. The library owners are
[`design_selection.rs`](../../crates/holonic-engine/src/design_selection.rs) and
[`Foundation/DesignSelection.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/DesignSelection.lean),
stated in the vocabulary of `relation_ladder`/`Foundation/RelationLadder.lean`.

[established-bounded; formal-checked; implemented-exact] **Design equivalence is equal potential,
never equal score, and it is a new owner rather than a `physical_occurrence` submodule.** The
selection cascade consumes the receivers that read `physical_occurrence`'s complexes, so it sits
above that layer; and its population is a **rectangle neither existing family admits** — several
objects, each read at several environments. `VerticalFamily` refuses a second object,
`HorizontalFamily` refuses a second environment, and `PluralFibre` refuses a member of different
kinship by construction. `DesignFamily::declare` founds the rows as vertical families and the
columns as horizontal ones, so the composition is checked rather than asserted, and two designs
about the same object are refused by name as one object read twice. Design equivalence **is**
`RelationLadder.EqualPotential` over `DesignFamily::design_situation`, whose generators are
admitted `physical_occurrence::Passage`es — vertical environment changes and horizontal mutations,
each built through that owner's own constructor so a generator exists only where the passage does —
and whose receivers are the declared receiver family read at the carrier's environment index.
`merge_verdict` returns `Refuted{separator} | NotSeparatedWithinBound{bound} | EquivalentBy{iso}`,
only the third reaches `merge`, and `MergedClass`'s fields are private, so a bounded search cannot
reach a merged class by any path. A separator **overrides** a declared isomorphism, because the
separator is evidence and the declaration is not. In Lean:
`only_equivalentBy_licenses_merge`, `notSeparatedWithinBound_does_not_license_merge`,
`presentAgreementDoesNotImplyEnvironmentAgreement` and
`declaredEnvironmentAgreementDoesNotImplyUndeclared`, the last being
`RelationLadder.equalPotentialAntitone` made concrete — and executably, enlarging the declared
history ceiling from `0` to `1` turns the same pair's `NotSeparatedWithinBound` into `Refuted`.

[established-bounded; implemented-exact] **The cascade is five typed stages and no stage reads a
scalar.** Hard constraints return one typed `ConstraintViolation` per violated constraint and never
a penalty term — the stage performs no arithmetic at all, so no weight can make a violation
survivable. Pareto filtering runs over the **`(receiver, environment)` axes**, collapsing no
environment before the frontier has seen it, through
`presentation_cost::frontier_by`: the frontier rule of C5, **minimally generalized at its own
owner** to a declared three-valued axis comparison because a design's reading can be *undecided*
where a `BigUint` cost coordinate never is, with `pareto_frontier` re-expressed through it so there
is one spelling of the rule. An undecided comparison — a plural reading whose exact intervals
overlap, or an axis a receiver did not read — never licenses a discard. Worst-environment ranking
takes the extremum in the bad direction over the *declared* environment family: an undeclared
environment is absent and is neither a best case nor a worst case (`undeclared_environment_is_absent`),
a design unread at a declared environment is refused for ranking there and never imputed
(`unread_at_a_declared_environment_refuses`), and a worst that several environments attain returns
all of them. Quality-diversity returns one representative **set** per structural cluster, and
structural clusters are the connected components of the indistinguishability graph over
`physical_occurrence`'s own `DecidedClass` law — never a float embedding. No float decides
anything, every ranking comparison is exact through `topological_receiver::compare_values`, and
ties are returned as ties: a tier carries every exactly-equal design sorted by identity, and a pair
the exact law does not decide is returned in `undecided` rather than ordered.

[proved-derived; formal-checked] **A scalar-first cascade discards a frontier design every stage
above it keeps.** The constructed instance is `PresentationCost.chordFamily` lifted to designs —
readings `(0,10)`, `(10,0)`, `(6,6)` on two smaller-is-better receivers. All three pass the
constraints, all three are frontier points, each is its own structural cluster and quality-diversity
keeps the balanced one; yet over all 168 declared rational weightings with positive weight on
either axis, the balanced design is a minimizer of none. That is
`PresentationCost.unsupported_not_minimizer`, cited rather than rebuilt.

[definition] **A finding that corrects this plan.** The sentence "the mounted release already
exhibits this empirically" was wrong. The mounted release at
`/home/b/Downloads/holonics-m5-rbx1-rank05` carries **three presentations of one object** — one
designed structure and two Protenix predictions of the same binder against RBX1 — and **no
dissociation constant, no cross-species assay and no second design**. Its `STRUCTURE_MANIFEST`
names `design_models.csv` and `design_names.csv` by digest, but those files are not mounted. The
two per cent / six-fold observations are therefore recorded prose with no repository-local
measurement behind them, and they are modelled here as a **synthetic instance on exact rationals**
and labelled as such: two binders at `100` and `101` at one assay — inside a declared tolerance of
`2`, so rung 6 holds — that read `100` and `1200` at another, and two designs whose interface
receiver reads `41` on both and whose dissociation constant reads `50` against `300`. Rung 6 at a
receiver does not even give rung 4 at that same receiver at that same environment, which is the
sharp form of what the plan meant.

[established-bounded; measured] **On the release.** The three RBX1 presentations are one object at
three environments, so a design family over them is refused by name — that refusal is the
structural reason the release supplies no horizontal material — and they are used vertically. Over
the 10,368 addressed alpha-carbon pairs at 8 Å the formed-contact receiver reads **64 / 59 / 45**
for the designed structure, the free prediction and the CUL1-bound prediction, with **1 / 0 / 0**
open readings; the worst over the three declared environments at that greater-is-better receiver is
`45`, attained at the CUL1-bound presentation alone, and replacing one environment's reading with
an `Unread` returns `UnreadAt` rather than a ranking. The horizontal material is **synthetic**:
three designs built by exact perturbation of the mounted contact complexes — one renamed monomer of
the binder sequence, which is what makes each a different object and exactly what
`Passage::<Horizontal>::mutation` requires, and `0 / 3 / 7` flipped decided contact classes. At
each of the three real environments they are a horizontal family, each design's three faces are a
vertical family, the separator between the unperturbed and the seven-flip design is exactly those
**7** contacts, and the release's single open reading is carried on neither side.

[definition] **B9 — Evaluation discipline. Returned.** The six disciplines are six declared
partitions of a design population by one typed key each — target, interface family,
generator/predictor lineage, assay, disagreement class, environment pair — and the leakage law is
structural rather than a convention. The library owners are
[`evaluation_discipline.rs`](../../crates/holonic-engine/src/evaluation_discipline.rs) and
[`Foundation/EvaluationDiscipline.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/EvaluationDiscipline.lean).
It is a **new owner and not more of `design_selection`**: its carrier is the *quotient* of the
design population by the lineage relation rather than the designs, its receivers carry a fitting
history that a selection's `DeclaredReceiver` has no reason to carry, and its return is a
conclusion with a scope rather than a survivor list. The cost cascade of B10 is the opposite case
and extends `design_selection` instead — one cascade, two readings.

[established-bounded; formal-checked; implemented-exact] **Lineage never straddles a split, by
construction.** `LineageClasses` is the quotient of the design population by the relation the
horizontal `physical_occurrence::Passage::<Horizontal>::mutation` passages generate: an admitted
mutation is one `LineageEdge::Passage`, and two designs whose monomer sequences differ at no more
than a declared `EditRadius` many sites carry a `LineageEdge::EditDistance` whose site list **is**
the chain of single-site mutations joining them in sequence space, whether or not the family holds a
face for each intermediate. A changed target component or a changed sequence length founds no edge,
which is the mutation constructor's own refusal inherited rather than re-decided.
`Split::from_class_partition` takes a partition of *classes*, so its sides are unions of whole
classes and a straddle is not expressible; `Split::from_raw_designs` takes designs and returns
`SplitStraddlesALineageClass` naming the pair, the shared class and the connecting chain; and
`LineageClasses::straddle_of` returns that same leak as data, which is the converse witness. In
Lean: `ofClassPredicate_does_not_straddle` against `rawSplit_straddles`, with
`Lineage.cls_eq_of_rel` the fact that makes the first structural. `#print axioms` on the B9 theorems
returns only `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.

[established-bounded; formal-checked; implemented-exact] **Leakage through receivers, not only
through members.** A `FittedReceiver` carries the occurrences and designs it was fitted on, and
`evaluate_at` refuses at an occurrence it was fitted on and at any design lineage-equivalent to one
it was fitted on — the leak no member-level split catches, since nothing crosses the split and the
receiver still holds the evaluation side inside it. Success returns a `ReceiverAdmission` whose
fields are private and whose only constructor is that check, so an admission cannot be written by
hand. A `Calibration` is fitted within one assay and `carry_to` returns it unchanged there; across
assays it is refused unless an `AssayBridge` joining exactly those two is supplied, which is the law
`EnvironmentPassage` imposes on environments, restated for assays. Lean:
`evaluateAt_refuses_a_lineage_equivalent_occurrence`, `across_assays_without_a_bridge_is_refused`
and `a_bridge_between_other_assays_is_refused`.

[proved-derived; formal-checked] **A wet or external return is a new receiver occurrence.** The
earlier prediction's face is an occurrence at its own time and `ExternalComparison::state` returns
it unchanged; what the return produces is a *new relation between two occurrences*, stated on a
`relation_ladder::Rung` and carrying its own time index, strictly later than the prediction's. The
rung is computed from the two exact readings and the declared tolerance — `ReceiverEqual` on exact
equality, `WithinTolerance` inside the declared aperture, `NoRelation` otherwise — and never
declared. The cited law is `standing.rs`'s
`the_available_face_changes_while_the_source_does_not`: the available face changes while the source
does not. An external return that is not later is refused, and an `Unread` return is refused by name
because an unread return is not a return.

[established-bounded; implemented-exact] **Predictor disagreement is a fibre property.**
`disagreement_subsets` is `PluralFibre::partition`'s own four-way partition read as three evaluation
subsets — the two unanimous roles are one subset because an evaluation splits on *whether* the
predictors agree — and the open class takes precedence exactly as it does there, counted on neither
side. **A finding that sharpens the plan:** a contact counts as agreeing only when the predictor's
answer equals every member's decided class, and a separating contact takes two decided values by
definition, so *no* point predictor agrees with every member on a separating contact. The separating
subset's agreement rate is structurally zero for any such predictor, whatever its rate on the
unanimous subset — which is a sharper statement than "performance there says nothing", and the
worked instance exhibits it at `(1,1)` unanimous against `(1,2)` and `(1,3)` separating.

[proved-derived; formal-checked] **What an evaluation may conclude.** `EvaluationConclusion` has
three arms and no fourth: `EstablishedBounded` at its split and receiver, `GeneralizationRefuted`
with its counterexample, and `NotRefutedWithinThisEvaluation` as its own return. There is no arm
that affirms a generalization, `UniversalClaim` is uninhabited exactly as `RealizationProof` is, and
`at_another_split` returns `None` at any split but the one the conclusion was drawn at. `read_held_out`
takes a `ReceiverAdmission` by reference, so a conclusion cannot be drawn where the leakage law did
not admit the reading.

[definition] **B10 — Cost cascade and receipts. Returned.** The cascade half extends the B8 owner —
[`design_selection.rs`](../../crates/holonic-engine/src/design_selection.rs) and
[`Foundation/DesignSelection.lean`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/DesignSelection.lean)
— because it is *the same cascade read for what it costs* and not a second pipeline: a
`CascadeStage` carries the cheap reading it runs, the expensive receiver it stands in for and a
`presentation_cost::CostReceipt` per candidate for each, and `CostedCascade::run` runs a stage only
on the survivors of the cheaper stages. The receipt half — `RunReceipt`, the named clocks and the
tool-version readers — is in `evaluation_discipline.rs`, because a run receipt is evidence an
evaluation stands on and not a property of a design population.

[proved-derived; formal-checked; implemented-exact] **The soundness law of a cascade.** A stage may
discard only under a `DiscardLaw::HardConstraint` — whose cheap test *is* its expensive test, so it
is run once and charged once — or under a `DiscardLaw::CertifiedBound`, whose `Certified` token has
no public constructor and is minted only by `CascadeStage::certified_bound` after checking, at every
candidate of a declared probe, that the cheap reading refuses only where the expensive receiver
refuses; the first violation is `CertificateRefuted` naming the design. A
`DiscardLaw::UncertifiedProxy` **discards nothing**: what it would have removed is recorded in
`StageRun::would_have_discarded` and carried forward, and `run_admitting_every_proxy_discard` exists
only so the loss can be exhibited. In Lean, `certified_cascade_preserves_the_frontier` proves that a
cascade of certified stages returns exactly the full evaluation's survivors, and
`uncertified_proxy_loses_a_frontier_design` is the constructed instance where it does not;
`scalarFirstDiscardsAFrontierDesign`, which cites `PresentationCost.unsupported_not_minimizer`, is
the same loss at the design level. `cost_saving` returns the exact per-axis `BigUint` difference
with a typed direction and is never clamped to zero, because a cheap stage is itself a cost.

[established-bounded; measured] **The measured cascade, on the designed M5 structure, CPU only.**
Four stages over the 10,368 addressed `binder × RBX1` residue pairs: the cheap alpha-carbon filter
at the certified inflated aperture, the all-atom contact complex on its survivors, the rigidity
receiver and the grade-zero Hodge reading over the surviving interface. The material is 96 binder
residues carrying 473 atoms and 108 RBX1 residues carrying 857 atoms. The inflation is **measured,
never declared**: the largest distance from an alpha carbon to an atom of its own residue is
`7140003/10^6` Å, and `grain_tower::certified_coarse_aperture_squared` turns it into an inflated
coarse aperture squared of `124099666840009/(2.5·10^11)`, about 496.40 Å². Stage one takes 10,368
exact residue-pair classifications and discards 6,427, leaving 3,941; stage two takes **156,658**
exact atom-pair classifications on those survivors and finds 304 residue pairs carrying an all-atom
contact, where running it on everything would take **405,361** — a cumulative saving of **248,703**
atom-pair classifications, about 61.4 per cent. The certified discard is sound on this material:
**0 of the 6,427** discarded pairs carries an all-atom contact. **At the equal 8 Å aperture the same
discard is unsound**, and the measurement says by how much: it would discard 10,303 pairs and lose
**239 of the 304** all-atom contacts, 78.6 per cent — the residue-pair form of B0's 78.45 per cent
at the contact level, on the designed structure alone. Stage three reads 107 occurrences and 169
constraints with `rank J = 169`, `dim ker J = 152` and `dim ker Jᵀ = 0`; stage four reads 107 cells
with `dim ker Δ₀ = 1` and `β₀ = 1`. The four named clocks, as exact integer nanoseconds from
`std::time::Instant`: setup `133,873,256`, resident execution `41,086,275,664`, readout
`145,116,707,158`, end to end `186,337,424,672`. The measurement is `#[ignore]`d with its run
command in its own module header; the default test run does not take it.

[established-bounded; source-inspected] **A finding that corrects this plan.** The sentence "the
repository has verified no such kit" is wrong. This workstation carries **Boltz-2 2.2.1** and
**torch 2.14.0+cu130** in the virtual environment an earlier session installed at
`.local/venv-protein`, and a **ProteinMPNN** checkout at `.local/tools/ProteinMPNN` whose `HEAD` is
`8907e6671bfbfc92303b5f79c4b5e6ce47cdef57`. Those three version strings are **read**, not recorded
by hand: `evaluation_discipline::python_package_version` and `git_head` ask the tools themselves,
and `ToolVersion::Read` carries a `Recorded` token with no public constructor, so a version that was
not read cannot be written — the only other value is `ToolVersion::Unavailable{why}`, which says why.
A `RunReceipt`'s fields are private and its only constructor is `RunRecorder::finish`, which refuses
without an `end_to_end` clock; every clock reading is an exact integer nanosecond count carrying the
declared source it came from. What the repository still has **no** measurement of is either kit's
output: neither has been run against an M5 design here, and nothing in this increment changes the
non-claim at the end of this document.

[definition] **A finding that sharpens the plan.** A typed key and a lineage partition are two
independent declarations and nothing makes them agree, so `Split::leave_one_out` is where they are
reconciled: it computes the held-out set from the declared key and then refuses unless that set is a
union of lineage classes. The declared `EditRadius` is not a nuisance parameter either — it decides
the quotient, and on the worked four-design family the same population is four classes at radius
zero, two at radius one and one at radius three. Neither the radius nor the key has a default.

## Extension relationships

[definition] RNA is a nearby extension of the protein construction because it supplies a discrete sequence, a
nonlocal pairing incidence, pseudoknots, continuous configuration, ion and ligand modulation,
cotranscriptional chronology and several functional faces in one manageable domain, and because two
molecules reaching the same pairing diagram by different paths may respond differently afterwards —
a direct biological use of the receiver-history law. DNA and chromatin compose the
existing bend-twist-stretch chart with base-pair frames, linking, twist and writhe, nucleosome and
loop incidence, and transcription and repair receivers. Viral and cancer ecologies are compositions
over those carriers, where a class is a receiver-relative equivalence under declared hosts,
interventions and immune receivers rather than a taxonomic label. Neurochemical modulation is the
further research target: a modulator enters as constitutive modulation `Theta(m,eta)` with its own slow
dynamics, changing gain, time constants, excitability, coupling, plasticity and future sensitivity,
so that two circuits with the same present firing face and different modulator state separate under
the next stimulus or drug.

## Non-claims

[definition] No HNN has produced a protein sequence, backbone or structure in this repository, and
nothing here establishes that one generates better binders than established design methods. What
the repository owns is an exact representation and analysis substrate. That boundary is a falsifier
to be discharged by construction, not a disclaimer to be repeated.
