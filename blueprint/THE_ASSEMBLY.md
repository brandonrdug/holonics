# THE ASSEMBLY

**Ratified 2026-08-07.** *"We have no business in limbo anymore, we need to proceed."*

The parts exist. 28% of the library body — 51 modules, 59,914 lines — has no inbound edge. This
document is the wiring, in dependency order, with the exact type adapters and the falsifier for each
loop. It is not a menu.

## The three structural facts that govern every step

**F1 — the dependency graph forbids the obvious wiring.**
`body · holonic-structure · relational-geometry · soma-standing-deposit` are leaves;
`holonic-engine` sits above the first two; `soma-membrane` above `body`; `life` above both;
`holon-plate` above `life`. **A `life` example can therefore never call `holon_plate::deposit`** —
it is a Cargo cycle, and that, not laziness, is why the plate mouth is unfed.

**F2 — there is one shared carrier and it needs no adapters.** `GradedCausalComplex` with
`CausalCellId` and `ComparativeMultiplicity`. Seven organs already take
`(&GradedCausalComplex, BTreeSet<CausalCellId>)`: `rebase_invariants_on`, `dilate`, `read_cover`,
`spread`, `read_substitution`, `found_potential`, `closed_hull`. `dilate(..).support` *is* the type
of `Cover.left`, `Neighbourhood.sections`, and `skein`'s contexts. **The backbone costs zero
conversion code.**

**F3 — the two halves do not touch.** `holonic-engine` (110,852 lines) and `body`+`membrane`+`abi`
(54,281) share exactly one crate, `holonic-structure` (2,102 lines, seven types), and **zero data
adapters**. The only crossing is `soma/life/src/exact_world.rs`, 95 lines, exercised by **1 of 27**
`ExactEventLaw` implementations.

## The work, in dependency order

**1 · a new engine module, `complex_system` — `GradedCausalComplex` → `ObservedSystem`.**
`CausalCellId(u64)` and `ItemId(u64)` are the same representation with no `From`, no `Into`, and no
function anywhere converting them. **That single missing adapter is the cut line between §11's
condensation half and its positivity half.** Write `fn item(c: CausalCellId) -> ItemId` locally —
never `impl From` in `algebraic.rs`, which would put a placement dependency in the algebraic carrier.

`ComplexSystem { complex, receivers: Vec<DilatedSection>, inputs: Vec<CausalCellId> }`. Observation
is `1 + section.lineage.distance[&cell]` inside the horizon, `0` outside — a receiver-local address,
the same shape `eros_placement_over_real_charts.rs` already uses. Successor steps across a 1-cell;
`None` is a declared terminus.

**The seam is one-directional and that is a declaration, not an omission.** `Observation` is
documented as *"an opaque exact token — never a magnitude."* There is no adapter back. Widening it
to carry a coefficient puts an orderable quantity in the conduct path and fires §13 rule 2.

**2 · Realizers from substitutions.** `place` needs `reaches: FnMut(RealizerId) -> Vec<ItemId>`.
`CausalCell` does not retain what founded it. Use `skein::Substitution`: each declared substitution
is a realizer whose landings are `substitution.added()`. This wires `skein` — zero callers today —
into `placement` directly, and makes the realizer population an object the machine returns rather
than a bookkeeping side-channel.

**3 · `RecoveredCodec` → `ObservedSystem`.** A finite machine whose states are `SymbolClass` and
whose inputs are symbols — `ObservedSystem`'s exact shape. Then `compress` returns its Nerode
congruence and `shortest_separating_input` returns the same quantity by an independent joint-automaton
BFS. **Two implementations of one quantity, which §8 asks for, free, and it can fail.**

**4 · The curvature bridge.** `discrete_curvature` already reads `HingeId`/`VertexId` — the same
identity types `local_star` uses. Three pieces are not free:

- **B1** `BTreeMap<HingeId, RatVec3>` → `Rat`: take `dot` against the hinge's own edge direction,
  because `local_star.rs:2082` spends the response *only* along that edge. **Refuse `norm_squared`
  in review** — it is direction-blind and cannot distinguish an expanding hinge from a contracting one.
- **B2** declare link sizes **from hinge incidence, not from `link_vertices.len()`**, or `found`'s
  certification restates its input instead of being a second frame. Declared aperture: the
  interior-cycle vertex subpopulation. Outside it, the typed refusals are correct behaviour.
- **B3** the write-back at `local_star.rs:2301`, the one genuinely lossy conversion.
  `Rat → RatVec3` is **not a function**. The only honest lift keeps the direction and revises the
  magnitude, and refuses when the response along its own edge is exactly zero. **Any implementation
  that picks a canonical direction has invented geometry the layout did not have.**

**5 · Plate I/O.** Each of the ~25 `soma/life/examples` sites keeps its hash **and** writes the
octets to `output/<driver>/<name>.form`. Then `holon-plate deposit` and `standing-deposit deposit`
run from the shell. **No dependency is added anywhere**, which is what F1 requires.

**6 · The `RBIN` plate schema.** A census is fixed names and `u64` values, so a varying-arity family
like `betti_0…betti_k` cannot be one. Use `cells`, `grades`, `boundary_rank_total`, `betti_total`,
`torsion_factors`, and the Euler characteristic — the last encoded as `euler_positive` and
`euler_negative`, exactly one nonzero, because **`i64 → u64` must be a declared bijection, never a
cast.**

## The plate choreography

```text
DEPOSIT   a part with a live body seals a form
CARRY     the octets move; nobody interprets them
RE-LIGHT  a DIFFERENT part opens it
PRESENT   the re-lit body takes one deed, and is re-sealed
```

**The depositor and the resumer must be different parts, and the resumer must compute a census field
the depositor could not.** A part that deposits and resumes its own plate has one frame, and a hash
cannot catch a forged-but-consistent plate — only the second frame can.

**Every hand-off carries a deed.** `resume` → `present_and_require_change` → `redeposit`. A hand-off
with no deed is a restore wearing a dance's name, and `DeedChangedNothing` refuses it.

**The census must contain at least one field the hand-off itself moves.** `ERST` records why the
obvious six were insufficient: a depth-one carrier advances *within* its extent, so an extent cannot
witness that a body received anything.

**Lineage lives one level up, and the census is the wrong home for it by construction** — a resumer
cannot derive its parent's hash from its own form, so a census carrying it would refuse every
descendant. Write the child plate as a `return` and the parent plate as a `mount` in
`standing-deposit`: the child's `closure_sha256` **is** its lineage, already implemented, no new
field. It inherits the right semantics too — a corrupted child REFUSES; a parent that moved on
REPORTS, because *a standing that could not fall behind the current would not be standing.*

**Concurrency is solved by content addressing, not locking.** A plate's filename is its
`plate_sha256`; nothing is written twice. The forbidden move is two parts holding *live bodies* of
one plate and both re-depositing: **a re-lit body is owned by exactly one part for its whole life,
and it dies by re-depositing.**

## The loops, each with its falsifier

**(a) DECOMPOSE → RE-INTEGRATE.** The signal is the **collapsed-pair population**, not a verdict —
each pair carries the shortest word separating two items the one-shot reading merged. It enters at
`revise_and_resume`: the decomposer *is* the `Program`, and every collapsed pair founds a parented
`CodecVersion` cutting at that word. **Falsifier, both halves required:** ablate the revision and
confirm the population does *not* shrink; and run where `is_exact()` is true and confirm **no codec
version is founded**. A mechanism that founds on every pass has a clock, not a consequence.

**(b) LAYOUT → CURVATURE.** The signal is `CurvatureFlowStep::revisions`, entering at the
`geometry_responses.clone()`. **Grade the deficit, not the combinatorial charge** — the charge moves
only when the complex changes, so a run grading it will report no movement and conclude wrongly.
**Falsifier:** nonzero deficit must move; flat must stay fixed; and the claim *"the flow drives every
deficit to zero"* is **FALSE** — bipartite components with unequal parts are fixed at nonzero
deficit, at a scale that is pure counting. A run claiming universal convergence has mis-graded.

**(c) PRODUCTION → ANALYSIS.** β₁ at grade 1 is the independent routes to one result; torsion is a
recruitment that cannot be un-derived. **(a) and (c) are one crossing on two materials** — that is
§4's anti-scatter discipline holding, not two organs. **Falsifier:** withhold the reading and confirm
target selection is identical; and **the reading must be able to be nonzero** — the 31 deposited
artifacts today are one statement with β₁ = 0, so the first obligation is a declared control.
Refusals must feed it too: a reader ingesting only acceptances is success-filtering wearing
analysis's name.

**(d) PLATE I/O.** The signal is the octets. **Falsifier:** round-trip through a second process — a
`FormNotCanonical` refusal proves the driver's rest was never a canonical form, **and that can fail
today with nobody knowing, because a hash of a non-canonical form is a perfectly stable hash.**

## The holistic constraint

*"It's never just one thing or method, never one kind of chart."* Four places where a single chart
silently becomes the answer, each with a preventer already in the code: the **pivot rule** (read
under all three and compare), the **walk order** (the section and the lineage are two fields of one
return — an adapter that keeps `.support` and drops `.lineage` deletes the chart and keeps the
invariant, which reads as rigour and is the loss of the second frame), the **receiver** (free-rank
and torsion obstructions, the second existing because the first was insufficient), and the
**aperture** (each organ declares its own; composing without reading them returns a wrong answer).

**The reviewable rule: no adapter may reduce one of these structures to a boolean or a scalar on its
way to the next organ.** Gate on the boolean if you must; deposit the population.

## What must not be built

A scalar score, weight, bias, gate or threshold in the conditioning path. A `MinCover` founded by
inverse frequency. A `pub use` glob of the new engine modules — `ReceiverId`, `Disagreement`,
`Partition`, `Cover`, `Observation`, `ItemId` all collide. A `restore`/`thaw`/`unfreeze` verb. A
lineage field inside the plate container. A compression ratio, or any plate figure readable as a
competence number. An external checker anywhere load-bearing. A `Rat → RatVec3` reconstruction. A
second rank implementation — route everything through `smith_normal_form`. A driver reporting counts
instead of artifacts. Anything named by an ordinal.
