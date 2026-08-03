# THE HYPERGRAPH SUPPLIES THE REWRITE; THE TRIANGLE CARRIES THE COMPARISON

**2026-07-21 · assistant derivation from Brandon's triangular/gyrating-manifold intuition ·
Brandon-authorized construction built · host/multicore/CUDA/rest exact · no Formula change**

## The result in plain language

The object Brandon has been describing is not a traditional cellular automaton with triangular
pixels. It is closer to a **rewrite-enriched oriented event complex**:

- actual occurrences are discrete without being scalar;
- arbitrary-arity relations say what is locally connected;
- oriented cells say what boundary an occurrence composes;
- local rewrite rules change those relations while holding a real interface as a pivot;
- transport along the oriented incidence says what one face does to another;
- causal dependence comes from which actual event consumes or preserves another event's material;
- a triangle compares two routes between the same situated endpoints;
- higher cells state coherence among those comparisons; and
- every view is a receiver projection from inside that evolving complex.

“Triangle,” “hypergraph,” “manifold,” “circuit,” and “field” therefore name different faces of one
candidate construction. None can replace the others.

The normative typed version is deposited in [`ELEMENTARY_MECHANICS.md`](../ELEMENTARY_MECHANICS.md).

## I · Why an ordinary cellular automaton is too absolute

A conventional cellular automaton begins with a fixed lattice, one state from a fixed alphabet at
each cell, a fixed neighborhood, and a synchronous or otherwise selected iteration rule. That is a
valid and powerful model. MathWorld explicitly includes triangular lattices among the possible
grids. But changing the grid from squares to triangles does not address Brandon's central point:
the activity is not a private state owned by one cell.

In the candidate Eros object, the elementary datum is an actual incidence such as

```text
edge occurrence belongs to triangle occurrence with this orientation,
event occurrence depends on these earlier occurrences,
transport across this incidence carries this exact local map.
```

The activity belongs to that relational neighborhood. A triangle can be part of several
higher-grain bodies, can share an edge with another triangle, can expose an unmatched face, and can
be replaced by a local rewrite. Asking for “the state of the triangle” generally projects away the
very relation of interest.

This retains discreteness. The occurrence and the event are discrete. What is rejected is only
the assumption that discreteness must be encoded as one scalar per fixed cell.

## II · What the Wolfram hypergraph work contributes

The Wolfram model makes several distinctions that the laboratory needs to keep:

1. a **spatial hypergraph** is one state of relations;
2. an **updating event** is one actual local replacement of relations;
3. a **causal graph** relates updating events through material dependence;
4. a **multiway graph** retains alternative updating histories; and
5. **causal invariance** is the additional property that permitted divergent histories ultimately
   reconcile in the relevant causal structure.

The first three have a direct structural use here. The fourth is useful as a bounded analytical
instrument, not as an instruction to keep every possible match alive inside Soma. The fifth is a
proof obligation. Wolfram's own survey notes that causal invariance is not guaranteed for
multi-relation rules and is relatively uncommon in the enumerated rule class. It therefore cannot
be inferred from a canonical executor schedule.

The translation is:

```text
Wolfram relation collection       candidate Eros relation cut
Wolfram updating event            actual local world/Eros occurrence
Wolfram causal dependence         source production/consumption dependence
Wolfram multiway alternative      possible but not necessarily lived continuation
Wolfram causal invariance         Eros confluence/schedule-independence obligation
```

This is a structural correspondence, not an identification of Eros with the Wolfram Physics
Project or a claim about fundamental physics.

## III · Why a hypergraph still is not enough

A hyperedge can relate any number of vertices and so expresses arbitrary local arity beautifully.
But a bare hypergraph does not tell us:

- which occurrences are 0-, 1-, 2-, or higher-dimensional;
- how a higher occurrence is oriented;
- whether its boundary closes;
- whether two equally labelled hyperedges are one occurrence or two;
- which incidence is spatial/boundary and which is causal/dependency; or
- what exact relation is transported along a path.

Those are precisely the jobs of the occurrence-level oriented complex and its carrier maps.

Conversely, a chain complex says how oriented boundaries cancel but does not say which local
replacement rules are afforded. The correct construction is a coupling, not a contest:

```text
typed multi-hypergraph + local rewrite
                  |
                  v
actual occurrence-level oriented event complex
                  |
                  v
dependency graph + transported carrier + emitted successor.
```

## IV · The triangle has three simultaneous readings

For the directed triangle

```text
x0 --a01--> x1 --a12--> x2
 \________________a02___/
```

the same occurrence has three lawful readings.

### Boundary reading

```text
partial tau = a12 - a02 + a01,
partial partial tau = 0.
```

This is why a triangle is the smallest useful oriented closing face. It is not why every trio of
intersecting lines becomes one triangle; the incidence must actually exist.

### Transport reading

```text
Chi_tau = (T_a12 circle T_a01, T_a02).
```

The triangle compares the composite route with the direct route. Equality is one possible flat
face. A nontrivial comparison can be winding, curvature, contradiction, residual, or a founding
signal under a declared receiver, but none of those is a universal scalar property of `tau`.

### Hinge reading

When `tau` shares an actual edge with another cell, that edge can be held as the invariant
interface of a local rewrite. The neighboring cells may rebase around it, the transport across it
may change, or a retriangulation may replace its surrounding star.

This is the rigorous content of “pivot.” A point drawn at the same coordinates is not a pivot. An
actual preserved interface is.

## V · What “changing bases” can mean

The conversation has used changing bases for at least three distinct operations:

1. **carrier rebase** — change local coordinates by `G_x`; topology stays fixed;
2. **combinatorial retriangulation** — replace cells inside one fixed exterior boundary; and
3. **metric fold** — change angles or lengths around a preserved hinge.

The first needs exact transition maps. The second can be represented by graph rewriting or
Pachner/bistellar moves. The third additionally needs metric or kinematic data. Treating them as
one operation is why a picture of a kink can look explanatory while the data underneath remains
ambiguous.

The 2-dimensional elementary retriangulations are especially close to Brandon's image:

```text
2 -> 2: hold a quadrilateral boundary and exchange its diagonal;
1 -> 3: hold one triangle boundary and introduce an interior vertex;
3 -> 1: remove that interior vertex when the inverse conditions hold.
```

They show how a local surface can change its discrete basis while its exterior relation remains
fixed. They do not by themselves define Eros's consequence, connection, or compression laws.

## VI · N-sheets and cross-sections

“N-sheets” need not mean a Cartesian product of every available field. A product `X × Y` is lawful
only when the application actually supplies independent factors and the product relation.

The more general object is an atlas of occurrence complexes with declared overlap maps. A
cross-section is then a pullback/restriction through an actual map, and a seam is an actual shared
subcomplex. Higher-dimensional cells can bind several lower-dimensional sheets without implying
that every constituent coexists in one dense product.

This makes the visual language precise:

- a **sheet** is a locally continuing incidence/transport stratum;
- a **cross-section** is a receiver restriction through an actual map;
- a **seam** is a declared shared boundary/interface;
- a **pin** is the discrete occurrence at which the interface is founded or held;
- a **fold** is a rebase or rewrite about that interface; and
- a **face** is the receiver presentation of the resulting local relation.

The point/line/loop intuition is then chart-relative without becoming arbitrary. One occurrence
may project to a point in one quotient, trace a line across event order, and close as a loop under a
higher path comparison. Those are three maps from one lived construction, not three absolute
identities asserted at once.

## VII · Lightning, potential, and diffusion

The lightning image can be translated without pretending that Eros already contains atmospheric
electrodynamics.

```text
open transported boundary     leader-like afforded continuation
local path comparison         polarization / relative potential face
formed junction               conducting route through actual interfaces
returned world consequence    return-like later current
unmatched oriented boundary   residual capable of bending later transport
```

A literal diffusion law needs more. On an additive cochain complex one can define a coboundary
`d`; with a metric/Hodge star one can define a codifferential and Laplacian; with conductance or
capacity weights one can define how activity propagates. Without those choices, “diffusion” is a
useful qualitative expectation but not an executable law.

Likewise, a probability field needs a receiver partition/filtration and measure. A multiway graph
or population of open leaders supplies possibilities and causal structure, not normalized
probability on its own.

The information-chemistry reading fits here. Interfaces have typed compatibility, orientation,
valence-like arity, and residual. Reactions are local rewrites whose applicability depends on the
present complex. Acidity, chirality, charge, or catalysis may be lawful application charts; none
is an intrinsic universal label on a triangle.

## VIII · The first-person camera

An observer view is a map from the active construction at a declared receiver and grain. It is not
an absolute coordinate system outside the event. A useful observatory should therefore select:

```text
receiver occurrence or region,
event/causal cut,
grain,
transport path or comparison,
exposed boundary and residual,
and the quotient used to render them.
```

The rendered coordinates can still look like an ordinary 2D or 3D camera. The difference is that
the view transform is derived from a named situated chart and the exact data remains available
beside it. This is an observer law, not a new causal engine object.

## IX · The source correction this derivation produced

The live source already contains substantial parts of the candidate object:

- event-local plural cells;
- oriented boundary and dependency incidence;
- exact `partial partial = 0` validation for source boundaries;
- local pins and path transports;
- co-present regional closure;
- higher-grain composition;
- exposed open residual;
- outgoing interior folding; and
- exact rest/remount.

The authorized construction closed the carrier gaps directly:

1. every cell now carries independent dependency rank, topological dimension, and constituent
   grain;
2. regional seams form only through exact source-declared interface capabilities, never inferred
   reach, grain, coordinate, or projected equality;
3. the complete pair of parallel paths is first-class and `Chi` is only its optional projection;
4. an actual local rewrite can name the dependency which preserves its interface;
5. every outgoing interior fold checks an exact structural boundary-conduct family and returns an
   ephemeral preservation certificate; and
6. two different source worlds cross the same one-core, eight-core, CUDA, and durable-rest mouth
   with exact agreement.

This does not install a universal rule matcher or DPO subsystem. The source still supplies the
actual event and its interface. Canonical sorting still establishes deterministic execution only;
confluence or causal invariance of arbitrary interacting rewrite rules remains unproved. The
compression certificate covers the current later-contact boundary, not every possible future
world observable.

## X · Consequence for the theory record

The strict-nerve/open-horn derivation remains a useful special chart, but it is too narrow to be
the core. A category nerve fills composable arrows according to its own strict composition law,
while Eros must distinguish an available mathematical composite from an actually formed event.
The stable base is therefore an occurrence-level oriented complex; a semi-simplicial set, strict
nerve, CW complex, or directed hypergraph is an optional representation when its assumptions fit.

Similarly, `J_*` in `FORMULA §CXL` must be read as a finite occurrence population under closure.
Only after incidence linearization does it become a chain on which oriented cancellation is
defined. Opposed coefficients cancel only on the same actually shared face; they do not erase the
distinct incident cells, and equally labelled but unglued faces cannot cancel.

No Formula amendment was made in this construction. The correction is explicit here and in the
elementary specification so it can be reviewed before any canonical rewrite.

## Sources opened for this derivation

- Wolfram Physics Project:
  [relation rewriting](https://www.wolframphysics.org/technical-introduction/basic-form-of-models/first-example-of-a-rule/),
  [updating events and causal dependence](https://www.wolframphysics.org/technical-introduction/the-updating-process-in-our-models/updating-events-and-causal-dependence/),
  [multiway systems](https://www.wolframphysics.org/technical-introduction/the-updating-process-in-our-models/multiway-systems-for-our-models/),
  [causal invariance](https://www.wolframphysics.org/technical-introduction/the-updating-process-in-our-models/causal-invariance/index.html), and
  [graph-type distinctions](https://www.wolframphysics.org/technical-introduction/additional-material/appendix-graph-types/).
- MathWorld:
  [Hypergraph](https://mathworld.wolfram.com/Hypergraph.html),
  [Cellular Automaton](https://mathworld.wolfram.com/CellularAutomaton.html),
  [Simplex](https://mathworld.wolfram.com/Simplex.html), and
  [Simplicial Complex](https://mathworld.wolfram.com/SimplicialComplex.html).
- Lack and Sobociński, [*Adhesive Categories*](https://www.brics.dk/RS/03/31/), and Baldan et al.,
  [*Left-Linear Rewriting in Adhesive Categories*](https://arxiv.org/abs/2407.06181), for exact
  concurrency/confluence boundaries in graph rewriting.
- Pachner,
  [*P.L. Homeomorphic Manifolds are Equivalent by Elementary Shellings*](https://doi.org/10.1016/S0195-6698(13)80080-7),
  for the PL scope of elementary triangulation moves.
- Hatcher, [*Algebraic Topology*, Chapter 2](https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf),
  for chains, oriented boundary, and relative closure.
