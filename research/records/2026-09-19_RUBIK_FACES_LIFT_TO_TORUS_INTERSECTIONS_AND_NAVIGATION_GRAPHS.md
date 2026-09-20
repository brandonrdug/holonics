# Rubik faces lift graph projections into torus intersections and predictive navigation

**Date:** September 19, 2026. **Status:** research synthesis. **Source image:** user-supplied
reference render, treated as a receiver projection rather than as an authoritative mathematical
diagram. This record schedules no new construction and preserves the active roadmap.

## Direct ruling

[project-postulate] A Rubik's Cube state is equivalent to a **face**. Here “face” means a complete
situated presentation at a declared receiver: the state, its active incidence, generators,
orientation convention, target, unresolved fibre and cost scope. It does not mean only one of the
cube's six physical sticker faces.

[interpretation] The attached render has a good visual instinct. Its three triples of overlapping
circles show cyclic relation families and shared points, but the 2D graph is a projection that
collapses depth, orientation, layer, winding, source lineage and unresolved configuration fibre.
The useful lift is therefore not to declare that the drawing *is* a complete cube graph. It is to
read the drawing as one receiver face of a higher-incidence torus carrier.

The visual word “hypergeometric” is best made precise here as **higher-incidence / hypergraph
geometry**: several cyclic supports share contact populations, and a point may represent a joint
constraint among more than two relations. No statistical hypergeometric distribution is inferred
from the picture alone.

## Recovered Rubik construction

[established-bounded; implemented-exact; computational-witness] The existing
[`rubik_corner_quotient_navigation.rs`](../../crates/holonic-engine/examples/rubik_corner_quotient_navigation.rs)
derives the six quarter-turn generators from actual signed cube-coordinate face geometry. The
corner projection closes to the genuine `S8` permutation quotient of order `40,320`, checks every
projected unit edge, and returns quotient diameter `8` in the declared quarter-turn metric. It
also lifts selected words to all 54 stickers. Corner orientation, edge permutation and edge
orientation remain the full-state fibre; the example explicitly does not claim a complete
God's-Algorithm solution for arbitrary cube states.

[established-bounded; source-inspected] The [September 13 navigation synthesis](2026-09-13_MASS_FLUX_GAPS_AND_OPTIMAL_NAVIGATION_RETURN_THEIR_SOURCE_MAPS.md)
places this in the existing `TransportWord`, quotient, source-map and receiver-history owners.
Korf's pattern-database work is prior art for optimal cube search, while the repository's return
derives its own physically grounded quotient and its exact lower/upper certificates. The
ordinary full 3x3 diameter and the smaller quotient diameter are different receiver facts.

[definition] For a declared state family `X`, move generators `G`, target `x_*` and cost `c`, the
navigation value is

```text
D(x_*) = 0
D(x)   = min_g ( c(g) + D(T_g x) ).
```

The minimizing actions form a policy fibre. An abstract quotient `q : X → Y` gives a lower bound
when each generator descends, `q T_g = U_g q`, and equality with a full-state solution requires
a cost-preserving lift that reaches the actual target. A displayed graph or one exact distance
face is therefore not automatically the complete cube state.

## The face is the correct primitive

[definition] A Rubik face is the receiver-visible boundary of a continuing configuration:

```text
f = (K, Θ, x, G, R, L, W)
```

where `K` is active incidence, `Θ` is material/constraint data, `x` contains piece positions and
orientations, `G` is the admitted move family, `R` is the chosen receiver, `L` is lineage, and `W`
is declared work/cost. A state can be complete at the corner receiver while remaining plural at
the full sticker receiver. That is not an error; it is the receiver atlas doing its work.

This is the same relation as the shared HNN carrier: one Holon across local, modal and receiving
charts, with a restriction from a complete object to a face. The graph is a face of the carrier;
the carrier is not exhausted by the graph.

## From three circles to three torus supports

[interpretation] The right-hand render can be lifted as three overlapping cyclic supports

```text
T_α, T_β, T_γ
```

with each `T_i` carrying a phase/winding coordinate and each shared region carrying a declared
contact constraint. A compact coordinate model is the phase atlas

```text
T³ = S¹_α × S¹_β × S¹_γ,
```

but the Rubik state graph is a discrete, constrained population inside this atlas, not the whole
continuous torus. The torus coordinates are a lift for cyclic turn relations, not a replacement
for piece incidence.

The correspondence is:

| Rendered feature | Lifted meaning |
|---|---|
| One colored circle | One cyclic generator/phase family |
| Circle intersection | Shared contact or compatibility constraint |
| Triple intersection | Joint constraint among three cyclic families |
| Colored node | A receiver-visible state/event on a support |
| Circular ordering | Generator order or winding order |
| Projected crossing | A pair collapsed by the display receiver |
| Lifted separation | The retained depth, phase, orientation or source fibre |

[definition] A cube face turn acts on the carrier by an admitted generator `T_g`. The torus
support records the phase/winding of the generator family; the actual state action still acts on
the piece incidence. A valid lift must preserve the generator action, target image and receiver
fibre. A decorative torus drawn around an unrelated graph is not that lift.

The repository already owns this distinction. [`HNN_FORMULA.md`](../../docs/HNN_FORMULA.md) treats
toroidal cycles, overlapping field domains and higher-cell joints as native carrier relations;
`analytic_field` supplies torus phase charts; connection and holonomy owners transport current
around paths; an embedding in a 3D scene is only one receiver.

## Why the trefoil reading is useful—and what it does not mean

[interpretation] The three circular families in the render have a projected crossing pattern that
resembles a trefoil braid. Strictly, a trefoil is not “a graph with three circles intersecting.” It
is an embedded `(2,3)` torus-knot slope, and its crossings arise from projection. The correct
Holonics reading is therefore:

```text
graph projection → intersecting support domains → winding/holonomy lift
→ torus-knot boundary receiver.
```

[proved-standard; formal-checked] The repository's `HolonicTorusKnots.lean` constructs the genuine
geometric two-torus, an integral slope map, its canonical lift, and the embedding of coprime
slopes. It also proves that an odd `m`-half-twist band has coprime boundary slope `(2,m)`.
The executable `BandReading` in
[`traversible_chain.rs`](../../crates/holonic-engine/src/traversible_chain.rs) retains the
per-junction twist list and derives:

```text
m = 3  →  (2,3) torus knot  →  trefoil boundary.
```

That is stronger than a visual resemblance: the twist count, direction and winding are retained.
The render should therefore show a trefoil-like braid as a **phase/winding receiver** of the
intersecting torus supports, not claim that every graph crossing is already a topological knot.

## Möbius strips, Möbius shorts and Rubik orientation

[established-bounded; source-inspected] The [half-twist synthesis](2026-08-16_THE_JUNCTION_IS_A_HALF_TWIST_AND_A_MODULUS_IS_WHAT_A_DECLARED_QUOTIENT_RETAINS.md)
distinguishes the Möbius strip from Möbius shorts and makes the junction's direction load-bearing.
The repository keeps the per-junction inversion list; orientability is derived from twist parity,
not stored as a replacement for the passages.

[interpretation] This is a natural visualization companion for Rubik's orientation fibres:

- a Rubik edge orientation has a mod-2 face;
- a Rubik corner orientation has a mod-3 face;
- a torus phase has an integral winding face;
- a Möbius seam has an orientation-reversal face;
- the full state retains the source passages that produced all of them.

These are not one theorem or one modulus. They are distinct receiver readings over a common
configuration carrier. A half-twist may model an orientation-reversing transition in a lifted
atlas, but it does not prove that the cube's edge-orientation law *is* a Möbius band. The map must
be declared and its residual checked.

The visual lift therefore uses three torus supports with crossing/phase nodes and a trefoil braid;
Möbius structure appears as an optional orientation-reversing junction, not as a replacement for
the cube group.

## Rubik, chess and anticipation

[definition] Rubik navigation is a fixed-generator, invertible, target-directed problem. Once the
state, face-turn family and metric are declared, the exact value function and descending policy
can be certified. This is a Cayley/Schreier navigation face.

[definition] Chess is different. A position carries turn, active piece incidence, legal-action
conditions and rule-relevant history/rights. A predictive continuation has alternating control:

```text
∃ our move, ∀ admitted replies, continuation condition.
```

It is not a shortest path through one fixed group, and an opponent probability model is not the
same thing as the universal reply quantifier. Captures, attachments and separations change the
active incidence and therefore change the available generators.

[project-postulate] The shared predictive relation is not “evaluate a board and choose the
largest scalar.” It is:

```text
current face + source/conditions
→ admitted generator family
→ successor faces / opponent replies
→ future receiver separation or agreement
→ selected continuation with source retained.
```

Rubik is the clean deterministic case. Chess is the branching/adversarial case. Both are
navigation through continuing faces, and both fit the tube statement that prediction asks when a
tube transports and why. The source map, phase, branch, material and unresolved future family
must survive before any magnitude or extremum receiver.

## What the visualization shows

[established-bounded; visualization] The accompanying visual keeps the reference render's
composition but makes the abstraction explicit:

1. a cube state appears as a complete receiver face;
2. its relations are shown as three overlapping circle families;
3. the projection is lifted to three torus-support ellipses;
4. a trefoil-like phase braid carries the winding receiver;
5. a phase slider animates the cyclic motion while retaining the displayed face label.

The visual is intentionally a receiver, not a proof. Its central claim is the direction of lift:

```text
state face → graph projection → torus/holonomy carrier → trefoil phase face.
```

## Scope and non-claims

[established-bounded; source-inspected] This synthesis does not claim that the social-media image
contains a complete Rubik state graph, that three circles uniquely determine a torus embedding,
or that the displayed crossings prove a trefoil. The exact repository return is the physically
derived face-turn quotient and its full-state fibre; the torus and trefoil relation is the
mathematical lift used to retain cyclic phase, winding, intersections and orientation.

[definition] No separate Rubik, chess, trefoil or torus engine is founded here. The existing
`structure_group`, `TransportWord`, `ReceiverHistoryCompression`, `HolonicTorusKnots`,
`BandReading`, `JointReceiverDescent`, `continuing_tube` and shared HNN carrier remain the owners.
This deposit synthesizes their relation and records the visualization as an exterior receiver.

[source-audit 2026-09-19 335f296e] Prior-art found the genuine Rubik face-turn quotient,
God's-Algorithm/navigation records, chess configuration analysis, torus phase owners, Möbius
shorts/half-twist records, and trefoil boundary readings. The current user request composes those
owners; it does not license claiming a missing Rubik or knot construction.
