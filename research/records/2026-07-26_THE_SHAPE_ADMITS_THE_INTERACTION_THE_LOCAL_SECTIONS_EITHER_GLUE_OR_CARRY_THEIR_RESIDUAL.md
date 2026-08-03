# THE SHAPE ADMITS THE INTERACTION; THE LOCAL SECTIONS EITHER GLUE OR CARRY THEIR RESIDUAL

**2026-07-26 · GRAPHICS/PHYSICS ENGINE ROUND A / BUILT / EXACT CPU /
RECEIVER CELL MIGRATED / 23 TESTS PASS / BOUNDED EXAMPLE PASSES / NO BEVY /
NO FLOAT / NO VULKAN / NO SOMA INTEGRATION**

## 1. Question and stop

The Round A question was whether the standing exact receiver cell could become
one actual receiver-indexed causal construction rather than adjacent
`CausalDiagram`, `Construction`, and `trace_receiver` utilities.

The stopping condition required:

1. one explicit evolution shape;
2. distinct exact realizations of that shape;
3. explicit interaction rather than juxtaposition-as-contact;
4. structured copy, retention, and departure laws;
5. two receiver-local fibers;
6. one lawful overlap assembly and one exact obstruction; and
7. the prior exact crossing receipt unchanged.

All seven are now present.

## 2. The production structures

`crates/holonic-engine` now carries:

- `EvolutionShape`: typed boundary species, reusable laws, unfolded
  occurrences, occurrence ports, causal chronology, and admitted
  `InteractionPattern`s;
- `ReceiverProgram`: an executable assignment of every shape occurrence to
  ray emission, one caused triangle test, or crossing-fiber assembly;
- `RealizationWitness`: complete boundary and law carriers for an exact
  domain realization;
- `LogicalRealization` and `ReceiverRealization`: separate realizations of
  the same shape;
- `ParameterEcology`: copy, retention, and departure laws which cannot be
  bypassed merely because the Rust value implements `Clone`;
- `ReceiverFiber` and `LocalSection`: exact receiver-local observations;
- `assemble_cover`: an arbitrary finite connected cover whose pairwise
  overlaps compare only after both sections transport into one declared
  common face;
- `BoundedAssembly`: compatible transported local sections over a named
  boundary;
- `GluingObstruction`: the oriented residual when a claimed overlap does not
  commute; and
- `ExactValue`: integers, exact ratios, Sturm-isolated algebraic roots, exact
  enclosures derived from supported convergent-series tail certificates, and
  structural exact expressions with `less/equal/greater/OPEN` comparison.

No structure above constructs a total scene. The bounded assembly retains the
two receivers and two source regions which compose it.

## 3. Interaction owns contact

An evolution shape may contain available occurrences without any relationship
between them. They remain one co-present antichain until an explicit
interaction binds an output port to a boundary-compatible input port.

`InteractionPattern` carries:

- the common boundary species;
- the exact source and target occurrence ports;
- directed hand;
- whether the bond carries precedence or is same-predecessor co-presence; and
- an optional receiver scope.

The complete interaction is checked before its chronology commits. A label
cannot make two distinct boundary species compatible. A failed bond leaves the
shape unchanged.

## 4. The receiver realization is causal

The migrated cell has four occurrences:

\[
\text{ray}
\longrightarrow
\{\text{near triangle test},\text{far triangle test}\}
\longrightarrow
\text{ordered plural fiber}.
\]

Two explicit interaction patterns carry those four bonds. The
`ReceiverProgram` binds each triangle-test occurrence to the actual
source-founded `EntityId`. It validates that:

- every shape occurrence has exactly one executable operation;
- one abstract law cannot silently realize incompatible operation species;
- every tested entity exists and is a triangle;
- the ray and every test are carried by admitted interactions;
- each assembly input is carried by an admitted interaction; and
- the tests occur causally between ray emission and assembly.

Only the entity population selected by this validated active subdiagram enters
`trace_receiver_entities`. This is not an observer filter or a second scene.
It is the geometric realization of the supplied shape.

## 5. Exact local assembly

The central and parallel receivers each retain a complete local
`PixelFiber`. Their depth, ray, and orientation remain receiver-relative.

For one declared overlap, the comparison doctrine transports a pixel fiber
back to the ordered source entity and barycentric source-face point. The two
center pixels agree and assemble over that named overlap. A foil which claims
that opposed pixel addresses denote one source point returns
`GluingObstruction` with both transported faces. No preferred receiver erases
the difference.

For a finite cover, pairwise face equality is not enough. The engine also
follows the address correspondences around every overlap component. If a
cycle returns to a different address in the same receiver-local section, it
returns an `AddressHolonomy` residual even when every compared face has the
same value. A three-receiver foil closes this exact obstruction.

Therefore the engine now distinguishes:

\[
\text{different local presentations of one transported source face}
\]

from

\[
\text{a false overlap claim whose residual remains informative}.
\]

## 6. Exact number carrier

An algebraic number is a defining integer polynomial plus a strict rational
interval. The constructor computes the Sturm sequence and admits the value
only when the interval contains exactly one real root. Algebraic equality and
order use the root's Sturm variation address; overlap of intervals alone is
not treated as equality.

A certified series carries a finite exact partial sum and one typed tail
certificate:

- an absolute geometric tail bound;
- an alternating monotone tail; or
- an exact closed tail.

The engine checks each certificate's numeric admissibility and derives its
exact rational enclosure. The source law still owes the stated fact that its
omitted terms satisfy the geometric bound or alternating-monotone condition;
the carrier does not turn that premise into an oracle. Unsupported
comparisons remain `OPEN`; no decimal or tolerance enters.

## 7. Exact acceptance

Command:

```text
cargo test -p holonic-engine --all-targets
```

Result: 23 passed, 0 failed.

Command:

```text
cargo run -p holonic-engine --example exact_receiver
```

The migrated central realization is exactly equal to the preceding direct
`trace_receiver` receipt:

- aperture: \(5\times3\), exact span \(2\times2\);
- 15 receiver rays;
- 30 admitted triangle incidences;
- 9 exact crossings;
- causal shape: ray, two co-present tests, plural join;
- two geometric receiver realizations;
- one logical-resource realization;
- center overlap: assembled;
- false opposed-address overlap: obstructed; and
- singular event copy: refused.

The exact crossing paths remain:

```text
(2,0): t=2:[near], t=3:[far]
(1,1): t=2:[near]
(2,1): t=2:[near], t=3:[far]
(3,1): t=2:[near]
(1,2): t=3:[far]
(2,2): t=3:[far]
(3,2): t=3:[far]
```

The equal receipt, complete paths, bounded gluing, and obstruction are the
acceptance evidence. The scalar counts only describe their finite physical
cell.

## 8. Boundary

Round A does not establish native conics, simplicial cell complexes, root
fibers for general implicit surfaces, hinge propagation, dynamics,
conservation, display presentation, multicore execution, or Vulkan. It does
not schedule those works.

The result establishes the reusable categorical and exact-arithmetic carrier
which those later laws must inhabit.
