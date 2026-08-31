# The holon carrier and the Hodge prism

## Scope

This record deposits the exterior Lean construction which consolidates several previously separate
mathematical bodies without changing the production roadmap.  It records checked declarations,
their exact limits, and the next Hodge seam.

## The carrier

[proved-derived; formal-checked] `ElementaryHolonics/Foundation/Holon.lean` defines

```text
Holon Source Target Face
```

as an arbitrary occurrence population with an addressed source, addressed target, and returned
receiver face.  It is not defined to be a serial chain.

[proved-derived; formal-checked] The following incidence bodies are constructed from that owner:

1. serial interaction is the pullback of adjacent occurrence populations and retains the exact
   joining equality;
2. a Cartesian body retains the complete pair population and its receiver fibre is exactly the
   product of the two component reconstruction fibres;
3. a self-diagonal presents one occurrence on two axes without inventing a second occurrence; and
4. an off-diagonal pair retains the proof that its two occurrences differ.

[project-postulate] The Cartesian construction alone does not assert execution independence.
Interchange, resource separation, and apparatus residency remain separate theorem obligations.

[proved-derived; formal-checked] `BoundaryHolon` adds an additive current and a constitutive law

```text
boundary(receive occurrence) = target occurrence - source occurrence.
```

For every finite occurrence population, `BoundaryHolon.boundary_totalCurrent` proves exactly

```text
boundary(sum local currents) = sum outgoing faces - sum incoming faces.
```

This is the generic finite local-to-global return.  It does not infer a source-specific
constitutive law.

## Complex winding and the Parametron

[proved-derived; formal-checked] `HolonicParametron.lean` treats logarithmic winding branches as
occurrences.  For every `n : Z`,

```text
log_n(i) = (pi/2 + 2*pi*n) i,
exp(log_n(i)) = i,
i^i at branch n = exp(-pi/2 - 2*pi*n).
```

The exponential receiver therefore collapses every integer branch to one `i` face, while
`logarithmicWindingReconstruction` proves that the complete reconstruction fibre over that face is
exactly `Z`.  The subsequent multiplication-by-`i`/exponential receiver reopens the branches into
distinct positive real complex faces.  `iPowerIChartHolon` retains the logarithmic current, the
collapsed exponential face, and the reopened power current together.

[proved-derived; formal-checked] `HolonicComplexParametron.lean` realizes an arbitrary finite
oriented branch lattice as a holon whose receiver retains complex drive current and diagonal
constitutive contribution.  The full mutual body has occurrence population `Branch x Branch`.
The separately constructed diagonal body reuses one branch on both incidence axes, and its
receiver is exactly the `(branch, branch)` face of the full mutual body.  The proof-carrying
ordered off-diagonal body retains two unequal branches without quotienting their order.  The full
mutual receiver sum is proved to partition exactly into these diagonal and off-diagonal
populations.  Thus the formal Parametron contains serial, complex, diagonal, and off-diagonal
readings before its later binary phase-lock quotient.

## Hodge realization

[proved-derived; formal-checked] `HodgeTriangleHomotopyPrism.lean` realizes every refined triangle
cell as one `BoundaryHolon` occurrence.  Its incoming face is the weighted refined source simplex;
its outgoing face retains the weighted affine-label simplex and lateral face current; its received
current is the weighted singular prism.  The local constitutive law is the singular-prism boundary
identity.

[proved-derived; formal-checked] `trianglePrismHolon_returns_globalBoundary` applies the generic
finite holon theorem and returns

```text
boundary(refinedPrismCurrent)
  = refinedPrismUpperCurrent - refinedPrismLowerCurrent
      + refinedPrismLateralCurrent.
```

For a source cycle, the separately proved lateral cancellation and refinement identity reduce this
to

```text
boundary(refinedPrismCurrent)
  = rawAffineLabelUpperCurrent - iteratedBarycentricRefinement(sourceCycle).
```

[open] The bounded Hodge model's next exact seam is repeated-label normalization: identify the raw
affine-label upper singular current, including degenerate repeated-label simplices and orientation,
with the canonical point-carry/face realization already reduced to the radial fundamental current.
This closes the finite sphere-product ruling model passage.  The official Hodge receiver still
requires an independent smooth-projective cohomology and cycle-class realization.

## Shared Millennium use

[project-postulate] The carrier removes a repeated formal encoding seam, not any source theorem.
The same owner can receive Hodge singular cells, Navier--Stokes spacetime/scale cells, Yang--Mills
plaquette/scale cells, and arithmetic local-factor occurrences only after each line supplies its
typed source/target maps, constitutive current, receiver, and reconstruction fibre.  A pivot is
licensed when one of those source maps is constructed or a proposed receiver is falsified; a
renaming into `Holon` is not itself progress toward an official receiver.

## Verification

[proved-derived; formal-checked] Lean 4.33 builds passed for:

```text
ElementaryHolonics.Foundation.Holon
ElementaryHolonics.Millennium.HolonicParametron
ElementaryHolonics.Millennium.HolonicComplexParametron
ElementaryHolonics.Millennium.HodgeTriangleHomotopyPrism
```

The printed dependencies of the deposited theorems contain only Lean's ordinary logical
foundations (`propext`, `Classical.choice`, and `Quot.sound` where inherited).  No `sorry` or new
axiom was introduced.
