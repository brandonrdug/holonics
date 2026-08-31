# The unicursal stroke is an oriented current, the star fan cancels its internal spokes, and a visible cycle cannot be a boundary

**Date:** 2026-08-26  
**Scope:** exterior Lean theorem cartography; this record does not schedule the production engine

## Question returned

[historical] Brandon's direct messages repeatedly connected a unicursal stroke with causal
lineage, voltage difference, current, heat export, star geometry, knot crossings, and the
local-to-global passage.  The 2026-08-26 prompt sharpened the request: retain the ordered stroke,
explain why the apparently reversed fundamental-theorem sign is an outward-loss orientation, and
test whether the center-constrained star supplies the missing Hodge geometry.

[definition] The construction separates three objects which a final drawing can hide:

1. the ordered one-dimensional stroke and all of its edge occurrences;
2. the two-dimensional fan whose local triangle boundaries glue to that stroke; and
3. a receiver which annihilates higher boundaries while returning a nonzero difference on a
   selected cycle.

The first two objects do not automatically supply the third.

[historical] The authorized evidence audit used `/home/b/.codex/history.jsonl` (notably entries
279, 298, 322, 369, 626, 662, 674, 717, 764, 1032, 1209, and 1241) and
`/home/b/.claude/history.jsonl` (notably entries 11210--11232, 12081, 12149, 14135, 14145,
14321, 14353--14354, 14460--14465, and 14543--14606).  Those messages consistently pose current,
lineage, crossing, heat/diffusion, knot, pin/standing-wave, and local-to-global hypotheses.  They
are reasoning provenance; only the constructions below receive theorem grades.

## Owner-absence audit

[established-bounded; formal-checked] `Tesseract.lean` owns one fixed Gray-code Hamiltonian cycle,
but `theCycleLeavesFourEdges` proves that it is not an Euler traversal of the cube graph.
`GraphTrace.lean` owns bounded non-backtracking walks on the tetrahedral graph.  The polygon,
torus, induction, and Hodge files own several source-specific boundary/current laws.  Before this
deed there was no source-neutral owner simultaneously retaining an arbitrary ordered edge word,
its exact potential integral, the reverse loss chart, and the center-fan gluing law.

## The checked unicursal-current return

[proved-derived; formal-checked] `HolonicUnicursalCurrent.lean` constructs:

- signed vertex and directed-edge populations over `ℤ`;
- the antisymmetric current
  `orientedEdgeCurrent source target`, including reversal and degenerate-edge laws;
- `StrokeEdge`, `endpoint`, and `edgeWord`, so the occurrence population and every join remain
  present rather than being replaced by the final picture;
- exact word composition at the actual endpoint;
- `strokeCurrent` as the sum of the retained edge occurrences;
- the finite fundamental theorem
  `strokeAction potential start tail = potential (endpoint start tail) - potential start`;
- the outward-loss receiver
  `outwardLoss = potential start - potential finish = -strokeAction`;
- oriented triangular faces and their zero vertex-boundary return;
- `fanTriangles` and `fanBoundaryCurrent`, with exact cancellation of every internal center spoke;
- for a closed stroke, equality between its edge current and the boundary of its center fan; and
- the conventional five-vertex pentagram word `[0,2,4,1,3,0]`, including closure, five edge
  occurrences, one visit to every vertex before return, zero potential return, and its exact fan
  boundary.

[proved-derived; formal-checked] The reversed boundary expression is therefore not a reversed or
approximate fundamental theorem.  It is the same addressed passage read by the oppositely oriented
receiver.  Calling that reading thermal loss additionally requires a source-specific storage,
constitutive, chronology, and boundary law; the sign theorem itself is exact and source-neutral.

## The shared nonboundary instrument

[proved-derived; formal-checked] `Foundation/BoundaryReceiver.lean` extracts the common receiver
law.  For additive maps

```text
boundary : Y ->+ X
receiver : X ->+ Z,
```

if `receiver (boundary source) = 0` for every source while `receiver cycle != 0`, then
`cycle` is not in the image of `boundary`.  Both a composite-zero and a pointwise-zero interface
are returned.  The zero receiver is proved unable to satisfy the visibility premise and is the
minimal negative control.

[proved-derived; formal-checked] Three checked source passages now consume this one owner:

1. `HodgeSphereFundamentalDetector.lean` proves that any normalized singular degree-two detector
   separates `sphereFundamentalCandidate` from the image of the singular three-boundary;
2. `HolonicPolygonalTorusCarrier.lean` uses its concrete dual cross-section cut to prove that a
   longitudinal winding is not a cellular two-boundary; and
3. `HolonicFourTorusCarrier.lean` uses each concrete dual-axis cut to prove that the corresponding
   axis winding is not a cellular two-boundary.

The torus passages construct their receivers and nonzero readings unconditionally.  The Hodge
passage is conditional on the still-unconstructed singular detector; that premise is not hidden by
the shared theorem.

## The star is also the falsifier

[counterexample; formal-checked] `closed_fanBoundaryCurrent_eq_stroke` and
`pentagram_is_fanBoundary` prove that the filled planar star is a boundary.  Consequently its
unicursality, closure, fivefold word, or visible central fan cannot establish that the represented
homology class is nonzero.  This is useful information: it rejects the tempting promotion from
“one stroke closes” to “the stroke or filling detects a nontrivial Hodge class.”

[open] Affine crossing points, over/under information, knot type, angle data, metric lengths, and a
polynomial or quintic realization require an additional geometric source map.  They are not
recoverable from the abstract vertex word or its zero exterior boundary alone.  The pentagram
currently certifies a five-address current and fan-gluing law, not a theorem about general
quintics, Fermat, string dimension, or knot equivalence.

## The finite tetrahedral target closes the free detector premise

[proved-derived; formal-checked] `HodgeTetrahedralChainComplex.lean` now adds the four addressed
vertices to the already constructed four faces and six edges.  Each edge boundary is proved to be
its terminal vertex minus its initial vertex; every face boundary has zero vertex boundary; the
resulting rational `C₂ -> C₁ -> C₀` passage is packaged as a genuine `ChainComplex`; and every
carrier above degree two is zero.

[proved-derived; formal-checked] `HodgeTetrahedralReduction.lean` composes that target with the
existing singular source.  For every genuine chain map

```text
reduction : SphereSingularChainComplex ⟶ tetrahedralChainComplex,
```

the chain-map square and the zero target differential in degree `3 -> 2` prove

```text
SphereSingularChainComplex.d 3 2 ≫ reduction.f 2 = 0.
```

Thus the detector's boundary-annihilation law is no longer an independent hypothesis.  If the
same map returns the exact normalization square

```text
faceRealizationMorphism ≫ reduction.f 2 = 𝟙 TetrahedralFaceModule,
```

then Lean constructs `TetrahedralDegreeTwoReceiver`, proves the sphere fundamental class nonzero,
and proves both the tetrahedral realization and the two-ruling map injective.

[proved-derived; formal-checked] `HodgeTetrahedralRealizationChainMap.lean` closes the other
direction at every finite dimension.  It constructs the four singular vertex occurrences, proves
their equality from equality of the complete three-stage face-inclusion words, proves each
realized edge has terminal-minus-initial boundary, and assembles the four faces, six edges, and
four vertices into one genuine chain map

```text
tetrahedralChainComplex ⟶ SphereSingularChainComplex.
```

This is the exact geometric inclusion which the future reduction must retract.  It retains the
edge and vertex seams rather than treating the four face images as unrelated degree-two values.

## The local-to-global carrier law is now checked

[proved-derived; formal-checked] `HodgeTetrahedralCarrierAssembly.lean` supplies the requested
composition law.  `FaceNaturalCarrier` assigns a finite tetrahedral chain to every addressed
singular simplex at every degree and requires the local equation

```text
∂ carry(σ) = sum_i (-1)^i carry(face_i σ).
```

Because a rational singular-chain module is the coproduct of its addressed simplex generators,
Lean proves that this local law linearizes to a genuine global chain map.  If the four radial face
occurrences return to their four matching finite face atoms, the same theorem proves the entire
degree-two realization/reduction square is the identity and constructs the normalized detector.

[proved-derived; formal-checked] This is a precise local-to-global theorem rather than a slogan:
local carrier values alone do not compose; their complete alternating face populations must agree.
The seam law is exactly the obstruction.  The remaining construction is now an inhabitant of
`FaceNaturalCarrier` with four normalization equations.

## Barycentric navigation return

[proved-standard; external-source] Barycentric coordinates present a point by three vertex weights;
after the exact normalization `t₁+t₂+t₃=1`, they are the normalized areas of the three
opposite subtriangles.  Ceva's directed product law characterizes three cevians meeting at one
point.  Menelaus' signed product characterizes one transversal crossing the three sides, with a
sine-weighted spherical form.  Routh retains the central triangle's exact area when the three
currents do not converge.  Sources:

- https://mathworld.wolfram.com/BarycentricCoordinates.html
- https://mathworld.wolfram.com/ArealCoordinates.html
- https://mathworld.wolfram.com/CevasTheorem.html
- https://mathworld.wolfram.com/MenelausTheorem.html
- https://mathworld.wolfram.com/RouthsTheorem.html
- https://mathworld.wolfram.com/SphericalTriangle.html

[proved-derived; formal-checked] The Hodge subdivision owner is already an exact bounded
instantiation of that navigation calculus.  The three weights are a complete affine
reconstruction fibre over fixed landmarks; each address pair selects one of six successor cells;
word concatenation is serial transport; every seam is returned; and the `(4/9)^n` law forces all
words into declared receiver apertures without losing their source maps.

[project-postulate] A moving-target Eros lift should retain the landmark body, source and target
world-lines, normalized affine weights, admissible path family, action/cost quantity line, emitted
deed, returned world consequence, morphology delta, and route reconstruction fibre.  Ceva is the
local reconvergence receiver, Menelaus is the boundary-crossing receiver, and Routh's central area
is a residual aperture.  Learned navigation is established only when the returned consequence
changes rested morphology and later current uses that change after source-detached remount.

## External exact provenance for the remaining construction

[historical] The Lean 3 repository `Shamrock-Frost/BrouwerFixedPoint` contains a checked general
sphere-homology proof ending in `nth_homology_of_n_sphere`.  Its source chain proceeds through
standard-simplex boundary geometry, relative homology, the connecting homomorphism, barycentric
subdivision, cover subcomplexes, excision, and contractibility.  The complete imported source is
not directly compatible with current Lean 4 and contains roughly 15,800 reachable local lines;
the relevant missing mechanisms are subdivision, its chain homotopy to the identity, and the
cover/excision passage.  Current Mathlib already owns much of the categorical homology-sequence
machinery, so the source-faithful project port should specialize to `S²` and reuse the finite
tetrahedral owners constructed here rather than porting the all-dimensional theorem wholesale.

## The first geometric subdivision owner

[proved-derived; formal-checked] `HodgeStellarSubdivision.lean` constructs the literal
two-dimensional successor of the unicursal star.  Its centre is the exact equal-weight point of
the standard triangle.  Three affine cone maps join that centre to the three addressed boundary
edges.  Lean proves the three internal spokes occur in oppositely oriented pairs, so the boundary
of the signed subtriangle population is exactly the boundary of the original singular simplex.

[proved-derived; formal-checked] The construction linearizes over the complete singular-chain
coproduct.  Every finite iteration returns exactly the original exterior boundary.  This is a
uniform scale theorem: refinement grows the internal occurrence population while the declared
seam receiver remains invariant.

[open] The next dimension is forced.  A normalized tetrahedral carrier must satisfy the
degree-three equation: the alternating carried two-faces of every singular three-simplex cancel.
The next owner therefore cones/subdivides addressed three-simplices, proves the chain homotopy, and
establishes cover-smallness before any finite face is assigned.

[proved-derived; formal-checked] `HodgeTetrahedralStellarSubdivision.lean` now closes the first
part of that next dimension.  It constructs four actual affine tetrahedral cone maps, proves all
six internal triangular seams pair with opposite orientations, proves their signed population has
the original singular three-simplex boundary, and proves the same exterior return after every
finite iteration.

[proved-derived; formal-checked] `HodgeStellarSubdivisionHomotopy.lean` closes that recursive
residual.  It cones each of the three stellar subtriangles and the identity triangle to the exact
source barycentre, proves the six coned edge populations cancel in addressed opposite pairs, and
constructs `P₂` with `∂P₂ = S₂ - id`.  The corrected degree-three current
`S₃rec = S₃ + ∂P₂` therefore satisfies the exact chain-map square `S₃rec∂ = ∂S₂`.  Its induction
theorem proves the same synchronized boundary equality at every finite refinement scale.

[counterexample; formal-checked] `HodgeStellarSubdivisionMeshObstruction.lean` proves that the
three-cone operator cannot close that geometric edge.  Its all-zero descendant branch fixes both
endpoints of one exterior edge at every finite scale.  Two exact open coordinate apertures cover
the source triangle, but neither contains both endpoints, so the persistent branch is never
subordinate.  The algebraic chain homotopy remains valid; cover-smallness was the false promotion.

[proved-derived; formal-checked] The edge-refining successor now exists.  The degree-one owner
splits every singular edge at its exact midpoint, cancels the paired midpoint, commutes with the
endpoint boundary, and contracts source parameter distance by exactly `1/2`.  The degree-two owner
constructs six barycentric subtriangles, cancels all midpoint and radial seams, commutes with the
degree-one subdivision, and contracts squared source distance by exactly `(4/9)^n` along every
addressed word.

[proved-derived; formal-checked] Compactness and the metric Lebesgue-number theorem now convert the
exact contraction into open-cover smallness for every singular `S²` simplex.  Retained suffix
factorization proves every deeper descendant remains small, and a finite occurrence family admits
one synchronized depth.  No sample point assigns a face and no floating mesh diameter occurs.

[proved-derived; formal-checked] The first recursive homotopy is also explicit.  A midpoint sweep,
a folded triangle retaining the reversed parametrization, and a constant triangle retaining its
degenerate seam return `P₁∂ = S₁-id`.  Singular-chain orientation is therefore proved by filled
source occurrences rather than by identifying a reversed map with a negative coefficient.

[proved-derived; formal-checked] The degree-two residual is now constructed rather than described:
`R₂ = S₂-id-∂P₁`.  Its complete boundary is proved zero from the two chain squares and the
degree-one prism.  `BarycentricDegreeTwoFilling` exposes exactly one remaining field
`P₂∂=R₂`, and Lean proves that every inhabitant automatically corrects the degree-three current
to satisfy `S₃rec∂=∂S₂`.  No lower-dimensional sign or compatibility premise remains hidden.

[proved-derived; formal-checked] `HodgeBarycentricAffineSourceComplex.lean` now inhabits that
field.  It retains free rational chains on the actual affine source maps, proves the six
barycentric, identity, and nine prism occurrences are closed before any receiver simplex can
collapse them, cones the complete source current to one common barycentric apex, proves
`P₂∂=R₂`, and returns the unconditional recursive degree-three square
`S₃rec∂=∂S₂`.

[proved-derived; formal-checked] `HodgeBarycentricChainSupport.lean` now exposes the actual finite
support of every rational singular chain, retains every exact coefficient and simplex address,
reconstructs the original categorical chain from that support, and returns one cover-small depth
for all descendants of every support occurrence.

[open] Combine the checked common-apex filling and actual-support synchronization into the
normalized cover-small `FaceNaturalCarrier`.

## Exact Hodge residual after the deed

[open] The immediate source-specific construction is now one `FaceNaturalCarrier`, normalized on
the four radial faces.  It cannot be supplied by assigning a seam-crossing singular simplex to
whichever face contains a sampled point.  It owes an exact subdivision/carrier law, face
compatibility, and the retained chart/seam reconstruction testimony.  After that, the
remaining source passage is surjectivity/comparison

```text
CellularH2 ≃ₗ[ℚ] RationalSingularHomology 2 sphereProductTopCat,
```

followed by the cohomological dual and rational `(1,1)` typing.

## Instrument receipt

[definition] The returned receipt is:

| Field | Return |
|---|---|
| source occurrence | arbitrary ordered vertex tail; concrete polygonal torus, four-torus, and detector-indexed sphere sources |
| new owner | exact unicursal current/fan gluing, the source-neutral visible-cycle/nonboundary theorem, the finite tetrahedral chain target, its geometric inclusion chain map, face-natural local-to-global carrier assembly, geometric stellar subdivision, and its explicit recursive chain homotopy |
| commuting law | local potential differences telescope to the exterior boundary; triangle spokes and coned edge seams cancel; each admitted receiver kills the relevant boundary map; nested face words preserve vertex identity; face-natural local carriers assemble to a global reduction; `∂P₂=S₂-id`; `S₃rec∂=∂S₂`; and every finite synchronized refinement preserves that exact square |
| retained fibre | every ordered edge occurrence remains in `edgeWord`; receiver kernels are not collapsed by the theorem |
| quantifier widened | the nonboundary argument is generalized from repeated source-local contradiction proofs to arbitrary additive boundary/receiver maps |
| hypothesis exposed | Hodge owes one normalized `FaceNaturalCarrier`; its global chain map, retraction square, and boundary annihilation are now derived |
| independent consequence | polygonal longitude and four-torus axis nonboundary theorems factor through the same owner |
| official consequence | none yet; every official Millennium receiver remains open |
| shortest obstruction | combine the inhabited source-faithful `BarycentricDegreeTwoFilling` with the checked actual-chain support and synchronized cover-small scale to construct the normalized carrier |

## Verification

[established-bounded; implemented-exact; measured] Focused Lean checks passed for
`BoundaryReceiver.lean`, `HolonicUnicursalCurrent.lean`, `HolonicPolygonalTorusCarrier.lean`,
`HolonicFourTorusCarrier.lean`, `HodgeSphereFundamentalDetector.lean`,
`HodgeTetrahedralChainComplex.lean`, `HodgeTetrahedralRealizationChainMap.lean`,
`HodgeTetrahedralReduction.lean`, `HodgeTetrahedralCarrierAssembly.lean`, and
`HodgeStellarSubdivision.lean`, `HodgeTetrahedralStellarSubdivision.lean`, and
`HodgeStellarSubdivisionHomotopy.lean`, and
`HodgeStellarSubdivisionMeshObstruction.lean`, `HodgeBarycentricEdgeSubdivision.lean`,
`HodgeBarycentricTriangleSubdivision.lean`, `HodgeBarycentricCoverSmallness.lean`, and
`HodgeBarycentricSubdivisionHomotopy.lean`.  The aggregate build
is rerun after every new aggregate import.  Their audits contain no new project-local axiom or
`sorryAx`; only standard Lean/Mathlib axioms reported by `#print axioms` remain.
