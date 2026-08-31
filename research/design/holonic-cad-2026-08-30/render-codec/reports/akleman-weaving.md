# Akleman et al. — Weaving, Rotation Systems, and Discrete Gauss–Bonnet

Source PDFs (pdftotext -layout) in `scratchpad/pdfs/`. **`akleman-ijsm99.pdf` is image-only —
pdftotext produced 0 bytes of text. Skipped; no extraction possible without OCR.** Page numbers below
are the PDF's own physical page order, confirmed against `\f` form-feed boundaries.

---

## 1. akleman-siggraph09.txt — "Cyclic Plain-Weaving on Polygonal Mesh Surfaces with Graph Rotation Systems" (Akleman, Chen, Xing, Gross; SIGGRAPH 2009), 8 pages

### Definitions

**Cyclic plain-weaving.** "a cyclic plain-weaving on an orientable surface S is a projection of a link
L on S, such that (1) there are no triple intersections at a single point on S, and (2) a traversal of
the image on S of each component of L goes over and under alternatingly as it crosses the images of
other components or of itself." (p.2)

**Graph rotation system.** "a graph rotation system uniquely determines a graph embedding on an
orientable or non-orientable surface, and thus uniquely determines the surface." (p.2, citing Edmonds
1960)

**Edge twisting / extended rotation system.** "An important concept in graph rotation systems is edge
twisting. An edge has type 0 if it is untwisted and type 1 if it is twisted." (p.2) Mechanically: "each
edge E in the graph G can be regarded as a flat paper strip... If we implement the operation 'twisting
E' by standing on one end of the paper strip E and twisting the other end of E in clockwise direction
by 180°... then the edge twisting operation corresponds to changing the face boundary walks in the
graph rotation system." (p.2) Fig.3 shows an untwisted vs. a twisted edge.

**Over/under alternation guarantee — Theorem 2.1.** "Let ρ0(G) be a graph rotation system with no
twisted edges... Let A be an arbitrary subset of edges of G. If we twist all edges in A, then the
resulting graph rotation system induces a cyclic plain-weaving on Sh." (p.3) Proof deferred to a
companion tech report.

**Half-edges.** "let Ei,0 and Ei,1 denote the over and under half-edges (in the sense of [Mantyla
1988])" (p.3). Mesh preconditions: "every vertex has valence at least 3, and every face has at least
three sides... every edge has positive length" (p.3).

**Gap valence / Schlafli-like notation.** "The number of ribbons around a gap defines the shape of the
gap. We call this the valence of the gap... the four gaps around the ribbon piece have valences d0,
d1, d2, and d3... a Schlafli-like notation with a four-tuple (d0, d1, d2, d3)." (p.5)

### Notation / Equations

- Half-edge displaced position: p_i,j = (p¹_i,j + p²_i,j)/2 + (−1)^j·h·e_i·n⃗_i, where h is a width
  parameter, e_i the edge length, n⃗_i the edge normal, (−1)^j = +1 for the over strand (p.4).
- Face-walk example K1 = {E0,0,E1,0,E2,0,E3,0,E6,1,E5,1,E4,1,E3,1} → control polygon P1 =
  {p0,0,p1,0,p2,0,p3,0,p6,1,p5,1,p4,1,p3,1} (p.3–4).
- Half-edge plane: n⃗_i·(p − p_i,j) = 0 (p.4).
- Pattern tuples: (6,3,6,3) triaxial, (6,4,3,4) ring, (4,4,4,4) basic quad weave (p.5–6).

### Construction: Face-Tracing Algorithm (p.2)

```
Subroutine FaceTrace(⟨u0,w0⟩, t0):
1. trace ⟨u0,w0⟩; 2. t = t0 + type([u0,w0]) mod 2;
3. ⟨u,w⟩ = Next(⟨w0,u0⟩,t); 4. while ⟨u,w⟩≠⟨u0,w0⟩ and t≠t0: trace ⟨u,w⟩;
   t = t + type([u,w]) mod 2; ⟨u,w⟩ = Next(⟨w,u⟩,t).
Trace-All-Faces(ρ(G)): while an untraced face corner exists, call FaceTrace on it.
```
Returns the boundary-walk cycles = the link projected on the surface.

### Construction: Projection method (PR), "four main steps" (p.3–4)

1. **Construct PR Control Polygons**: trace all face walks (Face-Tracing); displace each half-edge to
   p_i,j; replace walk edges with these positions → non-self-intersecting control polygon.
2. **Construct PR Control Ribbons**: assign a plane to each half-edge; build a non-planar quadrilateral
   "edge-region" per edge (2 endpoints + 2 adjacent face centers); project it onto both half-edge
   planes; take a bilinear fractional sub-quad using user parameters c (length), w (width), split along
   the ribbon direction; connect the two resulting quads with quadrilateral connectors in face-trace
   order → Control Ribbon.
3. **Construct PR Control Yarn**: define an ellipsoid per internal edge (center = edge midpoint, axes
   h/2·e_i·n⃗_i and half the internal-edge width); sample into an n-sided convex polygon; connect the
   polygons into a generalized toroid.
4. **Construct Smooth Ribbons/Yarns**: smooth control ribbons via cubic Bézier surfaces (G¹-continuous
   at boundaries); smooth control yarns via offline Catmull-Clark subdivision.

Parameter guidance: "a dense weaving is obtained with c≈1, with w≈1, and with relatively very small h
values. Small values of c and w provide sparse weaving." (p.5) Gap closing improves as the dihedral
angle θ between the two faces flanking an edge approaches 180° (best in 120°–180° range), aided by
Doo-Sabin subdivision passes (p.5).

### Figures

Fig.1 (p.1): woven sculptures (Venus 5 cycles, bunny 8, rocker arm 2, genus-3 object 16 cycles) as
ribbon meshes. Fig.2 (p.1): real vs. PR-rendered sparse/dense triaxial weave; unfolded ribbons are
wavy, only two ribbon types needed. Fig.3 (p.2): untwisted vs. twisted edge. Fig.4 (p.3): cube with one
twisted edge and its resulting control polygon. Fig.5 (p.3–4): nine-panel PR pipeline on an all-twisted
cube (mesh → projection planes → edge-region quads → projected regions → planar piece pairs →
connector quads → colored control mesh → smooth ribbon). Fig.8/9 (p.5): rendered yarns for bunny/Venus,
one color per cycle. Fig.10/11 (p.6): regular/semi-regular weave patterns shown sparse vs. dense.

### Visual depiction

Cycle color is arbitrary/disambiguating: "The colors of the thread cycles are randomly chosen... we
used saturated colors." (p.6) Ribbon width is not uniform: "the actual widths of ribbons are different
in different parts of the mesh" because sizes track the underlying polygon scale (p.6).

---

## 2. akleman-candg12.txt — "Hamiltonian Cycle Art: Surface Covering Wire Sculptures and Duotone Surfaces" (Akleman, Xing, Garigipati, Taubin, Chen, Hu; C&G 2012), 17 pages

### Definitions

**Hamiltonian path/cycle.** "a Hamiltonian path is a path in an undirected graph that visits each
vertex exactly once. A Hamiltonian cycle (or Hamiltonian circuit) is a Hamiltonian path that is a
cycle." (p.1)

**Hamiltonian triangle strip (Taubin's foundation).** "Taubin showed that it is always possible to
construct a triangular mesh from any given quadrilateral mesh such that the dual of the triangular
mesh has an Hamiltonian cycle... every connected manifold quadrilateral mesh without boundary can be
represented as a single Hamiltonian generalized triangle strip cycle." (p.1)

**Single covering curve.** "These curves are constructed by connecting the centers of every two
neighboring triangles in the Hamiltonian triangle strips. We call these curves surface covering since
they follow the shape of the mesh surface by meandering over it like a river." (p.1)

**Duotone surfaces / Jordan curve basis.** "The Jordan Curve Theorem states that any simple closed
curve in the plane separates the plane into two regions... Jordan's theorem is only correct for
genus-0 surfaces. Any single curve on a surface with positive genus does not necessarily separate the
surface into two regions." (p.4) Their fix: "a useful property of vertex insertion schemes such as
Catmull-Clark subdivision: If such a vertex insertion scheme is applied to a mesh, the vertices of the
resulting quadrilateral mesh are always two colorable." (p.4)

**Theorem 1** (bipartite connectivity). "For a bipartite graph, say U0 and U1 are the two edge disjoint
vertex sets and Y, B are Yellow and Blue graphs respectively. Then, we can make Y and B connected
respectively." (p.12)

**Lemma 1** (genus-0 tree/tree duality). "For an embedded bipartite graph on a genus-0 surface... If
one of the Y/B graphs is a tree, then the other is also a tree." (p.11)

### Notation / Equations

- Control-vertex position: p_cv = (p0,0+p0,1+p1,1+p0,1)/4 = (2p0,0+p1,0+p1,1)/4 (p.6).
- Trapezoid-corner bilinear form: v_{m,n} = Σ_{i=0}^{1}Σ_{j=0}^{1} [(1−(−1)^i s)(1−(−1)^j t)/4]·p_{i+m,j+n},
  s,t∈[0,1], indices mod 2 (p.7).

### Construction: surface covering curve, "a 2-step process" (p.5) expanded to 6 steps (p.5–7)

1. **Initial Mesh**: any manifold mesh, convex faces preferred.
2. **Quadrangulation**: if not quad, apply a quad-conversion subdivision (dual-of-Simplest
   recommended); skip if already quad.
3. **Initial Triangulation**: insert a diagonal ("red") into every quad; each triangle now has two
   original ("black") edges and one red edge.
4. **Control Vertex Position Computation**: weighted average per triangle via p_cv, favoring the vertex
   shared by the two black edges (avoids high-frequency wobble).
5. **Initial Curves**: connect control points across shared black edges → one closed curve per
   original face.
6. **Combining Curves**: repeatedly flip a red diagonal lying between two separate curves (merging
   them) until one closed curve remains; the flipped diagonals trace a spanning tree of the dual graph.

**Wires/ribbons**: constant-diameter (simple extrusion using rotation-minimizing/Frenet frames from
surface normals) vs. variable-diameter (inscribe a trapezoid per triangle via the bilinear v_{m,n}
equation with size parameters s,t; connect adjacent trapezoids with quad connectors, turning the
triangle strip into a quad strip; smooth via Catmull-Clark). Dense coverage at s≈1, t≈1.

**Duotone algorithm** (p.12): (1) convert mesh to 2-colorable quad mesh; (2) 2-color vertices
(Blue/Yellow, bipartite); (3) triangulate each quad along a same-colored diagonal (two choices per
quad), producing yellow/blue graphs and a Truchet-tile texture per triangulation choice; (4) flip a
diagonal between two separate same-color components (swapping that diagonal's color) until (5) a
single curve remains, with pure-yellow vertices/edges on one side and pure-blue on the other.

### Figures

Fig.1 (p.1): four spherical meshes next to their derived single 3D curve. Fig.2 (p.2): dense coverage,
constant vs. variable-diameter sparse/dense ribbons. Fig.3 (p.2): Fertility and Stanford Bunny as
duotone surfaces. Fig.4 (p.4): Mandelbrot/Monnerot-Dumaine duotone space-filling curve precedent.
Fig.5 (p.4): Bosch TSP-art curve vs. duotone TSP-art. Fig.6 (p.5–6): ten-panel pipeline walkthrough
(mesh → quadrangulation → triangulation → control vertices → per-face loops → all loops → selected
diagonal → flipped diagonal → merged curve → final curve). Fig.9–11 (p.7): trapezoid construction,
connectors, extruded/prism wire version. Fig.15–17 (p.10): Catmull-Clark 2-coloring, the two diagonal
triangulations of a quad, paired Truchet textures. Fig.18–19 (p.11): duotone surfaces before/after the
connectivity fix. Fig.20/22/23 (p.13,15,17): Buddha and positive-genus duotone surfaces, and results
from low-quality meshes.

### Visual depiction

"these curves are constructed by connecting the centers of every two neighboring triangles... follow
the shape of the mesh surface by meandering over it like a river" (p.1), compared directly to
space-filling curves, TSP-art, and Truchet tiling: "In terms of visual aesthetics, our curves most
closely resemble Truchet curves. In fact, if our method is applied to a planar grid, the result will be
a single Truchet curve." (p.5) Duotone surfaces are two flat paint regions bounded by the single curve,
textured per-quad with Truchet-tile arcs "since they closely resemble planar TSP art and Truchet-like
curves" (Abstract, p.1).

---

## 3. akleman-gmp06a.txt — "Practical Polygonal Mesh Modeling with Discrete Gaussian–Bonnet Theorem" (Akleman, Chen; GMP 2006), 6 pages

### Definitions

**Gauss–Bonnet (smooth statement).** "the integral of the Gaussian curvature over a closed smooth
surface is equal to 2π× the Euler characteristic of the surface which is 2−2g. The theorem requires a
smooth surface." (p.1)

**Piecewise linear mesh.** "We say that a mesh M is piecewise linear if every edge of M is a straight
line segment, and every face of M is planar." (p.1) Valence mᵢ/nⱼ used per-vertex/per-face without
further definition.

**Angle deflection at a vertex.** "θ̄(µi) = 2π − Σ_{j=1}^{mi} θj, where θj is the internal angle of the
j-th corner of vertex µi and mi is the valence of the vertex µi." (p.2) Sign reading: "θ̄(µi) > 0: then
vertex µi is either convex or concave... = 0: planar... < 0: then vertex µi is a saddle point." (p.2)

**Calladine's discrete Gaussian curvature** (cited precedent). "the most popular discrete version of
Gaussian curvature introduced by Calladine for triangular meshes uses angular deflection... given as
Angular Deflection / Area Associated with Vertex" (p.2–3).

**Sum of Angle Deflections (SAD).** "θ̄(M) = Σ_{i=1}^{v} θ̄(µi)." (p.3)

**Discrete Gauss–Bonnet — Theorem 2.2.** "Let M be a piecewise linear mesh of genus g. Then the SAD
θ̄(M) of the mesh M is equal to 2π(2−2g)." (p.3) Proof sums per-face interior angles (nⱼ−2)π against
per-vertex 2π−θ̄(µi), combines via Euler's equation: "θ̄(M) = 2π(v−e+f)... By Euler Equation (1), we
get θ̄(M) = 2π(2−2g). This proves the theorem." (p.3)

### Notation / Equations

- Euler equation: v − e + f = 2 − 2g (Eq.1, p.1).
- Regular mesh: e = nm(2−2g)/(2n+2m−nm), v = 2n(2−2g)/(2n+2m−nm), f = 2m(2−2g)/(2n+2m−nm) (p.1).
- **Lemma 2.1** (average valences m̄,n̄): e = n̄m̄(2−2g)/(2n̄+2m̄−n̄m̄), v = 2n̄(2−2g)/(2n̄+2m̄−n̄m̄),
  f = 2m̄(2−2g)/(2n̄+2m̄−n̄m̄) (p.2).
- Angle deflection: θ̄(µi) = 2π − Σθj (p.2). Calladine ratio: Angular Deflection / Area (p.2–3).
- SAD: θ̄(M) = Σθ̄(µi) (p.3). Face-angle sum: Σσ(φj) = n̄fπ − 2fπ (Eq.2, p.3).
- Vertex-angle sum: Σ(2π−θ̄(µi)) = 2vπ − θ̄(M) (p.3).
- Discrete Gauss–Bonnet: θ̄(M) = 2π(v−e+f) = 2π(2−2g) (p.3).
- Fixed-genus subdivision limit: 2/m̄ + 2/n̄ − 1 ≈ 0 → m̄ ≈ 2n̄/(n̄−2); with m̄≥3,n̄≥3: 3 ≤ n̄ ≤ 6 (p.4).

### Practical-modeling consequences (step guidance, not a rendering pipeline)

1. Compute θ̄(µi) per vertex from corner angles; classify convex/concave (>0), planar (=0), saddle
   (<0).
2. Since SAD is a fixed topological invariant (2π(2−2g)) under any topology-preserving edit, "if we
   gain angle deflections in some vertices, we will lose some angle deflections in some other
   vertices." (p.3)
3. To add a branch (eye socket, nose) without changing genus, introduce paired saddle and
   minima/maxima critical points via extrusion or "wrinkle" operations (Fig.5–6, p.4): extrusion of a
   4-valent quad yields 4 vertices at valence 5 and 4 at valence 3; wrinkle yields 4 at valence 4, 2 at
   valence 3, 2 at valence 5 — both net-zero average-valence change.
4. For quad-dominant modeling: minima/maxima need 3-valent vertices; saddles need valence > 4 (p.4).

### Figures

Fig.1/2 (p.2): Ilhan Koman's developable/saddle sculptures, motivating deflection beyond 2π. Fig.3
(p.3): genus-0/1/2 object sequence with +1 marks at minima/maxima/convex-concave points and −1 at
saddles, totals summing to 2−2g (Morse-theory analogy). Fig.4 (p.4): regular (4,4) mesh with strained
thin quads vs. two non-regular structures with locally adjusted valence, looking "more regular." Fig.5/6
(p.4): branch creation via extrusion and via "wrinkle," with explicit before/after valence labels.
Fig.7 (p.4, end): paper sculptures (cat mask, swan) built by cutting/stapling flat paper, as a physical
demo of angle-deflection-conserving shaping.

### Visual depiction

No shading/tone claims; the only visual claims concern paired critical points making quads look "more
regular" (Fig.4 caption, p.4) versus thin/strained in a naively regular grid.

---

## 4. akleman-smi10.txt — "Single-Cycle Plain-Woven Objects" (Xing, Akleman, Chen, Gross; SMI 2010), 10 pages

### Definitions

**Rotation at a vertex.** "A rotation at a vertex of a graph is a cyclic ordering of the set of the
edge-ends that are incident at that vertex... a rotation system specifies a graph embedding and...
every graph embedding can be specified by a rotation system." (p.2)

**Extended graph rotation system (EGRS) / signed helical twists.** "edge twists are used to create
crossings in a weaving. In extended graph rotation systems, an edge is viewed as a paper strip that can
be twisted clockwise or counter-clockwise in helical sense... These strands are either 'parallel' to
the mesh edge for an 'untwisted edge', or they both cross over the edge and over each other for a
'twisted edge'." (p.2) Exactly 3 states: "twisted edges can only be in one of two possible states...
(c) +1 (i.e. counter-clockwise) twisted or (d) −1 (i.e. clockwise) twisted." (p.3)

**Cyclic plain-weaving (restated).** "a cyclic plain-weaving on an orientable surface So is a
projection of a link L on So, such that (1) there are no triple intersections at any single point of
So, and (2) a traversal of the image on So of each component of L goes over and under alternatingly as
it crosses the images of other components or of itself." (p.2)

**Single-cycle condition — Theorem 2.1** (a "weaving version of Edmonds' theorem," p.3). "Let ρ(G) be a
graph rotation system... Suppose that the cyclic plain-weaving induced by ρ(G) has at least two
distinct cycles. Let e be an edge in G whose two sides belong to two different cycles c1 and c2... If
we twist e, then we combine the two cycles c1 and c2 into one cycle and reduce the number of cycles in
the weaving by one. Using this procedure, we can always reduce the number of cycles in a weaving to
one." (p.3) Mechanism: "if an edge at the intersection of two faces is twisted, the two faces are
merged into one face." (p.3)

### Notation / Equations

- Minimum twisted edges via dual spanning tree: F − 1 = 2E/µ − 1, µ = average face-sides, F = faces,
  E = edges (p.6–7); µ is "at least 3 and at most a little more than 6," so minimum lies between 0.33E
  and 0.66E.
- Cayley's formula (complete dual graph): τ(G) = F^{F−2} (p.6–7).
- Spanning-tree recursion: τ(G) = τ(G−e) + τ(G/e) (p.7).
- "with probability 1, there are 2^{F−1} single cycle embeddings of G." (p.7)

### Construction: single-cycle weaving via dual spanning tree (p.5–6)

1. Build the dual mesh M* of M. 2. Compute any spanning tree T of M*. 3. Twist every primal edge of M
whose dual lies in T — each twist merges the two faces on its sides (Theorem 2.1); a full spanning
tree merges all faces into one, i.e. a single cycle. 4. This uses the provable minimum number of
twists (|T| = F−1 edges).

**Practical algorithm** (p.9): randomly twist edges to a user-chosen target ratio; then repeatedly
twist/untwist edges lying on the boundary between two different cycles (alternating to hold the ratio)
until one cycle remains.

### Construction: extended projection method for untwisted edges, 5 steps (p.3–4)

1. Project the mesh to a local plane. 2. Connect each face center to its vertices, forming a radial-
graph quadrilateral ("edge-region": 2 edge endpoints + 2 adjacent face centers) per edge. 3(a). For
twisted edges, project the edge-region to two small planar regions, one slightly above and one
slightly below the plane. 3(b). For untwisted edges, instead create two side-by-side quadrilaterals in
the original plane (visually "triangular-looking," since two vertices of each coincide at a face
center). 4. Form strips by bilinear interpolation with parameters w (width), c (length/steepness):
twisted edges give two strips stacked into an "×" (over/under crossing); untwisted edges give two
parallel, non-crossing strips. 5. Connect strips face-to-face into a control-strip ring; smooth via
B-Spline/Bézier (ribbons) or convert to a toroidal control yarn and subdivide (yarns).

### Figures

Fig.1 (p.1): rainbow single-cycle bunnies at 4 twist %, magnified insets. Fig.2 (p.1): random twisting
on Rockarm at 20–98%, annotated cycle counts (3138→3), showing random twisting alone rarely reaches one
cycle. Fig.3 (p.3): the 4 edge states — plain, 0-twisted, +1, −1 — canonical legend. Fig.4 (p.3): an
untwisted octahedron with 8 unlinked face-boundary cycles vs. the same mesh partly twisted, producing
one linked/crossing weaving — direct demonstration of Theorem 2.1. Fig.5 (p.4): 8-panel walkthrough of
the extended projection method (mesh → face centers/vertices → one untwisted edge-region → all
edge-regions → projected regions → stripes → colored stripes → final threads). Fig.6/7 (p.3–4):
cross-sections of "×"-shaped twisted-edge strips vs. parallel untwisted-edge strips. Fig.8/9 (p.5):
single-cycle Venus/Rockarm at multiple twist %, dense vs. sparse, uniform vs. rainbow colored. Fig.11/12
(p.7–8): single-cycle results on non-quad meshes (geodesic dome, sphere tilings).

### Visual depiction

"For single-cycle woven objects, we changed the hue of the ribbon color (rainbow coloring) along the
cycle to show the structure" (p.5), versus uniform coloring used as a proof device: "for the former
[uniform-colored single-cycle objects] we can theoretically only use one color" (p.9) — i.e. a single
uniform color visually certifies single-cycle-ness, while rainbow coloring makes the winding path of
that one self-crossing thread legible.
