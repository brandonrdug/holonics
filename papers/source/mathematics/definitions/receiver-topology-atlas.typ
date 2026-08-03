#let receiver-topology-atlas = (
  key: "definition:receiver-topology-atlas",
  kind: [Definition],
  title: [Source incidence, receiver planarization, and face-dual recurrence],
  status: [Project definition using standard planarization, rotation-system, dual-graph, and Ihara geometry],
  depends: (
    "definition:co-present-receiver-atlas",
    "definition:situated-knot-receiver",
  ),
  claim: [
    Let $X_e$ be one marked source incidence complex and let
    $q_r:X_e arrow.r Y_r$ be a regular two-dimensional receiver face.
    Three typed objects are retained:

    + $G_X$, whose vertices and edges are only the source incidences and
      branches declared by $X_e$;
    + $D_r(X)$, the planar diagram obtained by splitting projected branches
      at regular visible crossings while retaining their source branches,
      depth order, and crossing orientation; and
    + $G_r^star$, the face-dual multigraph of $D_r(X)$.

    An apparent crossing is a vertex of $D_r(X)$ but is not thereby a vertex
    of $G_X$. A source incidence remains one source vertex through every
    receiver even when several of its inscriptions participate.

    The receiver rotation system is the exact cyclic order of outgoing
    projected rays at every diagram vertex. Its face permutation recovers the
    oriented boundary cycles of $D_r(X)$ without angles or floating-point
    coordinates. The corresponding unweighted loop testimonies are
    $
      Z_(G_X)(u)
      =
      product_([P] in "Prim"(G_X))(1-u^(ell(P)))^(-1)
    $
    and
    $
      Z_(G_r^star)(u)
      =
      product_([P] in "Prim"(G_r^star))(1-u^(ell(P)))^(-1),
    $
    where primitive loops are closed non-backtracking paths modulo cyclic
    choice of starting dart.

    For one co-present receiver family, the *receiver-topology atlas* is the
    actual joint image of
    $
      X_e mapsto
      (G_X,D_r(X),G_r^star)_(r in I_e).
    $
    It does not identify source incidence with diagram incidence or complete
    independently selected diagrams to a Cartesian population.
  ],
  proof: none,
  boundary: [
    The unweighted zeta functions count combinatorial primitive loops only.
    They carry neither receiver metric, cross-ratio swing, source chronology,
    nor overlap holonomy. Collinear overlap, equal-depth crossings, collapsed
    source vertices, and multiple crossings at one projected point are
    discriminants rather than silently resolved diagram vertices. A
    receiver-topology atlas is not a Riemann-zeta representation.
  ],
)
