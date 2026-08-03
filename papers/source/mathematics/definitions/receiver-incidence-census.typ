#let receiver-incidence-census = (
  key: "definition:receiver-incidence-census",
  kind: [Definition],
  title: [Receiver incidence census: source, image, silhouette, crossing, and fiber],
  status: [Project definition using standard polyhedral projection and planarization geometry],
  depends: (
    "definition:receiver-topology-atlas",
  ),
  claim: [
    Let $X$ be a finite marked incidence body with source vertices $V_X$,
    source edges $E_X$, and a situated planar receiver
    $
      q_r:abs(X) arrow.r Y_r.
    $
    The receiver retains the following populations separately:

    $
      P_r(X)=q_r(V_X),
      quad
      mu_r(y)=abs({v in V_X:q_r(v)=y}),
    $

    where $P_r(X)$ is the set of distinct received vertex coordinates and
    $mu_r$ is their source-fiber multiplicity. For a convex polyhedral body,
    the silhouette-corner population is
    $
      S_r(X)
      =
      "Vert"("conv"(q_r(abs(X)))).
    $
    The regular apparent-crossing population is
    $
      C_r(X)
      =
      {
        (y,e,e',s,t):
        q_r(e(s))=q_r(e'(t))=y,
        e!=e',
        "the received tangents are transverse"
      },
    $
    with source parameters, branch identity, hand, and depth order retained.
    Splitting received branches at $P_r(X)$ and $C_r(X)$ gives the
    planarized diagram $D_r(X)$ and its own vertex, edge, and face counts.
    When the convex silhouette is a nondegenerate polygonal cycle,
    $
      abs(E_(partial,r))=abs(S_r(X)).
    $
    When $D_r(X)$ is connected, its separately planarized populations obey
    $
      abs(V(D_r))-abs(E(D_r))+abs(F(D_r))=2,
      quad
      sum_(v in V(D_r)) "deg"(v)=2 abs(E(D_r)).
    $
    These are receiver-local incidence laws; neither equation identifies a
    received edge with one source edge.

    The *receiver incidence census* is the typed family
    $
      "Census"_r(X)
      =
      (
        (f_k(X))_k,
        P_r(X),
        mu_r,
        S_r(X),
        C_r(X),
        (f_k(D_r(X)))_k
      ).
    $
    Source vertices, distinct image coordinates, silhouette corners,
    apparent crossings, material joints, visible edge fragments, and
    complementary regions are therefore different populations even when a
    drawing uses one glyph for several of them.
  ],
  proof: none,
  boundary: [
    The convex-hull silhouette is the correct boundary receiver for a convex
    body. Nonconvex, transparent, refractive, self-intersecting, or
    occluding worlds require their declared visibility and propagation law.
    A multiple receiver fiber is not thereby a material contact, while one
    projected source vertex of high valence is not thereby several
    accidental crossings. The census records a face; it does not reconstruct
    the complete source body.
  ],
)
