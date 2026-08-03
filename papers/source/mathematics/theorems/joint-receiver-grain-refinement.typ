#let joint-receiver-grain-refinement = (
  key: "theorem:joint-receiver-grain-refinement",
  kind: [Theorem],
  title: [A jointly separating receiver refines a locally tolerated fiber],
  status: [Exact consequence of product maps and partition refinement],
  depends: ("definition:co-present-receiver-atlas",),
  claim: [
    Let $x,x' in X_e$ be two actual occurrences.  Suppose one receiver grain
    $cal(P)_i$ identifies them, while another receiver grain $cal(P)_j$
    separates them:
    $
      [q_i(x)]_(cal(P)_i)=[q_i(x')]_(cal(P)_i),
      quad
      [q_j(x)]_(cal(P)_j)!=[q_j(x')]_(cal(P)_j).
    $
    Then the joint receiver face separates $x$ and $x'$.  More generally,
    refining any one receiver partition can only split, never merge, the
    fibers of the joint quotient.

    Therefore a finite difference may remain *grain-dark* at some receivers
    while being consequential in the joint atlas.  Coarsening is
    receiver-exact for a declared objective exactly when every pair newly
    identified by that coarsening retains the same admitted consequence and
    overlap signature.
  ],
  proof: [
    Equality in the joint quotient requires equality in every component.
    The inequality in the $j$ component therefore separates the two joint
    tuples. If $cal(P)'_j$ refines $cal(P)_j$, every
    $cal(P)'_j$-class lies inside one $cal(P)_j$-class, so replacing the
    latter component by the former can only split joint fibers. The final
    statement is the definition of receiver-exact factorization at the
    declared objective.
  ],
  boundary: [
    More resolution is not automatically more useful. A refinement which
    exposes no consequential distinction may lawfully depart, while a
    coarse receiver may remain necessary because it carries a stable
    invariant or wider aperture unavailable to a fine receiver.
  ],
)
