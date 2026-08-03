#let situated-knot-receiver = (
  key: "definition:situated-knot-receiver",
  kind: [Definition],
  title: [Situated knot receiver and its crossing field],
  status: [Project definition over standard knot projections],
  depends: (
    "definition:receiver",
    "definition:situated-occurrence",
    "definition:causal-soul",
  ),
  claim: [
    Let $K:S^1 arrow.r M^3$ be an oriented tame embedding in an oriented
    three-manifold.  A *situated knot receiver*
    $
      rho=(Sigma_rho,pi_rho,nu_rho)
    $
    consists of an oriented receiving surface, a generic projection
    $pi_rho:M^3 arrow.r Sigma_rho$, and a coorientation or depth law
    $nu_rho$ sufficient to order the two preimages of every transverse
    double point.

    Its crossing population is
    $
      cal(C)_rho(K)
      =
      { {s,t}:s!=t, pi_rho(K(s))=pi_rho(K(t)),
      " the projected tangents are transverse" }.
    $
    Together with the source orientation, depth order, and local crossing
    sign, this population forms the received diagram $D_rho(K)$.

    The embedded knot $K$, its ambient-isotopy class $[K]$, its received
    diagram $D_rho(K)$, and the scalar crossing count
    $abs(cal(C)_rho(K))$ are four different objects.  A crossing is a
    receiver-relative incidence between two source parameters.  It is not
    an intrinsic vertex of the embedded knot.
  ],
  proof: none,
  boundary: [
    The receiver must be generic for the crossing population to consist of
    transverse double points.  Tangencies, cusps, triple points, and failed
    depth order belong to the projection discriminant.  Switching one
    over/under relation is a crossing change and may change knot type; it is
    not a Reidemeister re-presentation of the same knot.
  ],
)
