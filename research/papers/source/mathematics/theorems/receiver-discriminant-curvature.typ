#let receiver-discriminant-curvature = (
  key: "theorem:receiver-discriminant-curvature",
  kind: [Theorem],
  title: [Receiver crossings are chamber data; curvature requires alternate transports],
  status: [Exact geometric consequence under the stated genericity and connection hypotheses],
  depends: (
    "definition:situated-knot-receiver",
    "theorem:three-frame-return-covariance",
  ),
  claim: [
    Let $cal(P)$ be a smooth parameter space of pairs $(K,rho)$ consisting
    of a tame embedding and a situated receiver, and let
    $Delta subset cal(P)$ be the discriminant of nongeneric received
    diagrams.  On each connected chamber of $cal(P) minus Delta$, the
    crossing population, crossing signs, and depth order continue without a
    combinatorial event.  A generic one-parameter path meeting a codimension
    one stratum of $Delta$ produces the corresponding local Reidemeister
    event.

    Suppose additionally that each receiver $rho$ carries a fiber $E_rho$
    and each admitted receiver path $gamma$ carries transport $U_gamma$.
    The ordered crossings along one path form a lineage, but they are not
    curvature.  Curvature appears only when two alternate transports can be
    compared.  On a discrete triangle,
    $
      Omega_(012)=U_(02)-U_(12)U_(01),
    $
    or, for invertible edge maps, through the returned holonomy
    $
      H_(012)=U_(20)U_(12)U_(01).
    $
    In a smooth connection chart this is the infinitesimal law
    $
      F_nabla=d A+A ∧ A.
    $
  ],
  proof: [
    Generic transversality makes the received diagram stable under a small
    parameter variation until the path meets the discriminant.  The local
    models for a generic codimension-one passage are precisely the
    Reidemeister diagram events.  The second claim follows from the
    definition of a connection's curvature as the first-order
    path-dependence of parallel transport around an infinitesimal
    two-dimensional comparison cell.  A single path has no alternate route
    with which to form that comparison.
  ],
  boundary: [
    Crossing count can jump with receiver while knot type remains fixed.
    Conversely, a crossing change alters the over/under law and can change
    knot type without being a receiver motion.  A nontrivial returned
    holonomy may disappear after quotienting to knot type while remaining
    visible to a framed, braid, metric, or causal-lineage receiver.  A
    gyroparallelogram gives one specialized model of this failure of ordinary
    vector addition only when the transport law satisfies the gyrogroup
    axioms; it is not a universal curvature definition.
  ],
)
