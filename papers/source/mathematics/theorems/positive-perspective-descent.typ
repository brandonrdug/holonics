#let positive-perspective-descent = (
  key: "theorem:positive-perspective-descent",
  kind: [Theorem],
  title: [Anchored positive forms descend across lawful perspectives],
  status: [Exact linear-algebraic descent statement],
  depends: (
    "definition:receiver",
    "definition:formulation-span-atlas",
  ),
  claim: [
    Let $cal(R)$ be a receiver rechart groupoid, let
    $V:cal(R) arrow.r op("Hilb")_"iso"$ assign a test space to every chart,
    and let $T_u=V(u)$ for $u:rho arrow.r sigma$. Suppose a Hermitian form
    $Q_rho$ is supplied in every chart and satisfies the anchored covariance
    law
    $
      Q_sigma(T_u f,T_u g)=Q_rho(f,g)
      quad "for every" u:rho arrow.r sigma.
    $

    Then positive semidefiniteness and Hermitian inertia are constant on each
    receiver orbit. If the charts cover one glued test bundle and their
    transitions obey the cocycle law, the compatible family $(Q_rho)$
    descends to one global Hermitian form $Q$. The descended form is positive
    semidefinite if and only if every local representative is positive
    semidefinite.
  ],
  proof: [
    For an invertible transition $T_u$, the covariance law is the congruence
    $Q_rho=T_u^*Q_sigma T_u$. Therefore
    $Q_rho(f,f)=Q_sigma(T_u f,T_u f)$, proving sign equivalence, while
    Sylvester inertia is preserved by invertible congruence.

    On chart overlaps, the covariance law makes the value assigned to a represented
    vector independent of the chosen chart. The transition cocycle makes
    this pairwise identification consistent on triple overlaps, so the local
    forms define one form on the glued bundle. Every global vector has a
    local representative, which proves the final equivalence.
  ],
  boundary: [
    The theorem does not turn a negative direction positive by changing
    orientation. “Some positive perspective exists” is insufficient unless
    it carries the same anchored form through the same cocycle and the charts
    cover every admitted direction. The set of positive semidefinite
    Hermitian forms is a convex cone; for an indefinite form, the set of
    vectors on which its quadratic value is nonnegative need not itself be
    convex.
  ],
)
