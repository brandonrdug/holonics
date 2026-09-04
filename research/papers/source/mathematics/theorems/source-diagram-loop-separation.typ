#let source-diagram-loop-separation = (
  key: "theorem:source-diagram-loop-separation",
  kind: [Theorem],
  title: [Source-loop invariance and receiver-loop recurrence do not determine causal identity],
  status: [General separation with an exact bounded counterexample],
  depends: (
    "definition:receiver-topology-atlas",
    "theorem:four-member-projective-swing",
  ),
  claim: [
    For a fixed marked source incidence graph $G_X$, its unweighted Ihara
    function $Z_(G_X)$ is invariant under every regular receiver change.
    It is nevertheless unchanged by any nonidentical source deformation
    which preserves the abstract incidence graph.

    Conversely, the unweighted receiver-dual function $Z_(G_r^star)$ may
    change under receiver precession while $X_e$ remains exact, and the same
    receiver-dual function may recur at two nonidentical source geometries.
    Hence neither $Z_(G_X)$ nor one $Z_(G_r^star)$ determines the causal soul
    of the received construction.

    Any loop carrier capable of doing so must at least retain the joint source
    occurrence, the receiver transition, and the geometric or holonomy weight
    transported around the loop. A possible research form is
    $
      cal(Z)_(cal(J),rho)(u)
      =
      product_([P])
      det(
        I-rho("Hol"_(cal(J))(P)) W(P) u^(ell(P))
      )^(-1),
      quad "(OPEN DECORATED LOOP CARRIER)"
    $
    but its representation $rho$, weight $W$, admissible primitive paths, and
    trace identity must be derived from the selected ecology.
  ],
  proof: [
    The first invariance is immediate because changing $r$ does not alter the
    vertices or edges of $G_X$. The same observation proves that an
    incidence-preserving geometric deformation is invisible to the
    unweighted function.

    For the converse, take the exact tetrahedral incidence $K_4$. One direct
    receiver presents a crossing-free planar $K_4$, while an exact Cayley
    precession presents one regular apparent crossing. The first face dual
    has four vertices and six edges; the second has five vertices and eight
    edges, and their exact Ihara reciprocal polynomials differ. Move only one
    source vertex from height $1$ to height $1/4$ while retaining every
    incidence and the precessed receiver. The crossing departs and the first
    receiver-dual polynomial recurs, although the oriented volume witness
    changes from $16$ to $4$ and three squared edge lengths change.

    The exact construction and both determinant calculations are deposited
    in `observations/receiver-topology-atlas-01`. These two counterexamples
    prove both failures of determination. Therefore any identity-bearing
    loop object owes the omitted transported decoration.
  ],
  boundary: [
    The displayed decorated product is a precisely scoped open construction,
    not a proved invariant. In particular, equality with a completed zeta
    function, correspondence between its primitive paths and rational
    primes, positivity of its evaluation, and covariance through
    discriminants remain unproved.
  ],
)
