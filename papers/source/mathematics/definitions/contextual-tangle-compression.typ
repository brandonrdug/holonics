#let contextual-tangle-compression = (
  key: "definition:contextual-tangle-compression",
  kind: [Definition],
  title: [Contextual tangle equivalence and receiver-exact substitution],
  status: [Project definition using standard tangle and skein composition],
  depends: (
    "definition:receiver",
    "definition:causal-soul",
    "definition:holonic-process-double-category",
  ),
  claim: [
    Fix an oriented marked boundary $B$.  Let $op("Tan")(B)$ be the
    collection of tangles with boundary $B$, modulo ambient isotopy relative
    to $B$.  A compatible exterior context $C$ composes with an interior
    tangle $T$ by gluing, written $C[T]$.

    For a declared compositional receiver family $cal(R)$, define
    *contextual receiver equivalence*
    $
      T approx_cal(R) T'
      quad "iff" quad
      R(C[T])=R(C[T'])
    $
    for every $R in cal(R)$ and every admitted compatible context $C$.
    Because contexts themselves compose, $approx_cal(R)$ is a congruence:
    an equivalent interior may be substituted inside every larger admitted
    exterior.

    A receiver-exact tangle compression is a factorization through the
    quotient
    $
      q_cal(R):op("Tan")(B) arrow.r
      op("Tan")(B)/approx_cal(R).
    $
    It may discard distinctions between interiors only at the stated
    receiver and context boundary.

    After linearizing over a ring $R_0$, a skein relation is a local module
    relation such as
    $
      alpha [T_+]+beta[T_-]+gamma[T_0]=0.
    $
    It licenses linear replacement inside any compatible context in the
    resulting skein module.  It does not assert
    $T_+ approx T_-$, $T_+ approx T_0$, or ambient isotopy of the three
    tangles.
  ],
  proof: none,
  boundary: [
    Equal closure under one receiver is weaker than contextual equivalence.
    Contextual equivalence is weaker than causal-soul equivalence unless the
    receiver family is jointly conservative.  A skein quotient can identify
    distinct knots or retain torsion, and its coefficients may be signed or
    complex.  Skein reduction is therefore not automatically positive,
    metric-decreasing, unique, or computationally cheaper.
  ],
)
