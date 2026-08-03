#let transported-positive-atlas-rh = (
  key: "corollary:transported-positive-atlas-rh",
  kind: [Conditional corollary],
  title: [An exhaustive sign-preserving formulation atlas would imply RH],
  status: [Exact conditional consequence; proposed relativistic proof form],
  depends: (
    "definition:parametric-weil-bundle",
    "theorem:weil-signature-transport",
    "theorem:completed-defect-recurrence",
  ),
  claim: [
    Suppose a transport groupoid of formulation charts has the following
    properties:

    - every admissible returned Weil current is represented by an anchored
      vector in some fiber;
    - every orbit meets a base fiber on which the anchored Weil form is
      proved positive semidefinite without assuming RH;
    - every transition is receiver-exact and carries the Hermitian response
      by a positive congruence; and
    - transition composition, adjoint return, boundary terms, and holonomy
      preserve that covariance.

    Then the completed Weil form is nonnegative on every admissible returned
    current, and the Riemann Hypothesis holds.
  ],
  proof: [
    Take any admissible returned current. Exhaustiveness places it in one
    represented fiber and the orbit condition connects it to a positive base
    fiber. Repeated application of positive-congruence covariance preserves
    its sign along the complete path. Hence the completed Weil response is
    nonnegative for every admissible current. Weil's criterion then implies
    RH.
  ],
  boundary: [
    Merely finding a positive vector, a positive chart, or some path to a
    positive value is insufficient. The path must carry the same anchored
    test occurrence, its response, and all completion terms. Exhaustiveness
    and sign-preserving holonomy are the unproved obligations.
  ],
)
