#let receiver-domination-rh = (
  key: "corollary:receiver-domination-rh",
  kind: [Conditional corollary],
  title: [Completed receiver domination would imply RH],
  status: [Exact conditional consequence of Weil's criterion],
  depends: ("theorem:completed-defect-recurrence",),
  claim: [
    Suppose every admissible compactly supported returned current $f$
    admits a finite contemporary receiver $S_f$ for which
    $
      Q_W(f) >= Sigma_(S_f)(f) >= 0,
    $
    with $Q_W$ equal to the completed Weil form on that current. Then the
    Riemann Hypothesis holds.
  ],
  proof: [
    The assumed inequality gives $Q_W(f)>=0$ for every admissible $f$.
    Weil's positivity criterion is equivalent to the Riemann Hypothesis.
  ],
  boundary: [
    The hypothesis is not established. Neither bounded experiments,
    critical-line symmetry, positivity of an Euler metric, nor trace-class
    transport proves the domination inequality.
  ],
)
