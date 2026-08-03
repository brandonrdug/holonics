#let squeezed-positive-return-rh = (
  key: "corollary:squeezed-positive-return-rh",
  kind: [Conditional corollary],
  title: [A noncircular squeeze by positive returned receivers would imply RH],
  status: [Exact conditional consequence of the squeeze theorem and Weil's criterion],
  depends: (
    "lemma:geometric-remainder-squeeze",
    "theorem:completed-defect-recurrence",
  ),
  claim: [
    Suppose that for every admissible returned current $f$ there is a
    sequence of independently positive receiver responses
    $
      Sigma_n(f)>=0
    $
    and explicitly derived errors $E_n(f)>=0$ such that
    $
      abs(Q_W(f)-Sigma_n(f))<=E_n(f)
      quad "and" quad
      E_n(f) arrow.r 0.
    $
    Then $Q_W(f)>=0$ for every admissible $f$, and the Riemann Hypothesis
    holds.
  ],
  proof: [
    The assumed bounds give
    $
      Q_W(f)>=Sigma_n(f)-E_n(f)>=-E_n(f).
    $
    Letting $n arrow.r infinity$ and applying the squeeze theorem yields
    $Q_W(f)>=0$. Weil's positivity criterion then implies RH.
  ],
  boundary: [
    The approximation index is not automatically a prime count. A compact
    current already meets only finitely many finite places; the useful
    sequence may instead refine the final receiver, prolate/Sonin
    resolution, or completed formulation chart. The error must include
    every endpoint, archimedean, finite-place, aperture-connection, and
    holonomy term without defining itself from the desired sign. Finite
    positive samples without such an error squeeze establish nothing
    universal.
  ],
)
