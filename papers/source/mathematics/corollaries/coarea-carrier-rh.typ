#let coarea-carrier-rh = (
  key: "corollary:coarea-carrier-rh",
  kind: [Conditional corollary],
  title: [An exact covariant coarea carrier for every completed defect would imply RH],
  status: [
    Exact conditional consequence; archimedean base carrier is constructed
    and its semilocal continuation remains open
  ],
  depends: (
    "definition:covariant-coarea-carrier",
    "theorem:covariant-coarea-fundamental-theorem",
    "theorem:completed-defect-recurrence",
    "theorem:positive-remainder-resolution-squeeze",
    "theorem:archimedean-remainder-amplitude",
  ),
  claim: [
    Suppose that for every final receiver $(S,R)$ there is an independently
    constructed covariant coarea carrier $C_(S,R)$ satisfying
    $
      Q_W(f)-Sigma_S(f)
      =
      norm(C_(S,R)f)^2
    $
    for every admitted current.  Require the carrier charts to preserve this
    response by the half-Jacobian law and require every prime seam, after
    anchoring the same current in the two contemporary receivers, to obey
    $
      norm(C_(S union {p},R)f)^2
      -
      norm(C_(S,R)f)^2
      =
      -W_p(f ast f^sharp)-kappa_(S,p)(f).
    $
    Then $Q_W(f)>=0$ for the complete admissible family and the Riemann
    Hypothesis holds.
  ],
  proof: [
    The Sonin response is a Hilbert--Schmidt norm square and the assumed
    carrier identity gives
    $
      Q_W(f)
      =
      Sigma_S(f)+norm(C_(S,R)f)^2>=0.
    $
    The chart and seam laws ensure that this is the same anchored completed
    response under every lawful reparameterization and prime transition,
    rather than a positive value obtained by changing the occurrence.
    Weil's criterion then implies RH.
  ],
  boundary: [
    The prime seam on the right may have either sign; the corollary does not
    impose a positive contribution per prime or a monotone receiver history.
    The archimedean base carrier is independently constructed by
    `theorem:archimedean-remainder-amplitude`.  The unproved statement is
    its expanded semilocal identity, including endpoint, finite-place,
    support, aperture-connection, and critical-stratum terms. Constructing
    $C_(S,R)$ from the desired defect by an abstract square root would be
    circular.
  ],
)
