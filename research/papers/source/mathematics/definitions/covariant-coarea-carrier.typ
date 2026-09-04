#let covariant-coarea-carrier = (
  key: "definition:covariant-coarea-carrier",
  kind: [Definition],
  title: [A covariant coarea carrier is a receiver-local field of squared amplitudes],
  status: [Project definition built from classical direct-integral and coarea geometry],
  depends: (
    "definition:receiver",
    "definition:parametric-weil-bundle",
  ),
  claim: [
    Fix one contemporary receiver $rho$.  A _covariant coarea carrier_ for
    an admitted current space $cal(H)_rho$ consists of:

    - a measured parameter region $(Lambda_rho,nu_rho)$;
    - a measurable field of Hilbert fibers
      $cal(K)_(rho,xi)$ over $xi in Lambda_rho$; and
    - an independently specified amplitude law
      $B_(rho,xi):cal(H)_rho arrow.r cal(K)_(rho,xi)$

    for which
    $
      (C_rho f)(xi)=B_(rho,xi)f
    $
    is square-integrable.  Its carried quadratic response is
    $
      D_rho(f)
      =
      norm(C_rho f)^2
      =
      integral_(Lambda_rho)
      norm(B_(rho,xi)f)^2 dif nu_rho(xi).
    $

    When a regular map
    $I:M arrow.r B$ supplies the parameter fibers, the coarea theorem may
    disintegrate this response over $I^(-1)(c)$.  The normal Jacobian,
    induced fiber measure, orientation, and any critical strata are part of
    the carrier.  They may not be discarded after the scalar integral is
    evaluated.
  ],
  proof: none,
  boundary: [
    The carrier belongs to the contemporary receiver; it is not a fixed
    enlarged field containing all earlier and later receivers.  Its
    nonnegativity follows only after the amplitude law and measure have been
    constructed independently.  Defining $C_rho$ as an abstract square root
    of a desired nonnegative defect would assume the sign it is meant to
    establish.  Critical points where the coarea Jacobian loses rank are
    typed seams, not regular fibers with a zero silently divided away.
  ],
)
