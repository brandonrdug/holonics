#let finite-archimedean-tail-squeeze = (
  key: "corollary:finite-archimedean-tail-squeeze",
  kind: [Corollary],
  title: [A certified finite archimedean tail supplies an exact bounded squeeze],
  status: [Exact consequence of the published finite Guinand--Weil tail order],
  depends: ("theorem:positive-remainder-resolution-squeeze",),
  claim: [
    On one fixed finite Galerkin band, suppose Hermitian matrices
    $Q_T$ and $Q_infinity$ obey
    $
      0<=Delta_T:=Q_infinity-Q_T<=B_T I,
      quad
      B_T arrow.r 0.
    $
    If the finite matrix
    $
      Q_T+B_T I
    $
    is independently certified positive semidefinite, then for every
    coefficient vector $v$ the response
    $
      Sigma_T(v)
      =
      v^* (Q_T+B_T I) v
    $
    is nonnegative and
    $
      abs(v^*Q_infinity v-Sigma_T(v))
      <=
      B_T norm(v)^2
      arrow.r 0.
    $
  ],
  proof: [
    The tail order gives
    $
      -B_T I
      <=
      Delta_T-B_T I
      <=0.
    $
    Since
    $
      Q_infinity-(Q_T+B_T I)=Delta_T-B_T I,
    $
    evaluation on $v$ gives the stated absolute bound.  Positivity of
    $Sigma_T$ is precisely the independent finite-matrix certificate.
  ],
  boundary: [
    This closes the archimedean cutoff axis on one already finite
    frequency band.  It does not prove the shifted certificate for every
    band, control the Galerkin limit, enlarge the support aperture, or sign
    the semilocal remainder.  The index $T$ is an archimedean integration
    cutoff, not a count of primes and not the full receiver resolution.
  ],
)
