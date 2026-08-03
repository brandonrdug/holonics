#let covariant-coarea-fundamental-theorem = (
  key: "theorem:covariant-coarea-fundamental-theorem",
  kind: [Theorem],
  title: [The half-Jacobian preserves a coarea carrier and its covariant FTC has signed seams],
  status: [Classical change of variables and metric-connection identity; exact laboratory synthesis],
  depends: (
    "definition:covariant-coarea-carrier",
    "theorem:transported-fundamental-theorem",
  ),
  claim: [
    First let $Phi:U arrow.r V$ be a regular change of carrier coordinates,
    let
    $
      J_Phi(u)=abs(det D Phi(u)),
    $
    and let $R_u$ be a unitary identification of the corresponding output
    fibers.  If $b(x)$ is a square-integrable carrier section on $V$, then
    the pulled section
    $
      tilde(b)(u)
      =
      J_Phi(u)^(1/2)R_u b(Phi(u))
    $
    obeys
    $
      integral_V norm(b(x))^2 dif x
      =
      integral_U norm(tilde(b)(u))^2 dif u.
    $

    Now let $rho(t)$ be a piecewise smooth path of contemporary receivers,
    let $f_t$ be one anchored current transported along that path, and let
    $
      Psi(t)=C_(rho(t))f_t
    $
    be the resulting section of the carrier-output Hilbert bundle.  For a
    metric-compatible connection $nabla$ and seams $t_1,dots,t_m$,
    $
      norm(Psi(b))^2-norm(Psi(a))^2
      =
      2 op("Re")
      sum_j integral_(I_j)
      chevron.l Psi(t),nabla_(partial_t)Psi(t) chevron.r dif t
      +
      sum_k
      (norm(Psi(t_k^+))^2-norm(Psi(t_k^-))^2).
    $
    Thus every contemporary response is nonnegative while its interior
    connection current and discrete seam changes may have either sign.
  ],
  proof: [
    The first identity is the ordinary change-of-variables theorem; unitary
    fiber transport preserves the pointwise norm and the square-root
    Jacobian converts the volume element into amplitude.

    On each smooth stratum, metric compatibility gives
    $
      partial_t norm(Psi(t))^2
      =
      2 op("Re")
      chevron.l Psi(t),nabla_(partial_t)Psi(t) chevron.r.
    $
    Integrate this scalar identity on every stratum and telescope the
    one-sided endpoint values.  The unmatched values at the seams are
    exactly the displayed jumps.
  ],
  boundary: [
    Positivity belongs to each complete carrier norm, not to every derivative
    or seam increment.  A monotone tail integral is one special case in
    which the connection density and jumps have a chosen sign; it is not a
    general law of changing receivers.  The theorem supplies no carrier
    amplitude for the completed Weil defect and does not sign the
    prime-admission connection term.
  ],
)
