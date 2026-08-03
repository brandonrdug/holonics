#let causal-impedance-rh = (
  key: "corollary:causal-impedance-rh",
  kind: [Conditional corollary],
  title: [A source-derived passive causal realization of the completed return proves RH],
  status: [
    Exact conditional consequence; the required theta--Euler--Gamma
    realization is identified but not yet constructed
  ],
  depends: (
    "theorem:causal-parity-kirchhoff-return",
    "theorem:completed-return-flux",
    "theorem:completed-theta-phase-current-bridge",
  ),
  claim: [
    Put
    $
      Xi(z)=xi(1/2+z),
      quad
      F(z)=frac(Xi'(z),Xi(z)).
    $
    Suppose there is a directed family of finite source-derived occurrence
    complexes $X_alpha$ with coboundaries $d_alpha$, nonnegative
    constitutive operators $W_alpha,G_alpha$, and dynamic bodies
    $
      L_alpha(z)
      =
      d_alpha^* W_alpha d_alpha+z G_alpha,
      quad op("Re")z>0.
    $
    Let $S_alpha(z)$ be their interior-shorted boundary responses from
    ("DYNAMIC SHORT") and let $y_alpha$ be normalized scalar receiver ports.
    If
    $
      F_alpha(z)
      =
      chevron.l S_alpha(z)y_alpha,y_alpha chevron.r
      arrow.r
      F(z)
      quad "(SOURCE RESPONSE LIMIT)"
    $
    locally uniformly on the right half-plane, then the Riemann Hypothesis
    holds.

    Equivalently, it is sufficient to construct the same family directly as
    a causal storage/dissipation identity for the completed source
    convolution, or as one source-native Gram factorization of the Pick
    kernel
    $
      K_F(p,q)
      =
      frac(
        F(p)+overline(F(q)),
        p+overline(q)
      ).
      quad "(COMPLETED PICK RETURN)"
    $
    Through the completed theta bridge, this is exactly a factorization of
    the seam phase current $cal(P)_0$ on the bilateral-exponential receiver
    span, not positivity of each isolated crossing layer.
  ],
  proof: [
    The causal-parity Kirchhoff theorem makes every $F_alpha$ positive real:
    $
      op("Re")F_alpha(z)>=0
      quad "for "op("Re")z>0.
    $
    Local uniform convergence preserves holomorphy and the nonnegative real
    part, so $F$ is positive real.  The completed-return-flux theorem makes
    this equivalent to RH.

    A holomorphic function is positive real on the right half-plane exactly
    when its Pick kernel ("COMPLETED PICK RETURN") is positive semidefinite.
    The completed-theta phase-current theorem gives
    $
      Xi(p)overline(Xi(q))K_F(p,q)
      =
      4
      integral_RR integral_RR
      e^(p a)cal(P)_0(a,b)e^(overline(q)b)
      dif a dif b.
    $
    Multiplication by the nonzero analytic receiver factors preserves kernel
    sign away from zeros, and a right-half-plane zero is itself a failure of
    the positive-real law.  Hence a source-native Gram or dissipative
    realization of this pullback supplies the same conclusion.
  ],
  boundary: [
    Defining $W_alpha$, $G_alpha$, or a storage form by first assuming
    $op("Re")F>=0$ would be circular.  The family must be constructed from
    the positive theta source together with the exact Euler, Gamma, endpoint,
    and causal-boundary relations already present before zero locations are
    known.  Causal time parity proves that internal time faces cancel and
    that a local dissipation identity composes; it does not assign the
    required nonnegative constitutive operators by itself.
  ],
)
