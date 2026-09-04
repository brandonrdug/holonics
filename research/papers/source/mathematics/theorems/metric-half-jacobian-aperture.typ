#let metric-half-jacobian-aperture = (
  key: "theorem:metric-half-jacobian-aperture",
  kind: [Theorem],
  title: [The square root of a pulled metric gives the successor aperture an exact positive complement],
  status: [Exact Hilbert-space consequence of the Euler successor geometry],
  depends: ("theorem:euler-successor-geometry",),
  claim: [
    Let $J:H arrow.r H'$ be boundedly invertible and put
    $
      G=J^*J.
    $
    Its polar decomposition is
    $
      J=U G^(1/2),
      quad
      U=J G^(-1/2),
    $
    with $U$ unitary.  If $Pi$ is a $G$-orthogonal projection, then
    $
      tilde(P)=G^(1/2)Pi G^(-1/2)
    $
    is an ordinary orthogonal projection.  Consequently, for every $v in H$,
    $
      norm(J v)^2
      =
      norm(G^(1/2)Pi v)^2
      +
      norm(G^(1/2)(I-Pi)v)^2.
    $
    The same identity holds after summing over an orthonormal source basis
    whenever the corresponding operators are Hilbert--Schmidt.
  ],
  proof: [
    Since $G$ is strictly positive, its bounded positive square root and
    inverse exist.  Direct calculation gives $U^*U=UU^*=I$.  The
    $G$-self-adjoint identity $Pi^*G=G Pi$ implies
    $
      tilde(P)^*=tilde(P),
    $
    while $Pi^2=Pi$ implies $tilde(P)^2=tilde(P)$.  Hence $tilde(P)$ is
    orthogonal.  Apply ordinary Pythagoras to
    $G^(1/2)v$ and use
    $
      tilde(P)G^(1/2)=G^(1/2)Pi
    $
    together with $norm(J v)=norm(G^(1/2)v)$.
  ],
  boundary: [
    $G^(1/2)$ is an operator-valued half-metric analogous to a scalar
    square-root Jacobian.  The positive complement belongs to the complete
    successor metric at that event; it is not an untouched predecessor
    block and is not automatically the completed Weil defect.  Identifying
    that complement, or another independently constructed coarea carrier,
    with the exact defect remains the RH-bearing open identity.
  ],
)
