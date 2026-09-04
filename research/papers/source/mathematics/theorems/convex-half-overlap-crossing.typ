#let convex-half-overlap-crossing = (
  key: "theorem:convex-half-overlap-crossing",
  kind: [Theorem],
  title: [A convex overlap field has an oriented half-crossing surface],
  status: [Classical covariogram, Brunn--Minkowski, and coarea results; exact laboratory synthesis],
  depends: (
    "definition:covariant-coarea-carrier",
    "theorem:oriented-half-density-crossing",
    "theorem:covariant-coarea-fundamental-theorem",
  ),
  claim: [
    Let $K subset RR^n$ be a convex body with volume $V_K>0$, and define its
    overlap field
    $
      c_K(x)
      =
      op("Vol")(K inter (K+x))
      =
      (1_K ast 1_K^*)(x).
      quad "(OVERLAP FIELD)"
    $
    Then $c_K$ is even and positive definite,
    $
      op("supp")(c_K)=K-K,
      quad
      hat(c_K)=abs(hat(1_K))^2,
    $
    and $c_K^(1/n)$ is concave on $K-K$.

    For $0<t<1$, put
    $
      Omega_t
      =
      {x:c_K(x)>=t V_K}.
      quad "(OVERLAP STRATUM)"
    $
    Every $Omega_t$ is centrally symmetric and convex. The laboratory
    positive-half crossing is the outward-oriented regular face
    $
      L_+(K)
      =
      partial Omega_(1/2)
      =
      {x:c_K(x)=V_K/2}.
      quad "(HALF CROSSING)"
    $
    A receiver direction selects its positive branch; the opposite branch is
    the orientation-reversed $L_-(K)$.

    Whenever $c_K$ is continuously differentiable on the swept regular
    strata, neighboring overlap boundaries obey the exact coarea transport
    $
      op("Vol")(Omega_alpha)-op("Vol")(Omega_beta)
      =
      integral_alpha^beta
      (
        integral_(c_K^(-1)(t V_K))
        frac(V_K,norm(nabla c_K(x)))
        dif cal(H)^(n-1)(x)
      )
      dif t
      quad "(BOUNDARY SWEEP)"
    $
    for $0<alpha<beta<1$. Thus the changing interior between two neighboring
    shape boundaries is carried by their receiver-relative surface field;
    it is not reconstructed from a final contour.

    In one logarithmic dimension, for
    $K=[-ell/2,ell/2]$,
    $
      c_K(x)=(ell-abs(x))_+,
      quad
      L_+(K)={ell/2},
      quad
      L_-(K)={-ell/2}.
      quad "(DYADIC FACE)"
    $
    Hence the positive crossing has normalized overlap
    $c_K(ell/2)/c_K(0)=1/2$. When $ell=log 2$, exponentiation sends the two
    branches to $2^(1/2)$ and $2^(-1/2)$, exactly the two boundary points of
    the multiplicative convolution-root aperture.
  ],
  proof: [
    Formula ("OVERLAP FIELD") is an autocorrelation. Fourier transformation
    therefore gives the displayed modulus square, proving positive
    definiteness and evenness. Its support is the difference body $K-K$.

    For $x,y in K-K$ and $0<=lambda<=1$,
    $
      (1-lambda)(K inter (K+x))
      +
      lambda(K inter (K+y))
      subset
      K inter
      (K+((1-lambda)x+lambda y)).
    $
    Brunn--Minkowski applied to this inclusion proves concavity of
    $c_K^(1/n)$. Superlevel sets of a concave function are convex; evenness
    makes them centrally symmetric. This proves ("OVERLAP STRATUM") and the
    existence of the half-crossing boundary.

    Apply the coarea theorem to the scalar map $c_K/V_K$ on the region
    between $Omega_beta subset Omega_alpha$. Its normal Jacobian is
    $norm(nabla c_K)/V_K$, which gives ("BOUNDARY SWEEP").

    For an interval of length $ell$, translating by $x$ leaves an overlap of
    length $(ell-abs(x))_+$. Substitution gives ("DYADIC FACE") and its
    exponential image.
  ],
  boundary: [
    What equals $1/2$ is the receiver-normalized overlap on the crossing
    face, not the unnormalized Hausdorff area of that face. The weighted
    surface measure in ("BOUNDARY SWEEP") is the derivative of swept interior
    volume and depends on the local curvature through
    $norm(nabla c_K)$. At a singular half level, the convex boundary remains
    defined, while the classical smooth integrand must be replaced by the
    corresponding measure-theoretic coarea statement.

    Convexity supplies a real positive crossing surface and a lawful
    change-of-boundary calculus. It does not identify every completed-zeta
    current with one convex-body covariogram.
  ],
)
