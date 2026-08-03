#let theta-positive-execution-lift = (
  key: "theorem:theta-positive-execution-lift",
  kind: [Theorem],
  title: [RH is the positive ordered-execution lift of the theta phase current],
  status: [Exact process-theoretic equivalence; explicit source factor remains open],
  depends: (
    "definition:ordered-causal-execution",
    "theorem:completed-theta-phase-current-bridge",
  ),
  claim: [
    Let
    $
      Xi(z)=xi(1/2+z),
      quad
      H_t(x)=abs(Xi(x+i t))^2,
    $
    and let $cal(V)_exp$ be the finite span of the bilateral-exponential
    receivers
    $
      a mapsto e^(p a),
      quad op("Re")p>0.
    $
    Define the polarized normal-current kernel
    $
      cal(M)(p,q)
      =
      frac(
        Xi'(p)overline(Xi(q))
        +
        Xi(p)overline(Xi'(q)),
        p+overline(q)
      ).
      quad "(NORMAL EXECUTION RESIDUAL)"
    $
    On the diagonal $p=x+i t$,
    $
      cal(M)(p,p)
      =
      frac(partial_x H_t(x),2x)
      =
      partial_r H_t(sqrt(r))
      quad
      (r=x^2).
      quad "(SQUARED-NORMAL CURRENT)"
    $

    The completed shifted kernels give actual signed finite events between
    positive receiver boundaries. Their symmetric derivative at the
    unshifted seam is the identity-carried theta execution current
    $Gamma_Xi$ whose residual Hermitian form has kernel $cal(M)$.
    Then the following statements are equivalent:

    - the Riemann Hypothesis;
    - $cal(M)$ is positive semidefinite on every finite co-present family of
      right-half-plane receivers;
    - $Gamma_Xi$ is a positive ordered-execution current, so its finite
      outward integrals are arrows of $op("Exec")_+$;
    - the theta phase current
      $
        cal(P)_0(a,b)
        =
        frac(c_Phi^2,2)
        integral_(abs((a+b)/2))^infinity
        y
        Phi(y+(a-b)/2)
        Phi(y-(a-b)/2)
        dif y
      $
      is nonnegative on $cal(V)_exp$; and
    - there are a Hilbert space $cal(K)$ and a linear residual executor
      $
        cal(R):cal(V)_exp arrow.r cal(K)
      $
      such that every finite exponential superposition $g$ satisfies
      $
        4integral_RR integral_RR
        g(a)cal(P)_0(a,b)overline(g(b))
        dif a dif b
        =
        norm(cal(R)g)^2.
        quad "(SOURCE RESIDUAL FACTORIZATION)"
      $

    Consequently, an explicit source-derived construction of $cal(R)$,
    together with the displayed identity on the complete declared receiver
    span, is a constructive proof of RH. Finite outward events then compose
    by residual addition, or equivalently by the transported fundamental
    theorem in the squared-normal coordinate $r=x^2$.
  ],
  proof: [
    `theorem:completed-theta-phase-current-bridge` proves that $cal(M)$ is
    four times the bilateral-Laplace pullback of $cal(P)_0$, and proves
    $
      "RH"
      arrow.l.r
      cal(M)>=0
      arrow.l.r
      cal(P)_0>=0
      " on "cal(V)_exp.
    $
    By `definition:ordered-causal-execution`, an identity-carried tangent is
    a positive execution current exactly when its residual form is positive.
    Matrix positivity of $cal(M)$ is precisely positivity under every finite
    co-present receiver family.

    A positive Hermitian form admits a Kolmogorov--GNS factorization, giving
    $cal(R)$ and ("SOURCE RESIDUAL FACTORIZATION"). Conversely, that
    factorization makes the quadratic form a squared norm and hence
    nonnegative. This proves all equivalences.

    Finally, for $r_1<=r_2$, integration of the normal current gives
    $
      H_t(sqrt(r_2))-H_t(sqrt(r_1))
      =
      integral_(r_1)^(r_2)
      partial_r H_t(sqrt(r))
      dif r.
    $
    Positive residuals are closed under integration and under the residual
    composition law, so an exact positive infinitesimal executor composes
    into every finite outward successor.
  ],
  boundary: [
    Abstractly invoking a square root, GNS construction, or reproducing
    kernel does not prove RH: each exists here exactly when the unresolved
    sign is already known. The proof-bearing construction must derive
    $cal(R)$ directly from the theta source $Phi$, the opposed coordinates
    $(a-b)/2$, and the moving boundary $abs((a+b)/2)$.

    The theorem defines the exact algorithmic proof object; it does not claim
    that the present software engine has constructed it. A numerical
    execution on finitely many receivers is testimony, while an exact rule
    valid on arbitrary finite exponential superpositions is the proof.
  ],
)
