#let normalized-euler-resolvent-return = (
  key: "lemma:normalized-euler-resolvent-return",
  kind: [Lemma],
  title: [The normalized Euler resolvent folds every prime-power return into one amplitude],
  status: [Exact operator-norm factorization of the finite-prime response],
  depends: (
    "theorem:euler-successor-geometry",
    "theorem:euler-metric-recurrence",
    "theorem:prime-power-aperture-incidence",
  ),
  claim: [
    Let $U$ be unitary on a complex Hilbert space, let $0<a<1$, and put
    $
      J_a=I-a U,
      quad
      G_a=J_a^*J_a,
      quad
      d_a=sqrt(1-a^2).
    $
    The normalized Euler resolvent
    $
      cal(R)_a
      =
      d_a J_a^(-1)
      =
      d_a sum_(n>=0)a^n U^n
    $
    is independently defined by an operator-norm convergent Neumann series.
    Its returned metric is
    $
      cal(R)_a^*cal(R)_a
      =
      (1-a^2)G_a^(-1)
      =
      I+sum_(m>=1)a^m(U^m+(U^*)^m).
      quad "(POISSON)"
    $

    For a prime $p$, take
    $
      a=p^(-1/2),
      quad
      ell_p=log p,
      quad
      U=U_(ell_p).
    $
    Whenever the logarithmic current $x$ represents a returned test current
    $h=f ast f^sharp$, the finite-place response is exactly
    $
      W_p(h)
      =
      ell_p(
        norm(cal(R)_p x)^2-norm(x)^2
      ).
      quad "(PRIME AMPLITUDE)"
    $

    The same resolvent is the fixed-state response of the lossless two-port
    operator
    $
      cal(J)_a
      =
      mat(
        a U,d_a I;
        d_a I,-a U^*
      ),
      quad
      cal(J)_a^*cal(J)_a=I.
    $
    Indeed, the state equation
    $
      s=a U s+d_a x
    $
    has the unique solution $s=cal(R)_a x$.

    This resolvent is also the exact inverse of prime admission in the
    semilocal Poisson population.  For a finite receiver $S$ let
    $
      cal(M)_S
      =
      {m>=1: q ∤ m " for every finite " q in S}
    $
    and, wherever the sum converges absolutely, define
    $
      (cal(E)_S f)(x)
      =
      abs(x)^(1/2)
      sum_(m in cal(M)_S) f(m x).
    $
    If $p ∉ S$ and $(V_p phi)(x)=phi(p x)$ on
    $L^2(RR_+^*,dif^*x)$, then
    $
      cal(E)_(S union {p})
      =
      (I-p^(-1/2)V_p)cal(E)_S.
      quad "(ADMISSION)"
    $
    Therefore, with $J_p=I-p^(-1/2)V_p$,
    $
      cal(R)_p cal(E)_(S union {p})
      =
      sqrt(1-p^(-1))cal(E)_S.
      quad "(RETURN)"
    $
  ],
  proof: [
    Since $norm(a U)=a<1$, the Neumann series for $J_a^(-1)$ converges in
    operator norm.  The operator $J_a$ is normal because it is a polynomial
    in the unitary $U$.  Hence
    $
      cal(R)_a^*cal(R)_a
      =
      (1-a^2)(J_a^*J_a)^(-1).
    $
    Expanding both resolvents gives
    $
      (1-a^2)
      sum_(r,s>=0)a^(r+s)U^((s-r)).
    $
    The coefficient of $U^m$ and of $U^(-m)$ is $a^m$ for every $m>=1$,
    while the coefficient of $I$ is one.  This proves ("POISSON") in
    operator norm.

    Taking the quadratic response of ("POISSON") gives
    $
      norm(cal(R)_a x)^2-norm(x)^2
      =
      2sum_(m>=1)a^m
      op("Re") chevron.l x,U^m x chevron.r.
    $
    The prime-power aperture-incidence theorem identifies the right side,
    after multiplication by $ell_p$, with $W_p(h)$.

    Direct block multiplication proves that $cal(J)_a$ is unitary because
    $a^2+d_a^2=1$ and $d_a$ commutes with $U$.  Solving its first-row fixed
    state equation gives the displayed resolvent.

    Finally,
    $
      cal(M)_S
      =
      cal(M)_(S union {p})
      union
      p cal(M)_S,
      quad "(disjoint)".
    $
    Splitting the defining sum for $cal(E)_S$ along this disjoint union
    gives
    $
      cal(E)_S f
      =
      cal(E)_(S union {p})f+p^(-1/2)V_p cal(E)_S f,
    $
    which is ("ADMISSION").  Applying $d_p J_p^(-1)$ gives ("RETURN").
  ],
  boundary: [
    This is a positive endpoint factorization of the entire signed
    prime-power response; it does not say that $W_p$ is positive.  For the
    translation representation, whose spectrum contains one,
    $
      norm(cal(R)_a)^2=(1+a)/(1-a)>1.
    $
    Thus the prime channel is not itself contractive.  The local Poisson
    metric in ("POISSON") and the monoid partition in ("ADMISSION") do not
    by themselves supply the global additive Poisson summation formula.
    That further relation conjugates additive Fourier transform with
    multiplicative inversion and fixes the compatible arithmetic
    principal-value normalization.  It is the missing source of cross-channel
    coupling, not an interchangeable name for the resolvent identity.
  ],
)
