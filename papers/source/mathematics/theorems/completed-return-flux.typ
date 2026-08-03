#let completed-return-flux = (
  key: "theorem:completed-return-flux",
  kind: [Theorem],
  title: [The completed local metrics form one normal return field],
  status: [
    Exact Euler--Gamma--endpoint synthesis and equivalent positive-real,
    Stieltjes, and connected-moment formulations of the RH sign
  ],
  depends: (
    "lemma:mellin-return-seam",
    "lemma:weighted-mellin-basis-rebase",
    "theorem:prime-wheel-euler-transport",
    "theorem:conditioned-support-quotient-shorting",
    "theorem:weil-support-induction-reduction",
  ),
  claim: [
    Normalize the completed zeta function by
    $
      xi(s)
      =
      frac(1,2)s(s-1)pi^(-s/2)Gamma(s/2)zeta(s),
      quad
      Xi(z)=xi(1/2+z).
    $
    For $s=sigma+i t$ with $sigma>1$, define the positive local return
    metrics
    $
      cal(K)_0(s)=abs(s(s-1))^2,
      quad
      cal(K)_infinity(s)
      =
      pi^(-sigma)abs(Gamma(s/2))^2,
    $
    $
      cal(K)_p(s)=abs(1-p^(-s))^(-2).
      quad "(LOCAL METRICS)"
    $
    The Euler product gives the exact factorization
    $
      abs(xi(s))^2
      =
      frac(1,4)
      cal(K)_0(s)cal(K)_infinity(s)
      product_p cal(K)_p(s).
      quad "(COMPLETED RETURN METRIC)"
    $
    Its outward normal logarithmic current is
    $
      cal(V)(sigma,t)
      =
      partial_sigma log abs(xi(s))^2
      =
      2op("Re")frac(xi'(s),xi(s))
    $
    $
      =
      2op("Re")(
        frac(1,s)+frac(1,s-1)
      )
      +op("Re")psi(s/2)-log pi
    $
    $
      space -2
      sum_p sum_(m>=1)
      (log p)p^(-m sigma)cos(m t log p).
      quad "(LOCAL-TO-COMPLETED FLUX)"
    $
    Thus the endpoint, Gamma/archimedean, and complete prime-power
    responses are not separate loads: in their common half-plane they are
    the three local faces of one covector
    $d log abs(xi)^2$.

    Center the seam by $z=x+i t$ and put
    $
      F(z)=frac(Xi'(z),Xi(z)).
    $
    Then
    $
      cal(V)(1/2+x,t)=2op("Re")F(x+i t).
      quad "(CENTERED NORMAL FIELD)"
    $
    If the normal coordinate is reparameterized by $x=x(tau)$, its
    reported component becomes
    $
      cal(V)_tau=dot(x)(tau)cal(V)_x.
      quad "(NORMAL COVARIANCE)"
    $
    Positivity below is therefore oriented toward the declared half-plane
    $x>0$; reversing the receiver normal reverses the reported current.

    The following statements are equivalent:

    - every nontrivial zero of $zeta$ lies on $op("Re")(s)=1/2$;
    - $F$ is holomorphic on $x>0$ and
      $
        op("Re")F(z)>=0
        quad "for every "op("Re")(z)>0;
        quad "(POSITIVE-REAL FIELD)"
      $
    - for any $c>0$, the Cayley scattering face
      $
        cal(S)_c(z)
        =
        frac(F(z)-c,F(z)+c)
        =
        frac(Xi'(z)-c Xi(z),Xi'(z)+c Xi(z))
        quad "(SCATTERING FACE)"
      $
      is a Schur function on the right half-plane and is inner at almost
      every regular point of its boundary;
    - the genus-zero entire function
      $
        H(w)=frac(Xi(sqrt(w)),Xi(0))
        quad "(SQUARED-AXIS RETURN)"
      $
      has only negative real zeros; and
    - its impedance
      $
        Z(w)=frac(H'(w),H(w)),
        quad
        F(z)=2z Z(z^2),
        quad "(STIELTJES IMPEDANCE)"
      $
      is a Stieltjes transform of a positive measure on
      $[0,infinity)$.

    Under these equivalent statements, if the critical ordinates are
    $gamma$ with multiplicities $m_gamma$, then
    $
      Z(w)
      =
      sum_(gamma>0)
      frac(m_gamma,w+gamma^2),
      quad
      op("Re")F(x+i t)
      =
      sum_gamma
      m_gamma frac(x,x^2+(t-gamma)^2).
      quad "(POISSON RETURN)"
    $
    Hence
    $
      dif mu_x(t)
      =
      frac(1,pi)op("Re")F(x+i t)dif t
    $
    is a positive receiver measure, and it converges weakly as
    $x arrow.r 0^+$ to the complete zero-counting measure
    $
      dif mu_0=sum_gamma m_gamma delta_gamma.
      quad "(BOUNDARY RETURN)"
    $

    For an admissible current $f$, let
    $
      A_f(z)=cal(M)f(1/2+z).
    $
    The completed Weil response is then the boundary normal energy of the
    same return metric:
    $
      Q_W(f)
      =
      lim_(x arrow.r 0^+)
      frac(1,2pi)
      integral_RR
      abs(A_f(i t))^2
      partial_x log abs(Xi(x+i t))^2
      dif t
    $
    $
      =
      sum_gamma m_gamma abs(A_f(i gamma))^2.
      quad "(WEIL AS BOUNDARY FLUX)"
    $
    Moment conditioning, support restriction, and old-body relaxation act
    on this one quadratic form.  In particular, whenever the normal field
    is positive, every conditioned support short is nonnegative because it
    is the infimum of a nonnegative boundary-flux energy.  Conversely,
    nonnegativity of the complete nested family of conditioned shorts gives
    Weil positivity and therefore the first equivalent statement.

    There is an exact coefficient receiver which does not enumerate zeros.
    Write
    $
      H(w)=sum_(n>=0)h_n w^n,
      quad h_0=1,
      quad
      Z(w)=sum_(n>=0)c_n w^n,
      quad
      mu_n=(-1)^n c_n.
    $
    The relation $H'=H Z$ gives the source recursion
    $
      c_n
      =
      (n+1)h_(n+1)
      -
      sum_(k=1)^n h_k c_(n-k).
      quad "(CONNECTED RETURN)"
    $
    The RH statements above are further equivalent to the simultaneous
    positive-semidefiniteness, for every $N$, of the two Hankel populations
    $
      [mu_(i+j)]_(0<=i,j<=N)>=0,
      quad
      [mu_(i+j+1)]_(0<=i,j<=N)>=0.
      quad "(STIELTJES GRAM LAW)"
    $
    The first connected members are
    $
      mu_0=h_1,
      quad
      mu_1=h_1^2-2h_2,
    $
    $
      mu_2=h_1^3-3h_1h_2+3h_3,
    $
    $
      mu_3
      =
      h_1^4-4h_1^2h_2+2h_2^2+4h_1h_3-4h_4.
      quad "(FIRST CONNECTED MEMBERS)"
    $
    Thus the remaining sign can be attacked as one uniform Gram
    factorization of the connected return sequence derived from the
    archimedean theta moments, rather than by checking zeros or support
    cells one at a time.
  ],
  proof: [
    For $sigma>1$, take absolute squares in the completed Euler product.
    Logarithmic differentiation is justified by absolute convergence.
    The endpoint and Gamma factors give
    $
      partial_sigma log cal(K)_0
      =
      2op("Re")(
        frac(1,s)+frac(1,s-1)
      ),
    $
    $
      partial_sigma log cal(K)_infinity
      =
      op("Re")psi(s/2)-log pi.
    $
    For a finite place, the norm-convergent geometric series gives
    $
      partial_sigma log cal(K)_p
      =
      -2(log p)
      sum_(m>=1)p^(-m sigma)cos(m t log p).
    $
    Their sum proves ("LOCAL-TO-COMPLETED FLUX").  The chain rule proves
    ("NORMAL COVARIANCE").

    The functional equation and reality give
    $Xi(-z)=Xi(z)$ and
    $Xi(overline(z))=overline(Xi(z))$.  Pairing opposite zeros in the
    Hadamard product removes the genus-one exponentials:
    $
      Xi(z)
      =
      Xi(0)
      product_(a mod plus.minus)
      (1-z^2/a^2).
    $
    If RH holds, every representative is $a=i gamma$, so
    $
      F(z)
      =
      sum_(gamma>0)m_gamma
      (
        frac(1,z-i gamma)+frac(1,z+i gamma)
      ).
    $
    Every summand has positive real part for $op("Re")(z)>0$, proving
    ("POSITIVE-REAL FIELD") and ("POISSON RETURN").  Conversely, a zero of
    $Xi$ in the right half-plane is a pole of $F$ whose real part changes
    sign in every punctured neighborhood.  Positive-realness excludes such
    a zero.  Evenness then excludes zeros in the left half-plane, so all
    zeros lie on the fixed seam.  The Cayley transform carries the right
    half-plane to the unit disk; boundary reality of
    $Xi(i t)$ makes its regular boundary values unimodular.  This proves the
    scattering equivalence.

    Evenness makes $H$ an entire function of $w=z^2$ of genus zero.  The
    centered zeros $z=plus.minus i gamma$ become the negative roots
    $w=-gamma^2$.  Logarithmic differentiation gives
    ("STIELTJES IMPEDANCE").  Conversely, a Stieltjes logarithmic derivative
    can have singularities only on the negative real axis, while every zero
    of $H$ is a pole of $H'/H$ with positive integral residue.  Hence the
    Stieltjes property forces all zeros of $H$ to be negative real.

    The Poisson-kernel approximation to the identity proves
    ("BOUNDARY RETURN").  Since a compactly supported smooth Mellin current
    has rapidly decreasing seam amplitude, it may be used as the test
    function in that weak limit.  The Mellin adjoint-return identity and the
    completed explicit formula then give ("WEIL AS BOUNDARY FLUX").
    Nonnegative forms remain nonnegative under restriction and form
    shorting.  The converse through nested support is the established Weil
    support-induction reduction.

    Finally, $H'=H Z$ proves ("CONNECTED RETURN").  If RH holds, then
    $
      mu_n
      =
      sum_(gamma>0)m_gamma gamma^(-2n-2),
    $
    so both matrices in ("STIELTJES GRAM LAW") are Gram matrices of the
    positive measure
    $sum_(gamma>0)m_gamma gamma^(-2)delta_(gamma^(-2))$.
    Conversely, the Stieltjes moment theorem applied to the two Hankel
    populations produces a positive measure on $[0,infinity)$.  Cauchy
    bounds for the Taylor series of $Z$ make this measure compactly
    supported, and
    $
      Z(w)=integral frac(1,1+t w)dif nu(t)
    $
    near the origin.  Analytic continuation then makes $Z$ a Stieltjes
    function, proving RH by the preceding equivalence.  Expanding
    ("CONNECTED RETURN") gives ("FIRST CONNECTED MEMBERS").
  ],
  boundary: [
    The theorem identifies the single proof-bearing field; it does not
    assume that positivity of each local metric signs its normal derivative.
    The source-side task is now precise: factor every connected Hankel
    population in ("STIELTJES GRAM LAW"), or equivalently construct the
    completed scattering face as an inner contraction, from the
    Euler--Gamma--theta data without importing the zero locations.

    If RH is false, a non-fixed zero orbit
    $z$ and $J(z)=-overline(z)$ contributes
    $
      2op("Re")(
        A_f(z) overline(A_f(J(z)))
      )
    $
    to the returned Weil response.  Its two-arm Gram has one positive and
    one negative direction.  This is the exact unabsorbed interior residue:
    not a missing scalar load, but a pole of the completed normal field
    between the Euler half-plane and the fixed seam.
  ],
)
