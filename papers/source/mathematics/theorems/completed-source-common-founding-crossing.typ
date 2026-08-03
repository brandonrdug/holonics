#let completed-source-common-founding-crossing = (
  key: "theorem:completed-source-common-founding-crossing",
  kind: [Theorem],
  title: [Common founding and reunion factor every source crossing, but only the completed current is causal],
  status: [
    Exact Jordan meet--join law, gcd crossing partition, Möbius foil, and
    arithmetic--archimedean completion seam; the coupled frame sign remains open
  ],
  depends: (
    "theorem:completed-source-volterra-frame-defect",
    "theorem:divisor-source-transport-boundary",
  ),
  claim: [
    Fix $omega>0$ and define the generalized Jordan atom
    $
      J_(2omega)(n)
      =
      n^(2omega)
      product_(p divides n)
      (1-p^(-2omega)),
      quad
      J_(2omega)(1)=1.
      quad "(DIVISOR ATOM)"
    $
    The completed source coefficients are exactly
    $
      c_omega(n)
      =
      frac(J_(2omega)(n),n^omega),
      quad
      w_omega(n)
      =
      frac(J_(2omega)(n),n^(omega+1/2)).
      quad "(SOURCE ATOM)"
    $
    Their divisor cumulative is
    $
      sum_(d divides n)J_(2omega)(d)=n^(2omega).
      quad "(CUMULATIVE AXIS)"
    $
    Consequently, if
    $
      u_n(d)
      =
      sqrt(J_(2omega)(d))
      bold(1)_(d divides n),
    $
    then
    $
      chevron.l u_m,u_n chevron.r
      =
      gcd(m,n)^(2omega),
      quad "(GCD GRAM)"
    $
    and the normalized incidence vectors
    $v_n=n^(-omega)u_n$ satisfy
    $
      chevron.l v_m,v_n chevron.r
      =
      (
        frac(gcd(m,n),lcm(m,n))
      )^omega.
      quad "(VALUATION DISTANCE)"
    $
    Thus the generalized Jordan population is a positive divisor-axis
    incidence before it becomes a source amplitude.

    The source amplitude itself is modular on the divisor lattice:
    $
      w_omega(m)w_omega(n)
      =
      w_omega(gcd(m,n))
      w_omega(lcm(m,n)).
      quad "(FOUNDING--REUNION LAW)"
    $
    Equivalently, write
    $
      d=gcd(m,n),
      quad m=d a,
      quad n=d b,
      quad gcd(a,b)=1.
    $
    With
    $
      eta_(omega,d)(a)
      =
      a^(omega-1/2)
      product_(
        p divides a;
        p divides.not d
      )
      (1-p^(-2omega)),
      quad "(CONTEXTUAL ARM)"
    $
    one has
    $
      w_omega(d a)=w_omega(d)eta_(omega,d)(a),
    $
    $
      w_omega(m)w_omega(n)
      =
      w_omega(d)^2
      eta_(omega,d)(a)
      eta_(omega,d)(b)
      =
      w_omega(d)w_omega(d a b).
      quad "(CROSSING WEIGHT)"
    $
    The arm therefore depends on which prime axes have already been
    founded in $d$; the same integer ratio is not an absolute detached
    constituent.

    This meet--join law gives the exact crossing expansion of the causal
    energy.  Let
    $
      G_F=phi_omega ast F
    $
    on the positive logarithmic ray, extended by zero to negative time,
    and for a finite receiver $tau$ put
    $
      b_n^(tau)(r)
      =
      w_omega(n)
      G_F(r-log n)
      bold(1)_(0<r<tau).
      quad "(ADMITTED EVENT FACE)"
    $
    Local finiteness gives
    $
      cal(V)_(omega,tau)F
      =
      sum_(n<e^tau)b_n^(tau).
    $
    Partitioning every ordered pair by its unique common founding gives
    $
      norm(cal(V)_(omega,tau)F)^2
      =
      sum_(d<e^tau)cal(C)_(d,tau)(F),
      quad "(FOUNDING PARTITION)"
    $
    where
    $
      cal(C)_(d,tau)(F)
      =
      sum_(
        a,b>=1;
        gcd(a,b)=1
      )
      chevron.l
        b_(d a)^(tau),
        b_(d b)^(tau)
      chevron.r.
      quad "(COPRIME ARMS)"
    $
    Each summand uses the common founding $d$, the two coprime arms, and
    the reunion label $d a b$ through ("CROSSING WEIGHT").

    A founding layer is not, however, an independently positive energy.
    Its coprime incidence matrix
    $
      C_(a,b)=bold(1)_(gcd(a,b)=1)
    $
    already has the principal minor on ${1,p}$
    $
      mat(1,&1;1,&0),
      quad det=-1.
      quad "(INDEFINITE ARM CELL)"
    $
    The exact resolution is Möbius-signed:
    $
      cal(C)_(d,tau)(F)
      =
      sum_(k>=1)
      mu(k)
      norm(
        sum_(j>=1)b_(d k j)^(tau)
      )^2.
      quad "(MOBIUS FOIL)"
    $
    The first opposed square occurs at every prime $p$ because
    $mu(p)=-1$.  Summing all founding layers reconstitutes the one coherent
    current rather than a population of positive independent cells:
    $
      sum_d cal(C)_(d,tau)(F)
      =
      sum_(q>=1)
      (
        sum_(k divides q)mu(k)
      )
      norm(
        sum_(j>=1)b_(q j)^(tau)
      )^2
      =
      norm(
        sum_(j>=1)b_j^(tau)
      )^2.
      quad "(GLOBAL RECONSTITUTION)"
    $

    The same inseparability is visible between the arithmetic and
    archimedean faces.  On a finite cut define
    $
      (cal(A)_(omega,tau)G)(r)
      =
      sum_(log n<=r)
      w_omega(n)G(r-log n),
      quad "(ARITHMETIC ADMISSION)"
    $
    and
    $
      (cal(G)_(omega,tau)F)(r)
      =
      integral_0^r
      phi_omega(r-s)F(s)dif s.
      quad "(ARCHIMEDEAN RESPONSE)"
    $
    Causality gives the exact cascade
    $
      cal(V)_(omega,tau)
      =
      cal(A)_(omega,tau)
      cal(G)_(omega,tau).
      quad "(COMPLETED CURRENT)"
    $
    Therefore its shared bipolar defect is the coupled capacitance
    $
      I-cal(V)^*cal(V)
      =
      (
        I-cal(G)^*cal(G)
      )
      -
      cal(G)^*
      (
        cal(A)^*cal(A)-I
      )
      cal(G).
      quad "(COUPLED CAPACITANCE)"
    $
    Neither parenthesis has been assigned a sign; only their exact
    difference is the physical source defect.

    The arithmetic load is genuinely expansive after the first nontrivial
    admission.  For every $tau>log 2$, choose a nonzero nonnegative $G$
    supported in $(0,delta)$ with
    $
      0<delta<min(log 2,tau-log 2).
    $
    The $n=1$ and $n=2$ response faces are disjoint, while every other
    admitted face is pointwise nonnegative.  Hence
    $
      norm(cal(A)_(omega,tau)G)^2
      >=
      (
        1+w_omega(2)^2
      )
      norm(G)^2
      >
      norm(G)^2.
      quad "(ARITHMETIC PRESSURE)"
    $
    Thus the second term in ("COUPLED CAPACITANCE") is an actual load, not
    a sign convention that can be removed by declaring the arithmetic
    subsystem passive.

    Indeed the separation is singular inside the target causal
    half-plane.  In the initial Dirichlet convergence region,
    $
      hat(A)_omega(p)
      :=
      sum_(n>=1)w_omega(n)n^(-p)
      =
      frac(
        zeta(p+1/2-omega),
        zeta(p+1/2+omega)
      ),
      quad
      op("Re")p>1/2+omega.
      quad "(ARITHMETIC TRANSFER)"
    $
    The completed and complementary transfers are
    $
      hat(psi)_omega(p)
      =
      frac(Xi(p-omega),Xi(p+omega)),
    $
    $
      hat(G)_omega(p)
      =
      frac(hat(psi)_omega(p),hat(A)_omega(p)).
      quad "(COMPLEMENTARY TRANSFER)"
    $
    For $0<omega<1/2$, put
    $
      p_0=1/2-omega>0.
    $
    Meromorphic continuation of ("ARITHMETIC TRANSFER") has a simple zero
    at $p_0$ because its denominator is $zeta(1)$, while
    $hat(psi)_omega(p_0)$ is finite and nonzero.  Consequently
    $hat(G)_omega$ has the compensating simple pole:
    $
      hat(A)_omega(p)
      =
      zeta(1-2omega)(p-p_0)
      +O((p-p_0)^2),
    $
    $
      hat(G)_omega(p)
      =
      frac(
        hat(psi)_omega(p_0),
        zeta(1-2omega)
      )
      frac(1,p-p_0)
      +O(1).
      quad "(COMPLETION SEAM)"
    $
    The zero and pole cancel in
    $hat(psi)_omega=hat(A)_omega hat(G)_omega$.  At $omega=1/2$ this seam
    reaches the boundary $p=0$; for $omega>1/2$ it lies outside the causal
    right half-plane.
  ],
  proof: [
    The first identity in ("SOURCE ATOM") is the definition of
    $c_omega$.  Dividing once more by $sqrt(n)$ gives the second.
    Both $J_(2omega)$ and the divisor sum in ("CUMULATIVE AXIS") are
    multiplicative.  At $n=p^a$ the sum telescopes:
    $
      1+
      sum_(j=1)^a
      (
        p^(2omega j)-p^(2omega(j-1))
      )
      =
      p^(2omega a).
    $
    This proves ("CUMULATIVE AXIS") and hence the two Gram identities.

    At each prime axis, the minimum and maximum of the two valuations are
    the valuations of the gcd and lcm.  If both valuations are positive,
    each side of
    $
      J(m)J(n)=J(gcd(m,n))J(lcm(m,n))
    $
    carries the same two factors $1-p^(-2omega)$ and the same total
    exponent.  If one valuation is zero, each side carries one such
    factor.  Multiplication over primes and
    $m n=gcd(m,n)lcm(m,n)$ prove ("FOUNDING--REUNION LAW").
    Comparing the prime supports of $d a$ and $d$ proves
    ("CONTEXTUAL ARM") and ("CROSSING WEIGHT").

    Substitute
    $
      psi_omega
      =
      sum_n w_omega(n)
      phi_omega(dot-log n)
    $
    into causal convolution.  This gives the admitted event sum.
    Expanding its squared norm and assigning $(m,n)$ to
    $d=gcd(m,n)$ proves ("FOUNDING PARTITION") and ("COPRIME ARMS").

    The displayed two-arm determinant proves
    ("INDEFINITE ARM CELL").  Möbius inversion gives
    $
      bold(1)_(gcd(a,b)=1)
      =
      sum_(k divides a,\ k divides b)mu(k).
    $
    Substitute this into ("COPRIME ARMS") and put
    $a=k i$, $b=k j$ to obtain ("MOBIUS FOIL").  Then put $q=d k$ and
    use
    $
      sum_(k divides q)mu(k)
      =
      cases(1,&q=1,0,&q>1)
    $
    to prove ("GLOBAL RECONSTITUTION").

    Associativity of causal convolution gives ("COMPLETED CURRENT").
    Add and subtract $cal(G)^*cal(G)$ in
    $I-cal(G)^*cal(A)^*cal(A)cal(G)$ to prove
    ("COUPLED CAPACITANCE").
    For the pulse in ("ARITHMETIC PRESSURE"), its translate by $log 2$ is
    disjoint from the original.  The remaining translated faces have
    nonnegative coefficients and nonnegative values, so they cannot reduce
    the pointwise sum.  Pythagoras for the first two faces proves the
    displayed strict lower bound.

    Finally,
    $
      sum_(n>=1)
      frac(J_(2omega)(n),n^s)
      =
      frac(zeta(s-2omega),zeta(s))
    $
    for $op("Re")s>1+2omega$.  Substitution
    $s=p+omega+1/2$ proves ("ARITHMETIC TRANSFER").
    Evenness of $Xi$ changes the transfer from
    $Xi(omega-p)/Xi(omega+p)$ to the displayed completed ratio.
    At $p_0=1/2-omega$, the denominator argument in
    ("ARITHMETIC TRANSFER") is one and the numerator argument is
    $1-2omega$.  The zeta pole has residue one, while zeta has no real
    zero in $(0,1)$.  The completed ratio is finite and nonzero there.
    The two local Laurent expansions therefore give ("COMPLETION SEAM").
  ],
  boundary: [
    The gcd was the correct common-founding coordinate, but positivity
    cannot be assigned one founding at a time.  A cross between the
    $1$-arm and the $p$-arm belongs to founding $d$, whereas the
    self-interaction of the $p$-arm belongs to founding $d p$.  Möbius
    parity is the exact foil which prevents those perspectives from being
    counted twice.  The negative square at $k=p$ is therefore not evidence
    against the whole source; it proves that independent positive
    common-founding blocks are the wrong proof object.

    The completion seam gives the same warning at the continuum boundary.
    In $0<omega<1/2$, neither the arithmetic admissions nor the
    archimedean response defines a bounded causal subsystem on the whole
    target half-plane: their internal zero and pole cancel only in the
    completed current.  A proof may use the factorization on finite cuts,
    but it may not prove passivity of the two factors separately and then
    compose them.

    What remains is now narrower than an unspecified Bessel estimate.  It
    is the coupled inequality
    $
      I-cal(G)^*cal(G)
      >=
      cal(G)^*
      (
        cal(A)^*cal(A)-I
      )
      cal(G)
      quad "(COMPLETED CAPACITANCE BOUND)"
    $
    on every finite cut, with the Möbius-signed common-founding crossings
    retained inside the right side and the completion seam retained inside
    the left.  A valid square decomposition must pair those two before
    either is collapsed.  The existing identities do not determine that
    orientation.  This is the first genuine signed term reached by the
    requested source expansion, not a reformulation introduced in place
    of the calculation.
  ],
)
