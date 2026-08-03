#let completed-source-seam-regularization = (
  key: "theorem:completed-source-seam-regularization",
  kind: [Theorem],
  title: [The Jordan incidence diverges at the half-seam while the completed seam retains strict capacity],
  status: [
    Exact zero--pole regularization, positive-divisor divergence, and
    strictly positive completed seam cell; two-variable continuation remains open
  ],
  depends: (
    "theorem:completed-source-common-founding-crossing",
  ),
  claim: [
    Fix
    $
      0<omega<1/2,
      quad
      p_0=1/2-omega,
      quad
      s_0=2p_0=1-2omega.
      quad "(HALF-SEAM)"
    $
    Retain the arithmetic, complementary, and completed transfers
    $
      A_omega(p)
      =
      frac(
        zeta(p+1/2-omega),
        zeta(p+1/2+omega)
      ),
    $
    $
      G_omega(p)
      =
      frac(
        Xi(p-omega),
        Xi(p+omega)
      )
      frac(1,A_omega(p)),
    $
    $
      S_omega(p)
      =
      A_omega(p)G_omega(p)
      =
      frac(
        Xi(p-omega),
        Xi(p+omega)
      ).
      quad "(SEPARATED AND COMPLETED)"
    $
    Put $rho(p)=p-p_0$ and regularize the internal cancellation by
    $
      tilde(A)_omega(p)
      =
      frac(A_omega(p),rho(p)),
      quad
      tilde(G)_omega(p)
      =
      rho(p)G_omega(p).
      quad "(SEAM REBASE)"
    $
    Both rebased faces are holomorphic and nonzero near $p_0$, and
    $
      S_omega
      =
      tilde(A)_omega tilde(G)_omega,
    $
    $
      tilde(A)_omega(p_0)
      =
      zeta(s_0),
      quad
      tilde(G)_omega(p_0)
      =
      frac(
        2xi(s_0),
        zeta(s_0)
      ).
      quad "(REBASED CROSSING)"
    $
    The opposed signs of the two values multiply to the positive completed
    face: $zeta(s_0)<0$ while $xi(s_0)>0$.

    The positive Jordan incidence does not itself converge to this
    rebased crossing.  At the seam, its raw cutoff is
    $
      A_(omega,X)^"raw"(p_0)
      =
      sum_(n<=X)
      w_omega(n)n^(-p_0)
      =
      sum_(n<=X)
      frac(J_(2omega)(n),n).
      quad "(RAW JORDAN SEAM)"
    $
    Every summand is positive and
    $
      A_(omega,X)^"raw"(p_0)
      tilde.op
      frac(
        X^(2omega),
        2omega zeta(1+2omega)
      )
      arrow.r infinity.
      quad "(JORDAN PRESSURE)"
    $
    By contrast, meromorphic continuation gives
    $
      A_omega(p_0)=0.
      quad "(CONTINUED ZERO)"
    $
    Therefore no termwise positive limit of the Jordan gcd Gram can
    produce the seam.  Completion must supply a counterterm of at least
    the exact leading size in ("JORDAN PRESSURE") before the infinite
    receiver limit is taken.

    This counterterm does not erase the completed capacity.  For any
    scalar transfer $T$, define its right-half-plane defect kernel
    $
      cal(K)_T(p,q)
      =
      frac(
        1-T(p)overline(T(q)),
        p+overline(q)
      ).
      quad "(TRANSFER DEFECT)"
    $
    The product law and ("SEAM REBASE") give the regular identity
    $
      cal(K)_(S_omega)(p,q)
      =
      cal(K)_(tilde(A)_omega)(p,q)
      +
      tilde(A)_omega(p)
      overline(tilde(A)_omega(q))
      cal(K)_(tilde(G)_omega)(p,q).
      quad "(REGULARIZED CAPACITANCE)"
    $
    At the seam this becomes
    $
      cal(K)_(S_omega)(p_0,p_0)
      =
      frac(
        1-zeta(s_0)^2,
        s_0
      )
      +
      frac(
        zeta(s_0)^2-4xi(s_0)^2,
        s_0
      )
      =
      frac(
        1-4xi(s_0)^2,
        s_0
      )
      >0.
      quad "(STRICT COMPLETED CELL)"
    $
    The two finite summands do not have fixed signs.  As
    $s_0 arrow.r 1^-$, $zeta(s_0) arrow.r -infinity$, so the first is
    negative and the second positive.  As $s_0 arrow.r 0^+$,
    $
      zeta(s_0) arrow.r -1/2,
      quad
      2xi(s_0) arrow.r 1,
    $
    so the first is positive and the second negative.  Their changing
    orientations are a genuine swing between the two regularized faces;
    only their completed sum has the fixed positive seam orientation.
  ],
  proof: [
    The Laurent expansion
    $
      zeta(1+rho)=frac(1,rho)+O(1)
    $
    gives
    $
      A_omega(p)
      =
      zeta(s_0)rho(p)+O(rho(p)^2).
    $
    The completed ratio is regular and nonzero at $p_0$, with
    $
      S_omega(p_0)
      =
      frac(
        Xi(1/2-2omega),
        Xi(1/2)
      )
      =
      frac(xi(s_0),xi(1))
      =
      2xi(s_0).
    $
    Dividing and multiplying by $rho$ prove ("REBASED CROSSING").
    On $0<s_0<1$, the alternating eta representation gives
    $zeta(s_0)<0$, while the defining completed product gives
    $xi(s_0)>0$.

    The generalized Jordan identity
    $
      J_(2omega)(n)
      =
      sum_(d m=n)
      mu(d)m^(2omega)
    $
    gives
    $
      sum_(n<=X)frac(J_(2omega)(n),n)
      =
      sum_(d<=X)
      frac(mu(d),d)
      sum_(m<=X/d)m^(2omega-1).
    $
    Since
    $
      sum_(m<=Y)m^(2omega-1)
      tilde.op frac(Y^(2omega),2omega)
    $
    and
    $
      sum_(d>=1)
      frac(mu(d),d^(1+2omega))
      =
      frac(1,zeta(1+2omega)),
    $
    partial summation proves ("JORDAN PRESSURE").  Positivity of every
    summand proves that this is not an ordinary convergent realization of
    ("CONTINUED ZERO").

    For arbitrary scalar functions $A,G$, direct expansion gives
    $
      1-A(p)G(p)overline(A(q)G(q))
      =
      (
        1-A(p)overline(A(q))
      )
      +
      A(p)overline(A(q))
      (
        1-G(p)overline(G(q))
      ).
    $
    Apply this to the two rebased faces and divide by
    $p+overline(q)$ to prove ("REGULARIZED CAPACITANCE").

    Finally put
    $
      theta_+(x)
      =
      sum_(n>=1)e^(-pi n^2 x).
    $
    The completed theta integral is
    $
      xi(s)
      =
      frac(1,2)
      +
      frac(s(s-1),2)
      integral_1^infinity
      theta_+(x)
      (
        x^(s/2)+x^((1-s)/2)
      )
      frac(dif x,x).
    $
    For $0<s<1$, its integral is strictly positive and $s(s-1)<0$, so
    $xi(s)<1/2$.  Positivity of $xi(s)$ was established above.  Therefore
    $0<2xi(s_0)<1$, which proves ("STRICT COMPLETED CELL").  The endpoint
    limits of zeta and xi give the two asserted orientation reversals.
  ],
  boundary: [
    The requested Jordan factorization fails for a precise reason.  Its
    finite gcd Grams are positive, but their seam mass grows like
    $X^(2omega)$ and cannot converge to the analytically continued zero.
    Subtracting that mass only from the arithmetic face would destroy the
    causal identity of the current.  The counterterm belongs to the
    co-present completion, exactly as the pole in $G_omega$ cancels the
    zero in $A_omega$.

    The completed cancellation nevertheless leaves the strict scalar
    capacity ("STRICT COMPLETED CELL") at every
    $0<omega<1/2$.  This is an unconditional positive cell inside the
    target half-plane, not an RH assumption and not a numerical sample.
    It proves that the half-seam itself is not where completed passivity
    fails.

    A scalar diagonal cell is not yet positivity of the two-variable
    kernel.  The remaining local calculation is the first nontrivial
    crossing of two nearby receiver coordinates: equivalently, the
    $2 times 2$ determinant of $cal(K)_(S_omega)$ as both coordinates depart
    from $p_0$.  Put
    $
      L_xi(s)=frac(xi'(s),xi(s)).
    $
    Since
    $
      S_omega'(p_0)
      =
      2xi(s_0)
      (
        L_xi(s_0)-L_xi(1)
      ),
    $
    its infinitesimal Schwarz--Pick numerator is exactly
    $
      cal(Q)(s_0)
      =
      (
        1-4xi(s_0)^2
      )^2
      -
      4s_0^2 xi(s_0)^2
      (
        L_xi(s_0)-L_xi(1)
      )^2.
      quad "(SEAM CROSSING CURVATURE)"
    $
    Nonnegativity of this quantity is the first nearby two-receiver
    obligation.  Its sign is not established here.  The Jordan
    incidence may enter only after the divergent common mode and its
    completion counterterm are paired; it cannot be inserted as an
    independently positive infinite Gram.
  ],
)
