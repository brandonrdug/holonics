#let divisor-source-transport-boundary = (
  key: "theorem:divisor-source-transport-boundary",
  kind: [Theorem],
  title: [A divisor-supported source transport must be diffuse and does not erase the global cut],
  status: [
    Exact finite-flow criterion, local-degree obstruction, and descendant-capacity
    separation; global congestion open
  ],
  depends: (
    "theorem:completed-scattering-hankel-successor",
    "theorem:prime-wheel-euler-transport",
  ),
  claim: [
    Fix $0<omega<1/2$.  Write
    $
      G_omega(r)=g_omega^("⟨1⟩")(r),
    $
    and let $y_omega$ be its unique zero in $(0,1)$.  Thus
    $
      G_omega(r)<0
      quad "for "0<r<y_omega,
      quad
      G_omega(r)>0
      quad "for "y_omega<r<1.
      quad "(SOURCE SIGN SEAM)"
    $
    For a finite scale $x>1/y_omega$, define
    $
      cal(N)^-_(omega,x)
      =
      {n in NN: n<=x, n/x<y_omega},
    $
    $
      cal(N)^+_(omega,x)
      =
      {m in NN: m<=x, m/x>y_omega},
    $
    with demands and capacities
    $
      d_(omega,x)(n)
      =
      c_omega(n)abs(G_omega(n/x)),
      quad n in cal(N)^-_(omega,x),
    $
    $
      b_(omega,x)(m)
      =
      c_omega(m)G_omega(m/x),
      quad m in cal(N)^+_(omega,x).
      quad "(SIGNED SOURCE MASSES)"
    $

    A divisor-supported transport is a nonnegative population
    $Pi_(omega,x)(n,m)$ which vanishes unless $n divides m$ and satisfies
    $
      sum_(m in cal(N)^+)Pi_(omega,x)(n,m)
      >=d_(omega,x)(n),
      quad "(DEMAND)"
    $
    $
      sum_(n in cal(N)^-)Pi_(omega,x)(n,m)
      <=b_(omega,x)(m).
      quad "(CAPACITY)"
    $
    Such a transport exists if and only if every subset
    $S subset.eq cal(N)^-_(omega,x)$ satisfies
    $
      sum_(n in S)d_(omega,x)(n)
      <=
      sum_(m in Gamma_x(S))b_(omega,x)(m),
      quad
      Gamma_x(S)
      =
      {m in cal(N)^+_(omega,x):
        " some "n in S" divides "m}.
      quad "(DIVISOR HALL CUT)"
    $

    The full Hall cut does not reduce the RH sign.  Since
    $1 in cal(N)^-_(omega,x)$ and $1$ divides every positive cell,
    $
      Gamma_x(cal(N)^-_(omega,x))
      =
      cal(N)^+_(omega,x).
    $
    Hence its Hall inequality is exactly
    $
      sum_(m in cal(N)^+)c_omega(m)G_omega(m/x)
      >=
      sum_(n in cal(N)^-)c_omega(n)abs(G_omega(n/x)),
    $
    or equivalently
    $
      h_omega^("⟨1⟩")(x)>=0.
      quad "(GLOBAL SOURCE CUT)"
    $
    A divisor-flow certificate is therefore a sufficient geometric
    realization of the source sign, but the abstract existence problem is
    a stronger condition which still contains the original RH-equivalent
    cut.

    Moreover, no bounded-degree local transport can work.  The exact
    small-r asymptotic is
    $
      G_omega(r)
      =
      -A_omega r^(omega-1)+O(r^(-1/2)),
    $
    where
    $
      A_omega
      =
      frac(4omega pi^omega,(1-2omega)Gamma(omega))
      op("B")(
        frac(3-2omega,2),
        omega
      )
      >0.
      quad "(OLD-CELL GROWTH)"
    $
    Put
    $
      M_omega
      =
      max_(y_omega<=r<=1)G_omega(r)<infinity.
    $
    If a transport carries the demand of one fixed integer $n$, then
    $
      op("card"){
        m in cal(N)^+_(omega,x):
        Pi_(omega,x)(n,m)>0
      }
    $
    is bounded below by
    $
      [
        frac(
          A_omega c_omega(n)n^(omega-1),
          M_omega
        )
        +o(1)
      ]
      x^(1-2omega)
      quad "as "x arrow.r infinity.
      quad "(DIFFUSE DEGREE)"
    $
    The required degree diverges because $1-2omega>0$.

    This is not an individual reachability obstruction.  Define the total
    positive descendant capacity
    $
      Z_(omega,x)(n)
      =
      sum_(
        m in cal(N)^+_(omega,x);
        n divides m
      )
      b_(omega,x)(m).
      quad "(DESCENDANT CAPACITY)"
    $
    For every fixed $n$, choose
    $y_omega<eta_0<eta_1<1$.  Prime descendants $m=n p$ with
    $
      eta_0 x/n<=p<=eta_1 x/n
    $
    give, by the prime number theorem,
    $
      Z_(omega,x)(n)
      >=
      C_(omega,n,eta_0,eta_1)
      frac(x^(1+omega),n^(1+omega)log x)
    $
    for all sufficiently large $x$, with a positive constant $C$.  Thus
    $
      frac(d_(omega,x)(n),Z_(omega,x)(n))
      =
      O_(omega,n)(
        frac(log x,x^(2omega))
      )
      arrow.r 0.
      quad "(INDIVIDUAL CAPACITY SURPLUS)"
    $
    Old cells have abundant descendants individually; the unresolved
    question is simultaneous sharing of those descendants.

    One canonical diffuse candidate makes that collision explicit.  When
    $Z_(omega,x)(n)>0$, put
    $
      Pi^prop_(omega,x)(n,m)
      =
      cases(
        d_(omega,x)(n)
        frac(b_(omega,x)(m),Z_(omega,x)(n)),
        &n divides m,
        0,&"otherwise".
      )
      quad "(PROPORTIONAL DESCENDANT FLOW)"
    $
    Every row then carries its exact demand.  Its load at a positive cell
    $m$ is
    $
      b_(omega,x)(m)
      C_(omega,x)(m),
    $
    where
    $
      C_(omega,x)(m)
      =
      sum_(
        n in cal(N)^-_(omega,x);
        n divides m
      )
      frac(d_(omega,x)(n),Z_(omega,x)(n)).
      quad "(DIVISOR CONGESTION)"
    $
    Therefore this explicit transport succeeds exactly when
    $
      C_(omega,x)(m)<=1
      quad
      "for every "m in cal(N)^+_(omega,x).
      quad "(CONGESTION LAW)"
    $
  ],
  proof: [
    The sign seam and the asymptotic formula follow from Suzuki's explicit
    incomplete-Beta expression for $G_omega$.  For
    $0<omega<1/2$, its $r^(omega-1)$ term dominates the
    $r^(-1/2)$ term at zero; changing the sign of $2omega-1$ gives the
    positive constant $A_omega$.

    Attach a source to a sink by an edge exactly when the source divides
    the sink, add a supersource with edge capacity $d_(omega,x)(n)$ to
    every negative cell, and add edges of capacity
    $b_(omega,x)(m)$ from positive cells to a supersink.  Infinite
    capacities on divisor edges turn the finite max-flow/min-cut theorem
    into ("DIVISOR HALL CUT").  The cell $1$ proves the full-neighborhood
    identity, and separating the positive and negative summands in the
    definition of $h_omega^("⟨1⟩")$ proves
    ("GLOBAL SOURCE CUT").

    For fixed $n$, ("OLD-CELL GROWTH") gives
    $
      d_(omega,x)(n)
      =
      [
        A_omega c_omega(n)n^(omega-1)+o(1)
      ]
      x^(1-omega).
    $
    Every positive cell has
    $
      b_(omega,x)(m)
      <=M_omega c_omega(m)
      <=M_omega x^omega.
    $
    Dividing the row demand by this maximum per-sink capacity proves
    ("DIFFUSE DEGREE").

    If $p$ is a sufficiently large prime not dividing fixed $n$, then
    $
      c_omega(n p)
      =
      c_omega(n)p^omega(1-p^(-2omega)).
    $
    On the closed receiver band $[eta_0,eta_1]$,
    $G_omega$ has a positive minimum.  Summing the resulting capacities
    over primes in the displayed interval and applying the prime number
    theorem proves ("INDIVIDUAL CAPACITY SURPLUS").

    Finally, summing ("PROPORTIONAL DESCENDANT FLOW") over $m$ gives
    $d_(omega,x)(n)$.  Summing it over divisors $n$ of a fixed $m$ gives
    $b_(omega,x)(m)C_(omega,x)(m)$, proving the equivalence with
    ("CONGESTION LAW").
  ],
  boundary: [
    This theorem invalidates a bounded local pairing of old cells with one
    or finitely many newer multiples.  The required transport is
    genuinely diffuse, with degree at least of order $x^(1-2omega)$ for
    every fixed old cell.

    It does not prove RH and it does not prove that divisor-supported
    transport exists.  The full Hall cut is exactly Suzuki's
    RH-equivalent source sign, so merely invoking max-flow would rename
    the obstruction.  The material reduction supplied here is narrower:
    individual reachability is not the problem, and the proportional
    construction isolates all remaining failure in the explicit divisor
    congestion $C_(omega,x)(m)$.

    Proving ("CONGESTION LAW") uniformly would be a valid source-derived
    proof.  A symbolic violation would refute this proportional flow but
    not every divisor flow or RH.  Any continuation must therefore
    analyze the displayed congestion itself; it may not return to an
    unspecified “uniform tail-energy inequality.”
  ],
)
