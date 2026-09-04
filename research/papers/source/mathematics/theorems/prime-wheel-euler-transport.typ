#let prime-wheel-euler-transport = (
  key: "theorem:prime-wheel-euler-transport",
  kind: [Theorem],
  title: [The prime wheel, Möbius cut, and Euler return are one transported incidence],
  status: [
    Exact synthesis of unique factorization, CRT, arithmetic Möbius
    inclusion--exclusion, and the established Mellin/Euler transport
  ],
  depends: (
    "definition:prime-valuation-atlas",
    "lemma:prime-axis-root-closure",
    "theorem:radix-residue-phase-decomposition",
    "theorem:euler-successor-geometry",
    "theorem:euler-metric-recurrence",
    "lemma:normalized-euler-resolvent-return",
    "theorem:prime-power-aperture-incidence",
  ),
  claim: [
    Let $S$ be a finite set of rational primes, put
    $
      P_S=product_(q in S)q,
      quad
      cal(C)_S={n in NN^+:gcd(n,P_S)=1},
    $
    and let $p ∉ S$.  With $S'=S union {p}$, unique factorization gives
    the disjoint valuation stratification
    $
      cal(C)_S
      =
      {p^k m:k>=0, m in cal(C)_(S')},
      quad "uniquely".
      quad "(VALUATION STRATA)"
    $
    Its first difference is
    $
      cal(C)_(S')=cal(C)_S without p cal(C)_S.
      quad "(CUT)"
    $

    On the finite wheel
    $
      cal(U)_S=(ZZ/P_S ZZ)^times,
    $
    each residue $r in cal(U)_S$ has the $p$ lifts
    $
      r+j P_S mod p P_S,
      quad 0<=j<p.
    $
    Exactly one lift is divisible by $p$.  Removing that lift leaves
    $p-1$ successors over every old residue, so
    $
      abs(cal(U)_(S'))=(p-1)abs(cal(U)_S).
      quad "(COPY--CUT)"
    $
    Reading the surviving residues in cyclic order joins the two gaps
    incident to every removed lift.  The primorial
    COPY/CUT/JOIN wheel is therefore the finite quotient of ("CUT"), not a
    separate prime-generating law.

    If $mu$ denotes the arithmetic Möbius function, the complete finite cut
    is the inclusion--exclusion identity
    $
      bold(1)_(cal(C)_S)(n)
      =
      sum_(d divides P_S) mu(d) bold(1)_(d divides n).
      quad "(MOBIUS CUT)"
    $
    For $op("Re")(s)>1$, its Dirichlet/Mellin character is
    $
      D_S(s)
      =
      sum_(n in cal(C)_S)n^(-s)
      =
      zeta(s) product_(q in S)(1-q^(-s)),
    $
    and one prime admission obeys
    $
      D_(S')(s)=(1-p^(-s))D_S(s),
      quad
      D_S(s)=(1-p^(-s))^(-1)D_(S')(s).
      quad "(EULER ADMISSION--RETURN)"
    $

    Let $U_t$ be logarithmic translation on $L^2(RR,dif u)$ and define
    $
      J_q=I-q^(-1/2)U_(log q),
      quad
      J_S=product_(q in S)J_q.
    $
    Since the translations commute, ("MOBIUS CUT") lifts exactly to
    $
      J_S
      =
      sum_(d divides P_S)
      mu(d)d^(-1/2)U_(log d).
      quad "(OPERATOR CUT)"
    $
    Its inverse converges in operator norm and returns every valuation
    stratum:
    $
      J_S^(-1)
      =
      sum_(m in cal(M)_S)m^(-1/2)U_(log m),
      quad
      cal(M)_S
      =
      {m in NN^+: "every prime divisor of "m" lies in "S}.
      quad "(VALUATION RETURN)"
    $

    The same strata have an exact projective face.  For
    $x_0,x_1,x_2 in cal(C)_(S')$ and every $k>=0$,
    $
      frac(
        p^k x_2-p^k x_1,
        p^k x_1-p^k x_0
      )
      =
      frac(x_2-x_1,x_1-x_0)
      quad "(when the denominators are nonzero),"
    $
    and dilation by $p^k$ likewise preserves every ordered cross-ratio.
    In the logarithmic chart this common dilation is the translation
    $
      log x arrow.r log x+k log p.
      quad "(SIMILARITY--TRANSLATION)"
    $

    Finally, for $0<a<1$ put
    $
      J_p(a)=I-a U_(log p),
      quad
      cal(K)_p(a)
      =
      (J_p(a)^*)^(-1)J_p(a)^(-1),
      quad
      cal(R)_p(a)=sqrt(1-a^2)J_p(a)^(-1).
    $
    Functional calculus gives the norm-convergent identity
    $
      a partial_a log cal(K)_p(a)
      =
      cal(R)_p(a)^*cal(R)_p(a)-I
      =
      sum_(k>=1)a^k
      (U_(k log p)+U_(-k log p)).
      quad "(RETURN DERIVATIVE)"
    $
    At $a=p^(-1/2)$, for a returned current represented by $x$,
    $
      W_p
      =
      (log p)
      chevron.l
        x,
        a partial_a log cal(K)_p(a)x
      chevron.r.
      quad "(PRIME RESPONSE)"
    $
    Thus the symmetric prime-power response is the logarithmic degree
    derivative of the metric of the exact valuation return.
  ],
  proof: [
    Every $n in cal(C)_S$ has one $p$-adic valuation $k=v_p(n)$, and
    $m=n/p^k$ belongs to $cal(C)_(S')$.  This proves ("VALUATION STRATA")
    and ("CUT").

    Because $p$ does not divide $P_S$, multiplication by $P_S$ permutes the
    residue classes modulo $p$.  Hence exactly one of the $p$ displayed
    lifts is zero modulo $p$.  The cardinality and cyclic gap statements
    follow.  Arithmetic Möbius inversion gives
    $
      sum_(d divides gcd(n,P_S))mu(d)
      =
      cases(1 & gcd(n,P_S)=1, 0 & "otherwise"),
    $
    which is ("MOBIUS CUT").

    Absolute convergence for $op("Re")(s)>1$ permits the Euler-factor
    calculation of $D_S$.  Splitting ("VALUATION STRATA") into its
    $p$-adic layers gives the reciprocal relation in
    ("EULER ADMISSION--RETURN").

    Expanding the finite commuting product $J_S$ gives ("OPERATOR CUT"):
    squarefree subsets of $S$ are precisely divisors of $P_S$, and their
    signs are $mu(d)$.  Expanding each inverse as a Neumann series gives
    ("VALUATION RETURN").  Its operator norm convergence follows from
    $
      sum_(m in cal(M)_S)m^(-1/2)
      =
      product_(q in S)(1-q^(-1/2))^(-1)<infinity.
    $

    Common dilation cancels from the displayed ratio and from all four
    factors of an ordered cross-ratio.  Taking logarithms turns that
    dilation into translation, proving ("SIMILARITY--TRANSLATION").

    Since $J_p(a)$ is an invertible normal function of one unitary,
    $
      log cal(K)_p(a)
      =
      sum_(k>=1)frac(a^k,k)
      (U_(k log p)+U_(-k log p))
    $
    in operator norm on compact subintervals of $0<a<1$.  Applying
    $a partial_a$ gives the series in ("RETURN DERIVATIVE").  The
    normalized Euler-resolvent identity identifies the same series with
    $cal(R)_p(a)^*cal(R)_p(a)-I$.  The established prime-power
    aperture-incidence formula then gives ("PRIME RESPONSE").
  ],
  boundary: [
    This theorem identifies the exact arithmetic preimage of the
    semilocal Euler successor.  Candidate succession, growth of the admitted
    place set $S$, and growth of the analytic support aperture are three
    distinct orderings; the theorem does not collapse them into one stage.
    Dilation similarity explains a lawful source of recurring ratio and
    cross-ratio faces, but those faces also occur among composites and are
    not primality tests.  Positivity of the return metric does not determine
    the sign of its degree derivative.  The theorem therefore does not sign
    the completed Weil form or prove RH; that obligation begins only after
    arithmetic admission, archimedean completion, moment conditioning, and
    support shorting meet in one receiver.
  ],
)
