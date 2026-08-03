#let prime-cut-incidence-calculus = (
  key: "theorem:prime-cut-incidence-calculus",
  kind: [Theorem],
  title: [Prime admission has an exact cut, Hessian, and valuation-layer decomposition],
  status: [Exact consequence of unique factorization and finite inclusion--exclusion],
  depends: (
    "definition:graded-arithmetic-accessibility-current",
    "theorem:prime-wheel-euler-transport",
    "theorem:receiver-relative-second-order-calculus",
  ),
  claim: [
    Let
    $
      cal(C)_S
      =
      {n in cal(N):gcd(n,product_(q in S) q)=1}
    $
    be a finite situated candidate chain inside a declared aperture
    $cal(N)$.  For $p ∉ S$, let $K_p$ restrict this chain to
    $cal(C)_(S union {p})$.  In the common enlarged valuation ring, define
    $
      Delta_p frak(A)_S
      =
      K_p frak(A)_S-frak(A)_S.
    $
    Then
    $
      Delta_p frak(A)_S
      =
      -
      sum_(n in cal(C)_S, p divides n)
      [n] bold(X)^(nu(n)).
      quad "(FIRST CUT)"
    $
    No removed occurrence is anonymous: its complete valuation monomial
    remains the coefficient address of the wall crossing.

    For distinct $p,q ∉ S$, static sieve restrictions commute and
    $
      Delta_q Delta_p frak(A)_S
      =
      Delta_p Delta_q frak(A)_S
      =
      sum_(n in cal(C)_S, p q divides n)
      [n] bold(X)^(nu(n)).
      quad "(CUT HESSIAN)"
    $
    Hence the cut commutator vanishes while the joint second difference may
    be nonzero.  The degree-two projection of ("CUT HESSIAN") isolates the
    mixed semiprime face $X_p X_q$.

    Prime squares are not obtained by pretending to admit $p$ twice.  They
    belong to the pairwise-disjoint valuation layers
    $
      cal(C)_(S,k)
      =
      {n in cal(C)_S:v_p(n)=k},
      quad
      cal(C)_S=union_(k>=0) cal(C)_(S,k),
    $
    whose degree-two $k=2$ coefficient is $X_p^2$.  Thus the exact
    second-order arithmetic geometry consists of both cross-axis incidence
    $X_p X_q$ and repeated traversal $X_p^2$.
  ],
  proof: [
    The first identity is the chain difference between a population and its
    restriction away from multiples of $p$.  Applying the $q$ difference
    restores with positive sign precisely the terms removed by both cuts.
    Divisibility by distinct primes is order-independent, proving the
    equality of the two mixed differences and the vanishing commutator.
    Unique factorization grades the shared population by valuation degree;
    degree two has exactly the partitions $2e_p$ and $e_p+e_q$.
  ],
  boundary: [
    Commutation holds for static exact divisibility cuts in one fixed
    aperture.  A receiver-dependent aperture, transported coefficient law,
    or changing arithmetic domain may have nonzero mixed curvature as defined
    above.  The first and second differences are chain identities; replacing
    them by cardinalities discards location, order, and valuation species.
  ],
)
