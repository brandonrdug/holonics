#let prime-interval-wall-current = (
  key: "theorem:prime-interval-wall-current",
  kind: [Theorem],
  title: [The interval from 113 to 127 has a six-occurrence arithmetic wall current],
  status: [Exact finite consequence; re-expression of the measured prime-spectral cell],
  depends: (
    "theorem:prime-cut-incidence-calculus",
    "theorem:prime-wheel-euler-transport",
  ),
  claim: [
    In the closed integer aperture $[113,127]$, begin with the
    $2$-coprime population and admit the successive sieve axes
    $3,5,7,11$.  The four exact first-cut currents are
    $
      Delta_3 frak(A)
      =
      -(X_3^2 X_13+X_3 X_41),
    $
    $
      Delta_5 frak(A)
      =
      -(X_5 X_23+X_5^3),
    $
    $
      Delta_7 frak(A)=-X_7 X_17,
      quad
      Delta_11 frak(A)=-X_11^2.
      quad "(INTERVAL WALL CURRENT)"
    $
    They correspond respectively to
    $
      117=3^2 dot 13,
      quad
      123=3 dot 41,
      quad
      115=5 dot 23,
      quad
      125=5^3,
      quad
      119=7 dot 17,
      quad
      121=11^2.
    $
    The endpoint survivors are $113$ and $127$.

    Consequently, the final scalar gap $14$ is the augmentation of a wall
    current containing three mixed degree-two crossings, one prime-square
    degree-two crossing, and two degree-three crossings.  The successive
    surviving place sets
    $
      {2},
      {2,3},
      {2,3,5},
      {2,3,5,7},
      {2,3,5,7,11}
    $
    determine the exact refinement lineage.
  ],
  proof: [
    The odd population is
    $
      113,115,117,119,121,123,125,127.
    $
    Cutting by $3$ removes $117,123$; cutting the survivors by $5$ removes
    $115,125$; the $7$ cut removes $119$; and the $11$ cut removes $121$.
    The displayed factorizations are exact and unique.  Projection by total
    valuation degree gives the stated four degree-two and two degree-three
    crossings.  Only $113$ and $127$ remain, so augmenting their ordered
    endpoint difference gives $14$ while forgetting the six interior wall
    events.
  ],
  boundary: [
    This theorem grades one finite situated interval.  It neither predicts
    the next prime nor identifies one universal metric between primes.
    Its purpose is to expose the topology hidden by the endpoint quotient:
    arithmetic accessibility changes through typed valuation walls.
  ],
)
