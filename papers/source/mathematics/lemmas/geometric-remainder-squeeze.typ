#let geometric-remainder-squeeze = (
  key: "lemma:geometric-remainder-squeeze",
  kind: [Lemma],
  title: [A geometric remainder is squeezed while its logarithmic path remains unbounded],
  status: [Classical geometric-series and squeeze theorem; exact log-polar refinement],
  depends: ("lemma:situated-mean-transport",),
  claim: [
    Let
    $
      w=alpha+i beta,
      quad alpha>0,
      quad z=e^(-w).
    $
    For
    $
      G_N=sum_(k=0)^N z^k
      quad "and" quad
      G=1/(1-z),
    $
    the exact remainder is
    $
      R_N=G-G_N=z^(N+1)/(1-z).
    $
    It obeys the two-sided squeeze
    $
      frac(abs(z)^(N+1),1+abs(z))
      <=
      abs(R_N)
      <=
      frac(abs(z)^(N+1),1-abs(z)),
    $
    and hence $R_N arrow.r 0$.

    At the same time,
    $
      -log abs(R_N)
      =(N+1)alpha+log abs(1-e^(-w)),
    $
    while any continuous phase lift satisfies
    $
      op("Arg")(R_N)
      =-(N+1)beta-op("Arg")(1-e^(-w)).
    $
    Thus Euclidean convergence to one boundary point is uniform linear
    translation and winding in the logarithmic residual chart.

    The dyadic occurrence is the exact specialization
    $
      sum_(n=1)^N 2^(-n)=1-2^(-N),
      quad
      R_N=2^(-N),
      quad
      -log R_N=N log 2.
    $
  ],
  proof: [
    The finite geometric identity gives
    $
      G_N=(1-z^(N+1))/(1-z)
    $
    and therefore the displayed remainder. The triangle and reverse
    triangle inequalities give
    $
      1-abs(z)<=abs(1-z)<=1+abs(z).
    $
    Since $abs(z)=e^(-alpha)<1$, division yields the two bounds, both of
    which tend to zero. Taking magnitude and phase of the exact remainder
    gives the logarithmic formulas. The dyadic row follows by substituting
    $z=1/2$ and omitting the $k=0$ term.
  ],
  boundary: [
    The squeeze requires $alpha>0$. At $alpha=0$ the upper denominator can
    lose its positive lower bound and the series terms no longer decay.
    Analytic continuation or an Abel boundary value is another
    transformation law, not the same convergent lineage. The scalar MVT may
    represent a real projection of one finite increment, but it neither
    causes convergence nor supplies one common witness for the complex
    path.
  ],
)
