#let euler-factor-formulation-cell = (
  key: "theorem:euler-factor-formulation-cell",
  kind: [Theorem],
  title: [One prime gives an exact Euler formulation cell],
  status: [Exact classical analytic identity, organized as a formulation cell],
  depends: (
    "definition:formulation-span-atlas",
    "lemma:formulation-span-composition",
  ),
  claim: [
    Fix a prime $p$ and let
    $
      H_p={s in CC: "Re"(s)>0},
      quad q=p^(-s).
    $
    On $H_p$ the rational, geometric-series, and recurrence formulations
    $
      F_(p,"rat")(s)={1}/{1-p^(-s)},
      quad
      F_(p,"ser")(s)=sum_(m>=0)p^(-m s),
    $
    $
      a_0=1,
      quad a_(m+1)=p^(-s)a_m,
      quad F_(p,"ser")=sum_(m>=0)a_m
    $
    have the same analytic-value receiver. They therefore form an exact
    receiver cell. This equality alone does not decide whether a chosen
    formulation correspondence is a rechart: if $p$, $s$, and the recurrence
    law are retained, the rational factor regenerates the geometric lineage;
    the bare summation receiver on the ambient space of absolutely summable
    sequences is noninjective. The logarithmic derivative retains the
    prime-power lineage:
    $
      -{dif}/{dif s}log F_(p,"rat")(s)
      =
      log(p) sum_(m>=1)p^(-m s).
    $
  ],
  proof: [
    On $H_p$, $abs(p^(-s))=p^(-"Re"(s))<1$, so the geometric series converges
    absolutely to $(1-p^(-s))^(-1)$ and its terms obey the displayed
    recurrence. Differentiating
    $-log(1-p^(-s))$ inside this half-plane gives the prime-power series.
    On the ambient sequence space, distinct absolutely summable sequences can
    have the same sum, so summation alone has no inverse. On this constrained
    geometric subfamily, however, the retained generator
    $q=p^(-s)$ reconstructs every $a_m=q^m$. Thus any inverse belongs to the
    supplied parameter-and-law decoration, not to equality of sums.
  ],
  boundary: [
    The geometric-series convergence boundary is $"Re"(s)=0$. The rational
    factor has poles only where $p^(-s)=1$, namely
    $s=2 pi i k/log(p)$ with $k in ZZ$; these are distinct discriminant
    species. The global Euler product for $zeta(s)$ requires
    $"Re"(s)>1$. This one-prime cell neither classifies every admissible
    operational rechart, continues the full product, nor implies any statement
    about nontrivial zeta zeros.
  ],
)
