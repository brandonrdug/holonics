#let prime-simplex-census = (
  key: "theorem:prime-simplex-census",
  kind: [Theorem],
  title: [Exact census of a finite prime simplex],
  status: [Classical stars-and-bars identity; exact atlas census],
  depends: ("definition:prime-valuation-atlas",),
  claim: [
    If $abs(S)=r$, then the degree-$d$ valuation fiber has
    $
      abs(Delta_(S,d))=binom(d+r-1,r-1)
    $
    members.  The members using exactly $k$ prime axes number
    $
      binom(r,k)binom(d-1,k-1)
    $
    for $1<=k<=min(r,d)$.  The members containing a fixed axis $p$ number
    $
      binom(d+r-2,r-1),
    $
    and those with exact exponent $v_p=m$ number
    $
      binom(d-m+r-2,r-2)
    $
    whenever $0<=m<=d$ and $r>=2$.
  ],
  proof: [
    The first count is the number of weak compositions of $d$ into $r$
    coordinates.  For support exactly $k$, choose its axes and then count the
    positive compositions of $d$ into $k$ parts.  Requiring a fixed axis
    subtracts one from that coordinate before applying weak compositions.
    Fixing its exponent leaves a weak composition of $d-m$ over the remaining
    $r-1$ axes.
  ],
  boundary: [
    These counts grade multiplicative formulations by valuation degree.  They
    do not count all integer-producing algorithms, all analytic formulations
    of a constant, or all receiver-equivalent paths.  Such paths require
    additional vertical transition data.
  ],
)
