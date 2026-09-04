#let three-frame-return-covariance = (
  key: "theorem:three-frame-return-covariance",
  kind: [Theorem],
  title: [The triangular counting return is covariant under independent recharting],
  status: [Exact relational transport theorem],
  depends: ("definition:three-frame-counting-correspondence",),
  claim: [
    Fix an incidence $e$ of a three-frame counting correspondence.  Let
    $
      g_i:cal(H)_(i,e) arrow.r cal(H)'_(i,e)
    $
    be independent invertible recharts, taken to be bounded isomorphisms
    whenever the fibers are infinite-dimensional normed spaces.  For
    $(i,j) in {(1,2),(2,3),(3,1)}$, carry each domain by
    $D'_((i,j),e)=g_i(D_((i,j),e))$, and define
    $
      T'_((i,j),e)=g_j T_((i,j),e) g_i^(-1).
      quad "(RECHART)"
    $
    Then
    $
      D'_(123,e)=g_1(D_(123,e))
    $
    and the returned operators obey
    $
      M'_(123,e)
      =
      g_1 M_(123,e) g_1^(-1).
      quad "(COVARIANT RETURN)"
    $
    Whenever the returned defect is defined,
    $
      Omega'_(123,e)
      =
      g_1 Omega_(123,e) g_1^(-1).
    $

    Consequently, when the returns are bounded endomorphisms and the recharts
    are bounded isomorphisms, their spectra and fixed subspaces agree up to
    the rechart.  In finite dimension their
    characteristic polynomials, traces, and determinants agree exactly.

    Let $W_1$ and $W'_1$ be Hermitian responses related by
    $
      W'_1(g_1 v,g_1 w)=W_1(v,w).
      quad "(RESPONSE RECHART)"
    $
    For every admissible anchored current $v$,
    $
      W'_1(M' g_1 v,M' g_1 v)-W'_1(g_1 v,g_1 v)
      =
      W_1(M v,M v)-W_1(v,v).
      quad "(RETURNED RESPONSE)"
    $
    Thus both the conjugacy class of the closed return and the congruently
    transported Hermitian response are independent of the three chosen
    coordinate charts.
  ],
  proof: [
    Substituting ("RECHART") into the three-edge composite cancels the two
    interior rechart pairs:
    $
      T'_(31)T'_(23)T'_(12)
      =
      g_1T_(31)g_3^(-1)
      g_3T_(23)g_2^(-1)
      g_2T_(12)g_1^(-1)
      =
      g_1M_(123)g_1^(-1).
    $
    The domain identity follows by applying the same substitutions to the
    three composability conditions.  Similar operators have the same
    spectrum; in finite dimension they have the same characteristic
    polynomial, trace, and determinant.  Also
    $
      ker(M'-I)=g_1 ker(M-I).
    $
    Finally substitute $M' g_1=g_1 M$ into
    ("RESPONSE RECHART") twice to obtain ("RETURNED RESPONSE").
  ],
  boundary: [
    Covariance does not mean that an event leaves the system unchanged.
    Replacing the incidence, current, aperture, transport law, or Hermitian
    response is a new situated comparison, not a rechart of the old one.
    Such a change may alter a scalar response or its sign.

    Conversely, a genuine negative Hermitian direction cannot be made
    positive by independently rotating the three charts.  The sign belongs
    to the anchored current and response at the declared incidence; it is
    neither an observer-free label on one object nor disposable coordinate
    noise.

    Edge matrices and plotted coordinates are not conjugacy invariants.
    The closed return also forgets some edge-wise lineage, so equal holonomy
    does not identify complete three-frame constructions.  Noninvertible
    cross-frame maps require the wider span/correspondence calculus and do
    not acquire a spectrum merely by notation.
  ],
)
