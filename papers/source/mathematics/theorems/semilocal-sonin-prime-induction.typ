#let semilocal-sonin-prime-induction = (
  key: "theorem:semilocal-sonin-prime-induction",
  kind: [Theorem],
  title: [Prime admission is an exact dual Sonin induction],
  status: [
    Published Sonin-space stability plus an exact laboratory dual-transport
    and dyadic kernel obstruction
  ],
  depends: (
    "theorem:euler-successor-geometry",
    "theorem:dyadic-poisson-half-filler",
  ),
  claim: [
    Let $S$ be a finite set of places containing $infinity$, let
    $p ∉ S$, and put $S'=S union {p}$,
    $a_p=p^(-1/2)$, and $ell_p=log p$.  Use the logarithmic translation
    convention
    $
      (U_p h)(u)=h(u-ell_p).
    $
    The published semilocal Sonin maps identify, for every $lambda>0$,
    $
      theta_S:
      op("Son")_(infinity,lambda)
      arrow.r
      op("Son")_(S,lambda)
      quad "isomorphically".
    $
    In the common real logarithmic chart, adjoining $p$ acts by
    $
      Delta_p=I-a_p U_p,
      quad
      theta_(S')theta_S^(-1)=Delta_p.
      quad "(ADMISSION)"
    $
    With the opposite translation convention, $U_p$ is replaced by
    $U_p^*$ and none of the following identities changes.

    The dual semilocal population return is
    $
      cal(E)_p=(Delta_p^*)^(-1)
      =
      sum_(m>=0)a_p^m(U_p^*)^m,
      quad
      Delta_p^*cal(E)_p=I.
      quad "(DUAL RETURN)"
    $
    Hence
    $
      chevron.l Delta_p f,cal(E)_p g chevron.r
      =
      chevron.l f,g chevron.r.
      quad "(PAIRING)"
    $
    The difference arm and the prime-power sum are therefore dual faces of
    one admission event; neither is an independently signed contribution.

    The maps in ("ADMISSION") are independent of $lambda$.  Consequently,
    for $mu>=lambda$, the nested-aperture square is the identity
    $
      theta_(S,lambda) iota_(infinity,mu,lambda)
      =
      iota_(S,mu,lambda) theta_(S,mu),
    $
    commutes.  Distinct prime additions commute as well:
    $
      Delta_p Delta_q=Delta_q Delta_p.
      quad "(INDUCTION COHERENCE)"
    $

    On the four-cell dyadic section, let $R$ be the core--shell involution
    and $P_+=(I+R)/2$.  The admission metric is
    $
      G_2=Delta_2^*Delta_2
      =(1+a^2)I-a R,
      quad a=2^(-1/2).
    $
    Therefore the local Poisson filler is the lower-metric spectral face
    $
      A_("Pois",2)^*A_("Pois",2)
      =
      frac(log 2,2)
      ((1+a+a^2)I-G_2)
      =
      frac(log 2,sqrt(2))P_+.
      quad "(SPECTRAL FACE)"
    $
    It is not a restriction of either $Delta_2$ or $cal(E)_2$: both are
    invertible, whereas
    $
      op("ker")(A_("Pois",2))=P_-cal(V)_4
    $
    has dimension two.
  ],
  proof: [
    Proposition 4.6 and Theorem 4.6 of the cited semilocal construction give
    $
      w_(S')theta_(S')f
      =
      g(lambda)-p^(-1/2)g(lambda/p)
    $
    and identify every real Sonin space with its semilocal counterpart.
    Passing to $u=log lambda$ gives ("ADMISSION").  Since
    $norm(a_p U_p)<1$, the Neumann series in ("DUAL RETURN") converges in
    operator norm.  The pairing identity follows immediately.  It is the
    relative form of the published equality
    $
      chevron.l theta_S f,eta_S g chevron.r
      =
      chevron.l f,g chevron.r.
    $

    The same $theta_S$ serves every aperture, so restriction to nested Sonin
    subspaces commutes.  Translations by $log p$ and $log q$ commute, proving
    ("INDUCTION COHERENCE").

    On the dyadic character cell, $R$ has eigenvalue $+1$ on $P_+$ and
    $-1$ on $P_-$.  Thus
    $
      (1+a+a^2)I-G_2=a(I+R)=2a P_+.
    $
    Multiplication by $(log 2)/2$ proves ("SPECTRAL FACE").  Finally,
    $a<1$ makes $Delta_2$ and its adjoint inverse injective, while the
    periodization theorem gives the displayed nonzero kernel.  An injective
    map cannot restrict to that quotient.
  ],
  boundary: [
    The place and support *spaces* already form a coherent inductive system.
    The dyadic periodization is a quadratic defect face of its admission
    metric, not the successor map itself.  These identities do not sign the
    completed Weil form.  What remains is a form-level support successor
    which couples the old positive body, the newly admitted support shell,
    and—at a prime step—the dual admission/return pair.
  ],
)
