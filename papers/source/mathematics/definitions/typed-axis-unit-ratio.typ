#let typed-axis-unit-ratio = (
  key: "definition:typed-axis-unit-ratio",
  kind: [Definition],
  title: [Typed axes, local units, and covariant ratios],
  status: [Project definition using standard line-bundle and projective geometry],
  depends: (
    "definition:situated-occurrence",
    "definition:receiver",
  ),
  claim: [
    Let $cal(D)$ be a collection of quantity types.  A *typed axis* of type
    $d in cal(D)$ over a base $B$ is an oriented real line bundle
    $A_d arrow.r B$.  A *unit* on a region $U subset B$ is a nowhere-zero
    local section $u_d in Gamma(U,A_d)$.  A quantity $q in (A_d)_x$ has the
    coordinate $x_u(q)$ determined by
    $
      q=x_u(q) u_d(x).
    $
    If $u'_d=a u_d$ with $a:U arrow.r RR^times$, then
    $
      x_(u')(q)=a^(-1)x_u(q).
    $
    The quantity and its type remain; only its coordinate face changes.

    Let $Phi:A_d arrow.r A_e$ be a typed linear comparison over the same
    base, and choose units $u_d,u_e$.  Its scalar ratio face $r_(u_e<-u_d)$
    is defined by
    $
      Phi(u_d)=r_(u_e<-u_d)u_e.
    $
    Under $u'_d=a u_d$ and $u'_e=b u_e$,
    $
      r_(u'_e<-u'_d)=(a/b)r_(u_e<-u_d).
    $
    Thus the map $Phi$ is primary and the displayed scalar is its
    receiver-dependent coordinate.

    Independently, a bare rational number is the equivalence class
    $
      m/n=[m:n] in PP^1(QQ), quad n !=0,
    $
    under $(m,n) tilde (lambda m,lambda n)$ for nonzero
    $lambda in QQ$.  It requires two entries but not two physical quantity
    axes.  It becomes a rate, scale conversion, or measured ratio only after
    a typed comparison supplies that interpretation.
  ],
  proof: none,
  boundary: [
    Type, axis, unit, coordinate, and scalar ratio are different data.  A
    unit is not merely a label: it is a selected nonzero frame in a typed
    one-dimensional fiber.  A conversion between unlike types requires an
    actual constitutive map; dimensional labels alone do not create one.
    The glyph $1/2$ may denote a projective ratio, an affine midpoint, a
    group average, a half-density exponent, or a fixed seam.  Those faces
    coincide only through declared maps.
  ],
)
