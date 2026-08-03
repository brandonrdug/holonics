#let prime-power-aperture-incidence = (
  key: "theorem:prime-power-aperture-incidence",
  kind: [Theorem],
  title: [Finite-prime currents are translated aperture intersections],
  status: [Exact logarithmic form of the finite-place explicit response],
  depends: (
    "lemma:mellin-half-density-chart",
    "theorem:euler-metric-recurrence",
  ),
  claim: [
    Let $R>1$, put $L=log R$ and
    $
      I_R=[-L/2,L/2].
    $
    Let $a in L^2(RR)$ be supported in $I_R$ and define
    $
      g(x)=x^(-1/2)a(log x),
      quad
      h(x)=integral_0^infinity
      g(x y) overline(g(y)) dif y.
    $
    For logarithmic translation
    $
      (U_t a)(v)=a(v+t),
    $
    one has
    $
      h(e^t)
      =
      e^(-t/2) chevron.l a,U_t a chevron.r.
    $
    Consequently the finite-place response is
    $
      W_p(h)
      =
      2log p sum_(m>=1)
      p^(-m/2)
      Re chevron.l a,U_(m log p) a chevron.r.
    $

    If $P_R$ denotes multiplication by $1_(I_R)$, then
    $
      chevron.l a,U_t a chevron.r
      =
      chevron.l a,P_R U_t P_R a chevron.r
    $
    and
    $
      P_R U_t P_R=0
      quad "whenever" quad
      abs(t)>=L.
    $
    Thus the $m$-th prime-power current meets the aperture exactly when
    $p^m<R$; equality is a measure-zero boundary contact.  For the box
    current $a=1_(I_R)$,
    $
      W_p(h)
      =
      2sum_(p^m<R)
      (log p)p^(-m/2)(log R-m log p).
    $
  ],
  proof: [
    Substitute $y=e^v$ and the half-density expression for $g$ into the
    definition of $h$.  The factors from the two copies of $g$ and the
    measure $dif y=e^v dif v$ leave the single factor $e^(-t/2)$ and the
    translated inner product.  Applying the same identity at $-t$ turns
    the two explicit-formula arms into twice the real part.

    The kernel of $P_R U_t P_R$ is supported on the intersection
    $I_R inter (I_R-t)$.  Its length is
    $max(0,L-abs(t))$, which proves the incidence criterion.  For the box
    current, the translated inner product is exactly that overlap length.
  ],
  boundary: [
    The theorem identifies when and where finite-prime recurrence contacts a
    bounded current.  It does not sign the resulting correlation and does
    not combine it with the archimedean or Sonin-aperture connection terms.
    In particular it supplies the finite-place current in the defect
    recurrence, not the positive semilocal remainder carrier.
  ],
)
