#let euler-metric-recurrence = (
  key: "theorem:euler-metric-recurrence",
  kind: [Theorem],
  title: [Prime-power recurrence is the normal derivative of the Euler metric],
  status: [Exact laboratory derivation; external novelty not asserted],
  depends: ("theorem:euler-successor-geometry",),
  claim: [
    For $sigma>0$, put
    $
      D_(p,sigma)(t)=1-p^(-sigma-i t)
    $
    and let $g_(p,sigma)(t)=abs(D_(p,sigma)(t))^2$. Then
    $
      partial_sigma log g_(p,sigma)(t)
      =
      2 log p sum_(m>=1) p^(-m sigma)
        cos(m t log p).
    $
    At $sigma=1/2$ this is the Fourier transform, under
    $hat(nu)(t)=integral e^(-i t u) dif nu(u)$, of the symmetric
    prime-power measure
    $
      nu_p
      =log p sum_(m>=1) p^(-m/2)
        (delta_(m log p)+delta_(-m log p)).
    $
  ],
  proof: [
    Write $z=p^(-sigma-i t)$. Since $abs(z)<1$,
    $
      partial_sigma log abs(1-z)^2
      =2 op("Re")((log p) z/(1-z)).
    $
    Expanding $z/(1-z)=sum_(m>=1)z^m$ gives the cosine series.
    The second statement follows by Fourier transforming the two atoms at
    $plus.minus m log p$ term by term.
  ],
  boundary: [
    This identifies the complete repeated-prime current inside one exact
    receiver deformation. It does not compare that local deformation with
    the archimedean term, endpoint terms, or the completed Weil sign.
  ],
)
