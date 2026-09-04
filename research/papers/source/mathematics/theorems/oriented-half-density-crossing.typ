#let oriented-half-density-crossing = (
  key: "theorem:oriented-half-density-crossing",
  kind: [Theorem],
  title: [The positive half-density factor is an oriented boundary carrier],
  status: [Classical differential and convolution identities; exact laboratory synthesis],
  depends: (
    "definition:covariant-coarea-carrier",
    "lemma:mellin-half-density-chart",
    "theorem:covariant-coarea-fundamental-theorem",
  ),
  claim: [
    Work first in the logarithmic coordinate $u=log rho$ and put
    $
      D=partial_u,
      quad
      cal(L)_+=D+1/2,
      quad
      cal(L)_-=-D+1/2.
      quad "(ORIENTED FACTORS)"
    $
    The laboratory symbol $cal(L)_+$ names this positively oriented
    half-density factor. It is not the $L_+$ member of a knot skein triple.
    On compactly supported smooth currents,
    $
      Q=-D^2+1/4
      =
      cal(L)_- cal(L)_+
      =
      cal(L)_+^* cal(L)_+
      >=0.
      quad "(POSITIVE INTERIOR)"
    $
    On a finite interval $[a,b]$, before the endpoint values are suppressed,
    one instead has the exact boundary balance
    $
      norm(cal(L)_+ h)^2
      =
      norm(D h)^2+1/4 norm(h)^2
      +
      1/2(
        abs(h(b))^2-abs(h(a))^2
      ).
      quad "(POSITIVE CROSSING)"
    $
    Reversing the orientation replaces $cal(L)_+$ by $cal(L)_-$ and
    reverses only the signed endpoint term.

    Let additive convolution have involution
    $g^*(u)=overline(g(-u))$. Then
    $
      Q (g ast g^*)
      =
      (cal(L)_+ g) ast (cal(L)_+ g)^*.
      quad "(COMMUTING POSITIVE SQUARE)"
    $
    Thus the same first-order crossing which creates the signed boundary
    flux creates a positive Gram interior after the crossing is closed with
    its adjoint.

    If $g$ is supported in $[-A/2,A/2]$, then both sides of
    ("COMMUTING POSITIVE SQUARE") are supported in $[-A,A]$. Under
    $rho=e^u$, this is the exact multiplicative support passage
    $
      [e^(-A/2),e^(A/2)]
      ast
      [e^(-A/2),e^(A/2)]
      arrow.r
      [e^(-A),e^A].
      quad "(HALF SUPPORT)"
    $
    At $A=log 2$, its root and closed supports are respectively
    $
      [2^(-1/2),2^(1/2)]
      quad "and" quad
      [1/2,2].
    $
  ],
  proof: [
    With compact support, $D^*=-D$, so
    $
      cal(L)_+^*
      =
      -D+1/2
      =
      cal(L)_-.
    $
    Multiplying the two factors cancels their mixed first-order terms and
    proves ("POSITIVE INTERIOR").

    Expanding the norm on $[a,b]$ gives
    $
      integral_a^b abs(D h+h/2)^2 dif u
      =
      integral_a^b (
        abs(D h)^2+abs(h)^2/4
      ) dif u
      +
      integral_a^b op("Re")(D h overline(h)) dif u.
    $
    The last integral is
    $(abs(h(b))^2-abs(h(a))^2)/2$, proving
    ("POSITIVE CROSSING"). The reverse factor changes the sign of this
    cross term.

    Fourier transformation sends $D$ to multiplication by $i t$. Hence
    $
      hat(Q(g ast g^*))(t)
      =
      (t^2+1/4)abs(hat(g)(t))^2
      =
      abs((i t+1/2)hat(g)(t))^2,
    $
    which is the transform of
    $(cal(L)_+ g) ast (cal(L)_+ g)^*$. Convolution adds supports, while
    a differential operator does not enlarge them, proving ("HALF SUPPORT").
  ],
  boundary: [
    The $1/2$ here is not a dimensionless assertion that every geometric
    surface has raw area $1/2$. It is the coefficient which splits a full
    Jacobian or endpoint flux between an amplitude and its adjoint, and it
    is the exponent which halves logarithmic support before a positive
    convolution closure. A geometric half-area statement requires a
    normalized measure and an actual crossing surface.

    The factorization constructs the support-preserving positive operator
    used by the archimedean vanishing ideal. It does not by itself identify
    that positive square with the complete Weil response after finite-prime
    admission.
  ],
)
