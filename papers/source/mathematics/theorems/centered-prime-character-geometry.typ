#let centered-prime-character-geometry = (
  key: "theorem:centered-prime-character-geometry",
  kind: [Theorem],
  title: [A centered prime character has circular phase, hyperbolic normal sheets, and flat local transport],
  status: [Exact laboratory derivation from the exponential character and Euler successor],
  depends: (
    "lemma:critical-seam-conjugacy",
    "lemma:geometric-remainder-squeeze",
    "theorem:euler-successor-geometry",
  ),
  claim: [
    Let $p$ be prime, $L=log p$, and
    $
      s=1/2+epsilon+i t,
      quad
      J(s)=1-overline(s)=1/2-epsilon+i t.
    $
    Put $x=epsilon L$, $theta=t L$, and define the normalized functional
    partners
    $
      A_+=p^(1/2-s)=e^(-x-i theta),
      quad
      A_-=p^(1/2-J(s))=e^(x-i theta).
    $
    Their common and oriented-normal faces are
    $
      C=(A_++A_-)/2=e^(-i theta)cosh x,
    $
    $
      N=(A_--A_+)/2=e^(-i theta)sinh x.
    $
    Consequently
    $
      C^2-N^2=e^(-2i theta),
      quad
      N=0 " iff " epsilon=0.
    $

    Pulling the Euclidean metric of $CC$ back along the two character
    sheets gives
    $
      g_+=e^(-2x)(dif x^2+dif theta^2),
      quad
      g_-=e^(2x)(dif x^2+dif theta^2).
    $
    Both metrics are locally flat. Their average and oriented
    half-difference are
    $
      (g_++g_-)/2=cosh(2x)(dif x^2+dif theta^2),
    $
    $
      (g_--g_+)/2=sinh(2x)(dif x^2+dif theta^2).
    $
    In the $(C,N)$ carrier, the difference of the two ambient Euclidean
    forms is the exact Lorentzian parameter metric
    $
      abs(dif C)^2-abs(dif N)^2
      =dif theta^2-dif x^2.
    $

    If $a=p^(-1/2)$ and
    $
      D_+(x,theta)=1-a A_+(x,theta),
    $
    then its Euler metric is
    $
      G_+(x,theta)
      =1+a^2 e^(-2x)-2a e^(-x)cos theta.
    $
    At the fixed seam,
    $
      partial_epsilon log G_+ |_(epsilon=0)
      =
      2L sum_(m>=1)a^m cos(m theta),
    $
    with the tail controlled by the geometric-remainder squeeze. The
    partner sheet has the opposite normal derivative.
  ],
  proof: [
    The formulas for $A_+$ and $A_-$ follow from
    $p^(-s)=e^(-s log p)$. Adding and subtracting them gives the hyperbolic
    factors, and $cosh^2 x-sinh^2 x=1$ gives the complex-square identity.
    Differentiation gives
    $
      abs(dif A_+)^2=e^(-2x)(dif x^2+dif theta^2)
    $
    and the analogous lower sheet. Each conformal exponent is affine in
    $x$, so its two-dimensional Gaussian curvature is zero. Directly
    differentiating $C$ and $N$ gives the Lorentzian difference.

    Expanding $abs(1-a e^(-x-i theta))^2$ gives $G_+$. At $x=0$,
    logarithmic differentiation gives
    $
      2L op("Re")(z/(1-z)),
      quad z=a e^(-i theta).
    $
    Since $a<1$, the squeeze lemma licenses
    $z/(1-z)=sum_(m>=1)z^m$ and controls every finite truncation remainder.
    Replacing $x$ by $-x$ reverses the normal derivative.
  ],
  boundary: [
    The Lorentzian metric is an exact signature on the parameter carrier,
    not a physical spacetime metric. A single prime character supplies flat
    local sheets and no intrinsic triangular holonomy. In the semilocal
    receiver, the first nontrivial connection is instead the turn of the
    receiving projection when it fails to commute with the Euler metric.
    The theorem does not extend the Euler product into the critical strip,
    identify zeta zeros, or sign the completed Weil response.
  ],
)
