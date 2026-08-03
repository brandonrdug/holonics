#let pi-split-formulation-family = (
  key: "theorem:pi-split-formulation-family",
  kind: [Theorem],
  title: [A parameterized two-arm formulation family for pi],
  status: [Exact elementary derivation],
  depends: (
    "definition:formulation-span-atlas",
    "lemma:formulation-span-composition",
  ),
  claim: [
    On $B_pi=(0,1)$ define
    $
      tau_pi(t)={1-t}/{1+t}
      quad "and" quad
      M_pi(t)
      =
      4(
        arctan(t)
        +
        arctan(tau_pi(t))
      ).
    $
    Then $tau_pi:B_pi arrow.r B_pi$ is an involution,
    $
      M_pi(t)=pi
      quad "for every" t in B_pi,
    $
    and the swap of the two arctangent arms is an exact rechart. Its unique
    fixed parameter is
    $
      t=sqrt(2)-1.
    $
    At $t=1/2$ the family gives
    $
      pi
      =
      4(
        arctan(1/2)
        +
        arctan(1/3)
      ).
    $
    For the power-series receiver
    $
      arctan(z)
      =
      sum_(n>=0)
      {(-1)^n z^(2n+1)}/{2n+1},
      quad abs(z)<1,
    $
    the two parameter-dependent coefficient lineages remain distinct even
    though the value receiver is constant. Over the real family,
    $max(t,tau_pi(t))$ is minimized at the fixed parameter.
  ],
  proof: [
    Direct substitution gives $tau_pi(tau_pi(t))=t$ and preserves $(0,1)$.
    Moreover,
    $
      {t+tau_pi(t)}/{1-t tau_pi(t)}=1.
    $
    Both arctangents lie in $(0,pi/4)$, so the tangent addition formula has no
    branch ambiguity and their sum is $pi/4$. The fixed-point equation
    $t=tau_pi(t)$ reduces to $t^2+2t-1=0$, whose member in $(0,1)$ is
    $sqrt(2)-1$. Since $t$ increases and $tau_pi(t)$ decreases, their maximum
    is minimized exactly where they meet.
  ],
  boundary: [
    The open interval avoids a real interior singularity. A complex extension
    must separately carry the pole at $t=-1$, arctangent branch data, and the
    series boundaries $abs(t)=1$ or $abs(tau_pi(t))=1$. Constant return
    therefore does not collapse the family to one formulation occurrence.
  ],
)
