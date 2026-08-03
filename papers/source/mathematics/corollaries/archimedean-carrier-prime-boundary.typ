#let archimedean-carrier-prime-boundary = (
  key: "corollary:archimedean-carrier-prime-boundary",
  kind: [Corollary],
  title: [A finite place cannot enter through the fixed archimedean carrier aperture],
  status: [Exact boundary of the published base carrier],
  depends: (
    "theorem:archimedean-remainder-amplitude",
    "theorem:prime-power-aperture-incidence",
    "theorem:completed-defect-recurrence",
  ),
  claim: [
    At the base aperture $I_2$, for every prime $p>=2$ and every $m>=1$,
    $
      P_2 U_(m log p) P_2=0.
    $
    Hence for the one-prime Euler difference
    $
      J_p=I-p^(-1/2)U_(log p)
    $
    one has
    $
      P_2 J_p P_2=P_2.
    $
    Extending the base amplitude form
    $B_2=-P_0 N_2 P_0$ by zero outside $I_2$ therefore gives
    $
      P_2 J_p^* B_2 J_p P_2=B_2.
    $
    A fixed-aperture conjugation of the archimedean carrier cannot produce
    either the prime-power response or the receiver-aperture connection.

    After aperture growth, a semilocal carrier would instead have to be
    independently defined so that, in one anchored comparison chart,
    $
      B_(S union {p},R)-B_(S,R)
      =
      -cal(W)_(p,R)-cal(K)_(S,p,R)
    $
    as Hermitian forms, where the two forms on the right represent
    $W_p$ and $kappa_(S,p)$.  This is precisely the operator form of the
    completed-defect recurrence.
  ],
  proof: [
    The interval $I_2$ has length $log 2$, while
    $m log p>=log 2$.  The translated-aperture incidence theorem therefore
    makes every compressed shift zero.  Expanding the two displayed
    compressions gives the fixed-carrier identities.  The required
    successor equation is the completed-defect recurrence written after
    polarizing its quadratic responses.
  ],
  boundary: [
    This corollary does not assert that semilocal transport is impossible.
    It proves that the published base remainder cannot be propagated by
    keeping its support domain fixed.  The semilocal intertwiners construct
    the receiver, Euler metric, Sonin aperture, and connection term; the
    audited sources do not construct the expanded remainder operator
    $B_(S,R)$ or prove the displayed form identity.
  ],
)
