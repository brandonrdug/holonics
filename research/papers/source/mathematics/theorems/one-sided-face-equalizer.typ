#let one-sided-face-equalizer = (
  key: "theorem:one-sided-face-equalizer",
  kind: [Theorem],
  title: [An undefined two-sided limit is an empty equalizer, not an absent limit],
  status: [Exact; three declared targets return three exact values for one expression],
  depends: (
    "definition:receiver-indexed-convergence",
    "theorem:limit-receiver-noncommutation",
  ),
  claim: [
    Let $f(x)=1\/x$ near $a=0$. The approach side is part of the receiver, not
    part of $f$. Declare
    $
      rho_-:x arrow.t 0,
      quad
      rho_+:x arrow.b 0,
      quad
      rho_(plus.minus) = "the equalizer of" rho_- "and" rho_+,
      quad "(THREE APPROACHES)"
    $
    where the two-sided receiver returns a value exactly when the one-sided
    receivers return the same value. The return then depends on the declared
    target, and *all three targets are lawful*:

    #table(
      columns: 4,
      stroke: 0.4pt,
      [*target*], [*at $rho_-$*], [*at $rho_+$*], [*at $rho_(plus.minus)$*],
      [$RR$], [OPEN], [OPEN], [OPEN],
      [$RR union {-infinity,+infinity}$], [$-infinity$], [$+infinity$], [OPEN],
      [$RR union {infinity}$ (one point)], [$infinity$], [$infinity$], [$infinity$],
    )

    In particular, on the one-point compactification -- equivalently on the
    Riemann sphere $PP^1(CC)$, where $f$ is the chart inversion
    $[z:w] |-> [w:z]$ -- the two-sided receiver returns $infinity$ and *there is
    no discrepancy to explain*. The two sides were an artifact of the target,
    since $RR union {infinity}$ has no sides at $infinity$.

    Therefore the sentence "the limit of $1\/x$ at $0$ is undefined" names the
    emptiness of one equalizer under one target. It does not name an absence of
    limits, and it is false under a declared target which the same expression
    admits.
  ],
  proof: [
    On $RR$ the one-sided images are unbounded, so no grain is eventually
    attained and both one-sided receivers return OPEN by
    ("RECEIVER CONVERGENCE"); the equalizer of two OPEN returns is OPEN.

    On $RR union {plus.minus infinity}$ with its order topology, every
    neighborhood of $+infinity$ contains a ray $(M,infinity]$, and $x in (0,1\/M)$
    gives $1\/x>M$; symmetrically at $-infinity$. The two one-sided returns are
    distinct members of the target, so the equalizer is empty and
    $rho_(plus.minus)$ returns OPEN.

    On $RR union {infinity}$ every neighborhood of $infinity$ contains
    ${abs(y)>M}$, and $0<abs(x)<1\/M$ gives $abs(1\/x)>M$ irrespective of sign.
    Both one-sided returns are $infinity$, they agree, and the equalizer returns
    $infinity$.

    The three rows are three receivers, and by
    #emph[theorem:limit-receiver-noncommutation] their returns are not obliged to
    agree: the quotient $RR union {plus.minus infinity} -> RR union {infinity}$
    identifying the two infinities is a factorization in one direction only, and
    it is exactly the map under which the two disagreeing returns become one.
  ],
  boundary: [
    This does not make every undefined limit definable. It shows that
    "undefined" is a *receiver return* and must name its target before it can be
    read as a fact about the expression. Where no declared target closes the
    equalizer, OPEN stands, and OPEN is not a licence to choose a side.

    Nothing here asserts that the one-point compactification is the correct
    target for any particular application. Which target is in force is a
    declaration with consequences: $RR union {infinity}$ closes this equalizer
    and simultaneously destroys the order, so a construction that needs
    $-infinity < +infinity$ may not adopt it.
  ],
)
