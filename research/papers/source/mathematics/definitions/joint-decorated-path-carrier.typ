#let joint-decorated-path-carrier = (
  key: "definition:joint-decorated-path-carrier",
  kind: [Definition],
  title: [Joint receiver decoration of lawful source paths],
  status: [Project definition with an exact bounded implementation],
  depends: (
    "definition:co-present-receiver-atlas",
    "definition:receiver-topology-atlas",
    "definition:situated-knot-receiver",
  ),
  claim: [
    Let $X_e$ carry a finite ordered source-incidence complex with oriented
    source darts $arrow(E)_X$. For a co-present receiver family
    $cal(J)=(q_r)_(r in I)$, every regular apparent crossing between source
    branches $a$ and $b$ supplies two typed source parameters
    $
      (a,s_a; b,s_b; r),
    $
    not one new source vertex.

    The family founds the common finite subdivision
    $
      Pi_a
      =
      {0,1}
      union
      {s_a : (a,s_a; b,s_b; r) " is visible for some " r}.
    $
    Every receiver evaluates every interval of $Pi_a$, while only the
    receivers which actually present a crossing carry its over/under and
    orientation marks.

    A *joint decorated dart* retains:

    + its oriented source branch, endpoints, frame, and exact source chord;
    + the ordered common subdivision $Pi_a$;
    + each receiver's exact projected interval chords and local gauge
      quotients; and
    + each receiver's own ordered crossing marks.

    The lawful transition relation is
    $
      cal(T)_cal(J)
      =
      {
        (d,d') :
        t(d)=o(d'),
        d' != overline(d)
      }.
    $
    Its junction is the actual source incidence $t(d)$. An apparent receiver
    crossing cannot supply a member of $cal(T)_cal(J)$ unless the source
    independently declares that incidence.

    $"Path"(cal(T)_cal(J))$ is the corresponding free noncommutative decorated
    path carrier. Source order, receiver marks, interval geometry, and any
    later evaluation remain separate fields until a domain law explicitly
    composes them.
  ],
  proof: none,
  boundary: [
    The common subdivision is the grain of one declared co-present receiver
    family, not a claim of physical quantum entanglement. Source-thread order
    is the chronology available in the bounded implementation; another
    ecology owes its own native partial order. The definition supplies no
    scalar weight, probability law, connection, curvature, completed-zeta
    trace identity, or prime correspondence.
  ],
)
