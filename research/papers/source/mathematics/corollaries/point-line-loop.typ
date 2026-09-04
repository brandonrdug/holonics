#let point-line-loop = (
  key: "corollary:point-line-loop",
  kind: [Corollary],
  title: [Point, line, and loop are receiver faces of one occurrence],
  status: [Project corollary],
  depends: (
    "definition:situated-occurrence",
    "definition:receiver",
    "lemma:ordered-composition",
  ),
  claim: [
    One continuing occurrence can be point-like under an event-cut receiver,
    line-like under an order-preserving lineage receiver, and loop-like under
    a return receiver that identifies its terminal and initial base
    positions.
  ],
  proof: [
    Apply three different receiver maps to the same ordered occurrence:
    evaluation at one event, retention of the complete parameterized path,
    and projection to a closed base-space return. The maps preserve different
    distinctions, so the three faces need not be mutually reconstructive.
  ],
  boundary: [
    The corollary does not assert that every point is intrinsically a hidden
    loop; the required continuation and return must actually be supplied.
  ],
)

