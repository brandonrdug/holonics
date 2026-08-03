#let formulation-span-composition = (
  key: "lemma:formulation-span-composition",
  kind: [Lemma],
  title: [Formulation correspondences compose by shared interior],
  status: [Exact categorical derivation],
  depends: ("definition:formulation-span-atlas",),
  claim: [
    Assume the chosen formulation decorations are stable under identity spans
    and pullback composition. Let
    $
      U_cal(F) arrow.l W_(cal(F)cal(G)) arrow.r U_cal(G)
      quad "and" quad
      U_cal(G) arrow.l W_(cal(G)cal(H)) arrow.r U_cal(H)
    $
    be formulation correspondences over $B$. Their composite has apex
    $
      W_(cal(F)cal(G))
      times_(U_cal(G))
      W_(cal(G)cal(H)).
    $
    The diagonal span is an identity, and composition is associative up to
    the canonical pullback isomorphism. If both input correspondences are
    exact for the same receiver family $cal(R)_0$, then their composite is
    exact for $cal(R)_0$.
  ],
  proof: [
    The pullback consists precisely of pairs of supplied comparison states
    whose two middle legs name the same $cal(G)$-state. Its projections
    followed by the outer legs give a span from $cal(F)$ to $cal(H)$.
    Pullback uniqueness supplies the unitors and associator. For each
    $rho in cal(R)_0$, exactness identifies the $cal(F)$ and $cal(G)$
    receiver faces on the first apex and the $cal(G)$ and $cal(H)$ faces on
    the second. Equality is therefore transitive on the pullback.
  ],
  boundary: [
    The pullback matches only the middle data explicitly retained by the
    spans. It does not recover directions already discarded by either leg,
    and it does not turn a noninvertible correspondence into a rechart.
    Decoration stability must be proved for each specialization.
  ],
)
