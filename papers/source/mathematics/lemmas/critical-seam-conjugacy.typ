#let critical-seam-conjugacy = (
  key: "lemma:critical-seam-conjugacy",
  kind: [Lemma],
  title: [The critical line is a chart of a fixed seam],
  status: [Exact coordinate-free reformulation],
  depends: ("lemma:mellin-return-seam",),
  claim: [
    On the completed spectral chart define the antiholomorphic involution
    $
      J(s)=1-overline(s).
    $
    Then
    $
      op("Fix")(J)={s:op("Re")(s)=1/2}.
    $
    If $phi$ is a biholomorphic rechart, the transported involution is
    $
      J_phi=phi compose J compose phi^(-1),
    $
    and
    $
      op("Fix")(J_phi)=phi(op("Fix")(J)).
    $
    Thus $"Re"(s)=1/2$ is the affine-chart expression of the invariant fixed
    seam, not an absolute line visible outside the completed relation.
  ],
  proof: [
    The equality $J(s)=s$ is equivalent to
    $s+overline(s)=1$, hence to $"Re"(s)=1/2$. If $J(s)=s$, then
    $J_phi(phi(s))=phi(J(s))=phi(s)$. Applying $phi^(-1)$ proves the reverse
    inclusion.
  ],
  boundary: [
    Conjugating the seam does not move a zero onto it. It only expresses the
    same fixed locus in another chart. A proof of RH still owes a mechanism
    which excludes zero orbits away from that locus.
  ],
)
