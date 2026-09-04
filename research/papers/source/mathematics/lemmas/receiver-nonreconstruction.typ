#let receiver-nonreconstruction = (
  key: "lemma:receiver-nonreconstruction",
  kind: [Lemma],
  title: [A non-injective face cannot reconstruct every interior],
  status: [Exact derivation],
  depends: ("definition:receiver",),
  claim: [
    If $q_rho:X -> Y_rho$ is non-injective, no function of the receiver value
    alone reconstructs every element of $X$.
  ],
  proof: [
    Choose $x != x'$ with $q_(rho) (x)=q_(rho) (x')$. A reconstruction
    $r:Y_rho -> X$ satisfying $r compose q_rho="id"_X$ would require the same
    argument to return both $x$ and $x'$, which is impossible.
  ],
  boundary: [
    A restricted inverse may exist on a supplied section or on a smaller
    observation family.
  ],
)
