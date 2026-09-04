#let ordered-composition = (
  key: "lemma:ordered-composition",
  kind: [Lemma],
  title: [Order belongs to transported composition],
  status: [Exact derivation],
  depends: ("definition:situated-occurrence",),
  claim: [
    For composable transport generators
    $a_i:x_i -> x_(i+1)$, the path
    $gamma=a_n dots a_1$ carries
    $
      T_gamma=T_(a_n) compose dots compose T_(a_1).
    $
    Reversing the written list without supplying inverse transports does not
    recover the reverse path.
  ],
  proof: [
    Composition is defined by feeding the output of $T_(a_i)$ into the domain
    of $T_(a_(i+1))$. Reversing the order generally destroys that typing; even
    when every generator is an endomorphism of one space, the reversed product
    need not agree unless the relevant maps commute. Only when every
    $T_(a_i)$ is invertible does exact reverse traversal have the separately
    supplied transport
    $T_gamma^(-1)=T_(a_1)^(-1) compose dots compose T_(a_n)^(-1)$.
  ],
  boundary: [
    No commutativity, invertibility, or time-reversal symmetry is assumed.
  ],
)
