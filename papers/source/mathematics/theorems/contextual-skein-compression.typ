#let contextual-skein-compression = (
  key: "theorem:contextual-skein-compression",
  kind: [Theorem],
  title: [Exact local substitution is compression only through a compositional receiver],
  status: [Exact consequence of contextual receiver equivalence],
  depends: (
    "definition:contextual-tangle-compression",
    "lemma:receiver-nonreconstruction",
  ),
  claim: [
    Let $T approx_cal(R) T'$ be contextual receiver equivalence at boundary
    $B$.  Then for every finite tower of admitted exterior contexts
    $C_n[dots C_1[-]dots]$ and every receiver $R in cal(R)$,
    $
      R(C_n[dots C_1[T]dots])
      =
      R(C_n[dots C_1[T']dots]).
    $
    Thus replacing $T$ by $T'$ is an exact compression for that complete
    future context-and-receiver family.

    If only one closure $C_0[T]$ and one receiver value agree, the same
    conclusion does not follow.  If instead a skein relation
    $alpha[T_+]+beta[T_-]+gamma[T_0]=0$ is supplied, exact substitution holds
    linearly in the skein module but does not make any pair of the three
    interiors equivalent.
  ],
  proof: [
    Contextual equivalence quantifies over every admitted context.  Applying
    its defining equality first to $C_1$, then regarding the result as an
    interior of $C_2$, and continuing inductively proves the first claim.
    Equality under one context is not quantified over later contexts, so it
    cannot prove the converse.  A skein relation is equality of a linear
    combination in a quotient module, not equality of its generators.
  ],
  boundary: [
    The theorem does not supply a complete set of local relations, a
    terminating or confluent normal form, or a cost improvement.  Exact
    contextual compression can be nonlocal to discover even when the
    replacement itself is local.  Brittenham--Hermiller's nonadditivity of
    unknotting number is a concrete warning that factorwise simplification
    costs need not add after composition.
  ],
)
