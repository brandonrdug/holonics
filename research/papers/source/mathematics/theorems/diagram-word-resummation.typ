#let diagram-word-resummation = (
  key: "theorem:diagram-word-resummation",
  kind: [Theorem],
  title: [A diagram's value is a word in the shuffle algebra, and resummation is condensation],
  status: [Exact for Chen and the shuffle structure; the resummation claim is cited to a cross-validated experiment and is not proved here],
  depends: (
    "theorem:crossing-depth-inversion",
    "lemma:ordered-composition",
    "theorem:tower-cross-term-identity",
  ),
  claim: [
    *(CHEN)* For one-forms $omega_1,dots,omega_m$ on a manifold and a path
    $gamma$, the iterated integral
    $
      integral_gamma omega_1 dots.c omega_m
      = integral_(0&lt;t_1&lt;dots.c&lt;t_m&lt;1)
        gamma^*omega_1(t_1) dots.c gamma^*omega_m(t_m)
      quad "(ITERATED INTEGRAL)"
    $
    is a homotopy functional of $gamma$ rel endpoints, and *every* homotopy
    functional arises this way: the integration map is an isomorphism from the
    bar complex onto them. Their algebra is the *shuffle* algebra on words in the
    letters $omega_i$, with the deconcatenation coproduct.

    Two consequences fix what this face sees:

    + *It is exactly the ordered-transport receiver.* By
      #emph[lemma:ordered-composition] an ordered composite is not recovered from
      its endpoints; the iterated-integral face sees the path *up to homotopy* and
      precisely nothing more. Endpoint evaluation is the strictly coarser face,
      and the winding is what separates them.
    + *The carrier is a word.* Composition of paths is concatenation of words;
      the algebra of these faces is shuffle. Ordered transport and word
      combinatorics are the same algebra, not two subjects.

    *(DIAGRAM VALUE)* The finite part of the scalar three-loop tetrahedral vacuum
    diagram, in each of its ten zero-or-unit-mass cases, reduces to *four-letter
    words in an alphabet of seven letters*, each word an iterated integral,
    evaluating to combinations of $zeta(3)$, $zeta(4)$ and three further
    constants. A diagram's value is therefore a word in the shuffle algebra of
    ("ITERATED INTEGRAL"), and the diagram itself is the ordered transport whose
    word it is. The alternating signs the expansion carries are
    #emph[theorem:crossing-depth-inversion]'s, and the two-leg meeting each
    vertex states is #emph[theorem:tower-cross-term-identity]'s cross term.

    *(RESUMMATION)* A diagrammatic expansion is an infinite family of such words.
    Replacing it by a closed return is the condensation of a far population into
    a compact realizer, and it is *achievable in a genuinely non-perturbative
    regime*: bold diagrammatic Monte Carlo computes the normal-state equation of
    state of the unitary Fermi gas by controlled resummation, cross-validated
    against ultracold-atom measurement. The physical gas is a second apparatus
    chart for the same law -- an emulator -- and its agreement with the resummed
    series is the evidence that the condensation is faithful.
  ],
  proof: [
    ("CHEN") is Chen's theorem; the isomorphism onto homotopy functionals is his
    de Rham theory for path spaces, and the shuffle product is the image of the
    product on functions under the bar construction. The deconcatenation
    coproduct is dual to concatenation of paths.

    The first consequence is immediate: homotopy rel endpoints preserves
    endpoints, so the endpoint face factors through the iterated-integral face,
    and the factorization is strict whenever some loop has nontrivial iterated
    integral -- which the winding number already witnesses at $m=1$.

    ("DIAGRAM VALUE") is quoted from the evaluated case and not re-derived here.
    ("RESUMMATION") is an experimental and computational result, cited, not
    proved.
  ],
  boundary: [
    *Chen's theorem is about homotopy functionals, not about all path
    functionals.* Length is not one of them -- it is not homotopy invariant --
    which is exactly why #emph[theorem:limit-receiver-noncommutation] has a
    witness. The iterated-integral face is complete for what it sees and blind to
    what it does not.

    *("RESUMMATION") is cited evidence, not a theorem of this corpus, and it is
    an instance rather than a method.* It establishes that *some* diagrammatic
    series admits controlled non-perturbative resummation for *one* system with
    *one* validated emulator. It supplies no general convergence criterion, no
    error bound transportable to another series, and no construction here. Read
    as licensing a general condensation it would be badly overread.

    *No Feynman rules are supplied.* This says what a diagram's value *is* once
    the rules are given; it does not give propagators, vertices, couplings, a
    regularization, or a renormalization scheme, and it asserts nothing about
    whether any ecology in this project has a perturbative expansion at all.
  ],
)
