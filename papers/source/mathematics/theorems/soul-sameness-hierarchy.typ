#let soul-sameness-hierarchy = (
  key: "theorem:soul-sameness-hierarchy",
  kind: [Theorem],
  title: [Soul sameness is representable; a face or digest is only one quotient],
  status: [Exact categorical consequence],
  depends: (
    "definition:causal-soul",
    "lemma:receiver-nonreconstruction",
  ),
  claim: [
    Let $cal(D)_"soul"$ be the category of marked causal soul bearers and
    marking-preserving maps. For $cal(S),cal(S)' in cal(D)_"soul"$:
    $
      cal(S) tilde.eq cal(S)'
      quad "iff" quad
      cal(D)_"soul"(-,cal(S))
      tilde.eq
      cal(D)_"soul"(-,cal(S)')
    $
    naturally. The covariant representables give the dual criterion.

    For any receiver functor
    $R_rho:cal(D)_"soul" arrow.r cal(V)_rho$, any encoding functor
    $E:cal(D)_"soul" arrow.r op("Byte")$, and any digest map
    $h:op("Byte") arrow.r op("Digest")$, the generally valid implication
    hierarchy is
    $
      "occurrence identity"
      arrow.r.double
      "soul isomorphism"
      arrow.r.double
      R_rho(cal(S)) tilde.eq R_rho(cal(S)').
    $
    For any declared observational doctrine $P$ and observation algebra
    $cal(O)$, the complete implication hierarchy is
    $
      "occurrence identity"
      arrow.r.double
      "soul isomorphism"
      arrow.r.double
      "doctrinal equivalence under P"
      arrow.r.double
      "observational equivalence under O"
      arrow.r.double
      R_rho(cal(S)) tilde.eq R_rho(cal(S)').
    $
    The last three implications require that the doctrine, observational
    algebra, and receiver be obtained by successively forgetting structure
    from the marked soul category.

    Equality
    $
      h(E(cal(S)))=h(E(cal(S)'))
    $
    is only equality at the composite encoding receiver $h compose E$.
    Neither equal receiver face nor equal digest implies soul isomorphism
    without a proved conservativity or reconstruction hypothesis.
  ],
  proof: [
    The equivalence between object isomorphism and natural isomorphism of
    representable functors is the Yoneda isomorphism criterion. Functors
    preserve isomorphisms, proving the forward receiver implication.

    Conversely, a nonconservative doctrine or receiver can identify
    nonisomorphic objects. A constant receiver is the simplest example.
    Elementary equivalence retains only the predicates expressible in its
    doctrine; observational equivalence retains only its observation algebra.
    The composite $h compose E$ is one still narrower receiver. Even byte
    equality identifies only the selected encoding unless $E$ is proved
    faithful and complete for all marked structure in scope; digest equality
    is weaker still because $h$ is not injective as a mathematical map on
    arbitrary byte strings.
  ],
  boundary: [
    Yoneda determines an object up to isomorphism from its complete family of
    relations, not from a finite list of chosen observations. Doctrinal
    equivalence and observational sobriomorphism are lawful intermediate
    relations, not replacements for the soul bearer. The theorem does not
    make soul-equivalent occurrences literally identical, nor does it require
    keeping every historical constituent active. A lawful receiver-exact
    compression may discard distinctions after every declared future receiver
    factors through its face.
  ],
)
