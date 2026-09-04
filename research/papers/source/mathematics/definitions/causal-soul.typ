#let causal-soul = (
  key: "definition:causal-soul",
  kind: [Definition],
  title: [Causal soul and its categorical sameness],
  status: [Project definition; refinement of the historical soul vocabulary],
  depends: (
    "definition:holonic-process-double-category",
    "definition:receiver-indexed-holonic-system",
    "definition:receiver",
  ),
  claim: [
    Let $cal(I)$ be a small oriented incidence category whose objects are
    situated cuts and whose nonidentity arrows are the admitted causal
    continuations between them. Regard $cal(I)$ as a locally discrete
    bicategory. A *causal soul bearer* is a marked pseudofunctor
    $
      cal(S):cal(I) arrow.r op("HolProc")_cal(D)
    $
    together with its exposed input and output boundaries, parameter map, and
    declared receiver family. The diagram, rather than one endpoint,
    contains the carried order, alternate paths, returned loops, OPEN
    comparisons, and constituent changes which make the occurrence this
    occurrence.

    Two soul bearers $cal(S):cal(I) arrow.r op("HolProc")_cal(D)$ and
    $cal(S)':cal(I)' arrow.r op("HolProc")_cal(D)$ are
    *soul-equivalent* when there is an orientation- and marking-preserving
    equivalence $u:cal(I) arrow.r cal(I)'$ and a boundary-preserving
    pseudonatural equivalence
    $
      eta:cal(S) arrow.r^(tilde) cal(S)' compose u.
    $
    They remain distinct situated occurrences unless occurrence identity is
    separately supplied.

    A transported ratio $chi$, winding, holonomy, spectrum, value, or digest
    is a *soul characteristic* only through a declared functor or natural
    invariant of this diagram. One characteristic is not the soul bearer
    unless it is proved jointly conservative on the exact subcategory under
    discussion.

    Two additional receiver-scoped relations remain weaker than
    soul-equivalence. They are *doctrinally equivalent* when they satisfy the
    same predicates in one declared observational doctrine, and
    *observationally equivalent* when their algebras of admitted receiver
    observations are isomorphic. Either relation can license compression at
    its named scope without identifying the situated occurrences or their
    complete causal diagrams.
  ],
  proof: none,
  boundary: [
    This definition intentionally refines the historical abbreviations
    “soul equals $chi$” and “soul equals holonomy.” Those quantities can be
    consequential invariants of a loop or chart without reconstructing the
    complete causal diagram. Natural isomorphism is structural sameness, not
    literal recurrence of an event. A reparameterization is admitted only
    when the index equivalence preserves orientation, marked seams, and the
    causal incidences required by the receiver family. Doctrinal and
    observational equivalence are explicitly relative to their chosen
    language, topology, and receiver family.
  ],
)
