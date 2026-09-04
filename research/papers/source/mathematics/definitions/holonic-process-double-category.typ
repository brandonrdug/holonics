#let holonic-process-double-category = (
  key: "definition:holonic-process-double-category",
  kind: [Definition],
  title: [Holonic processes as an open-system double category],
  status: [Project definition; standard structured-cospan carrier],
  depends: (
    "definition:holon",
    "definition:situated-event-correspondence",
  ),
  claim: [
    Let $cal(A)$ be a category of typed exposed boundaries, let $cal(C)$ be a
    finitely cocomplete category of causal constructions, and let
    $L:cal(A) arrow.r cal(C)$ preserve the finite colimits used below. Choose
    an admissible decoration family $cal(D)$ carrying the orientation,
    incidence, parameters, and receiver data required by the question.

    The *holonic process double category* $bb(H)_cal(D)$ has:

    - objects $a in cal(A)$, the typed exposed boundaries;
    - vertical arrows $f:a arrow.r a'$, the lawful boundary recharts;
    - horizontal arrows
      $
        L(a) arrow.r^i X arrow.l^o L(b),
      $
      the $cal(D)$-decorated situated open constructions from $a$ to $b$; and
    - 2-cells, the commuting maps of apices which preserve both boundary legs
      and every declared decoration.

    Sequential composition glues an outgoing boundary to a compatible
    incoming boundary by pushout. The horizontal unit is the identity
    cospan. Coproduct supplies symmetric monoidal *juxtaposition*. It does not
    by itself assert contact, shared current, or causal co-presence.

    Let $bb(I)$ be a separately declared double category or colored operad of
    interface patterns. A module action
    $
      mu:op("Sys") times bb(I) arrow.r op("Sys")
    $
    forms actual co-presence by port plugging, variable sharing, guarded
    incidence, lensing, or another typed interaction species. Under the
    structured-cospan hypotheses the open constructions form a symmetric
    monoidal double category; the action determines which juxtaposed
    constructions actually meet. Its horizontal bicategory is written
    $op("HolProc")_cal(D)$.

    When process homs are enriched over a monoidal parameter category
    $cal(P)$, a law $Lambda_F$ is a generalized element of the appropriate
    hom-object selected from the supplied question, standing construction,
    and live lineages. Parameter copying or departure follows the structure
    carried by $cal(P)$; it is not granted uniformly.

    A receiver is *strictly compositional at its declared scope* when it
    extends to a functor from the relevant sub-bicategory of
    $op("HolProc")_cal(D)$ into its category of presented faces. More
    generally it may be lax or oplax: the directed comparison 2-cell carries
    the composition residual rather than erasing it.
  ],
  proof: none,
  boundary: [
    The structured-cospan theorem supplies the carrier only after
    $cal(A),cal(C),L$, and the decoration laws are chosen. It does not say
    that every scientific domain has the same objects, dynamics, metric, or
    equations. Coproduct records independent juxtaposition, not chronology or
    contact. Pushout records lawful boundary gluing, not arbitrary physical
    fusion. An interaction action owes its explicit interface pattern. A
    receiver which does not preserve composition strictly owes a directed
    comparison cell or an OPEN residual rather than becoming strict by
    declaration.
  ],
)
