#let receiver-indexed-holonic-system = (
  key: "definition:receiver-indexed-holonic-system",
  kind: [Definition],
  title: [Receiver-indexed holonic system and bounded global assembly],
  status: [Project definition using standard indexed-category, enrichment, open-system, and sheaf structures],
  depends: (
    "definition:holonic-process-double-category",
    "definition:co-present-receiver-atlas",
  ),
  claim: [
    A *receiver-indexed holonic system* consists of the following typed data.

    - A category $cal(S)$ of admissible evolution shapes.
    - A symmetric monoidal double category $bb(I)$ of exposed interfaces and
      interaction patterns, together with a module $op("Sys")$ on which those
      patterns act.
    - A monoidal parameter category $cal(P)$ and $cal(P)$-enriched process
      hom-objects. Copying, retaining, or discarding a parameter is available
      only when its object carries the corresponding comonoid or resource law.
    - A receiver/context category $cal(R)$ and a fibration
      $
        p:cal(E) arrow.r cal(R),
      $
      whose fiber $cal(E)_rho$ is the local ecology available at receiver
      $rho$. A receiver transport $u:rho arrow.r sigma$ acts through a
      declared cartesian, cocartesian, lax, or oplax lift; it is not an exempt
      change of coordinates.
    - For each participating receiver, a realization
      $
        X_rho:cal(S) arrow.r cal(E)_rho
      $
      compatible with the interaction action at the declared scope.
    - A presheaf $cal(O)$ of received faces on a declared site of apertures.
      A section over a covered region is *global at that region* only when it
      is the unique sheaf gluing of compatible local sections.

    The contextual law
    $
      Lambda_F(Q ⊗ A ⊗ L) arrow.r (P,pi_B)
    $
    is a generalized element of an enriched process hom-object selected by
    the present frame $F$, standing $A$, live incidence $L$, and exposed
    boundaries. It is not a detached scalar function and does not range over
    every potential arrow. The present question and boundaries determine an
    admitted subdiagram $cal(S)_F$; only morphisms which factor into that
    active construction participate.

    Consequently a global face is never absolute. It is a holon over a named
    region $U$: a boundary-defined whole whose local sections transport and
    agree across a cover of $U$. A global invariant is a compatible natural
    family over that covered holon. Potentials outside the admitted
    factorization remain possible in the wider categories but are not active
    constituents of the contemporary event.
  ],
  proof: none,
  boundary: [
    The total category $cal(E)$ assembled by a Grothendieck construction is
    bookkeeping for the indexed fibers, not a privileged total observer.
    Monoidal juxtaposition does not itself create contact. Actual interaction
    requires an action of a declared wiring, cospan, lens, or other interface
    pattern. Pairwise-compatible local faces need not possess a common global
    section. A sheaf gluing, when it exists, is still relative to its region,
    topology, receiver family, and event grain.
  ],
)
