#let passive-incidence-kron-composition = (
  key: "theorem:passive-incidence-kron-composition",
  kind: [Theorem],
  title: [Passive incidence survives internal balance, gluing, and shorting],
  status: [
    Exact chain/cochain, port-response, and composition law; no claim that
    the Weil successor already has the required passive realization
  ],
  depends: (
    "theorem:conditioned-effective-tension",
  ),
  claim: [
    Let an oriented incidence complex have vertex fiber
    $
      cal(V)=cal(V)_I⊕cal(V)_B,
    $
    edge fiber $cal(E)$, boundary operator
    $partial:cal(E) arrow.r cal(V)$, and coboundary
    $d=partial^*:cal(V) arrow.r cal(E)$.  Let $W>=0$ be an edge
    constitutive operator and let $G>=0$ be a vertex-storage operator.
    On their natural common form domain define
    $
      cal(E)(v)
      =
      norm(W^(1/2)d v)^2+norm(G^(1/2)v)^2
      =
      chevron.l L v,v chevron.r,
      quad
      L=d^*W d+G.
      quad "(PASSIVE INCIDENCE)"
    $
    Here $partial_(k-1)partial_k=0$ types legal incidence when adjacent
    chain degrees are present; nonnegativity comes from $W$ and $G$, not
    from that topological identity alone.

    Write the response operator in interior/boundary blocks as
    $
      L=mat(A,&C;C^*,&D)
    $
    and suppose $A>=lambda_I I$ for some $lambda_I>0$.  Supplying boundary
    potential $y$ and imposing zero interior injection gives
    $
      A x+C y=0,
      quad
      x_y=-A^(-1)C y.
      quad "(INTERIOR BALANCE)"
    $
    The returned boundary current is
    $
      i_B
      =
      C^*x_y+D y
      =
      S y,
      quad
      S=D-C^*A^(-1)C.
      quad "(PORT RESPONSE)"
    $
    Moreover,
    $
      chevron.l S y,y chevron.r
      =
      inf_x cal(E)(x⊕y)>=0.
      quad "(PASSIVE SHORT)"
    $
    Thus the Dirichlet-to-Neumann response and the Kron reduction are the
    same returned boundary law, and internal balance cannot turn a passive
    incidence network into a negative terminal response.

    Parallel composition adds edge and storage forms.  Gluing two ports
    identifies their potentials and sums their oriented currents.  Both
    operations preserve ("PASSIVE INCIDENCE").  Eliminating any completed
    set of internal vertices then preserves ("PASSIVE SHORT"), and nested
    eliminations are associative.  Consequently a support induction would
    be complete if every source successor supplied, before the sign was
    assumed, an enlarged incidence/storage form with nonnegative
    constitutive operators whose Kron return is the next Weil form.

    In a capacitive reading, $rho=G v$ is stored charge and
    $dot(rho)$ is displacement current.  The complete balance law is
    $
      partial j+dot(rho)=s.
      quad "(STORED BALANCE)"
    $
    A nonzero port imbalance at one cut can therefore be the rate of change
    of internal storage.  Conservation applies to conduction plus storage
    over the complete event; it does not require the visible terminal
    currents to cancel instantaneously.
  ],
  proof: [
    Positivity in ("PASSIVE INCIDENCE") is immediate from the two squared
    norms.  The interior Euler equation is ("INTERIOR BALANCE").
    Substitution gives ("PORT RESPONSE"), while completing the square gives
    $
      cal(E)(x⊕y)
      =
      norm(A^(1/2)(x+A^(-1)C y))^2
      +chevron.l S y,y chevron.r.
    $
    This proves ("PASSIVE SHORT").  Direct sums preserve squared norms,
    and port gluing is restriction to a closed linear relation, so neither
    can create negative energy.  Associativity follows because successive
    shorts minimize over the same total interior.  Finally
    ("STORED BALANCE") is the vertex balance obtained by adjoining the
    time derivative of the stored vertex quantity to the incident edge
    current.
  ],
  boundary: [
    This theorem says exactly what a circuit proof of a Weil-support
    successor would owe.  A signed off-diagonal coupling, a conservation
    identity, or a Schur complement is not by itself such a proof.  The
    source must also supply the nonnegative edge self-terms or storage whose
    complete form is being shorted.  Factoring an operator only after
    assuming that operator nonnegative would be circular.
  ],
)
