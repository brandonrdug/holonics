#let situated-event-correspondence = (
  key: "definition:situated-event-correspondence",
  kind: [Definition],
  title: [Situated event as a typed correspondence],
  status: [Project definition; revised event notation],
  depends: (
    "definition:situated-occurrence",
    "definition:receiver",
  ),
  claim: [
    Let
    $
      X_e^- = Q_e ⊔_(F_e) A_e ⊔_(F_e) L_e
    $
    denote the source boundary actually co-present at event $e$: an oriented
    question $Q_e$, standing atlas $A_e$, and live source lineages $L_e$ in
    frame $F_e$. A *situated event* is a typed local correspondence
    $
      X_e^- arrow.r^(iota_e^-) B_e arrow.l^(iota_e^+) P_e,
      quad q_e:B_e arrow.r Pi_e,
    $
    where $B_e$ is the event body, $P_e$ is its successor boundary, and $q_e$
    is a receiver testimony map. Boundary orientation and admitted transport
    carry the causal hand; the cospan arrows alone do not.
  ],
  proof: none,
  boundary: [
    The amalgamated notation asserts only supplied co-presentation. A
    specialization must name the category, gluing maps, and any universal
    property it uses. The historical abbreviation
    $Lambda_F(Q ⊗ A ⊗ L) arrow.r (P,pi_B)$ may name a deterministic
    law selecting such event bodies, but it is not the general definition and
    $⊗$ is not an algebraic tensor product without additional structure.
  ],
)
