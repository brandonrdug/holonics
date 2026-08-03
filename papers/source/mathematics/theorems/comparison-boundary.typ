#let comparison-boundary = (
  key: "theorem:comparison-boundary",
  kind: [Theorem],
  title: [The boundary of a supplied triangular comparison closes],
  status: [Exact simplicial theorem],
  depends: ("definition:comparison-face",),
  claim: [
    Let $u:A -> B$, $v:B -> C$, and $w:A -> C$ be actual oriented
    1-cell occurrences, and let $tau$ be a supplied oriented comparison
    2-cell with
    $
      partial tau=v-w+u.
    $
    Then $partial^2 tau=0$.
  ],
  proof: [
    The oriented edge boundaries are
    $partial u=B-A$, $partial v=C-B$, and $partial w=C-A$. Therefore
    $
      partial^2 tau
      =(C-B)-(C-A)+(B-A)=0.
    $
    Cancellation occurs on the same vertex occurrences because the face was
    actually glued along those incidences.
  ],
  boundary: [
    The identity validates the supplied face. It does not attach $tau$ to
    arbitrary paths or declare their transports equal.
  ],
)

