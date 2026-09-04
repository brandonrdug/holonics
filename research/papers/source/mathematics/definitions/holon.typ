#let holon = (
  key: "definition:holon",
  kind: [Definition],
  title: [Holon],
  status: [Project definition],
  depends: (
    "definition:situated-occurrence",
    "definition:receiver",
  ),
  claim: [
    A *holon* at receiver $rho$ and grain $g$ is a tuple
    $H_rho=(X,B_rho,cal(T),q_rho)$ in which $X$ is a local occurrence
    complex, $B_rho subset.eq X$ is its exposed boundary, $cal(T)$ is its
    admitted transport family, and $q_rho:X -> Y_rho$ is its receiver. Its
    internal incidences close relative to $B_rho$, and its presented face is
    the image $q_(rho) (X)$. It is whole at grain $g$ precisely where that
    relative closure can participate as one constituent of a higher-grain
    relation.
  ],
  proof: none,
  boundary: [
    Whole and constituent are relational roles. The definition does not impose
    a permanent ownership tree or require the lower interior to remain active.
  ],
)
