#let transported-fundamental-theorem = (
  key: "theorem:transported-fundamental-theorem",
  kind: [Theorem],
  title: [Transported fundamental theorem along a path],
  status: [Classical connection identity],
  depends: ("lemma:ordered-composition",),
  claim: [
    Let $s(t)$ be a section of a vector bundle along a smooth path $gamma$,
    let $nabla$ be a connection, and let $U(t_2,t_1)$ be its parallel
    transport. Then
    $
      s(1)-U(1,0)s(0)
      =
      integral_0^1 U(1,t)
      nabla_(dot gamma(t))s(t)
      dif t.
    $
  ],
  proof: [
    Define $h(t)=U(1,t)s(t)$ in the single receiver fiber over $gamma(1)$.
    Compatibility of parallel transport gives
    $h'(t)=U(1,t)nabla_(dot gamma(t))s(t)$. Integrating the ordinary
    fundamental theorem from $0$ to $1$ yields the identity.
  ],
  boundary: [
    The formula requires the declared bundle and connection. It compresses the
    covariant change into a boundary difference but does not reconstruct the
    path, curvature, or holonomy discarded by that receiver.
  ],
)

