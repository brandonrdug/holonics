#let weil-signature-transport = (
  key: "theorem:weil-signature-transport",
  kind: [Theorem],
  title: [A genuine negative direction cannot be removed by recharting],
  status: [Exact transport theorem],
  depends: ("definition:parametric-weil-bundle",),
  claim: [
    Let $T:cal(H)_lambda arrow.r cal(H)_mu$ be invertible and suppose
    $
      W_mu(T f,T g)=c W_lambda(f,g)
    $
    for one real $c>0$ and all $f,g$. Then
    $
      q_mu(T f)=c q_lambda(f),
    $
    so $T$ carries the positive, null, and negative cones bijectively.
    In particular, $W_lambda$ is positive semidefinite if and only if
    $W_mu$ is, and their maximal negative-subspace dimensions agree.
  ],
  proof: [
    Set $g=f$ in the covariance identity. Because $c>0$, the sign is
    unchanged. Invertibility gives the converse and maps every negative
    subspace isomorphically to a negative subspace. Applying the same argument
    to $T^(-1)$ proves equality of the maximal dimensions.
  ],
  boundary: [
    An individual path in an indefinite fiber may cross its null cone and
    change sign. That does not eliminate the fiber's negative directions.
    Multiplying a test current by $-1$ or by a unit complex phase also leaves
    a Hermitian quadratic response unchanged. A transformation which flips
    the sign of the form is not a harmless orientation change; it changes the
    positive structure being tested.
  ],
)
