#let cm-norm-one-receiver-family = (
  key: "theorem:cm-norm-one-receiver-family",
  kind: [Theorem],
  title: [A CM norm-one constituent is circular in every complex receiver],
  status: [Classical algebraic-number-theoretic consequence used by the 2026 unit-distance construction],
  depends: (
    "definition:co-present-receiver-atlas",
    "definition:typed-axis-unit-ratio",
  ),
  claim: [
    Let $K/L$ be a CM quadratic extension with involution $c$, let
    $L$ be totally real of degree $f$, and choose one complex embedding
    $sigma_j:K arrow.r CC$ from each conjugate pair. The Minkowski receiver
    family is
    $
      Phi:K arrow.r CC^f,
      quad
      Phi(x)=(sigma_1(x),...,sigma_f(x)).
    $
    Every relative norm-one element
    $
      u c(u)=1
    $
    satisfies
    $
      abs(sigma_j(u))=1
      quad "for every" quad j.
    $
    Hence
    $
      Phi({u in K^times:u c(u)=1})
      subset
      (S^1)^f.
    $

    Every coordinate receiver $sigma_j$ is injective on $K$. Therefore a
    finite subset of one Minkowski lattice coset may be projected to any one
    complex coordinate without identifying its field elements; every
    difference by such a $u$ becomes a unit segment in that receiver.

    If a prime ideal $frak(p)$ and its conjugate $c frak(p)$ are exchanged
    by $c$, then a norm-one element carries the bipolar valuation law
    $
      v_(c frak(p))(u)=-v_(frak(p))(u).
    $
    One constituent can consequently have a prime-valuation face and a
    circular phase face across the same co-present arithmetic receiver
    family.
  ],
  proof: [
    Since $sigma_j(c(u))=overline(sigma_j(u))$,
    $
      1
      =
      sigma_j(u c(u))
      =
      sigma_j(u) overline(sigma_j(u))
      =
      abs(sigma_j(u))^2.
    $
    A field embedding is injective, proving the projection statement. Taking
    the $frak(p)$-valuation of $u c(u)=1$ and using
    $v_(frak(p))(c(u))=v_(c frak(p))(u)$ gives the bipolar valuation law.
  ],
  boundary: [
    This is a constraint-preserving arithmetic receiver construction, not
    an arbitrary visual projection and not a claim that every high-dimensional
    body can be flattened injectively. The norm-one torus does not by itself
    prove a statement about the Riemann zeta function. The unit-distance
    breakthrough additionally requires the number-field tower, split primes,
    class-group estimate, lattice cut, and population bound.
  ],
)
