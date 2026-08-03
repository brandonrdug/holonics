#let four-member-projective-swing = (
  key: "theorem:four-member-projective-swing",
  kind: [Theorem],
  title: [Three marked members fix a projective pivot; the fourth carries the swing],
  status: [Classical projective-line theorem with a receiver-atlas interpretation],
  depends: (
    "definition:co-present-receiver-atlas",
    "definition:comparison-face",
  ),
  claim: [
    Let $A,B,C,D$ be four distinct marked occurrences on one projective line
    $PP^1(K)$. There is a unique projectivity $h$ sending
    $
      (A,B,C) mapsto (infinity,0,1).
    $
    The remaining coordinate is
    $
      h(D)
      =
      chi(A,B;C,D)
      =
      frac((C-A)(D-B), (C-B)(D-A)).
      quad "(SWING)"
    $
    For every projectivity $g$ defined on the quadruple,
    $
      chi(g(A),g(B);g(C),g(D))=chi(A,B;C,D).
      quad "(RECEIVER COVARIANCE)"
    $
    Hence three marked members establish the local projective gauge and the
    fourth supplies its first nontrivial projective invariant.

    The same statement applies to four lines in a projective pencil through
    one pivot in any higher-dimensional projective space.  Overlapping cells
    $
      (A,B,C) arrow.r D,
      quad
      (B,C,D) arrow.r E
    $
    therefore grow a receiver atlas by retaining a pivot triple while
    adjoining one new swing coordinate at a time.

    Every nondegenerate field element $x$ has the exact face
    $
      x=chi(infinity,0;1,x).
    $
    If a receiver selects a nonzero quantity $m$ as its unit, then its local
    coordinate becomes $1$ while the transition to a receiver with unit $u$
    carries $m/u$. Normalization moves the value into receiver transport; it
    does not erase its construction or lineage.
  ],
  proof: [
    The group $op("PGL")_2(K)$ acts sharply triply transitively on ordered triples
    of distinct points of $PP^1(K)$, which gives the unique $h$. Direct
    substitution into the fractional-linear action proves
    ("RECEIVER COVARIANCE"). A projective pencil is itself a projective line,
    so the higher-dimensional local statement is the same theorem. The unit
    statement follows from the typed rebase law
    $x_(a u)(q)=a^(-1)x_u(q)$.
  ],
  boundary: [
    Four is the canonical local population for one projective swing, not a
    universal maximum number of receivers. A receiver may expose several
    independent marks, while higher-rank or degenerate incidence may require
    additional overlapping cells. Cross-ratio equality does not identify
    complete causal interiors.
  ],
)
