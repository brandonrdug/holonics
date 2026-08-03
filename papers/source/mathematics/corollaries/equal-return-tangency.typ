#let equal-return-tangency = (
  key: "corollary:equal-return-tangency",
  kind: [Corollary],
  title: [Equal return forces a situated tangency or a seam],
  status: [Classical pathwise Rolle consequence; exact laboratory seam synthesis],
  depends: ("lemma:situated-mean-transport",),
  claim: [
    Under the smooth scalar hypotheses of the situated mean-transport
    lemma, if $f(q)=f(p)$, there is a $c in (0,L)$ such that
    $
      d f_(gamma(c))(dot(gamma)(c))
      =
      g_(gamma(c))(
        op("grad")_g f|_(gamma(c)),
        dot(gamma)(c)
      )
      =
      0.
    $
    At a regular point of a surface or higher-dimensional manifold, the
    path tangent is therefore tangent to the level hypersurface
    $f^(-1)(f(p))$ at $gamma(c)$.  If an entire smooth family preserves the
    return, then
    $
      d f_(gamma(s))(dot(gamma)(s))=0
    $
    at every regular parameter value, so its tangent current lies in
    $ker(d f)$ throughout the family.

    For a piecewise-smooth path with declared seams and the same endpoint
    return, the complete closure law is instead
    $
      sum_j integral_(I_j) d f(dot(gamma)) dif s
      =
      -sum_k Delta_k.
    $
    A path with no smooth tangency can therefore close only through one or
    more nonzero seam terms.
  ],
  proof: [
    The first statement is Rolle's theorem applied to $f compose gamma$,
    together with the Riemannian identity
    $d f(X)=g(op("grad")_g f,X)$.  If $f compose gamma$ is constant, its
    derivative vanishes everywhere.  The seam statement follows by setting
    the endpoint difference to zero in the piecewise mean-transport
    identity.
  ],
  boundary: [
    Tangency to a level set does not imply $op("grad")_g f=0$, identify a unique
    point, or make the witness independent of the path.  Equal returned
    scalar values do not identify the paths' factor support, branch,
    holonomy, or interior topology.  A nonsmooth, multivalued, or
    bundle-valued return requires its declared chart, connection, and seam
    data before this scalar corollary applies.
  ],
)
