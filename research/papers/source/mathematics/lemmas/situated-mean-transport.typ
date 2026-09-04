#let situated-mean-transport = (
  key: "lemma:situated-mean-transport",
  kind: [Lemma],
  title: [Mean transport is path-relative and seams add discrete terms],
  status: [Classical pathwise calculus and parallel transport; exact laboratory seam synthesis],
  depends: ("definition:receiver", "definition:phase"),
  claim: [
    Let $(M,g)$ be a Riemannian manifold, let
    $gamma:[0,L] arrow.r M$ be a unit-speed geodesic from $p$ to $q$, and
    let $f:M arrow.r RR$ be smooth on the traversed chart.  Then
    $
      f(q)-f(p)
      =
      integral_0^L
      d f_(gamma(s))(dot(gamma)(s)) dif s,
    $
    and there is a $c in (0,L)$ such that
    $
      f(q)-f(p)
      =
      L d f_(gamma(c))(dot(gamma)(c))
      =
      L g_(gamma(c))(
        op("grad")_g f|_(gamma(c)),
        dot(gamma)(c)
      ).
    $
    For two scalar fields $P,Q$, Cauchy's mean-value theorem along the same
    path gives a $c$ with
    $
      (P(q)-P(p)) d Q_(gamma(c))(dot(gamma)(c))
      =
      (Q(q)-Q(p)) d P_(gamma(c))(dot(gamma)(c)).
    $

    More generally, let $V(s) in E_(gamma(s))$ be a section along $gamma$ of
    a vector bundle with connection, and let $cal(P)_(s arrow.r 0)$ denote
    parallel transport into the initial fiber.  Then
    $
      cal(P)_(L arrow.r 0)V(L)-V(0)
      =
      integral_0^L
      cal(P)_(s arrow.r 0)
      nabla_(dot(gamma)) V(s) dif s.
    $
    If a piecewise-smooth parameter path crosses typed seams
    $s_1,dots,s_m$, its complete scalar transport decomposes as
    $
      f(gamma(L))-f(gamma(0))
      =
      sum_j integral_(I_j) d f(dot(gamma)) dif s
      +
      sum_k Delta_k,
    $
    where the $Delta_k$ are the declared branch, rank, phase, or discrete
    valuation changes at those seams.
  ],
  proof: [
    Apply the fundamental theorem of calculus and the ordinary scalar
    mean-value theorem to the pullback $f compose gamma$.  Apply Cauchy's
    theorem to $P compose gamma$ and $Q compose gamma$.  For the bundle
    statement, parallel-transport $V(s)$ into the fixed vector space
    $E_p$; the derivative of that pulled-back curve is
    $cal(P)_(s arrow.r 0)nabla_(dot(gamma))V(s)$, so ordinary vector-space
    integration gives the identity.  Split a piecewise-smooth path at every
    seam and telescope its endpoint changes; the unmatched one-sided values
    are exactly the $Delta_k$.
  ],
  boundary: [
    The witness $c$ belongs to the chosen path and need not be invariant
    under another route or parameterization.  A vector-valued mean-value
    equality at one point generally does not follow: values first require a
    connection and parallel transport into one fiber.  Transport around
    different paths may carry holonomy.  A discrete seam may not be hidden
    inside a smooth derivative or inferred from an averaged scalar.
  ],
)
