#let receiver-indexed-convergence = (
  key: "definition:receiver-indexed-convergence",
  kind: [Definition],
  title: [Receiver-indexed convergence],
  status: [Project definition; the convergence receiver H.0208 requires before a limit may be called holonic],
  depends: (
    "definition:receiver",
    "definition:situated-occurrence",
    "definition:comparison-face",
  ),
  claim: [
    Let $q_rho:X -> Y_rho$ be a receiver. Let $rho$ additionally declare a
    *separating family* $cal(D)_rho$ of tests
    $
      d:Y_rho times Y_rho -> V_d,
      quad
      d(y,y)=0,
    $
    each valued in an ordered object $V_d$ with a distinguished zero and a
    declared family of *grains* $g succ 0$.

    A net $(x_i)_(i in I)$ in $X$ *converges at $rho$* to $x in X$, written
    $
      x_i ->_rho x,
    $
    when for every test $d in cal(D)_rho$ and every declared grain $g$ there is
    $i_0 in I$ with
    $
      d(q_rho(x_i),q_rho(x)) prec g
      quad "for all" quad i succ.eq i_0.
      quad "(RECEIVER CONVERGENCE)"
    $

    Read in the transport vocabulary: the net converges at $rho$ exactly when
    continued transport can no longer contribute a difference that $rho$ is able
    to experience. The limit is the *exhaustion of this receiver's distinguishing
    tests*, not an operation performed on $X$.

    Convergence is therefore a family of relations indexed by $rho$, and
    $->_rho$ and $->_sigma$ are different relations on the same net. Writing
    $x_i -> x$ without an index asserts a receiver that has not been declared.
  ],
  proof: none,
  boundary: [
    This defines *no new limit operation*. When $Y_rho$ carries a topology or
    uniformity, ("RECEIVER CONVERGENCE") is exactly ordinary convergence in
    $Y_rho$ pulled back along $q_rho$, and every classical theorem applies
    unchanged inside one index. The whole content is the index: it makes
    disagreement between receivers a theorem with a witness rather than a
    paradox, and it supplies the datum H.0208 names as missing.

    A separating family is *supplied by the receiver*, not derived from $X$.
    Two receivers with the same underlying map and different test families are
    different receivers. Nothing here licenses transporting a limit from one
    index to another; that requires a factorization, and its absence is the
    subject of #emph[theorem:limit-receiver-noncommutation].
  ],
)
