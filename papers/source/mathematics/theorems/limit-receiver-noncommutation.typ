#let limit-receiver-noncommutation = (
  key: "theorem:limit-receiver-noncommutation",
  kind: [Theorem],
  title: [A limit does not transport between receivers without a continuous factorization],
  status: [Exact; the transport criterion is one line, and the witness is classical],
  depends: (
    "definition:receiver-indexed-convergence",
    "definition:receiver",
    "lemma:receiver-nonreconstruction",
  ),
  claim: [
    Let $q_rho:X -> Y_rho$ and $q_sigma:X -> Y_sigma$ be receivers on one
    construction space, each carrying a declared convergence.

    *(TRANSPORT)* If $q_sigma$ factors continuously through $q_rho$, that is if
    there is a continuous $h$ with
    $
      q_sigma = h compose q_rho,
      quad "(FACTORIZATION)"
    $
    then $x_i ->_rho x$ implies $x_i ->_sigma x$ for every net.

    *(OBSTRUCTION)* Consequently, if some net converges at $rho$ and fails to
    converge at $sigma$, then no continuous $h$ satisfies ("FACTORIZATION"). The
    failure is a *witnessed obstruction to factorization*, not an inconsistency.

    *(WITNESS -- the diagonal paradox)* Let $X$ be the rectifiable paths in the
    unit square from $(0,0)$ to $(1,1)$. Let $s_n in X$ be the staircase of $2n$
    alternating axis-parallel segments and let $D$ be the diagonal. Take
    $
      q_"pos":X -> cal(K),
      quad
      q_"len":X -> RR_(>=0),
    $
    where $cal(K)$ is the compact subsets of the square under the Hausdorff
    metric, $q_"pos"$ returns the image and $q_"len"$ the arc length. Then
    $
      q_"pos"(s_n) -> q_"pos"(D),
      quad "so" quad
      s_n ->_"pos" D,
      quad "(POSITION CONVERGES)"
    $
    while
    $
      q_"len"(s_n)=2 " for every " n,
      quad
      q_"len"(D)=sqrt(2),
      quad
      2 != sqrt(2),
      quad "so" quad
      s_n arrow.r.not_"len" D.
      quad "(LENGTH DOES NOT)"
    $
    Hence arc length does not factor continuously through the image.

    *(THE FAILURE IS ONE-SIDED)* By Golab's semicontinuity theorem, compact
    connected $K_n -> K$ in the Hausdorff metric satisfy
    $
      cal(H)^1(K) <= liminf_n cal(H)^1 (K_n).
      quad "(SEMICONTINUITY)"
    $
    So the length receiver can only *lose* in the limit, never gain: here
    $sqrt(2) <= 2$, with the inequality strict. The obstruction has a hand.
  ],
  proof: [
    *(TRANSPORT)* Suppose $x_i ->_rho x$ and $q_sigma=h compose q_rho$ with $h$
    continuous. Then $q_rho(x_i) -> q_rho(x)$ in $Y_rho$, and continuity of $h$
    carries a convergent net to a convergent net, so
    $q_sigma(x_i)=h(q_rho(x_i)) -> h(q_rho(x))=q_sigma(x)$, which is
    $x_i ->_sigma x$.

    *(OBSTRUCTION)* Contrapositive of (TRANSPORT).

    *(WITNESS)* Every point of $s_n$ lies within $1\/n$ of the diagonal and every
    point of the diagonal within $1\/n$ of $s_n$, so the Hausdorff distance is at
    most $1\/n$ and tends to zero. Each $s_n$ consists of $n$ horizontal segments
    of total length $1$ and $n$ vertical segments of total length $1$, whichever
    the step sizes, since the horizontal displacements sum to $1$ and the
    vertical displacements sum to $1$ and no segment is traversed backward. Hence
    $q_"len"(s_n)=2$ for every $n$, independently of $n$, while
    $q_"len"(D)=sqrt(2)$ by Pythagoras. The two receivers therefore disagree, and
    by (OBSTRUCTION) no continuous factorization exists.
  ],
  boundary: [
    The two returns are *both exact*. "The staircase converges to the diagonal"
    and "the staircase does not converge to the diagonal" are simultaneously
    true at their declared receivers, and the classical paradox is produced
    entirely by the unindexed word "converges". Nothing here is a defect of the
    limit, of the staircase, or of length.

    (SEMICONTINUITY) is the classical Golab theorem and requires compact
    *connected* sets; it is not a general one-sidedness law for arbitrary
    receivers. A different receiver may fail in the other direction or in
    neither, and its hand must be established separately.

    The theorem gives a criterion, not a construction. Exhibiting $h$ when it
    exists, and exhibiting the separating pair when it does not, both remain
    work for the particular pair of receivers.
  ],
)
