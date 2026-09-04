#let modulus-of-transport = (
  key: "definition:modulus-of-transport",
  kind: [Definition],
  title: [Modulus of transport, and the two grains of an epsilon--delta statement],
  status: [Project definition; standard modulus of continuity, re-indexed by its two receivers],
  depends: (
    "definition:receiver",
    "definition:receiver-indexed-convergence",
  ),
  claim: [
    Let $f:X -> Z$ be carried between a *source receiver* $q_rho:X -> Y_rho$
    with grain family $G_rho$ and an *observing receiver* $q_sigma:Z -> Y_sigma$
    with grain family $G_sigma$. These are two receivers and two grain families;
    the classical statement writes one bar $abs(dot)$ on both sides and thereby
    identifies them silently.

    $f$ is *continuous at $a$ relative to $(rho,sigma)$* when there exists a map
    $
      omega_a:G_sigma -> G_rho
      quad "(MODULUS OF TRANSPORT)"
    $
    such that for every observing grain $epsilon in G_sigma$,
    $
      d_rho (q_rho(x),q_rho(a)) prec omega_a (epsilon)
      quad arrow.r.double quad
      d_sigma (q_sigma(f x),q_sigma(f a)) prec epsilon.
      quad "(EPSILON--DELTA, INDEXED)"
    $

    Three readings follow immediately, and they are the content:

    + The quantifier alternation $forall epsilon exists delta$ *is* the
      assertion that $omega_a$ exists. Continuity is not a property of $f$ alone;
      it is the existence of a transport between two declared grains.
    + $omega_a$ runs *contravariantly*. It carries the observing receiver's grain
      back to the source receiver's grain, opposite to $f$. What is demanded at
      the far end determines what must be supplied at the near end.
    + The classical hierarchy is a hierarchy on $omega$: *uniform* continuity is
      $omega_a$ independent of $a$; *Lipschitz* is $omega_a$ linear; *Hölder* is
      $omega_a$ a power. A modulus that exists only pointwise is a transport that
      must be re-supplied at every base point.

    The word is not an accident of vocabulary. The *modulus* of a complex number,
    the *modulus of continuity*, and the engineer's *section modulus* are one
    role in three materials: the small measure that governs how much a
    displacement is allowed to return.
  ],
  proof: none,
  boundary: [
    Existence of $omega_a$ is a hypothesis about the pair of receivers, not a
    theorem about $f$. Choosing $rho=sigma$ and identifying the grain families
    recovers the ordinary definition exactly and loses the index; that recovery
    is lawful whenever the two receivers genuinely coincide, and is the hidden
    step whenever they do not.

    Nothing here supplies a modulus. A construction that cannot exhibit
    $omega_a$ has not established continuity at that pair of receivers, and the
    absence is an OPEN return rather than a discontinuity.
  ],
)
