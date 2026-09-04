#let theta-crossing-layer-indefiniteness = (
  key: "lemma:theta-crossing-layer-indefiniteness",
  kind: [Lemma],
  title: [Every isolated theta crossing layer is indefinite],
  status: [Exact obstruction to layerwise Gram factorization],
  depends: (
    "theorem:completed-theta-phase-current-bridge",
    "theorem:theta-positive-execution-lift",
  ),
  claim: [
    For $y>0$, remove the positive constant from one fixed layer of the theta
    phase current and put
    $
      K_y(a,b)
      =
      bold(1)_(abs((a+b)/2)<=y)
      Phi(y+(a-b)/2)
      Phi(y-(a-b)/2).
      quad "(CROSSING LAYER)"
    $
    Then $K_y$ is indefinite on the ambient coordinate receiver space.
    Indeed, for every $s>y$, its restriction to the opposed receivers
    ${s,-s}$ is
    $
      mat(
        0, k_(y,s);
        k_(y,s), 0
      ),
      quad
      k_(y,s)=Phi(y+s)Phi(y-s)>0,
    $
    with eigenvalues $plus.minus k_(y,s)$.

    Hence the phase current cannot be proved positive by treating each
    $y$-layer as an independent Gram constituent and then integrating those
    constituents. The ordered accumulation in $y$ must carry an open
    off-diagonal crossing until later diagonal storage can participate.

    The first accumulated opposed-receiver face makes this explicit. Up to
    the common positive factor $c_Phi^2/2$, put
    $
      S(s)=integral_s^infinity y Phi(y)^2 dif y,
      quad
      C(s)=integral_0^infinity
      y Phi(y+s)Phi(y-s)dif y.
    $
    Then
    $
      mat(
        cal(P)_0(s,s), cal(P)_0(s,-s);
        cal(P)_0(-s,s), cal(P)_0(-s,-s)
      )
      =
      frac(c_Phi^2,2)
      mat(
        S(s), C(s);
        C(s), S(s)
      ),
    $
    whose symmetric and antisymmetric responses are proportional to
    $S(s)+C(s)$ and $S(s)-C(s)$. Thus the first ambient bipolar closure law
    is the exact domination $S(s)>=C(s)$.
  ],
  proof: [
    If $s>y$, then the diagonal activation conditions are
    $
      abs((s+s)/2)=s>y,
      quad
      abs((-s-s)/2)=s>y,
    $
    so both diagonal entries vanish. For the opposed entry,
    $
      (s+(-s))/2=0,
      quad
      (s-(-s))/2=s,
    $
    and positivity of the even Riemann theta kernel gives
    $
      K_y(s,-s)=Phi(y+s)Phi(y-s)>0.
    $
    The displayed matrix therefore has one positive and one negative
    eigenvalue.

    Substitution of $(a,b)=(s,s)$ and $(s,-s)$ into the definition of
    $cal(P)_0$ gives $S(s)$ and $C(s)$ respectively. Symmetry supplies the
    other two entries, and diagonalization in the vectors $(1,1)$ and
    $(1,-1)$ gives the final responses.
  ],
  boundary: [
    The opposed-point matrix concerns positivity on the full coordinate
    receiver space, which is stronger than the RH-equivalent requirement on
    the bilateral-exponential span. It is therefore a diagnostic of the
    stronger Weyl-kernel route, not a new equivalent criterion for RH.

    The lemma does not show that the integrated phase current is indefinite.
    It shows why a local-in-$y$, memoryless, one-layer-at-a-time executor
    cannot supply its positive factorization. Any successful source
    executor must mix crossing layers, or work directly after the
    bilateral-exponential pullback.
  ],
)
