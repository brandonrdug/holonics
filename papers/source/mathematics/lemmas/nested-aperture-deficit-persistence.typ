#let nested-aperture-deficit-persistence = (
  key: "lemma:nested-aperture-deficit-persistence",
  kind: [Lemma],
  title: [A negative compact witness survives every larger support aperture],
  status: [Exact consequence of compatible nested Hermitian forms],
  depends: ("definition:parametric-weil-bundle",),
  claim: [
    Let $cal(T)_R subset.eq cal(T)_(R')$ for $R<=R'$ be nested test-current
    fibers, and suppose their Hermitian responses are compatible:
    $
      q_(R')|_(cal(T)_R)=q_R.
    $
    Define the spectral floor
    $
      mu_R
      =
      inf_(0 != f in cal(T)_R)
      q_R(f)/norm(f)^2.
    $
    Then
    $
      mu_(R')<=mu_R.
    $

    More strongly, if one $f in cal(T)_R$ satisfies $q_R(f)<0$, and numbers
    $e_(R')>=0$ obey
    $
      q_(R')(g)>=-e_(R') norm(g)^2
      quad "for every" g in cal(T)_(R'),
    $
    then every later aperture satisfies
    $
      e_(R')
      >=
      -q_R(f)/norm(f)^2
      >0.
    $
    Consequently no lower-error bound indexed only by enlargement of a
    compatible support aperture can converge to zero after a negative
    compact witness has entered.
  ],
  proof: [
    The infimum defining $mu_(R')$ is taken over a set containing the set
    defining $mu_R$, so $mu_(R')<=mu_R$.  Compatibility carries the same
    witness and the same response into every later fiber.  Substituting that
    witness into the assumed lower bound gives
    $
      q_R(f)=q_(R')(f)>=-e_(R')norm(f)^2,
    $
    which rearranges to the displayed positive lower bound for $e_(R')$.
  ],
  boundary: [
    This is a statement about genuine nested aperture growth.  A
    finite-rank resolution sequence inside one fixed receiver is a different
    axis and may have a vanishing discretization tail.  The lemma neither
    asserts that a negative witness exists nor signs the completed Weil
    response.
  ],
)
