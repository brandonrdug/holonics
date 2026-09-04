#let positive-covariant-monodromy-seam = (
  key: "theorem:positive-covariant-monodromy-seam",
  kind: [Theorem],
  title: [A positive covariant monodromy law fixes the critical seam],
  status: [Exact transport theorem with an explicitly conditional RH consequence],
  depends: (
    "definition:parametric-weil-bundle",
    "lemma:critical-seam-conjugacy",
    "lemma:reciprocal-monodromy-counterexample",
  ),
  claim: [
    Let $cal(E) arrow.r X$ be a complex vector or Hilbert bundle. Suppose each
    fiber $cal(E)_x$ carries an independently constructed positive-definite
    Hermitian form $H_x$, and every admitted path $gamma:x arrow.r y$ carries
    an invertible transport
    $
      T_gamma:cal(E)_x arrow.r cal(E)_y
    $
    satisfying
    $
      H_y (T_gamma v,T_gamma w)=H_x (v,w).
      quad "(COV)"
    $
    Then the holonomy $M_gamma=T_gamma$ of every closed admitted path based at
    $x$ is $H_x$-unitary and
    $
      op("spec")(M_gamma) subset {lambda in CC:abs(lambda)=1}.
      quad "(UNIT)"
    $

    In particular, let $U_t=e^(t A)$ be a strongly continuous returned flow
    satisfying (COV) in one fiber for every real $t$. Every eigenvalue $z$ of
    $A$ is purely imaginary. If an independently constructed trace
    correspondence identifies the complete nontrivial zero spectrum of
    $xi(s)$ with the point spectrum of
    $
      Theta=1/2 I+A,
    $
    including multiplicity and every arithmetic and archimedean trace term,
    then every nontrivial zero has real part $1/2$ and RH follows.
  ],
  proof: [
    For a closed path, (COV) gives
    $
      M_gamma^* H_x M_gamma=H_x.
    $
    Conjugating by the positive square root $H_x^(1/2)$ turns $M_gamma$ into
    an ordinary unitary operator, whose spectrum lies on the unit circle.

    If $A v=z v$ with $v!=0$, then $U_t v=e^(t z)v$. Norm preservation gives
    $
      H(v,v)
      =H(U_t v,U_t v)
      =e^(2t op("Re")(z))H(v,v)
    $
    for every real $t$. Positivity of $H(v,v)$ forces
    $op("Re")(z)=0$. Under the stated independent spectral correspondence,
    every nontrivial zero is $rho=1/2+z$ with $op("Re")(z)=0$.
  ],
  boundary: [
    The theorem does not construct the bundle, positive metric, returned
    flow, generator, or trace correspondence. Defining $Theta$ from the known
    zero set would be circular. In the current semilocal programme the
    archimedean Sonin/prolate amplitude supplies one positive-semidefinite
    base form. To use it as the displayed metric one must additionally prove
    either nondegeneracy or invariance of its radical and then work on the
    positive quotient, while showing that no zero mode is discarded there.
    Its receiver-covariant continuation through finite-place and support
    growth, together with a trace identity identifying the generator's
    spectrum with the completed zeros, remains the proof-bearing object.
  ],
)
