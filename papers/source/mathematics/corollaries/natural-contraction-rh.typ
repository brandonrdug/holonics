#let natural-contraction-rh = (
  key: "corollary:natural-contraction-rh",
  kind: [Conditional corollary],
  title: [A complete natural contraction of the zeta amplitudes implies RH],
  status: [Exact conditional consequence; same RH sign wall in coherent form],
  depends: (
    "theorem:natural-contraction-feasibility",
    "theorem:semilocal-successor-defect-contraction",
  ),
  claim: [
    Suppose the completed zeta test currents, prime/support apertures, and
    lawful receiver recharts form an exhaustive index category $cal(J)$.
    Suppose the existing predecessor, Euler, and aperture amplitudes assemble
    into the natural transformations $X$ and $Y$ of the natural-contraction
    theorem, with
    $
      Q_W(f)=norm(X_j f)^2-norm(Y_j f)^2
    $
    for every represented completed Weil current. If
    $cal(C)(X,Y)$ is nonempty, then $Q_W(f)>=0$ for every admissible test
    current and the Riemann Hypothesis holds.
  ],
  proof: [
    A natural contraction gives nonnegativity of every represented response
    by the defect identity of the preceding theorem. Exhaustiveness covers the
    complete Weil test space. Weil's positivity criterion is equivalent to
    RH, so RH follows.
  ],
  boundary: [
    This is not a new positivity carrier under another name. It identifies
    the exact coherence which the already-open contraction must satisfy
    across perspectives, prime additions, and support growth. Proving that
    the candidate feasibility set is nonempty from the completed arithmetic relation
    remains the proof-bearing obligation.
  ],
)
