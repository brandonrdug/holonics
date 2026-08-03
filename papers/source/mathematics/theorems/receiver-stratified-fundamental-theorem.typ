#let receiver-stratified-fundamental-theorem = (
  key: "theorem:receiver-stratified-fundamental-theorem",
  kind: [Theorem],
  title: [Receiver-stratified fundamental theorem of transport],
  status: [Exact piecewise-covariant telescoping identity under the stated transport and seam hypotheses],
  depends: (
    "definition:receiver-configuration-calculus",
    "theorem:transported-fundamental-theorem",
  ),
  claim: [
    Let $gamma:[0,1] arrow.r E$ be an oriented receiver path meeting finitely
    many seams
    $
      0<t_1<dots.c<t_r<1
    $
    and remaining in smooth transport chambers between them.  Let
    $frak(S)_t$ be a section of a chain or module bundle along $gamma$, let
    $cal(P)_(u arrow.r v)$ be its chamber transport, and let
    $J_k$ be the declared seam identification from the left fiber to the
    right fiber.  Define the exact jump
    $
      Delta_k frak(S)
      =
      frak(S)_(t_k^+)-J_k frak(S)_(t_k^-).
    $
    Then, in the final fiber,
    $
      frak(S)_1-cal(P)_(0 arrow.r 1) frak(S)_0
      =
      integral_0^1
      cal(P)_(t arrow.r 1)
      nabla_(dot(gamma)(t)) frak(S)_t
      dif t
      +
      sum_(k=1)^r
      cal(P)_(t_k^+ arrow.r 1)
      Delta_k frak(S).
      quad "(STRATIFIED FTC)"
    $
    The integral is taken chamber by chamber.  When the path is wholly
    discrete, it is absent and the jump sum is the exact telescoping
    successor law.  When no seam is crossed, the formula reduces to the
    covariant fundamental theorem.
  ],
  proof: [
    Apply the transported fundamental theorem separately on every closed
    chamber segment.  Transport each resulting equality into the final
    fiber.  Adjacent one-sided boundary terms cancel after insertion of the
    declared seam map $J_k$; the uncancelled difference is precisely
    $Delta_k frak(S)$.  Summing the finite segment identities leaves the two
    endpoint terms, the transported chamber integrals, and the transported
    jumps displayed above.
  ],
  boundary: [
    The theorem does not manufacture a seam identification when the ecology
    supplies none.  Accumulating infinitely many seams requires a convergence
    theorem.  A scalar count has a distributional derivative supported on
    wall crossings, but that count forgets which chains crossed and how.
    Applied to the graded arithmetic accessibility current, the theorem is
    exact only after its prime aperture, occurrence chain, and receiver
    boundary are fixed.
  ],
)
