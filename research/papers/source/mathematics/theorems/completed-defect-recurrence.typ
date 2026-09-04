#let completed-defect-recurrence = (
  key: "theorem:completed-defect-recurrence",
  kind: [Theorem],
  title: [Receiver-covariant completed-defect recurrence],
  status: [Exact laboratory synthesis],
  depends: (
    "theorem:euler-successor-geometry",
    "theorem:euler-metric-recurrence",
  ),
  claim: [
    Let
    $
      Sigma_S(f)
      =op("Tr")(Theta_S(f)P_S Theta_S(f)^*)
    $
    be a defined trace-class Sonin return, let $Q_S(f)$ be the completed
    explicit-formula response with the finite places in $S$, and set
    $
      D_S(f)=Q_S(f)-Sigma_S(f).
    $
    For $S'=S union {p}$ define the aperture connection
    $
      kappa_(S,p)(f)
      =Sigma_(S')(f)-Sigma_S(f).
    $
    If
    $
      W_p(h)=log p sum_(m>=1)
      (h(p^m)+p^(-m)h(p^(-m)))
    $
    for $h=f ast f^sharp$, then
    $
      D_(S')(f)
      =D_S(f)-W_p(h)-kappa_(S,p)(f).
    $
    In the predecessor chart,
    $
      kappa_(S,p)(f)
      =op("Tr")(Theta_S(f)(Pi_p-P_S)Theta_S(f)^*).
    $
  ],
  proof: [
    The explicit formula changes by
    $Q_(S')-Q_S=-W_p$. Similarity invariance of the trace and the transported
    successor projection give
    $Sigma_(S')-Sigma_S=kappa_(S,p)$. Subtracting these two exact differences
    yields the recurrence.
  ],
  boundary: [
    The recurrence has no sign by itself. In particular, the off-diagonal
    aperture turn $Pi_p-P_S$ is not positive in the predecessor metric.
    Proving nonnegativity of the completed successor defect for the full
    admissible family is the RH-bearing open step, not a consequence of this
    identity.
  ],
)
