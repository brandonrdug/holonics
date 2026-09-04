#let situated-formulation-family = (
  key: "definition:situated-formulation-family",
  kind: [Definition],
  title: [Situated formulation family],
  status: [Project definition; exact carrier for parameterized formulations],
  depends: (
    "definition:receiver",
    "definition:phase",
  ),
  claim: [
    Let $cal(C)$ be a category of admissible spaces and maps, let $B$ be a
    parameter base, and work in the slice $cal(C)/B$. A *situated formulation
    family* over $B$ is a decorated object
    $
      cal(F)_B
      =
      (u_cal(F):U_cal(F) arrow.r B,
       L_cal(F), Delta_cal(F), cal(R)_cal(F),
       c_cal(F), pi_cal(F)).
    $
    The total space $U_cal(F)$ retains the parameters and internal states
    admitted by the typed formulation law $L_cal(F)$. The typed discriminant
    $Delta_cal(F)$ records where a required branch, rank, convergence,
    operation, or receiver law fails to continue. The receiver family
    $
      cal(R)_cal(F)
      =
      {q_(rho,cal(F)):U_cal(F) arrow.r Y_rho}_rho
    $
    presents selected faces. The optional cost or metric record $c_cal(F)$ and
    source testimony $pi_cal(F)$ are decorations, not the identity of the
    family.
  ],
  proof: none,
  boundary: [
    A specialization must name $cal(C)$, the parameter base, the complete
    domain of each law, and every receiver used in a comparison. Equality
    after one receiver does not identify formulation families, their internal
    states, or their discriminants.
  ],
)
