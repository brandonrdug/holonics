#let receiver-relative-second-order-calculus = (
  key: "theorem:receiver-relative-second-order-calculus",
  kind: [Theorem],
  title: [Joint incidence and curvature are the symmetric and ordered second faces],
  status: [Exact finite-square identities with the standard smooth curvature limit],
  depends: (
    "definition:receiver-configuration-calculus",
    "theorem:receiver-stratified-fundamental-theorem",
    "theorem:receiver-discriminant-curvature",
  ),
  claim: [
    Consider an admitted receiver square with configurations
    $S_(00),S_(10),S_(01),S_(11)$ carried into one comparison fiber.  Its
    joint second difference is
    $
      H_(i j) S
      =
      S_(11)-S_(10)-S_(01)+S_(00).
      quad "(JOINT INCIDENCE)"
    $
    This is the exact inclusion--exclusion coefficient of the feature which
    appears only when receiver changes $i$ and $j$ are co-present.

    If the two paths carry ordered transports
    $
      U_(00,10),U_(10,11),U_(00,01),U_(01,11),
    $
    their curvature residual is
    $
      cal(R)_(i j)
      =
      U_(10,11) U_(00,10)
      -
      U_(01,11) U_(00,01).
      quad "(ORDERED RESIDUAL)"
    $
    With invertible transports this residual may equivalently be represented
    by returned holonomy.  In the smooth limit it becomes
    $
      R(V_i,V_j)
      =
      [nabla_(V_i),nabla_(V_j)]
      -nabla_([V_i,V_j]).
      quad "(CURVATURE)"
    $

    The two second faces are logically independent.  A commuting square may
    have $cal(R)_(i j)=0$ while $H_(i j) S != 0$: joint interaction can be
    present even when its two orders agree.  Conversely, nonzero curvature
    records order-dependent transport and need not create a new scalar
    population.

    If $Delta_p$ is a declared arithmetic place-admission or valuation-layer
    difference and $nabla_(V_i)$ is an admissible receiver derivative, then
    $
      cal(C)_(i,p)
      =
      nabla_(V_i) Delta_p-Delta_p nabla_(V_i)
      quad "(MIXED CURVATURE)"
    $
    measures whether changing the receiver transports the arithmetic cut.
    It is the precise comparison between “move the perspective, then admit
    the prime face” and “admit the prime face, then move the perspective.”
  ],
  proof: [
    Expanding the four values of a finite bivariate difference gives
    ("JOINT INCIDENCE") by inclusion--exclusion.  Subtracting the two
    composites around the square gives ("ORDERED RESIDUAL") by definition.
    The infinitesimal commutator formula is the standard curvature of a
    connection after correction by the bracket of the varying vector fields.
    The examples $S_(a b)=a b$ and two identity transports give
    $H_(i j) S=1$ but zero ordered residual, proving that neither second face
    can replace the other.  The mixed formula is the same commutator with
    one continuous receiver direction and one discrete arithmetic direction.
  ],
  boundary: [
    A receiver “partial” is undefined when the incidence base does not admit
    its independent tangent.  In that case one must use an actual path or
    correspondence, not insert a false coordinate direction.  The mixed
    curvature is relative to a specified arithmetic cut and comparison
    transport; it is not a universal statistic of a prime.
  ],
)
