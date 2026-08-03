#let hexagonal-receiver-census = (
  key: "theorem:hexagonal-receiver-census",
  kind: [Theorem],
  title: [Six is the first two-three polygonal hinge; projection decides which six is seen],
  status: [Exact elementary Euclidean and polyhedral theorem],
  depends: (
    "definition:receiver-incidence-census",
  ),
  claim: [
    Let $H_a$ be a regular hexagon of side length $a>0$.

    First, among regular polygonal cycles, six is the least side population
    whose rotation group contains both an order-two and an order-three
    rotation. Equivalently,
    $
      2 divides n
      " and "
      3 divides n
      "if and only if"
      6 divides n.
    $
    The center-to-vertex decomposition of $H_a$ consists of six equilateral
    triangles. It may be grouped into two three-sector halves or three
    two-sector rhombi while retaining the same exterior hexagon.

    Second, a line segment joining points in the relative interiors of a
    pair of opposite edges divides $H_a$ into two pentagons. When the points
    are the opposite edge midpoints, the two pentagons are congruent and
    each has cyclic side-length word
    $
      (a/2,a,a,a/2,sqrt(3)a).
    $
    A line through opposite vertices instead gives two quadrilaterals; the
    two cuts are different receiver constructions.

    Third, for the cube $C=[-1,1]^3$, the plane
    $
      x+y+z=0
    $
    is perpendicular to a body diagonal and cuts $C$ in the regular
    hexagon whose vertices are the permutations of $(1,-1,0)$. Orthogonal
    projection along that body diagonal has receiver census
    $
      8 " source vertices"
      arrow.r
      7 " distinct image coordinates"
      arrow.r
      6 " silhouette corners".
    $
    The two opposite body-diagonal vertices share the central image fiber;
    the other six form the regular hexagonal silhouette.

    Fourth, a regular pentagonal pyramid received along its height has
    $
      6 " source vertices"
      arrow.r
      6 " distinct image coordinates"
      arrow.r
      5 " silhouette corners".
    $
    Its apex is the interior received point at which the five projected
    lateral edges are materially incident. It is one source vertex of
    valence five, not five accidental crossings. The cube and pentagonal
    pyramid can therefore present related center-and-cycle drawings while
    carrying nonidentical source fibers and incidences.
  ],
  proof: [
    The rotation by $2 pi/n$ generates the cyclic rotation group of a
    regular $n$-gon. It contains elements of orders two and three exactly
    when both orders divide $n$, whose least common multiple is six.
    Connecting the center of a regular hexagon to its vertices gives six
    equilateral sectors; grouping them proves the two stated decompositions.

    A chord with endpoints in the interiors of opposite edges leaves three
    original vertices on each boundary arc. Adding the two chord endpoints
    gives five boundary vertices on each side. For midpoint endpoints, the
    four inherited boundary lengths are $a/2,a,a,a/2$, and the distance
    between opposite edge midpoints is twice the apothem, $sqrt(3)a$.

    The cube section has the six stated vertices. Consecutive differences
    have equal norm and the section has a sixfold cyclic ordering, so it is
    regular. Under body-diagonal projection the vertices
    $(1,1,1)$ and $(-1,-1,-1)$ both map to the center; direct substitution
    shows that the remaining six have equal received radius and consecutive
    chord length. For the pentagonal pyramid, height projection fixes the
    five base vertices and sends the apex to the base center, giving the
    final census and incidence statement.
  ],
  boundary: [
    A regular hexagon is neither intrinsically a cube nor the first polygon
    which can be subdivided. The exact firstness concerns simultaneous
    order-two and order-three cyclic symmetry. A cube-like volume is one
    section or projection face with a declared receiver. Visible edge,
    visible vertex, source vertex, and crossing counts must not be
    interchanged.
  ],
)
