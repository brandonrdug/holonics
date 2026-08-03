#let embodied-optical-receiver-atlas = (
  key: "definition:embodied-optical-receiver-atlas",
  kind: [Definition],
  title: [Embodied optical receiver atlas and shared-axis deformation],
  status: [Project definition using standard surface, optical-transfer, and joint-image geometry],
  depends: (
    "definition:co-present-receiver-atlas",
    "definition:receiver-incidence-census",
  ),
  claim: [
    An *embodied optical receiver atlas* begins with one contemporary body
    state
    $
      B=(M_B,g_B,partial M_B,ell_B),
    $
    where $M_B$ is a surface incidence complex, $g_B$ its local metric or
    rest-length data, $partial M_B$ its retained boundary, and $ell_B$ the
    admitted loading or realization law. A realized surface $x_B$ determines
    situated optical axes $a_i(B)$, typically through local surface normals,
    eye posture, or another declared section of the body's optical bundle.

    Each participating eye, ommatidium, pixel, or other optical receiver has
    a typed factorization
    $
      q_i^B
      =
      S_i^B compose H_i^B compose A_i^B,
    $
    where $A_i^B$ is its aperture and axis-relative admission,
    $H_i^B$ its lawful optical propagation, and $S_i^B$ its finite sampling
    face. Their contemporary optical field is the actual joint image
    $
      cal(J)_B
      =
      "im"((q_i^B)_(i in I_B)),
    $
    not the Cartesian product of independently selectable eye values.

    A body event $E:B arrow.r B^+$ may change the surface, metric, posture,
    axes, apertures, and overlap maps together. Thus it transports one
    receiver atlas to another:
    $
      E_*:
      (B,(q_i^B)_i,cal(J)_B)
      arrow.r
      (B^+,(q_i^(B^+))_i,cal(J)_(B^+)).
    $
    No member is an external camera exempt from that event.

    If the body carries a bilateral involution $iota_B$, paired receivers are
    related by its supplied transport. They are not required to have equal
    faces, equal histories, or identical optics. For a triangulated realized
    surface, the exact discrete Gaussian curvature at an interior vertex is
    $
      K_v=2 pi-sum_(tau in cal(T)(v)) alpha_(tau,v).
    $
    In the equilateral flat case this becomes
    $
      K_v=(6-"deg"(v)) pi/3.
    $
    Hence a six-valent triangular neighborhood has a hexagonal dual cell and
    zero angle defect, while metric deformation or a different valence bends
    the available receiver axes.
  ],
  proof: none,
  boundary: [
    Incidence alone does not determine a realized surface: metric,
    boundary, and loading data remain necessary. A shared body couples the
    receiver family without making all faces equal or proving a particular
    neural integration law. Lens, cornea, retina, and tissue are not
    literally wave nodes or antinodes; such language becomes exact only
    after a wave-response model identifies its zeros and extrema. The
    definition is not restricted to biology, but biological claims retain
    their experimental jurisdiction.
  ],
)
