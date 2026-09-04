#let receiver-configuration-calculus = (
  key: "definition:receiver-configuration-calculus",
  kind: [Definition],
  title: [Receiver-relative configuration calculus],
  status: [Project definition built from standard incidence, stratification, and implicit-function geometry],
  depends: (
    "definition:co-present-receiver-atlas",
    "definition:receiver-topology-atlas",
    "definition:typed-axis-unit-ratio",
  ),
  claim: [
    Let the actual co-presence of $m$ receiver lineages be an incidence object
    $
      E arrow.r B_1 times dots.c times B_m,
    $
    not the full Cartesian product.  Let $pi_X:X arrow.r E$ be the family of
    contemporary configurations, with fiber $X_e$, and let
    $
      q_e:X_e arrow.r product_(i=1)^m Y_(i,e)
      quad "(JOINT RECEIVER)"
    $
    be the joint receiver map.  Its image contains only faces which arise
    together from one actual configuration.

    A finite family of typed comparison laws
    $
      b_a(e,q_e(x)) bowtie_a 0,
      quad a in A,
    $
    defines the receiver-relative accessible region
    $
      Omega_e
      =
      {x in X_e:
        b_a(e,q_e(x)) bowtie_a 0
        " for every active "a}.
      quad "(ACCESSIBLE REGION)"
    $
    Equalities $b_a=0$ are its oriented boundary sheets.  Their sign vectors
    stratify the total configuration ecology
    $
      cal(X)={(e,x):e in E, x in X_e}.
    $
    If $A_(e,x)={a:b_a(e,q_e(x))=0}$, the receiver discriminant is
    $
      Delta
      =
      {(e,x):
        "rank" D_x(b_a circle q_e)_(a in A_(e,x))
        < abs(A_(e,x))}.
      quad "(DISCRIMINANT)"
    $
    Thus a smooth chamber is a region where the active law class and the
    transverse boundary incidence continue.  A seam is a crossing of a
    boundary or of $Delta$; it is not inferred from a plotted kink alone.

    A “partial change of receiver $i$” at $e$ exists only when there is an
    admissible tangent $V_i in T_e E$ satisfying
    $
      D tau_j(V_i)=0
      quad "for every "j != i.
      quad "(RELATIVE PARTIAL)"
    $
    Entanglement may make this subspace empty.  If an active square boundary
    law $B(e,x)=0$ has an admitted horizontal fiber $H_(e,x)$ for which
    $(D_x B)|_H$ is invertible, its continuation along $V_i$ is determined by
    $
      D_x B nabla_(V_i) x=-(D_e B)[V_i].
      quad "(BOUNDARY CONTINUATION)"
    $

    On an affine chart with four distinct marks, the projective Swing
    $
      chi(A,B;C,D)
      =
      frac((A-C)(B-D),(A-D)(B-C))
    $
    has the exact logarithmic differential
    $
      frac(dif chi,chi)
      =
      frac(dif A-dif C,A-C)
      +frac(dif B-dif D,B-D)
      -frac(dif A-dif D,A-D)
      -frac(dif B-dif C,B-C).
      quad "(SWING DIFFERENTIAL)"
    $
    This covector annihilates tangents to the common projective rechart
    orbit.  It therefore measures relative four-member motion, not motion
    against an absolute coordinate frame.
  ],
  proof: none,
  boundary: [
    The comparison laws, incidence object, admissible tangents, and transport
    are supplied by the ecology being studied.  The definition does not
    assert one ambient space, one master clock, or independently movable
    receivers.  A singular discriminant point can require a correspondence,
    blow-up, or discrete continuation rather than a derivative.  The Swing
    differential is valid only away from coincident marks and the chosen
    quotient pole; the undivided projective pair remains the complete carrier
    at a chart boundary.
  ],
)
