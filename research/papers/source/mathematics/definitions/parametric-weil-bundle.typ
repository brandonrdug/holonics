#let parametric-weil-bundle = (
  key: "definition:parametric-weil-bundle",
  kind: [Definition],
  title: [Parametric Weil-response bundle],
  status: [Project definition; incidence-relative positivity geometry],
  depends: (
    "definition:situated-event-correspondence",
    "definition:three-frame-counting-correspondence",
    "lemma:mellin-return-seam",
  ),
  claim: [
    Let
    $
      tau:E arrow.r
      B_"arith" times B_"arch" times B_"recv"
    $
    be the incidence object of three local counting frames: arithmetic
    place/valuation, archimedean Fourier--Poisson--Mellin transport, and the
    receiving test/aperture/normalization frame.  Let
    $pi:cal(H) arrow.r E$ be a bundle whose fiber $cal(H)_e$ consists of the
    test currents admitted at the actual incidence $e$.
    Each fiber carries a Hermitian response
    $
      W_e:cal(H)_e times cal(H)_e arrow.r CC.
    $
    Its evaluated quadratic response and nonnegative cone are
    $
      q_e(f)=W_e(f,f),
      quad
      cal(C)_e={f:q_e(f)>=0}.
    $
    An admitted incidence comparison $alpha:e arrow.r e'$ may carry a
    partial transport
    $
      T_alpha:D_alpha arrow.r cal(H)_(e'),
      quad
      D_alpha subset cal(H)_e.
    $
    For $f,g in D_alpha$, its response defect is
    $
      cal(K)_alpha(f,g)
      =
      W_(e')(T_alpha f,T_alpha g)
      -W_e(f,g).
    $
    When the fibers are anchored by maps
    $iota_e:cal(H)_e arrow.r cal(H)_W$ into the classical
    admissible Weil test space, receiver exactness requires the transition
    to represent the same completed test occurrence:
    $
      iota_(e') T_alpha=iota_e.
    $

    A one-parameter chart
    $
      gamma:J arrow.r E
    $
    selects a receiver-readable section through the incidence network.  It
    induces the familiar displayed family
    $
      q_gamma(t)=W_(gamma(t))(f(t),f(t)),
    $
    but $t$ orders only that chosen section.  The three projections
    $tau_i gamma$ retain their own local lineages and need not be
    synchronized beyond the incidences selected by $gamma$.
  ],
  proof: none,
  boundary: [
    The inequality $q_e(f)>=0$ is an evaluation of a Hermitian form on
    one transported direction, not an observer-free scalar property.
    Positivity of the form means that every admitted direction in the fiber
    is nonnegative. A chart which merely selects some different positive
    direction does not establish that statement. The bundle, connection,
    anchors, and transition laws must be constructed; naming a parameter
    does not supply them.

    The product of the three lineage bases is an addressing space, not an
    enlarged simultaneous state field.  Only incidences in $E$ are
    co-present.  A common scalar parameter may be useful for differentiation
    after a section is selected, but it may not silently become a master
    chronology for prime admission, Fourier/Mellin scale, support, and the
    receiving current.
  ],
)
