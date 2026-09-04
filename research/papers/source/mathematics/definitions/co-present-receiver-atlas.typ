#let co-present-receiver-atlas = (
  key: "definition:co-present-receiver-atlas",
  kind: [Definition],
  title: [Co-present receiver atlas, joint face, and receiver grain],
  status: [Project definition using standard image, fiber-product, and partition geometry],
  depends: (
    "definition:situated-event-correspondence",
    "definition:receiver",
    "definition:typed-axis-unit-ratio",
  ),
  claim: [
    Fix one actual event incidence $e$ and its participating construction
    $X_e$.  Let
    $
      q_i:X_e arrow.r Y_i,
      quad i in I_e,
    $
    be its contemporary receiver maps.  The *joint receiver face* is the
    actual image
    $
      cal(J)_e
      =
      "im"(q_e),
      quad
      q_e=(q_i)_(i in I_e):
      X_e arrow.r product_(i in I_e)Y_i.
      quad "(JOINT FACE)"
    $
    Thus $cal(J)_e$ contains only tuples which arise from one occurrence of
    $X_e$; it is not completed to the Cartesian product of independently
    selectable receiver values.  The family is *entangled at* $e$ whenever
    this image does not factor as the product of the individual images.

    When receiver overlaps carry partial transition maps
    $
      g_(i j):Y_i|_(U_(i j)) arrow.r Y_j|_(U_(j i)),
    $
    the compatible interior presented by the atlas is the fibered relation
    $
      "Int"(cal(J)_e)
      =
      { (y_i) in cal(J)_e :
         g_(i j)(y_i)=y_j
         " on every admitted overlap" }.
      quad "(COMPATIBLE INTERIOR)"
    $
    It is an available interior of the contemporary faces, not an ambient
    volume assumed before them.

    A finite *receiver grain* $cal(P)_i$ is a partition or cover of the
    distinctions in $Y_i$.  Its center is a supplied pivot section $c_i$,
    not an absolute origin, and its aspect is a typed comparison of two
    receiver axes.  Two occurrences are indistinguishable at this grain when
    their faces occupy one common aperture and retain one declared
    consequence signature.  A difference is *tolerated* precisely while
    every realization in that unresolved fiber preserves the currently
    declared consequence and overlap relations.

    One event successor is supplied jointly:
    $
      cal(J)_e^+
      =
      Lambda_e(
        cal(J)_e;
        (q_i,cal(P)_i,c_i)_(i in I_e)
      ).
      quad "(JOINT SUCCESSOR)"
    $
    Receiver-local continuation may be evaluated independently after this
    co-present relation is formed.  Evaluation order across the finite faces
    is not event chronology.
  ],
  proof: none,
  boundary: [
    The index $I_e$ contains receivers participating in this event, not every
    historical or potential receiver.  Finite grain limits what one face can
    distinguish; it does not determine what exists. Pairwise overlap
    agreement need not supply a compatible higher interior unless the
    transition domains and cocycle or wider descent conditions are also
    satisfied. A stable nonidentity return may be curvature rather than
    error.
  ],
)
