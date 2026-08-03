#let polyhedral-face-word-nonreconstruction = (
  key: "corollary:polyhedral-face-word-nonreconstruction",
  kind: [Corollary],
  title: [An f-vector, skeleton, and convex hull do not determine the carried face word],
  status: [Exact consequence of the classical Kepler--Poinsot incidence data],
  depends: (
    "lemma:receiver-nonreconstruction",
    "definition:receiver-incidence-census",
  ),
  claim: [
    The great dodecahedron and small stellated dodecahedron both have
    $
      (f_0,f_1,f_2)=(12,30,12),
    $
    icosahedral skeletons, and regular-icosahedral convex hulls. Nevertheless
    the great dodecahedron carries twelve intersecting pentagonal faces with
    Schlaefli symbol ${5,5/2}$, while the small stellated dodecahedron carries
    twelve pentagrammic faces with symbol ${5/2,5}$. They are dual rather
    than identical.

    Therefore the tuple
    $
      ("f-vector","abstract skeleton","convex hull")
    $
    is not a conservative receiver for face traversal, winding, intersection
    structure, duality, or interior. Those data owe the carried face word and
    its incidence, not merely the visible hull.
  ],
  proof: [
    The shared census and icosahedral skeleton/hull are the standard
    Kepler--Poinsot data. Their distinct Schlaefli symbols exchange face and
    vertex-figure roles; pentagonal and pentagrammic face traversals are not
    the same incidence. Thus two nonidentical polyhedral constructions have
    equal values under the stated tuple receiver, and receiver
    non-reconstruction applies.
  ],
  boundary: [
    This result does not identify all stellations or all self-intersecting
    polyhedra. It shows exactly which coarse receiver fails. A richer marked
    incidence complex may distinguish the two without reconstructing any
    unrelated metric or material law.
  ],
)
