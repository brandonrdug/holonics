#let glossary() = [
= Geometric algebra lexicon

The terms below name relationships among whole families. They are not aliases for isolated output
values.

#table(
  columns: (1.15fr, 2.75fr),
  inset: 7pt,
  stroke: 0.5pt + luma(200),
  [*Term*], [*Working meaning*],
  [Characteristic map], [The polynomial map sending a matrix to the coefficients of its characteristic polynomial.],
  [Fiber], [The complete source family mapped to one declared receiver value.],
  [Stratum], [A region on which a declared structural type remains constant; its boundary records a qualitative change.],
  [Reparameterization], [An invertible change of variables used to expose relations hidden in the original coordinates.],
  [Orbit], [Every point reachable from one source by a declared transformation group.],
  [Tangent direction], [A first-order motion satisfying the linearized constraints of a space or fiber.],
  [Singular point], [A point where the defining constraints lose rank and the local geometry is not regular.],
  [Conjugation], [The recharting $M mapsto P M P^(-1)$ by an invertible change of basis $P$.],
  [Invariant], [A quantity or structure preserved by a declared transformation family.],
  [Quotient], [A receiver that deliberately identifies sources under a declared equivalence.],
  [Graph chart], [A presentation of matrix entries as weighted loops and directed edges; useful, but dependent on the chosen basis.],
  [Computational witness], [A reproducible finite instance of a relation already stated at its proper scope.],
)

#v(12pt)
#block(
  width: 100%,
  inset: 10pt,
  radius: 4pt,
  fill: rgb("#fff6dd"),
  stroke: 0.7pt + rgb("#9a6b12"),
)[
  *Translation discipline.* Replace “what answer does this matrix give?” with “what source family
  maps to this receiver, where does the fiber change type, and which transports remain inside it?”
]
]
