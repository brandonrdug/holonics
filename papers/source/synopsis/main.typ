#import "../holonics/schema.typ": render-sequence
#import "../holonics/registry.typ": entries, validate-registry
#import "../holonics/foundations.typ": foundations
#import "../holonics/logic-category.typ": logic-category
#import "../holonics/algorithms.typ": algorithms
#import "../holonics/algebra-combinatorics.typ": algebra-combinatorics
#import "../holonics/geometry-calculus.typ": geometry-calculus
#import "../holonics/topology-analysis-dynamics.typ": topology-analysis-dynamics
#import "../holonics/manifold-knot-geometry.typ": manifold-knot-geometry
#import "../holonics/arithmetic-analysis.typ": arithmetic-analysis
#import "../holonics/algebraic-geometry.typ": algebraic-geometry
#import "../holonics/transcendence-special-functions.typ": transcendence-special-functions
#import "../holonics/computation-information.typ": computation-information
#import "../holonics/mathematical-physics.typ": mathematical-physics
#import "../holonics/rh-routes.typ": rh-routes
#import "../holonics/counterexamples.typ": counterexamples

#validate-registry()

#set page(
  paper: "us-letter",
  margin: (x: 0.72in, y: 0.68in),
  numbering: "1",
)
#set text(
  font: ("Libertinus Serif", "New Computer Modern"),
  size: 8.7pt,
  lang: "en",
)
#set par(justify: true, leading: 0.47em)
#set heading(numbering: "1.1")
#show heading.where(level: 3): it => {
  set block(above: 11pt, below: 4pt)
  set text(size: 9.4pt, weight: "bold")
  it
}
#show math.equation: set text(size: 8.5pt)

#align(center)[
  #text(size: 17pt, weight: "bold")[
    A Synopsis of Elementary Causality\
    in Pure Holonic Mathematics
  ]

  #v(5pt)
  #text(size: 8pt)[
    dependency edition 1 · exact constructions, transformations, derivations, boundaries
  ]
]

#v(12pt)

#block(stroke: 0.5pt + rgb("#6d7781"), inset: 7pt)[
  *Truth boundary.* Entries marked `project-postulate` define the laboratory
  modeling language. `proved-standard` imports ordinary mathematics under its
  stated hypotheses. `proved-derived` is a laboratory derivation.
  `conditional` retains its antecedent. `conjecture` is not proved. No entry in
  this edition proves the Riemann Hypothesis.
]

#outline(depth: 2, indent: auto)

= Elementary situated relations

#render-sequence(foundations)

= Logic, categories, gluing, and translation

#render-sequence(logic-category)

= Algorithms, execution, recursion, and rebase

#render-sequence(algorithms)

= Algebra, symmetry, order, and combinatorics

#render-sequence(algebra-combinatorics)

= Geometry, calculus, series, and invariance

#render-sequence(geometry-calculus)

= Topology, analysis, dynamics, and fractal iteration

#render-sequence(topology-analysis-dynamics)

= Manifolds, curvature, projection, knots, and simplicial geometry

#render-sequence(manifold-knot-geometry)

= Counting, primes, analytic transport, and completion

#render-sequence(arithmetic-analysis)

= Algebraic geometry, families, and cohomological arithmetic

#render-sequence(algebraic-geometry)

= Transcendence, special functions, and formulation atlases

#render-sequence(transcendence-special-functions)

= Computation, information, optimization, and formal dynamics

#render-sequence(computation-information)

= Mathematical-physics interfaces

#render-sequence(mathematical-physics)

= Independent Riemann-Hypothesis route atlas

#render-sequence(rh-routes)

= Counterexamples and quarantined false bridges

#render-sequence(counterexamples)
