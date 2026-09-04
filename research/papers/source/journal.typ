#import "@preview/unequivocal-ams:0.1.2": ams-article, theorem, proof
#import "lib/holonics.typ": *
#import "sections/00_orientation.typ": orientation
#import "sections/01_foundations.typ": foundations
#import "sections/02_formula.typ": formula
#import "sections/03_comparative.typ": comparative
#import "sections/04_learning.typ": learning
#import "sections/05_machine.typ": machine
#import "sections/06_network_protocol.typ": network-protocol

#show: ams-article.with(
  title: [Foundations of the Relational Holonic Calculus],
  authors: (
    (
      name: "Brandon",
      organization: [Laboratory],
    ),
    (
      name: "Sol",
      organization: [Research collaborator],
    ),
  ),
  abstract: [
    This working monograph reconstructs the most durable mathematical content of the Soma
    research programme as a dependency network rather than a chronology of claims. Its core is an
    occurrence-level calculus in which actual current meets available Standing in one atomic
    event, producing one successor and immediate radiation; a genuinely later consequence can
    then change later conduct. The manuscript derives receiver-relative comparison, completion,
    and exact compression; develops finite exponential, Euler-product, theta/Mellin, and
    aperture-tail relations without claiming analytic completion or the Riemann hypothesis;
    types the links to hypergraph rewriting, manifolds, fractal return, physics, and living
    systems; distinguishes a learned relation from one neural factorization; and states the
    measured boundary of the production machine. Direct constraints, assistant derivations,
    external theorems, implementation facts, and measurements remain explicitly distinct.
  ],
  bibliography: bibliography("references.bib"),
)

#show link: set text(font: "New Computer Modern")
#show figure.where(kind: "theorem"): roman-statement
#set table(align: left)

#outline(
  title: [Contents],
  depth: 3,
  indent: auto,
)
#pagebreak()

#orientation
#foundations
#formula
#comparative
#learning
#machine
#network-protocol
