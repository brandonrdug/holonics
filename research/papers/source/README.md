# Mathematical holonics papers

This is the laboratory's authored Typst publication layer for mathematical holonics. It is a
reading and writing surface, not a second claim index, engine owner, research scheduler, or
replacement for the source record. The mathematics is independent of any one Eros or
machine-learning application.

For the current pure-holonics/RH scope, begin with the dependency-ordered
[*Synopsis of Elementary Causality in Pure Holonic Mathematics*](synopsis/README.md) and its
importable [holonics registry](holonics/registry.typ). The older composed papers and object library
below remain source material until an entry is independently imported and regraded there.

Use the pinned [`MATHEMATICAL_HOLONICS.md`](../../../archive/reference/holobrochos-a07ff376/src/soma/MATHEMATICAL_HOLONICS.md)
for historical mathematical orientation, the pinned
[`MATHEMATICAL_RESEARCH_NETWORK.md`](../../../archive/reference/minimum-mechanics-a07ff376/src/soma/MATHEMATICAL_RESEARCH_NETWORK.md)
for the mechanism-indexed external source atlas, and the current
[`ESTABLISHED_CAPABILITIES`](../../../docs/canon/06_ESTABLISHED_CAPABILITIES.md) ledger for bounded
implementation and measured evidence.

The initial mixed volume remains available as an integrated historical manuscript:

- [`journal.typ`](journal.typ) is the compilation root.
- [`sections/01_foundations.typ`](sections/01_foundations.typ) develops J1.
- [`sections/02_formula.typ`](sections/02_formula.typ) develops J4.
- [`sections/03_comparative.typ`](sections/03_comparative.typ) develops J5.
- [`sections/04_learning.typ`](sections/04_learning.typ) develops J3.
- [`sections/05_machine.typ`](sections/05_machine.typ) develops J2.
- [`sections/06_network_protocol.typ`](sections/06_network_protocol.typ) records the dependency
  network and publication protocol.
- [`lib/holonics.typ`](lib/holonics.typ) is the small local notation and diagram library.
- [`lib/elements.typ`](lib/elements.typ) is the medium-aware geometric proof grammar: one
  construction is addressed consistently in its diagram, prose, and algebra.
- [`mathematics/`](mathematics) is the reusable object library for definitions, lemmas,
  theorems, corollaries, proofs, dependencies, and explicit boundaries.
- [`references.bib`](references.bib) contains the external bibliography; internal research and
  observation routes are linked at first use.

The manuscript uses `unequivocal-ams` as its page and numbering grammar. The local library keeps
the template's page, title, headings, counters, and proof treatment, but renders theorem-family
bodies in roman type so intentional emphasis remains visible. It also supplies the global/local
navigation layer and the reusable relational vector grammar used by the geometry figures.

## Standalone studies

- [`papers/categorical-holonics/main.typ`](papers/categorical-holonics/main.typ) formalizes the
  agnostic causal-compositional carrier. It now separates evolution shape, monoidal
  juxtaposition, typed interaction, enriched parameters, receiver fibers, local observation,
  and domain realization. A global face is transported local assembly over a boundary-defined
  region, never an absolute total field. Souls are marked causal diagrams rather than hashes or
  scalar invariants, with doctrinal and observational equivalence retained as weaker
  receiver-scoped relations. Its RH specialization turns the existing successor-contraction
  obligation into one convex naturality cone without claiming that the cone is already nonempty.
- [`papers/elements-of-holonics/main.typ`](papers/elements-of-holonics/main.typ) establishes the
  elementary mathematical layer: situated occurrence, comparison, boundary, atlas, transport,
  return, scale-turn, curvature, and local duality. Its first extension defines parameterized
  formulation families, lawful comparisons as decorated spans, and reversible rechartings as
  only the exact groupoid core. Machine learning appears only as one later application of that
  common geometry.
- [`papers/causal-formulation-ecologies/main.typ`](papers/causal-formulation-ecologies/main.typ)
  develops that span atlas through nonidentical formulations for π, e, complex powers, prime
  powers, and zeta. Its first exact cells distinguish involutive rechart, constant receiver
  return, changing series interior, bare summation from a recurrence-aware reverse translation,
  rational poles, and convergence boundaries. Its later application sections compare the same
  geometry with learned
  transformations, but those sections do not define the formulation ecology or its mathematical
  boundary.
- [`papers/riemann-receiver-geometry/main.typ`](papers/riemann-receiver-geometry/main.typ)
  reconstructs the complete RH line as a geometric, proof-auditable argument. It separates
  classical results, exact laboratory derivations, bounded measurements, and open hypotheses;
  derives the semilocal Euler successor metric and receiver-aperture connection; and stops at the
  precise completed-return inequality still required for RH.
- [`papers/prime-archimedean-formulation-atlas/main.typ`](papers/prime-archimedean-formulation-atlas/main.typ)
  gives the finite-prime side an exact valuation-simplex and root-lattice carrier, populates its
  vertical formulation direction with nonidentical π and e paths, and follows exact prime-divisor
  currents through both recurrence and additive accumulation in Machin and Chudnovsky
  presentations. It joins finite and infinite places through the product formula and zeta
  completion, derives path-relative mean transport with explicit discrete seams on Riemannian
  manifolds, refines its former “fibered groupoid” into the complete span bicategory plus exact
  rechart core, and formalizes ray tracing as a situated receiver. Its Bowl of Integers, Cayley
  cubic, Chen--Gackstatter, Klein quartic, and fractal comparisons explain why complex rendered
  faces can testify about constrained topology without becoming proof by appearance.
- [`papers/knot-causal-topology/main.typ`](papers/knot-causal-topology/main.typ) separates an
  embedded knot from its received diagram, braid presentation, skein class, prime connected-sum
  factors, and unknotting path. It uses Reidemeister, Alexander, Markov, Schubert,
  rational-tangle, skein-module, and planar-algebra structures to define contextual substitution
  and compression, then states the exact extra positivity and trace laws a knot-causal RH route
  would still owe.
- [`papers/receiver-relative-arithmetic-calculus/main.typ`](papers/receiver-relative-arithmetic-calculus/main.typ)
  defines the shared dynamic carrier for actual receiver incidence, receiver-generated boundary
  strata, exact smooth-plus-seam transport, graded prime-valuation occurrence currents, and
  higher-order joint incidence versus curvature. It reconstructs the `113 -> 127` refinement as
  six typed arithmetic wall crossings and places the π/e formulation fibers in the same
  three-direction arithmetic--Archimedean--receiver ecology required by the RH work.
- [`papers/prime-number-observatory/main.typ`](papers/prime-number-observatory/main.typ) is an
  exploratory showcase of the prime-number and RH observations: exact wheels and prime-power
  carriers, deterministic host/CUDA receipts, receiver-dependent prime relations, polynomial
  fibers, certified eta closures, explicit-formula residuals, and the open boundaries that keep
  those patterns from being mistaken for a universal prime geometry or an RH proof.

## Compile

Use Typst 0.15.1 from the clean repository root. The historical sources request New Computer
Modern Mono through `unequivocal-ams`; install that font for reproducible typography or treat the
reported fallback as a presentation difference. The following ten roots reproduce the retained
PDF set:

```sh
typst --version  # must report 0.15.1
mkdir -p papers/rendered
typst compile --root papers/source papers/source/journal.typ papers/rendered/soma-holonics-foundations.pdf
typst compile --root papers/source papers/source/papers/categorical-holonics/main.typ papers/rendered/categorical-holonics.pdf
typst compile --root papers/source papers/source/papers/elements-of-holonics/main.typ papers/rendered/elements-of-holonics.pdf
typst compile --root papers/source papers/source/papers/causal-formulation-ecologies/main.typ papers/rendered/causal-formulation-ecologies.pdf
typst compile --root papers/source papers/source/papers/riemann-receiver-geometry/main.typ papers/rendered/riemann-receiver-geometry.pdf
typst compile --root papers/source papers/source/papers/prime-archimedean-formulation-atlas/main.typ papers/rendered/prime-archimedean-formulation-atlas.pdf
typst compile --root papers/source papers/source/papers/knot-causal-topology/main.typ papers/rendered/knot-causal-topology.pdf
typst compile --root papers/source papers/source/papers/receiver-relative-arithmetic-calculus/main.typ papers/rendered/receiver-relative-arithmetic-calculus.pdf
typst compile --root papers/source papers/source/papers/prime-number-observatory/main.typ papers/rendered/prime-number-observatory.pdf
typst compile --root papers/source papers/source/synopsis/main.typ papers/rendered/synopsis-elementary-causality.pdf
```

## Long-term shape

Create these paths only when a real entry or paper needs them:

```text
entries/YYYY-MM-DD_slug/
  entry.typ
  figures.typ
  notes.typ

papers/short-title/
  main.typ
  sections/
  figures/
  references.bib
```

A visible reading note uses `reader-note` from the local library so authorship and disposition
remain explicit. Ordinary Typst `//` comments remain private and do not render.

## Boundary

This volume does not supersede the live mathematical orientation, external research network,
`FORMULA.md`, historical research deposits, or measured results. It reconstructs selected
relations into dependency-ordered mathematical manuscripts. Every claim remains restricted by
its named source, hypotheses, receiver, parameter region, evidence grade, and open boundary.
