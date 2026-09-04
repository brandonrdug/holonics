# Synopsis of Elementary Causality in Pure Holonic Mathematics

This directory is the authoritative dependency route for the current pure-holonics programme.
It is inspired by Carr's *Synopsis*: results are ordered by what they require and connected by
explicit transformations. It is not a textbook, a journal, an Eros roadmap, or a prose-first
survey.

## Trust boundary

The compilation root is [`main.typ`](main.typ). It renders the importable entries in
[`../holonics/registry.typ`](../holonics/registry.typ) in strict dependency order.

Each entry has:

- a stable identifier and mathematical kind;
- one normalized epistemic grade;
- a typed statement;
- dependencies which must occur earlier in the sequence;
- a derivation, proof, or precise source;
- admitted transformations and receiver;
- an exact boundary.

The registry rejects duplicate identifiers, unknown grades, and dependencies which are missing or
occur later. This checks the declared graph; it does not prove that a claimed mathematical
dependency is semantically sufficient. That second audit is mathematical work.

## Grades

`project-postulate`, `definition`, `identity`, `proved-standard`, `proved-derived`, `conditional`,
`conjecture`, `counterexample`, `computational-witness`, and `historical-toy` are the only grades.

A published theorem is imported only after its hypotheses and both directions, when applicable,
are stated. A laboratory conjecture remains a conjecture. A finite computation remains a witness.
A conditional result displays its antecedent. No inhabited placeholder stands for an open
proposition.

## Broad dependency atlas

The current edition contains 244 importable entries. Its order is derivational rather than
historical:

1. situated occurrence, receiver, comparison, holon, soul, exact compression, standing, phase,
   probability, and loss;
2. logic, induction, categories, universal constructions, gluing, and theory/model translation;
3. parameterized algorithms, ordered execution paths, composition, recursion, exact rebase, and
   quotient;
4. algebraic structures, symmetry, linear algebra, field and Galois transport, order,
   combinatorics, graphs, matroids, and generating functions;
5. projective ratio geometry, calculus, exact series and limits, boundary cancellation, and
   coordinate change;
6. topology, measure, functional and harmonic analysis, dynamics, fractal iteration, PDE, and
   exact asymptotic relations;
7. manifolds, differential forms, curvature, Ricci flow, symplectic and holomorphic geometry,
   conics, knots, tangles, and simplicial complexes;
8. counting, primes, Dirichlet and Möbius structure, Euler products, theta/Poisson/Mellin
   completion, \(\xi\), Hadamard factorization, and the explicit formula;
9. algebraic geometry, families, discriminants, cohomology, Frobenius, and purity;
10. transcendence, \(\pi\), \(e\), Gamma/Beta/hypergeometric and elliptic functions, modular
    forms, periods, continued fractions, and formulation atlases;
11. computation, rewriting, automata, type theory, information and coding, exact optimization,
    quantum circuits, and a bounded statistical-learning portal;
12. dimensioned mathematical physics, variational laws, exact conservation, circuits, stress,
    thermodynamics, relativity, quantum representation theory, and local observable algebras;
13. a route-neutral RH atlas followed by counterexamples to recurrent false bridges.

This breadth is an import architecture, not a claim that every specialist theorem in mathematics
has been rederived. A field enters through exact typed structures and transport maps, and can be
deepened without changing the foundation. H.0031 is the general theory/model/translation portal:
an unlisted field is not excluded, but neither is it silently declared proved.

The projective Swing is stored first as its exact ordered numerator--denominator pair. A scalar
quotient is only one admissible chart. Likewise, an infinite construction is admitted through an
exact limit, closure, identity, certified enclosure, or complete quantified asymptotic relation.
No finite numerical surrogate bears a proof.

## RH boundary

The root proposition is the standard zero-locus statement for
\(\mathcal X(z)=\xi(\tfrac12+z)\). Weil positivity is one route. The Weil conjectures are a
function-field analogue. A Weyl function is an operator-theoretic object. They are not synonyms
and none is the standard to which every holonic argument must conform.

Every RH route records its exact equivalence, proof mechanism, source-side construction, and
unresolved implication. An RH-equivalent sign, norm, kernel, recurrence, spectrum, or inequality
is not a proof until that unresolved implication is established.

The broadened fields do not manufacture a proof by vocabulary. They expose the exact maps a
holonic proof would have to compose: arithmetic source to analytic completion, completion to a
positive/closed/real/spectral receiver, and that receiver back to the full zero divisor. The
open obligation remains a universal exact implication, not a request for more numerical evidence.

## Holobrochos inheritance

The current foundation retains the exact useful distinctions from Holobrochos:

- presentation equality, denoted-value equality, receiver equality, and occurrence identity are
  separate relations;
- comparison is situated by a frame and is therefore at least a frame/object/object relation;
- current and form are receiver-relative roles rather than two ontological species;
- equal endpoints do not identify ordered paths;
- exact compression means factorization through a declared quotient for a declared receiver
  family;
- exact rebase is an invertible conjugacy or natural transport; and
- boundary-of-boundary and coboundary-of-coboundary vanish exactly.

Historical Holobrochos slogans are not imported as theorems. In particular, cross-ratio is not
Euler characteristic, \(\partial^2=0\) does not by itself prove recurrence or physical
conservation, factorhood does not imply infinite recurrence, and physical or computational claims
require their own typed hypotheses.

## Formal companion

[`../../../formal/elementary-holonics/`](../../../../formal/elementary-holonics) is the retained Lean trust
boundary. It formalizes the elementary relational/algorithmic spine and selected exact identities.
It does not formalize RH by replacing it with a finite surrogate. The older Labyrinth and Shrine
formal trees are historical/toy unless an individual result is rederived into the current package.

## Compile

From the repository root:

```sh
typst compile --root papers/source \
  papers/source/synopsis/main.typ \
  papers/rendered/synopsis-elementary-causality.pdf
```

Compilation is structural verification, not a reason to spend a research round on rendering.
