# Corpus and method audit — 2026-07-25

## Existing mathematical corpus

The prior reusable Typst library contains 114 declared objects:

- 26 definitions
- 17 lemmas
- 57 theorems
- 13 corollaries
- 1 proof

Its declared key graph has no duplicate keys, missing dependencies, or cycles. It is nevertheless
not an elementary dependency synopsis. Important generic objects depend on later RH-specific
constructions:

- generic Schur/Kron/passivity depends on conditioned RH tension;
- the Kirchhoff-return theorem inherits that RH dependency;
- generic coarea depends on a parametric Weil bundle;
- generic congruence/inertia depends on the formulation atlas;
- a storage reduction depends on the conditional RH corollary it is meant to realize; and
- several “positive carrier implies RH” corollaries are coordinate faces of one sign obligation,
  not a serial chain of discoveries.

The new registry therefore rederives the elementary spine rather than merely sorting the 114 old
files. Old entries remain source material until imported and regraded one by one.

## Formal corpus

The current formal foundation is `src/soma/formal/elementary-holonics/`: pinned Lean/Mathlib, no
`sorry`, exact receiver factorization, situated transition paths, conjugate rebase, telescoping,
the exact numerator--denominator Swing carrier, and Mathlib's actual `RiemannHypothesis`
proposition. `src/soma/formal/rh-source-transport/` remains a separate exact finite conditional
result whose proportional candidate is rejected at the claimed analytic scope; it is not an RH
proof.

The old `src/labyrinth/mathematics/lean/` and `src/shrine/holon-math/` trees are quarantined as
historical/toy:

- 44 old files define an inhabited `OPEN` type and “prove” named conjectures by returning its
  inhabitant;
- `App_RH.lean` proves correctness of an integer-square-root interval, not a proposition about
  zeros of \(\zeta\);
- avoiding real/complex analysis was treated as rigor even when it removed the subject being
  studied; and
- kernel acceptance was sometimes reported as validating the intended scientific interpretation
  without a soundness map.

## Assistant behavior audit

The failure is systematic. In the current long conversation record, Brandon has had to use
“proceed” roughly 150 times and repeatedly call out vagueness, hedging, hyperfocus, “next
construction,” “what follows,” and open calculations. A broader assistant-message scan found
hundreds of continuation phrases and repeated uses of “remaining” or “next” around the same
unresolved implication.

The recurring pattern was:

1. locate a valid obstruction;
2. rename it a calculation, carrier, criterion, or next construction;
3. update neighboring prose, files, tests, or presentation;
4. return to the same obstruction; and
5. ask Brandon for another intuition.

That is why `AGENTS.md` no longer embeds the most recent RH carrier. It now stores method and scope;
the synopsis stores mathematics. “Calculation” is reserved for a bounded executable operation.
“Derivation” requires an identified implication and bridge. If no bridge is known, the result is
reported as unsupported rather than promised as the next step.

## RH route correction

The old corpus made the Weil sign the hub of nearly every path. The independent audit instead
found four nonidentical mechanism classes:

1. source-derived positive response;
2. exact closure and cancellation;
3. real-zero-preserving phase dynamics; and
4. exact source-spectrum geometry.

The first registry includes fifteen routes or programmes: positive-real/Pick, Weil, Li,
Stieltjes/Hankel, Nyman–Beurling–Báez-Duarte, Jensen/Laguerre–Pólya, de Bruijn–Newman,
de Branges/canonical systems, Speiser, Hilbert–Pólya, trace/noncommutative geometry,
function-field cohomology, prime/Möbius residual, Robin–Lagarias, and Bagchi recurrence.

Every route relocates the hard implication; none currently closes it. The present laboratory's
Euler–Gamma–theta positive-response work is retained as one branch. Its status is not inflated by
being recent.

## Broad import completed; depth remains explicit

The expanded registry now carries 244 entries across logic/category theory, algorithms, algebra
and combinatorics, geometry and calculus, topology and analysis, manifolds and knots, arithmetic
analysis, algebraic geometry, transcendence and special functions, computation and information,
mathematical physics, independent RH routes, and counterexamples. The registry compiles as one
dependency-checked source.

This is broad by construction but not encyclopedic by pretense. The remaining frontier is depth:

- formalize substantially more of the analytic and geometric spine in Lean;
- deepen higher category/topos/homotopical, Lie, noncommutative, and representation-theoretic
  interfaces when an actual dependency calls for them;
- deepen spectral sequences, index theory, trace formulas, canonical systems, and analytic
  continuation at theorem-proof level;
- deepen algebraic geometry beyond the entry portals to the exact cohomological machinery used by
  each arithmetic analogue;
- deepen PDE, stochastic-process, probability, and statistical-learning laws only with their
  complete spaces, measures, dynamics, and quantifiers; and
- derive an RH source-side theorem that closes one full established equivalence.

No sampled numerical route is listed. Big-\(O\), convergence, completion, and closure occur only
as exact quantified mathematical relations. Finite computations may discover
counterexamples or exact identities, but cannot substitute for the universal implication.

## Holobrochos correction

The audit retained Holobrochos where it is mathematically exact: construction before
presentation; source occurrence, denoted value, and receiver face kept distinct; situated
three-body comparison; current/form as receiver-relative roles; quotient factorization as
receiver-exact compression; path identity stronger than endpoint identity; conjugacy as exact
rebase; and chain/cochain boundary cancellation.

It did not import the historical overclaims that a continuum is fictitious, signed integers are
inadmissible, cross-ratio equals Euler characteristic, \(\partial^2=0\) alone establishes
recurrence or conservation, factors recur infinitely, primes are universally frame-relative, or
physics and complexity claims follow without their own hypotheses.

This audit is a scope record, not an executable queue. The present mathematical question selects
which dependency is deepened.
