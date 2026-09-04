# The constructive differential boundary and receiver calculus

## Authority and scope

**Status:** COMPLETED BOUNDED FORMAL SUPPLEMENT UNDER [`THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md). THIS FILE
SCHEDULES NOTHING.

[definition] Brandon's direct instruction of 2026-08-31 founds `CDB1`. It supplements QLT with one
Lean owner connecting typed first-order factors, exact finite integration, boundary return,
receiver shadows, and refinement limits. It returns immediately to CONS3 after its gate.

[project-postulate] The phrase “multiply both sides by `dx`” is never admitted as untyped symbolic
algebra. A lawful reconstruction states which operation occurred: evaluation of a linear
differential on a tangent occurrence; pullback of a differential form; tensor/rebase of a typed
quantity line; integration over an oriented domain; or coefficient extraction from an explicit
square-zero extension.

[project-postulate] A receiver face tending to zero does not make its carrier or influence zero.
Departure requires the complete residue/reconstruction fibre to vanish or a proof that every
declared future consequence factors through the zero face.

## Reused owners

[proved-derived; formal-checked] `HolonicDifferenceCalculus.lean` already proves that finite local
differences telescope to their two boundary faces, and that a coarse difference is the exact sum of
its microscopic window.

[proved-derived; formal-checked] `HolonicUnicursalCurrent.lean`,
`HolonicGranularBoundaryRadiation.lean`, `HolonicDiscreteInduction.lean`, and
`HolonicPortResolvedBoundaryTransport.lean` already own specialized path, Stokes-like, continuity,
and stored/current/boundary telescopes.

[proved-standard; source-inspected] Mathlib provides `DualNumber`, `TrivSqZeroExt`, the square-zero
ideal, and the equivalence between derivations and algebra lifts through a square-zero extension.
These are the admitted infinitesimal substrate; no Kock--Lawvere or nonstandard-real axiom is added.

[proved-derived; formal-checked] `Chronology.lean` already owns the chord chart, the equivalence
between a flat chord-chart derivative and the mean endpoint rate, and the receiver squeeze theorem.

## Required construction

[definition] `HolonicConstructiveDifferentialBoundary.lean` must return:

- an explicit first-order jet over Mathlib dual numbers;
- square-zero, standard-face, residue, product/Leibniz, and complete reconstruction laws;
- an `ExactDifferentialPath` whose typed tangent increments integrate through one bundled linear
  differential to the endpoint difference;
- the same finite FTC after an arbitrary linear receiver shadow;
- a higher-dimensional receiver with exact kernel/reconstruction-fibre characterization;
- a nonzero pure infinitesimal whose standard face is zero;
- an exact radix family whose individual real cell potential tends to zero while every integrated
  total is one;
- an explicit MVT witness certificate under the standard hypotheses; and
- a squeeze certificate which places only the receiver face and does not silently delete another
  residue coordinate.

## Gate and falsifiers

**Pass CDB1:** [definition] the new owner builds through `HolonicQuantumTransport.lean` under Lean
`v4.33.0`, contains no `sorry` or new axiom, prints only admitted Lean/Mathlib axioms, and its finite
and limit controls return exactly.

[counterexample] A proof which cancels a nilpotent tangent as though it were invertible fails CDB1.

[counterexample] A proof which infers carrier equality from equal standard faces without checking
the residue fails CDB1.

[counterexample] A refinement argument which concludes that a total potential vanishes because
each cell contribution tends to zero fails the exact radix control.

[counterexample] A boundary theorem without orientation/domain, local differential law, endpoint
faces, or integrability/refinement hypotheses does not establish FTC, Stokes, or flux conservation.

[counterexample] A lower-dimensional shadow is not the higher-dimensional occurrence. It becomes
an exact chart only for the receiver/history family whose successors factor through it.

## Return

[proved-derived; formal-checked] CDB1 returned
`HolonicConstructiveDifferentialBoundary.lean`. Its noncommutative-ring first-order jet preserves
factor order and separately returns the standard and residue faces; its complete pair receiver is
injective; and a nonzero pure infinitesimal witnesses that a zero standard face is not a zero
carrier.

[proved-derived; formal-checked] `ExactDifferentialPath.integratesToBoundary` composes one typed
linear differential with the existing finite telescope. An arbitrary linear receiver commutes with
that endpoint return. `HigherDimensionalReceiver.equalShadow_iff_difference_mem_kernel` identifies
the exact reconstruction population behind one lower-dimensional face.

[proved-derived; formal-checked] `refinement_cell_vanishes_but_total_remains` proves simultaneously
that the `1/(n+1)` cell face tends to zero and that the complete `n+1`-cell sum is exactly one for
every refinement. The MVT certificate returns an interior occurrence with its derivative witness;
the squeeze certificate places only its declared real face while retaining a separate residue
coordinate.

[established-bounded; formal-checked; measured] `bash tools/lean_check.sh` built the live
`HolonicQuantumTransport.lean` umbrella successfully under Lean `v4.33.0`: 3,765 jobs. The new
owner contains no `sorry` or new axiom. Its printed axiom surface is the admitted Lean/Mathlib
surface (`propext`, `Classical.choice` where the imported analytic theorem uses it, and
`Quot.sound`); it does not add Kock--Lawvere, unique-choice, nonstandard-real, or paraconsistent
axioms.
