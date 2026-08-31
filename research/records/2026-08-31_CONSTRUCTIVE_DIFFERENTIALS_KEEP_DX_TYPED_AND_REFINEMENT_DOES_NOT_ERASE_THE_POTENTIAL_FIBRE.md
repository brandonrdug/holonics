# Constructive differentials keep `dx` typed and refinement does not erase the potential fibre

Date: 2026-08-31  
Status: research and construction evidence under `blueprint/THE_ROADMAP.md`; this record schedules
nothing.

## Personal perspective recovered from the conversation line

[interpretation; source-inspected] Brandon's repeated corrections across the Codex thread and the
Claude Code sessions of 2026-08-29--30 have one stable shape. Formal proof, geometric model,
receiver projection, motion through time, and engine execution are required to be faces of one
construction. Isolated prose cards, visually smooth but mathematically unauthenticated diagrams,
and toy solvers which replace topology by counts are rejected for the same reason: their displayed
face cannot reconstruct the claimed mechanism.

[interpretation; source-inspected] The desire to reinforce the foundation before returning to
Eros/Athena is not a request to avoid the engine. It is a request to make later implementation
decisions local and unsurprising: exact owner, exact factor order, exact boundary, exact receiver,
and a falsifier which fires before a large Rust/CUDA passage is built around the wrong object.

[project-postulate] The practical response is therefore a bounded formal supplement followed by a
return to CONS3, not another general solver cabinet or indefinite mathematical detour.

## The supplied sources

[established-bounded; source-inspected] Brasca and Clemente's
[Synthetic Differential Geometry in Lean](https://arxiv.org/pdf/2603.17457) formalizes
Kock--Lawvere differential calculus and multivariate infinitesimal Taylor equality in Lean. Its
development is intuitionistic, introduces a unique-choice axiom, and actively excludes hidden uses
of `Classical.choice`. It is a strong design precedent but cannot be imported as an ordinary
classical real theorem or as a new project axiom.

[established-bounded; source-inspected] Giordano's
[Infinitesimals without Logic](https://arxiv.org/pdf/0909.3954) and
[order/geometric representation paper](https://www.mat.univie.ac.at/~giordap7/Giordano-Order_relation_and_geometrical_representation_of_Fermat_reals.pdf)
construct finite nilpotent decompositions, exact Taylor formulas on nilpotent neighborhoods,
cancellation laws restricted to standard coefficients, and geometric/order representations. The
Fermat reals form a ring rather than a field: unrestricted division by `dx` is not licensed.

[established-bounded; source-inspected] Rovelli and Zatloukal's
[Natural discrete differential calculus in physics](https://arxiv.org/html/1902.03026v2) treats
integrated `p`-forms as cochains on oriented simplices, obtains `d` from the boundary, and obtains a
discrete adjoint/codifferential from the finite cochain pairing. Its continuum-approximation remarks
do not supply a general convergence theorem.

[established-bounded; source-inspected] Harlow and Wu's
[Covariant phase space with boundaries](https://arxiv.org/html/1906.08616v4) shows why total
derivatives cannot be discarded independently of boundary action terms. Shifts of the Lagrangian,
symplectic potential, and corner/boundary terms must travel together; permissive boundary
conditions can make the additional term nonzero.

[established-bounded; source-inspected] Gangbo, Kim, and Pacini's
[Wasserstein differential forms](https://arxiv.org/pdf/0807.1065) constructs tangent/cotangent
objects and Green-type boundary formulas on a stratified infinite-dimensional measure space. The
regularity hypotheses are substantial, and the authors do not claim that every prescribed boundary
admits the required surface.

[established-bounded; source-inspected] Nugraha's
[Chunk and Permeate infinitesimal field](https://arxiv.org/pdf/2607.08206) uses the formal Laurent
series field, its valuation ring, and a standard-part receiver. The algebraic content useful here is
the valuation/residue split. Its paraconsistent permeability layer, broad constructivity claims,
and Grossone claims are not required: a typed receiver map with a retained kernel states the usable
relation without combining inconsistent chunks.

[historical; source-inspected] Rosinger's
[non-Archimedean field extensions](https://arxiv.org/pdf/0911.4824) supplies ultrapower “walkable
worlds,” monads, nested scales, and self-similar order geometry. The field construction depends on
ultrafilters, and the proposed physical meanings are speculative evidence only.

[interpretation; source-inspected] Weng's
[octonion fluid paper](https://arxiv.org/pdf/2211.04225) is useful as a warning and a question. Its
ordered octonion products demonstrate that factor order, conjugation, and dimensional rebasing
cannot be suppressed. Its proposed fluid/electromagnetic consequences are definition-dependent and
not supported there by a boundary theorem, convergence proof, or experimental calibration.

## Derived formal correction

[definition] In first-order calculus, `dx` is a tangent occurrence and `df_x` is a linear map or
covector. The lawful expression is `df_x(dx)`. A shared scale acts by `df_x(r dx) = r df_x(dx)`;
this is linearity, not syntactic multiplication of an equation by a glyph.

[definition] In differential-form calculus, the corresponding move is pullback to a path/domain
and integration. Jacobian, orientation, exterior degree, quantity line, boundary, and regularity
remain explicit.

[definition] In a square-zero extension, `a + b epsilon` retains standard face `a` and differential
residue `b`; `epsilon^2 = 0` makes the first-order product rule exact. The standard-face receiver
may return zero while `b` remains nonzero.

[proved-standard] FTC states that the integral of an exact differential is its endpoint difference.
It does not state that the local differential, field, circulation, or hidden receiver fibre is zero.

[definition] Radix refinement separates local amplitude from integrated current. The exact control
uses `n+1` cells, each carrying `1/(n+1)`: each cell face tends to zero as `n` grows, while the sum is
exactly one at every refinement. A local limit cannot be substituted for the integrated boundary
return.

[definition] A higher-dimensional shadow is a linear receiver `q : Ambient -> Face`. Equal shadows
mean exactly that the occurrence difference lies in `ker q`. The complete reconstruction fibre,
not the lower-dimensional face, is the higher-dimensional object still compatible with the
measurement.

## Formal return and engine consequence

[proved-derived; formal-checked] `HolonicConstructiveDifferentialBoundary.lean` now returns the
bounded construction through the live quantum-transport umbrella:

- `firstOrderJet_product_residue` gives the order-preserving product coefficient
  `left * dright + dleft * right` over a possibly noncommutative ring;
- `completeJetReceiver_injective` and
  `pureInfinitesimal_has_zeroFace_and_nonzeroResidue` separate a projected zero from carrier zero;
- `ExactDifferentialPath.integratesToBoundary` and `receiverIntegratesToBoundary` compose a typed
  linear differential with the standing finite telescope;
- `HigherDimensionalReceiver.equalShadow_iff_difference_mem_kernel` returns the exact unresolved
  receiver kernel;
- `refinement_cell_vanishes_but_total_remains` keeps the pointwise-zero and integrated-one facts in
  one theorem; and
- the MVT and squeeze certificates retain their hypotheses, witness, and uncollapsed residue face.

[established-bounded; formal-checked; measured] The focused owner compiled without warnings, and
`bash tools/lean_check.sh` built `HolonicQuantumTransport.lean` successfully under Lean `v4.33.0`:
3,765 jobs. The owner contains no `sorry` or new axiom. Its axiom audit prints only admitted
Lean/Mathlib axioms; `Classical.choice` remains visible in the imported analytic existence results.
Here “constructive differential calculus” therefore means explicit typed construction and retained
reconstruction data, not a claim that the complete imported analysis development is
constructive-logic-only.

[definition] Three constraints return to the engine. First, contraction preserves operand order,
quantity type, and target-site/port lineage; a displayed scalar factor never authorizes an untyped
rewrite. Second, terminal receiver/readback may not infer that the complete dependent complex
current vanished merely because a positive or standard receiver face is zero. Third, refinement
must join the complete local current and its boundary return before any pointwise-small or
lower-dimensional receiver is allowed to condense it.

[project-postulate] This closes the requested foundation sharpening without displacing engine work.
CONS3 resumes at the pre-existing moment-front contraction/receiver/readback residual; these three
constraints narrow that split but do not add a new engine organ.
