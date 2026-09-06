# Imported mathematical constructions

[historical] These are the 28 explicitly authored mathematical passages in the retired apparatus,
with their original assertions, hypotheses and fibres. A declared `proved-derived` grade below
is archived testimony, not a new proof audit. Current source and the
[mathematical synthesis](../../../docs/MATHEMATICS_AND_NATIVE_CONDUCT.md) govern current use.

The readable before/after views retain ordered child roles. Exact expression IDs, multiplicities,
ports, syntax, source links and all 550 manual expression occurrences remain in
[mathematics.json](mathematics.json), with object/claim metadata in [relations.json](relations.json).
These files are documentation, with no evaluator, importer or training-pipeline binding.

## Passage 1: swing OBJ-2d9a0cfd-f103-44b2-bfb7-c8bbc0917c4a -> OBJ-84e4457a-7509-4b15-8b14-87474ad48f35

ID: `OBJ-a4f0f506-84f6-4095-ac20-65d0f48c1025` · original grade: `proved-derived` · 2026-08-28T04:37:20.080699+00:00

Before: `OBJ-2d9a0cfd-f103-44b2-bfb7-c8bbc0917c4a`

````````text
transport(source: genuine rational singular two-chain of S2 x S2, diagonal: paired coordinate simplices over one shared source simplex, left_axis: 0x2, interaction_axis: 1x1 with Koszul orientation, right_axis: 2x0, return: ordered two-shuffle rejoin, reconstruction_fibre: productRoundTripDefectCycle, regular_cell_extension: family(platonic_carrier: record(p: 3, q: 3, face_population: 4, history_population: 32), platonic_carrier: record(p: 4, q: 3, face_population: 6, history_population: 96), platonic_carrier: record(p: 3, q: 4, face_population: 8, history_population: 64), platonic_carrier: record(p: 3, q: 5, face_population: 20, history_population: 160), platonic_carrier: record(p: 5, q: 3, face_population: 12, history_population: 384)))
````````

After: `OBJ-84e4457a-7509-4b15-8b14-87474ad48f35`

````````text
chain(before_defect: transport(source: genuine rational singular two-chain of S2 x S2, diagonal: paired coordinate simplices over one shared source simplex, left_axis: 0x2, interaction_axis: 1x1 with Koszul orientation, right_axis: 2x0, return: ordered two-shuffle rejoin, reconstruction_fibre: productRoundTripDefectCycle, regular_cell_extension: family(platonic_carrier: record(p: 3, q: 3, face_population: 4, history_population: 32), platonic_carrier: record(p: 4, q: 3, face_population: 6, history_population: 96), platonic_carrier: record(p: 3, q: 4, face_population: 8, history_population: 64), platonic_carrier: record(p: 3, q: 5, face_population: 20, history_population: 160), platonic_carrier: record(p: 5, q: 3, face_population: 12, history_population: 384))), filler_term_0_negative: -(s0 s0 d2 x, s2 y), filler_term_1_positive: +(s2 s0 d2 x, s1 y), filler_term_2_positive: +(s0 x, s1 s1 d1 y), filler_term_3_negative: -(s1 x, s2 y), returned_boundary: productRoundTripDefectFillerChain_boundary, boundary_holon: productReconstructionBoundaryHolon)
````````

Operation: diagonalReconstructionFillerTwo / productRoundTripDefectFillerChain

Orientation: closed reconstruction defect -> explicit degree-three current -> exact source-minus-target boundary

Receiver: Genuine rational singular degree-two homology of S²×S²

Boundary: d H₂ + H₁ d = rejoin₂ separate₂ - id; on cycles, d H₂ = rejoin₂ separate₂ - id

Retained fibre: The original genuine singular cycle, all three separated axes, four signed tetrahedral filler occurrences, and the exact chain equivalences in degrees two and three are retained.

Hypotheses: ["current is a finite rational diagonal two-current","for the shortened closed-cycle law, diagonalBoundaryTwo current = 0","the genuine attachment uses productChainDiagonalEquiv in degrees two and three"]

## Passage 2: Product degree-three boundary separation

ID: `OBJ-a208e4d4-ff6d-4287-b008-66c52410fe16` · original grade: `proved-derived` · 2026-08-28T04:52:02.416928+00:00

Before: `OBJ-df579779-f7c0-4b3b-9bba-78bd1a0b5192`

````````text
Current(DiagonalOccurrence X Y 3)
````````

After: `OBJ-ba48e49a-5907-4dde-8584-5013ef50cacc`

````````text
Current(TotalThreeOccurrence X Y)
````````

Operation: The exact degree-three Alexander–Whitney separation current.

Orientation: diagonal degree 3 -> ordered total-degree axes -> degree 2 boundary

Receiver: Sphere-product Hodge ruling receiver retaining all four total-degree axes.

Boundary: totalBoundaryThree ∘ separateThree = separateTwo ∘ diagonalBoundaryThree; instantiated on genuine S²×S² singular chains by separatedProductThreeChain_boundary.

Retained fibre: The diagonal source simplex, each of the four ordered axis occurrences 0×3/1×2/2×1/3×0, rational coefficients, and the genuine product-chain equivalence are all retained.

Hypotheses: ["X and Y are simplicial sets","currents are finite rational occurrence currents","factor degree and simplex orientation are retained"]

## Passage 3: oriented Euclidean residue--winding equivalence

ID: `OBJ-b80f0f04-b607-4985-a4e3-cf71a3383439` · original grade: `proved-derived` · 2026-08-29T04:08:37.673523+00:00

Before: `OBJ-e0f73b0f-ba43-42c2-9923-fba97de63698`

````````text
s : ℤ
````````

After: `OBJ-8e622913-c4cf-4271-9571-314d6029ef80`

````````text
ordered-product(residue-cross-section: (s : ZMod m), signed-winding: s / (m : ℤ), reconstruction-law: s = residue.val + m * winding)
````````

Operation: intEuclideanChart m

Orientation: source-to-residue-cross-section-and-signed-winding

Receiver: lossless oriented Euclidean residue transport

Boundary: The passage concerns integer Euclidean residue transport only; it does not identify arithmetic modulus with analytic norm, geometric moduli, or divisor ledgers.

Retained fibre: For each residue r : ZMod m, the complete predecessor fibre is equivalent to ℤ through the signed winding coordinate q, with source reconstructed as r.val + m*q.

Hypotheses: ["m : ℕ","NeZero m"]

## Passage 4: Generalized pantographic swing in the constraint chart

ID: `OBJ-6af6e48e-5548-4877-a84a-d79485bb2c3b` · original grade: `definition` · 2026-08-29T16:22:26.964195+00:00

Before: `OBJ-09ae7357-30f6-498b-bd7b-fc8a88dc782d`

````````text
a
````````

After: `OBJ-065327c8-aa82-4906-854c-12abcf375376`

````````text
operator-application(scale-current: lambda, anchor: b, board: d, source-occurrence: a)
````````

Operation: P^lambda_(b,d) = chi_(b,d)^(-1) ∘ (lambda·-) ∘ chi_(b,d)

Orientation: source occurrence to chart-scaled returned occurrence

Receiver: projective constraint-chart receiver; affine pantograph and harmonic swing are declared faces

Boundary: The definition covers the projective endpoint transport and its affine board-at-infinity face. It does not identify a mechanical linkage configuration, a railway contact law, a Complex Parametron fibre, or a physical long-range interaction.

Retained fibre: Retain the complete linkage/interaction occurrence population, both boundary maps, joining equalities for serial composition, assembly chirality and singular branches, constitutive current/phase, delay/contact history, and every distinction omitted by the selected endpoint receiver.

Hypotheses: ["b and d are distinct addressed projective constraints","chi_(b,d)(x)=(x-b)/(x-d) is defined on the admitted source domain","the returned rational denominator is nonzero at the supplied occurrence","lambda is a typed endomorphism/scaling current of the declared one-dimensional receiver line"]

## Passage 5: Generalized deviation differentiates to complete separation jerk

ID: `OBJ-b4981c6f-9786-4a18-83ed-f502762f6ee3` · original grade: `proved-derived` · 2026-08-29T16:41:12.768123+00:00

Before: `OBJ-d6ea16b7-00af-499d-866f-abf4ccea6b77`

````````text
equation(left: D_tau^2 xi, relation: =, curvature: R(u,xi)u, acceleration-gradient: nabla_xi a)
````````

After: `OBJ-bb5824f4-f25e-4b4a-a264-4fdc52f42a98`

````````text
equation(left: D_tau^3 xi, relation: =, curvature-gradient: (nabla_u R)(u,xi)u, accelerated-leg-1: R(a,xi)u, separation-rate: R(u,D_tau xi)u, accelerated-leg-2: R(u,xi)a, acceleration-gradient: D_tau(nabla_xi a))
````````

Operation: covariant derivative D_tau=nabla_u with the tensor Leibniz rule

Orientation: forward: generalized deviation to complete separation jerk

Receiver: separation-jerk receiver

Boundary: Riemann sign convention may reverse curvature terms; the acceleration-gradient derivative vanishes only under a declared geodesic/restricted congruence

Retained fibre: Retain curvature-gradient, two accelerated-leg terms, separation-rate term, and acceleration-gradient derivative as distinct occurrences; a receiver omitting the last is incomplete for a generic accelerated congruence.

Hypotheses: ["torsion-free connection","[u,xi]=0","D_tau=nabla_u","generalized deviation D_tau^2 xi=R(u,xi)u+nabla_xi a"]

## Passage 6: Ordered plural-time jet descends to a diagonal world-line jet

ID: `OBJ-4274cc10-00e5-40e9-9c27-d8c1664c935f` · original grade: `definition` · 2026-08-29T16:41:12.893880+00:00

Before: `OBJ-13480182-e7be-4df2-ada2-2d4c087ef383`

````````text
definition(defined-object: J_X[a_1,...,a_n], relation: :=, operator-word: ordered-composition(latest-operator: nabla_(a_n), intermediate-operators: ..., earliest-operator: nabla_(a_1), operand: X))
````````

After: `OBJ-90a6fc41-fafa-43eb-b6a7-c1dec7487ce0`

````````text
receiver-equation(input: J_X[a_1,...,a_n], receiver-map: a_1=...=a_n=u, output: nabla_u^n X)
````````

Operation: diagonal insertion of one world-line direction u into every ordered covector slot

Orientation: forward: plural addressed time-word to diagonal proper-time receiver

Receiver: diagonal world-line receiver

Boundary: derivative order is tensor/jet rank on one base and does not add spacetime dimensions

Retained fibre: All ordered addressed axis words that return the same diagonal jet, together with commutator, curvature, torsion, gauge, and domain testimony required to separate them.

Hypotheses: ["the selected covariant derivatives and section are defined","all addressed slots are inserted with the declared direction u"]

## Passage 7: Constant-mass rebase relates higher position jets to force derivatives

ID: `OBJ-d92198c8-5d3d-4285-9f0b-0c6fc63d4fc5` · original grade: `proved-derived` · 2026-08-29T16:41:12.971928+00:00

Before: `OBJ-13480182-e7be-4df2-ada2-2d4c087ef383`

````````text
definition(defined-object: J_X[a_1,...,a_n], relation: :=, operator-word: ordered-composition(latest-operator: nabla_(a_n), intermediate-operators: ..., earliest-operator: nabla_(a_1), operand: X))
````````

After: `OBJ-4a2cecd6-a944-4e4c-91d9-bdfeb21a51a8`

````````text
equation(left: nabla_u^n F, relation: =, right: ordered-product(factor: m, factor: nabla_u^(n+2) x))
````````

Operation: constant-mass constitutive rebase F=m nabla_u^2 x followed by n covariant derivatives

Orientation: forward: kinematic jet to force-valued jet

Receiver: constant-mass force/kinematic bridge

Boundary: variable mass, nonmetric transport, or a changed projection introduces additional Leibniz/connection terms

Retained fibre: Retain whether the occurrence was presented as position order n+2 or force order n, the mass line, connection, projection convention, and every derivative slot.

Hypotheses: ["m is constant","F=m nabla_u^2 x","one connection and projection convention is retained"]

## Passage 8: Pantograph recurrence lifts to the complete finite derivative tower

ID: `OBJ-3e41f454-23d3-4d21-b610-8bc2584535fe` · original grade: `proved-derived` · 2026-08-29T16:41:13.056349+00:00

Before: `OBJ-d75123d7-9d1c-4da9-b9e4-cf52f0c96ae1`

````````text
equation(left: D y(x), relation: =, right: ordered-product(factor: beta, factor: y(p x)))
````````

After: `OBJ-433f769f-e9c5-4d1d-a7c1-3b3516ddefe4`

````````text
equation(left: D^n y(x), relation: =, right: ordered-product(factor: beta^n, factor: p^binomial(n,2), factor: y(p^n x)))
````````

Operation: finite induction by differentiation and the chain rule

Orientation: forward: seed recurrence to complete finite derivative tower

Receiver: pantographic higher-jet receiver

Boundary: scalar or complex one-variable chart; no claim of curved-connection or variable-gain naturality

Retained fibre: Retain the ordered n derivative/scale-crossing occurrences and the source section at p^n x; beta^n p^binomial(n,2) is their closed receiver coefficient, not their identity.

Hypotheses: ["n is a natural number","p and beta are constant","y satisfies D y(x)=beta y(p x)","y has the requested finite derivatives"]

## Passage 9: finite causal time to typed causal extent family

ID: `OBJ-092417db-b3ab-45b7-bf1c-8559050a815d` · original grade: `definition` · 2026-08-29T22:18:04.495243+00:00

Before: `OBJ-3a44ade4-61c7-479c-8820-4153d1f6893d`

````````text
composition(before: U_x, operator: pi_A: algorithmic unfolding -> apparatus micro-realization, operator: S_A: exact resource current and feasible schedule -> least local makespan T_A*, operator: chi_A,O: positive rational local-clock -> observer-clock transport, after: Delta t_O = (m/n) T_A* with quotient-residue phase, reconstruction-fibre: precedence, path latency, resource demand/capacity, service allocation, transport, apparatus projection, clock addresses, quotient Q, phase R)
````````

After: `OBJ-414cf5a6-a333-43d2-932e-1742178374ff`

````````text
typed-causal-extent-family(indexed_potential_population: {'index': 'n', 'population': 'Phi_n', 'size_receiver': '|x|=n'}, causal_unfolding: {'map': 'x -> U_x', 'retains': ['occurrences', 'precedence', 'transport', 'resource demand', 'boundaries', 'higher cells']}, time_quantity_line: {'coordinate_face': 'local oscillator crossing count', 'dimension': 'time', 'symbol': 'T_A'}, length_quantity_line: {'coordinate_face': 'ruler/wavelength cell count', 'dimension': 'length', 'symbol': 'L_A'}, clock_ruler_constitution: {'dimension': 'length tensor dual(time)', 'law': 'lambda_A = kappa_A(tau_A)', 'residue': 'quotient-remainder fibre', 'symbol': 'kappa_A : T_A -> L_A'}, feasible_schedule_population: {'constraints': ['causal precedence', 'current conservation', 'resource capacity', 'transport latency', 'attained horizon'], 'symbol': 'Sigma_A(U_x)'}, optimal_local_extent: {'length': 'Lambda_A*(x)=kappa_A(T_A*(x))', 'time': 'T_A*(x)=min_{sigma in Sigma_A(U_x)} H(sigma)'}, bound_certificate: {'exact': 'lower=upper', 'law': 'L_A(x) <= T_A*(x) <= U_A(x)', 'lower': ['critical path', 'resource pressure', 'boundary cut'], 'upper': 'uniformly constructed feasible schedule'}, family_receivers: {'acceptance': 'exists accepting certificate is separate', 'verifier_case': 'max over all bounded certificates', 'worst_case': 'max_{x in Phi_n} T_A*(x)'}, composition: {'pantograph': 'state/clock scales multiply; elapsed causal extents do not', 'parallel': 'maximum only with independence/interchange and capacity partition', 'serial': 'addition only under a mandatory serial join'}, tower_naturality: {'global': 'cofinal uniform return, not finite-stage extrapolation', 'law': 'restriction/rebase maps commute with unfolding, clock-ruler, bounds, observers, and admitted successors'}, reconstruction_fibre: {'dynamic_law': 'q T_g = U_g q', 'retains': ['unfoldings', 'schedules', 'paths', 'collapsed resource distributions', 'clock phase', 'separating successor histories']})
````````

Operation: indexed dependent-family lift plus typed clock-ruler constitution

Orientation: forward

Receiver: familywise exact causal extent, P/NP complexity, Hodge/Riemann interface

Boundary: The source is one finite unfolding/apparatus clocked duration. The target is an indexed potential family with distinct time and length quantity lines. No physical length is inferred until a positive addressed clock-ruler constitution is supplied; no family complexity is inferred until uniform quantifiers and schedule/bound certificates are supplied.

Retained fibre: For each shared duration/length/asymptotic face retain every source potential, causal incidence complex, feasible schedule, service allocation, resource/cut pressure, critical path, clock phase, observer chart, and successor history. Any later receiver or generator that separates a collapsed pair reopens the quotient.

Hypotheses: ["Each potential has an admitted finite causal unfolding and at least one feasible schedule.","Every resource capacity and transport latency is an exact addressed constitutive datum.","The time-to-length coefficient occupies L tensor dual(T), not the scalar line.","Worst-case or verifier maxima are taken only after rebasing every duration into one common positive observer line.","Parallel max laws require exact independence/interchange and resource-capacity partition.","A P/NP adapter must preserve Mathlib TM2 polynomial cost uniformly and retain certificate-search history."]

## Passage 10: swing OBJ-3a44ade4-61c7-479c-8820-4153d1f6893d -> OBJ-af4c9156-ba6f-49fb-872e-921f7be358b1

ID: `OBJ-a33533f2-c871-4c26-a18a-29ecd0aa4f55` · original grade: `established-bounded` · 2026-08-29T22:19:34.820175+00:00

Before: `OBJ-3a44ade4-61c7-479c-8820-4153d1f6893d`

````````text
composition(before: U_x, operator: pi_A: algorithmic unfolding -> apparatus micro-realization, operator: S_A: exact resource current and feasible schedule -> least local makespan T_A*, operator: chi_A,O: positive rational local-clock -> observer-clock transport, after: Delta t_O = (m/n) T_A* with quotient-residue phase, reconstruction-fibre: precedence, path latency, resource demand/capacity, service allocation, transport, apparatus projection, clock addresses, quotient Q, phase R)
````````

After: `OBJ-af4c9156-ba6f-49fb-872e-921f7be358b1`

````````text
bracket(source_input: x, uniform_machine: M, encoding_length: |encode(x)|, lower_causal_length: lower_M(x), realized_trace_length: steps_M(x), upper_causal_length: upper_M(x), clock_duration_fibre: DurationFibre_A(x,M))
````````

Operation: index by encoded inputs, anchor to one uniform TM2 computation, and retain lower/actual/upper causal trace lengths; leave apparatus clock duration in a separate addressed fibre

Orientation: per-unfolding-to-uniform-family

Receiver: source-specific P/NP finish-line receiver

Boundary: This swing specifies the smallest audited receiver interface; it proves neither a polynomial upper bound nor a superpolynomial lower bound and does not alter repository sources.

Retained fibre: All per-input unfoldings, feasible schedules, resource laws, causal-path/resource lower certificates, clock-duration realizations, observer charts, and candidate-machine analyses remain explicit fibres behind the family bounds.

Hypotheses: ["fixed source and output encodings","one uniform TM2 computation rather than per-input advice","per-input lower bound applies to the realized TM2 trace","per-input upper bound contains the realized TM2 trace","apparatus clock duration is not identified with trace length"]

## Passage 11: Receiver-indexed causal-length tower formalization swing

ID: `OBJ-736ff42c-e6ae-402b-b3b3-59d156e82aee` · original grade: `proved-derived` · 2026-08-29T22:54:55.047510+00:00

Before: `OBJ-30348ea9-e250-4616-b8d3-328d0e25914b`

````````text
dependent-record(index_family: I : Type, addressed_path_family: P : I → AddressedDirectedPathCategory, boundary_extent: bᵢ : Ob(Pᵢ) → BoundaryLineᵢ, passage_extent: Λᵢ : Mor(Pᵢ) → ∏ a, ExtentLine(i,a), identity_law: Λᵢ(id)=0, serial_law: Λᵢ(g∘f)=Λᵢ(f)+Λᵢ(g), causal_potential_fibre: Φᵢ(x) : feasible addressed continuation histories, clock_ruler_comparison_span: TimeLineᵢ ← Kᵢ → LengthLineᵢ, comparison_reconstruction: mp=nq+r with 0≤r<n, retaining quotient, residue, address, and calibration, scale_rebase: Sᵢⱼ with Λⱼ∘Sᵢⱼ=Rᵢⱼ∘Λᵢ and complete ReconstructionFiber, complexity_receiver: L_M(x)≤steps_M(x)≤U_M(x)≤p(|encode(x)|) uniformly in x, p_equals_np_finish: UniformVerifierCompiler, p_not_equals_np_finish: ConcreteSeparator robust under admitted encodings and polynomial reductions, derived_hodge_mellin_boundary: Hodge and Mellin receivers enter only after their source-specific boundary, metric, positivity, summability, and reconstruction obligations)
````````

After: `OBJ-4183cb84-4787-47cf-88cd-578a9eb835c3`

````````text
formal-construction(typed_extent_lines: {'lean_receivers': ['BoundaryExtent', 'PassageExtent', 'FiniteControl.equal_count_does_not_identify_extent'], 'statement': 'BoundaryExtent and PassageExtent are distinct addressed carrier occurrences even when their Nat coordinates agree.'}, clock_ruler_span: {'lean_receivers': ['ClockRulerSpan.targetState_potential', 'ClockRulerSpan.targetState_add', 'ClockRulerSpan.targetState_injective', 'ClockRulerSpan.reconstructionFibre_subsingleton', 'FiniteControl.quotientOnly_collides_phaseSeparates'], 'statement': 'A positive rational clock passage returns complete quotient-residue ruler state, with injective source crossing reconstruction and an explicit reconstruction fibre.'}, causal_potential_family: {'lean_receivers': ['Tower.CausalPotentialFibre', 'Tower.BoundaryIndexedPotentialFamily', 'Tower.extendPotential', 'FiniteControl.extendedPotential_components'], 'statement': 'Boundary-indexed causal potentials retain every history beginning at a situated boundary and serial extension returns the exact pullback occurrence.'}, serial_composition: {'lean_receivers': ['Tower.clockLength_serial', 'Tower.resourceWork_serial', 'Tower.rulerState_serial', 'Tower.serialReconstructionFibreEquiv', 'Tower.serialAssociatorFibreEquiv'], 'statement': 'Serial clock and resource lengths add while lineage retains both occurrences, their exact joining equality, and complete fibres through associativity.'}, parallel_interchange: {'lean_receivers': ['Tower.ParallelInterchangeReceipt', 'Tower.ParallelInterchangeReceipt.resourceWork_le_capacity_mul_clockLength', 'ParallelControl.receipt_clockLength', 'ParallelControl.noncommutingCell_refuses_interchange'], 'statement': 'Parallel max-clock projection is conditional on an exact commuting comparison cell, braided receiver preservation, obstruction and logical-resource equality, and a concrete capacity partition.'}, scale_rebase: {'lean_receivers': ['ScaleRebase.identity', 'ScaleRebase.comp', 'ScaleRebase.transportInteraction', 'ScaleRebase.compReconstructionFibreEquiv', 'ScaleRebase.transportReceiverPotential'], 'statement': 'Scale passages preserve state, history, receiver, address, extent, resource, ruler phase, stationary histories, and exact pullback joins; composite reconstruction is a dependent sum of intermediate and fine fibres.'}, tm2_cost_bridge: {'lean_receivers': ['EncodingAnchoredCausalLengthFamily.toTM2ComputableInPolyTime', 'EncodingAnchoredCausalLengthFamily.lowerExtent_le_outputSteps', 'TowerTM2Anchor.towerClockLength_eq_outputSteps', 'TowerTM2Anchor.outputReconstructionLift'], 'statement': 'One fixed encoding and finite TM2 identify boundary length with encoded input length and passage length with the actual TM2 output computation steps; one uniform polynomial bound constructs the official polynomial-time receiver.'}, p_np_finish_boundary: {'lean_receiver': 'pEqualsNP_of_uniformEncodingAnchoredVerifierCompiler', 'statement': 'P = NP is not constructed. The remaining terminal route requires an inhabitant of UniformEncodingAnchoredVerifierCompiler plus the separately owed PSubsetNP hypothesis.'})
````````

Operation: Lean construction and kernel verification of the receiver-indexed addressed causal-length tower, finite firing controls, and fixed-encoding TM2 polynomial-time bridge

Orientation: forward: approved causal-length-tower specification to kernel-checked Lean realization

Receiver: Lean kernel and repository official TM2/InP/verifier receivers

Boundary: Exact scope: the two new Lean modules and their imported source owners. UAR, roadmap, construction state, physical calibration, generic schedule realizability, and an unconditional P-versus-NP result are outside this swing.

Retained fibre: Complete fibres are retained by ClockRulerSpan.ReconstructionFibre, Tower.serialReconstructionFibreEquiv, Tower.ParallelInterchangeReceipt.reconstructionFibreEquiv, ScaleRebase.compReconstructionFibreEquiv, Tower.ReceiverReconstructionFibre, and TowerTM2Anchor.OutputReconstructionFibre; no choice-defined inverse or endpoint-only condensation is introduced.

Hypotheses: ["Mathlib and repository foundation imports are admitted source owners.","Boundary and passage extents remain different situated types.","Serial composition is AddressedPassage.Join and retains the joining equality.","Parallel max-length is available only under the explicit ParallelInterchangeReceipt.","Scale rebases carry complete history reconstruction fibres.","TM2 cost is the actual TM2Outputs.steps for one fixed encoding and machine.","No inhabitant of UniformEncodingAnchoredVerifierCompiler is asserted."]

## Passage 12: Critical diagonal cancels shell shrinkage against frequency growth

ID: `OBJ-f6a7aeba-da86-419d-95c4-8aa831a895f1` · original grade: `proved-derived` · 2026-08-30T01:21:56.261587+00:00

Before: `OBJ-db77160b-0f39-4db9-a4b9-1cb7e4a34017`

````````text
equation-left(factor: {'arguments': ['T', {'arguments': [{'arguments': [2, 'j'], 'op': 'mul'}, 2], 'op': 'add'}], 'function': 'terminalDyadicRadius'}, factor: {'base': {'arguments': [{'arguments': ['j', 1], 'op': 'add'}], 'function': 'dyadicRadius'}, 'exponent': 2})
````````

After: `OBJ-45c91bdf-2af4-45d5-b2c8-7729d5f80aad`

````````text
{'quantity_line': 'terminal-duration', 'symbol': 'T'}
````````

Operation: Substitute terminalDyadicRadius(T,n)=T·2^(-n), dyadicRadius(m)=2^m, n=2j+2, and m=j+1; cancel the exact powers of two.

Orientation: left-to-right

Receiver: critical diagonal heat exponent

Boundary: This proves only the scale-time product identity for the chosen dyadic shell mode; it does not assert any nonlinear Navier--Stokes decay.

Retained fibre: The separate shell index k=2j, Hodge scale j, frequency N=2^(j+1), heat eigenvalue (2π)^2N^2, viscosity ν, terminal duration T, and mode amplitude remain recoverable.

Hypotheses: ["T is a real terminal duration","j is a natural dyadic scale","the terminal shell index is k=2j","the chosen shell frequency is N=dyadicRadius(j+1)"]

## Passage 13: Periodic shear exposes the quartic amplitude obstruction

ID: `OBJ-6dacef78-5654-4352-b73e-6d1a202a0ba4` · original grade: `counterexample` · 2026-08-30T01:22:22.852209+00:00

Before: `OBJ-5d0f0966-cd4c-4ab7-a155-e7df7ab60d6b`

````````text
quotient(numerator: {'domain': 'I^+_{2j}', 'integrand': 'Q_{B,N}(t)'}, denominator: {'domain': 'I^+_{2j}', 'integrand': 'D_{B,N}(t)'})
````````

After: `OBJ-c750a5c3-8e5b-42ad-8e30-839c5a80c925`

````````text
{'arguments': [{'rational': {'denominator': 8, 'numerator': 3}}, {'arguments': ['B', 2], 'op': 'pow'}, {'arguments': [{'arguments': [{'arguments': [8, {'power': 2, 'symbol': 'pi'}, 'nu', 'T'], 'op': 'mul'}], 'op': 'exp'}, 1], 'op': 'add'}], 'op': 'mul'}
````````

Operation: Insert u_{B,N}(x,t)=(0,B exp(-ν(2πN)^2(t-b)) sin(2πNx₁),0), integrate cos^4 and sin^2 over the unit torus, integrate time from a=b-δ to b, and use N=2^(j+1), δ=T/N^2.

Orientation: left-to-right

Receiver: amplitude obstruction to quartic enstrophy-shell absorption

Boundary: This refutes a solution-uniform absorption remainder whose terminal-shell allowance has subquartic amplitude growth or is independent of the restarted amplitude. It does not refute a solution-dependent quartic remainder; summability of that remainder is precisely the unavailable terminal estimate.

Retained fibre: The exact solution, initial amplitude B exp(ν(2πN)^2 b), Q integral, D integral, terminal shell endpoints, frequency address N, and separate amplitude/frequency scalings remain recoverable.

Hypotheses: ["ν>0","T>0","j is natural","N=2^(j+1)","δ=T/N^2","I^+_{2j}=(b-δ,b] is the terminal shell","B>0","the zero-force periodic shear has pressure zero and vanishing advective term"]

## Passage 14: actual source Dini fibre equals native fibre

ID: `OBJ-40071928-ce0e-4e3d-aae2-b5777265330a` · original grade: `proved-derived` · 2026-08-30T04:55:23.486827+00:00

Before: `OBJ-8584b3e8-caee-4a6e-a838-3e36634a02bf`

````````text
addressed-functional-occurrence(source: openSharpSourceDiniReconstructionFiber, target_clock: t0 + targetTime, horizon: horizon, integrand: norm(source(target-elapsed)-source(target))/elapsed)
````````

After: `OBJ-58713645-8ab5-4e61-b6e0-caad9e881923`

````````text
addressed-functional-occurrence(source: nativeSharpSourceDiniFiber, target_clock: t0 + targetTime, horizon: horizon, integrand: norm(source(target-elapsed)-source(target))/elapsed)
````````

Operation: open-slice native-overlap state transport and exact ENNReal lintegral congruence

Orientation: actual-open-source fibre -> native restart fibre

Receiver: literal actual nonlinear-source Dini reconstruction fibre

Boundary: one admitted native restart overlap; no terminal-uniform passage as T is approached

Retained fibre: the dependence on restart base, overlap radius, source time jet, and absent terminal-uniform coefficient is retained

Hypotheses: ["positive viscosity","strict-interior restart base","closed target subaperture lies below the native uniqueness overlap","0 < horizon < targetTime"]

## Passage 15: actual clocked pantographic vorticity-band swing

ID: `OBJ-7cbd18e6-37a9-4298-a125-4f5f03043b79` · original grade: `proved-derived` · 2026-08-30T05:18:33.776379+00:00

Before: `OBJ-3af0a2c6-a8d4-4e3f-a6eb-f452fb742487`

````````text
equality(left: compactMildSourceIntegratedCoefficient solution hs hst ht k, operator: =, right: signed-sum(chain: compactPantographicPartialChainIntegratedCoefficient solution hs hst ht depth k, residual: compactPantographicResidualIntegratedCoefficient solution hs hst ht depth k, boundary: compactPantographicFrozenBoundaryCoefficient solution hs hst ht k))
````````

After: `OBJ-433844c3-e3e3-46d8-9241-4e048f3aefb9`

````````text
equality(left: openPeriodicVorticityBandProjector solution targetTime modes, operator: =, heat_face: compactInitialVorticityHeatBand solution hs hst ht modes, difference: -, transported_population: signed-sum(chain_band: compactPantographicPartialChainIntegratedBand solution hs hst ht depth modes, residual_band: compactPantographicResidualIntegratedBand solution hs hst ht depth modes, boundary_band: compactPantographicFrozenBoundaryBand solution hs hst ht modes))
````````

Operation: finite signed Fourier synthesis followed by the exact compact mild vorticity identity

Orientation: coefficientwise transported source swing -> actual finite spatial vorticity band

Receiver: finite phase-bearing torus aperture; in particular dyadicFrequencyShell level

Boundary: No spatial norm, cross-scale sum, or terminal-time integral is asserted by this swing. The residual and frozen boundary remain explicit.

Retained fibre: Finite-depth pantographic residual, earlier heat face, frequency addresses, Fourier phases, and the complete finite aperture are retained.

Hypotheses: ["0 < nu","0 < s","s <= t","t < T","finite modes","finite pantographic depth"]

## Passage 16: swing OBJ-b9858cb6-1ed8-4c2f-be5d-569f86ac8303 -> OBJ-1e23234d-7d6b-43fd-b6af-bbda3c1659c8

ID: `OBJ-e694c2ee-01f5-4497-87f9-272155fbc524` · original grade: `counterexample` · 2026-08-30T10:32:29.744915+00:00

Before: `OBJ-b9858cb6-1ed8-4c2f-be5d-569f86ac8303`

````````text
bracket(endpoint_energy: M_0(n), integrated_energy_dissipation: Integral_[0,M_2(n)^-1] M_1(n) dt, integrated_enstrophy_dissipation: Integral_[0,M_2(n)^-1] M_2(n) dt)
````````

After: `OBJ-1e23234d-7d6b-43fd-b6af-bbda3c1659c8`

````````text
bracket(required_square_current: Integral_[0,M_2(n)^-1] M_3(n) dt, exact_singleton_return: M_1(n))
````````

Operation: reciprocal-order-two clock aperture scaling separator

Orientation: lower-current budget does not uniformly pay required order-three current

Receiver: endpoint-uniform temporal payment of the adaptive nonlinear-source square owner

Boundary: Scaling receiver only; not a Navier-Stokes solution and not a blow-up construction. No claim about realizability of the singleton family as one nonlinear trajectory.

Retained fibre: A terminal-uniform passage remains open only through actual integrated order-three spatial square current, the viscous current of an order-two energy, or a constitutive estimate controlling it. Lower endpoint H0 plus integrated H1 and even granted integrated H2 remain insufficient.

Hypotheses: ["single addressed axial Fourier occurrence","clock duration equals reciprocal order-two Sobolev mass","inhomogeneous periodic Sobolev weights","kernel-checked Lean source hash c63be029d936eb8e435c262ec42d449a865de426583b618f10c3fdac05649ce9"]

## Passage 17: calibrated H2 exchanged-triad multiplier swing

ID: `OBJ-e86e759e-57f9-4691-b50d-8d8c5ac493a7` · original grade: `proved-derived` · 2026-08-30T11:32:27.690755+00:00

Before: `OBJ-f42107ae-499a-4015-b0fe-0a3c2955e960`

````````text
(1+lambda(q))*Face(p,q,r)+(1+lambda(r))*Face(p,r,q)
````````

After: `OBJ-20e1323e-ffb0-4127-bd1f-031d678171b2`

````````text
(lambda(q)-lambda(r))*Face(p,q,r)
````````

Operation: 

Orientation: forward

Receiver: finite divergence-free exchanged Fourier-triad H2 current

Boundary: finite addressed triad; no infinite convolution sum, terminal limit, or absolute-mass quotient

Retained fibre: three addressed pins, oriented complex triadic face, turn calibration, divergence witness, pre-cancellation pair, and pre-absolute phase population

Hypotheses: ["p+q+r=0","complexDot(complexFrequencyVector p,u_p)=0","full-turn scale supplied by TurnCalibration"]

## Passage 18: H2 shell lever through adjacent smooth dyadic multiplier product

ID: `OBJ-c617dfc5-42ae-44d8-a0bc-53f1516e0e45` · original grade: `proved-derived` · 2026-08-30T11:55:03.153143+00:00

Before: `OBJ-94707684-e825-4e97-91b2-dded358ded57`

````````text
inequality(left: abs(torusStokesEigenvalue(q)-torusStokesEigenvalue(k)), relation: ≤, right: ordered-product(scale: primitiveTorusStokesScale, coefficient: 6, low-length: dyadicRadius(lowLevel+1), high-length: dyadicRadius(highLevel+1)))
````````

After: `OBJ-497a4746-368d-449d-ac02-bcd7f57922f6`

````````text
equality(left: T_H2,j + T_H2,j+1, relation: =, right: T_H2)
````````

Operation: discrete multiplier product rule followed by adjacent smooth-boundary cancellation

Orientation: shell-local signed transfer to adjacent-band reconstruction

Receiver: formal H2 dyadic product-swing equality

Boundary: one divergence-free addressed closed Fourier triad; transported and receiver pins lie in dyadicFrequencyShell (j+1); finite signed transfer before norm and population sum

Retained fibre: Infinite triad summation, coefficient-amplitude payment, cross-shell boundary flux, comparable unequal-radius interactions, time integration, endpoint-uniform service, and the official continuation receiver remain open.

Hypotheses: ["complexDot(complexFrequencyVector p, u_p)=0","q and r occupy dyadicFrequencyShell (j+1)","adjacent smooth band weights at j and j+1 add to one on that shell"]

## Passage 19: Actual H2 triad shell lever swings into finite separated population bound

ID: `OBJ-05e526c3-ac6a-43f9-85bf-1f104fb1fc3a` · original grade: `proved-derived` · 2026-08-30T12:08:15.649866+00:00

Before: `OBJ-22bd2be8-41cd-4f30-a0ae-ab978744461f`

````````text
inequality(left: norm(h2ExchangedTriadTransfer(triad,actualModes)), relation: ≤, right: primitiveTorusStokesScale * 6 * dyadicLowHighLengthRatio(lowLevel,highLevel) * dyadicRadius(highLevel+1)^2 * norm(triadicEnergyFace(actualModes)))
````````

After: `OBJ-30b0c0e4-5a08-4c9d-8902-0c908272d059`

````````text
inequality(left: norm(current: separatedH2TriadPopulationCurrent(highLevel,population,actualModes)), relation: ≤, right: ordered-product(primitive-stokes-scale: primitiveTorusStokesScale, coordinate-factor: 6, high-shell-square: dyadicRadius(highLevel+1)^2, ratio-weighted-occurrence-mass: sum_(lowLevel<highLevel) dyadicLowHighLengthRatio(lowLevel,highLevel) * sum_(triad in population(lowLevel)) norm(triadicEnergyFace(actualModes(lowLevel,triad)))), reconstruction-fibre: ordered-pair(admitted-occurrences: sigma(lowLevel in range(highLevel), population(lowLevel)), excluded-comparable-and-higher: offset ↦ population(highLevel+offset)))
````````

Operation: shell-addressed finite sigma population junction, nested norm triangle receiver, and exact dyadic row summation

Orientation: single actual high--high--low interaction -> finite strictly separated occurrence population

Receiver: finite H2 separated-population norm and common shell-face-mass receiver

Boundary: Only finite populations at lowLevel < highLevel are summed. The theorem applies the norm after the actual signed complex-current junction. It proves neither an infinite-population estimate nor the complete nonlinear Navier--Stokes production bound.

Retained fibre: The dependent sigma atlas retains every `(lowLevel, triad)` occurrence and exact cardinality. `comparableAndHigherTriadPopulationFiber highLevel population offset = population (highLevel + offset)` retains the excluded comparable shell at offset zero and all higher shells. Comparable/high--high--high interactions, phase cancellation lost by the norm receiver, and the passage to actual solution Fourier-mode convolution remain open.

Hypotheses: ["every admitted lowLevel lies in Finset.range highLevel","every admitted occurrence is an AddressedClosedFourierTriad","the advecting mode is divergence-free at its actual advecting frequency","the advecting frequency lies in dyadicFrequencyShell lowLevel","the transported and receiver frequencies lie in dyadicFrequencyShell highLevel","for the uniform corollary, each complete low-shell face mass is bounded by the same nonnegative M"]

## Passage 20: Completed physical H2 curl multiplier factorization

ID: `OBJ-fcafe889-2a84-4a03-acec-b67ebf15d31c` · original grade: `proved-derived` · 2026-08-30T12:12:53.972852+00:00

Before: `OBJ-95433976-23cd-4f62-94ed-692c3c0230dd`

````````text
difference(transported_weight: sum(order_one: lambda_q, order_two: power(base: lambda_q, exponent: 2)), receiver_weight: sum(order_one: lambda_r, order_two: power(base: lambda_r, exponent: 2)))
````````

After: `OBJ-173ec6f2-c06c-41ac-a28a-62082129391d`

````````text
product(pantographic_difference_lever: difference(transported_stokes_coordinate: lambda_q, receiver_stokes_coordinate: lambda_r), symmetric_physical_curl_scale: sum(storage_unit: 1, transported_stokes_coordinate: lambda_q, receiver_stokes_coordinate: lambda_r))
````````

Operation: commutative polynomial factorization of the literal two-order velocity-chart multiplier difference

Orientation: transported-minus-receiver, before coefficient mass

Receiver: physical H2 curl-energy exchanged triad current

Boundary: single addressed closed Fourier triad; finite algebraic exchange before infinite convolution, norm, time integration, or terminal continuation

Retained fibre: Retains the vorticity-chart test-factor swing 1+lambda, the separate leading curl-curl lambda factor, transported and receiver Stokes coordinates, the advecting-pin pairing lever, the oriented triadic energy face, primitive lattice calibration, equal-radius null fibre, and all comparable/high-high-high interactions excluded by the later dyadic receiver.

Hypotheses: ["triad.advecting + triad.transported + triad.receiver = 0","complexDot(complexFrequencyVector triad.advecting, advectingMode) = 0","lambda(k) = torusStokesEigenvalue(k)","physical velocity-chart multiplier = lambda(k) + lambda(k)^2"]

## Passage 21: Intrinsic calibrated triadic face to ordered pointwise L1 bound

ID: `OBJ-aaff4c66-1d42-4fab-b9d5-f3cf3147fc1c` · original grade: `proved-derived` · 2026-08-30T13:23:09.986868+00:00

Before: `OBJ-2dce460b-98d0-4038-966d-d7a5f6345500`

````````text
norm(subject: calibratedTriadicEnergyFace(calibration: {'name': 'calibration', 'type': 'TurnCalibration'}, advecting-frequency: {'name': 'advectingFrequency', 'type': 'SpatialFrequency'}, transported-frequency: {'name': 'transportedFrequency', 'type': 'SpatialFrequency'}, advecting-mode: {'name': 'advectingMode', 'type': 'ComplexVector'}, transported-mode: {'name': 'transportedMode', 'type': 'ComplexVector'}, receiver-mode: {'name': 'receiverMode', 'type': 'ComplexVector'}))
````````

After: `OBJ-b7ad2085-0a5f-4d71-bbb3-4a9cf538e4ef`

````````text
ordered-product(turn-carrier: fullTurn(calibration: {'name': 'calibration', 'type': 'TurnCalibration'}), transported-frequency-length: frequencyL1(transported-frequency: {'name': 'transportedFrequency', 'type': 'SpatialFrequency'}), advecting-mode-length: complexVectorL1(advecting-mode: {'name': 'advectingMode', 'type': 'ComplexVector'}), transported-mode-length: complexVectorL1(transported-mode: {'name': 'transportedMode', 'type': 'ComplexVector'}), receiver-mode-length: complexVectorL1(receiver-mode: {'name': 'receiverMode', 'type': 'ComplexVector'}))
````````

Operation: kernel-checked ordered L1 norm transport under the intrinsic full-turn derivative current

Orientation: norm-to-majorant

Receiver: Pointwise real L1 majorant retaining turn, transported frequency, advecting mode, transported mode, and receiver mode in order.

Boundary: One transported-frequency Fourier interaction and three ordered ComplexVector occurrences at one fixed TurnCalibration; no triad population, shell summation, time integration, terminal trace, or continuation statement.

Retained fibre: Retain the complete calibrated complex interaction and triadic face, all three component populations of each ComplexVector, the transported frequency coordinates, arc partition, positive radial scale, complex phase discarded by norm, triangle-inequality slack, and the separate Euclidean-circle decoding witness. The majorant is not an inverse decoder.

Hypotheses: ["calibration.partition.arcLength_nonneg at every addressed arc occurrence","calibration.radialScale_pos","the established complex dot L1 inequality","the established complexVectorL1 scalar-action equality","the established complex-frequency L1 decoding equality"]

## Passage 22: finite receiver-weighted physical H2 velocity current to negative half completed exchange current

ID: `OBJ-eee250b5-2431-48c3-8b6e-fecf42d1d70c` · original grade: `proved-derived` · 2026-08-30T13:32:29.017576+00:00

Before: `OBJ-2baf1692-13d4-4bc9-ae6f-6056e2e7b4d2`

````````text
finite-current(finite-address-population: physicalH2VelocityTriadAperture radius, receiver-weighted-face: ordered-product(receiver-multiplier: physicalH2CurlEnergyMultiplier (completeTransportReceiver address), oriented-triadic-face: triadicEnergyFace address.1 address.2 (velocityMode address.1) (velocityMode address.2) (velocityMode (completeTransportReceiver address))))
````````

After: `OBJ-91fa0b16-9e74-4b4b-9de0-3cb375c7d807`

````````text
scalar-action(situated-rational-coordinate: rational-face(oriented-numerator: -1, denominator: 2), finite-exchanged-current: finite-current(finite-address-population: physicalH2VelocityTriadAperture radius, completed-exchanged-face: physicalH2ExchangedTriadTransfer (completeTransportTriad address) (velocityMode address.1) (velocityMode address.2) (velocityMode (completeTransportReceiver address))))
````````

Operation: completeTransportExchange plus physicalH2ExchangedTriadTransfer

Orientation: transported/receiver exchange followed by finite reindexing

Receiver: finite exchange-invariant three-pin frequency-cube receiver retaining address multiplicity

Boundary: finite CompleteTransportAddress population only; no infinite convolution, cofinal limit, time integration, or Navier-Stokes continuation consequence

Retained fibre: all ordered address occurrences, all three frequency pins, the complete physical H2 multiplier on each exchanged pin, the complex triadic face, and the divergence-free witness remain reconstructible

Hypotheses: ["every retained advecting, transported, and receiving frequency lies in one frequencyCube radius","the velocityMode is divergence-free on that cube","completeTransportExchange preserves the finite aperture","the exchanged triadic energy faces are antisymmetric"]

## Passage 23: Physical H2 cyclic transfer to multiplier coboundary

ID: `OBJ-310720b9-418d-4949-a409-823bafdc4e7f` · original grade: `proved-derived` · 2026-08-30T13:41:54.144964+00:00

Before: `OBJ-9b076473-b5ec-4f5e-b692-f25c9647dfe2`

````````text
ordered-sum(term: T_p=(M(q)-M(r))A, term: T_q=(M(r)-M(p))B, term: T_r=(M(p)-M(q))C)
````````

After: `OBJ-603dd85a-5b1b-4f0a-ae6a-c03417463400`

````````text
ordered-sum(term: product(multiplier: M(p), returned_difference: difference(positive_face: C, negative_face: B)), term: product(multiplier: M(q), returned_difference: difference(positive_face: A, negative_face: C)), term: product(multiplier: M(r), returned_difference: difference(positive_face: B, negative_face: A)))
````````

Operation: closed-triad exchanged-face cancellation at each of three advecting pins, followed by cyclic coefficient collection

Orientation: cyclic-forward

Receiver: signed complex triadic physical H2 receiver before norms

Boundary: One addressed closed triad and its three rotated divergence-free velocity-mode faces; no convolution sum, norm, time integral, or terminal receiver.

Retained fibre: The three distinct oriented faces A, B, C, their mode and pin incidences, all comparable-scale occurrences, and the explicit nonzero counterexample remain retained.

Hypotheses: ["p+q+r=0 in the integer frequency lattice","p dot u=0, q dot v=0, and r dot w=0","M is the completed physical H2 multiplier for the physical specialization"]

## Passage 24: physical H2 velocity cube exhaustion swing

ID: `OBJ-36f3ad02-f995-4ef4-8226-bc4d286ecdf5` · original grade: `proved-derived` · 2026-08-30T13:57:22.603342+00:00

Before: `OBJ-b100043c-15db-4314-b9a5-b41347ee2bda`

````````text
finite_sum_receiver(radius: R, population: CompleteTransportAddress with p,q,r in frequencyCube(R), face: physicalH2VelocityExchangedTriadFace, receiver: (1/2) * re(sum))
````````

After: `OBJ-4e6cf7d4-46e1-4c03-b804-5e1a13be1e2c`

````````text
complete_current_receiver(source: openActualAdvectionMode(solution,t,k), test: openPeriodicVelocityFourierMode(solution,t,k), multiplier: physicalH2CurlEnergyMultiplier(k), receiver: homogeneousCoordinateH2ModeWork, population: tsum over SpatialFrequency)
````````

Operation: common-three-pin cube cofinal exhaustion; completed-multiplier H3 absolute summability; output/parent Fubini; actual-advection fibre identification; Fourier-reality real receiver

Orientation: forward

Receiver: positive one-half real completed exchange to complete physical H2 velocity-advection current

Boundary: Fixed strict-interior time only. No terminal limit, time-uniform estimate, continuation theorem, or absolute-value replacement of the signed current.

Retained fibre: Retains every CompleteTransportAddress, both independent parent pins, the closed receiver pin, common cube radius, output/parent joining equality, complex raw phase, negative-real physical-current orientation, and exact finite exchange sign.

Hypotheses: ["OpenPeriodicSolutionOn T nu initial 0 velocity pressure","strict-interior time t in (0,T)","existing exact finite divergence-free exchange identity","smooth solution slice supplies the laplacian-squared-minus-laplacian H3 carrier"]

## Passage 25: finite unique-low cyclic rotation and least-pin derivative reorientation

ID: `OBJ-7016bd3e-6af1-4fad-8b53-e7ce35f7bbd3` · original grade: `proved-derived` · 2026-08-30T14:01:21.625873+00:00

Before: `OBJ-1082b553-a804-4fb5-aee9-8dca60cfbe1f`

````````text
finite physical H2 velocity current in four unique-low sectors
````````

After: `OBJ-8e8c9ec8-c187-4cc3-9e09-1bddbee9f107`

````````text
advecting-low cyclic orbit reoriented through least pin plus comparable residue
````````

Operation: complete address rotation followed by closed-triad divergence exchange

Orientation: advecting-low chart; positive cyclic order p→q→r→p

Receiver: Lean exact-equality receiver followed separately by calibrated norm receiver

Boundary: finite common three-pin cube only; comparable sector retained; no infinite limit or absorption

Retained fibre: Inverse rotations recover transported-low and receiver-low source occurrences exactly; retain original address, three pins, three velocity modes, each oriented face, sector proof, common cube membership, the signed cyclic coboundary, and the comparable residue.

Hypotheses: ["all three pins lie in the same finite frequency cube","velocity modes are divergence-free on that cube","the three unique-low predicates are pairwise disjoint and exhaustive with the comparable predicate"]

## Passage 26: Own-mode Hermitian projective clock

ID: `OBJ-b8c93af6-ed9e-48e5-82c1-615aef80aaf1` · original grade: `proved-derived` · 2026-08-30T16:19:27.936308+00:00

Before: `OBJ-9774a15f-58aa-400b-8c43-cd42aad532c5`

````````text
application(operator: modeHermitianPhase, receiver: Omega_k, source: S_k)
````````

After: `OBJ-68bc7da2-334d-4f28-905b-d63d878e3fbe`

````````text
application(operator: modeHermitianPhase, receiver: Omega_k, source: J_k)
````````

Operation: Apply modeHermitianPhase Omega_k and remove the aligned viscous Stokes occurrence.

Orientation: source-to-time-jet

Receiver: own Fourier-mode Hermitian phase receiver

Boundary: One Fourier address and one time occurrence of an unforced OpenPeriodicSolutionOn; exact phase identity only, with no norm estimate, phase payment, terminal control, or continuation claim.

Retained fibre: The aligned viscous occurrence ((nu * lambda_k):C) • Omega_k is retained. At Omega_k = 0, no division is cancelled: the complete nonlinear source and complete time jet are proved equal and remain distinct situated occurrences.

Hypotheses: ["S_k = J_k + ((nu * torusStokesEigenvalue k : R) : C) • Omega_k","Omega_k is the contemporaneous physical vorticity Fourier coefficient","modeHermitianPhase uses the exact Hermitian pairing and a totalized quotient"]

## Passage 27: swing OBJ-8446ace4-d11f-4c3e-9084-3e1c54f7850c -> OBJ-d1ab10c9-5c1a-4229-be7c-8db0a07a32ce

ID: `OBJ-74b62066-aa71-4089-99c2-7bca0dd64928` · original grade: `proved-derived` · 2026-08-30T16:29:17.639215+00:00

Before: `OBJ-8446ace4-d11f-4c3e-9084-3e1c54f7850c`

````````text
derivative(operator: d/dt, operand: L_t(K_k(w(t) Omega(t))))
````````

After: `OBJ-d1ab10c9-5c1a-4229-be7c-8db0a07a32ce`

````````text
sum(variation: L'_t(K_k(w(t) Omega(t))), horizontal_current: L_t(K_k(w(t) H(t))))
````````

Operation: Hermitian connection cancellation followed by the time-varying continuous-linear-map product rule

Orientation: forward

Receiver: literal real-clock derivative of the exact outer-Hodge transported mode

Boundary: Finite complex vorticity mode, exact standing Hodge reconstruction, and one real clock; no bound, viscosity absorption, terminal control, or closure.

Retained fibre: The zero-mode fibre retains the full OmegaJet; endpoint b and the entire LJet remainder remain explicit; alternate transport scalars satisfying the same local derivative law are not identified.

Hypotheses: ["HasDerivAt Omega OmegaJet at t","HasDerivAt w (-a*w) at t with a=<Omega,OmegaJet>/<Omega,Omega>","HasDerivAt L LJet at t"]

## Passage 28: swing OBJ-18e230ed-f223-4734-85ef-6f00515b271a -> OBJ-9512305c-7df9-43f9-a129-9ab074389d02

ID: `OBJ-dbbfbdab-0c1b-4cfd-85d0-fcba5847d06d` · original grade: `proved-derived` · 2026-08-30T16:40:23.814023+00:00

Before: `OBJ-18e230ed-f223-4734-85ef-6f00515b271a`

````````text
equation(left: B', horizontal: H_horizontal, nonlinear: N_outer, damping: -Omega_outer*B)
````````

After: `OBJ-9512305c-7df9-43f9-a129-9ab074389d02`

````````text
equation(left_derivative: (1/2 |B|^2)', positive_damping: +Omega_outer |B|^2, nonlinear_power: Re(conj(B) N_outer), horizontal_power: Re(conj(B) H_horizontal))
````````

Operation: real half-norm-square receiver applied to the exact complex scalar clock law

Orientation: forward

Receiver: real coercive-candidate receiver retaining both signed source powers

Boundary: One addressed insertion leg. Positivity applies only to Omega_outer*|B|^2 when viscosity and address hypotheses fire; neither source power is assigned a sign.

Retained fibre: Retain B, N_outer, H_horizontal, the complex phases lost by Re, the transported carrier z=w*Omega, the full pair (w,Omega) with w*Omega=z, and the zero-B/nonzero-B' fibre.

Hypotheses: ["HasDerivAt B (H_horizontal + N_outer - (Omega_outer:Complex)*B) at t","Omega_outer is real","the complex norm square is read through the real Hermitian pairing"]

