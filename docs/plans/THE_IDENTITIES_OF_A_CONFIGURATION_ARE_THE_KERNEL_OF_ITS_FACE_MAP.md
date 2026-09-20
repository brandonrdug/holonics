# The identities of a configuration are the kernel of its face map

[definition] This is a construction contract subordinate to [THE_ROADMAP](THE_ROADMAP.md). It
designs the **identity atlas**: an algorithmically generated, exactly certified graph of the
identities of a configuration family, their relations, their collapses into simpler geometries,
and the landmark constants they force. It adds no milestone by itself and founds an owner only
for the concrete absent object each intention names. Classical results are `proved-standard` with
their names inline; the wider assembly retains its stated open obligations after the bounded
first instance. GitHub's geometry/reuse milestone tracks the return; this contract does not
create a separate construction order.

## Existing construction and the returned subset

[established-bounded; source-inspected] Wave 10 returned `identity_atlas` and
`Geometry/TwoSidedIdentityAtlas.lean`: exact polynomial operations, chart-relative kernel
certification, polynomial completion, special-fibre comparisons and the displayed T0–T2
identities. The [Wave 10 audit](../../research/records/2026-09-20_WAVE_TEN_IS_REPAIRED_AND_THE_LIBRARY_RETURNS_TO_HELICAL_GENERATORS_AND_HNN.md)
repairs certificate construction, unresolved returns and chart/matroid bounds. Coverage of an
ambient variety is a separate source statement: a caller's prose is not a proof. T2's current
return concerns the declared Gram chart; the shared [helical geometry](../HELICAL_GEOMETRY.md)
provides its actual screw-form consumer and the orbit/contact geometry it previously omitted.

[definition] I7/I8 continue existing subjects. `LandmarksAndModuli`, `Farey`, `Polarity` and
`winding_inertia` own period/modulus and branch/winding returns. `PiIterationConstraint`,
`MachinPhaseConstraint` and exact analytic owners carry π/e generators; the Copson–de Bruijn
and de Bruijn–Newman families have distinct source laws. `GeneratorInference`,
`GeneratorModeQuotient`, `ReceiverHistoryCompression`, `ReceiverCodeCost`, quadratic moments and
the native factor/receiver owners already supply inferred families, sufficient continuation and
encoding equations. The [September synthesis](../MATHEMATICS_AND_NATIVE_CONDUCT.md#constraint-defined-modes-and-named-de-bruijn-boundaries)
and [helical source map](../HELICAL_GEOMETRY.md#landmarks-and-holonic-compression-already-have-owners)
locate them. This atlas adds a polynomial relation-finding operation; it neither establishes
those subjects for the first time nor completes their native composition by citing them.

## The governing statement

[project-postulate] Brandon, September 19: walk a graph that can be generated algorithmically and
converges on all known trigonometric and geometric identities and their relationships — there are
finitely many relationships and constraints; find landmark constraint faces such as `π`, `e` and
the de Bruijn–Newman constant automatically; do it for the
[helical pair](../../research/records/2026-09-19_THE_TRIGONOMETRY_OF_A_HELICAL_PAIR_IS_TRIGONOMETRY_OVER_A_TWO_SIDED_ANGLE.md)
so that no identity can be missed, because deriving them by hand is exhausting in the literal
sense of resources. It is auto-formalization and a solver, an application of HNNs, and not a side
application: it is the same concept as fractal generators — convergent paths into real
commonalities, with familial and group characteristics and their phase distributions — and it is
the way to nail Holonic Compression.

## Why the intuition is right, and where it stops

[proved-standard] **Finiteness.** For polynomial and rational identities the intuition is a
theorem three times over. The identities among a finite receiver family on a configuration form an
ideal, and every ideal of a polynomial ring is finitely generated (Hilbert's basis theorem). The
relations among those generators admit a finite free resolution over the base polynomial ring,
of length at most its variable count (Hilbert's syzygy theorem); this does not assert the same
bound over an arbitrary quotient ring. And completion to a confluent
rewriting system — Buchberger's algorithm, which is Knuth–Bendix completion for commutative
algebra — halts for a supplied finite ideal presentation (Dickson's lemma). Buchberger's
criterion certifies a Gröbner basis **of the ideal supplied**; a separate equality with the
face-map kernel is required to certify every identity. Polynomial trigonometry is the smallest
case: every polynomial identity among sines and cosines of integer combinations of independent
angles follows from one relation per angle, `c² + s² = 1`, and the group law.

[proved-standard] **Discovery and verification have different costs.** Random polynomial
evaluation supplies a one-sided test under the Schwartz–Zippel hypotheses; exact substitution or
ideal membership supplies a certificate. Computing the normal form and storing its certificate
can themselves be expensive. General circuit identity-test derandomization is tied to circuit
lower bounds (Kabanets–Impagliazzo); Gröbner computations and real quantifier elimination have
severe worst-case growth. This is a search/certificate distinction in the spirit of
[the Millennium frame](../canon/THE_MILLENNIUM_FRAME.md), not a general polynomial-cost guarantee.
Mechanical geometry supplies related constructions: Wu's
method, the area and full-angle methods, and the Chou–Gao–Zhang deductive database, which forward
chains a configuration to the **fixpoint** of all its derivable properties.

[proved-standard] **Where it stops.** Identity of general expressions in `exp`, `sin`, `|·|`, `π`
is undecidable (Richardson). It becomes decidable for the structured classes that matter here:
**holonomic (D-finite) functions**, represented by an annihilating operator and initial data, are
closed under sum, product and integration. On a declared nonsingular chart with effective exact
initial data, equality of the represented solutions can be certified by an annihilator and
uniqueness; singularities and initial data are explicit in the
[Ore-algebra representation](https://www.algebra.uni-linz.ac.at/people/mkauers/ore_algebra/generated/ore_algebra.dfinite_function.html).
A Wilf–Zeilberger certificate for an applicable hypergeometric identity supplies its rational
telescoping relation together with the needed boundary conditions. Relations
among **periods** are conjecturally generated by three moves — additivity, change of variables,
Stokes (Kontsevich–Zagier) — which is this document's graph walk stated as an open conjecture.
Group word problems are undecidable in general; the finite strata are tables and the rest is
navigation.

## The design

[definition] **An identity is two constructions with one face.** For a configuration variety `V`,
a finite receiver family `F = {f₁ … f_m}` and a degree `d`, let `Mon_d(F)` be the monomials of
degree at most `d` in the `f_j` and let the **face map** send a formal combination to the function
it denotes on `V`. Its kernel `Id_d(V, F)` is the identities — the operations tablet's collapsed-pair
population, `4 = 2+2 = 2² = 2·2` as linear algebra. Everything below computes, certifies, organizes
and uses that kernel.

**I1 — Configurations with exact points.** A configuration declares its generators and relations
(a group `G_k`, a variety, a linkage), its symmetry group `Γ`, a **rational parametrization** that
yields exact sample points (half-angle parameters, Cayley-parametrized motors, the Study quadric),
with an explicit parameter domain, nonvanishing denominators and coverage/density certificate
for every component of V on which an identity is claimed, and its **collapses**: maps to simpler
configurations (`δ → 0`, `k → 0`, a side projection,
coincident axes). Configurations and collapses form the tube this atlas is indexed by. Owners to
compose: `algebraic.rs` (finitely presented coordinate algebras), `structure_group`,
`TransportWord`, `multiquadratic.rs`.

**I2 — Discovery by exact kernel.** Evaluate `Mon_d(F)` at `N` exact points to get
`E ∈ ℚ^{N × |Mon_d|}` and take `ker E` with `exact_linear::kernel_basis`. Every true identity lies
in `ker E` for valid samples, so this is a candidate **space**, not an assertion that each true
identity appears as a returned basis vector. Finite sampling may leave spurious directions.
Until I3 certifies the entire basis, `rank E` is only the sampled rank, a lower bound on the
dimension of the received polynomial filtration. After certification, it equals that dimension;
for a compatible grading this is the cumulative Hilbert function through degree d, not the
single graded piece. One sample at `x=0` gives rank 1 for `{1,x,x²}` on the affine line, although
the true filtered dimension is 3.

**I3 — Certification, twice.** Each kernel vector is proved by substituting the parametrization
and checking a zero polynomial exactly on I1's declared charts; a vector that fails returns a
nonzero remainder from which an admissible exact counterexample point is sought. With the
coverage/density hypotheses and every basis vector certified,
`ker E = Id_d(V, F)` **exactly**: true identities lie in the sampled kernel and the certified
basis proves the reverse inclusion. A chart of only `y=0` in `V(xy)` would incorrectly certify
`y`; the second component must be covered. For a relations-based presentation, retain an
ideal-membership witness and the ideal's declared meaning instead. Polynomial identities may
lower to `ring`/`linear_combination`; denominator and domain obligations accompany the proof.
Lean remains exterior verification. Report certificate size and check cost.

**I4 — Elementary identities and closure for all degrees.** Reduce `Id_d` modulo the degree-d
part of the ideal generated by lower-degree relations to get **new generators**. In a graded
chart this uses the corresponding monomial multiples; in a filtered chart retain lower-degree
relations and account for cancellations rather than assuming `F · Id_(d−1)` is complete. Complete to a
Gröbner basis of the generated ideal J. Buchberger closure certifies reductions within J; to
claim **all** degrees also prove `J = ker(face map)`, for example by elimination from a complete
source presentation with denominator saturation, or an independently certified Hilbert bound.
Without that second inclusion return bounded-degree completeness and the remaining ideal
obligation. The singleton `{x}` is already a Gröbner basis but does not generate `<x,y>`.
`Millennium/Border.lean` concerns degeneration and receiver blindness, not an implemented
Gröbner/border-basis completion engine. Compose its applicable statements rather than infer
that algorithm from its filename. Primary algorithm references distinguish a basis of a given
ideal from an image-kernel computation: [Macaulay2 Gröbner bases](https://www.macaulay2.com/doc/Macaulay2-1.26.05/share/doc/Macaulay2/Macaulay2Doc/html/___Gr%C3%B6bner_spbases.html)
and the [Singular elimination tutorial](https://www.singular.uni-kl.de/ftp/pub/Math/Singular/doc/tutor.pdf).

**I5 — The identity matroid, its relations and its routes.** The columns of `E` are a linear
matroid; its circuits are minimal **sampled dependencies**, becoming identities among the selected
monomials after I3. Its flats are the corresponding dependence-closed families.
`matroid_chow.rs` already carries the Chow ring of a matroid with its Hodge–Riemann form
(Adiprasito–Huh–Katz), so the identity structure of a configuration has a Hodge reading with no
new Chow-ring owner, once the represented matroid/flats are supplied at that owner's supported
scope. That owner accepts simple matroids: zero/parallel columns require an explicit
simplification retaining their relations and reconstruction, or its declared refusal.
Polynomial syzygies require their own module maps; `derivation_atlas` already measures
route-space homology, but that is not a syzygy resolution without a connecting chain map.
The graph to walk is: nodes are basis identities,
edges are S-pair reductions, symmetry orbits and collapses.

**I6 — Collapses, lifts and the character chart.** A defined collapse transports existing
identities, and can create additional ones. Compute the specialized face-map kernel independently
and compare it with the transported generic ideal. For `u ↦ δx`, the generic kernel is zero but
at `δ=0` it is `<u>`. Thus a circular, Galilean or hyperbolic collapse returns either ideal
equality with its base-change hypotheses, or the extra special-fibre relations. A proposed lift
`f₀ + k f₁ + …` must satisfy the original face-map equation and may be obstructed; it is not
guaranteed by the collapsed identity alone.
Where the declared representation admits a complete isotypic decomposition, use it to split
`Mon_d(F)`; otherwise retain the coupled representation. On torus factors pass to
**character (winding) monomials**, where identities become lattice arithmetic (`winding_inertia.rs`,
Smith normal form) — name the windings. [interpretation] In Holonic notation a matrix-coefficient
addition theorem inserts a resolution of the identity between two transports:
`⟨r|ρ(g₁g₂)|v⟩ = Σ_i ⟨r|ρ(g₁)|e_i⟩⟨e^i|ρ(g₂)|v⟩`, with `cos(a+b) = cos a cos b − sin a sin b` its
smallest instance and the declared metric `G` exactly the hypothesis the resolution needs.
For functions with a supplied representation and matrix-coefficient receiver, this derives
addition identities systematically. It does not classify every special-function identity.

**I7 — The transcendental layer and landmark constants.** An admitted D-finite function is
represented by its **annihilating operator, domain and initial data**, exact over the declared
coefficient field: `exp` is `y′ = y`; the whole two-sided
family `C_k, S_k` is `y″ + k y = 0`, so identities are derived uniformly in `k`. Identity is the
annihilator of the difference plus finitely many initial values; `hypergeometric_closure.rs` (the
three-site turning equation with its local turn numbers) is the owner to extend. A **landmark
constant is an invariant such a system forces**, kept as constraint, branch and enclosure under the
[constraint-mode contract](../CONSTRAINT_MODES_AND_RECEIVER_FACES.md), never as a float:

| Kind | Example | How it is generated |
|---|---|---|
| period — the first return of a flow, a cycle paired with a form | `π` | for `k > 0` the half-period is `π/√k`; continuation to `k < 0` requires a declared complex branch and does not give a real hyperbolic period; `k = 0` is the separate degenerate fibre |
| unit-time value of a generator | `e` | `y′ = y`, `y(0) = 1`, read at `1` |
| connection coefficient or monodromy between sites | `Γ` values, `ζ(3)` (Apéry's recurrence) | local turn numbers and transition matrices of a Fuchsian system |
| critical parameter where a placement reading changes arm | de Bruijn–Newman `Λ` | the heat-flow time at which a family becomes real-rooted; `RH/DeBruijn*`, `HeatFlow*`, `Jensen*`, `HurwitzPolynomial` own the analytic side and `SpectralReading` is its finite analogue; approached as a staircase of finite-degree thresholds |

[interpretation] Enumerating systems by declared order, degree and sites generates candidate
constraint faces. Multiple certified routes to one face expose a reusable landmark; the
enumeration does not establish a canonical ordering of importance or completeness of all
constants. Finite spectral thresholds approach an analytic critical parameter only with the
source-family convergence and tail/zero-control hypotheses from the RH owners. A procedure for
deciding equality of represented functions does not thereby decide arbitrary equalities between
their values at different arguments.
Coincidences between constants are proposed by integer-relation search on enclosures (exterior
jurisdiction; the Ramanujan Machine and PSLQ are prior art) and stay `conjecture` until a
telescoping or ideal-membership certificate exists.

**I8 — Navigation, learning and compression.** The certified layers return the relations inferred
within their stated scope. Learning can also develop where to look: receiver/degree choices,
auxiliary constructions, collapses or lifts. Certified rank gain per exact-arithmetic cost is a
declared measurement or policy feature, not the native navigation law. Derive continuation from
the actual source-conditioned variation/transport, preserving phase, constraints and successor
family; a score-ranked candidate queue alone does not supply that construction. This is a
[Hephaestus automaton](../HEPHAESTUS_AUTOMATA.md) on HNN traversal, and it uses the navigation
law recovered in the [mass/flux and navigation synthesis](../../research/records/2026-09-13_MASS_FLUX_GAPS_AND_OPTIMAL_NAVIGATION_RETURN_THEIR_SOURCE_MAPS.md)
with the source, admissible generators, target and cost declared, and any quotient/lift certified.
**Holonic Compression consumes these relations**: a Gröbner basis with a declared monomial order gives canonical algebraic
representatives; an executable codec additionally owes its decoder, retained fibre and cost.
For the admitted future family require `D E = ρ` and `E_next T = U E`. Applying an identity is a
zero-remainder rebase at its declared receiver; `skein.rs` supplies an existing local-substitution
form. The Hilbert function measures independent algebraic faces, not by itself encoded bits,
runtime cost or preservation of continuing conduct.

## First instance, small enough to falsify

[open] **T0.** One angle with `k` a variable: recover `C² + kS² − 1` as an ideal generator and
its bounded-degree consequences in the declared chart. **T1.** Two angles and their sum: the addition laws uniformly
in `k`; compute the `k = +1, 0, −1` kernels separately, retain extra collapse relations, and certify
both Gröbner closure and equality to the declared face-map kernel before an all-degree claim.
**T2.** Three helical axes with receivers `K`, `R`, pitches, spreads and quadrances: recover the
transferred laws of cosines and sines. A certified relation absent from the helical record is
new to that record; repository and external prior art determine any broader novelty claim.
Report the filtered Hilbert dimension as algebraic redundancy and measure codec cost separately.
Return the basis, the certificates (exact and Lean), the matroid and route readings, the collapse
tests and the measured cost per degree.

## What this must not become

[definition] A completeness claim is always relative to a declared `(V, F, d)` or to a closed
face-map ideal certificate (including its Gröbner check); numerical coincidence never promotes
itself; the learned policy proposes and never certifies; and no identity table is authored by
hand where the kernel can return it.

[source-audit 2026-09-19 d3ef0a75] prior-art searches: `'gröbner|buchberger|knuth.?bendix|rewriting
system|normal form|syzyg'` → 107 files (owners: `algebraic.rs`, `matroid_chow.rs`, `skein.rs`,
`Millennium/Border.lean`); `'identity discovery|vanishing ideal|ideal membership|hilbert
function|polynomial identity testing'` → no owner composes discovery by kernel;
`'holonomic function|d-finite|zeilberger|…|annihilat'` → 245 files, owners `hypergeometric_closure.rs`
and the August 24 annihilator-certificate record; `'pslq|integer relation|LLL'` → 14 files;
`'method atlas|derivation.?atlas|route space'` → 85 files (`derivation_atlas.rs`). This contract
composes them; it has not found an owner that already does I2–I4.
