# The Claude Lean burst has an exact core, and the two geometry preprints open typed gates, not solutions

## Disposition

**[established-bounded]** This record audits the Lean material present on 2026-08-23, corrects its
strongest semantic overstatements, and places two new geometry preprints into an ordered formal
worktrack. It is research evidence for the Lean exterior; it does not schedule or alter the live
Rust/Athena construction in `CONSTRUCTION_STATE.md` and `blueprint/THE_ROADMAP.md`.

**[open]** No Millennium Prize Problem is solved by the audited files. The complex-structure claim
for `S⁶` and the positive-sectional-curvature claim for `S² × S²` are not established by this
repository. Both remain external claims whose load-bearing geometric and analytic passages have
not been independently verified here.

## Snapshot and receipt

**[established-bounded; formal-checked]** At Git standing
`7d48b28bba430e241bc7e31623683f9e5676857b`, the non-`Scratch` candidate layer comprised 50 new
Lean files, 12,065 lines, 710 theorem declarations, 12 lemma declarations, 145 definitions, three
structures, eight abbreviations, and five instances. A source scan found no `sorry`, `admit`, local
`axiom`, `opaque`, or `unsafe` in those 50 files.

**[established-bounded; formal-checked]** Before the corrections and new bridges recorded below,
`lake build` accepted 3,933 jobs for candidate closure
`b82c31bb5eba001902ed5bfff92f6e623352bf9a4e0d64a41bf355a13444fd85` in 3.343 seconds. That
receipt establishes checker acceptance of the declarations at that closure; it does not grade the
English names or identify a theorem with the external problem it evokes.

**[established-bounded; formal-checked]** Focused checks after the audit accept
`SixSphereMonodromy`, `TwoRegionPositivity`, `HilbertReceiverForm`,
`NavierStokesPeriodicEnergy`, and every file changed by the semantic correction. The new
finite-matrix checks use kernel reduction (`decide`) rather than `native_decide`; the audited new
bridge theorems expose only `propext`, `Classical.choice`, and `Quot.sound` in `#print axioms`.

**[established-bounded; formal-checked]** After the new pressure, advection, viscous, Hilbert,
six-sphere, and two-region owners and the semantic corrections were complete, the 50-file layer
contained 12,341 lines and 720 theorem declarations. `lake build` accepted the final aggregate in
3,937 jobs at non-`Scratch` formal-source closure
`f48026ffdbb3cd3d7e729f427e98ea7ff5f96396fe77c500ced8a0ce532a269b`, elapsed 24.995 seconds,
exit status zero.

## What the burst actually added

### BSD and arithmetic

**[proved-derived; formal-checked]** `PrimeAxes` sharpens the earlier divisor-count quotient bound
for the integral normal form `y² = x(x-a)(x-b)` to

```text
|E(ℚ)/2E(ℚ)| ≤ 2^(2(ω(|ab(a-b)|)+1)),
rank E(ℚ) ≤ 2(ω(|ab(a-b)|)+1).
```

The theorem is an upper bound, not an equality or an occupied-dimension computation. Its former
terminal name was corrected to `theRankIsBoundedByTheOccupiedPrimeAxes`.

**[open]** There is no isomorphism transporting an arbitrary elliptic curve with full rational
two-torsion to the integral `E a b` normal form. There is also no assembled Selmer group, local
image/kernel, or `ZMod 2` finrank theorem. `GeneralSelmer` currently proves coordinate
multiplicativity only for a partial coordinate face; `PrimeAxes` obtains its bound by pigeonholing
complete sign/valuation readings, not by using a Selmer linear map.

**[proved-derived; formal-checked]** `LatticeCount` proves `SF p B = 4 + 8k` on the prime
`p ≡ 3 (mod 8)` branch once the box contains the relevant representations. `FamilyPeriod` proves
the real period is nonzero for positive scale and establishes its exact scaling and Gamma-value
identities.

**[conditional; formal-checked]** `FamilyRatio.theRankClauseNeedsOnlyTheRatio` makes the remaining
analytic BSD gate on that family explicit:

```text
SF p B = 4c
2 L(W_p,1) = c² Ω_p
-------------------
the BSD rank clause for p.
```

**[open]** The shortest genuine family-BSD successor is therefore the exact
Waldspurger--Tunnell central-ratio identity above. The finite lattice parity and period
nonvanishing are no longer the missing premises.

**[proved-derived; formal-checked]** `CanonicalHeight` constructs an abstract Tate limit from a
bounded duplication defect and proves quadratic scaling of that limit.

**[open]** `CanonicalHeight` does not yet instantiate a point height on `E a b`, prove the required
two-sided bounded defect, or connect to the existing `HeightDatum` owner.

### The seventeen, polygon, and descent cluster

**[proved-derived; formal-checked]** The cluster contains exact finite arithmetic: Euclidean-domain
instances for `ℤ[√2]` and `ℤ[√-2]`, Fermat/totient necessities, an inductive square-root tower,
finite facts at 17, and many exact quartic identities.

**[open]** `CongruentSeventeen` does not prove its own `IsCongruentNumber 17`: its witness omits the
positivity and ordering clauses required by that definition. `SeventeenSeparator.Coset` is an
unattached four-element enumeration with no map to an actual descent quotient or
Tate--Shafarevich group. `QuarticSeventeen` leaves every decisive global refusal as an unproved
`Prop`.

**[established-bounded; formal-checked]** Two reflexive propositions formerly advertised as
two-adic stabilization and persistent local solubility were removed. Their types were respectively
`P → P` and `True`; they returned no arithmetic evidence. The finite congruence observations now
remain explicitly experimental until an admissible-residue theorem for every `2^k` and a local
point at every place are supplied.

**[interpretation]** The polygon/face modules remain useful as a catalogue of scalar receiver
shadows: angle excess, Euler characteristic, covering constraints, and finite rotation orders.
They become topology or geometry only after vertices, edges, charts, embeddings, tangent fields,
and transition incidence are typed.

**[established-bounded; formal-checked]** The vacuous `PoincareHopf` proxy and reflexive
Gamma-factor proxy were removed. The flat holon theorem and torus-cover theorem were renamed to
state their actual returns: totalized division gives zero at zero excess, and the Euler equation
permits each degree. Neither theorem now claims an infinite group or constructs a cover.

### RH

**[proved-derived; formal-checked]** The RH layer proves substantial ordinary analytic facts:
entirety and symmetries of the completed zeta, reality on the critical line, critical-strip
containment of nontrivial zeros, a local argument principle, Jensen's formula, exact Gamma decay on
the critical-height line, a Mellin representation, and boundedness on fixed vertical strips.

**[proved-derived; formal-checked]** `GrowthDefect` proves that the former
`TheOrderOneGrowthOfXi`, because it was uniform in an arbitrary circle centre, would force the
completed zeta to be constant. That definition is therefore not a usable growth target.

**[open]** The corrected abscissa-dependent growth statement remains unproved. `Balance` contains
arithmetic on a defined expression `4a+2b`, not a count of actual zeros. `WeilVector` evaluates a
finite-place functional on explicit vectors but supplies no explicit formula relating that side to
an archimedean term and a sum over zeros. No theorem locates an individual zero on the critical
line.

**[open]** The ordered RH successor is: prove corrected abscissa circle growth from the Gamma,
Mellin, functional-equation, and middle-strip owners; obtain honest Jensen counting; then build the
full Weil explicit formula and its separating positivity class. Zero-orbit symmetry alone cannot
close RH.

### Hodge and Yang--Mills

**[proved-derived; formal-checked]** `MillenniumCoupling` proves generic theorems about
self-adjoint receiver forms: positivity, definiteness, finite-dimensional coercivity, compact
obstruction, pullback transport, and perturbative survival of a gap. Its antisymmetric-perturbation
theorem was corrected to accept an arbitrary skew continuous linear operator instead of requiring
the perturbation itself to be a self-adjoint `ReceiverForm`.

**[proved-derived; formal-checked]** `HilbertReceiverForm` installs the repository's actual finite
Hilbert-chain middle Laplacian as a receiver form. Its null cone is exactly the harmonic subspace;
global coercivity is equivalent to a trivial harmonic kernel; and restriction to the nonharmonic
orthogonal complement is positive, definite, and coercive.

**[open]** `HodgeIndex` is a finite Householder-signature model, not cohomology and not the Hodge
conjecture. `TraceForm` proves Frobenius-form identities, not the Rosati/Weil theorem in its
geometric setting. `CurvatureAndGap` uses declared finite spectra and arithmetic Wilson values; it
does not construct a connection, Yang--Mills measure, continuum limit, or a scale-uniform gap.

**[open]** The next Yang--Mills/Hodge gate is a directed family of actual cochain/gauge complexes
with typed refinement maps and a receiver-exact comparison theorem. The quantity needed is a
positive coercivity lower bound uniform in scale after quotienting the harmonic/gauge vacuum, not
the existential finite-dimensional constant already proved at each isolated scale.

### Navier--Stokes

**[proved-derived; formal-checked]** `NavierStokesPeriodicEnergy` now proves on the actual
three-dimensional carrier:

1. the pressure-flux product-divergence identity;
2. zero periodic pressure work for `C¹`, incompressible fields;
3. the derivative of the half-norm-square kinetic density;
4. the kinetic-energy-flux divergence identity; and
5. zero periodic advection work;
6. the scalar periodic Green identity; and
7. the vector viscous identity
   `∫⟪Δu,u⟫ = -∫∑ᵢ‖∇uᵢ‖²`.

The pressure, advection, and viscous faces have honest `PeriodicSolution` corollaries at strictly
positive time, where the existing spatial-slice differentiability bridge applies.

**[open]** These are the three spatial kinetic-energy faces, not regularity. The remaining exact
energy chain is the time derivative of the kinetic-energy integral and its composition with all
three spatial faces and the forcing term through the solution equation. A priori energy equality
still does not control the scale-critical vorticity receiver needed to exclude blow-up.

## The six-sphere preprint

Source: `https://alpo.ge/s6.pdf`, SHA-256
`283bba102dd1d5dc346af81b28145bdaaea6654398d5032e76e97bafb9a858f2`.

**[established-bounded]** The 108-page PDF is titled *A compact complex threefold fibred by tori
over the projective line, and the six-sphere*. The PDF itself provides no author or ordinary date
metadata. It claims an explicit compact complex threefold fibred by complex two-tori over
`P¹`, with multiplicity-three and multiplicity-four elliptic fibres and a nonnormal toric cusp
fibre, whose underlying smooth manifold is `S⁶`.

**[established-bounded]** The load-bearing chain in the source is:

```text
rank-four integral (3,4,∞) monodromy
  -> equivariant period functions τ, μ, β
  -> toric filling at the unipotent cusp
  -> two logarithmic-transform fillings
  -> holomorphic/Hausdorff gluing
  -> van Kampen + two integral-homology computations
  -> homotopy-sphere recognition and Θ₆ = 0
  -> transported integrable complex structure on standard S⁶.
```

**[established-bounded]** The source derives
`π₁(X) = ℤ/|12ℓ₀ - 4ℓ₁ - 3ℓ₂|` and chooses `(ℓ₀,ℓ₁,ℓ₂)=(0,1,-1)`, for which the obstruction is
`-1`. It explicitly says its construction conflicts with a published Campana--Demailly--Peternell
corollary and locates the alleged failure at the nonnormal fibre and at a monodromy assumption.

**[proved-derived; formal-checked]** `Geometry/SixSphereMonodromy.lean` checks the exact finite
entrance: determinants and orders of `T₁,T₂`, the inverse cusp monodromy and square-zero logarithm,
inverse-transpose dual matrices, the triangle-group product, complete fixed lattices of `A₁,A₂`,
the monodromy-invariant `γ` coordinate, the unimodular cusp map, denominator clearing, and the
chosen unit obstruction. Two transcription signs were caught and corrected by these checks.

**[open]** None of the period, positivity, filling, freeness/properness, gluing, topology, or smooth
recognition passages is formalized. The external headline must therefore be read as an
independently unverified claim, not as a consequence admitted into this repository.

**[interpretation]** The lawful holonic reading is stronger than the earlier scalar angle-excess
analogy. The invariant `γ` is a receiver quotient of the monodromy population; the three local
twists accumulate into one returned Seifert/holonomy obstruction; the special fibres are distinct
local chart fillings; and the topology depends on preserving their addressed boundary lineage
through gluing. This correspondence is an interpretation until those maps and their commuting
squares are explicit.

**[established-bounded]** The scalar orbifold excess
`1/3 + 1/4 - 1 = -5/12` is not the twist obstruction. The exact relation is instead
`12ℓ₀ - 4ℓ₁ - 3ℓ₂ = 12(ℓ₀ - ℓ₁/3 - ℓ₂/4)`. No theorem currently identifies either expression
with the polygon `AngleExcess` owner.

## The Brendle--Hung preprint

Source: `https://arxiv.org/pdf/2608.19068`, PDF SHA-256
`46bb66824fa239b95dbfa6a661de675a2d15d0a1e38332433827bf9f31f4e4f7`; arXiv source archive
SHA-256 `81cf36b7fa6f05fcb7f1dbf825cd391b2b95fae71fa016d73f21e871c848d2b1`.

**[established-bounded]** Simon Brendle and Pei-Ken Hung's 34-page arXiv preprint *A metric on
`S² × S²` with positive sectional curvature* claims that `S² × S²` admits such a metric. It begins
with a nonnegatively curved Cheeger--Müter metric and perturbs it as
`g_s = g + s h¹ + s² h² + s³ h³`.

**[established-bounded]** At a generic base point the source identifies one zero-curvature
two-plane. The first variation of the minimized curvature vanishes; the second is nonnegative and
positive away from a two-torus `Σ`; the third-order residue on `Σ` has nonzero mean. Solving
`V³ = μ + Δ_Σ χ` and adding the conformal third-order perturbation makes that residue the constant
`μ`; the sign of `s` is then chosen to match the sign of `μ`. The abstract Section 2 supplies the
two-region compactness argument that extends positivity across the nongeneric locus.

**[established-bounded]** The released TeX and companion Mathematica notebook contain the
following audit defects in the second-order calculation:

1. the TeX defines `V²_cd` with `h²_bd` where the notebook uses `h²_cd`;
2. the displayed expansion repeats `2 λ_d V²_dd` where bilinear expansion requires
   `2 λ_c λ_d V²_cd`;
3. the displayed identity labelled `V²_bd` states `V²_bb = 0`;
4. from `|V²_dd| ≤ C R`, the written choice `λ₀ = √(C/δ)` has the ratio reversed; the displayed
   lower-bound algebra requires `|λ_d|² C ≤ δ`, hence a bound no larger than `√(δ/C)`; and
5. the notebook correctly forms `Vbc`, then immediately overwrites it with
   `FullSimplify[Vac,...]` before returning `Vbc == 0`. The advertised computation therefore does
   not verify the actual `V²_bc = 0` identity.

**[open]** These defects do not constitute a counterexample to the claimed metric, because four
are locally repairable transcription/smallness errors and the missing `Vbc` identity might still
be true. They do prevent this audit from treating the released computation as an independent
verification of the load-bearing Proposition 5.2.

**[proved-derived; formal-checked]** `TwoRegionPositivity.lean` proves the abstract scalar squeeze
with a division-safe explicit threshold: a near-region lower bound
`U ≥ (κ/2)s³ - Cs⁴` and an away-region lower bound `U ≥ κεs² - Cs³` are both strictly positive at
sufficiently small positive scale. It proves the pointwise, finite-population, and nonempty
finite-sum forms.

**[proved-derived; formal-checked]** The same file checks exactly

```text
-3472117/384 + (42025/6) sqrt(5/3) > 0,
```

the numerical coefficient used in the paper's second-order estimate. This proves only that scalar
inequality, not the curvature identity that is supposed to produce it.

**[interpretation]** The paper supplies a precise holonic higher-order squeeze: the zeroth receiver
has a collapsed fibre; first order leaves it unchanged; second order separates its complement but
retains `Σ`; third order, after a Laplacian rebase, separates the final fibre; the sign of `s`
orients the returned passage. This mechanism can be reused only after another problem supplies an
actual receiver, its degeneracy strata, uniform remainders, and a compactness or continuation
theorem.

## PhysicsAI relevance audit

Source: `https://github.com/gecrooks/PhysicsAI`, audited at revision
`0e03deca084de46e11047a8bb9aafa3e22261a70` (2026-08-23).

**[established-bounded]** PhysicsAI is not an AI runtime. At the audited revision it contains two
Lean/TeX/Python research workstreams and no model, training loop, agent runtime, CI workflow, or
machine-learning dependency. The repository describes the AI collaboration as provenance. Its
code is MIT licensed.

**[established-bounded]** The source contains 43 detailed-fluctuation-theorem Lean modules and ten
two-qubit-monodromy Lean modules. A static declaration scan finds 516 theorem/lemma declarations in
the former and 211 in the latter, with no operative `sorry`, `admit`, project `axiom`, or `opaque`.
Both developments are pinned to Lean/mathlib 4.15, whereas elementary-holonics is pinned to 4.27.
They were not executed during this audit; their advertised green builds remain upstream receipts,
not locally reproduced `formal-checked` evidence.

**[proved-derived]** As expressed by its source types, the fluctuation workstream defines the
strong detailed fluctuation theorem as the measure identity
`p.map neg = p.withDensity exp(-σ)`. It proves the reflection law, the second law, the integral
fluctuation theorem, and the exact reconstruction
`dftMix (p.map abs) = p` from a mixture of elementary two-outcome kernels.

**[proved-derived]** Its most reusable source layer is generic analysis rather than its physics
labels: finite moment cones and supporting certificates, Cauchy--Binet and Cauchy determinants,
iterated Leibniz rules, Mittag--Leffler/Stieltjes expansions, Wronskian--Hankel identities and
positivity, Rolle cascades, and finite-mixture minimizer uniqueness. The general uniqueness theorem
is conditional on an explicit interior-fibre hypothesis and is stated for `FinMix`; it is not an
unqualified uniqueness theorem for arbitrary Borel measures.

**[established-bounded]** The two-qubit workstream formalizes the computed finite layer of a
published circuit-depth calculation: an `SU(4)/C₂` alcove, literal quantum Littlewood--Richardson
tables, 72 declared Agnihotri--Woodward--Belkale inequalities, rational membership certificates,
named gate-family polytopes, volume polynomials, and a fidelity identity.

**[open]** That development explicitly does not formalize the Cartan decomposition, the physical
`LogSpec` map, the Agnihotri--Woodward--Belkale realization theorem, flat-connection moduli,
Mehta--Seshadri, symplectic reduction, or quantum cohomology. Its `MonodromySlice` is therefore a
finite half-space object, not a proved image of addressed connection holonomy. Its maximal
compact-Lie-group tori are not the complex quotients `ℂ/(ℤ+τℤ)` required by the modular-torus and
six-sphere tracks.

**[interpretation]** For Navier--Stokes, the generic derivative and determinant lemmas are possible
supporting tools, but the fluctuation body applies to a stochastic fluid observable only after an
actual path-space reversal/Radon--Nikodym theorem. It supplies no velocity PDE, pressure
cancellation, Sobolev estimate, or continuation criterion. Deterministic kinetic energy may not be
renamed entropy production to acquire its conclusions.

**[interpretation]** For Hodge/Yang--Mills, Cauchy--Binet and moment positivity may help analyze
finite Laplacian minors or spectral receiver shadows. A finite spectral moment vector still retains
a reconstruction fibre, and no finite collection of positive moments by itself gives the required
scale-uniform separation of spectral support from zero. The missing flat-connection-to-polytope
bridge is a useful dependency map, not a mass-gap theorem.

**[interpretation]** The strongest Millennium-adjacent reuse is on the RH side: the
Stieltjes/Mittag--Leffler, Chebyshev, Wronskian-positivity, and zero-counting chain may supply lemmas
for constructing a separating test-function cone after a Weil explicit formula exists. PhysicsAI
contains no zeta, xi, prime distribution, or theorem identifying its string weight with an RH
receiver, so there is presently no direct theorem application.

**[project-postulate]** Do not add PhysicsAI as a whole-project Lake dependency. Port only a named
MIT-attributed generic theorem that closes a current owner-local gap, retain the upstream revision
as lineage, compile the port under Lean 4.27, and inspect its axioms. The best initial candidates
are `cauchy_binet`, the iterated-product derivative rule, `cauchy_det`, the Wronskian quotient
identity, and `cascade_zero_bound`.

**[established-bounded]** PhysicsAI's own DFT status prose is stale: the terminal "honest residue"
still calls general Cauchy--Binet, Wronskian, and uniqueness work open even though later modules in
the same source tree declare those results. Exact theorem types, rather than its README counts or
status narrative, must govern any reuse.

## Ordered Lean worktrack from this point

### 1. Close the periodic Navier--Stokes energy identity

**[open]** Prove differentiation under the unit-cube integral for the time-slice kinetic energy,
read the actual `PeriodicSolution` momentum equation against velocity, and compose it with the
pressure, advection, and viscous returns already proved. Retain the `t > 0` boundary until an
endpoint regularity bridge is available.

**[open]** After energy closure, define a scale-local vorticity/enstrophy receiver and derive the
vortex-stretching term. The first decisive regularity target is a continuation theorem from an
integrable scale-critical receiver, not another restatement of smoothness.

### 2. Turn finite Hodge/Yang--Mills coercivity into a scale question

**[open]** Construct refinement maps between finite Hilbert/gauge complexes, prove that harmonic
and nonharmonic projections commute with those maps, and state the uniform lower-bound defect.
The mass-gap problem enters only at this directed-family limit.

### 3. Repair and replay the Brendle--Hung symbolic hinge

**[open]** Correct the notebook's `Vbc` assignment, rerun every second- and third-order cell from a
fresh kernel, bind outputs to source hashes, and prove or refute the missing identity independently.
Only then should the Cheeger metric, zero-plane bundle, curvature variation, and compact
Grassmannian argument enter Lean.

### 4. Advance the six-sphere chain one owner at a time

**[open]** The next exact gate is the equivariant period package, including the negative Hermitian
determinant that makes every displayed period matrix a lattice. It must precede toric filling.

**[open]** Subsequent gates are: toric cusp action and proper quotient; logarithmic-transform
actions and freeness; boundary transition maps and Hausdorff gluing; addressed van Kampen;
integral Mayer--Vietoris/Leray comparison; only then homotopy-sphere recognition. A scalar
Seifert obstruction cannot skip those gates.

### 5. Keep the two BSD fronts distinct

**[open]** On the prime family, prove the exact central-ratio identity and invoke
`FamilyRatio.theRankClauseNeedsOnlyTheRatio`.

**[open]** On arbitrary full-two-torsion curves, build the quotient homomorphism into a finite
`ZMod 2` receiver space, prove kernel exactly `2E`, assemble every local-place equation, compute the
Selmer kernel finrank, and add the normalization/isomorphism transport from arbitrary models.

### 6. Advance RH only through a global formula

**[open]** Close the corrected abscissa growth statement and honest Jensen count first. Then build
the explicit formula as an equality between the prime distribution, archimedean contribution, and
actual zero population. A positivity theorem over a separating test-function family is the first
gate that can constrain zero placement.

### 7. Reuse PhysicsAI only where an exact gap requests it

**[open]** First attempt the next Navier--Stokes, Hodge/Yang--Mills, and RH gates with mathlib and
the existing local owners. If one returns a concrete missing determinant, iterated-derivative,
supporting-hyperplane, or zero-counting lemma, port that smallest PhysicsAI owner with attribution
and prove it at the local toolchain. Semantic proximity to entropy or monodromy alone is not an
import criterion.

## Modular-torus visualization feasibility

**[established-bounded; implemented-exact]** The present engine owns several nearby but distinct
constructions: `ExactComplexAxisPair` carries the local complex-axis rotation
`J(a,b)=(-b,a)`; `ExactTorus` is a real quartic ring torus in `ℝ³`; `ProjectionLaw` owns exact
receiver projection; and `presentation_gauge` renders certified one-variable polynomial faces.
The already-returned `analytic_field_transport` artifact contains exact quarter-arc and cycle
holonomy TSV testimony for one fixed real ring torus.

**[open]** The engine does not own the quotient `ℂ/(ℤ+τℤ)`, an oriented period-lattice basis with
`Im τ > 0`, paired fundamental-domain boundaries, `SL₂(ℤ)` generator transport, the `(3,4,∞)`
orbifold fibres, or a generator-equivariant map from that quotient complex into a reusable
projected mesh/vector/raster presentation port. The existing real `ExactTorus` may not be renamed
or interpreted as that missing complex torus.

**[open]** Consequently no engine-native modular-family visualization is generated in this phase.
An exterior interactive illustration is easy, but it would be an exterior receiver illustration,
not engine provenance. Native construction should wait for an authorized roadmap station and
should add the bounded period-lattice-to-presentation edge rather than a new visualization
subsystem.

## Handoff

**[established-bounded]** This record is the recommended entry point for any subsequent Claude or
Codex Lean session. Read the types before the names, preserve the exact/conditional/open split
above, and continue from the seven numbered gates rather than from theorem counts or narrative
proximity to a famous conjecture.
