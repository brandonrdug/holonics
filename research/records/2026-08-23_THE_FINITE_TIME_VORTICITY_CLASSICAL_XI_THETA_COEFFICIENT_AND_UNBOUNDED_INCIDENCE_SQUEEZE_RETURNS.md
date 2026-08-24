# The finite-time vorticity, classical xi, theta-coefficient, and unbounded-incidence squeeze returns

Date: 2026-08-23

## Scope and authority

**[historical]** The immediate starting position was
`2026-08-23_THE_IMMEDIATE_LEAN_FRONTIER_RETURNS_CURL_COMMUTATION_CLASSICAL_XI_A_CONCRETE_GAP_AND_A_CANONICAL_BSD_DEFECT.md`.
Its ordered open fibres supplied the four fronts pursued here; it did not schedule the live Rust
construction.

**[project-postulate]** This record is an evidence handoff for the exterior Lean
theorem-cartography line.  It does not alter `blueprint/THE_ROADMAP.md` or
`CONSTRUCTION_STATE.md`, and no theorem, fixture, source count, or build receipt below substitutes
for a deed required by the live roadmap.

**[established-bounded; formal-checked]** This phase adds seven owner-local Lean modules, exposes
them through the aggregate import surface, deposits this record, and catches the generated claim
index up across the four Lean records now present on the 2026-08-23 line.  Unrelated dirty Rust,
blueprint, life, Athena, `CLAUDE.md`, construction-state, and `Scratch/` material remained outside
the phase.

**[open]** No Millennium Prize Problem is solved here.  Each return either proves a finite or
conditional passage, identifies the correct mathematical object, or constructs a calibration
family that narrows what a future theorem must add.

## Navier--Stokes: the vorticity argument now inhabits a finite lifespan

**[definition]**
`ElementaryHolonics/Millennium/NavierStokesFiniteTimeVorticity.lean` defines
`PeriodicSolutionOn T` by extending the existing finite carrier `SmoothSolutionOn T` with the
spatial periodicity needed for torus integration.  The ambient fields keep their existing global
function types, but the solution laws and regularity hypotheses are imposed only on the declared
closed time slab, and the differential conclusions are requested only at interior occurrences
`0 < t < T`.

**[proved-derived; formal-checked]** Joint smoothness on the slab interior now supplies the exact
finite-time analogues of spatial-slice smoothness, equality of joint and slice curl, time--curl
commutation, curl--Laplacian commutation, pressure annihilation, and the nonlinear identity

```text
curl ((u . grad)u) = (u . grad)omega - (omega . grad)u.
```

Differentiating the admitted momentum equation in space and applying the curl receiver therefore
proves the complete pointwise vorticity equation at every `0 < t < T`; it is not an extra PDE
hypothesis and it does not assume a globally smooth continuation.

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesFiniteTimeEnstrophy.lean` justifies differentiation
under the periodic cube integral from a compact cylinder strictly inside the lifespan.  Periodic
transport cancels, viscous work becomes negative vorticity dissipation, and the finite carrier
returns the exact forced identity

```text
E_omega'(t) = -nu D_omega(t) + S_omega(t) + F_omega(t)
```

for every interior time.

**[conditional; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesFiniteTimeContinuation.lean` proves that nonnegative
viscosity, a uniform spatial-Jacobian bound `norm(Du) <= K`, and a curl-forcing-work bound `F` give

```text
E_omega'(t) <= 2 K E_omega(t) + F.
```

Uniform versions on every compact interval `[a,b]` with `0 < a <= b < T` produce the exact
Gronwall bound; nonpositive curl-forcing work produces the exponential specialization.  Neither
bound constructs `K` or `F` from the initial data.

**[definition]** `CanExtendPast` presently means that the same velocity and pressure fields carry
a `PeriodicSolutionOn S` for some `S > T`.  `ControlledTerminalObstruction` is the conjunction of
uniform interior control with failure of that declared extension receiver.  This strict typing
does not yet permit a freshly constructed continuation whose fields are glued to the old ones at
the terminal face.

**[proved-derived; formal-checked]** The final result returns

```text
CanExtendPast OR ControlledTerminalObstruction.
```

This is exact logical branch accounting under the supplied control, not a continuation theorem:
excluded middle retains the unresolved terminal fibre instead of silently identifying an interior
estimate with extension.

**[open]** Endpoint regularity at `t = 0` and `t = T`, a restart carrier allowing newly constructed
fields, equality/gluing of the old and restarted traces, local well-posedness, and a maximal-lifespan
principle remain absent.  The uniform full-Jacobian hypothesis must also be replaced by a
time-dependent scale-critical receiver, such as the integral condition appearing in a genuine
Beale--Kato--Majda or Prodi--Serrin passage.  Three-dimensional stretching remains the analytic
obstruction.

## RH: growth and Jensen counting now belong to classical xi

**[definition]**
`ElementaryHolonics/RH/RiemannXiGrowth.lean` attaches the growth receivers to the already-defined
classical entire function

```text
xi(s) = (s(s-1) completedRiemannZeta_0(s) + 1) / 2,
```

rather than treating the additive pole-removed completion as though it had the zeta divisor.

**[proved-derived; formal-checked]** The unconditional shifted order-one bound for the additive
completion survives both polynomial factors, the added constant, and division by two.  It yields
an unconditional pointwise bound for classical xi and then a translated-circle-average bound.
Jensen's identity is instantiated with `riemannXi` itself, so its divisor is the multiplicity
population actually relevant to RH.

**[proved-derived; formal-checked]**
`ElementaryHolonics/RH/RiemannXiZeroCounting.lean` proves that restriction of the doubled-disc xi
divisor to the inner disc is exactly the inner divisor mass.  Every inner zero pays at least
`log 2` to the outer Jensen receiver and every occupied outer-annulus address pays nonnegative
weight.  Consequently, for `R >= 1` and a centre `c` with `xi(c) != 0`, the classical-xi zero
population in the radius-`R` disc has an unconditional order-one doubled-radius bound, with
multiplicity retained.

**[open]** This constrains population growth but not horizontal placement.  No positivity,
argument-principle deformation, or separating receiver forces a zero onto `Re(s) = 1/2`; the RH
obstruction is now plainly placement rather than use of the wrong divisor.

## BSD: the finite ternary population reaches the exact theta coefficient

**[definition]**
`ElementaryHolonics/Millennium/FamilyThetaWaldspurgerBridge.lean` gives separate finite owners to
the tight-box populations for

```text
2x^2 + y^2 + 8z^2  = p
2x^2 + y^2 + 32z^2 = p,
```

their coefficients, and the oriented Tunnell coefficient `2A_p - B_p`.

**[proved-derived; formal-checked]** Doubling the third coordinate constructs an addressed
bijection from the complete `32z^2` population to the even-third-coordinate slice of the
`8z^2` population.  Splitting the thin population by parity then proves the exact finite identity

```text
sum (-1)^|z| = 2 A_p - B_p,
```

and identifies the existing orbit-normalized canonical branch count with `(2A_p-B_p)/4`.

**[conditional; formal-checked]** On a prime branch `p mod 8 = 3`, vanishing of the previously
isolated `waldspurgerTunnellDefect` is equivalent to one displayed equality between the actual
Poisson-transported family-theta integral and the squared finite ternary coefficient, with the
existing archimedean factor and real period.  This theorem fixes the population, sign, parity,
orbit quotient, and normalization of the remaining gate; it does not prove the equality.

**[open]** The Waldspurger--Tunnell analytic/arithmetic comparison itself remains missing.  That is
the next BSD leaf: show that the family theta period lands on the square of this exact coefficient,
including the local factors, rather than introduce another count or scalar defect.

## Hodge and Yang--Mills: unbounded incidence alone does not squeeze the gap

**[definition]**
`ElementaryHolonics/Millennium/HilbertIncidenceRefinement.lean` constructs the split Hilbert chain

```text
V --x |-> (x,0)--> V x V --(a,b) |-> b--> V.
```

Both differentials are nonzero when `V` is nontrivial.  Their adjoints occupy the complementary
summands.

**[proved-derived; formal-checked]** The middle Hodge Laplacian of this chain is exactly the
identity, its nonharmonic population is the whole middle carrier, and its Laplacian energy is
exactly squared norm.

**[proved-derived; formal-checked]** Taking `V_n` to be Euclidean space of dimension `n+1` and
appending a zero coordinate constructs a sequential adjacent refinement at every scale.  The
refinement commutes with both differentials and both adjoints, both incidence maps remain nonzero,
the middle finrank is `2(n+1)` and hence unbounded, and the nonharmonic lower bound is uniformly
one.

**[counterexample; formal-checked]** This family refutes the stronger claim that unbounded
sequential middle dimension together with two nonzero incidence maps is by itself enough to force
a vanishing nonharmonic gap.  The explicit witness has gap one at every scale.

**[established-bounded; formal-checked]** The witness is a split linear calibration, not a lattice
gauge theory.  It supplies no gauge group, gauge quotient, plaquette curvature, interacting
Hamiltonian, physical vacuum sector, continuum reconstruction, or four-dimensional Yang--Mills
measure.

**[open]** A genuine Yang--Mills squeeze must make the interaction and quotient carry the burden:
construct a cellular `0 -> 1 -> 2` gauge complex, remove exact gauge and harmonic directions,
install the nonlinear curvature/Hamiltonian, transport it coherently under lattice refinement,
and then return either a scale-uniform first excitation or an explicit collapsing sequence together
with its continuum reconstruction fibre.

## Holonic synthesis and ordered continuation

**[interpretation]** The useful common structure is a transport discipline, not an identity of
subjects.  Navier--Stokes chronology is retained by the finite time slab and ordered derivative;
RH reflection is a swing only through its proved involutive functional equation; BSD parity is an
oriented receiver preserved through an addressed population bijection; and Hodge refinement is a
chain only through its commuting differential and adjoint squares.  In each case a receiver reads
a consequence while the unreturned alternatives remain a named obstruction population.

**[interpretation]** The strongest cross-pivot is between theta/Mellin transport in RH and the
theta-period/coefficient gate in BSD: both now use the correct analytic object and retain the
finite or divisor population being read.  The shared harmonic-analysis apparatus can be reused,
but the zeta explicit formula and the Waldspurger correspondence remain different constitutive
laws.  The strongest physical cross-pivot is between Navier--Stokes enstrophy and Hodge/Yang--Mills
spectral energy: both admit chain, adjoint, dissipation, and refinement receivers, while nonlinear
stretching and nonabelian curvature prevent their identification.

**[open]** The recommended next work order is:

1. replace constant Navier--Stokes control by a measurable time-dependent coefficient and prove
   the corresponding integral Gronwall passage; then type terminal trace, restart, and gluing so a
   finite critical norm closes `CanExtendPast` rather than merely coexisting with its negation;
2. prove the weighted argument principle for classical xi on a cofinal admissible contour family,
   transport the logarithmic derivative to the prime and gamma faces, and retain the boundary term
   until a proved limit removes it; only then attack Weil positivity and a critical-line separator;
3. close the exact BSD theta-coefficient equality now exposed, by identifying the modular/ternary
   theta coefficient and paying every local and archimedean factor; then compose it with the
   existing Selmer, height, and rank owners;
4. replace the split Hodge calibration with a gauge-covariant cellular complex and interacting
   finite-volume Hamiltonian before asking for uniform spectral separation or a continuum limit;
5. reuse the chain/gluing infrastructure for the Hodge conjecture only after defining the actual
   cycle-class realization map and its locally admissible rational Hodge population.  The present
   Hilbert complex is not that comparison theorem.

**[open]** Poincare remains a solved external theorem and may serve as topology/flow calibration;
it is not an unsolved target.  P versus NP remains outside this ordered squeeze because none of the
four current defects composes into its verification-to-search obstruction without a new typed
bridge.

## Validation receipt

**[established-bounded; formal-checked]** Owner-local builds returned exit status zero for the RH,
BSD, Hodge, and finite-time Navier--Stokes closures.  Representative declaration audits for all
four fronts report only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

**[established-bounded]** A source scan of all seven new modules found no `sorry`, `admit`, local
`axiom`, `opaque`, or `unsafe` declaration.

**[established-bounded]** The claim-index generator was run once after the returned Lean artifact
stood.  Its complete dirty-tree proposal also named an unrelated untracked Athena blueprint and
changed a verifier-reference count through that file.  Those two unrelated deltas were excluded;
the four already-committed/current Lean-record rows and their aggregate counts were retained.  The
complete `claim-index` gate is therefore not reported green on this shared dirty worktree.

**[established-bounded; formal-checked]** The release aggregate `lake build` returned exit status
zero after 3,960 jobs in 38 seconds.  Its output contained existing lint, deprecation, and
declaration-audit notices but no build error.

**[established-bounded]** The aggregate SHA-256 over every non-`Scratch` Lean source below
`soma/formal/elementary-holonics`, sorted by path and hashed with file boundaries retained by
`sha256sum`, is
`a101e5fce16a5a3fc51da49f3271fe08f2428c04d8d8c83bde8fd4ffb572f736`.
