# The parallel Lean squeeze closes the energy, growth, refinement, and period-algebra gates

Date: 2026-08-23

## Scope and authority

**[historical]** The immediate starting point was
`2026-08-23_THE_CLAUDE_LEAN_BURST_HAS_AN_EXACT_CORE_AND_THE_TWO_GEOMETRY_PREPRINTS_OPEN_TYPED_GATES_NOT_SOLUTIONS.md`.
Its seven ordered gates supplied evidence and orientation for this squeeze; it did not schedule the
live Rust construction.

**[project-postulate]** This record is the current evidence handoff for the exterior Lean theorem
cartography line.  It does not alter `blueprint/THE_ROADMAP.md` or `CONSTRUCTION_STATE.md`, and it
does not authorize a Lean fixture, visualization, or theorem count to substitute for a live-roadmap
deed.

**[established-bounded; formal-checked]** The phase changed only owner-local Lean sources, the
aggregate Lean import surface, and this research record.  Unrelated dirty Rust, blueprint, life,
Athena, `CLAUDE.md`, construction-state, and `Scratch/` material remained outside the phase.

## Exact returns

### Positive-time periodic Navier--Stokes energy

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesPeriodicEnergy.lean` now proves, for every
`PeriodicSolution` and every `t > 0`,

```text
d/dt (1/2 ∫_[0,1]^3 |u|^2)
  = -ν ∫_[0,1]^3 Σ_i |∇u_i|^2 + ∫_[0,1]^3 f·u.
```

The returned chain includes the joint Eulerian time jet, its equality with the official
`derivWithin` at positive time, pointwise momentum work, periodic pressure and advection
cancellation, the componentwise Green identity, compact-cube integrability, and differentiation
under the integral from a compact positive-time cylinder.  No domination hypothesis was added.

**[conditional; formal-checked]** The viscous work is a nonpositive contribution when the receiver
is integrable and `0 ≤ ν`.  The energy equality itself remains algebraically valid for every real
coefficient admitted by `PeriodicSolution`; the physical word "dissipation" begins only at that
separate sign gate.

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/DissipationGapBridge.lean` owns the exact abstract composition

```text
E' = -νD + W,    λE ≤ D,    0 ≤ ν
             ⇓
E' ≤ -(νλ)E + W.
```

It also returns weak and strict unforced decay, integrating-factor antitonicity, the exact interval
comparison `E(b) ≤ exp(-νλ(b-a)) E(a)`, the impossibility of a positive unforced stationary
state under positive `ν,λ`, and stationary forced balance.  Its Navier--Stokes attachment fills only
the proved energy-balance port; its gap remains an explicit hypothesis.

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesPeriodicEnstrophy.lean` constructs the unit-cube
vorticity receiver and proves its positive-time smoothness, slice/joint-curl agreement, periodicity,
divergence freedom, transport cancellation, compact-cylinder differentiation, vorticity Green
identity, and integrability.  Its explicit conditional attachment is curled momentum before
nonlinear expansion; the already-proved nonlinear curl identity then derives, rather than assumes,
transport minus stretching.

**[conditional; formal-checked]** Given that visible curled-momentum attachment, the forced
positive-time enstrophy equality is

```text
Eω' = -ν Dω + Sω + Fω.
```

For `0 ≤ ν`, nonincrease is equivalent to `Sω + Fω ≤ νDω`.  The stretching integrand is
bounded at every admitted differentiable occurrence by
`‖∇u‖op · ‖ω‖²`, with an attached positive-time solution corollary.

**[open]** The endpoint `t = 0`, mixed time--curl commutation, curl--Laplacian commutation, an
actual scale-critical absorption/continuation estimate, and global regularity remain unresolved.
The exact stretching term is now exposed; it has not been bounded by the energy receiver.

### Directed finite Hodge transport and the Yang--Mills scale gate

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/HilbertTransportRefinement.lean` bundles actual finite Hilbert
complexes and coherent nonempty directed refinement systems.  A refinement is an isometry on all
three carriers commuting with both differentials and both adjoints.  Those four squares prove
transport of harmonic, exact, coexact, and nonharmonic populations; middle-Laplacian naturality;
and exact Laplacian-energy preservation.

**[proved-derived; formal-checked]** The fine-only population
`newNonharmonicModes` is the intersection of the fine nonharmonic space with the orthogonal
complement of the transported coarse population.  Every such mode is formally nonharmonic and is
orthogonal to every transported coarse nonharmonic occurrence.

**[proved-derived; formal-checked]** `HasUniformNonharmonicGap` and
`HasUniformGapDefect` are exact logical alternatives on a nonempty scale family:

```text
¬ HasUniformNonharmonicGap ↔ HasUniformGapDefect.
```

Each individual finite scale is coercive; no theorem promotes its scale-dependent witness to one
common separator.

**[open]** A nonconstant realized refinement family, a uniform positive separator, convergence to
a continuum operator, gauge realization, and constructive-QFT testimony remain absent.  This is
the typed entrance to the Yang--Mills mass-gap question, not its solution.

### BSD central normalization

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/FamilyCentralRatio.lean` closes the completed/uncompleted central
normalization on the prime branch `p ≡ 3 (mod 8)`.  It proves the positive root number, folds the
theta integral at one, evaluates it as twice an explicit convergent Gaussian lattice sum, and
returns the equivalence

```text
2 L_p(1) = c² Ω_p
  ↔
4 · centralGaussianSum(p)
  = centralArchimedeanFactor(p) · c² Ω_p.
```

The statement is exact for every integer `c`; it becomes the desired Waldspurger--Tunnell gate only
when `c` is instantiated by the finite signed ternary-form count.  It does not itself perform that
identification.

**[open]** The remaining prime-family BSD leaf is the exact Gaussian-sum/finite-count identity.
Neither the completed normalization nor another factor-of-two manipulation is still missing.

### RH growth and an honest divisor count

**[proved-derived; formal-checked]**
`ElementaryHolonics/RH/AbscissaGrowth.lean` proves a global shifted order-one pointwise envelope for
`completedRiemannZeta₀`.  The proof composes a factorial bound for the real Gamma factor on the
right, the existing Mellin bound on a fixed middle strip, and the completed-zeta reflection on the
left.  It then transports the pointwise bound to the corrected translated-circle Jensen receiver.

**[proved-derived; formal-checked]**
`ElementaryHolonics/RH/ZeroCounting.lean` converts that weighted receiver into actual inner divisor
mass.  A zero in the radius-`R` disc pays at least `log 2` to the radius-`2R` Jensen population, the
outer annulus pays nonnegatively, and the inner receiver is proved equal to the total completed-zeta
divisor mass on the inner disc.  Thus, for `R ≥ 1` and a nonzero centre, the inner multiplicity count
has an unconditional doubled-radius order-one bound.

**[open]** The Weil explicit formula remains the decisive global gate: an equality among the actual
zero divisor, the von Mangoldt distribution, and the archimedean term over a separating
test-function family.  Growth and counting constrain population size, not placement on the
critical line.

### Six-sphere equivariant periods

**[proved-derived; formal-checked]**
`ElementaryHolonics/Geometry/SixSpherePeriods.lean` advances `SixSphereMonodromy` to the paper's
finite pointwise period algebra.  It proves the invariant alternating form `Q₀`, isotropy of the
displayed period rows, all three generator transformations, exact period-matrix equivariance,
upper-half-plane preservation, and invariance of

```text
D = Im β - 6 (Im μ)² / Im τ.
```

**[proved-derived; formal-checked]** The realified period matrix has determinant
`Im τ · D`; under `Im τ > 0` and `D < 0`, its four real columns are linearly independent.  The
Hermitian Gram matrix is derived from `i Q₀(v, conjugate w)`, has determinant
`24 Im τ · D < 0`, and is not positive semidefinite.

**[open]** Holomorphic construction and uniqueness of the period functions, lattice
discreteness/cocompactness, quotient properness, toric/logarithmic filling, Hausdorff gluing,
homology, and `S⁶` identification remain outside the proved return.

### Brendle--Hung symbolic hinge

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/BrendleHungHinge.lean` gives the second variation separate typed
owners for the linear term, symmetric bilinear `Q`, linear `r,z`, the contraction, and the required
`r-z` exchange symmetry over characteristic zero.  It proves the complete ten-component expansion
and forces the last mixed term to be

```text
2 λc λd Vcd,
```

where `Vcd` is typed with the actual `h²_cd` component.

**[counterexample; formal-checked]** A one-dimensional rational model makes the correct `cd` term
nonzero while the repeated `dd` replacement is zero.  The erroneous repeated-`Vdd` display is
therefore not a universal bilinear identity.

**[proved-derived; formal-checked]** The printed scalar `h²_bc` coefficient is exactly the
`θ ↦ π/2-θ` exchange of the printed `h²_ac` coefficient.  Exact frame/operator equivariance
transports a supplied `Vac = 0` proof to `Vbc = 0`, and the smallness condition is exactly
`λd² C ≤ δ ↔ |λd| ≤ sqrt(δ/C)` under `0 ≤ δ` and `0 < C`.

**[open]** The full tensor/operator exchange, an independent proof of `Vac = 0`, trusted fresh
computer-algebra replay, and the geometric curvature argument remain open.  The source notebook's
assignment of `Vbc` from `Vac` is not evidence for the missing identity.

## Holonic composition actually used

**[interpretation]** The common shape across these returns is not a declaration that the physical
theories are identical.  It is a typed composition pattern: a local occurrence crosses a declared
operator, the receiver records energy/period/divisor data, transport preserves the reading when its
squares commute, and a scale or boundary enlargement retains a named reconstruction defect.

**[established-bounded; formal-checked]** The pattern is realized here by four distinct exact
owners: periodic paired-face cancellation in Navier--Stokes, adjoint-compatible chain refinement in
the Hodge package, monodromy-equivariant period transport in the six-sphere package, and
radius-doubled divisor reception in RH.  No cross-domain physical identity was asserted.

## Recommended next squeeze

**[open]** First, discharge `HasPointwiseVorticityBalanceAt` from the official momentum equation by
proving the mixed time--curl and curl--Laplacian commutation receipts.  Then ask for the weakest
scale-critical receiver that absorbs the now-exact three-dimensional stretching term.  Do not
replace this with another energy equality.

**[open]** Second, realize at least one nonconstant directed Hilbert/gauge refinement family and
decide whether its new-mode population carries a uniform gap or an explicit vanishing-gap sequence.
The abstract dissipation-gap bridge then transports either return without identifying Yang--Mills
with fluid dynamics.

**[open]** Third, build RH's explicit formula as a typed equality on a declared test-function
space.  Only after that equality stands should PhysicsAI's generic Wronskian, supporting-hyperplane,
or zero-counting lemmas be considered owner-locally.

**[open]** Fourth, close BSD's one remaining Waldspurger--Tunnell equality by matching the explicit
Gaussian lattice sum to the finite signed count already present in the family line.

**[open]** Fifth, advance the six-sphere construction through analytic period existence and the
topological lattice quotient before any filling or `S⁶` claim, and repair the Brendle--Hung full
frame/operator equivariance before returning to curvature.

## Validation receipt

**[established-bounded; formal-checked]** The owner-local closure command built the nine changed
modules together through Lake and returned exit status zero after 3,655 jobs in 37.020 seconds.

**[established-bounded; formal-checked]** The release receiver `lake build` returned exit status
zero across the complete aggregate import surface after 3,945 jobs in 5.167 seconds.  Its output
contained existing lint, deprecation, and declaration-audit notices but no build error.

**[established-bounded; formal-checked]** Independent semantic audits checked the new theorem
signatures, their receiver hypotheses, and their declared axiom dependencies.  The proved returns
use Lean's standard logical axioms and do not import a project-local theorem asserting a Millennium
conclusion.

**[established-bounded]** The aggregate SHA-256 over every non-`Scratch` Lean source below
`soma/formal/elementary-holonics`, sorted by path and hashed with file boundaries retained by
`sha256sum`, is
`0d700154145fe353e18aa936b747e0a8cfc77e94d7a74e3a336a5432a2810f76`.
