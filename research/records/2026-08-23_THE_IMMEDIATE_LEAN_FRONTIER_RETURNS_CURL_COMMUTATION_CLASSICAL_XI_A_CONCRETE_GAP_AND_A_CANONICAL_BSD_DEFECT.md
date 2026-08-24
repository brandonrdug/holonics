# The immediate Lean frontier returns curl commutation, classical xi, a concrete gap, and a canonical BSD defect

Date: 2026-08-23

## Scope and authority

**[historical]** The starting evidence was
`2026-08-23_THE_PARALLEL_LEAN_SQUEEZE_CLOSES_THE_ENERGY_GROWTH_REFINEMENT_AND_PERIOD_ALGEBRA_GATES.md`.
Its recommended order identified the four gates pursued here; it did not schedule the live Rust
construction.

**[project-postulate]** This record is an evidence handoff for the exterior Lean theorem-cartography
line.  It does not alter `blueprint/THE_ROADMAP.md` or `CONSTRUCTION_STATE.md`, and none of its
formal objects, theorem counts, or build receipts substitutes for a live-roadmap deed.

**[established-bounded; formal-checked]** The phase adds six owner-local Lean modules, updates the
aggregate Lean import surface, corrects one signed-count documentation orientation, updates the
enstrophy port documentation, and deposits this record.  Unrelated dirty Rust, blueprint, life,
Athena, `CLAUDE.md`, construction-state, and `Scratch/` material remained outside the phase.

**[open]** No Millennium Prize Problem is solved by this phase.  The returns below remove exact
calculus and object-identification ambiguities and expose smaller named obstructions; they do not
close the global analytic or arithmetic theorems.

## Navier--Stokes: the curled equation now follows from momentum

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesCurlCommutation.lean` proves on every strictly
positive-time `SmoothSolution` that the Eulerian time derivative commutes with spatial curl.  The
proof uses symmetry of the admitted joint second derivative and the already-proved equality between
joint-derivative and slice-derivative vorticity.

**[proved-derived; formal-checked]** The same module proves from finite smooth calculus that
spatial differentiation commutes with the Euclidean vector Laplacian and therefore

```text
curl (Delta u) = Delta (curl u).
```

The proof uses repeated second-derivative symmetry to rotate the third derivative; it assumes no
analyticity.

**[proved-derived; formal-checked]** The official momentum equality, together with the smooth
velocity and pressure carriers, reconstructs a `C^2` positive-time spatial force slice.  Spatially
differentiating momentum, applying the linear curl receiver, killing the symmetric pressure
Hessian, and composing both commutation squares constructs
`HasPointwiseVorticityBalanceAt` directly from `SmoothSolution`.

**[proved-derived; formal-checked]** Consequently every positive-time `PeriodicSolution` now
returns the exact forced enstrophy identity without a separately assumed vorticity equation:

```text
E_omega' = -nu D_omega + S_omega + F_omega.
```

Here `E_omega` is one half of the unit-cube integral of squared vorticity,
`D_omega` is the component-gradient-square population, `S_omega` is signed vortex-stretching work,
and `F_omega` is curl-forcing work.  Periodic transport cancels and the viscous Green identity has
the displayed negative sign.

**[conditional; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesVorticityControl.lean` proves that a uniform cube bound
`norm (D u) <= K` gives

```text
S_omega <= 2 K E_omega.
```

For `0 <= nu` and curl-forcing work bounded above by `F`, it follows that
`E_omega' <= 2 K E_omega + F`.  Uniform versions of those two bounds on a positive closed interval
give the exact mathlib Gronwall receiver; nonpositive curl-forcing work gives

```text
E_omega(t) <= E_omega(a) * exp (2 K (t-a)).
```

**[established-bounded; formal-checked]** The current `PeriodicSolution` carrier already assumes
global positive-time smoothness, while the control theorem accepts the Jacobian constant and
forcing-work bound as hypotheses rather than constructing them.  It therefore supplies no
continuation estimate merely by exhibiting some `K`.

**[open]** The identity must be transported to the finite-time solution carrier, and `K` must be
replaced by a continuation-independent, data-controlled or scale-critical receiver whose integral
cannot diverge at a maximal time.

**[open]** A formal Beale--Kato--Majda or Prodi--Serrin continuation passage, the periodic
Biot--Savart/logarithmic estimate needed to control the full Jacobian from vorticity, compatible
restart/gluing, endpoint `t = 0`, and global regularity remain absent.  Three-dimensional stretching,
not a missing curl identity, is now the exact obstruction retained by the formal line.

## RH: the correct entire object and an admissible explicit-formula port

**[definition]** Mathlib's `completedRiemannZeta₀` is the additive pole-removed completion

```text
Lambda_0(s) = Lambda(s) + 1/s + 1/(1-s).
```

**[proved-standard; formal-checked]** Its analyticity and reflection law are available through the
named imported mathlib theorems.

**[established-bounded]** The audited formal layer supplies no theorem identifying the additive
completion's zero divisor with the Riemann-zeta zero divisor.

**[project-postulate]** The additive completion may not be used as the zeta-zero receiver without
a proved divisor bridge.

**[proved-derived; formal-checked]**
`ElementaryHolonics/RH/RiemannXi.lean` installs the classical entire function

```text
xi(s) = (s(s-1) Lambda_0(s) + 1) / 2
      = s(s-1) Lambda(s) / 2              away from 0 and 1.
```

It proves global complex differentiability, nonnegative divisor, Jensen's formula, reflection
`xi(1-s)=xi(s)`, endpoint values `xi(0)=xi(1)=1/2`, and exact equivalence of `xi(s)=0` with
`zeta(s)=0` in the open critical strip.

**[established-bounded; formal-checked]** The pre-existing `RH/ZeroCounting.lean` remains a correct
growth/counting receiver for the divisor of `completedRiemannZeta₀`.  It is not a count of zeta or
classical-xi zeros and is not used as one in the new explicit-formula module.  Rebasing its growth
argument to the polynomially modified classical `xi` remains a separate deed.

**[definition]**
`ElementaryHolonics/RH/ExplicitFormulaReceiver.lean` gives separate owners to a smooth compactly
supported complex kernel on the real logarithmic line, its analytic bilateral Laplace transform,
the multiplicity-weighted classical-xi divisor in a disc, the finite von Mangoldt receiver, the two
polar addresses, and the logarithmic-derivative contour.

**[definition]** `AdmissibleXiContour` requires a positive radius and a boundary meeting no xi
zero.  Both the weighted argument-principle port and the prime--archimedean residual-identity target
carry that admission explicitly; zero-freeness is not hidden in the desired equality.

**[conditional; formal-checked]** A weighted argument-principle receipt and a fixed
prime--archimedean residual identity compose to the exact truncated equality

```text
xi-zero receiver
  = polar receiver - finite-prime receiver - archimedean receiver + boundary receiver.
```

The argument-principle defect vanishes exactly when the equality port is filled on an already
admissible contour.  Because the archimedean and boundary scalars remain parameters, the residual
identity alone is bookkeeping and is not a proof that an independently defined deformation
returned them.

**[proved-derived; formal-checked]** Agreement of spectral kernels on every occupied xi-divisor
address suffices for equal zero receivers.  Agreement of arithmetic kernels at every address in
`Finset.Icc 1 N` and its reflected logarithm suffices for equal finite-prime receivers.  These are
support-local congruence results, not converses or complete reconstruction-fibre characterizations.

**[proved-derived; formal-checked]** On `Re(s) > 1`, the untruncated von Mangoldt Dirichlet receiver
is exactly `-zeta'(s)/zeta(s)` by the existing mathlib-backed finite-place theorem.

**[open]** The weighted global argument principle, construction of a cofinal admissible contour
family, exact prime/gamma deformation, normalization of the archimedean term, disappearance of the
boundary receiver, rebase of growth/counting to classical xi, and a separating Weil-positivity
class remain unresolved.  The new file types those ports; it does not postulate the explicit
formula or constrain a zero to the critical line.

## BSD: the remaining family theorem is one canonical scalar defect

**[definition]**
`ElementaryHolonics/Millennium/FamilyWaldspurgerGate.lean` fixes the canonical signed ternary census
on its proved-tight box and the orbit-normalized branch count.  If `A_p` counts the `32 z^2` form
and `B_p` the `8 z^2` form, the chosen orientation is `2 A_p - B_p`; reversing the orientation
negates the count but leaves its square unchanged.

**[proved-derived; formal-checked]** The tight census equals the structural census, is divisible by
four, and its quotient is odd on every prime branch `p mod 8 = 3`.

**[established-bounded]** The adjacent `LatticeCount` header was corrected from the opposite
written sign; its definitions and theorems already used the right signed sum.

**[definition]** `waldspurgerTunnellDefect p` is the difference between the fully normalized
Gaussian central lattice receiver and the archimedean factor times the square of the canonical
finite branch count and the real period.

**[proved-derived; formal-checked]** Defect vanishing is equivalent to the canonical central-ratio
identity.

**[conditional; formal-checked]** On a prime `p mod 8 = 3`, zero defect supplies the existing
`LatticeCountDatum` and therefore the repository's established BSD rank clause for that family
member.

**[established-bounded; computational-witness]** Native-evaluated examples accepted during the Lean
build return
canonical branch counts `1`, `-1`, and `3` at `p = 3`, `11`, and `43` respectively.  These finite
witnesses do not prove the family defect vanishes.

**[open]** The actual Waldspurger--Tunnell theta/period comparison remains unproved.  Naming its
canonical scalar defect removes sign, box, parity, and normalization ambiguity; it does not reduce
the external theorem's analytic depth.

## Hodge and Yang--Mills: a nonconstant finite calibration family

**[definition]**
`ElementaryHolonics/Millennium/HilbertConcreteRefinement.lean` realizes the abstract refinement
owner on two identity--zero Hilbert complexes.  The coarse middle carrier is the real line, the
fine carrier is the Euclidean plane, and refinement is first-coordinate isometric inclusion with
all differential and adjoint squares commuting.

**[proved-derived; formal-checked]** The middle finrank grows strictly from one to two.  The second
fine coordinate is a nonzero new nonharmonic mode orthogonal to the complete transported coarse
population.

**[proved-derived; formal-checked]** The middle Laplacian energy is squared norm at both scales, so
the family has uniform nonharmonic gap one; no larger constant works.  Its exact uniform-gap defect
is therefore false.

**[established-bounded; formal-checked]** This two-scale identity--zero family is a finite
calibration fixture; it constructs no lattice gauge complex or continuum limit and returns no
Yang--Mills mass-gap theorem.

**[open]** The next genuine owner is an unbounded incidence-bearing refinement family with nonzero
differentials and explicit gauge/harmonic quotient, returning either a uniform separator or a
concrete vanishing-gap sequence.

## Holonic composition and the next squeeze

**[interpretation]** The four tracks share a lawful composition pattern without identifying their
subjects: transport an occurrence through explicit local operators, read it through a declared
receiver, preserve lineage under refinement or contour change, and retain the exact unresolved
fibre instead of replacing it by a scalar success flag.

**[established-bounded; formal-checked]** That pattern is realized by distinct formal owners here:
the Navier--Stokes stretching-absorption inequality, the RH argument-principle and deformation
ports, the BSD scalar central-ratio defect, and the Hilbert uniform-gap alternative.  No physical
identity among fluids, gauge fields, zeta zeros, and elliptic curves is asserted.

**[open]** The ordered next Lean squeeze is:

1. transport the exact vorticity balance to `NavierStokesFiniteTime`, define the maximal-time
   scale-critical receiver, and formalize a BKM/Prodi--Serrin continuation implication before
   attempting data-controlled closure;
2. rebase the order-one growth and Jensen count from the additive completion to classical xi,
   then prove the weighted argument principle on `AdmissibleXiContour` before contour deformation;
3. attack `waldspurgerTunnellDefect = 0` through the actual theta/Poisson correspondence between
   the Gaussian sum and signed ternary census, without another normalization layer; and
4. replace the two-scale identity--zero Hilbert fixture by an unbounded cellular or lattice family
   with nontrivial incidence and decide its uniform gap/defect behavior before any continuum or
   Yang--Mills interpretation.

## Validation receipt

**[established-bounded; formal-checked]** The owner-local closure command built all six new modules
together and returned exit status zero after 3,683 jobs.  Existing imported lint, deprecation, and
declaration-audit notices remained warnings rather than build errors.

**[established-bounded; formal-checked]** A separate scratch audit asked Lean for the axiom
dependencies of representative BSD, Hilbert-gap, classical-xi, explicit-formula, curled-momentum,
Gronwall, and exponential-bound theorems.  Every result returned exactly
`[propext, Classical.choice, Quot.sound]`; the temporary audit source was then deleted.

**[established-bounded]** A source scan of all six new modules found no `sorry`,
`admit`, local `axiom`, `opaque`, or `unsafe` declaration.

**[established-bounded; formal-checked]** The release aggregate `lake build` returned exit status
zero after 3,952 jobs in 12.465 seconds.  Its output contained existing lint, deprecation, and
declaration-audit notices but no build error.

**[established-bounded]** The aggregate SHA-256 over every non-`Scratch` Lean source below
`soma/formal/elementary-holonics`, sorted by path and hashed with file boundaries retained by
`sha256sum`, is
`ff3957368f77228c6e09f38a7e8baec6209e63bf37aa1c8a027b03a21f28f08b`.
