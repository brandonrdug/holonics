# The BSD front is now assembly, and the Millennium squeeze has typed successors

**Date:** 2026-08-22  
**Purpose:** Claude-readable independent audit and parallel execution order after the general-height return  
**Authority boundary:** `[definition]` This is a user-directed Lean research record. It does not
alter `blueprint/THE_ROADMAP.md`, displace the Rust/CUDA construction frontier, or authorize an
update to `CONSTRUCTION_STATE.md`.

## The decision

`[project-postulate]` Do not forfeit or reorient the BSD arithmetic line. The shortest exact
successor is the strong Mordell--Weil assembly on the already formalized integral split family

```text
E_ab : y^2 = x (x-a) (x-b),       a b (a-b) != 0.
```

`[proved-derived; formal-checked]` `GeneralCollision` supplies the finite square-class receiver
atlas and `Finite (E_ab(Q)/2E_ab(Q))`. `GeneralCertificate` and `GeneralHeight` supply the actual
doubled-abscissa quotient, bounded cancellation, quartic duplication growth, the chord quadratic,
and quadratic fixed-point translation growth. These are the inputs used by the existing checked
`FamilyMordell` descent; no further theta, reflection, cokernel, or positivity theorem is needed to
assemble finite generation on this displayed family.

`[proved-derived; formal-checked]` `GeneralMordell.lean` now defines point height, chooses one
representative from each finite class, bounds every translate, and proves the strict descent

```text
X = Q + Q + R,       h(R) <= H0,       h(Q) < h(X),
```

It proves bounded-height finiteness and concludes

```text
AddGroup.FG ((GeneralFace.E (a : Q) (b : Q)).Point).
```

`[proved-derived; formal-checked]` The assembly retains two exceptional fibres rather than hiding
them in totalized division: `v=0`, where a point has two-torsion abscissa `0`, `a`, or `b`; and
`numA=0`, where `u^2=ab`. The latter is bounded directly as a rational root of the integral
quadratic `z^2-ab=0`. Only the remaining fibre uses the certified quotient and quartic duplication
law.

`[interpretation]` In holonic language the descent is a genuine scale swing, not a metaphor. The
same point is read through two caused receiver paths: self-duplication grows the abscissa
quartically, while translation by a retained class representative grows it quadratically. The
strict exponent gap forces a return to lower height. `classOf` is the finite receiver atlas; the
chosen representative is retained standing; a returned half is a point in the reconstruction
fibre; and the descent word repeatedly transports through the same finite atlas until it reaches a
bounded face.

## What the recent pivot proved, and what it did not

`[proved-derived; formal-checked]` `CokernelCalculus` proves a reusable algebraic fact: if a nonzero
integral multiple of a class lies in an additive closure, then its cokernel class is torsion, while
over a `Q`-module the original class already lies in the rational span.

`[open]` Its BSD theorem only says that every class of `E(Q)/2E(Q)` is killed by two. It constructs
no local descent conditions, Selmer group, Tate--Shafarevich group, or descent exact sequence. Its
Hodge theorem lives in rational cohomology and constructs no integral cohomology lattice or
rationalization square. The statement that the two obstructions are "one species" is not yet a
map, equivalence, or natural transformation between their cokernels.

`[proved-derived; formal-checked]` `SelmerCalculus` correctly defines, for an abstract receiver
family, the subgroup of classes admitted by every receiver and proves that a realized image lies
inside it. It also gives an exact blind-receiver counterexample.

`[open]` The arithmetic receiver family still has to be constructed: the places of `Q`, local
points on the descent torsors, the local images, `Sel_2`, and the quotient identified with
`Sha[2]`. The generic calculus cannot substitute for those instances. The present global descent
bounds `E(Q)/2E(Q)` and yields no information about `Sha` by itself.

`[proved-derived; formal-checked]` `PositiveForm` correctly separates an indefinite index form
from a definite form and proves positivity of the abstract rank-one regulator under an assumed
`HeightDatum` and a non-torsion point.

`[open]` It does not construct the Neron--Tate height datum, a Hodge polarization, an ample class,
or Hodge--Riemann positivity. Effectivity cannot supply those missing structures.

`[proved-derived; formal-checked]` `FunctionalEquationParity` proves the parity of a finite central
analytic order under an entire functional equation and computes the fixed loci of the relevant
involutions.

`[open]` Fixed-locus identification does not place zeros on the critical line, and central parity
does not identify analytic order with algebraic rank. These theorems constrain a later analytic
realizer but do not advance the missing BSD equality by themselves.

`[project-postulate]` These pivot files remain useful as exact bars against false proofs. They are
not schedulers. The arithmetic construction resumes from the strongest checked input, which is
the general height owner.

## Ordered BSD worktrack after `GeneralMordell`

`[project-postulate]` Proceed in this order, repairing each gate in its owner:

1. **Strong Mordell--Weil on the displayed split family.** Finish the assembly above.
2. **General divisor-rank receiver.** Adapt the checked sign-vector collision argument of
   `FamilyDivisorRank` to `E_ab`, using finite generation and the three explicit rational
   two-torsion translates. Return a theorem whose hypotheses expose the divisor count.
3. **Complete the reconstruction fibre (returned).** `GeneralTwoTorsion` classifies
   `E_ab[2](Q) = {O,(0,0),(a,0),(b,0)}` and proves that a nonempty halving fibre is a torsor for
   this four-point population. The explicit `Nat.card` bound has returned separately in
   `GeneralQuotientCardinality`.
4. **Make the scope literal.** First transport rational split roots to an integral chart by a
   declared dilation. Then construct an `AddEquiv` from an arbitrary rational Weierstrass curve
   with full rational two-torsion to a split chart and prove that addition, doubling, height,
   Kummer slots, and quotient receivers commute. Until this gate closes, "every full-two-torsion
   curve" is prose wider than the formal theorem.
5. **Construct the actual local receiver family.** Build the two-covering torsors, localize them at
   all places, define the local images and `Sel_2`, and prove the Kummer exact sequence through
   `Sha[2]`. This is where `SelmerCalculus` becomes an instantiated owner.
6. **Construct the arithmetic positive form.** Define the canonical/Neron--Tate height from the
   checked naive-height dynamics, prove the bounded-difference limit, parallelogram law,
   torsion-vanishing equivalence, and regulator independence. This is where `PositiveForm` becomes
   an instantiated owner.
7. **Join to analysis without skipping the equality.** Construct the curve's completed
   `L`-function, continuation and functional equation in the same typed chart; only then compare
   its central analytic order to the independently returned algebraic rank. The equality remains
   the BSD hard core.

`[conditional]` The modular-lambda/Landen/theta seam remains a lawful scale route after the chart
and isogeny maps are explicit. It may supply analytic transport, local factors, or testable
functional equations; it does not identify rank and order without a theorem connecting the
arithmetic realizers, regulator, local receiver family, and analytic leading coefficient.

## Parallel Navier--Stokes squeeze

`[proved-derived; formal-checked]` `NavierStokesMovingLoop` now carries genuine curve integrals and
pressure endpoint cancellation, `NavierStokesFiniteTime` supplies a finite-slab solution carrier,
and `HilbertTransportChain` supplies a finite-dimensional Hodge decomposition.

`[open]` None of reflection, cokernel torsion, or a finite Hodge decomposition controls the
noncompact analytic loss at a terminal time. The strongest next conservation-of-faces theorem is

```text
integral_divergence_unitCube_eq_zero_of_onePeriodic
```

derived from the divergence theorem and equality of paired periodic faces. It must be proved on
the actual `Space` carrier, not assumed as a periodic slogan.

`[project-postulate]` Continue from that return:

1. periodic integration by parts, closing the advective, pressure, and viscous face returns;
2. the finite-slab kinetic-energy/dissipation identity, and a slab version of moving circulation;
3. finite Fourier/de Rham instantiation of the Hodge chain and the Leray projection, retaining the
   mean harmonic mode and proving projection--Laplacian commutation;
4. an actual heat/Stokes semigroup and Duhamel local solution with compatible restart and gluing;
5. exact parabolic scaling and a continuation criterion in a named critical receiver such as
   `L^3`, homogeneous `H^(1/2)`, or the BKM vorticity integral;
6. a proof that terminality forces divergence of that critical receiver.

`[open]` The Millennium burden then stands without camouflage: exclude that critical divergence.
The kinetic-energy receiver is supercritical in three dimensions. Circulation, topology,
Gauss--Bonnet, finite Hodge transport, and heat traces type retained terms but do not currently
supply the missing scale-critical coercive estimate.

`[proved-derived; formal-checked]` `UniformityBar` now gives exact elementary witnesses for the
pointwise/uniform distinction used by both this front and Yang--Mills: positive values at every
finite level can have zero infimum, and boundedness on every shorter horizon can coexist with
blow-up at the limiting horizon. The bar is diagnostic; it supplies no uniform estimate.

`[interpretation]` Here conservation of faces is literal. The unit cube has paired receiver faces;
periodicity identifies their transported traces with opposite orientations, so their net returned
flux vanishes. The energy ledger is the descended scalar face of that boundary cancellation.
Vorticity stretching remains an interior holonic interaction and is not erased by the boundary
return.

## Parallel Hodge--Yang--Mills squeeze

`[open]` The highest-leverage exact successor to `HilbertTransportChain` is the bilinear energy
form

```text
q_T(x,y) = <middleLaplacian x, y>.
```

Prove symmetry, nonnegativity, and that its radical is exactly `harmonic`. Then pass to the positive
quotient by that radical, define the finite eigen-spectrum, prove nonnegative spectrum and zero
eigenspace equal to the harmonic sector, and construct the complementary equivalence between
chain cohomology and harmonic representatives.

`[conditional]` This creates a real shared spine: chain cohomology retains harmonic zero modes,
while the positive excitation quotient removes them and exposes the positive finite spectrum. It
can instantiate a finite `SpectrumHasMassGap` predicate when the zero and nonzero sectors are both
inhabited.

`[open]` A finite classical spectral gap is not the Yang--Mills mass gap. The missing ports are a
gauge-fixed Hamiltonian or quantum transfer operator, a state-space/GNS completion, equality of
its spectrum with the problem spectrum, Osterwalder--Schrader reconstruction, and a separator
uniform in lattice spacing and volume.

`[open]` On the Hodge side, never identify algebraic cycle classes with the chain's `exact` sector:
exact chains are boundaries and represent zero cohomology classes. A lawful bridge needs a
rational cohomology-to-harmonic representative map compatible with the cycle-class map. An
integral-Hodge route additionally needs integral cycles, integral cohomology, the integral cycle
map, and a commuting rationalization square. Only after those ports exist can polarization and
Hodge--Riemann positivity act on a geometric instance.

## Parallel RH squeeze

`[open]` The fast exact successor is an entire `riemannXi`, defined from the Mathlib completed-zeta
owner with the pole-cancelling correction. Prove differentiability, the `s -> 1-s` functional
equation, and zero equivalence with `riemannZeta` inside the nontrivial strip. Then instantiate
`FunctionalEquationParity` to prove that any finite central order is even.

`[open]` Add conjugation reality and the resulting `s -> 1-conj(s)` symmetry. These steps construct
the actual reflection orbit of the RH object, but they still do not collapse that orbit onto its
fixed line. The missing return is a positive or self-adjoint realizer strong enough to force
placement, such as a proved Weil positivity criterion on a separating test family.

`[interpretation]` The RH holonic face is therefore not the critical line alone. It is the complete
orbit, its receiver involutions, the shortest separator distinguishing an off-line pair from a
fixed point, and the positive return that would collapse the reconstruction fibre. Fixed-locus
geometry without that return is only the chart.

## Deprioritized and retained pivots

`[proved-derived; formal-checked]` `AdviceBar` correctly proves that an unbounded lengthwise truth
table exists for every language and therefore separates no complexity class.

`[project-postulate]` P versus NP remains deprioritized in this parallel wave. Its eventual live
route must retain a uniform polynomial resource bound or a lower-bound invariant; a finite table
without a uniform bound is not a construction edge.

`[proved-standard]` Poincare remains solved. Its useful role here is infrastructure: three-manifold
decomposition, harmonic sectors, and topology of fluid or gauge carriers. It is not an unsolved
target to relabel.

## Parallel execution returned

`[proved-derived; formal-checked]` `GeneralQuotientCardinality.lean` proves the advertised exact
weak-Mordell--Weil receiver bound

```text
Nat.card (E_ab(Q) / 2 E_ab(Q)) <= 4 * tau(|ab(a-b)|)^2.
```

It installs the existing finite quotient, applies the checked collision theorem to chosen quotient
representatives, and converts a double difference into quotient equality. It imports only
`GeneralCollision` and contains no admission.

`[proved-derived; formal-checked]` `NavierStokesPeriodicFlux.lean` constructs the unit cube on the
actual Euclidean `Space` carrier, transports it through the volume-preserving coordinate
equivalence, applies Mathlib's Bochner divergence theorem, and cancels each upper face against the
corresponding lower face using `IsOnePeriodic`. Its exact terminal theorem is

```text
integral_divergence_unitCube_eq_zero_of_onePeriodic.
```

The consumed hypothesis is global `C^1` periodicity. This is kinematic boundary-flux cancellation,
not pointwise incompressibility, an evolution law, existence, or regularity.

`[proved-derived; formal-checked]` `HilbertTransportSpectrum.lean` proves the Laplacian energy
identity, identifies the form's radical with the harmonic population, descends a positive-definite
and nondegenerate form through `AlgebraicGNS`, proves the finite spectrum nonnegative, identifies
the zero eigenspace, and constructs an exact finite `SpectrumHasMassGap` when both harmonic and
nonharmonic populations are nontrivial.

`[open]` That finite separator belongs to one finite chain. No gauge Hamiltonian realization,
scale family, common positive lower bound, continuum spectral convergence, or quantum mass-gap
return has been constructed.

`[proved-derived; formal-checked]` Claude's `GeneralMordell.lean` has returned the three-fibre
contraction, quadratic translation bound, finite representative atlas, global descent step,
bounded-height finiteness, and the final `AddGroup.FG` theorem on the displayed integral split
family. The checked theorem does not itself construct a normalization equivalence from every
Weierstrass presentation carrying full rational two-torsion.

`[proved-derived; formal-checked]` `GeneralMordell` now also consumes its finite generation and the
collision bound. If `4*tau(|ab(a-b)|)^2 < 2^r`, it proves that the displayed split curve cannot
have `r` points independent modulo torsion. The proof uses exactly the uniform `2^r` free-parity
population; it does not assume that rational two-torsion contributes a uniform extra factor, since
a rational two-torsion point can itself be divisible by two when rational four-torsion is present.

`[proved-derived; formal-checked]` `GeneralTwoTorsion` classifies the identity and the three root
points as the complete rational two-torsion population, proves that adding any such point preserves
a halving fibre, and proves that every two halves differ by one of them. This is the complete
reconstruction-fibre statement, not merely a chosen returned half.

`[open]` The immediate arithmetic successors are now the split-chart normalization equivalence and
the instantiated local Selmer receiver family. The first makes the current universal prose
literal; the second begins the route toward `Sha[2]`.

`[project-postulate]` The next non-overlapping wave is therefore: construct the split-chart
normalization and local Selmer receivers; derive the periodic integration-by-parts ledger from the
new flux theorem; instantiate an actual finite Fourier/de Rham chain in the spectral owner; and
construct the entire `riemannXi` join. Every deed retains its continuum or analytic reconstruction
fibre and returns a focused Lean receipt before aggregate integration.

`[established-bounded; formal-checked]` On 2026-08-22, after importing the three parallel owners,
`lake build ElementaryHolonics` completed successfully after aggregate integration. Focused direct
checks of `GeneralQuotientCardinality`, `NavierStokesPeriodicFlux`, and
`HilbertTransportSpectrum` also returned exit status zero. Their axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound` where applicable. The final coherent aggregate
contained 3,778 jobs.
