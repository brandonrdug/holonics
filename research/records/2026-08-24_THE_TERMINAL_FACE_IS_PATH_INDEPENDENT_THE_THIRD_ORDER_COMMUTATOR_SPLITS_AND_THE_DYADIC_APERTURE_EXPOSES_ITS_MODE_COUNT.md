# The terminal face is path-independent, the third-order commutator splits, and the dyadic aperture exposes its mode count

**Date:** 2026-08-24

## Scope and authority

**[project-postulate]** This record deposits the next exterior Lean theorem-cartography phase on
the periodic Navier--Stokes continuation line.  It schedules no Rust construction, does not alter
`blueprint/THE_ROADMAP.md`, and does not advance `CONSTRUCTION_STATE.md`.

**[established-bounded; formal-checked]** Four owner-local Lean modules were added to the aggregate
import surface.  They construct a full-tail terminal trace under an explicit time-transport law,
genuine finite dyadic Fourier projectors for actual solution slices, an exact finite diagonal
heat/Stokes semigroup, and a third-directional commutator identity derived from the actual
unforced momentum equation.  Unrelated dirty Rust, roadmap, Athena, life, `CLAUDE.md`, and
`Scratch/` material remained outside this phase.

**[open]** No Millennium problem is solved.  The new theorems replace four narrative bridges with
typed carriers and expose sharper obstructions, but they do not yet prove the infinite
Littlewood--Paley estimate, the integrated H3 production inequality, or uniform local existence.

## The finite scale population is now genuine

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesDyadicShellProjectors.lean` constructs finite cubes in
the actual integer character lattice of `(R/Z)^3`.  It proves the exact cardinality
`(2R+1)^3`, constructs consecutive dyadic shells, and partitions every declared outer aperture
into low, middle, and high populations.  The aperture is retained in every theorem; no finite
projector is identified with the complete Fourier series.

**[proved-derived; formal-checked]** Probability-Haar orthogonality makes finite synthesis an
exact coefficient selector.  Specializing the coefficient family to an admitted open periodic
solution gives actual vorticity and Jacobian band fields, their exact Fourier support, their exact
three-band reconstruction inside the aperture, and the derivative-multiplier identity for every
Jacobian mode.

**[proved-derived; formal-checked]** Every actual vorticity coefficient is bounded by the genuine
spatial critical-vorticity receiver.  The honest pointwise band estimate is therefore

```text
norm(P_S omega(t,q)) <= card(S) * norm(omega(t))_infinity.
```

For a radius-`R` cube the payment is exactly `(2R+1)^3`.  This theorem is useful because it is too
weak in precisely the correct way: it retains the population cost which an arbitrary scalar
`middle` placeholder had hidden.

**[open]** The mode-count loss cannot yield the BKM middle-shell estimate.  At dyadic level `j` it
grows cubically with the aperture instead of costing one uniform critical-vorticity payment.
Removing it requires cancellation in a suitably smooth annular multiplier kernel.  A sharp cube
or Dirichlet projector should not be expected to have a uniform `L1` kernel bound.  Thus the next
analytic owner is not another cardinality argument; it is a periodic smooth
Littlewood--Paley/Calderon--Zygmund kernel theorem with its normalization and boundary chart
explicit.

## Linear diffusion now has an exact finite owner

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesFiniteFourierHeat.lean` defines a state over any finite
frequency population and the exact diagonal multiplier

```text
exp (-nu * t * (2*pi)^2 * |k|^2).
```

It proves the zero-time identity, exact semigroup composition, preservation of the Fourier
divergence constraint, the exact finite energy formula, energy nonexpansion for nonnegative
viscosity and elapsed time, and nonnegative viscous loss.

**[established-bounded; formal-checked]** This is the first explicit heat/Stokes transport owner
on the present Fourier line, but it is finite.  It proves neither an infinite diagonal operator
on a weighted Sobolev carrier nor a smoothing estimate between different Sobolev orders.  It also
contains no nonlinear convolution, Galerkin convergence, solution construction, or continuation
claim.

## The actual unforced PDE now produces its third-order commutator

**[proved-derived; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesH3Production.lean` proves the scalar third Leibniz split
and instantiates it on each Jacobian--velocity product face along an arbitrary affine spatial
line.  The third derivative of advection is exactly the sum of the top transport face and the
three lower commutator faces carrying coefficients `1,3,3`.

**[proved-derived; formal-checked]** For an actual zero-force `OpenPeriodicSolutionOn`, the module
derives the component momentum equation from the existing solution carrier, takes three spatial
line derivatives, substitutes the commutator split, and returns

```text
D^3(time jet) + top transport
  = nu * D^3(Laplacian velocity)
      - D^3(pressure gradient)
      - lower commutator remainder.
```

The accompanying norm theorem bounds the resulting PDE defect by the explicit lower Leibniz
population.  No fourth spatial derivative remains in that defect receiver.  Neither the
differentiated equation nor its estimate is supplied as a premise.

**[established-bounded; formal-checked]** This closes one local algebraic edge, not the H3 energy
law used by `NavierStokesH3Continuation`.  It treats pure third derivatives along one direction;
the full periodic energy estimate must include the complete mixed multi-index population, pair
the equation with those derivatives, integrate, cancel transport and pressure, make viscosity
dissipative, and bound the summed commutator.

**[open]** The current `periodicH3DerivativeEnergy` squares operator norms of
`iteratedFDeriv`.  Operator norm is not a quadratic Hilbert receiver and is not differentiable at
every operator.  Consequently the old derivative premise cannot honestly be discharged merely by
rewriting the new pointwise identity.  The correct next carrier is a coordinate/Frobenius
quadratic Sobolev energy, followed by norm comparison to whichever high-order receiver the final
continuation interface uses.

## The open terminal face has a path-independent C0 trace

**[conditional; formal-checked]**
`ElementaryHolonics/Millennium/NavierStokesTerminalTrace.lean` descends every strict-tail velocity
slice to the genuine compact torus.  Its control structure requires exactly a Lipschitz law in the
Banach space `C(SpatialTorus, Space)`; it carries no decorative H3 premise and derives no such law
from the separate scalar high-order bound.

**[proved-derived; formal-checked]** The strict tail is proved dense in its closed completion.
Uniform extension then constructs a canonical terminal torus field and proves convergence along
the complete terminal filter.  An addressed dyadic approach is separately constructed and proved
to reach the same value; any terminal trace defined by that sequence equals the full-tail
extension.  The pulled-back Euclidean trace is continuous and exactly one-periodic.

**[interpretation]** This is a precise instance of a face as perceived by a receiver.  The source
has no value at the open time `T`, while the continuous-torus-field receiver completes the strict
tail.  Lipschitz transport makes the returned boundary face independent of the chosen approach.
Without that transport receipt, selecting one dyadic subsequence would not establish a unique
terminal face.

**[open]** The returned trace is only `C0`.  It does not yet retain three spatial jets, prove
pointwise divergence at the limit, or found a local restarted Navier--Stokes solution.  A scalar
uniform H3 integral receiver alone does not supply the time-Lipschitz premise.  A stronger trace
route needs a genuine Sobolev carrier plus time-current bounds, or an Aubin--Lions/Rellich-type
compactness theorem with enough strength to feed local well-posedness.

## What the four returns do to the continuation composite

```text
actual open periodic solution
  |-- curl / quotient --> genuine torus vorticity
  |-- Fourier receiver --> actual finite dyadic populations
  |                         \-- [OPEN] smooth-kernel uniform shell estimate
  |-- differentiate PDE --> exact 1/3/3 third-order commutator
  |                         \-- [OPEN] mixed quadratic H3 integration
  |-- finite Stokes flow --> exact diagonal semigroup
  |                         \-- [OPEN] infinite smoothing + Duhamel contraction
  \-- tail transport -----> path-independent C0 terminal trace
                            \-- [OPEN] H3 trace / local restart

finite critical-vorticity integral
  --> logarithmic Gronwall bound
  --> [OPEN uniform restart radius]
  --> already-proved seam + overlap uniqueness
  --> compatible extension past T
```

**[established-bounded]** The former arbitrary `OpenH3FrequencyComb` testimony now has genuine
finite candidate fields beneath it, but the theorem that gives each middle shell a uniform
critical-vorticity payment is still absent.  The former arbitrary H3 production premise now has an
actual pointwise PDE commutator beneath it, but the differentiable quadratic energy and periodic
integrated estimate are still absent.  The uniform restart interface remains a real analytic
port; neither a C0 trace nor the finite heat semigroup fills it.

**[counterexample]** The force obstruction from the preceding phase remains decisive.  The final
unconditional route must stay at zero force, or state explicit future regularity and compatibility
of the force.  The new H3 production theorem therefore specializes to zero force rather than
narrating through an arbitrary-force premise.

## Recommended order of the next squeeze

**[open]** First replace the operator-norm-square H3 receiver with a finite
coordinate/Frobenius quadratic energy containing all derivatives of orders zero through three.
Prove positivity, exact differentiation, and comparison with the existing derivative receiver.

**[open]** Next lift the third-directional identity to all mixed multi-indices and
integrate it on the periodic torus.  The target return is the actual zero-force inequality

```text
E3'(t) <= C * norm(Du(t))_infinity * E3(t),
```

with transport and pressure cancelled and viscosity retained as a nonpositive term.

**[open]** In parallel replace sharp shell indicators by a smooth finite-support
dyadic partition on `Z^3`; prove a scale-uniform `L1` bound for the annular kernels, then attach
Hodge inversion to obtain one `norm(omega)_infinity` payment per middle shell and weighted-Sobolev
decay for the high tail.  Only after those estimates stand should the concrete projectors be
assembled into `OpenH3FrequencyComb`.

**[open]** Extend the finite diagonal heat owner to the Fourier Hilbert basis and a
weighted periodic Sobolev space.  Prove semigroup smoothing, a Leray/divergence-free closed
subspace, the bilinear advection estimate, and a Duhamel contraction whose radius depends only on
the H3 bound.  Translate that local theorem uniformly along the controlled tail; the existing seam
and uniqueness owners can then construct the extension.

**[interpretation]** In holonic terms, the current obstruction is no longer an unnamed missing
bridge.  The dyadic aperture returns its exact growing population, the commutator returns its
lower interaction faces, the heat passage returns its finite diagonal transport, and the terminal
receiver returns a unique boundary face.  The open fibre is the scale-uniform analytic law which
lets those four exact finite/local returns commute with completion.

## Validation receipt

**[established-bounded; formal-checked]** The four owner-local direct Lean checks ran in parallel
and returned exit status zero in 14.61 s, 15.15 s, 7.34 s, and 14.41 s respectively.  Printed
audits use only `propext`, `Classical.choice`, and `Quot.sound`; a declaration-oriented scan found
no `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration.  After the independent
audit removed the terminal owner's unused H3 field, that changed owner was checked again directly
in 13.9 s with exit status zero.

**[established-bounded; formal-checked]** The first aggregate receiver returned exit status zero
in 21.63 s, after which an independent audit supplied a new falsifier: the terminal carrier
retained an unused H3 field and two module descriptions overstated their scope.  Those declarations
and descriptions changed.  The final `lake build ElementaryHolonics` therefore ran on a different
closure from `soma/formal/elementary-holonics`, returned exit status zero in 22.81 s, and completed
3,985 jobs.  Its code closure was `ElementaryHolonics.lean` plus the four new modules and their
imported predecessors; its purpose was to test the corrected coherent aggregate closure.
Pre-existing linter warnings elsewhere in the aggregate remain outside this phase.
