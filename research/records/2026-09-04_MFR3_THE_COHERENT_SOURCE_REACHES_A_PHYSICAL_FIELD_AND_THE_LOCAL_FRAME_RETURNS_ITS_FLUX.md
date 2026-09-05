# MFR3: the coherent source reaches a physical field and the local frame returns its flux

**Date:** 2026-09-04. **Campaign:** the
[standing MFR goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
**Predecessor:** [the fixed-profile exclusions and coefficient controls](2026-09-04_MFR3_THE_PERIODIC_SOURCE_REJECTS_FIXED_PROFILES_AND_RETURNS_ITS_ENERGY_AND_COHERENT_FEEDS.md).
**Position:** MFR3 remains in progress. **Grades:** per claim. Formal acceptance, written
derivations and the symbolic receiver check have separate scopes.

## The coherent population now has an actual source

[proved-derived; formal-checked] `NavierStokesFiniteFourierSmoothReconstruction` upgrades the
existing real Fourier reconstruction to `C-infinity` when the actual unweighted coefficients
have one common finite support. It reduces the existing character series to its finite sum;
there is no replacement Fourier engine. `NavierStokesCoherentTriadReconstruction` instantiates
that result with the predecessor's population at `+/-e0,+/-e1`, proves its reality and
divergence freedom, and recovers every coefficient exactly from the resulting real smooth
periodic field `witnessVelocity`.

[proved-derived; formal-checked] The existing actual-advection convolution bridge then returns
the complete source at `k=e0+e1`. Its third-component squared norm is twice the complete
diagonal squared-feed sum; the corresponding coefficient inequality holds exactly for
`kappa>=1`. This now concerns the actual initial field's `Du(u)`, rather than a freely supplied
coefficient population. The initial velocity coefficient at `k` is still exactly zero.

[proved-derived; formal-checked] `NavierStokesInitialSpatialContinuity` derives continuity of
the ordinary spatial derivative and actual advection on the complete initial-inclusive slab
`univ × Ico 0 T`. It composes the source's continuous joint derivative within the slab with
the spatial inclusion; it does not extend the physical time domain past zero. The actual
periodic velocity and advection descend to continuous torus fields, and their Fourier
coefficients remain continuous at time zero. Accessors identify them with the existing strict
interior receivers.

[proved-derived; formal-checked] For every `nu>0`, the existing `periodicLocalExistence` theorem
now supplies an actual unforced `OpenPeriodicSolutionOn` from `witnessVelocity`. Initial equality
and the new coefficient continuity give a positive interior time with nonzero third advection
component at `k`. Since `k_2=0`, this component survives the Leray pressure projection, including
the negative sign of the nonlinear term on the right of the velocity equation.
`witness_local_solution_has_nonzero_projected_source` is the composed physical source result.

[open] The positive-time theorem asserts nonzero projected nonlinear source. It does not yet
assert a positive-time value of the complete coherence defect, or creation of a nonzero velocity
coefficient at `k`. Those stronger receivers require their own time-evolution and complete
feed-diagonal passages. No finite-time singularity follows from the present control case.

## The local moving frame retains its complete energy flux

[proved-derived; formal-checked] The existing `NavierStokesPeriodicFlux` proof now exposes its
pre-cancellation result as `integral_divergence_unitCube_eq_boundaryFlux`.
`unitCubeBoundaryFlux` is the sum of the actual front-face integrals minus the back-face
integrals of the corresponding normal components. The old periodic cancellation theorem
composes this result with equality of opposite faces. Its statement and hypotheses are preserved.

[definition] For the same MFR1 source chart, write

```text
U(y,s)=q(s) u(c(s)+ell(s)y,theta(s)),    P=q^2 p,
theta'=ell*q,    mu=nu*q/ell,    d=ell'/ell,    v=c'/ell,    r=q'/q,
e=|U|^2/2,    G=sum_i U_i grad U_i,
D=sum_i |grad U_i|^2,
J=e (U-d*y-v)+P*U-mu*G.
```

`D` retains the complete spatial gradient energy. `G` is the viscous energy flux, defined from
the actual component functions. For the exponential fixed-centre chart, `d=-beta`, `r=-alpha`;
therefore `J=(e+P)U+beta*e*y-mu*G`.

[proved-derived; formal-checked] `NavierStokesLocalEnergyFlux` derives from the actual rescaled
momentum, including force, the pointwise law

```text
partial_s e + div J = (2*r-3*d)e - mu*D + U dot [ell*q^2*f].
```

For any `C1` spatial selection `chi`, the corresponding law is

```text
chi*partial_s e + div(chi*J)
  = chi*((2*r-3*d)e-mu*D+U dot [ell*q^2*f]) + grad chi dot J.
```

Pressure work remains in the same flux as advection, viscosity and frame motion. It has not
been cancelled by importing the complete periodic energy theorem into a local core.

[proved-derived; formal-checked] For an unforced source and `C2` selection, the owner proves
integrability of the selected rate and returns

```text
integral_cube chi*partial_s e + boundaryFlux_cube(chi*J)
  = integral_cube chi*((2*r-3*d)e-mu*D) + integral_cube grad chi dot J.
```

The cube here is a declared fixed local chart receiver, with all six oriented face currents.
It is not identified with the expanding periodic cell. The statement integrates the pointwise
time derivative; it does not add a differentiation-under-the-integral theorem for the total
selected energy. It already exposes the exact local currents the next core/exterior attempt
must account for.

## A concrete modulated periodic core

[definition] The next attempt uses a smooth periodic envelope instead of a globally fixed
normalized profile. Set `b=2*pi*ell`, and, in coordinates `(x,y,z)`, define

```text
eta_b = exp(sum_j (cos(b*y_j)-1)/b^2),
v_j = sin(b*y_j)/b,    c_j = cos(b*y_j),
M = c_1+c_2-v_1^2-v_2^2,
T_b = curl(eta_b*e_z) = eta_b*(-v_2,v_1,0).
```

The first poloidal choice is `P_even=curl curl(eta_b*e_z)`, with components
`eta_b*(v_1*v_3,v_2*v_3,M)`. The revised choice keeps the same toroidal field and changes only
the poloidal potential:

```text
P_odd = curl curl(v_3*eta_b*e_z)
      = eta_b*(v_1*(v_3^2-c_3), v_2*(v_3^2-c_3), v_3*M),
U_b,lambda = T_b + lambda(s)*P_b.
```

The double curl's third component uses the transverse Laplacian, not the full Laplacian.
In the revised family the toroidal potential remains `eta_b*e_z`; multiplying it by `v_3`
would define a different family and change the receiver equations.

[proved-derived] Both choices are smooth and divergence-free for every `ell>0`, with literal
period `1/ell` in each normalized coordinate. They reconstruct a smooth unit-periodic physical
field by `u_app(x,theta(s))=a(s)U((x-c)/ell(s),s)`, with
`a=a0 exp(alpha*s)`, `ell=ell0 exp(-beta*s)`, `theta'=ell/a` and positive reference scales.
The initial field is smooth. The finite clock alone does not make this candidate solve momentum.

[proved-derived] The toroidal/poloidal energy cross term vanishes pointwise for either
choice. On the centred expanding cell, `|v_j|<=|y_j|` and
`eta_b<=exp(-2|y|^2/pi^2)`, using `1-cos t>=2t^2/pi^2` for `|t|<=pi`.
Thus bounded `lambda` gives a uniform polynomial-times-Gaussian energy majorant. The normalized
energy converges to that of the Gaussian profile and is bounded below by its nonzero toroidal
part. At `alpha=3*beta/2`, the physical energy prefactor `a^2*ell^3` is constant. These facts
meet the bounded-energy scaling test; they do not establish the full energy or momentum law.

[definition] For either choice, retain the exact normalized residual

```text
R = -beta*b*partial_b U + lambda'*P_b
      + DU[U] + beta*DU[y] + alpha*U - mu*Delta U + grad Pi,
mu=nu/(a*ell).
```

Here `partial_b` holds `lambda` fixed. `Pi` is the mean-zero pressure on the actual expanding
torus, obtained from `Delta Pi=-div(DU[U])`. The right side has zero mean by periodic divergence
integration. Its smooth Fourier solution retains the full pressure coupling. The time and
dilation terms are combined before testing the changing period.

## The first receiver fixes strain; the second rejects this profile

[proved-derived; computational-witness] The
[exact symbolic calculation](../experiments/mfr3_periodic_core/derive_receivers.py) differentiates
the declared potentials and residual, verifies divergence freedom and the energy cross term,
and returns the third component of `curl R` at the centre:

```text
even poloidal potential:  2*(alpha+beta) + 2*mu*(5+b^2),
odd poloidal potential:   2*(alpha+beta) - 4*lambda + 2*mu*(5+b^2).
```

Pressure drops out only after taking curl. The modulation derivative is retained in the
calculation; its third curled component vanishes exactly because `(curl P_b)_3=0`.

[proved-derived] For `alpha,beta>0` and `mu>=0`, the even choice fails already at the centre.
The odd choice adds the missing axial stretching: `U(0)=0`, `omega_3(0)=2` and
`partial_3 U_3(0)=2*lambda`. Its nonlinear vorticity contribution is `-4*lambda`. Exact momentum
would consequently require the specific modulation

```text
lambda(s) = [alpha+beta+mu(s)*(5+b(s)^2)]/2.
```

[proved-derived] For `alpha>beta>0`, `b->0` and `mu->0`, so this condition forces
`lambda->(alpha+beta)/2`. The revised Gaussian limit is

```text
g=exp(-(x^2+y^2+z^2)/2),
T_infinity=g*(-y,x,0),
P_infinity=g*(x*(z^2-1), y*(z^2-1), z*(2-x^2-y^2)).
```

Taylor expansion of the explicit sine/cosine envelope gives convergence of each spatial
derivative needed at a fixed receiver, and `-beta*b*partial_b omega_3->0` there. The third
vorticity component is independent of `lambda`, so no separate limit for `lambda'` is needed
for this receiver.

[proved-derived; computational-witness] On the axis `(0,0,z)`, the limiting third curled
residual is exactly

```text
2*(alpha+beta-beta*z^2)*exp(-z^2/2) - 4*lambda*exp(-z^2).
```

At `z=sqrt((alpha+beta)/beta)`, with the centre-required limiting modulation, this becomes
`-2*(alpha+beta)*exp(-(alpha+beta)/beta)`, which is strictly negative. In particular, at
`alpha=3*beta/2` it is `-5*beta*exp(-5/2)` at `(0,0,sqrt(5/2))`.

[proved-derived] The two receivers therefore exclude this one-parameter mixed-potential
family as an exact concentrating source throughout `beta<alpha<=3*beta/2`. An assumed exact
source would have zero curled residual at every chart time; its nonzero limit at the second
fixed receiver contradicts that requirement. The same local argument excludes the displayed
Euler family whenever the corresponding vanishing-viscosity premise holds. This is a written
analytic exclusion supported by exact derivative algebra, not a Lean theorem about this
specific trigonometric family.

## Construct the axial strain from the vorticity profile

[proved-derived] The failed pair identifies a coupled relation to construct next. For a smooth
axisymmetric stationary normalized Euler profile, write its near-axis azimuthal velocity as
`U_theta=r*F(z)+O(r^3)` and axial velocity as `U_z=W(z)+O(r^2)`. Smooth axisymmetry makes the
axis velocity `W e_z` and vorticity `2F e_z`. The third curled momentum equation therefore reads

```text
(W+beta*z)*F' + (alpha+beta-W')*F = 0.
```

This is the full axis relation, before division at a possible zero of `F`. It follows by
retaining both vorticity transport `W*(2F)'` and stretching `-(2F)*W'`, together with the
moving-frame terms `beta*z*(2F)' + (alpha+beta)*(2F)`.

[proved-derived] On an interval where `F>0`, the integrating factor gives the explicit
construction

```text
W(z) = -beta*z + F(z)*[W(0)/F(0)+(alpha+2*beta)*integral_0^z 1/F(t) dt].
```

Indeed differentiating `(W+beta*z)/F` gives `(alpha+2*beta)/F`. The symbolic apparatus checks
this substitution as well. For Gaussian `F=exp(-z^2/2)` and `W(0)=0`, l'Hopital's rule gives
`W(z)/z -> -beta`; retaining the Gaussian axial vorticity would require a nondecaying axial
velocity. The preceding Gaussian poloidal field does not supply it.

[proved-derived] A different axis construction uses `F(z)=(1+z^2)^(-p/2)`, `p>1`, and the same
explicit integral for `W`, with `W(0)=0`. Its asymptotic linear coefficient is
`-beta+(alpha+2*beta)/(p+1)`. Choosing `p=1+alpha/beta` cancels this coefficient. The first two
terms of the primitive,
`z^(p+1)/(p+1) + p*z^(p-1)/(2*(p-1))`, together with the binomial expansion of `F`, give
`W(z) ~ [beta*p/(p-1)]/z` as `z->+infinity`. In the current scale window this selects
`2<p<=5/2`. This pair satisfies the complete stationary axis equation at every finite `z`;
it has replaced an independently guessed strain parameter by a source-coupled construction.

[open] This is an axis profile, not a three-dimensional periodic solution. The next return must
extend it through the radial momentum and incompressibility relations, solve pressure and
match the actual exterior/periodic transport, or identify the next obstruction. Zero-vorticity
intervals must use the undivided equation. A surviving complete profile, residual and quantitative
stability estimate remain required. The RH source and its separate arithmetic-sign obligation
retain their standing scope.

## Verification and ownership

[established-bounded; process-audit] Lean 4.33.0 returned the final focused and umbrella checks
from `formal/elementary-holonics/`:

```sh
lake build ElementaryHolonics.Millennium.NavierStokesCoherentTriadReconstruction \
  ElementaryHolonics.Millennium.NavierStokesLocalEnergyFlux
lake build ElementaryHolonics
```

The focused closure returned 8,962 jobs and the live umbrella 9,864. These are build scopes,
not counts of new theorems. Decisive axiom reports for all four new owners and the revised
boundary owner contain only `propext`, `Classical.choice` and `Quot.sound`. The terminal imports,
owner map and current position are integrated. The new initial continuity includes the actual
time-zero boundary; the core-family exclusion and coupled axial construction remain written
derivations outside this Lean acceptance scope.

[established-bounded; computational-witness] The symbolic command is
`python research/experiments/mfr3_periodic_core/derive_receivers.py` with SymPy 1.14.0.
All assertions returned; [the receipt](../experiments/mfr3_periodic_core/receipt.json) retains
the exact receiver expressions. No numerical simulation, residual threshold or stability
margin is asserted by this calculation.

[definition] Four new formal owners are `NavierStokesFiniteFourierSmoothReconstruction`,
`NavierStokesInitialSpatialContinuity`, `NavierStokesCoherentTriadReconstruction`, and
`NavierStokesLocalEnergyFlux`, all under the existing `Millennium/` root.
`NavierStokesPeriodicFlux` now exposes the general boundary result used by its old periodic
cancellation. Concurrent HNP changes remain with their parallel owner.
