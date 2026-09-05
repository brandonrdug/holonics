# The local core has a periodic realization and its pressure retains exterior torque

**Authority:** Brandon's standing
[moving-frame goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
MFR3 continues. This return constructs the periodic initial field; the complete pressure and
momentum residual for that field is the next source calculation. MFR4 owns its quantitative
residual/stability closure. The concurrent HNP campaign is independent.

## The finite core becomes an actual field

[definition] Use the exact Euler coefficients through radial mode 28 and the corrected
first-viscosity coefficients through mode 14 from the
[preceding return](2026-09-05_MFR3_THE_FORCED_AXIS_RETURNS_A_VISCOUS_RESPONSE_AND_THE_INNER_CHART_RETAINS_PRESSURE.md).
Their axial Taylor budgets remain `61-2m` / `60-2m` for Euler `W,J`, and `29-2m` / `28-2m`
for the viscous response. `J=a*Omega`, `X=a^2`; the previous convention `J=X*G` is identical
because `Omega=a*G`. The positive amplitude root and the selected `Y,E` retain their prior
definitions. Keep `T=W1_14[z]` and `L=J0_28[z^4]` as free real coefficients.

[definition] Let `W_mu,J_mu` be the **complete finite polynomials** produced by these
coefficients, with the `L*s^28*z^4` angular term restored. Set

```text
h(s,z) = sum_m W_mu,m(z) s^m / (2(m+1)),
g(s,z) = -sum_m J_mu,m(z) s^(m+1) / (2a(m+1)),
A(x,y,z) = (-y*h, x*h, g),     s=x^2+y^2.
```

[established-bounded; computational-witness]
[construct_periodic_potential.py](../experiments/mfr3_periodic_core/construct_periodic_potential.py)
reuses the actual exact FLINT recurrence, returns every coefficient, and independently recovers
`W_mu=2h+2s*h_s` and `J_mu=-2a*g_s` by differentiation. The
[receipt](../experiments/mfr3_periodic_core/periodic_potential_receipt.json)
retains both free coefficients and the exact selectors. The generated coefficient payload is
preserved in `.local/mfr3-periodic-core/periodic_potential.json`; the script regenerates it.
No sampled root or floating coefficient defines the field.

[proved-derived; formal-checked] `NavierStokesCoreVectorPotential` constructs arbitrary finite
bivariate polynomial potentials and proves their smoothness. Its actual Cartesian curl is

```text
U = (x*V-y*Omega, y*V+x*Omega, W),
V=-h_z,  Omega=-2g_s,  W=2h+2s*h_s.
```

It proves smoothness, divergence zero and preservation of periodicity for the actual curl,
using the existing derivative-curl and mixed-derivative owners. The coefficient reconstruction
above remains a computational witness; the generic calculus theorem is kernel checked.

[definition] The finite polynomial agrees with the earlier analytic axis at the retained
jets. No equality with that entire analytic axis, radial convergence, or vanishing of the
unretained nonlinear products is asserted. The polynomial's complete residual includes those
products, the earlier quadratic-viscosity source and the cutoff region.

## A periodic source with a preserved local germ

[proved-derived; formal-checked] For a smooth potential `B` and an actual Mathlib
`ContDiffBump(0)` of outer radius less than `1/2`, `NavierStokesPeriodicCore` constructs

```text
A_per(x) = sum_{n in Z^3} b(x-n) B(x-n),
u_initial = curl A_per.
```

Integer lattice centres are separated by at least one. In a neighborhood of every point,
only one translate can contribute; the sum is therefore locally a smooth translated core.
The resulting potential and velocity are smooth and unit-periodic. The velocity is divergence
free and equals `curl B` throughout the inner ball. Equality on that open ball preserves the
entire velocity germ of this finite polynomial field.

[proved-derived; formal-checked] Physical scaling uses
`B(x)=(ell/q)*A(x/ell)`. The actual curl is `q^(-1)*U(x/ell)` when `ell!=0`.
The explicit `physicalCoreBump` has inner radius `ell/8` and outer radius `ell/4`;
`0<ell<2` pays lattice separation. With `q>0` and `mu=nu*q/ell`, this is the MFR1 convention.
`completedVelocity_periodic_local_existence` composes the constructed initial field with
the existing periodic local-existence theorem and returns a positive lifespan and an actual
global pressure for every `nu>0`.

[open] This local-existence return does not show that its solution follows the proposed
moving finite-polynomial family. Its actual global pressure has yet to be evaluated against
that family's local pressure comparison. Dilation still changes the rescaled torus period
to `1/ell`; the construction does not replace it with a fixed normalized unit torus.

## The pressure contribution survives the angular receiver

[proved-derived; formal-checked] `NavierStokesExteriorTorque` uses arbitrary Cartesian pressure.
For `ell_ang=x*U_y-y*U_x`, drift `U+beta*x`, and actual axial vorticity `omega_z`, it derives

```text
d_tau ell_ang = angular_projection(momentum_residual)
               - (x*P_y-y*P_x)
               + mu*(Laplacian ell_ang - 2*omega_z)
               - (alpha-beta)*ell_ang.
```

The trajectory derivative is an actual joint spacetime chain rule. The pressure torque is
the derivative in direction `(-y,x,0)`, including at the axis. The `-2*omega_z` term comes
from differentiating the position carrier in the scalar Laplacian. MFR1's physical momentum
theorem supplies this residual in the centred unforced chart, with arbitrary Cartesian pressure.

[proved-derived; formal-checked] Reconstruction by `ell/q` cancels the normalization current
and retains `nu*D-(ell/q)*torque`. Rescaled pressure torque equals `q^2` times the physical
torque. Equal local Poisson sources leave a harmonic pressure difference; the formal theorem
does not discard its gradient or angular derivative.

[established-bounded; computational-witness] The independent
[periodic pressure experiment](../experiments/mfr3_periodic_pressure/derive_jet_flat_pressure.py)
constructs, in coordinates of period `2*pi`,

```text
F(theta)=sin(theta)*((1-cos(theta))/2)^N,  g(z)=sin(z),
v=(-F(x)*g'(z), -F(y)*g'(z), (F'(x)+F'(y))*g(z)).
```

For `N=32`, its velocity vanishes to order 65 at the origin. Exact Fourier derivatives verify
the leading order of `F`; the displayed velocity then has zero jets through order 64.
Nevertheless its uniquely normalized finite-Fourier pressure has

```text
-0.005457852 <= p_zz(0) < -0.005457851,
p_xx(0)=p_yy(0)=-p_zz(0)/2,
-0.001796841 <= [x^3*y](x*p_y-y*p_x) < -0.001796840.
```

The opposite quartic torque coefficient is its negative. The
[receipt](../experiments/mfr3_periodic_pressure/pressure_receipt.json)
contains exact rational values and enclosures checked by rational inequalities. All divergence
and pressure Poisson coefficients vanish exactly. An independent compact expression verifies
`trace(Dv^2)` against the full Jacobian products; the Fourier zero mode and the source value
at the origin are separately zero. The `N=1` control returns `p_zz(0)=-389/2340` and quartic
torque coefficient `1379/7020`. Unit-torus pullback scales first derivatives by `2*pi` and
second derivatives and the Poisson source by `(2*pi)^2`.

[counterexample; computational-witness] Thus vanishing of these finite velocity jets does
not imply vanishing of the pressure Hessian or local angular torque. This witness is an
independent periodic variation, not the computed pressure of the full MFR3 core.

[proved-derived] More generally, for a smooth periodic divergence-free field `u` and this `v`,
the Poisson source of `u+t*v` is
`trace(Du^2)+2t*trace(Du*Dv)+t^2*trace(Dv^2)`. Linearity of the mean-zero periodic Poisson
inverse gives the same quadratic decomposition of pressure. Its axial Hessian coefficient
at order `t^2` is the nonzero value above. Consequently pressure cannot be constant across
this family, although all its velocity jets through order 64 coincide. This is a written
algebraic consequence of the finite witness and the periodic Poisson inverse described in
[Tao's local well-posedness notes](https://terrytao.wordpress.com/2018/09/16/254a-notes-1-local-well-posedness-of-the-navier-stokes-equations/),
in the normalized periodic-pressure discussion leading to equation (33).

[interpretation] This is a concrete null-fibre distinction useful to Holonics: a local
velocity-jet receiver returns zero on the added field, while a pressure receiver separates it.
The exterior source must remain available to the later receiver. The example makes no
singularity claim.

## Verification and next construction

[established-bounded; process-audit] The primary agent reviewed the delegated sources,
replaced a sine-based torque observable with the actual Cartesian angular derivative, required
independent source and derivative checks, and replaced unchecked sign-based enclosures with
exact outward rational bounds. The temporary low-degree potential example was replaced by
the arbitrary finite bivariate constructor used above. Drafts remain recoverable under `/tmp`.

[established-bounded; process-audit] Verification returned with exit status zero:

- `lake build ElementaryHolonics.Millennium.NavierStokesExteriorTorque` (8,730 jobs).
- `lake build ElementaryHolonics.Millennium.NavierStokesPeriodicCore` (3,701 jobs), including
  the final finite-polynomial and physical-potential owners.
- `lake build ElementaryHolonics` (9,891 jobs), including the final arbitrary-pressure laws.
- `/tmp/holonics-mfr3-symbolic/bin/python research/experiments/mfr3_periodic_core/construct_periodic_potential.py`,
  with its complete output retained in the local coefficient artifact and summarized in the receipt.
- `/tmp/holonics-mfr3-symbolic/bin/python research/experiments/mfr3_periodic_pressure/derive_jet_flat_pressure.py`,
  with the final exact output in `pressure_receipt.json`.

The final new endpoint axiom prints contain only `propext`, `Classical.choice` and `Quot.sound`.
Lean is 4.33.0 with the repository's pinned dependencies; the coefficient constructor uses
python-flint 0.9.0 / FLINT 3.6.0, and the pressure witness uses Python rational arithmetic.
No runtime/Cargo behavior was changed or separately tested by this mathematical return.

[open] Next evaluate the complete global pressure and oriented momentum residual of the
specified finite-core family, including its cutoff region, moving bump, free coefficients,
image coupling and all unretained products. A pressure or transport obstruction changes that
family; it must not prompt another unrelated local coefficient extension. MFR4 then requires
the quantitative estimate that could absorb the returned residual. MFR5's arithmetic sign
and the RH endpoint remain open.
