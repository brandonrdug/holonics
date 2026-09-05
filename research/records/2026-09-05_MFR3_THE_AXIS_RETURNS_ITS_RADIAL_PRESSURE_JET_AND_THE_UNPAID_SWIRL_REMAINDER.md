# MFR3: the axis returns its radial pressure jet and the unpaid swirl remainder

**Date:** 2026-09-05. **Campaign:** the
[standing MFR goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
**Predecessor:** [the physical coherent source, local flux and coupled axis](2026-09-04_MFR3_THE_COHERENT_SOURCE_REACHES_A_PHYSICAL_FIELD_AND_THE_LOCAL_FRAME_RETURNS_ITS_FLUX.md).
**Position:** MFR3 remains in progress. **Grades:** per claim. The record separates formal
source identities, the actual primitive construction, symbolic checks and further written analysis.

## The Cartesian source retains the axis

[definition] Use the meridional receiver `rho=x^2+y^2`, with the actual Cartesian occurrence
retained in reconstruction:

```text
u(x,y,z) = (x*V(rho,z)-y*Omega(rho,z),
            y*V(rho,z)+x*Omega(rho,z), W(rho,z)).
```

The map `(x,y,z)->(rho,z)` is a rotational quotient receiver, not an invertible three-dimensional
coordinate change. The Cartesian field uses no division by the radius. The investigation tests
stationary normalized Euler profiles. For the Navier–Stokes source, the transported viscosity
and profile time current remain additional terms of the actual MFR1 equation.

[proved-derived; formal-checked] `NavierStokesAxisymmetricChart` derives the Cartesian derivative,
divergence, normalized Euler momentum, pressure gradient and curl from the actual coefficient
functions. With subscripts denoting the two actual partial derivatives,

```text
div u = 2*V + 2*rho*V_rho + W_z,
Du[u] + beta*Du[(x,y,z)] + alpha*u = (x*A-y*C, y*A+x*C, B),

A = (alpha+beta)*V + (W+beta*z)*V_z
      + 2*rho*(V+beta)*V_rho + V^2-Omega^2,
C = (alpha+beta+2*V)*Omega + (W+beta*z)*Omega_z
      + 2*rho*(V+beta)*Omega_rho,
B = alpha*W + (W+beta*z)*W_z + 2*rho*(V+beta)*W_rho.
```

An axisymmetric pressure has gradient `(2*x*P_rho,2*y*P_rho,P_z)`. The curl of the displayed
momentum field retains the pressure-compatibility current `2*B_rho-A_z`, both axial swirl
derivatives, and the third component `2*C+2*rho*C_rho`.

[proved-derived; formal-checked] When `rho!=0`, a zero Cartesian residual reconstructs
`A=C=B=0`. At `x=y=0`, its value tests only `B`; every `A,C` remains behind that value receiver.
The derivative receiver recovers `2*C(0,z)` as the third curl component. This is a source-bound
instance in which a zero face retains nonzero derivative information.

[proved-derived] Pressure closure on the meridional domain requires `C=0` and
`A_z=2*B_rho`. These follow from `P_rho=-A/2`, `P_z=-B` and equality of mixed pressure derivatives.
They are additional source relations; solving the axis swirl equation does not supply them.

[established-bounded; computational-witness] The independent
[Cartesian symbolic calculation](../experiments/mfr3_periodic_core/derive_radial_continuation.py)
also checks the Laplacian coefficients. The radial and angular entries use
`4*rho*f_rhorho+8*f_rho+f_zz`; the axial entry uses
`4*rho*W_rhorho+4*W_rho+W_zz`. A time-dependent viscous profile adds its actual time jets and
subtracts `mu` times these expressions. The script differentiates the Cartesian pressure source
as well as the velocity; its pressure-gradient check is not an equality of a formula with itself.

## An actual positive axial profile and its first obstruction

[proved-derived; formal-checked] `NavierStokesAxialPrimitive` constructs, from a positive smooth
`F`, the reciprocal axial coordinate and strain

```text
k=alpha+2*beta,
I(z)=integral_0^z 1/F(t) dt,
Gamma(z)=k*F(z)*I(z),
W0(z)=Gamma(z)-beta*z.
```

Actual interval differentiation proves
`(W0+beta*z)F'+(alpha+beta-W0')F=0`. Positivity gives `I(z)!=0` for `z!=0`; thus `Gamma(z)!=0`
away from the axis when `k!=0`. The smoothness of `I` and `W0` is derived from the same source.
`I` is an axial spatial coordinate, not the physical clock of MFR1.

[proved-derived; formal-checked] `NavierStokesAlgebraicAxis` instantiates that construction with

```text
F(z)=(1+z^2)^(-p/2),
F(0)=1,    F'(0)=0,    F''(0)=-p,
W0(0)=0,   W0'(0)=alpha+beta,   W0''(0)=0,   W0'''(0)=-2*k*p.
```

The profile is everywhere positive and smooth for every real `p`. The reciprocal integrals
are actual definitions; the displayed axis equation and jets are not input ports.

[definition] For the proposed concentration window `beta<alpha<=3*beta/2`, retain the prior
axial-tail selection `p=1+alpha/beta`, hence `2<p<=5/2`. The formal source construction above
is more general; this selection does not assert three-dimensional energy control.

[proved-derived; formal-checked] The affine-radial lift

```text
u0=(-x*W0'/2-y*F, -y*W0'/2+x*F, W0)
```

is smooth and exactly incompressible. `NavierStokesAxialLift` derives its actual normalized
momentum coefficients

```text
A0=(W0')^2/4-F^2-Gamma*W0''/2-(alpha+beta)*W0'/2,
C0=Gamma*F'+(alpha+beta-W0')*F,
B0=Gamma*W0'+alpha*W0.
```

Any smooth pressure completing this Cartesian momentum would force both `C0=0` and `A0'=0`.
The first condition holds for the constructed axis, but its actual pressure coefficient has

```text
A0'(0)=0,       A0''(0)=2*p*(1+k^2).
```

For `p>0`, this contradicts `A0'=0`. `algebraicAxialLift_has_no_pressure_completion` proves
that no global `C2` pressure completes this particular normalized affine-radial field. The
obstruction is obtained from the derivative at the axis, without a numerical far-field inference.

## Pressure determines the first radial correction

[definition] Retain the next radial profiles, with all functions of `z`:

```text
Z(rho,z)=W0(z)+rho*H(z),
Omega(rho,z)=F(z)+rho*K(z),
V(rho,z)=-W0'(z)/2-rho*H'(z)/4.
```

[proved-derived; formal-checked] `NavierStokesFirstRadialLift` derives the actual profile jets
and proves that the reconstructed Cartesian field is divergence-free. Its momentum coefficients
return complete quadratic polynomials in `rho`:

```text
B(rho,z)=B0(z)+rho*B1(z)+rho^2*B2(z),
B1=Gamma*H'+k*H,                         B2=H*H'/2,

C(rho,z)=C0(z)+rho*C1(z)+rho^2*C2(z),
C1=Gamma*K'+(alpha+3*beta-2*W0')K + H*F'-H'*F/2,
C2=H*K'-H'*K.
```

The radial coefficient at `rho=0` is the prior `A0`. The owner also differentiates the actual
momentum coefficient functions to recover `B_rho(0,z)=B1(z)` and `C_rho(0,z)=C1(z)`.

[proved-derived] The first pressure-compatibility row therefore requires
`Gamma*H'+k*H=A0'/2`. Using the constructed axis relation, its integrating factor gives

```text
J(z)=integral_0^z A0'(t)/F(t) dt,
H(z)=F(z)*J(z)/(2*Gamma(z))       for z!=0.
```

Indeed `(Gamma*H/F)'=A0'/(2F)`. The homogeneous integration constant is removed by regularity
at the axis, because `Gamma(0)=J(0)=0` and `Gamma'(0)=k`.

[proved-derived; formal-checked] The primitive owner proves this actual off-axis differential
identity and derives its nonzero denominator from `F>0`, `k!=0`, `z!=0`.
`NavierStokesAxisRegularization` identifies the integral quotient with the ratio of its
derivative-extended slopes at zero. `NavierStokesAxisFirstJet` then uses the actual primitives
and one L'Hopital step to prove

```text
H(0)=0,                 H'(0)=A0''(0)/(4*k).
```

This is an actual `HasDerivAt` result. The zero factor `Gamma(0)` was not used to disguise an
unadmitted totalized derivative. For the constructed algebraic source, the final owner proves

```text
H'(0)=p*(1+k^2)/(2*k),
```

differentiability of `H` everywhere, and the pressure-correction identity at every `z`.
For the concentration rates and `p>0`, this derivative is positive even though `H(0)=0`.

## Swirl determines the next carrier and leaves an explicit remainder

[proved-derived; formal-checked] Matching `C1(0)=0` forces
`K(0)=H'(0)/(2*(beta-alpha))`. In the proposed window `beta<alpha`, this value is negative.
The constructed source therefore has `C2(0)=-H'(0)K(0)>0` after the first swirl row is matched.
`algebraic_firstSwirl_payment_leaves_quadratic_defect` proves the strict positivity for the
actual constructed `F,W0,H` and an admitted derivative of `K` at the axis.

[proved-derived; computational-witness] The explicit remaining coefficient is

```text
d = p^2*(1+k^2)^2 / [8*k^2*(alpha-beta)] > 0.
```

At `z=0`, after `C0` and `C1` are matched, the complete truncated swirl coefficient is
`C(rho,0)=d*rho^2`. Thus the angular momentum residual has size `d*r^5` at radius `r`, and
its third curl component is `6*d*r^4`. The source and oriented remainder are retained; the
finite radial truncation is not promoted to an exact solution. The symbolic receipt independently
derives the axis jets from the successive equations before checking these expressions.

## A regular construction for the first swirl correction

[proved-derived] The first swirl equation can be solved as a separate regular-singular
continuation. Set `K=F^2*L`. From the exact axis relation,

```text
Gamma*L' + (beta-alpha)*L = R,
R=H'/(2*F)-H*F'/F^2.
```

With the reciprocal axial coordinate `q=I(z)`, let `zeta` denote its inverse on the relevant
interval and `Rtilde(q)=R(zeta(q))`. Because `Gamma=k*F*I` and `I'=1/F`, the equation becomes

```text
q*dL/dq - gamma*L = Rtilde(q)/k,
gamma=(alpha-beta)/k.
```

Here `q` is spatial. In the present scale window, `0<gamma<=1/7`. A regular solution is

```text
L0=Rtilde(0)/(beta-alpha),
L(q)=L0+(1/k)*integral_0^1 [Rtilde(t*q)-Rtilde(0)]*t^(-gamma-1) dt,
K(z)=F(z)^2*L(I(z)).
```

Differentiating and integrating by parts in `t` gives the displayed equation. The subtraction
is essential: on compact `q` intervals the numerator is `O(t)`, leaving an integrable
`t^(-gamma)` bound. Higher `q` derivatives carry `t^n`, so smooth source data give a smooth
regular solution. The homogeneous branches `c*|q|^gamma` are continuous at zero but have no
finite first derivative there unless `c=0`; differentiability selects the regular branch.

[proved-derived] For the positive smooth algebraic source, the required smooth extension of
`H` can also be seen from

```text
H(z) = [integral_0^1 A0'(t*z)/F(t*z) dt]
        / [2*k*integral_0^1 1/F(t*z) dt].
```

The denominator never vanishes, and the fixed compact integration interval permits every
parameter derivative locally. These smoothness and full `K` constructions are written analytic
returns. The new Lean endpoint proves the actual first derivative of `H`; it does not yet
formalize this complete smooth integral inverse or the constructed `K`.

[open] The next return must continue or replace the finite radial expansion while controlling
the retained `C2` and pressure residuals, establish the required radial convergence/weighted
control, and match the actual periodic exterior. The full time current and viscosity belong in
that construction. No periodic concentrating solution, stability margin or finite-time singularity
has returned. The independent RH arithmetic-sign investigation remains open under the same goal.

## Owners and verification

[definition] Seven owners under `formal/elementary-holonics/ElementaryHolonics/Millennium/`:
`NavierStokesAxisymmetricChart`, `NavierStokesAxialLift`, `NavierStokesAxialPrimitive`,
`NavierStokesAxisRegularization`, `NavierStokesAxisFirstJet`, `NavierStokesFirstRadialLift`,
and `NavierStokesAlgebraicAxis`.

[established-bounded; process-audit] Lean 4.33.0 returned the final checks from
`formal/elementary-holonics/`:

```sh
lake build ElementaryHolonics.Millennium.NavierStokesAlgebraicAxis
lake build ElementaryHolonics
```

The focused closure returned 3,419 jobs and the live umbrella 9,871. These are build scopes,
not counts of new theorems. Decisive axiom reports from all seven new owners contain only
`propext`, `Classical.choice` and `Quot.sound`. The terminal import, owner map and current
position are integrated. Source review and changed-line whitespace review returned. The written
smooth integral construction for `K` remains outside this formal acceptance scope.

[established-bounded; computational-witness] The symbolic command is
`python research/experiments/mfr3_periodic_core/derive_radial_continuation.py` with SymPy 1.14.0.
Its actual Cartesian derivative assertions, independently solved axis jets and full radial
polynomial checks returned; [the JSON receipt](../experiments/mfr3_periodic_core/radial_receipt.json)
retains the precise expressions and assumptions. This is derivative algebra, not a numerical
stability or existence certificate. Concurrent HNP changes remain owned by that session.
