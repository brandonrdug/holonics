# MFR3: the second resonance closes and the moving swirl returns its viscous source

**Date:** 2026-09-05. **Campaign:** the
[standing MFR goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
**Predecessor:** [the analytic inverse, next sensitivity and circulation exterior](2026-09-05_MFR3_THE_ANALYTIC_INVERSE_RETAINS_ITS_RESONANCE_AND_THE_CIRCULATION_DEMANDS_AN_EXTERIOR.md).
**Position:** MFR3 remains in progress. **Grades:** per claim.

## The complete next forcing returns

[definition] Retain `alpha=3/2`, `beta=1`, `G_0(z)=(1+z^2)^(-5/4)`, squared swirl strength
`X=a^2>0`, and the free axial coefficient `Y=W_15[z^1]`. The prior root `P(X_*)=0` and
positive sensitivity `R(X_*)>0` remain standing. The new finite construction uses

```text
N_W(m)=61-2m,       N_G(m)=60-2m,       m=0..28.
```

[proved-derived] Store `J_m=X*G_m` in the computation. Then the angular term in the radial
momentum is `-(sum J_i J_j)/X`. Through pressure mode 28 its numerator is polynomial-divisible
by `X`: each product has at least one angular factor below mode 14. The mode-15 pressure row
reads the previous `J_14[z^2]` coefficient with multiplier `-4`, while its own `W_15[z]`
multiplier is zero. This determines the former and retains `Y`. Products contributing through
radial mode 28 cannot contain two factors whose `Y` dependence starts at mode 15, so the
retained construction remains affine in `Y`.

[established-bounded; computational-witness] The
[full recurrence](../experiments/mfr3_periodic_core/derive_full_second_resonance.py)
constructs every retained `W_m,J_m,V_m`, with `V_m=-W_m'/(2(m+1))`, by exact rational
polynomial arithmetic. Every nonzero transport divisor is rational and independent of `X,Y`.
The two swirl resonances are retained without division. The code rejects a quadratic `Y`
product or an angular numerator that is not divisible by `X` inside this aperture.

After the previous free angular coefficient has been determined, the script recomputes the
actual nonlinear `A,B,C` Cauchy products. All retained pressure rows and all swirl rows except
14 and 28 are zero. Incompressibility is checked through the actual coefficient derivatives.
The two remaining rows are exactly

```text
C_J14 = X*P(X)*z^2,
C_J28 = X*(Q_28(X)+R(X)*Y)*z^4.
```

The first polynomial and the second row's complete `Y` sensitivity agree with the independent
previous receipts. The new constant forcing `Q_28` is degree 28. Its full rational coefficient
map is retained in the [receipt](../experiments/mfr3_periodic_core/full_second_resonance_receipt.json),
along with the scaled degree-29 `Q_J28=X*Q_28`.

[proved-derived; formal-checked] `NavierStokesSecondResonanceRepair` contains the exact integer
numerator and positive common denominator of `Q_28`. It proves

```text
Q_28(X)<0       for 5625/2236 <= X <= 1366/543,
Y_*(X)=-Q_28(X)/R(X)>0,
Q_28(X)+R(X)*Y_*(X)=0.
```

It composes this with the existing interior-root theorem to obtain a simultaneous first and
second compatibility repair. The original forcing is retained exactly. Its sign proof uses
outward integer coefficient bounds with denominator `2^60`, a positive common scale, and a
small rational endpoint comparison. The positive low coefficients and a sufficient part of
the negative tail determine the sign; the remaining negative tail is retained in the exact
forcing and bounded in the proof.

[established-bounded; computational-witness] Substituting `Y=-Q_28/R` gives a univariate
numerator for every retained residual. The script verifies that every such numerator vanishes
modulo the actual polynomial `P`. Since `X_*>0` and `R(X_*)>0`, the selected finite jet has
zero retained source rows through mode 28. An outward rational calculation gives the integer
enclosure

```text
1679495189493 <= Y_*(X_*) <= 1691966325597.
```

This is a Taylor-coefficient enclosure, not a velocity bound, convergence radius or stability
margin. The numerical enclosure has computational evidence; positivity and the affine repair
are kernel checked.

[established-bounded; computational-witness] `J_28[z^4]` remains a free fibre. The stored jet
uses its zero representative, and a unit perturbation leaves the complete retained mode-28
swirl row unchanged. The source is affine in this coefficient in the retained aperture, so
the representative does not settle it. The next pressure row has not yet been constructed.

## The moving source is derived from the Cartesian equation

[proved-derived; formal-checked] `NavierStokesMovingSwirlCirculation` takes an actual joint
spacetime coefficient `Omega(t,s,z)`. It splits its Fréchet derivative into the time direction
and the spatial trajectory direction, then composes the existing angular-momentum identity.
For the time-dependent meridional drift and carrier

```text
b(t,s,z)=(2s(V+beta), W+beta*z),
L(t)=s(t)*Omega(t,s(t),z(t)),       p'(t)=b(t,p(t)),
```

the actual derivative is

```text
L' = s*(Omega_t+C) - (alpha-beta)*L.
```

Here `C` is the stationary part of the normalized swirl momentum, evaluated on the current
time slice. Rates and coefficient functions may vary with normalized time. No derivative of
the joint profile is supplied as an assumed jet equality.

[proved-derived; formal-checked] `NavierStokesSwirlDiffusion` constructs the second-derivative
bridge from the existing gradient and divergence owners. For any smooth scalar meridional
profile `f`, its Cartesian lift satisfies

```text
Delta[f(s,z)] = 4s*f_ss + 4f_s + f_zz,
Delta[x_i*f(s,z)] = x_i*(4s*f_ss+8f_s+f_zz),       i=0,1.
```

The vector-Laplacian components then give, for the actual reconstructed velocity,

```text
x_0*(Delta U)_1-x_1*(Delta U)_0
 = s*(4s*Omega_ss+8Omega_s+Omega_zz)
 = 4s*ell_ss+ell_zz,                              ell=s*Omega.
```

Define `D ell=4s*ell_ss+ell_zz`. Every displayed term retains `s=0`; no radius division
appears. The owner also proves the actual axis derivative receiver

```text
D ell(0,z)=0,
partial_s[D ell](0,z)=8*Omega_s(0,z)+Omega_zz(0,z)
```

under the stated third-order smoothness. A zero diffusion value on the axis leaves this
derivative source available.

[proved-derived; formal-checked] `NavierStokesViscousSwirlBalance` defines the complete centred
Cartesian residual from the actual velocity, time derivative, advection, dilation, amplitude,
pressure gradient and vector Laplacian. Its angular projection is

```text
x_0*Residual_1-x_1*Residual_0 = s*(Omega_t+C)-mu*D ell.
```

Pressure cancels in this projection. An actual zero Cartesian residual therefore gives

```text
L' = mu*D ell - (alpha-beta)*L
```

along any admitted meridional trajectory. The proof reconstructs a Cartesian occurrence for
each nonnegative squared radius, including zero. It does not assume the scalar viscous swirl
equation or manufacture a trajectory.

## The physical reconstruction removes the normalizing current

[definition] MFR1's `amplitude` variable is the reciprocal physical velocity amplitude; call
it `q` here. The regular centred chart has

```text
U(y,tau)=q(tau)*u(lambda(tau)*y,clock(tau)),
q'=-alpha*q,       lambda'=-beta*lambda,
clock'=lambda*q,   mu=nu*q/lambda.
```

The time in the coefficient calculations is normalized time `tau`. The physical clock is
the separately reconstructed `clock(tau)`.

[proved-derived; formal-checked] The new source bridge instantiates MFR1's actual
`OpenSmoothSolutionOn.rescaled_momentum` for an unforced physical solution at an interior
physical time. Given exact velocity/pressure profile representations and the displayed chart
derivatives, it proves the centred Cartesian residual zero. Thus the preceding angular law
can be instantiated from the physical source; its PDE is not merely a declared scalar port.
This return uses a fixed centre. General centre motion remains in the original MFR1 owner.

[proved-derived; formal-checked] The actual MFR1 velocity definition reconstructs physical
angular momentum with the factor `lambda/q`. Differentiating that factor and composing the
viscous angular law gives

```text
d/dtau [(lambda/q)*L] = nu*D ell.
```

The normalizing `(alpha-beta)L` term cancels in this reconstructed quantity. The theorem
requires the regular chart denominators to be nonzero and derives the derivative by the
ordinary quotient and product rules. This is a normalized-time derivative of the reconstructed
physical quantity, not a claim that normalized and physical time coincide.

## Viscosity already requires more than an amplitude current

[established-bounded; computational-witness] The full recurrence returns the first angular
correction's two axis coefficients

```text
G_1[z^0]=-(5/14)X-35/8,
G_1[z^2]=(15/16)X+3885/416.
```

For `Omega=a*G_0+s*a*G_1+...`, the constant and quadratic coefficients of the axis diffusion,
divided by `a`, are

```text
Phi_0(X)=-(20/7)X-75/2,
Phi_2(X)=(15/2)X+9525/104.
```

The receipt derives these from `8G_1+G_0''`, not from a separately chosen diffusion field.

[proved-derived] If only `a` changes while this instantaneous Euler axis shape and first
radial correction are retained, the two axis time receivers are `a'` and `-(5/4)a'`.
Matching the viscous source at both would require

```text
a'=mu*a*Phi_0(X),
-(5/4)a'=mu*a*Phi_2(X).
```

But `Phi_2+(5/4)Phi_0=(55/14)X+2325/52>0` for `X=a^2`. Positive amplitude and viscosity
make the two equations incompatible. This is a local obstruction to that amplitude-only
modulation of the returned Euler jets.

[proved-derived; formal-checked] `NavierStokesViscousAxisJets` proves the displayed exact
coefficient algebra, the positive mismatch, and incompatibility of the two receiver equations.
It also constructs a second coefficient current:

```text
a'=mu*a*Phi_0(a^2)<0,
b'=mu*((55/14)a^2+2325/52)>0.
```

Then `-(5/4)a'+a*b'=mu*a*Phi_2(a^2)`, so both displayed axis receivers agree. The
coefficient attachment to the Euler jet is computational; the incompatibility and two-current
repair of these explicit scalar equations are kernel checked.

[proved-derived] A local shape carrying this second coefficient is
`F=a*G_0*(1+b*z^2/(1+2z^2)^2)` at `b=0`: the extra factor contributes one unit to the
quadratic coefficient per unit `b`. For `a>0,b>=0` this profile is positive and smooth,
and its ratio to `a*G_0` tends to one at large axial distance. This written candidate
preserves the declared axial tail while admitting the required leading shape current.
Its full time-dependent pressure, radial correction and higher-axis equations remain to be paid.

## Current continuation and verification

[open] Continue with a time-dependent axis/radial construction using the returned viscous
source and shape current, keeping the free `J_28[z^4]` and the next pressure compatibility
visible. Establish the actual nonlinear source bounds and radial convergence for that family,
and construct its exterior/time transport. The previous stationary global exclusion remains
standing. No full viscous profile, stability margin, finite-time physical singularity or RH
sign conclusion is claimed; MFR3 and the full standing goal remain active.

[definition] New formal owners are `NavierStokesSecondResonanceRepair`,
`NavierStokesMovingSwirlCirculation`, `NavierStokesSwirlDiffusion`,
`NavierStokesViscousSwirlBalance`, and `NavierStokesViscousAxisJets`.

[established-bounded; process-audit] Lean 4.33.0 returned the focused closures and live umbrella.
Commands from `formal/elementary-holonics/` were

```sh
lake build ElementaryHolonics.Millennium.NavierStokesSecondResonanceRepair
lake build ElementaryHolonics.Millennium.NavierStokesViscousSwirlBalance
lake build ElementaryHolonics.Millennium.NavierStokesViscousAxisJets
lake build ElementaryHolonics
```

The focused closures returned 3,008, 8,729 and 3,006 jobs respectively; the umbrella returned
9,884. These are build scopes, not theorem counts. Moving circulation and diffusion are included
in the viscous-source closure. Decisive axiom reports use only `propext`, `Classical.choice`,
and `Quot.sound`.

[established-bounded; process-audit] The 29 exact forcing coefficients and common denominator,
all outward integer comparisons and their endpoint inequality match the final recurrence
receipt. Its first polynomial and next sensitivity match the prior independent results;
selected residual numerators, free-fibre response and leading viscous coefficients returned.
Source and changed-line whitespace reviews returned. The umbrella imports, owner map, roadmap
and current position are integrated. The nonlinear recurrence remains a computational witness;
the sign/repair and source-transport theorems retain their kernel-checked scopes.

[established-bounded; computational-witness] The final experiment uses python-flint 0.9.0
and FLINT 3.6.0 for [exact rational polynomial operations](https://python-flint.readthedocs.io/en/latest/fmpq_poly.html).
From the repository root, with python-flint 0.9.0 installed:

```sh
python research/experiments/mfr3_periodic_core/derive_full_second_resonance.py
```

It prints progress to stderr and the complete receipt to stdout. The retained equations,
parameter domain, first and second independent controls, selected-parameter remainder checks,
free-fibre perturbation and leading viscous axis receivers are explicit in the script.

[historical; process-audit] An incomplete exploratory arithmetic draft was recovered under
`/tmp/NavierStokesSecondResonanceRepair.draft.lean`. The maintained certificate was reconstructed
from the exact recurrence coefficients and uses outward integer bounds to reduce the sign proof
to a small rational comparison. The exploratory draft is not accepted evidence. Concurrent
Athena/HNP runtime sources remain outside this mathematical edit.
