# MFR3: the forced axis returns a viscous response and the inner chart retains pressure

**Date:** 2026-09-05. **Campaign:** the
[standing MFR goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
**Predecessor:** [the second resonance and moving viscous source](2026-09-05_MFR3_THE_SECOND_RESONANCE_CLOSES_AND_THE_MOVING_SWIRL_RETURNS_ITS_VISCOUS_SOURCE.md).
**Position:** MFR3 remains in progress. **Grades:** per claim.

## The time source changes the axial primitive

[definition] For a positive axial swirl profile `F(t,z)`, let `K_axis(t,z)` denote the
first radial swirl coefficient. With normalized time `t`, define the actual source

```text
S(t,z)=F_t(t,z)-mu(t)*(8*K_axis(t,z)+F_zz(t,z)).
```

The axis swirl equation is
`S+(W+beta*z)F_z+(alpha+beta-W_z)F=0`. Its instantaneous Euler primitive alone omits `S`.

[proved-derived; formal-checked] `NavierStokesForcedAxialPrimitive` constructs

```text
I(z)=integral_0^z 1/F(r) dr,
J_S(z)=integral_0^z S(r)/F(r)^2 dr,
W(z)=(alpha+2beta)*F(z)*I(z)-beta*z+F(z)*J_S(z).
```

Actual interval differentiation proves the complete axis equation. Smooth positive `F` and
smooth `S` give a smooth constructed `W`; `W(0)=0`. Adding any `c*F` preserves the source
equation, while the zero-axis anchor selects a unique differentiable `W`. Its actual axis jet is

```text
W'(0)=alpha+beta+S(0)/F(0).
```

Thus keeping the axial value zero does not keep its strain unchanged. The moving-axis theorem
uses the actual time derivative in `S`, rather than assuming that the Euler identity survives.
The first radial coefficient supplying the viscous source remains part of the coupled problem.

[proved-derived; formal-checked] The same owner constructs the linear response

```text
w=(alpha+2beta)*(f*I-F*integral_0^z f/F^2)+F*integral_0^z S/F^2.
```

For a viscosity parameter obeying `mu'=-delta*mu`, choose `S=-delta*f-Phi`. Actual spatial
differentiation gives

```text
Gamma*f' + (alpha+beta-W_0'-delta)*f + w*F' - w'*F = Phi.
```

This is a constructed solution of the linearized axis equation. Differentiating the defining
parameter integrals gives the same first variation on a regular positive-profile domain; that
parameter-integral interpretation is written analysis, while the displayed source identity
is kernel checked.

## A positive shape approaches the Euler axis

[definition] At the standing critical rates `alpha=3/2`, `beta=1`, `delta=1/2`, retain
`G_0=(1+z^2)^(-5/4)`, `X=a^2` in the certified first-root bracket, and set

```text
chi(z)=z^2/(1+2z^2)^2,       eta(z)=z^28/(1+2z^2)^15,
A(X)=40X/7+75,              B(X)=-55X/7-2325/26,
F_mu(z)=a*G_0(z)*(1+mu*(A+B*chi+E*eta)).
```

[proved-derived; formal-checked] `NavierStokesViscousAxisShape` proves that both weights are
even and smooth, tend to zero at large positive axial distance, and satisfy
`0<=chi<=1/8`, `0<=eta<=1/16384`. Every derivative of `eta` below order 28 vanishes at zero.
The actual shape is smooth and has

```text
F_mu(0)=a*(1+mu*A),
F_mu''(0)=a*(-(5/2)*(1+mu*A)+2mu*B).
```

Its ratio to `a*G_0` tends to `1+mu*A` along the axial tail. For
`mu(t)=mu0*exp(-delta*t)`, the owner derives its actual time derivative
`-delta*mu(t)*a*G_0*(A+B*chi+E*eta)`.

[proved-derived] Here `a` is the limiting Euler amplitude. Because viscosity decreases in
normalized time, the initial shape coefficient is negative while its leading forward-time
current is positive. This differs from prescribing a positive initial shape coefficient and
assuming it will approach the same Euler axis. The source determines the direction of approach.

## The first viscous pressure and swirl response

[definition] Expand the normalized profiles as `U_mu=U_*+mu*U_1`, with `mu'=-mu/2`.
Use `J=XG` for the Euler angular coefficients and `k=Xf` for their viscous corrections.
The response fields are `w_m,k_m,v_m`, with `v_m=-w_m'/(2(m+1))`. Their retained budgets are

```text
N_w(m)=29-2m,       N_k(m)=28-2m,       m=0..14.
```

[proved-derived] The linear source is the derivative of the actual Euler momentum, minus
`delta` times the response, minus the Laplacian of the Euler profile. The mode diffusion
coefficients are `4(m+1)(m+2)` for radial/angular velocity and `4(m+1)^2` for axial velocity.
At viscosity order `j`, the critical axial and angular indicial multipliers are respectively

```text
(7n+8-m-j)/2,       (7n-m-j)/2.
```

For the reflected first-viscosity response, the first angular resonance is `m=13,z^2` and
the next axial resonance is `m=14,z^1`. The time contribution shifts both from their Euler
locations. The [independent symbolic audit](../experiments/mfr3_periodic_core/audit_viscous_expansion.py)
checks the complete viscosity coefficients through order two before radial extraction;
its [receipt](../experiments/mfr3_periodic_core/viscous_expansion_receipt.json) retains the quadratic source.

[established-bounded; computational-witness] The corrected
[first-response construction](../experiments/mfr3_periodic_core/derive_first_viscous_response.py)
uses the actual Euler coefficients from the full second-resonance owner. The normalized axis
correction is `f_0=G_0*(A+B*chi+E*eta)`, and its axial response is

```text
w_0=(7/2)*(f_0*I_0-G_0*integral f_0/G_0^2)
       -G_0*integral ((1/2)*f_0+Phi)/G_0^2,
Phi=8G_1+G_0''.
```

All integrals are based at zero. The complete retained axis equation is checked before the
higher rows are accepted. The first angular compatibility condition is

```text
C_(1,13)[z^2]=X*(N(X)+D(X)*E).
```

After cancelling the common `X`, `N` has degree 14, `D` degree 13, and every coefficient
of both polynomials is positive. Their exact rational coefficients are in the
[response receipt](../experiments/mfr3_periodic_core/first_viscous_response_receipt.json).
The selected correction is `E=-N/D`.

[proved-derived; formal-checked] `NavierStokesViscousResponseParameters` contains those exact
coefficients and proves `D>0`, `E<0`, and the compatibility repair. It proves the coarse bound
`|E|<=27000000000` on the certified `X` bracket. Together with `|B|<=110`, the weight bounds
give an explicit positive-shape domain:

```text
0<=mu<=1/10000000
  implies  4/5 < 1+mu*A-mu*(|B|/8+|E|/16384),
  hence    F_mu(z)>0 for every real z and a>0.
```

The decaying viscosity stays in this domain for all nonnegative normalized times if its
initial value does. This is a sufficient mathematical parameter bound, not a physical
stability threshold or a measured machine capacity.

[established-bounded; computational-witness] At response mode 14, pressure reads the previous
free angular coefficient with multiplier `-4` and the Euler coefficient `Y=W_15[z]` with
multiplier `25200`. Hence the angular coefficient has `6300*Y` in its determined value.
The new `T_v=w_14[z]` remains free. The next angular constant is determined without fixing it.
Recomputation verifies the complete retained axis and radial source after selecting `E`.

The first pressure potential is constructed as
`P_(1,0)=-integral B_(1,0)` and `P_(1,m)=-A_(1,m-1)/(2m)` for `m=1..15`, anchored at zero.
Its radial and axial gradients match every retained first-response momentum row. This is a
finite local pressure construction; its exterior is not selected by the polynomial anchor.

[established-bounded; computational-witness] The affine-viscosity profile retains a nonzero
quadratic source. At the axis its scaled angular receiver is

```text
mu^2 * [ (595960/8281)X^3 + (43602575/30758)X^2 + (165625/26)X ].
```

This is `-mu^2*(8k_1(0)+k_0''(0))`; the quadratic angular advection vanishes at that receiver.
The parameter owner proves this explicit polynomial positive for `X>0`, and the displayed
source nonzero for `mu>0`. Higher viscosity terms, or the full nonlinear forced primitive,
must therefore remain in the next construction. Closing the linear response did not produce
an exact finite-viscosity fluid solution.

## The inner chart is fixed by the physical clock

[definition] On the regular `mu>0` chart set `s=mu*xi` and retain `z`. Write

```text
H(t,xi,z)=xi*Omega(t,mu(t)*xi,z).
```

[proved-derived; formal-checked] `NavierStokesViscousInnerChart` derives the actual pullback
derivatives, including the time contribution from `mu'`, and proves the exact angular source
conjugation. An actual centred Cartesian source with zero residual gives

```text
H_t + 2xi*(V+(alpha+beta)/2)*H_xi + (W+beta*z)*H_z
  = 4xi*H_xixi + mu*H_zz.
```

The outer coefficients are evaluated at `(s,z)=(mu*xi,z)`. Radial diffusion has unit strength;
axial diffusion retains `mu`. The proof includes the axis and does not infer an inverse at
`mu=0`. It also derives `mu'=-(alpha-beta)mu` from the actual MFR1 length/normalizer jets.

[proved-derived; formal-checked] With MFR1's reciprocal velocity normalizer `q`, the physical
radial scale and angular momentum satisfy

```text
lambda_inner^2 = lambda^2*mu = nu*lambda*q = nu*clock',
L_physical = (lambda/q)*L_outer = nu*H.
```

For the exponential frame, the squared inner scale is exactly
`nu*(alpha+beta)*physicalClockRemaining`. The same clock owner identifies this remaining
quantity with the physical endpoint minus the current physical time. These are source-bound
chart identities, not a demonstration that a singularity occurs.

[proved-derived; formal-checked] A monomial `s^m*mu^j*z^n` becomes
`mu^(m+j)*xi^m*z^n`. The viscosity and radial indices share a scale order while the complete
polynomial in `xi` remains available to radial diffusion. The time derivative of each viscosity
power is derived from the actual `mu` curve. This explains the coupled resonance pattern
without identifying distinct radial carriers merely from their common total order.

## Pressure keeps its axis trace

[definition] In the inner chart use

```text
P_axis(z)=P(0,z),
P_hat(xi,z)=[P(mu*xi,z)-P_axis(z)]/mu.
```

[proved-derived; formal-checked] The owner proves the exact reconstruction and pressure
operator identity

```text
P(mu*xi,z)=P_axis(z)+mu*P_hat(xi,z),
Delta_outer P = P_axis'' + 4xi*P_hat_xixi + 4*P_hat_xi + mu*P_hat_zz.
```

The axis pressure contributes its axial derivative information. The scaled radial difference
is a separate carrier. A derivative-extended slope regularizes that difference at `mu=0`.
For both a fixed slice and a jointly differentiable pressure family `P_mu`, Lean proves a
continuous extension with value `xi*partial_s P_0(0,z)`. In the changing family, both pressure
evaluations use the same parameter before subtraction; their parameter derivatives cancel.
This retains a pressure derivative receiver at the collapsed radial chart while leaving the
full source behind it.

## Current construction and limits

[open] The returned objects are a positive axis family, an exact forced axis equation, a
finite first-viscosity response with local pressure, and exact inner-coordinate source laws.
The complete nonlinear radial profile and global exterior are not constructed. The positive
quadratic residue and free `T_v` specify the next correction questions.

[definition] MFR3 next needs a periodic source realization of the local core and its complete
exterior pressure coupling, including pressure torque where axisymmetry is broken. This is
the missing source/domain construction. MFR4 then owns the complete residual and quantitative
linear/nonlinear control for that specified realization. Requiring full radial convergence
before beginning that residual/stability phase would put MFR4's work into MFR3. The stationary
global exclusion remains standing; the local axisymmetric calculation does not settle the
periodic exterior. The RH arithmetic-sign investigation remains open under the same goal.

## Verification and source repair

[definition] New formal owners: `NavierStokesForcedAxialPrimitive`,
`NavierStokesViscousAxisShape`, `NavierStokesViscousResponseParameters`, and
`NavierStokesViscousInnerChart`.

[established-bounded; process-audit] Lean 4.33.0 returned the focused checks and live umbrella.
Commands from `formal/elementary-holonics/` were

```sh
lake build ElementaryHolonics.Millennium.NavierStokesForcedAxialPrimitive
lake build ElementaryHolonics.Millennium.NavierStokesViscousResponseParameters
lake build ElementaryHolonics.Millennium.NavierStokesViscousInnerChart
lake build ElementaryHolonics
```

The focused closures returned 2,650, 3,425 and 8,732 jobs respectively; the umbrella returned
9,888. These are build scopes, not theorem counts. The axis-shape owner is included in the
parameter closure. Decisive axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

[established-bounded; process-audit] The final corrected coefficient maps match the formal
response selector, positive divisor, coarse bound and explicit quadratic remainder. The
complete axis, radial pressure/swirl, pressure-potential gradient, parameter-selection and
source-expansion checks returned. Source and changed-line whitespace reviews returned. The
umbrella imports, owner map, current position and roadmap are integrated. The nonlinear
recurrence remains computational; the primitive, positive-family and chart-source identities
retain their kernel-checked scopes.

[established-bounded; computational-witness] The independent expansion audit uses SymPy 1.14.0.
The response construction uses python-flint 0.9.0 / FLINT 3.6.0 and recomputes the axis,
all retained pressure/swirl rows, pressure gradients and selected-parameter residuals:

```sh
python research/experiments/mfr3_periodic_core/audit_viscous_expansion.py
python research/experiments/mfr3_periodic_core/derive_first_viscous_response.py
```

[historical; process-audit] Source inspection found an incorrect manually entered reciprocal
binomial table in the initial response script, despite its higher-row checks returning zero.
The initial script/receipt were preserved under `/tmp/holonics-mfr3-first-viscous-incorrect-binomial.*`.
The maintained source generates all reciprocal and weight coefficients from the exact binomial
rule, verifies the reciprocal product, and requires the complete axis equation before accepting
the higher rows. The corrected replay, not the initial receipt, is the accepted evidence.
Concurrent Athena/HNP runtime sources remain preserved.
