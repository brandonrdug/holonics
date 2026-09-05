# The compact radial cutoff returns a pressure-independent residual obstruction

**Authority:** Brandon's standing
[moving-frame goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
This continues the
[periodic-source construction](2026-09-05_MFR3_THE_LOCAL_CORE_HAS_A_PERIODIC_REALIZATION_AND_ITS_PRESSURE_RETAINS_EXTERIOR_TORQUE.md).
MFR3 remains active; a residual obstruction now changes the proposed family. HNP remains independent.

## The specified cutoff and its actual periodic source

[definition] Concretize the cutoff by

```text
chi(s,z) = smoothTransition((4-64*(s+z^2))/3).
```

It is one on squared distance at most `1/64`, and zero at squared distance at least `1/16`.
Apply it to the complete finite potential, retaining both previous coefficient fibres:

```text
A_j = (-y*chi*h_j, x*chi*h_j, chi*g_j),  U_j = curl A_j,
U_mu = U_0 + mu*U_1,                  mu' = -mu/2.
```

[proved-derived; formal-checked] `NavierStokesRadialCoreCutoff` derives smoothness, support,
the unchanged inner derivative receiver, and the complete cut velocity

```text
V_j = -(chi*h_j)_z,
Omega_j = -2*(chi*g_j)_s,
W_j = 2*chi*h_j + 2s*(chi*h_j)_s.
```

All cutoff derivatives remain in the velocity. Its angular momentum has actual compact
Cartesian support in the normalized radius-`1/4` ball. This explicit radial choice supplies
rotational symmetry by formula; the preceding generic bump contract alone did not state that
property. The preceding generic periodic-completion theorem remains valid at its original scope.

[proved-derived; formal-checked] `NavierStokesMovingPeriodicCore` first scales the potential
physically, then periodizes it, then reads the normalized velocity:

```text
B_mu(x) = (ell/q) * (A_0+mu*A_1)(x/ell),
u_phys = curl periodize(B_mu),
U_per(y) = q*u_phys(ell*y).
```

The physical field is unit-periodic; the normalized period is `1/ell`. For `0<ell<1`, `q!=0`,
and `|y|<1/2`, `U_per=U_mu`. Actual neighborhood equality transports the time derivative,
spatial derivative, Laplacian and the entire momentum residual at positive normalized times.
The pressure is the same arbitrary Cartesian field on both sides of this equality.

## The full source has a leading term that cannot disappear

[proved-derived; formal-checked] `NavierStokesAffineAngularResidual` starts from the existing
Cartesian `momentumResidual`. Write `L_j=x*U_j,y-y*U_j,x` and `delta=alpha-beta`. For arbitrary
smooth three-dimensional `U_0,U_1`, when `mu'=-delta*mu`, its angular projection is exactly

```text
angular(momentumResidual) = delta*L_0
  + D L_0 [U_0 + mu*U_1 + beta*y]
  + mu*C_1 + mu^2*C_2 + pressureTorque,

C_1 = D L_1 [U_0+beta*y] - angular(y, Laplacian U_0),
C_2 = D L_1 [U_1]        - angular(y, Laplacian U_1).
```

There is no omitted nonlinear order for this affine velocity family. Pressure remains arbitrary;
its dependence on the changing torus is not replaced by a fixed polynomial in `mu`.

[proved-derived; formal-checked] `NavierStokesCompactMaximum` constructs a positive global
maximum of the actual compact leading angular momentum from any positive seed. Fermat's theorem
and the Cartesian-to-meridional derivative give `D L_0=0` at its entire horizontal circle, whose
squared radius is strictly positive. `NavierStokesPressureCircle` applies Rolle's theorem to
the actual pressure restricted to that circle. There is an angle with zero pressure torque,
even when the pressure is not rotationally symmetric or periodic.

[proved-derived; formal-checked] The complete `C_1,C_2` operators are bounded on that compact
circle. If `M>0` is the attained leading circulation, set `c0=delta*M`; let `B>=0` bound
`|C_1|+|C_2|` there. The constructed positive threshold

```text
epsilon = min(1, c0/(2*(B+1)))
```

gives, for `0<=mu<=epsilon`, an actual point on the circle with

```text
angular(momentumResidual) >= delta*M/2 > 0.
```

`NavierStokesCompactAngularObstruction` proves this statement from compact support, smoothness
and the positive seed. The first response may be nonaxisymmetric. The leading **angular momentum**
is the rotationally symmetric quantity used by the argument. The threshold is an obstruction
threshold for the viscosity parameter; it is not a nonlinear stability radius.

## The retained coefficients pay the positive seed

[established-bounded; computational-witness]
[audit_compact_cutoff_source.py](../experiments/mfr3_periodic_core/audit_compact_cutoff_source.py)
reads the actual previously generated coefficient payload and reconstructs `J=-2*(a*g)_s`.
At `r=2^(-6)`, `s=r^2`, `z=0`, exact outward rational arithmetic gives `2<J<3` throughout the certified
`X,Y` brackets. Those brackets are checked against the prior second-resonance receipt.
Since `0<a=sqrt(X)<2`, the actual inner field has `Omega=J/a>1` and

```text
L_0(r,0,0) > r^2.
```

The free `L*s^28*z^4` term vanishes at this receiver; `T` belongs to the first-viscosity response.
The [receipt](../experiments/mfr3_periodic_core/compact_cutoff_source_receipt.json) retains the
exact interval, the independent Cartesian cutoff curl and the complete source polynomial,
including the term that vanishes only after the critical-point theorem is applied.

[proved-derived; formal-checked] `NavierStokesCompactPeriodicObstruction` takes that displayed
seed inequality as an explicit hypothesis, with the seed radius kept as a parameter, and joins
the full periodic source to the MFR1 rates

```text
ell(tau)=ell0*exp(-tau),  q(tau)=q0*exp(-3*tau/2),
mu(tau)=(nu*q0/ell0)*exp(-tau/2)=nu*q(tau)/ell(tau).
```

For `nu>0`, `0<ell0<1`, `q0>0`, at every sufficiently late normalized time and for **every**
smooth Cartesian pressure, a point with `|y|<=1/4` satisfies

```text
angular(momentumResidual) > (alpha-beta)*r^2/2 = r^2/4.
```

For the retained receiver `r=2^(-6)`, the floor is `2^(-14)`. The radius, its squared-radius
receiver and its circulation floor are retained as related scale expressions; expanded fractions
are numerical receipt values. The endpoint is kernel checked with its stated seed hypothesis. The exact finite-coefficient
seed is the computational receiver above; no automatic embedding of the entire JSON coefficient
table into Lean is claimed.

[counterexample; computational-witness] This supplies a concrete obstruction to driving the
complete residual of this fixed radial-cutoff family to zero merely by taking `mu` small or
closing further local radial rows. Solving its global pressure equation cannot remove the bound,
because the bound holds for every smooth pressure. The constructed initial field and its local
solution remain valid. The proposed affine-in-viscosity continuation is the rejected attempt.

[open] The result does not bound a general nearby solution in an arbitrary stability norm,
or establish a regularity or singularity conclusion for general Navier--Stokes data. Such a
claim would require the actual perturbation space and operator estimate. The returned positive
projection is a source obstruction, not that estimate.

## The next frame must change the actual source

[proved-standard] Chae's [Theorem 1.1](https://arxiv.org/pdf/math/0601060) excludes self-similar
Euler blowup under its smoothness hypotheses when the profile vorticity belongs to every `L^p`
for sufficiently small positive `p`. Smooth compactly supported vorticity meets that integrability
condition. Thus a fixed compact stationary leading profile cannot be admitted as a repair merely
by changing its angular symmetry; any proposed limiting argument must retain the theorem's
actual regularity and integrability hypotheses.

[proved-derived] An additional scalar frame alone composes with the existing one. In the
normalized equation, substitute `U(y,tau)=R(tau)*V(y/R(tau),tau)`, `P=R^2*Pi`, and write
`gamma=R'/R`. The chain rules give
`U_tau=R*(V_tau+gamma*V-gamma*xi·grad V)`,
`(U·grad)U=R*(V·grad)V`, `grad P=R*grad Pi`, and `Laplacian U=R^(-1)*Laplacian V`.
Dividing by `R` therefore changes

```text
(alpha,beta,mu) -> (alpha+gamma, beta-gamma, mu/R^2).
```

The physical chart becomes `ell_new=ell*R`, `q_new=q/R`, retaining
`ell_new*q_new=ell*q`. Its angular gap is `alpha-beta+2*gamma`.
This calculation is a written chain-rule derivation, not a new formal owner or a new solution.

[definition] The next MFR3 construction is an anisotropic moving chart, beginning with
`A=diag(ell_r,ell_r,ell_z)`, physical clock derivative `b`, and transported velocity
`U=b*A^(-1)*u`. Derive its full pressure metric, viscosity tensor, divergence, energy and physical
angular-momentum reconstruction before choosing another profile. The moving exterior and any
leading time dependence must then enter those actual equations. The scalar MFR1 owners and
the preceding coefficient constructions remain reusable evidence at their stated scopes.

[open] That anisotropic source derivation and a replacement surviving family remain unfinished.
MFR4 must test the replacement's full residual and quantitative nonlinear control. MFR5's
arithmetic sign remains open. No anisotropy, extra clock, or holonic chart by itself selects a
Millennium conclusion.

## Source review and verification

[established-bounded; process-audit] Primary review corrected the delegated symbolic audit's
initial confusion between swirl diffusion and angular-momentum diffusion: for `L=s*Omega`, the
latter is `4s*L_ss+L_zz`, with no added `8*L_s`. It also required deriving the source from the
full swirl PDE and retaining the baseline-gradient term before the maximum is applied. The
final independent Cartesian curl, complete source identity and exact seed calculation pass.

[established-bounded; process-audit] The final parameterized-radius focused endpoint build passed
(8,842 jobs), followed by the live `lake build ElementaryHolonics` umbrella (9,898 jobs).
The earlier focused pressure-circle, compact-maximum, radial-cutoff and moving-periodic builds
also returned. All new endpoint axiom prints contain only `propext`, `Classical.choice` and
`Quot.sound`. The exact symbolic audit returned exit status zero with SymPy 1.14.0 and Python
rational arithmetic. Lean is 4.33.0 with the repository's pinned dependencies.

[definition] Reproduce the symbolic receiver with
`/tmp/holonics-mfr3-symbolic/bin/python research/experiments/mfr3_periodic_core/audit_compact_cutoff_source.py`.
If the ignored coefficient payload is absent, first regenerate it with the preceding
`construct_periodic_potential.py` owner as described in the periodic-source record.
The seven new formal owners are imported by the umbrella and listed in the architecture map.
No HNP runtime behavior or Cargo checks belong to this mathematical return.
