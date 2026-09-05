# The anisotropic frame returns its pressure metric and radial viscous clock

**Authority:** Brandon's standing
[moving-frame goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md),
following the
[compact-cutoff obstruction](2026-09-05_MFR3_THE_COMPACT_RADIAL_CUTOFF_RETURNS_A_PRESSURE_INDEPENDENT_RESIDUAL_OBSTRUCTION.md).
MFR3 continues with an actual source chart and a coupled clock regime. No replacement profile,
nonlinear stability theorem or Millennium endpoint is asserted.

## One physical source through the full linear chart

[definition] Let `A(tau)` be the spatial frame, `B=A^(-1)`, `c` its centre and `b=t'` the
physical-clock rate. The normalized coordinates `y,tau` are dimensionless. Define

```text
x=c+A*y,                         U(y,tau)=b*B*u(x,t),
P(y,tau)=b^2*p(x,t),              D=B*A',
C=B*B^*,                         L_B U=sum_i D^2 U[B*e_i,B*e_i].
```

The `e_i` are the actual Cartesian basis vectors. `C` is the inverse spatial metric. The frame
and its inverse remain continuous-linear maps; no diagonal assumption is used in the general
spatial or momentum laws.

[proved-derived; formal-checked] `NavierStokesLinearFrameSpace` derives the actual spatial
derivative, divergence, pressure gradient and second derivative:

```text
D_y U=b*B*(D_x u)*A,              div_y U=b*div_x u,
grad_y P=b^2*(A^*)*grad_x p,        C*grad_y P=b^2*B*grad_x p,
L_B U=b*B*Laplacian_x u.
```

The pressure-gradient metric consequence is composed in the dynamic source proof. Physical
periods are transported to `B*e_i`; reconstruction returns `u=b^(-1)*A*U` on the regular chart.

[proved-derived; formal-checked] `NavierStokesLinearFrameDynamics` differentiates the actual
joint source and the moving frame. The inverse jet follows from the differentiated inverse
identity, `B'=-B*A'*B`. Its `OpenSmoothSolutionOn.linearFrame_momentum` gives

```text
U_tau + D_y U[U-D*y-B*c'] + (D-(b'/b)I)*U
  = nu*b*L_B U - C*grad_y P + b^2*B*f.
```

The time derivative, nonlinear term, force and pressure all come from the same supplied physical
solution on its strict open lifespan. Incompressibility follows from that source. The inverse-time
law is derived for inverse frames, and the diagonal construction below supplies that actual jet.
No normalized PDE, pressure cancellation or viscosity estimate is assumed on behalf of a profile.
The normalized particle drift is `U-D*y-B*c'`; `U` alone is the transported physical velocity.

## The two spatial factors retain their fibres, metric and chronology

[proved-derived; formal-checked] `NavierStokesAnisotropicFrame` constructs
`A=diag(r,r,z)` and `B=diag(r^(-1),r^(-1),z^(-1))`, their inverse relations, adjoints and actual
time derivatives along arbitrary differentiable scalar curves. It gives

```text
D=diag(r'/r,r'/r,z'/z),           C=diag(r^(-2),r^(-2),z^(-2)),
det A=r^2*z.
```

The complete spatial fibre is

```text
A*x=A*y iff r*(x_0-y_0)=0,
             r*(x_1-y_1)=0,
             z*(x_2-y_2)=0.
```

Thus zero-length fibres remain represented. The inverse/source theorems explicitly require
the relevant factors to be nonzero; a degenerate displayed chart supplies no physical inverse.

[proved-derived; formal-checked] `NavierStokesAnisotropicDynamics` supplies the actual two-length
source equation, with diffusion

```text
nu*b*(r^(-2)*(U_00+U_11)+z^(-2)*U_22).
```

Here `U_ij` denotes the actual second spatial derivative. Both pressure and viscosity use the
same frame factors. The scalar specialization `r=z=ell`, `b=ell*q` recovers MFR1's velocity
exactly. Its pressure is `ell^2` times MFR1's pressure; the inverse pressure metric cancels this
factor in the PDE.

[proved-derived; formal-checked] Relative to the frame centre, physical angular momentum is

```text
L_physical=(r^2/b)*L_normalized.
```

The actual derivative of its reconstruction factor is
`(r^2/b)'=(2r'/r-b'/b)*(r^2/b)`. Its product with radial viscosity is exactly
`(r^2/b)*(nu*b/r^2)=nu`. This is a reconstruction/source relation. Conservation or a bound on
physical angular momentum would still have to come from the complete source, including torque
and any centre motion.

## Energy follows the physical cell, including its time derivative

[proved-derived; formal-checked] `NavierStokesLinearFrameEnergy` applies the actual affine
Jacobian to the inverse image of the physical unit cell. With
`Y={y:c+A*y lies in unitCube}`, the physical energy is

```text
E_physical=abs(det A)/(2*b^2) * integral_Y U^T*(A^T*A)*U.
```

For the two-length frame the kinetic metric is
`r^2*(U_0^2+U_1^2)+z^2*U_2^2`. The spatial population and velocity metric change together;
the integral is not silently taken over the original normalized unit cube.

[proved-derived; formal-checked] The complete receiver is equal to the physical periodic
kinetic energy throughout every regular chart neighborhood. Composing that equality with the
existing unforced open-solution energy theorem gives

```text
d_tau E_physical(t(tau)) = -nu*b*Dissipation_physical(t(tau)).
```

The diagonal source theorem constructs the required regular neighborhood from its actual scalar
derivatives and nonzero values. This retains the moving-cell energy law, not merely a static
norm correspondence. No new bound on dissipation or a terminal continuation theorem follows.

## A clock that retains radial diffusion

[definition] Let `K>0` be a constant circulation reconstruction scale and choose

```text
b=r^2/K,                         epsilon=(r/z)^2,
Pi=P/r^2=(r/K)^2*p.
```

Reading `r,z` as lengths and `b` as physical-clock rate, `K` has the units of circulation per
unit mass, the same units as kinematic viscosity. This is a chart choice in the declared
Navier--Stokes model, not a measured physical parameter or a constructed singular flow.

[proved-derived; formal-checked] `NavierStokesAnisotropicViscousClock` derives

```text
L_physical=K*L_normalized,
mu_radial=nu/K,                   mu_axial=(nu/K)*epsilon,
pressure force=diag(1,1,epsilon)*grad Pi.
```

Its actual `OpenSmoothSolutionOn.radial_clock_momentum` retains all grid and centre terms while
replacing the diffusion/pressure side by

```text
(nu/K)*(U_00+U_11+epsilon*U_22) - diag(1,1,epsilon)*grad Pi.
```

The velocity reaction uses `b'/b=2r'/r`. Radial viscosity remains in the leading equation;
the positive angular normalization gap of the rejected inviscid compact continuation is absent.
This identifies a different source regime. It does not establish a stationary compact profile
or rule out another maximum-principle obstruction.

[proved-derived; formal-checked] The aspect ratio has the actual derivative
`epsilon'=2*(r'/r-z'/z)*epsilon`. The physical energy weights reduce to

```text
E_physical = (K^2/2) * integral_Y
  [z*(U_0^2+U_1^2)+(z^3/r^2)*U_2^2].
```

The pointwise reduced density is kernel checked; its integral uses the preceding transported
energy equality. The existing physical-clock constructor also supplies `t'=r^2/K` when the
radial length is exponential, with its previously proved finite clock endpoint under positive
rates. The source equation is used only where that clock lies inside the given solution's lifespan.

[conditional] If `r=r0*exp(-beta_r*tau)` and `z=z0*exp(-beta_z*tau)`, aspect tends to zero
when `beta_r>beta_z`. The axial energy weight is
`(z0^3/r0^2)*exp((2beta_r-3beta_z)*tau)`. If its normalized axial squared-speed integral stays
bounded below, bounded physical energy requires `2beta_r<=3beta_z`. Thus
`0<beta_z<beta_r<=3beta_z/2` survives these particular aspect/energy tests. This is a written
scaling consequence with explicit profile hypotheses, not an existence or stability result.

## The next pressure fibre must be paid by the source

[counterexample] A positive coefficient `epsilon` tending to zero does not itself remove the axial
pressure force: `Pi=P0(z)/epsilon` gives `epsilon*Pi_z=P0'(z)`. This is an operator-level example;
the actual pressure must be reconstructed from its physical source and periodic domain.

[open] MFR3 next derives the pressure component with zero horizontal frequency directly from
the actual periodic source, retaining the frame's horizontal cell and axial period. In particular,
the axial force must be compared to the horizontal mean of the axial velocity's quadratic source
before taking an aspect-ratio limit. Do not impose a bounded reduced pressure or delete its axial
mean by a gauge convention. Only a spatially constant pressure gauge is free.

[interpretation] Strain-supported viscous vortices provide a useful comparison after that source
return. [Gallay--Wayne](https://arxiv.org/abs/math/0503353) studies Burgers vortices with background
strain; [Maekawa--Miura--Prange](https://arxiv.org/abs/1807.10341) studies a time-dependent linear-strain
setting. Any comparison here must obtain the required strain and pressure from the admitted
periodic field. Those imposed-background results do not supply our missing exterior or finite-energy
continuation. A mismatch in that source is the falsifier for the comparison.

[open] A replacement leading profile with its complete exterior, MFR4's quantitative nonlinear
control, and MFR5's arithmetic sign remain unfinished. The earlier compact-cutoff obstruction and
RH endpoint scope remain standing.

## Independent audit and verification

[established-bounded; computational-witness]
[derive_source.py](../experiments/mfr3_anisotropic_frame/derive_source.py) differentiates an arbitrary
second spatial/first time jet through a symbolic moving anisotropic frame that also has shear.
It verifies `R_chart=b^2*B*R_physical`, including centre motion, force, inverse derivative,
pressure metric, mixed diffusion, divergence, kinetic metric and relative angular reconstruction.
Replacing either pressure or diffusion by the ordinary unweighted operator fails its symbolic
control. The [receipt](../experiments/mfr3_anisotropic_frame/source_receipt.json) also checks the
coupled radial-clock pressure, diffusion and energy factors. No physical solution is supplied
by this audit.

[established-bounded; process-audit] Primary review corrected a delegated draft's use of
component products in place of angular momentum, required actual arbitrary-curve inverse and
reconstruction derivatives, and restored unrelated stale edits to the already completed compact
audit. The final mathematical operators retain their original quantities and source hypotheses.

[established-bounded; process-audit] The first broad build exposed an elaboration defect in
the HNP proof committed in `18c28983`. An isolated checkout reproduced it. The reviewed repair
adds explicit `Fin 1` parameters and normalizes the existing deposit/recurrence proofs in
`HolonicOrientedSiteTransport.lean`; theorem statements and native behavior are preserved.
Its focused 3,167-job build passed. The isolated checkout and its copy-on-write project cache
remain in `.local/mfr3-anisotropic-verification`; the pinned package cache is shared.

[established-bounded; process-audit] The final anisotropic source/clock target passed 9,021 jobs.
The repaired isolated umbrella passed all 9,904 jobs against committed base `18c28983` plus the
six new mathematical owners, their imports and that proof repair. New endpoint axiom prints
contain only `propext`, `Classical.choice` and `Quot.sound`. Lean is 4.33.0 with pinned dependencies;
the exact SymPy 1.14.0 audit returned exit status zero. No unrelated native/Cargo checks are
claimed by this return.
