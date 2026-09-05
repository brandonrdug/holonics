# The viscous core returns its periodic strain source and cubic response

**Authority:** Brandon's standing
[moving-frame goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
This continues the [actual axial pressure mean](2026-09-05_MFR3_THE_AXIAL_PRESSURE_MEAN_RETURNS_THE_COMPLETE_QUADRATIC_SOURCE_THROUGH_THE_MOVING_CELL.md).

## A regular viscous circulation with an explicit strain requirement

[definition] Use the radial clock `b=r^2/K`, radial viscosity `mu=nu/K`, exponential radial
rate `beta`, and a candidate normalized axial strain `a`. With squared radius `s=x^2+y^2`, set

```text
q=(a-2*beta)/(4*mu),
L(s)=Gamma*(1-exp(-q*s)),
Omega(s)=dslope(L,0,s),
U=(-a*x/2-Omega(s)*y, -a*y/2+Omega(s)*x, a*z).
```

The divided difference `dslope` reads the derivative at its base point. It keeps the axis in the
same function as the nonzero-radius population.

[proved-derived; formal-checked] `NavierStokesGaussianCirculation` proves

```text
s*Omega(s)=L(s),       Omega(0)=Gamma*q,       Omega'(0)=-Gamma*q^2/2,
2*s*(beta-a/2)*L'(s)=4*mu*s*L''(s).
```

`Omega` is analytic at every real `s`, including zero. For positive `mu` and `a>2*beta`, `q>0`;
for positive `Gamma`, circulation is positive at every positive radius and tends to `Gamma` at
infinity. Thus this exact circulation is not a compact radial cutoff.

[proved-derived; formal-checked] `NavierStokesGaussianCore` gives the actual smooth Cartesian
field, its zero divergence, and angular momentum `x*U_2-y*U_1=L(s)`, including the axis.
Its nonzero linear axial strain makes the whole comparison field nonperiodic.

[established-bounded; computational-witness]
[derive_gaussian_profile.py](../experiments/mfr3_viscous_strain_source/derive_gaussian_profile.py)
independently checks the full off-axis Cartesian radial-clock momentum expression, including
the distinct axial frame rate `gamma`. The pressure is an actual radial primitive:

```text
Pi=(a*beta/2-a^2/8)*s + (1/2)*integral_0^s Omega(v)^2 dv
   -a*(a+2*beta)*z^2/(2*epsilon).
```

The residual is zero for `a=2*beta+4*mu*q`; the pressure retains its axial inverse-aspect term.
The [receipt](../experiments/mfr3_viscous_strain_source/gaussian_profile_receipt.json) states the
off-axis symbolic scope. The smooth angular extension is the separate kernel-checked result.

[proved-standard] This comparison belongs to the Burgers-vortex family with background strain.
[Gallay–Wayne](https://arxiv.org/abs/math/0503353) and
[Maekawa–Miura–Prange](https://arxiv.org/abs/1807.10341) treat such strain-supported settings.
In particular, the latter paper explicitly retains the nondecaying linear background and its
quadratic pressure. Those results do not furnish a periodic finite-energy exterior here.

## The physical solution must supply the strain current

[proved-derived; formal-checked] `NavierStokesAxialStrainSource` differentiates the actual
unforced periodic momentum equation and uses the existing mixed time–space commutation owner.
For every gradient entry at an interior stagnation occurrence,

```text
J_t = -J^2 + nu*D(Laplacian u) - D(gradient p).
```

The formal statement gives actual `HasDerivAt` results entry by entry. If the axial direction is
a `Du` eigenvector with eigenvalue `a`, its diagonal receiver is

```text
a_t = nu*[D(Laplacian u)]_33 - p_zz - a^2.
```

The pressure condition for any proposed strain rate is necessary and sufficient at that actual
source occurrence. Neither the time derivative nor the pressure curvature is supplied as an
unattached matrix port.

[conditional] At a frame with `b=1`, a fixed normalized strain under `b_tau=-2*beta*b` asks for
the physical rate `a_t=2*beta*a`. If the axial viscous strain receiver is zero, the required
pressure curvature is `p_zz=-a^2-2*beta*a`. This is the instantaneous condition tested below;
it is not an assertion that the rate continues to a terminal time.

## Actual periodic data preserve the local derivatives used by the test

[definition] Work first on the phase torus `[0,2*pi]^3`, with `mu=nu=beta=1`,
`a=10/3`, `q=1/3`, `Gamma=3`. Let

```text
F(theta)=3*sin(theta)/2-3*sin(2*theta)/10+sin(3*theta)/30,
C=F',                         B(z)=1+rho*(1-cos(z))^3,
psi=A*(cos(x)+cos(y))+B2*(cos(2*x)+cos(2*y))
    +C3*(cos(3*x)+cos(3*y))+D*cos(x)*cos(y)
    +E*(cos(2*x)*cos(y)+cos(x)*cos(2*y)),
(A,B2,C3,D,E)=(169/216,-4/135,11/3240,7/27,1/108).
```

The phase potential is

```text
P=(-a*C(x)*F(y)*F(z)/2, a*F(x)*C(y)*F(z)/2, B(z)*psi(x,y)).
```

Its curl is `S+B*V`, where
`S=(-a*F(x)*C(y)*C(z)/2,-a*C(x)*F(y)*C(z)/2,a*C(x)*C(y)*F(z))`
and `V=(psi_y,-psi_x,0)`.

[proved-derived; formal-checked] `NavierStokesPeriodicStrainPotential` constructs the unit-periodic
potential by evaluating `P` at `2*pi*X`. Its actual curl is a smooth divergence-free periodic
initial datum for every real `a,rho`; the standing positive-viscosity local-existence construction
returns an `OpenPeriodicSolutionOn` with its own global pressure and finite energy per physical
period cell. No pressure from the Gaussian
comparison is imposed on that solution.

[established-bounded; computational-witness] The exact phase-to-physical scaling is
`u_phys(X,t)=k*u(k*X,k^2*t)`, `p_phys=k^2*p`, `k=2*pi`, with viscosity unchanged.
The finite Fourier audit reconstructs the curl from the same potential. Its Taylor checks give
`F=x+O(x^7)`, `C=1+O(x^6)` and
`psi=constant-s/2+s^2/24-s^3/324+O(|(x,y)|^8)`. Thus the velocity agrees with the Gaussian-plus-linear-
strain field through fifth order. Varying `rho` first changes velocity at degree seven, preserving
every local derivative used by the cubic viscous source.

[established-bounded; computational-witness] The preceding lower-order construction and its
[receipt](../experiments/mfr3_viscous_strain_source/lower_order_source_receipt.json) are retained.
It matched velocity through cubic order and varied it at degree five. That was sufficient for
the first-gradient test, but its cubic evolution also read changed fifth derivatives through
viscosity. The stronger construction above pays that distinction before interpreting the next
pressure response.

## Pressure reconstruction and the returned cubic response

[established-bounded; computational-witness]
[derive_source_order3.py](../experiments/mfr3_viscous_strain_source/derive_source_order3.py)
retains all 2,188 nonzero pressure modes. It checks the actual curl, velocity conjugate symmetry,
zero divergence, zero source mean, real pressure, complete modewise Poisson inversion, and the
nonconstant axial identity `p_hat(0,0,n)=-hat(u_3^2)(0,0,n)`.

[established-bounded; computational-witness] The pressure curvature is a quadratic function of
`rho`, retained exactly in the [receipt](../experiments/mfr3_viscous_strain_source/source_order3_receipt.json).
A positive algebraic root of `p_zz+160/9=0` lies between `41571/38563` and `43492/40345`.
At that root the complete initial source matrix satisfies `-J^2+Delta J-H_p=2*J`, where

```text
J=[[-5/3,-1,0], [1,-5/3,0], [0,0,10/3]],
Delta J=[[0,4/3,0], [-4/3,0,0], [0,0,0]].
```

The pressure gradient at the origin is zero. The full horizontal pressure mean is unchanged by
`rho`, since the vertical velocity is unchanged; the local Hessian reads the remaining horizontal
frequency population. This is not a pressure-gauge adjustment.

[established-bounded; computational-witness] The full quartic Taylor part of pressure is now
reconstructed, with all fifteen monomials retained. Subtracting the Gaussian particular part
`p4_G=-s^2/12` gives exactly

```text
p4-p4_G = h_ax*H_ax + h_cos*H_cos + h_sin*H_sin,
H_ax=z^4-3*s*z^2+3*s^2/8,
H_cos=x^4-6*x^2*y^2+y^4,
H_sin=x*y*(x^2-y^2).
```

Each displayed polynomial is harmonic. The full homogeneous cubic part of the actual initial
momentum source, minus the Gaussian-clock target `(2*y*s/3,-2*x*s/3,0)`, is exactly
`-gradient(p4-p4_G)`. This is a three-component polynomial equality, not just agreement at selected
receivers. Viscous, advective and pressure contributions are retained separately.

[established-bounded; computational-witness] On the selected positive matching root, exact affine
endpoint bounds after reduction modulo its quadratic give

| Carrier | Exact outward enclosure |
|---|---|
| `h_ax` | `[219/1000,11/50]` |
| `h_cos` | `[-9/125,-71/1000]` |
| `h_sin` | `[33/250,133/1000]` |

The receipt retains the complete unreduced/reduced coefficients, both matching-root intervals,
and the chosen positive branch. The other root is not declared inadmissible.

[counterexample; computational-witness] Thus matching the complete first-gradient rate does not
preserve this fixed Gaussian local shape: all three returned cubic currents are nonzero. The
current is caused by the quartic pressure response after every local velocity derivative needed
by viscosity has been matched. The harmonic assertion concerns this quartic Taylor polynomial;
it does not assert that the full pressure difference is harmonic on a neighborhood or globally.

[proved-derived; formal-checked] `NavierStokesQuarticPressureCurrent` constructs these three
harmonic pressure carriers with arbitrary real coefficients. It proves the actual gradient
formula, zero Laplacian, and smooth divergence-free cubic current. The current and its first
spatial derivative vanish at the centre, but the complete current is zero if and only if all
three coefficients are zero. A zero first jet therefore retains the full three-parameter fibre;
it does not erase the returned deformation.

[proved-derived] The angular pair has the exact phase representation
`h_cos*H_cos+h_sin*H_sin=Re[(h_cos-i*h_sin/4)*(x+i*y)^4]`, by expansion of the fourth power.
It retains both angular components as one complex phase population; choosing a rotated reading
does not delete that population.

## Scope and continuation

[open] The formal solution theorems concern actual strict-interior time derivatives and actual
periodic local existence. The coefficient/root calculations are exact finite initial-source
computations; their Fourier attachment is a computational witness, not a new kernel theorem
identifying all coefficients or proving a terminal continuation. A complete modulated family,
MFR4's quantitative residual/stability control and MFR5's arithmetic sign remain open.

[definition] The next MFR3 construction composes these pressure-induced cubic currents into the
modulated core and retains the actual exterior that supplies their coefficients. Its pressure
evolution and higher spatial/time remainder must be derived before a continuing family or an
invariant strain-growth condition is asserted. MFR4 owns quantitative nonlinear stability.

[established-bounded; process-audit] All five new formal owners passed focused Lean builds.
The final quartic-current endpoint passed 3,576 jobs, the regular Gaussian core 3,398, the actual
strain-source owner 3,569, and the periodic initial/local-existence owner 3,702. Endpoint axiom
prints contain only `propext`, `Classical.choice` and `Quot.sound`.

[established-bounded; process-audit] The live umbrella encountered an actively changing HNP
`PassiveContact` proof draft in `HolonicOrientedSiteTransport.lean`. The mathematical integration
was therefore checked in `.local/mfr3-viscous-strain-verification`, against committed base
`98efc058` plus the five new mathematical owners and their imports. Its `lake build ElementaryHolonics`
passed all 9,917 jobs. All six integrated formal files match the checked copies. The isolated
checkout and independent copy-on-write project cache are retained; pinned package dependencies
are shared. Concurrent HNP source and evidence were preserved.

[established-bounded; process-audit] Lean is 4.33.0. The final exact order-three Fourier replay
exited zero and matched the stored receipt; the independent Gaussian Cartesian/profile-series
check also exited zero under SymPy 1.14.0 in `/tmp/holonics-mfr3-symbolic/bin/python`. These are
mathematical source controls. No native/Cargo behavior or full-fluid time evolution was newly
validated by this return.
