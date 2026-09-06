# The exterior modulation returns a joint pressure receiver

**Authority:** Brandon's standing
[moving-frame goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
This continues the
[pressure-evolution return](2026-09-05_MFR3_THE_PRESSURE_TIME_SOURCE_RETURNS_THE_MOVING_QUARTIC_CHART_AND_RELATIVE_STRAIN_CURVATURE.md).

## Two exterior directions in the same local-jet fibre

[definition] Retain the preceding periodic strain field `S`, horizontal swirl
`V=(psi_y,-psi_x,0)` and potential, and replace its axial factor by

```text
B(z)=1+rho*(1-cos z)^3+sigma*(1-cos(2*z))^3,
u=S+B*V.
```

The change is in the third component `B*psi` of the actual vector potential. Both
parameters are real; no sign convention removes part of the parameter fibre.

[proved-derived] Each cutoff variation vanishes to axial order six, and `V`
vanishes to horizontal order one at the centre. Their velocity variations
therefore start at total degree seven. Every velocity derivative through order
six remains fixed. The directions are independent: the second contains axial
frequency six, which the first does not contain. The initial axial velocity is unchanged,
so the initial full horizontal pressure-mean source is also unchanged.
That mean does not determine the pressure at a particular horizontal point.

[proved-derived] Reflection in the second coordinate fixes `S` and sends the
entire swirl field `B*V` to `-B*V`, when both position and velocity are transformed
by that reflection. The pressure Poisson map and the actual Navier--Stokes
time source respect this orthogonal transformation. Thus the axial scalar
receivers `p_zz(0)` and `p_tzz(0)` are even in the entire swirl profile `B`.
Pressure is quadratic in velocity; pressure-time is the sum of a quadratic
viscous contribution and a cubic convective contribution. Reflection removes
the terms of odd degree in `B`, so both scalar receivers have degree at most two
in `(rho,sigma)`. This does not mean they are separately even in those two
parameters. Other pressure receivers retain their actual polynomial degrees.

## Local production reduces the joint target

[established-bounded; computational-witness]
[local_jet_reduction.py](../experiments/mfr3_exterior_modulation/local_jet_reduction.py)
independently differentiates the accepted degree-five velocity Taylor polynomial.
Write `h=p_zz(0)` and `ht=p_tzz(0)`. The rotation symmetry and the local Poisson
equation give

```text
Du=[[-5/3,-1,0],[1,-5/3,0],[0,0,10/3]],
Hess p=diag(-22/3-h/2,-22/3-h/2,h),
Dv=[[50/9+h/2,-2,0],[2,50/9+h/2,0],[0,0,-100/9-h]],
Lap(Dv)=[[0,16/3,0],[-16/3,0,0],[0,0,0]].
```

The pressure trace is `-44/3`, not zero. Although the pressure Hessian is
nonlocal, its spatial Laplacian is fixed by the local Poisson source. Explicitly,
with `v=Lap(u)-(u.grad)u-grad p`, the calculation uses

```text
Lap(v)=Lap^2(u)-Lap((u.grad)u)+grad(tr(Du^2)).
```

Only the retained velocity derivatives through order five enter its gradient
at the centre. No harmonic pressure coefficient is set to zero.

[established-bounded; computational-witness] Differentiating the actual source
at the fixed symmetry centre, where `u=v=0`, gives

```text
Dw=Lap(Dv)-Dv*Du-Du*Dv-Hess p_t,
a_tt=2*a^3+2*a*h-ht,                 a=10/3,
Omega_tt=-88/9-h.
```

Here `Omega=(Du_10-Du_01)/2`. On the initial-pressure matching locus
`h=-160/9`, the whole matrix satisfies `Dv=2*Du`; consequently
`Omega=1`, `Omega_t=2`, `Omega_tt=8`, `a_t=2*a`, and

```text
(a/Omega)_tt=-640/9-ht.
```

The two conditions for this particular fixed-ratio candidate are therefore
`h=-160/9` and `ht=-640/9`. They are not conditions imposed on every modulated
family. The
[local receipt](../experiments/mfr3_exterior_modulation/local_jet_receipt.json)
retains the complete matrices and exact symbolic checks.

## Joint exterior receiver and verification

[established-bounded; computational-witness]
[derive_receivers.py](../experiments/mfr3_exterior_modulation/derive_receivers.py)
constructs the complete source in `Q[rho,sigma]`, using exact rational
multivariate polynomial coefficients. It retains 408 initial velocity modes,
3,308 first-time modes, 11,160 second-time modes, 3,284 initial pressure modes
and 10,974 pressure-time modes. Both ordered pressure-time trace terms agree
mode by mode with the independent pressure projection of both ordered
convection terms. Reality, divergence and source zero modes are verified.
No source coefficient is reduced modulo a matching condition.

[established-bounded; computational-witness] The complete two-direction
velocity-derivative population through order six is unchanged. All entries
of `Du`, `Dv`, `Dw`, the pressure Hessian and `Lap(Dv)` agree with the
independent local calculation above. At `sigma=0`, initial pressure and all
fifteen initial quartic coefficients agree exactly with the parent source;
all time matrices and fifteen pressure-time quartic coefficients agree after
reduction modulo its matching quadratic. Both full quartics reconstruct in
the declared five-coefficient symmetry family. The
[source receipt](../experiments/mfr3_exterior_modulation/source_receipt.json)
retains every coefficient, including the Poisson-source terms and the
harmonic terms needed by the standing moving-force modulation theorem.

[proved-derived; computational-witness]
[certify_joint_fibre.py](../experiments/mfr3_exterior_modulation/certify_joint_fibre.py)
retains the initial-pressure matching set as a complete ellipse:

```text
P=h+160/9 = H - (v-v_P)^T K (v-v_P),
v=(rho,sigma),                    K positive definite, H>0.
```

Its exact centre, matrix and height are recorded. Both old matching branches
remain on this ellipse. The new direction also changes the joint receiver:
the determinant of `D(h,ht)` is positive at the origin and on the retained
positive-pressure branch at `sigma=0`. On that algebraic branch it lies in
`[347549/250,1390197/1000]`. Thus the failure below is not caused by merely
renaming a direction invisible to these receivers.

[proved-derived; computational-witness] The second-condition polynomial has
an exact positive square completion on the **entire real parameter plane**:

```text
T=ht+640/9
 = d_0*(eta_rho+c*eta_sigma)^2+d_1*eta_sigma^2+m,
eta=v-v_T,                       d_0>0, d_1>0,
m in [32227/500,12891/200],        m>64.
```

All coefficients are rational, and the polynomial identity and signs are
checked exactly. The
[certificate](../experiments/mfr3_exterior_modulation/compatibility_receipt.json)
retains the square factors, centres and pivots without expanding them into a
list of parameter samples. Hence no real parameter pair satisfies both
target equations. On the whole initial-pressure ellipse,
`(a/Omega)_tt=-T<-64`. This rejects the fixed-ratio trajectory for this
expanded exterior family; it is not a later-time estimate.

## The returned obstruction separates its physical source terms

[established-bounded; computational-witness] The audit also computes the
viscous pressure-time contribution directly from
`tr(D(Lap u)*Du)+tr(Du*D(Lap u))`, with phase viscosity one. Subtracting it
from the complete source gives the convective contribution. Their sum is
verified as an exact polynomial identity. The viscous quadratic form is
positive definite, while the convective form is indefinite.

[established-bounded; computational-witness] In the new direction, the
coefficients of `sigma^2` have the following exact outward enclosures:

| Source contribution to `p_tzz` | Coefficient enclosure |
|---|---|
| Viscous | `[57871/500,115743/1000]` |
| Convective | `[-27437/1000,-6859/250]` |
| Total | `[17661/200,44153/500]` |

The convective contribution moves this coefficient toward the desired sign;
the viscous contribution outweighs it in this declared family. The full
square completion, which also retains the mixed and linear terms, establishes
the actual exclusion. This does not prove a sign for arbitrary periodic
exteriors or for other viscosities and core data.

[definition] The next MFR3 passage follows the **nonconstant** strain/spin
modulation and all five pressure-force coefficients supplied by the actual
source. A further exterior variation must be selected for its returned
pressure and diffusion contributions, with any change to axial velocity
carrying the corresponding full moving-cell mean. The failed fixed ratio is
retained as a candidate obstruction rather than imposed as a new acceptance
condition for all continuations.

[established-bounded; process-audit] The preceding time-jet owner's SymPy-to-FLINT
conversion was repaired to reduce the complete input polynomial modulo the
matching quadratic. Truncating input degree before reduction would lose nonzero
lower-order remainders. Independent SymPy remainder checks passed for zero,
constants, linear, quadratic, cubic and degree-nine inputs; the former
degree-at-most-two behavior is unchanged. The existing quotient algebra and its
declared matching condition remain the same.

[open] A continuing source-consistent family, the higher spatial/time remainder,
MFR4 quantitative residual and stability, and MFR5 arithmetic sign remain to be
constructed. This finite initial-source calculation establishes no positive-time
growth interval or finite-time singularity.

[established-bounded; process-audit] The final full-source run and the separate
local-jet and joint-fibre certificates exited zero under SymPy 1.14.0 and
python-flint 0.9.0. The refined run adding the viscous/convective split preserved
every earlier complete source-receipt field. The symbolic-expression draft was
stopped before a successful receiver return; its replacement uses exact FLINT
coefficient operations throughout the convolution. No Lean sources/imports or
native behavior changed, so no new Lean or Cargo build is claimed.
