# The axial pressure mean returns the complete quadratic source through the moving cell

**Authority:** Brandon's standing
[moving-frame goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
This continues the [anisotropic source and radial clock](2026-09-05_MFR3_THE_ANISOTROPIC_FRAME_RETURNS_ITS_PRESSURE_METRIC_AND_RADIAL_VISCOUS_CLOCK.md).

## The actual periodic source determines the nonconstant pressure mean

[definition] At an interior time of an admitted smooth, unforced, physical unit-periodic
Navier–Stokes solution, write

```text
mean_h f(z) = integral_0^1 integral_0^1 f(x,y,z) dy dx.
```

Here `u_3` is the vertical velocity, component `2 : Fin 3` in Lean. These are complete horizontal
integrals. The scalar pressure's spatially constant gauge remains unspecified.

[proved-derived; formal-checked] `NavierStokesAxialPressureMode` derives, for each physical
integer frequency `k=(0,0,n)` with `n != 0`,

```text
Fourier(u_3)(k,t) = 0,
Fourier(p)(k,t) = -Fourier(u_3^2)(k,t).
```

The first identity follows from actual incompressibility. It holds throughout the open lifespan,
so its actual time derivative vanishes. The source momentum equation then removes the zero
vertical viscous mode and equates the pressure gradient with negative vertical advection.
The existing complete H3 product/convolution owner identifies that advection coefficient as
`2*pi*i*n*Fourier(u_3^2)`. The nonzero multiplier can then be cancelled. No projected pressure
equation, Fourier truncation or nonlinear mean closure is assumed.

[proved-derived; formal-checked] `NavierStokesTorusHorizontalMean` splits off the axial circle
using a measure-preserving equivalence and retains exactly the full axial Fourier population.
Vanishing of all nonconstant coefficients reconstructs the continuous mean as its zero
coefficient. `NavierStokesPeriodicHorizontalMean` identifies this normalized Haar mean with the
literal physical integral above by two circle-to-interval integral identities. Periodic
projection removes arbitrary quotient representatives.

[proved-derived; formal-checked] `NavierStokesPressureMean` composes these owners to return

```text
mean_h p(z,t) + mean_h(u_3^2)(z,t) = C(t),
d_z mean_h p = -d_z mean_h(u_3^2)
             = -mean_h[d_z(u_3^2)].
```

The formal constant identity compares any two heights; `C(t)` can be read at any chosen reference
height. `NavierStokesHorizontalMean` and `NavierStokesCompactSlabBound` pay the actual derivative
interchange: the two horizontal integrals are regrouped over the compact square, and continuous
Fréchet derivatives have a uniform bound on a compact slab around the selected height. This is
local domination in the spatial parameter, not a bound uniform to a terminal fluid time.
The mean of squared velocity is retained before any scalar averaging of velocity itself.

## The same source passes through the full moving cell

[definition] Freeze the frame at a regular time and write

```text
A=diag(r,r,zScale),              x=centre+A*y,
b=r^2/K,                        epsilon=(r/zScale)^2,
Pi(y)=(r/K)^2*p(x),              W(y)=(b/zScale)*u_3(x).
```

For positive physical lengths and `K>0`, the actual transported horizontal cell at axial chart
coordinate `zeta` is

```text
[-centre_0/r,(1-centre_0)/r] × [-centre_1/r,(1-centre_1)/r].
```

Its normalized horizontal mean is `r^2` times the integral over that cell. Physical harmonic
labels remain integers; chart periods are `1/r,1/r,1/zScale`. The axial physical coordinate is
`centre_2+zScale*zeta`.

[proved-derived; formal-checked] `NavierStokesFramedHorizontalMean` proves the exact affine
transport, retaining amplitude `a` and both length factors:

```text
framed_mean_h[a*f(centre+A*y)](zeta)
  = a*mean_h f(centre_2+zScale*zeta).
```

Two actual affine substitutions prove the identity. The theorem allows any nonzero `r`, retaining
the two interval orientations; the physical interpretation uses positive lengths. A fixed
normalized unit square is not substituted for the transported cell.

[proved-derived; formal-checked] `NavierStokesAnisotropicPressureMean` now returns the actual
source through that cell:

```text
epsilon*framed_mean_h Pi + framed_mean_h(W^2) is independent of zeta,
epsilon*d_zeta framed_mean_h Pi = -d_zeta framed_mean_h(W^2),
abs(d_zeta framed_mean_h Pi) = abs(d_zeta framed_mean_h(W^2))/epsilon.
```

The source and derivative theorems require nonzero `r`, `zScale` and `K`. Actual derivative
transport comes from the physical compact-slab mean theorem and the affine chain rule; no
unspecified differentiability of a totalized `deriv` is used. The derivatives are spatial, with
the frame frozen at the selected interior physical time. The existing clock/source owners supply
the changing frame and its time terms separately.

[conditional] Along a proposed family, neglecting this mean pressure force requires control of
`d_zeta framed_mean_h(W^2)`. If its magnitude has a positive lower bound, the pressure-mean
gradient has the corresponding inverse-aspect lower bound. The theorem does not supply such a
lower bound: the full normalized horizontal cell itself changes size, and a localized core's
contribution can shrink under its averaging factor. No aspect-ratio limit has been interchanged
with an integral or a derivative here.

## Exact source control and the receiver distinction

[established-bounded; computational-witness]
[derive_source.py](../experiments/mfr3_axial_pressure_mean/derive_source.py) constructs the smooth
physical unit-periodic Taylor–Green source

```text
u=a(t)*(sin(2*pi*x)*cos(2*pi*z), 0, -cos(2*pi*x)*sin(2*pi*z)),
p=a(t)^2/4*(cos(4*pi*x)+cos(4*pi*z)),
a'=-8*pi^2*nu*a.
```

Exact symbolic time, advection, diffusion and pressure calculations return zero divergence and
the full unforced momentum residual. Its complete physical means are
`mean_h p=a^2*cos(4*pi*z)/4` and `mean_h(u_3^2)=a^2*sin(2*pi*z)^2/2`, whose sum is `a^2/4`.
The script independently integrates the chart fields over the exact shifted cell above and
recovers the same pressure/mean-square balance with the aspect factor.

[counterexample; computational-witness] Replacing the mean square by the square of the mean
discards a nonzero source: this field has `framed_mean_h W=0`. Omitting `epsilon` also changes
the force. At `a=r=K=1`, `zScale=2`, `centre_2=0`, `zeta=1/16`, the respective incorrect
balances are `-pi/2` and `-3*pi/2`. These exact nonzero values supplement the symbolic
expressions in the [receipt](../experiments/mfr3_axial_pressure_mean/source_receipt.json).

[interpretation] In Holonics terms, retaining only the first velocity mean does not preserve
this pressure receiver: distinct horizontal populations with the same first mean can have
different quadratic means and pressure forces. The source equation and the explicit control
give the map and a falsifier. This does not identify arbitrary coordinate singularities with
physical fluid blowup.

## Consequence for the next family and verification

[open] A replacement radial-viscous circulation profile must obtain its strain, pressure and
finite-energy exterior from the actual periodic field. The full moving-cell mean must be
evaluated before declaring its axial force negligible. The local core alone does not specify
that integral. The smooth Taylor–Green control supplies no singular continuation or asymptotic
lower bound for a proposed concentrating family.

[open] MFR3's replacement family, MFR4's quantitative residual/nonlinear stability and MFR5's
arithmetic sign remain unfinished. The rejected compact radial cutoff and the established RH
endpoint scopes remain standing.

[established-bounded; process-audit] The physical mean endpoint passed its 3,961-job focused Lean
build; the complete frame derivative and absolute-gradient endpoint passed 9,029 jobs. Endpoint
axiom prints contain only `propext`, `Classical.choice` and `Quot.sound`. Lean is 4.33.0 with the
repository's pinned dependencies. The final exact source control passed using SymPy 1.14.0 in
`/tmp/holonics-mfr3-symbolic/bin/python`. The live `lake build ElementaryHolonics` umbrella passed
all 9,912 jobs against committed base `2384e802` plus the eight new mathematical owners and their
imports. No native/Cargo behavior is changed or newly tested by this return.
