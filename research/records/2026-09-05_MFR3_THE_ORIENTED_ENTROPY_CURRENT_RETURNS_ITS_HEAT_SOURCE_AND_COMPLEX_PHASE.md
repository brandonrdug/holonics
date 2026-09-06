# The oriented entropy current returns its heat source and complex phase

**Authority:** Brandon's latest instruction focuses the standing MFR work on complex Euler,
Navier–Stokes and temporal evolution, using the existing entropy, cross-entropy and heat-diffusion
construction. Direct RH pursuit is deferred. The standing plan retains its filename and its
completed returns.

## Recovered meaning and source owners

[historical; source-inspected] Brandon's August 26 messages at `20:16:09.450Z` and
`20:54:30.773Z`, retained in the August 22 root conversation
`01a02c64-4285-7600-88f6-f634595262f8`, ask for deterministic addressed action histories,
entropy as an interior turn/current, distinct oriented time axes and interacting cross-currents.
In particular: “If their entropies are perfectly aligned, then the cross is also null!”
The September 3 message, quoted in the [complex-field record](2026-09-03_THE_SEAMS_ARE_LOCAL_OPTIMA_OF_THE_THREAD_ENERGY_THE_PRIMES_ARE_THE_MISSING_HALF_AND_THE_FLOW_BINDS_THE_INTEGER_EVENTS.md),
explicitly requests the complex Euler/Hodge lens. These are the sources of the current correction,
not a new statistical interpretation substituted for that request.

[proved-derived; formal-checked] `HolonicEntropyActionInduction` already constructs the exact
storage/current/production balance, its finite telescope, receiver-relative monotonicity under
its boundary and production hypotheses, the skew/dissipative split, and the oriented current

```text
Omega(J,K;i,j)=J_i*K_j-J_j*K_i.
```

Its cross-current reverses with orientation, has an exact returned-difference law, and retains
its alignment fibre. `HolonicTorusEntropyParametronEquivalence` realizes the same operation as the
exterior product of torus winding currents. These owners precede the present fluid investigation.

[proved-derived; formal-checked] The separate `HolonicMembraneActionTransport` owner supplies
statistical cross-entropy after its normalized positive receiver is declared, retaining its
complete action fibre. The earlier `no_successor_factor_of_equal_entropy` theorem already states
the general failure of a successor to factor through an insufficient scalar. The recent MFR
local-pressure example is a source-specific instance of this existing issue.

## Diffusion acts on the relation between the currents

[proved-derived] Let smooth current sections on a fixed Euclidean chart obey

```text
(D_t-nu*Delta)J=A*J+F,
(D_t-nu*Delta)K=A*K+G,
D_t=partial_t+b dot grad,
```

with the same real advecting field `b`, fixed diffusivity `nu`, and retained stretching matrix
`A` and sources `F,G`. Bilinearity and the spatial product rule give the exact two-current source

```text
(D_t-nu*Delta)(J wedge K)
  = (A*J) wedge K + J wedge (A*K)
    -2*nu*sum_a (partial_a J) wedge (partial_a K)
    + F wedge K + J wedge G.
```

The mixed spatial-derivative term comes from differentiating the product twice. The first-order
material derivative has only the two ordinary product terms. In three dimensions, after the
fixed oriented Euclidean Hodge identification with a vector cross product, stretching acts as
`tr(A)*I-transpose(A)`. For `A=grad b` with `div b=0`, this is `-transpose(A)`.
The component product identity and this induced stretching identity were independently verified
by the exact symbolic audit below. A moving frame must also transport the connection and Hodge
map; this displayed formula uses the fixed chart.

[proved-derived] An initially null cross-current does not remove its diffusion source. If
`K=f*J` with spatially varying `f`, then
`(partial_a J) wedge (partial_a K)=(partial_a f)*(partial_a J wedge J)`.
The relative scale and the changing direction therefore remain relevant on the null fibre.
A spatially constant common proportionality is preserved by a shared homogeneous linear heat
flow; spatially varying alignment requires the displayed source to vanish as well.

## An exact temporal fluid realization

[definition] Let `q>0`, `lambda=nu*q^2`, `theta=q*z` and put

```text
J(t,z)=exp(-lambda*t)*(cos theta, sin theta, 0),
K(t,z)=((1+exp(-4*lambda*t)*cos(2*theta))/2,
        exp(-4*lambda*t)*sin(2*theta)/2, 0).
```

Both fields depend only on the third spatial coordinate and have zero third component. The
period is `2*pi/q`; `q=2*pi` gives the unit torus. The two-frequency factorization is retained.

[established-bounded; computational-witness] Each is an actual smooth, unforced periodic
Navier–Stokes solution with pressure zero: divergence and self-advection vanish identically,
and `partial_t u=nu*Delta u`. At `nu=0`, both are stationary Euler solutions. The
[audit](../experiments/mfr_entropy_heat_current/derive_current.py) verifies the full momentum
residual, actual period, divergence, local kinetic-energy flux and periodic energy balance.
This is a controlled source instance; the nonlinear pressure/stretching terms vanish in this
shear class.

[proved-derived] Their complex horizontal faces and oriented cross-current are

```text
j=exp(-lambda*t)*exp(i*theta),
k=(1+exp(-4*lambda*t)*exp(2*i*theta))/2,
Omega_01=Im(conjugate(j)*k)
        =exp(-lambda*t)*(exp(-4*lambda*t)-1)*sin(theta)/2.
```

At time zero, `K=cos(theta)*J`: the entire cross-current is zero, including regions where both
currents are nonzero. For `nu>0`, `t>0` and `sin(theta)!=0`, it becomes nonzero. Its actual heat
source is

```text
(partial_t-nu*Delta)Omega_01
  =-2*lambda*exp(-5*lambda*t)*sin(theta).
```

This is exactly the mixed spatial-derivative term above. The zero-viscosity specialization keeps
the cross-current null. The temporal conclusion retains phase and orientation before taking any
scalar magnitude or entropy receiver.

[established-bounded; computational-witness] Both kinetic energies nevertheless obey their
ordinary dissipative laws, with normalized cell averages

```text
E_J=exp(-2*lambda*t)/2,          D_J=lambda*exp(-2*lambda*t),
E_K=(1+exp(-8*lambda*t))/8,      D_K=lambda*exp(-8*lambda*t),
E_J'=-D_J,                       E_K'=-D_K.
```

The complete [receipt](../experiments/mfr_entropy_heat_current/current_receipt.json) retains the
fields, oriented current, mixed source and energy identities. This realizes the existing
exterior-current operation on fluid sections. A thermal entropy receiver additionally supplies
its temperature/quantity map and entropy boundary flux; the velocity wedge itself is not assigned
entropy units by its name.

[proved-derived; formal-checked] `HolonicEntropyHeatCurrent` now proves the complex conjugate
pairing, initial alignment for every viscosity, positive-time reopening, Euler preservation,
actual componentwise heat equations and the sourced cross-current heat equation. The conclusion
uses actual temporal derivatives and iterated spatial derivatives of the displayed fields.
Its exact phase-coordinate source is the existing `entropyAxisCrossCurrent` applied to their
spatial derivative currents. The complete three-dimensional fluid realization and energy laws
remain at the independent symbolic-audit scope stated above.

[open] The nonlinear MFR datum still needs its actual stretching, pressure, boundary and
unresolved-mode contributions composed with this source law.

## The complex-field continuation has existing analytic sources

[proved-derived] On a zero-free patch, let `Phi=log H` and `V=H_z/H`. A complex heat source
`H_t=kappa*H_zz` gives

```text
Phi_t=kappa*(Phi_zz+Phi_z^2),
V_t=kappa*(V_zz+2*V*V_z).
```

The sign and domain of the heat parameter remain explicit. With real positive `kappa`,
`u=-2*kappa*V` solves the complex viscous Burgers equation. At a fixed time, the amplitude and
phase of a holomorphic potential give the local Hodge/conjugate-gradient circulation relation.
The Burgers time law and an incompressible Euler/Navier–Stokes realization carry their respective
actual velocity and pressure equations. The older complex-field record now states those passages
without calling the logarithmic heat equation itself the full incompressible Navier–Stokes law.

[established-bounded; computational-witness] The same second complex current has the entire
continuation `H(t,zeta)=(1+exp(-4*lambda*t)*exp(2*i*q*zeta))/2`. Its actual heat equation and
logarithmic/Burgers residual are verified by the source audit. Its simple zeros have exact paths

```text
zeta_n(t)=(pi/2+pi*n)/q-2*i*nu*q*t,      n integer,
H_zeta(t,zeta_n(t))=-i*q.
```

Thus the logarithmic receiver has moving simple poles at these zeros, with its regular domain
retained explicitly. The underlying periodic shear fields remain smooth. This is a concrete
null/pole and temporal-phase passage for the same source, not a new fluid blowup claim.

[proved-standard] Poláčik and Šverák construct finite-time singularities of complex-valued
one-dimensional viscous Burgers flow and relate them to zeros of its complex heat antecedent.
Their sector condition also gives a source-specific no-zero/global-existence regime. This provides
a concrete complex null-to-singular temporal construction to study independently of arithmetic.
Source: [Zeros of complex caloric functions and singularities of complex viscous Burgers equation](https://arxiv.org/abs/math/0612506),
§2, Propositions 2.1–2.2.

[proved-standard] Li and Sinai prove finite-time blowup for selected data in families of genuinely
complex-valued, unforced three-dimensional Navier–Stokes solutions on `R^3`. This is an existing
complex-valued source construction, with its own reconstruction conditions, available for the
next mechanism comparison. Source: [JEMS 10 (2008), 267–313](https://ems.press/journals/jems/articles/1424).
The present return has not formalized that proof or transferred it to the real periodic problem.

[definition] The current focus is the source-realized temporal relation: oriented complex current,
heat diffusion, stretching/pressure and boundary production, followed by the explicit remainder
comparison already planned. The two-current heat instance is a reusable control for that
composition. RH remains preserved application material, with direct arithmetic research deferred
under Brandon's latest instruction.

[established-bounded; process-audit] The focused heat-current owner passed 3,722 jobs, and the
isolated complete `lake build ElementaryHolonics` passed 9,923 jobs against committed base
`62dd5b0b` plus the new owner and its umbrella import. Both integrated formal files match the
checked isolated copies. Endpoint axiom prints contain only `propext`, `Classical.choice` and
`Quot.sound`. The full symbolic fluid/current/energy and complex-zero/Burgers audit exited zero with SymPy 1.14.0;
adding the complex continuation preserved every earlier source and energy receipt.
No native runtime behavior was changed or newly measured.
