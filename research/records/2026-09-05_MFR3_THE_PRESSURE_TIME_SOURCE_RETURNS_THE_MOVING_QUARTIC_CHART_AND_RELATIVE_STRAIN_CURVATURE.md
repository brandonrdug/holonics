# The pressure time source returns the moving quartic chart and relative strain curvature

**Authority:** Brandon's standing
[moving-frame goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
This continues the [viscous core and cubic response](2026-09-05_MFR3_THE_VISCOUS_CORE_RETURNS_ITS_PERIODIC_STRAIN_SOURCE_AND_CUBIC_RESPONSE.md).

## Actual time jets cross the same bounded source passages

[proved-derived; formal-checked] `NavierStokesPressureEvolution` differentiates the complete
quadratic source before applying its existing elliptic pressure map:

```text
P_t = Pmap[B(U_t,U)+B(U,U_t)].
```

Both ordered terms remain. The scale-indexed velocity jet is supplied by the actual fixed mild
path and coherent smooth Sobolev tower. The theorem holds as `HasDerivWithinAt` on `Ico 0 T`,
including the initial right face, and as `HasDerivAt` at interior times. No pressure-time jet or
extra velocity derivative is assumed.

[proved-derived; formal-checked] `NavierStokesVelocitySecondTimeJet` similarly returns

```text
U_tt = S(U_t) - B_Leray(U_t,U) - B_Leray(U,U_t).
```

The actual Stokes term uses the two-higher-order lift and the bilinear terms use the adjacent
lift; the operator indices and weighted decoders remain explicit. The same initial/right and
interior time scopes apply.

[proved-derived; formal-checked] `NavierStokesPressureJetReceivers` composes ordered spatial
derivatives, full Fourier reconstruction and point evaluation as bounded linear receivers.
The empty word is exactly the physical zero-gauge pressure of the same path. Prepending a
coordinate takes the actual spatial derivative of that reconstructed field. Every such receiver
carries the pressure time source through the actual right derivative; it is not a selected
finite Fourier sum substituted for the full pressure.

## The aspect chart retains force amplitudes and source terms

[definition] In the declared quartic symmetry family, put `s=x^2+y^2` and write

```text
P4=A*(x^4+y^4)+B*x^2*y^2+C*s*z^2+D*z^4+E*xy*(x^2-y^2).
```

The five coefficients are read from actual fourth derivatives with their Taylor factorials.
Reconstruction of a whole quartic from these five receivers requires this symmetry family.
The general ordered-word owner retains other derivatives, and the finite source audit below
checks all fifteen degree-four monomials independently.

[proved-derived; formal-checked] `NavierStokesAnisotropicQuarticCurrent` gives the exact split

```text
P4=L*s^2+M*s*z^2+D*H_ax,epsilon+b*H_cos+c*H_sin,
L=(6A+B-3*epsilon^2*D)/8,        M=C+3*epsilon*D,
kappa=epsilon*D,                b=(2A-B)/8,          c=E,
H_ax,epsilon=z^4-3*epsilon*s*z^2+3*epsilon^2*s^2/8.
```

`H_cos` and `H_sin` are the retained angular quartics. Applying the actual pressure metric
`diag(1,1,epsilon)` returns the harmonic force

```text
Q_epsilon=kappa*V_epsilon+b*Q_cos+c*Q_sin,
V_epsilon=(6xz^2-3*epsilon*x*s/2,
           6yz^2-3*epsilon*y*s/2,
           -4z^3+6*epsilon*s*z).
```

This field is smooth and divergence-free; its value and first derivative vanish at the centre.
Its complete null fibre is exactly `kappa=b=c=0`, for every real `epsilon`. In the raw pressure
chart the null fibre instead reads `epsilon*D=b=c=0`. Thus finite `D` becomes invisible at
`epsilon=0`, while the force-amplitude chart itself remains regular. The physical inverse-frame
theorems still require a regular frame; no finite pressure inverse is asserted at collapse.

[proved-derived; formal-checked] The two remaining coefficients retain the Poisson source:

```text
div[diag(1,1,epsilon)*grad(L*s^2+M*s*z^2)]
  = (16L+2*epsilon*M)*s+4M*z^2.
```

They cannot be silently folded into a harmonic-pressure correction. The owner constructs the
full pressure force, containing both of these terms and all three harmonic ones, as the actual
negative metric gradient of the reconstructed quartic.

## Actual modulation, including the moving basis

[proved-derived; formal-checked] `NavierStokesQuarticPressureModulation` derives the actual
diagonal polynomial pullback for `Pi=(r/K)^2*p`, spatial frame `diag(r,r,zScale)` and
`epsilon=(r/zScale)^2`. In the adapted coefficient chart `(L,M,kappa,b,c)`, the weights are

```text
w=(r^6, r^4*zScale^2, r^4*zScale^2, r^6, r^6)/K^2.
```

These are two factored homogeneity classes. The equalities are attached to the actual polynomial
pullback, not declared as new coefficient scales. For a fixed physical Taylor centre, each
normalized coefficient obeys

```text
C_i' = g_i*C_i + clockRate*w_i*R_i(P_t),
g=(6r'/r, 4r'/r+2zScale'/zScale, 4r'/r+2zScale'/zScale, 6r'/r, 6r'/r),
clockRate=r^2/K.
```

Here `R_i` is the explicitly constructed bounded physical coefficient receiver and `P_t` is the
actual source from the first section. The ordinary derivative holds at interior physical times;
the initial right derivative holds when the actual clock maps the declared half-open chart
aperture into the physical aperture. A moving Taylor centre would additionally require its
spatial derivative contribution; this return uses a fixed centre.

[proved-derived; formal-checked] The complete sourced pressure-force derivative also carries
the changing basis. If `F_epsilon(C)` denotes the full five-coefficient force, then

```text
d_tau F_epsilon(C)
  = F_epsilon(C') + epsilon'*(M*T_connection+kappa*V_connection),
T_connection=(0,0,-2*s*z),
V_connection=(-3*x*s/2,-3*y*s/2,6*s*z).
```

The final `sourcedQuarticPressureForce_hasDerivWithinAt_Ico` composes these terms with the actual
pressure source and physical clock. Holding the basis fixed would omit the displayed connection.

## The complete periodic second-time calculation

[established-bounded; computational-witness]
[derive_time_jets.py](../experiments/mfr3_pressure_evolution/derive_time_jets.py) consumes the same
initial spectrum as the preceding return. The common
[spectrum constructor](../experiments/mfr3_viscous_strain_source/source_spectrum.py) was extracted
from the original audit; the original complete audit replay remains identical. No new initial
field is selected for this calculation.

[established-bounded; computational-witness] The evolution retains all generated modes and
computes the actual phase-source fields

```text
v=Delta u-(u.grad)u-grad p,
-Delta p_t=tr(Dv*Du)+tr(Du*Dv),
w=Delta v-(v.grad)u-(u.grad)v-grad p_t.
```

The coefficient algebra is the exact quotient `Q[rho]/(P)`, with `P` the retained matching
quadratic. Both real root intervals are verified; the declared branch is positive. The final
populations contain 312 initial velocity modes, 2,164 first-time velocity modes, 6,824 second-time
velocity modes and 6,850 pressure-time modes. Modewise reality, divergence and source zero modes
are checked. An independent Leray-complement reconstruction agrees with the full ordered
pressure-time trace source.

[established-bounded; computational-witness] The initial pressure curvature, all fifteen initial
quartic pressure coefficients and the initial cubic velocity-time receivers match the accepted
parent exactly. `Dv=2Du` remains true. The full pressure-time Hessian, all fifteen quartic
coefficients and the complete `Dw-8Du` defect are retained in the
[receipt](../experiments/mfr3_pressure_evolution/time_jet_receipt.json).

[established-bounded; computational-witness] Independent local production identities agree:

```text
L_physical'=-1/2-15*h_ax/2,      M_physical'=30*h_ax,
(Dw)_10-(Dw)_01=16.
```

For the declared phase frame `beta=1`, `gamma=4/5`, `K=r=zScale=clockRate=1`, with
`epsilon'=-2/5`, the normalized initial rates have exact outward enclosures:

| Coefficient rate | Enclosure |
|---|---|
| `L'` | `[-823/500,-329/200]` |
| `M'` | `[6583/1000,823/125]` |
| `kappa'` | `[4519/500,9039/1000]` |
| `b'` | `[-329/200,-411/250]` |
| `c'` | `[-6241/1000,-156/25]` |

The `kappa` rate uses the mixed weight; it is not the raw axial pressure coefficient's rate.
The unit-period physical realization uses `k=2*pi`, `u_phys=k*u(kX,k^2*t)` and `p_phys=k^2*p`.
Its corresponding initial frame has `r=zScale=1/k`, `clockRate=1/k^2`, `K=1`, giving the same
normalized rates after the explicit weights and clock are applied.

## The fixed relative-strain trajectory fails at the next source receiver

[established-bounded; computational-witness] At the selected root, the physical phase-source
second axial-strain rate and pressure-time curvature satisfy

```text
(Dw)_22 in [-107813/1000,-26953/250],
(p_t)_zz in [7921/125,63369/1000].
```

The initial spin is `Omega=1`, with `Omega_t=2` and `Omega_tt=8`; the axial strain is `a=10/3`,
with `a_t=2a`. The spin second derivative is read from the antisymmetric entries of the complete
second gradient, not inferred from the axial pressure equation.

[proved-derived] The ratio `a/Omega` therefore has zero first derivative at this initial
receiver and second derivative `a_tt-8a`. The same quantity is the second derivative of
normalized axial strain in the declared radial clock at this instant: the normalized spin's
first two derivatives vanish. This follows by the quotient and clock product rules at the
stated jets; it is not a future-time estimate.

[counterexample; computational-witness] The exact ratio-curvature enclosure is
`[-3362/25,-134479/1000]`, entirely negative. Thus this datum, despite paying the complete initial
first-gradient growth, cannot follow the fixed relative-strain trajectory through second order.
The calculation does not show a later turnover, rule out other modulation, or decide physical
finite-time regularity. Those conclusions would require the corresponding time remainder and
continuation argument.

[proved-derived; computational-witness] The complete first-pressure matching fibre was then
checked using [verify_compatibility.py](../experiments/mfr3_pressure_evolution/verify_compatibility.py),
without repeating the Fourier calculation. The negative branch also has negative relative-strain
curvature, enclosed by `[-3904/25,-156159/1000]`. An exact rational polynomial certificate
`U*P+V*R=1`, with `P` the initial-pressure condition and `R=a_tt-8a`, proves that neither matching
branch can satisfy the fixed-ratio second condition. The
[certificate](../experiments/mfr3_pressure_evolution/compatibility_receipt.json) retains both branches,
all multipliers and the verified identity. This incompatibility is specific to the declared
one-parameter initial family and candidate trajectory.

[definition] MFR3 next uses the pressure and pressure-time receivers together to search the
remaining exterior fibre for a source-consistent growing-core modulation, retaining all five
pressure coefficients and the generated modes. The fixed relative-strain test is a rejected
candidate trajectory, not a replacement condition imposed on all modulated families.

[open] A surviving continuing family, higher spatial/time remainder, MFR4's quantitative
nonlinear stability and MFR5's arithmetic sign remain unresolved.

[established-bounded; process-audit] The final focused source/modulation integration passed
9,027 Lean jobs. The isolated `lake build ElementaryHolonics` passed 9,922 jobs against committed
base `e92d24bc` plus the five new formal owners and imports. The six integrated formal files match
the checked copies. Endpoint axiom prints contain only `propext`, `Classical.choice` and
`Quot.sound`. The isolated checkout and independent copy-on-write cache remain in
`.local/mfr3-pressure-evolution-verification`; concurrent HNP draft work was preserved.

[established-bounded; process-audit] The parent source audit replay is byte-identical after
extracting its shared initial spectrum. The final time-source replay exited zero and produced the
stored receipt under SymPy 1.14.0 and python-flint 0.9.0. Primary review corrected an early draft
that discarded generated first-time modes and used an incorrect second trace contraction; these
were implementation defects, not fluid obstructions. The final parent-match, full divergence,
independent pressure and local-production identities all returned. The separate full-fibre
compatibility certificate also exited zero. No native/Cargo behavior or later-time solution
interval was newly validated by this return.
