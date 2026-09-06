# The nonlinear cross-current returns pressure, stretching and cell flux

**Authority:** Brandon's instruction to proceed with the next construction after the
[oriented entropy/heat return](2026-09-05_MFR3_THE_ORIENTED_ENTROPY_CURRENT_RETURNS_ITS_HEAT_SOURCE_AND_COMPLEX_PHASE.md).
The current focus remains complex Euler/Navier–Stokes temporal sources and the existing
entropy/action current construction. Direct RH research remains deferred.

## The current belongs to one actual fluid solution

[definition] For the existing physical velocity `u` and its actual curl `omega`, use

```text
C=u cross omega,                  omega=curl u.
```

This is the negative of the `omega cross u` Lamb convention already named in
`NavierStokesVorticity`. Both current factors belong to the same velocity field and its derivative.

[proved-derived; formal-checked] The existing pointwise Lamb identity, together with the actual
kinetic-energy gradient, now gives the rotational momentum equation

```text
u_t=nu*Delta u+C-grad p-grad(|u|^2/2)+force.
```

`NavierStokesLambCurrentEvolution.smoothSolutionOn_rotational_momentum` derives this from the
finite-slab momentum equation. The transposed velocity Jacobian is proved to be the gradient of
the existing kinetic-energy density. Thus the oriented current supplies the nonlinear transport
while the pressure and kinetic-energy gradients retain their roles.

[proved-derived; formal-checked] `fluidCurrentAxes` places the three physical components in the
existing four-axis current section with fourth coordinate zero. Its `0,1` oriented entropy/action
receiver is exactly the third component of `C`. The corresponding complex receiver is

```text
C_2=Im(conjugate(u_0+i*u_1)*(omega_0+i*omega_1)).
```

The source is the physical real-flow chart with a complex two-axis receiver; this is not a claim
that the present file constructs all genuinely complex-valued three-dimensional solutions.
The current has acceleration units when velocity and vorticity have their ordinary physical units.
A thermal entropy quantity map is a further constitutive receiver, not a renaming of these units.

## The complete nonlinear temporal source

[proved-derived; formal-checked] `NavierStokesCrossCurrentCalculus` gives a continuous bilinear
realization of the already-owned spatial cross product. It proves the actual first-derivative
product rule and the full Euclidean Laplacian identity

```text
Delta(J cross K)
 = Delta J cross K + J cross Delta K
   +2*sum_a (partial_a J) cross (partial_a K).
```

Both mixed second-derivative terms are derived before summation. No Laplacian identity is supplied
as an assumption. The theorem applies to genuinely `C2` fields and to the same Euclidean spatial
operator used by the fluid source.

[proved-derived; formal-checked] Composing that calculus with the existing finite-slab momentum
and vorticity evolution yields

```text
C_t+(u.grad)C=nu*Delta C+S,

S = u cross ((omega.grad)u)
    - grad p cross omega
    - 2*nu*sum_a (partial_a u) cross (partial_a omega)
    + force cross omega + u cross curl(force).
```

`SmoothSolutionOn` supplies the actual joint smoothness, momentum, incompressibility and pressure.
The force's curl is retained. The equation holds at every interior point `0<t<T`; it does not
assume an independently prescribed vorticity or pressure evolution. Its open-lifespan attachment
uses a strictly smaller interior slab and asserts nothing about smoothness at the missing terminal
face. The algebra permits zero viscosity, with the corresponding Euler source, whenever the
admitted solution supplies that case.

## The source crosses the cell boundary and the time integral

[proved-derived; formal-checked] For component `i`, the actual advective/diffusive flux is

```text
F_i=C_i*u-nu*grad C_i,
partial_t C_i+div F_i=S_i.
```

The divergence form follows from the actual incompressibility equation, the scalar flux product
rule and commutation of component evaluation with the vector Laplacian. Pressure and stretching
remain in the source; they are not discarded by calling `C` a current.

[proved-derived; formal-checked] `NavierStokesCellLinearReceiver` pays differentiation of the
actual spatial integral, using joint smoothness and compact-cylinder domination. The composed
`NavierStokesLambCurrentCell` theorem returns

```text
M_i(t)=integral_unitCube C_i(x,t) dx,
M_i'(t)+faceBalance(F_i)=integral_unitCube S_i(x,t) dx.
```

`faceBalance` is the existing six-face oriented receiver, including all incoming and outgoing
faces. No periodic cancellation or nonnegative-production assumption is used in this theorem.
The open-lifespan attachment preserves the addressed time and physical cell. This is the actual
storage/current/production relation for the nonlinear cross-current, with the derivative-under-
integral step proved rather than supplied as a port.

[proved-derived] On a complete periodic cell, the mean of `C` itself vanishes for a smooth
incompressible velocity: componentwise, `C_i=partial_i(|u|^2/2)-sum_j partial_j(u_j*u_i)`, and
each derivative integrates to zero by opposite-face cancellation. The local current and its
face population therefore cannot be replaced by that scalar mean. Localized receivers retain
the corresponding weighted boundary/transport terms.

[open] This cell identity is not a terminally uniform estimate. Bounds on localized or moving
receivers, the complete source and the unresolved remainder still have to close on the intended
continuing interval. A signed current source does not acquire a positive production cone merely
from the balance identity.

## The unresolved field remains in the nonlinear current

[proved-derived; formal-checked] For any differentiable decomposition `u=v+w`, the existing curl
receiver is additive and the current reconstructs as

```text
C(u)=v cross curl v + v cross curl w
     +w cross curl v + w cross curl w.
```

Both ordered cross terms and the remainder self-interaction are retained. This is an identity of
the actual differentiated fields. It neither assumes that a finite resolved carrier is invariant
nor supplies a tail estimate by definition.

## The admitted periodic source verifies every oriented term

[established-bounded; computational-witness]
[derive_current.py](../experiments/mfr_lamb_current/derive_current.py) composes the existing complete
periodic source producer, retaining its two real exterior parameters `rho,sigma` and phase
viscosity one. It computes curl, the nonlinear current, its time derivative, advective transport,
Laplacian, stretching, pressure crossing and mixed diffusion over their full Fourier supports.
The complete current equation and rotational momentum identity agree mode by mode in
`Q[rho,sigma]`. The producer's existing source and parent-specialization assertions run as part
of the input construction; no source coefficient is replaced by a scalar receiver.

[established-bounded; computational-witness] All oriented terms have the required Fourier reality.
The velocity and curl are divergence-free. The current generally is not: the independent source
identity

```text
div C=|omega|^2-u dot curl omega
```

is verified with a nonzero current divergence. This prevents an incorrect incompressibility
assumption on the cross-current itself. The
[receipt](../experiments/mfr_lamb_current/lamb_current_receipt.json) retains the complete term
populations and the actual pressure/kinetic-gradient reconstruction.

[established-bounded; computational-witness] The declared resolved aperture is the full cube
`|k_i|<=1`. The four-term decomposition is exact. The resolved field alone produces a mode outside
that cube which survives the actual Leray projection:

```text
k=(-2,-2,-1),
Fourier(Leray C(v))(k)
 = i*(35/768)*(2+5*(rho+sigma))*(-1,1,0).
```

The displayed vector is perpendicular to `k`. The selected mode's null fibre is
`rho+sigma=-2/5`; on the admitted positive branch with `sigma=0`, it is nonzero. This is a
nonzero generated velocity source, not merely a gradient discarded by pressure projection or an
already-present high-frequency input. It demonstrates the feedback owed by this particular
resolved aperture; no universal impossibility of a finite reduction follows.

[established-bounded; computational-witness] The spatial receiver was declared in advance at
phase point `(pi/2,0,0)`. All oriented terms are retained there. On the preceding positive
pressure-matching branch (`sigma=0`), exact affine remainder and endpoint enclosures give:

| Initial component receiver | First component | Second component |
|---|---|---|
| `C_t` | `[-947/200,-2367/500]` | `[-6783/1000,-3391/500]` |
| Stretching contribution | `[319/200,399/250]` | `[937/250,3749/1000]` |
| Pressure contribution | `[-99/1000,-49/500]` | `[1071/250,857/200]` |
| Mixed diffusion contribution | `[5051/250,4041/200]` | `[-23/100,-229/1000]` |

The full advective and Laplacian terms are also recorded. These are instantaneous source
receivers, not positive-time bounds. Their distinct signs retain the directional content of the
current rather than promoting one term to a scalar verdict. The independent
[receiver analysis](../experiments/mfr_lamb_current/analyze_receivers.py) and its
[receipt](../experiments/mfr_lamb_current/receiver_receipt.json) verify the complete point balance,
root interval, enclosures and generated-mode factor.

[proved-derived] The prior phase-to-unit-period realization remains exact:
`u_phys=k*u(kX,k^2*t)`, `p_phys=k^2*p`, with `k=2*pi`. Vorticity carries factor `k^2`, the current
`k^3`, and each term of its temporal equation `k^5`. The physical clock and these reconstruction
factors remain separate from the scalar phase receivers.

## Verification and continuation

[established-bounded; process-audit] The focused nonlinear source/cell build passed 8,842 jobs.
The isolated complete `lake build ElementaryHolonics` passed 9,928 jobs against committed base
`dbb6d5a5` plus the four new owners and their imports. The five formal files match the verified
isolated copies; endpoint axiom prints contain only `propext`, `Classical.choice` and `Quot.sound`.
The exact full-source audit and its separate receiver analysis exited zero. Source review
corrected a draft complement selected from the full field rather than the resolved self-current,
retained the Leray projection and the selected mode's null fibre, and verified the actual nonzero
divergence of `C`. The committed native dependency repair in `dbb6d5a5` is part of the checked base;
parallel native work was preserved.

[definition] The next time-dependent candidate uses the already-owned heat and Leray source:
start with `h(t)=Heat_nu(t) u0`, carry the first nonlinear Duhamel return
`g(t)=integral_0^t Heat_nu(t-s) Leray C(h(s)) ds`, and retain `h+g` with every generated mode.
The four-term current identity exposes its residual as
`-Leray(h cross curl g + g cross curl h + g cross curl g)` after the Duhamel source is paid.
The candidate, its complete pressure and this feedback must be instantiated for the admitted
positive matching datum and estimated on a stated interval; no closed finite projection is
assumed. The existing moving-frame pressure/clock laws and complex potential/heat comparison
remain available for its receiver transport.

[open] Quantitative localized residual control, nonlinear stability, terminal continuation and
any fluid singularity remain unfinished. The present return constructs the actual nonlinear
current law, its temporal cell balance and its explicit source feedback.
