# The quartic step needs an executed domain before a Lock

Refs #73, #63; the formal lifts remain owed in #62.

[proved-derived; agent-inferred] This increment states a sufficient condition for the
**actual finite map** of the loaded symmetric quartic parametron. It does not certify
every pumped material, a global orbit, or the linear receiving bank's growing ray.
The four fixtures are mechanics regressions, with no training, curriculum, labels or
scientific generalization claim. The choice avoids the recorded failures of an
uncertified step, an authored answer counted as learning, and a located cause carried
unrepaired into another consumer. The objects are the parametron constitution,
participating wave port, phase/placement frame and clocked span; no circuit holonomy
or connection increment is introduced.

## The counterexample is retained

Write `R=D+Y⁻¹I`, `N=C+hR`, `X=N⁻¹`. The executed nonlinear branch is

```text
Nω = Cw + he − h(Ku + ∇Q(u))
u⁺ = u+hω,  w⁺=ω,  out=e−2ω/Y
Q(u)=β Σ_j |u_j|⁴/4.
```

`C,D ⪰ 0`, `β,h,Y>0` imply `N ≻ 0`, including a singular capacity.
They do not make the discrete map globally stable. Set `C=K=D=0`,
`h=Y=β=1`, `e=0`, `w=0`, with one realified node `u=(2,0)`:

```text
u⁺=(−6,0), w⁺=(−8,0), out=(16,0)
E_before=4, E_after=324
port=−64, signed integration defect=384
324−4=−64+384.
```

The correct solve and all zero numerical defects pass. The exact work account closes;
the state moves outward. A closure predicate must remain an accounting predicate.
`a_closed_quartic_balance_does_not_bound_the_executed_orbit` preserves this separator.

There is a useful bounded special case, distinct from a Lock: for this undriven
zero-capacity, zero-stiffness, zero-dissipation radial material,
`u⁺=(1−hYβ|u|²)u`. A displacement ball of radius `b` is invariant if
`hYβ b² ≤ 2`, since `|1−hYβ|u|²| ≤ 1` throughout it. The rate then obeys
`|w⁺| ≤ Yβ b³`. The origin has derivative one, so this ball does **not**
give a strict contraction or a separated half-turn Lock. The condition belongs to
this declared specialization; it is not applied to nonzero capacity or a pump.

## The actual Jacobian and scalar tangent condition

At the producing displacement let `L=K+H_β(u)`. Direct differentiation of the
executed solve gives

```text
J(u,w) = [ I−h²XL   hXC ]
         [ −hXL     XC  ].
```

The finite-step derivative contains `h²XL`; the continuous generator cannot replace it.
For scalar capacity `c≥0`, loaded resistance `r=d+Y⁻¹>0` and tangent stiffness `ell`,
let `n=c+hr`. The two-dimensional scalar block has

```text
det J=c/n,
tr J=1+c/n−h²ell/n.
1−det J=hr/n,
1−tr J+det J=h²ell/n,
1+tr J+det J=(4c+2hr−h²ell)/n.
```

The real quadratic Jury conditions therefore give strict unit-circle placement exactly
when `0<h²ell<4c+2hr`. For a **standing** pump with base stiffness `k≥0`,
strength `p>k/2` and radial saturation, the undriven sheets have
`a²=(2p−k)/β`; their two tangent stiffnesses are `2(2p−k)` and `4p`.
Thus `4ph²<4c+2hr` is sufficient for both tangent blocks under these scalar assumptions.
It is not a Half/Quarter schedule certificate and is not a finite-neighbourhood theorem.

## A finite cyclic-domain condition

The source checks proposed balls `B_Gt(c_t,r_t)` for each actual material phase.
Every metric is positive definite by exact inertia. A proposed lower bound `g_t>0`
is checked by `G_t⪰g_t I`. A proposed Euclidean radius `ε_t` is checked by
`r_t²≤g_t ε_t²`. Set `U_t=|c_u|₁`, which bounds the Euclidean centre norm.
For a radial quartic node,

```text
H_β(u)=β(|u|²I+2uuᵀ),
|H_β(u)−H_β(c_u)|₂ ≤ δ_t=3β(2U_t ε_t+ε_t²).
```

This follows by bounding both the squared-radius difference and the rank-one outer
product difference by `2U_t ε_t+ε_t²`. The same bound covers the block-diagonal
multi-node Hessian. For `A_t=[−h²X;−hX]`, the source computes the exact form
`A_tᵀG_(t+1)A_t`, bounds it by `a_t I` using its symmetric absolute row norm,
and independently checks that quadratic inequality by inertia. The derivative
departure is `A_t ΔH [I,0]`, hence

```text
(ΔJ)ᵀG_(t+1)(ΔJ) ⪯ (a_t δ_t²/g_t)G_t.
```

For a declared `s_t>0`, Young's inequality makes this sufficient test explicit:

```text
(1+s_t)J(c_t)ᵀG_(t+1)J(c_t)
  +(1+1/s_t)(a_t δ_t²/g_t)G_t ⪯ λ_t²G_t.
```

The source then executes the centre through **the generic advance**, checking
`|F_t(c_t)−c_(t+1)|²_G_(t+1)≤η_t²` and `η_t+λ_t r_t≤r_(t+1)`.
The metric balls are convex, so the derivative bound gives the stated inclusion.
Cyclic inclusion and `Π_t λ_t<1` certify a contracting period map, even when an
individual `λ_t` exceeds one. A proposed multiplier is never accepted without
these inequalities. A changed centre cannot inherit a zero residual.

The material period holds `C,D,β,Y,h` fixed and changes only stiffness and the
declared drive. Changing the other material terms is refused pending its holding law.
`PeriodicDomain::advance` charges the actual stiffness change at the held state as
pump work; `period_map` composes the admitted phases, retaining only the current point.

## Constitutive and consumer join

`holon::parametron::LoadedParametron` owns the storage, force, Hessian and mixed
step. It builds the following power-neutral Dirac structure without a capacity inverse:

```text
ω=−f_u, e_w=Cω, f_R=f_P=ω, e_u=Cf_w+e_R+e_P.
```

With `f_w=−(ω−w)/h`, `e_u=Ku+∇Q(u)`, `e_R=−Dω`, and
`e_P=e−ω/Y`, the bond is exactly the loaded solve. Its external pairing equals
`(Y/4)(|e|²−|out|²)`. The signed discrete defect is

```text
½h²ωᵀKω + Q(u+hω)−Q(u)−h∇Q(u)·ω
  −½(ω−w)ᵀC(ω−w).
```

The existing `ReferenceHolon` already implements `HolonLaw`; this increment adds
`Scheme::QuarticKickDrift` and the explicit nonlinear element relation to its
`advance` branch. Quadratic commit coefficients and midpoint/backward-Euler schemes
refuse that relation. Generic interconnection refuses to drop the nonlinear relation.

The nonlinear HNN `Phase` holds this generic law. Its actual tick consumes the
same constitutive `right` and `executed` methods, with the actual entered rate;
an approximate solve leaves its own equation residual. Its state and clock are the
actual producing displacement/rate and tick, not a rest-state surrogate. The existing
HNN chart and split bounds still govern their numerical channels independently.

`ResonatorOperands::nonlinear_lock` binds the proposed period to those actual phases
and verifies the executed solve. It refuses charted or inexact solves. `PeriodicLock`
requires a certified domain separated from zero along its declared displacement axis,
then reads a sheet and an amplitude-square enclosure. Its `advance` executes the
certified period and refuses a state outside the admitted domain.

The phase class is the declared material period index. The source navigator's full
phase/winding class, general nonlinear interconnection, whole-field Holarchy mounting,
the pump/aeon-Cycle owner consolidation, the rounded remainder-fibre envelope and the
Lean finite-domain lift remain owed. The consumed linear bank is not relabelled as
this nonlinear Lock, and no nonlinear circuit-learning result follows.

## Validation

The targeted library and test-source type-check passed. The final host build passed,
then all ten selected regressions passed: the four new mechanics tests and six gates
of the changed shared owners (wrong-solve refusal, midpoint, backward Euler, coefficient
assembly, quadratic pump work and quadratic interconnection). This is targeted
validation, not a full library-suite result. No training, generation, benchmark,
CUDA rebuild or replay of the earlier eight-host/one-CUDA milestone is part of this increment.

The positive witness is a standing pumped node with `C=I`, base `K=I`, `D=0`,
`p=3/4`, `β=1/2`, `h=Y=1`, centre `(±1,0,0,0)`. At either sheet its
effective stiffnesses are `1,3`. In `(u_x,u_y,w_x,w_y)` order use

```text
G = [ 1  0  0   0 ]
    [ 0  6  0  −2 ]
    [ 0  0  1   0 ]
    [ 0 −2  0   2 ].
```

`G⪰I`, `JᵀGJ=G/2`, `a=1`, and the exact certificate uses
`r=ε=1/100`, `λ=4/5`, `s=1/4`, `η=0`. Its Hessian variation is
`603/20000`; the robust margin is `(836391/80000000)G ≻ 0`.
The executed boundary state remains in the next domain. The sheet's displacement
amplitude-square enclosure is `[9801/10000,5101/5000]`. These are checked witness
proposals for this material, not constants inserted into the general law or a target answer.

The first positive fixture supplied an incorrect diagonal quadrature metric. The
Jacobian inequality correctly refused it; the preserved receipt reports three passes
and that failed fixture. The correction uses the exact quadrature relation
`G_y=I+2J_yᵀJ_y=[[6,−2],[−2,2]]`, not a weakened acceptance condition.
Further self-review added typed refusal of a zero timestep and an invalid Jacobian
extent; the final source and ten-test result include that guard.

Receipts, logs and source-hash projections are preserved in
[`receipts/2026-10-05-quartic-executed-domain`](receipts/2026-10-05-quartic-executed-domain).
The last build and final test receipts have `source_unchanged=true`.

| Final operation | Wall reading, ns | Child CPU reading, ns | Peak child RSS, bytes | Fixed wall guard |
|---|---|---|---|---|
| Type-check | `10813037695 = 5·1933·1118783` | `16847805000 = 2³·3·5⁴·13·86399` | `1504575488 = 2¹⁷·13·883` | `16 s = 2⁴ s` |
| Final host build | `10449972566 = 2·11·16573·28661` | `11543460000 = 2⁵·3·5⁴·192391` | `1463521280 = 2¹²·5·13·23·239` | `65 s = 5·13 s` |
| Final ten tests | `53109380 = 2²·5·2655469` | `87439000 = 2³·5³·11·7949` | `23838720 = 2¹⁴·3·5·97` | `16 s = 2⁴ s` |

Across the eight preserved native-check receipts, including builds and the rejected
metric fixture, summed child CPU is `78185591000 = 2³·5³·11·61·109·1069 ns`.
This is a sum of child readings, not an aggregate cgroup measurement or energy reading.
The existing wrapper held the common exclusive lease, checked the `8 GiB = 2³³ bytes`
prelaunch floor and enforced `4 GiB = 2³² bytes` group memory with no swap. It does not
enforce aggregate CPU or continuously enforce the system's running memory floor.
No limit was raised. The only build warning is the pre-existing unused `with_rank` method.
