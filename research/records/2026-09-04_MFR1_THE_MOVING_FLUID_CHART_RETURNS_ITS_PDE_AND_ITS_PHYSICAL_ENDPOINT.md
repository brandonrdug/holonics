# MFR1: the moving fluid chart returns its PDE and its physical endpoint

**Date:** 2026-09-04. **Campaign:** MFR1, under Brandon's activation of the
[standing MFR goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
**Truth status:** per claim. **Verification:** Lean 4.33.0; the focused endpoint target and live
umbrella returned. The concurrent HNP changes remain owned by that session.

## The source and the chart

[definition] The source is the existing `OpenSmoothSolutionOn` / `OpenPeriodicSolutionOn`,
including its real momentum equation, pressure, force, incompressibility, initial data and
joint smoothness on `Ico 0 T`. Let `c(s)` be the moving centre, `ell(s)` the spatial length,
`q(s)` the multiplying normalizer, and `theta(s)` the physical clock. The returned fields are

```text
U(y,s) = q(s) u(c(s)+ell(s)y, theta(s)),
P(y,s) = q(s)^2 p(c(s)+ell(s)y, theta(s)).
```

`q=1/a` in the design's physical-amplitude notation. The return selects the varying scalar
length/amplitude chart with arbitrary differentiable centre motion. General anisotropic matrix
deformation remains a possible source-specific extension when an ansatz requires it.

## Returned mathematical laws

[proved-derived; formal-checked] `NavierStokesRescalingSpace.lean` composes the existing
`NavierStokesParabolicRebase` with translation and an independent amplitude. It proves actual
Fréchet derivative, divergence, advection, pressure-gradient and Laplacian transport. The
Laplacian statement uses the source's `C²` spatial regularity. The inverse statements require
nonzero scale and normalizer. Unit periodicity becomes the literal period
`ell⁻¹ • EuclideanSpace.single i 1`, rather than an unchanged unit-torus assertion.

[proved-derived; formal-checked] `NavierStokesDynamicRescaling.lean` derives the moving time
jet from the joint source derivative, keeping the spatial and time ports. At a strict interior
source time, with nonzero `q,ell` and turnover clock `theta'=ell*q`, the source momentum gives

```text
U_s + D_y U[U]
  = (nu*q/ell) Delta_y U - grad_y P
    + (ell'/ell) D_y U[y] + ell^-1 D_y U[c'] + (q'/q) U
    + ell*q^2 f(c+ell*y,theta).
```

No field assumes this normalized momentum equation. `OpenSmoothSolutionOn.rescaled_momentum`
reads the original equation and the actual chain-rule identities. Separate theorems return
incompressibility, the initial-data value when the clock reads zero, pressure and velocity
periods, inverse reconstruction, and the zero-normalizer face. The momentum theorem is an
interior statement; no unproved one-sided derivative conversion at the initial boundary is
included in its grade.

[proved-derived; formal-checked] `NavierStokesRescalingClock.lean` constructs

```text
theta(s) = t0 + (B/k)(1-exp(-k*s)),
theta'(s) = B exp(-k*s),
theta(infinity) = t0+B/k.
```

For `B,k>0`, the derivative and remaining time are positive; `s>=0` maps to
`[t0,t0+B/k)` and `s>0` is strictly past `t0`. The exponential ratio `exp(k*s)` diverges.
The general receiver theorem proves that a vanishing scalar whose scaled receiver has an
eventual positive norm lower bound is incompatible with receiver continuity at the limiting
state. It retains the actual state path and lower bound.

[proved-derived; formal-checked] `NavierStokesRescalingEndpoint.lean` binds that criterion
to the actual compatible-extension owner. For the source solution, assume

```text
c(s) -> x*,    ell(s) -> 0,    theta(s) -> T,
eventually 0 < theta(s) < T.
```

Then either of the following separately suffices to prove `solution.IsMaximal`:

1. `q(s)->0` and an eventual bound `delta <= norm(U(y,s))`, for a fixed `y` and `delta>0`;
2. `q(s)*ell(s)->0` and an eventual bound `delta <= norm(D_y U(y,s))`.

The proof does not silently demand the extending fields be identical after `T`.
It takes any `CompatibleOpenPeriodicExtension`, uses exact prior velocity agreement and the
extension's smoothness at `(x*,T)`, and obtains a contradiction from the retained normalized
receiver. The derivative case uses the full spatial derivative as the joint derivative
restricted to the spatial port. The sampled physical point converges to a finite point, so
escape to infinity is not substituted for a local continuation defect.

## Scope and next construction

[conditional] These endpoint theorems are sufficient conditions for a supplied source solution.
Neither a profile satisfying the nonzero lower bound nor a stable concentrating solution has
been constructed. They give the exact analytic consequence a later ansatz/stability argument
must supply, without a certificate containing a Millennium conclusion.

[definition] MFR1's selected scalar moving-frame/endpoint construction is complete. The
independent folded-source work MFR2 is next. MFR3--MFR5 still owe actual source-specific
concentration constraints, residual/stability estimates and arithmetic-sign returns. The
recorded formula for variable viscosity is a coordinate consequence; the physical source
retains its original constant `nu`.

## Owners and verification

[established-bounded; process-audit] Commands, from `formal/elementary-holonics/`:

```sh
lake build ElementaryHolonics.Millennium.NavierStokesRescalingClock
lake build ElementaryHolonics.Millennium.NavierStokesDynamicRescaling
lake build ElementaryHolonics.Millennium.NavierStokesRescalingEndpoint
lake build ElementaryHolonics
```

The clock target returned 2,127 jobs; the dynamic target 8,724; the endpoint 8,726; and the live
umbrella 9,847. These are build scopes, not counts of new theorems. The new endpoint import is
registered in `ElementaryHolonics.lean`; the four owners are linked in the architecture map.
Decisive `#print axioms` outputs contain only `propext`, `Classical.choice`, `Quot.sound`.
The source and changed-line whitespace review returned. No Rust or native behavior is changed
by this construction.

[definition] Sources, all below `formal/elementary-holonics/ElementaryHolonics/Millennium/`:
`NavierStokesRescalingSpace.lean`, `NavierStokesDynamicRescaling.lean`,
`NavierStokesRescalingClock.lean`, `NavierStokesRescalingEndpoint.lean`. Existing imports provide
the formal dependencies; no new axiom or assumed profile equation was introduced.
