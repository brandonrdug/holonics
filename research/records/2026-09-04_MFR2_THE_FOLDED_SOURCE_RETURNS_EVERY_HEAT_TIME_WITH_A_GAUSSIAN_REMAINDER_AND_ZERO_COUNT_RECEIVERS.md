# MFR2: the folded source returns every heat time with a Gaussian remainder and zero-count receivers

**Date:** 2026-09-04. **Campaign:** MFR2 under the
[standing MFR goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
**Truth status:** per claim. **Evidence:** Lean 4.33.0, focused target and live umbrella builds;
decisive theorem dependencies are `propext`, `Classical.choice`, `Quot.sound`.

## The returned source

[definition] The standard flow is the existing `CriticalChart.Hstd`, with
`Hstd t z = (1/8) * heatE (-t/4) xi (1/2+i*z/2)`. For positive integer `m`, set

```text
phi_m(u) = (2*pi^2*m^4*exp(9u)-3*pi*m^2*exp(5u)) exp(-pi*m^2*exp(4u)).
```

The implementation uses `m=n+1`, `n : Nat`, so the partial population `range N` contains the
positive integers `1,...,N` and its first omitted integer is `N+1`.

[proved-derived; formal-checked] `FoldedKernel.Hstd_eq_integral_positiveHalfLine` first returns
the full standard kernel through theta reflection as an absolutely integrable cosine integral
on `Ioi 0`, for every real `t` and every complex `z`. The reflection acts on the assembled
kernel before the new integer decomposition.

[proved-derived; formal-checked] `FoldedSource.hasSum_foldedPhiTerm` reconstructs the actual
`PhiStd` from the positive-index theta population. `hasSum_foldedSourceTerm` carries that sum
through its full complex oscillatory receiver. Absolute integrability of every half-line event
and dominated convergence then give

```text
Hstd(t,z) = sum_(m>=1) integral_0^infinity exp(t*u^2) phi_m(u) cos(z*u) du.
```

The endpoint is `hasSum_integral_foldedSourceTerm`, not a newly defined proxy for `Hstd`.

## The complete omitted population

[proved-derived; formal-checked] For `u>=0`, `|t|<=T`, `|Im z|<=R`, `T,R>=0`, the norm of
the `m`-th flowed event is bounded by

```text
[2*pi^2*m^4*exp(-pi*m^2/2)] * exp(T*u^2+(R+9)*u-pi*exp(4u)/2).
```

`FoldedSourceBounds` proves positivity of `phi_m` on the half-line, this pointwise bound,
summability of its integer coefficient, and integrability of its spatial majorant. The latter
uses the standing quartic domination and Gaussian integrability, with an explicit polynomial
lower bound for the double exponential.

[proved-derived; formal-checked] Let `S_N(t,z)` be the sum of the first `N` event integrals.
The quarter-Gaussian constant and aperture integral are

```text
Cq = sum_(m>=1) 2*pi^2*m^4*exp(-pi*m^2/4),
I(T,R) = integral_0^infinity exp(T*u^2+(R+9)*u-pi*exp(4u)/2) du.
```

Both are finite in the stated scope. `FoldedSourceTail.norm_Hstd_sub_partialSource_le` proves

```text
norm(Hstd(t,z)-S_N(t,z)) <= Cq * I(T,R) * exp(-pi*(N+1)^2/4).
```

The exact tail is a shifted infinite population, not an asserted error sample. The bound tends
to zero and is uniform on the whole set `|t|<=T`, `|Im z|<=R`; no bound on `Re z` is needed.
The owner also returns fixed-time local uniform convergence throughout the complex plane.

## Derivatives and retained counts

[proved-derived; formal-checked] `FoldedSourceDerivative` differentiates each actual event
integral. Its integrand derivative is

```text
-u * exp(t*u^2) * phi_m(u) * sin(z*u).
```

The extra factor `u` is absorbed by increasing the height parameter in the same majorant;
the complex neighbourhood and almost-everywhere hypotheses of dominated differentiation are
proved. `hasDerivAt_integral_foldedSourceTerm` therefore gives the first complex derivative at
every `z`, for every real `t` and positive integer event.

[proved-derived; formal-checked] `FoldedSourceZeros` composes those derivatives with the finite
population and the existing `HurwitzLine` / `RectangleCountStable` owners. It proves:

- every finite `S_N(t,.)` is entire;
- its derivatives converge uniformly to the derivative of the actual `Hstd(t,.)` on compact sets;
- on any nondegenerate rectangle whose boundary is zero-free for `Hstd(t,.)`, the finite source
  approximations eventually have zero-free boundaries and the same interior divisor count,
  with multiplicity, as `Hstd(t,.)`.

The count comparison follows convergence of the logarithmic-derivative contour integrals and
their integer-valued argument-principle receiver. Its cutoff is eventual. No numerical cutoff,
computed zero census or on-axis placement is inferred from that theorem.

## Why the earlier divergence theorem remains valid

[proved-derived; source-inspected] `FlowedExplicitFormula.not_integrable_flowedTerm` concerns
each original event integrated on the whole real line in the positive standard-time direction.
It remains unchanged. Those event tails diverge before the collective theta cancellation.
The new construction reflects the assembled kernel first and then decomposes the positive
half-line. It does not exchange a divergent old integral and sum or identify the new term with
the old whole-line event integral.

[open] The arithmetic sign `Lambda_DN<=0` is still unproved. Positivity of the real half-line
theta terms is not positivity of their full complex oscillatory receiver or of Weil's form.
The returned source family, remainder and zero-count passage are material for that investigation.

## Verification and continuation

[established-bounded; process-audit] From `formal/elementary-holonics/`:

```sh
lake build ElementaryHolonics.RH.FoldedSourceZeros
lake build ElementaryHolonics
```

The focused target returned 8,841 jobs and the live umbrella 9,853. The six new owners' decisive
axiom prints contain only the three standard axioms; source and changed-line review returned.
`FoldedSourceZeros` is registered in the umbrella and all owners are linked in the architecture
map. Intermediate focused source, tail and derivative builds also returned; no native/Rust
behavior was changed by this work.

[definition] MFR2 is complete at the scope above. MFR3 is the next ordered construction:
source-specific fluid concentration conditions and exclusions. MFR4's actual profile/stability
return and MFR5's arithmetic sign remain later research obligations under the standing goal.
