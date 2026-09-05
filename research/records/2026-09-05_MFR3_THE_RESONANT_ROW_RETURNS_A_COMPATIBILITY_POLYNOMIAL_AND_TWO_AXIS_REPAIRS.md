# MFR3: the resonant row returns a compatibility polynomial and two axis repairs

**Date:** 2026-09-05. **Campaign:** the
[standing MFR goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
**Predecessor:** [the first radial pressure correction and swirl remainder](2026-09-05_MFR3_THE_AXIS_RETURNS_ITS_RADIAL_PRESSURE_JET_AND_THE_UNPAID_SWIRL_REMAINDER.md).
**Position:** MFR3 remains in progress. **Grades:** per claim.

## The radial source exposes its resonant rows

[definition] Retain the predecessor's actual Cartesian field and normalized stationary Euler
coefficients `A,B,C`. Write `s=x^2+y^2` and, as a formal radial expansion,

```text
W(s,z)=sum_m W_m(z)s^m,       Omega(s,z)=sum_m F_m(z)s^m,
V_m=-W_m'/(2(m+1)),          Gamma=W_0+beta*z,       k=alpha+2*beta.
```

[proved-derived] The divergence equation gives the displayed `V_m`. Extracting the Cauchy
products in `B,C` gives, for `m>=1`,

```text
B_m = Gamma*W_m' + [alpha+2m*beta+(1-m)W_0']W_m
      + sum_(i+j=m; i,j>=1) [W_i*W_j' - j/(i+1)*W_i'*W_j],

C_m = Gamma*F_m' + [alpha+(2m+1)beta-(m+1)W_0']F_m
      + W_m*F_0' - W_m'*F_0/(m+1)
      + sum_(i+j=m; i,j>=1) [W_i*F_j' - (j+1)/(i+1)*W_i'*F_j].

Pressure compatibility: A_(m-1)'=2m*B_m.       Swirl compatibility: C_m=0.
```

For example, in `B_m` the terms with one zero index give `Gamma*W_m'`,
`W_m*W_0'`, and `m(2beta-W_0')W_m`; the positive-index pairs give the remaining sum.
In `C_m`, the two appearances of `V_i` combine to the factor `-(j+1)/(i+1)`.
Thus each pressure row determines the next axial coefficient from earlier radial data,
and the swirl row then determines the corresponding angular coefficient, subject to resonance.
These are formal-series identities; no exchange with a convergent infinite sum is asserted.

[established-bounded; computational-witness] The
[independent coefficient audit](../experiments/mfr3_periodic_core/derive_all_order_recurrence.py)
extracts modes `1..4` directly from `B,C` with independent functions `W_j(z),F_j(z)` and checks
the displayed recurrence. Its [receipt](../experiments/mfr3_periodic_core/all_order_recurrence_receipt.json)
also checks the indicial multipliers and a limited symmetry-breaking slice. The finite audit
does not constitute a Lean theorem for every radial order.

[proved-derived] At the constructed axis, `Gamma(0)=0`, `Gamma'(0)=k`, and
`W_0'(0)=alpha+beta`. The coefficient multiplying the unknown Taylor coefficient of `z^n` is

```text
axial W_m: n*k+(2-m)alpha+(m+1)beta,
swirl F_m: n*k-m(alpha-beta).
```

At `alpha=3beta/2`, with `beta!=0`, the axial resonances occur at `m=8+7n` and
the swirl resonances at `m=7n`. The finite experiment below explicitly selects the reflection
class `W_m` odd and `F_m` even. Its first admitted resonances are `F_14,z^2` and `W_15,z^1`.
Without that restriction, `F_7,z^1` and `W_8,z^0` must also be considered.

[established-bounded; computational-witness] In the audit's stated slice containing the first
axis jets, `F_7=b*z`, and constant `W_8`, the pressure row at mode 8 gives `-2b=0`.
This tests that slice only; it neither proves reflection symmetry of every solution nor
eliminates all nonsymmetric continuations.

## The zero multiplier retains a source condition and a free fibre

[proved-derived; formal-checked] `NavierStokesSwirlDilationTransport` uses the actual reciprocal
primitive `I'=1/F_0` and constructed strain. For

```text
F_m(z)=F_0(z)^(m+1)*L(I(z)),
gamma_m=m*(alpha-beta)/(alpha+2beta),
```

it proves that the linear swirl operator is

```text
k*F_0(z)^(m+1) * [q*L'(q)-gamma_m*L(q)] at q=I(z).
```

Its mode-1 theorem identifies this with the predecessor's actual first Cartesian swirl
coefficient, including the oriented pressure-correction forcing. The general linear identity
is kernel checked; its assembly with the complete all-order nonlinear recurrence above remains
a written derivation. At the critical rate, `gamma_m=m/7`.

[proved-derived; formal-checked] `NavierStokesDilationResonance` differentiates the actual
operator `D_gamma L=q*L'-gamma*L` and proves, for smooth `L`,

```text
(D_gamma L)^(n)(0)=(n-gamma)*L^(n)(0).
```

At integer `gamma=n`, a nonzero source derivative of order `n` excludes a smooth solution.
When the source condition vanishes, adding any `c*q^n` preserves the source. The theorem
retains that entire homogeneous fibre. Away from resonance, it proves the corresponding
jet division and monomial inverse with the nonzero denominator explicit. It does not yet
construct the general smooth integral inverse or prove convergence of radial carriers.

## A circulation strength cancels the first finite obstruction

[definition] Fix `alpha=3/2`, `beta=1`, `p=5/2`, and `k=7/2`. Let

```text
G_0(z)=(1+z^2)^(-5/4),       F_0(z)=a*G_0(z),       X=a^2>0,
W_0(z)=(7/2)*G_0(z)*integral_0^z 1/G_0(t) dt-z.
```

[proved-derived; formal-checked] Multiplication of `F_0` by a nonzero constant divides its
reciprocal primitive by that constant and preserves its constructed `Gamma` and `W_0`.
Thus this parameter changes the swirl strength relative to the same axial strain. It is not
removed by merely changing the reciprocal coordinate.

[established-bounded; computational-witness] The
[fixed-strength replay](../experiments/mfr3_periodic_core/derive_radial_resonance.py)
uses the actual Taylor coefficients through `N_F(m)=30-2m` and `N_W(m)=31-2m`.
At `X=1`, all retained pressure rows through mode 14 and swirl rows through mode 13 vanish;
the remaining swirl row is `Q*z^2`, where the exact rational `Q<0` is retained in the
[receipt](../experiments/mfr3_periodic_core/resonance_receipt.json). Its coefficient of the
free `F_14,z^2` is zero. The value `Q` therefore rejects these fixed axis data in this finite
reflection class; changing that free coefficient cannot repair this row.

[established-bounded; computational-witness] The
[amplitude-family replay](../experiments/mfr3_periodic_core/derive_radial_resonance_family.py)
instead retains symbolic `X>0`, writes `F_m=a*G_m`, and includes `-X*sum G_i*G_j` in `A`.
Through mode 14, the determined coefficients are polynomials in `X` of degree at most `m`.
The sole remaining swirl forcing is `P(X)*z^2`, where `P` is degree 14 and `P(1)=Q` exactly.
All fifteen rational coefficients are in the
[family receipt](../experiments/mfr3_periodic_core/family_receipt.json). Powers `0..5` have
negative coefficients and powers `6..14` positive coefficients. Exact root isolation gives
one positive root in

```text
5625/2236 < X_* < 1366/543.
```

[proved-derived] The coefficient signs also give a short uniqueness argument. On `X>0`,
`P(X)/X^6` is strictly increasing: every negative coefficient of a negative power contributes
a positive derivative, the constant contributes zero, and every positive coefficient of a
positive power contributes a positive derivative. There can be at most one positive root.
Together with the exact endpoint signs this identifies a unique positive swirl strength
`a=sqrt(X_*)`. The coefficient attachment and signs in this argument have the finite
computational evidence just stated.

[proved-derived; formal-checked] `NavierStokesResonanceAmplitude` defines the actual polynomial
with all fifteen rational coefficients, proves its negative and positive signs at the two
rational endpoints, and applies the intermediate value theorem to obtain an interior root.
It then proves existence of `a>0` with `P(a^2)=0` and the same bounds on `a^2`. The kernel
certificate concerns this explicit polynomial. Its identification with the finite radial source
and uniqueness from the coefficient sign pattern retain the evidence scopes above.

[established-bounded; computational-witness] Continuing to mode 15 gives

```text
coefficient of W_15,z^1 in [z^1](A_14'-30B_15): 0,
coefficient of G_14,z^2 in that pressure row:   -4X.
```

Since `X>0`, pressure determines the previously free `G_14,z^2`. The next swirl row then
determines `G_15,z^0`, with affine dependence `-W_15,z^1/120` plus a known function of `X`.
The new coefficient `W_15,z^1` remains free. Recomputing every retained row after these
substitutions leaves only `C_14=P(X)z^2`; at `X_*` all retained rows through mode 15 close.
The root condition does not supply the missing higher Taylor rows or a radial convergence bound.

## An independent repair preserves the lower axis data

[established-bounded; computational-witness] The
[axis sensitivity replay](../experiments/mfr3_periodic_core/derive_radial_axis_repair.py)
keeps `a=1` and changes the axis coefficient of `z^30` by `epsilon`. The reciprocal
construction changes the coefficient of `z^31` in `W_0` by `(7/2)*(30/31)*epsilon`.
An independent exact replay gives the mode-14 swirl forcing `(Q+S*epsilon)z^2`, where

```text
S=-2196278537437716503986872527655349099000236898596401
   /4325956700507885082543750000000000000000000000000.
```

The [receipt](../experiments/mfr3_periodic_core/axis_repair_receipt.json) retains the actual
rationals `Q,S,epsilon=-Q/S`. After substitution, every retained pressure and swirl row
through mode 14 is zero, while `F_14,z^2` remains free. This branch has not undergone the
mode-15 continuation performed for the amplitude branch.

[proved-derived; formal-checked] `NavierStokesAxisJetPerturbation` constructs the actual profile

```text
F_epsilon(z)=(1+z^2)^(-5/4)*(1+epsilon*z^30/(1+2z^2)^16).
```

It proves `0<=z^30/(1+2z^2)^16<=1/32768`, smoothness, and positivity when
`epsilon>-32768`. The exact rational selected by the finite replay is a literal in this owner;
Lean proves `-32768<epsilon<0`. Every derivative below order 30 agrees with `G_0`; the
30th derivative changes by `30!*epsilon`. The perturbation ratio tends to zero at positive
infinity, so `F_epsilon/G_0` tends to one. The weight is even. Its constructed reciprocal
primitive and strain satisfy the actual axis equation. These are properties of the defined
smooth profile; the finite mode-14 source attachment remains the symbolic result above.

## What the next continuation must establish

[interpretation] The source has returned a useful distinction between nullity and
continuation. A zero indicial multiplier removes one coefficient from one equation's receiver;
it leaves both a source compatibility condition and a free coefficient. The next pressure
receiver can distinguish that coefficient. Keeping those relations reveals concrete admissible
axis choices and explains why arbitrary zeroing or division would lose the construction.

[open] Continue first with the amplitude root and the retained `W_15,z^1` fibre. The required
return is control of the next resonances and of the full radial remainder, or an explicit
obstruction that directs a replacement family. The all-order smooth inverse, radial convergence,
full three-dimensional pressure and tail, actual periodic exterior, profile time current and
transported viscosity remain obligations. No stationary global finite-energy profile, stable
nearly self-similar solution, finite-time physical singularity, or RH sign conclusion is claimed.

[proved-standard] Existing self-similar Euler exclusions constrain that
exterior. [Chae's Theorem 1.1](https://arxiv.org/html/math/0601060v2) uses integrability of the
full vorticity for every sufficiently small positive exponent. In
[Chae–Shvydkoy](https://arxiv.org/html/1201.6009), their scaling exponent is our `alpha/beta`:
Theorem 4.1 requires decaying strain and full-vorticity `L^q` control with
`q<3/(1+alpha/beta)`, hence `q<6/5` at the present rate. Their critical Theorem 3.1 uses
finite energy, the associated pressure representation, and uniform two-sided large-radius
velocity bounds. The axial data alone establish none of these three-dimensional hypotheses.

## Owners and verification

[definition] New formal owners under `formal/elementary-holonics/ElementaryHolonics/Millennium/`:
`NavierStokesDilationResonance`, `NavierStokesSwirlDilationTransport`, and
`NavierStokesAxisJetPerturbation`, together with `NavierStokesResonanceAmplitude`.
Their source identities supplement the existing Cartesian
axis and primitive owners; the Python experiments remain finite exterior calculations.

[established-bounded; process-audit] The focused swirl transport build returned 3,407 jobs,
the axis perturbation build 3,420, and the amplitude-root build 3,006, using Lean 4.33.0.
The final live umbrella returned 9,875 jobs. These are build scopes, not new theorem counts.
Decisive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The final commands, run from `formal/elementary-holonics/`, were

```sh
lake build ElementaryHolonics.Millennium.NavierStokesSwirlDilationTransport
lake build ElementaryHolonics.Millennium.NavierStokesAxisJetPerturbation
lake build ElementaryHolonics.Millennium.NavierStokesResonanceAmplitude
lake build ElementaryHolonics
```

The umbrella imports, owner map and current position are integrated. Source inspection,
exact comparison of the fifteen Lean coefficients against the family receipt, comparison of
`Q=P(1)` across both replays, the identity `Q+S*epsilon=0`, the literal epsilon comparison,
and changed-line whitespace review returned. The finite recurrence itself is not kernel checked.

[established-bounded; computational-witness] All four scripts use SymPy 1.14.0. Their checked
rows, exact parameters, rational outputs and assertion scopes are retained alongside each
script in JSON. The final amplitude replay returned exit 0 after the mode-15 junction, and its
polynomial and junction outputs agree exactly with the preceding receipt. These are exact
finite symbolic calculations; they provide no interval stability bound or infinite-series
convergence estimate. Concurrent HNP/Athena implementation remains outside this mathematical edit.

[definition] Reproduce the finite calculations from the repository root with Python and
SymPy 1.14.0:

```sh
python research/experiments/mfr3_periodic_core/derive_all_order_recurrence.py
python research/experiments/mfr3_periodic_core/derive_radial_resonance.py
python research/experiments/mfr3_periodic_core/derive_radial_resonance_family.py
python research/experiments/mfr3_periodic_core/derive_radial_axis_repair.py
```

The local runs used `/tmp/holonics-mfr3-symbolic/bin/python`; each successful invocation prints
the corresponding exact JSON receipt. The family calculation reports completed radial modes
to stderr while retaining the final JSON on stdout.

[historical; process-audit] Two superseded inline SymPy probes were found still running and
terminated after preserving their shell source under `/tmp/holonics-mfr3-retired-probe-*.txt`.
Their preliminary pressure extraction was incorrect. They returned no accepted evidence; the
retained scripts above use the actual coefficient `A_(m-1)'` and recompute the final residuals.
