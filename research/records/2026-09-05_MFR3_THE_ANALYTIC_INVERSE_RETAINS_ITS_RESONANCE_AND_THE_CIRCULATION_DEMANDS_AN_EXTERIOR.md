# MFR3: the analytic inverse retains its resonance and the circulation demands an exterior

**Date:** 2026-09-05. **Campaign:** the
[standing MFR goal](../../docs/plans/THE_MOVING_FRAME_RETURNS_THE_NULL_FIBRE_AND_THE_PHYSICAL_CONTINUATION.md).
**Predecessor:** [the compatibility polynomial and two axis repairs](2026-09-05_MFR3_THE_RESONANT_ROW_RETURNS_A_COMPATIBILITY_POLYNOMIAL_AND_TWO_AXIS_REPAIRS.md).
**Position:** MFR3 remains in progress. **Grades:** per claim.

## The scalar inverse preserves its source radius

[definition] In the critical frame `alpha=3/2`, `beta=1`, the swirl carrier at radial mode
`m` uses the actual reciprocal axial coordinate `q=I(z)` and the operator

```text
D_(m/7)L(q)=q*L'(q)-(m/7)*L(q).
```

The coordinate `q` is spatial. The normalized trajectory time used later in this record is
a separate variable and a separate source passage.

[proved-derived; formal-checked] `NavierStokesAnalyticDilationInverse` proves that for integers
`m,n>=0`,

```text
7*n!=m  implies  |n-m/7|>=1/7.
```

For a complex coefficient sequence `a_n`, it defines

```text
b_n = a_n/(n-m/7)  when 7*n!=m;        b_n=0 when 7*n=m,
r_n = a_n         when 7*n=m;         r_n=0 otherwise,
L(q)=sum_n b_n*q^n.
```

It proves `|b_n|<=7|a_n|`. If `sum |a_n| R^n` converges, the actual series defining `L`
converges on `|q|<=R`, is holomorphic on `|q|<R`, and obeys

```text
|L(q)| <= 7*sum_n |a_n| R^n,
D_(m/7)L(q)=sum_n (a_n-r_n)q^n.
```

The proof obtains the derivative of the convergent sum from uniform holomorphic bounds and
then checks the actual differentiated monomials. It neither assumes the inverse equation nor
replaces its residual with a coefficient count. The bound is uniform in radial mode `m` for
this scalar operator.

[proved-derived; formal-checked] If the resonant source coefficient vanishes, `L` solves the
complete scalar source equation. At `m=7j`, every `L+c*q^j` returns the same source residual.
The zero coefficient in the displayed definition selects one representative of that fibre;
the full homogeneous freedom remains in the theorem.

[proved-derived; formal-checked] The owner restricts the constructed complex inverse to the
real axis, derives its real derivative, and composes it with the existing reciprocal-axis
construction. Given a positive `C2` axial profile `F`, set

```text
K(z)=F(z)^(m+1)*L(I(z)),      Gamma=(7/2)*F*I,      W_0=Gamma-z.
```

On the admitted axial interval `|I(z)|<R`, its actual linear swirl coefficient becomes
`(7/2)*F(z)^(m+1)*sum a_n I(z)^n` when compatibility holds. Thus the inverse reaches the
real fluid carrier through an actual derivative theorem.

[open] This closes the scalar analytic inverse at its declared source radius. It does not
establish the required coefficient bounds for every nonlinear radial source, control the
mode-dependent factors `F^(m+1)`, or prove convergence of the two-variable fluid expansion.
Those source estimates remain necessary; the uniform scalar divisor bound alone does not
absorb their derivatives and products.

## The retained axial coefficient has an actual homogeneous carrier

[proved-derived; formal-checked] `NavierStokesSwirlDilationTransport` now also derives the
axial operator at radial mode `m+2`, using the same carrier `H=F^(m+1)*M(I)`:

```text
Gamma*H' + [alpha+2(m+2)beta-(m+1)W_0']H
 = (alpha+2beta)*F^(m+1)*D_eta M(I),

eta=[m(alpha-beta)-3beta]/(alpha+2beta).
```

This follows from the already constructed swirl operator by retaining its additional
`3beta*H` term. At critical radial mode 15 it gives the actual homogeneous profile

```text
dW_15(z)=F(z)^14*I(z).
```

Its pressure-linear operator is zero at every `z`. When `F(0)=1`, its actual derivative at
zero is one. The surviving coefficient `Y=W_15[z^1]` therefore has a constructed axial
variation, extending beyond the single Taylor face that first exposed it.

## The next swirl resonance responds to that coefficient

[proved-derived] The reflection class has its next swirl resonance at `m=28`, axial power
`z^4`. To find how it reads `Y`, differentiate the actual coefficient equations with respect
to `Y`. Write variations `dW,dG,dV` with `F=aG`, `X=a^2`, and
`dV_m=-dW_m'/(2(m+1))`. All variations below mode 15 vanish. A product contributing to mode
28 cannot contain two factors starting at mode 15; the corresponding pressure coefficient is
mode 27 and has the same property. Hence the source dependence on `Y` is affine through this
aperture. Every varied product needs only unvaried radial modes `0..13`.

[established-bounded; computational-witness] The
[sensitivity script](../experiments/mfr3_periodic_core/derive_next_resonance_sensitivity.py)
obtains those baseline modes from the accepted amplitude-family construction and propagates
the unit variation `dW_15=G_0^14*I_0`. It retains the complete Taylor dependency budgets

```text
dN_W(m)=61-2m,       dN_G(m)=60-2m,       m=15..28.
```

It differentiates the actual `A,B,C` Cauchy products, solves the nonresonant rows, and
recomputes every final linearized residual. Pressure rows 15–28 and swirl rows 15–27 are zero.
The complete remaining row is

```text
dC_28(z)=R(X)*z^4,
```

independent of the free coefficient `dG_28,z^4`. The exact degree-13 polynomial `R`, its
rational coefficients and the remainder modulo the prior polynomial `P` are retained in the
[receipt](../experiments/mfr3_periodic_core/next_resonance_sensitivity_receipt.json).
Its coefficients at powers 0–4 are negative; powers 5–13 are positive. The denominator
reported outside the rational coefficient polynomial is one. The calculation is a first
variation of a finite jet construction, not the full mode-28 source value.

[proved-derived; formal-checked] `NavierStokesNextResonanceSensitivity` contains those explicit
rational coefficients. Write `R(X)=R_+(X)-R_-(X)`, where each polynomial has nonnegative
coefficients. For the prior amplitude-root bracket `[l,u]=[5625/2236,1366/543]`, Lean proves

```text
0 < R_+(l)-R_-(u) <= R(X)     for every l<=X<=u.
```

It composes this with the predecessor's root theorem to obtain `P(X_*)=0` and `R(X_*)>0`.
For every returned constant forcing `Q_28`, the affine equation
`Q_28+R(X_*)Y=0` has the unique coefficient `Y=-Q_28/R(X_*)`. Positivity makes the surviving
coefficient effective at the next receiver. It does not alter the preceding `P(X)` row.

[open] The constant part `Q_28` of the full mode-28 source has not been computed in this
return, and the complete radial jet through that order has not been reconstructed. The
sensitivity certificate supplies the nonzero divisor needed for that next construction.
It does not assert that the full source is already zero.

## Circulation constrains the exterior of the local core

[proved-derived; formal-checked] `NavierStokesSwirlCirculation` composes the actual Cartesian
axisymmetric owner. With `p=(s,z)`, where `s=x^2+y^2`, define

```text
ell(p)=s*Omega(p),
b(p)=(2s(V(p)+beta), W(p)+beta*z),
delta=alpha-beta.
```

The returned derivative identity is

```text
d ell(p)[b(p)] + delta*ell(p)=s*C(p),
```

where `C` is the actual normalized swirl momentum coefficient. No radius division occurs at
`s=0`. Along an admitted differentiable trajectory `p'=b(p)`, the actual composed carrier
satisfies `ell'=f-delta*ell`, with `f(t)=s(t)C(p(t))`. At a stationary off-axis meridional
point with nonzero swirl and zero residual, this already forces `alpha=beta`.

[proved-derived; formal-checked] `NavierStokesSwirlHistory` retains the incoming carrier on
an actual finite interval `[t,0]`, with `t<=0`. If the displayed differential law holds there,
`|f|<=epsilon` there, and `|ell(t)|<=M`, then

```text
|ell(0)| <= exp(delta*t)*M
             + (epsilon/delta)*(1-exp(delta*t)),       delta!=0.
```

The proof differentiates `exp(delta*t)*(ell-epsilon/delta)` and its opposite-sign version.
Its finite-interval hypotheses do not require a complete past. For `delta>0`, a uniformly
bounded complete past makes the incoming term vanish and gives

```text
delta*|ell(0)| <= epsilon.
```

The compact-history theorem obtains `M` from the actual continuous angular-momentum function
on a compact set containing the whole backward trajectory. Exact zero swirl residual then
forces `ell(0)=0`; nonzero circulation excludes such a compact exact history.

[interpretation] A local zero swirl residual can coexist with nonzero circulation because
its finite history retains an incoming carrier. The exterior question is where that carrier
travels and whether the assumed past exists. Erasing the incoming term before proving a
bounded complete past would change the continuation problem. For the current critical rates,
the residual threshold is `|ell(0)|/2` on such a trapped complete history.

[proved-standard] [Constantin–Ignatova–Vicol, v3](https://arxiv.org/html/2602.17570v3#S4.SS3),
Theorem 4.5, excludes nontrivial global axisymmetric `C2` Euler similarity profiles with
physical exponent `gamma<1/2` under its conditions (3.5) and (3.8). Those include global
sublinearity and specified velocity/vorticity/gradient bounds. The target rates correspond
to `gamma=2/5`. The theorem constrains a global completion; local axis jets do not establish
its global hypotheses.

[proved-derived] In that convention `U_paper=(2/5)U_here` and the physical similarity drift
is `(2/5)(y+U_here)`. The local meridional quadratic form of `y+U_here`, at the current
axis jet, is `-r^2/4+7z^2/2`. Thus it has a contracting radial direction, regardless of swirl
strength. It fails a local nonnegative outgoing quadratic inequality. The finite axis
construction remains local; the new formal history theorem states explicitly which additional
past and residual assumptions would exclude an exterior.

[proved-derived] For a globally `C1` Cartesian field with `U=o(|x|)` uniformly and `beta>0`,
outside a large ball `inner(x,beta*x+U)>=beta*|x|^2/2`. Backward trajectories remain in a
ball; local ODE continuation on that compact set supplies a complete past. Its meridional
image is compact. Thus exact stationary swirl with `alpha>beta` vanishes by the history
theorem. This globalization is written analysis; Lean currently takes the trajectory and
its compact containment as hypotheses.

[open] The next attempt must retain the actual exterior/time dependence or return the
obstruction preventing it. A globally sublinear stationary axisymmetric completion carrying
this swirl is not an admissible default. In a time-dependent or viscous profile, the actual
profile time current, diffusion, and transported domain must enter the source balance; the
stationary `C` identity alone does not supply those terms or a stability estimate.

## Current continuation and verification

[open] Continue with the full constant forcing at the next resonant row and its now-certified
nonzero sensitivity. Preserve every following free coefficient and source compatibility row.
Use the analytic inverse to establish bounds on the actual nonlinear sources and radial
remainder, and construct a lawful exterior carrying its circulation and time current. No
radially convergent concentrating solution, stability margin, finite-time physical singularity,
or RH sign conclusion has returned. MFR3 and the standing goal remain active.

[definition] New formal owners are `NavierStokesAnalyticDilationInverse`,
`NavierStokesNextResonanceSensitivity`, `NavierStokesSwirlCirculation`, and
`NavierStokesSwirlHistory`. The existing `NavierStokesSwirlDilationTransport` now also owns
the axial conjugation and the normalized mode-15 homogeneous profile.

[established-bounded; process-audit] Lean 4.33.0 returned the final focused checks and live
umbrella. Commands from `formal/elementary-holonics/` were

```sh
lake build ElementaryHolonics.Millennium.NavierStokesAnalyticDilationInverse
lake build ElementaryHolonics.Millennium.NavierStokesNextResonanceSensitivity
lake build ElementaryHolonics.Millennium.NavierStokesSwirlHistory
lake build ElementaryHolonics
```

The focused closures returned 3,429, 3,007 and 3,405 jobs respectively; the umbrella returned
9,879. These are build scopes, not theorem counts. The circulation owner and updated axial
transport owner are in those dependency closures. Decisive axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The finite-history theorem requires derivative
and source bounds only on its displayed finite interval; the complete-past theorem is separate.

[established-bounded; process-audit] Direct comparison matched the final recurrence's
coefficient map and row receipts, all fourteen rational coefficients in the sensitivity Lean
owner, and the independently calculated positive interval bound. Source review and changed-line
whitespace review returned. The umbrella imports, owner map, roadmap and current position are
integrated. The finite radial recurrence and global ODE-containment argument retain their
separate computational and written scopes.

[established-bounded; computational-witness] The final sensitivity recurrence ran under
SymPy 1.14.0 and exited 0. The final rational interval bound was independently calculated
from the completed coefficient map; the expensive recurrence was not repeated for that
output-only addition. Reproduction from the repository root is

```sh
python research/experiments/mfr3_periodic_core/derive_next_resonance_sensitivity.py
```

The script prints mode progress to stderr and the exact JSON receipt to stdout. It reuses
the accepted amplitude-family source and does not read an evaluation target to manufacture
the sensitivity. Concurrent HNP/Athena runtime sources remain outside this mathematical edit.
