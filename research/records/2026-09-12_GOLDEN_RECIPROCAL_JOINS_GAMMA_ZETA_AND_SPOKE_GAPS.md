# The golden reciprocal joins Gamma, zeta and spoke gaps

[historical] Brandon's September 12 frontier-review request asks whether the reciprocal identity
`phi=(phi-1)^-1` relates to deeper zeta mathematics, and asks about the gap statistics of the
revised spoke/ring construction. This return keeps the ideal scaling law, the measured candidate
geometry, and the arithmetic special functions as explicit source maps.

## 1. The reciprocal identity closes functional arguments

[proved-derived] Put `x=phi^-1`, with `phi=(1+sqrt5)/2`. Then

`x+x^2=1`, `1-x=x^2`, `x/(1+x)=x^2`, `ln x=-ln phi`.

Thus complementation, an elementary fractional-linear map and squaring reach the same argument.
This is an actual reason special-function relations simplify at this value; it is more specific
than the presence of a named constant in two formulas.

[proved-standard] For 0<x<1, the dilogarithm identities are

`Li2(x)+Li2(1-x)=zeta(2)-ln x ln(1-x)`,

`Li2(x)+Li2(-x)=Li2(x^2)/2`,

`Li2(x/(1+x))=-Li2(-x)-(ln(1+x))^2/2`.

The second follows by separating even terms of the absolutely convergent defining series;
the reflection and fractional-linear identities have this real branch/domain in
[DLMF 25.12](https://dlmf.nist.gov/25.12).

[proved-derived] Write A=Li2(x), B=Li2(x^2), L=ln(phi). The three identities give
`A+B=zeta(2)-2L^2` and `A=3B/2+L^2/2`. Solving this two-equation system yields

`Li2(phi^-1)=3 zeta(2)/5-(ln phi)^2`,

`Li2(phi^-2)=2 zeta(2)/5-(ln phi)^2`.

These involve the ordinary Riemann zeta value zeta(2)=pi^2/6. The quadratic constraint makes the
argument orbit close; the defining series and functional equations supply the analytic relation.

## 2. Fifth-angle geometry gives a Gamma quotient

[proved-standard] Euler's reflection formula states
`Gamma(a)Gamma(1-a)=pi/sin(pi a)` away from its poles.
[DLMF 5.5.3](https://dlmf.nist.gov/5.5.E3).

[proved-derived] Applying it at 1/5 and 2/5 gives

`Gamma(1/5)Gamma(4/5) / (Gamma(2/5)Gamma(3/5))`
`=sin(2pi/5)/sin(pi/5)=2cos(pi/5)=phi`.

The existing `Millennium/Turn.lean::theGoldenRatioIsTwiceACosineOfTheFifthTurn` is the formal
trigonometric owner. This Gamma quotient follows from the standard reflection theorem; it is
recorded as a derivation here, not claimed as a newly added Lean theorem.

## 3. Hurwitz zeta and the arithmetic character modulo five

[proved-standard] For a>0, Hurwitz zeta satisfies
`zeta'(0,a)=ln Gamma(a)-ln(2pi)/2`, with the derivative taken in the first argument.
[DLMF 25.11.18](https://dlmf.nist.gov/25.11.E18).

[proved-derived] Taking the logarithm of the Gamma quotient cancels the constant terms and gives

`ln phi=zeta'(0,1/5)+zeta'(0,4/5)-zeta'(0,2/5)-zeta'(0,3/5)`.

Define chi5 to be 0 at multiples of five, +1 on residues 1,4 and -1 on residues 2,3. This is
already the project character in `Millennium/FiveTheta.lean`; the existing `FiveWitness` twists
a separate Hecke coefficient source by it and is not identical to the scalar L-series below.

[proved-derived] On Re(s)>1, splitting the scalar Dirichlet series into residue classes gives

`L(s,chi5)=5^-s [zeta(s,1/5)-zeta(s,2/5)-zeta(s,3/5)+zeta(s,4/5)]`.

Analytic continuation supplies the same identity near zero. The bracket vanishes at zero:
`zeta(0,a)=1/2-a` and the four weighted constants and residues both sum to zero. Differentiating
therefore gives `L'(0,chi5)=ln phi` without an additional ln5 term.
The residue-class construction is the standard finite-character relation in
[DLMF 25.15](https://dlmf.nist.gov/25.15).

[proved-standard] The arithmetic value is
`L(1,chi5)=2 ln(phi)/sqrt5`. Phi is a fundamental unit of Q(sqrt5), with norm -1 and regulator
ln(phi). The real quadratic class-number formula gives this value for its class number one.
[Elkies's analytic number theory notes](https://abel.math.harvard.edu/~elkies/M229.22/index.html)
state the value and the fundamental-unit/fifth-angle connection explicitly.

[proved-standard] The Dedekind zeta of that quadratic field factors as
`zeta_Q(sqrt5)(s)=zeta(s)L(s,chi5)` for Re(s)>1, and then meromorphically. Split, inert and
ramified prime factors give the equality locally. Consequently its residue at one is
`2 ln(phi)/sqrt5`. This gives a direct arithmetic source joining the golden unit and ordinary
Riemann zeta. It does not identify a finite polygon's spectrum with the Riemann zero source.

## 4. The same golden generator has its own dynamical zeta

[definition] For the finite allowed-word generator `B=[[1,1],[1,0]]`, let N_n=trace(B^n).
It counts closed length-n walks with a chosen starting position, including repetitions. Define
`zeta_B(z)=exp(sum_(n>=1) N_n z^n/n)` for |z|<1/phi.

[proved-derived] B has eigenvalues phi and psi=-1/phi, so
`N_n=phi^n+psi^n`. Expanding the two convergent logarithms gives

`zeta_B(z)=1/[(1-phi z)(1-psi z)]=1/(1-z-z^2)`.

Its first positive pole is 1/phi, the same growth rate that gives the matched code entropy
ln(phi). This is a dynamical zeta of an explicitly supplied finite-state source. The numerator,
clock variable, primitive cycles and convergence domain distinguish it from the Riemann and
Dedekind zeta functions. Their reusable pattern is a generator's multiplicities organized by
its actual product or recurrence law.

## 5. The spoke gaps have a scaling law with angular modulation

[definition] In the existing illustration, a regular n-gon follows the simultaneous pursuit
update with t=0.15. Its complex multiplier is `mu=(1-t)+t exp(2pi i/n)=q exp(i alpha)`.
For initial circumradius R, let rho_n(theta) be the radial profile of the unit regular polygon.
The fixed-ray radius after k updates is

`r_k(theta)=R q^k rho_n(theta-k alpha)`.

[proved-derived] Subtracting consecutive layers gives

`g_k(theta)=R q^k f(theta-k alpha)`,
`f(beta)=rho_n(beta)-q rho_n(beta-alpha)`.

The profile is periodic with the polygon's angular period. The new polygon is contained in the
preceding convex polygon, so f is nonnegative. Particular rays can meet a common boundary point;
strict positivity belongs to the measured finite cases, not every possible angle. The gaps are
a geometric envelope multiplied by the sampled rotating profile. Log radius alone cannot remove
that angular modulation.

[established-bounded; computational-witness] The
[spoke-gap experiment](../experiments/spoke_gap_zeta/README.md) measures all 101 layers and eight
fixed ruler rays for n=8 and n=12, using 80-digit mpmath ray/segment geometry. Each case has 800
positive gaps in the declared 100-step window. The n=8 contraction is approximately 0.961931510;
the n=12 contraction is approximately 0.982769799. After division by q^k, gap coefficients of
variation remain approximately 0.573289 and 0.576059. Their variation is therefore not merely
the shrinking radial envelope.

[established-bounded; computational-witness] For n=8, the normalized gaps range from about
0.00110638 to 0.0746878. The sum along each ray is 0.9797908938559263, equal to r_0-r_100 at the
declared precision. The eight series agree because of the candidate's actual symmetry. For
n=12 the different ray orbits retain their distinct radii. These are measurements of the
constructed model, not statistics extracted from the unknown photographed author's drawing.

[established-bounded; computational-witness] Pooled lag-one correlations use the 792 actual
within-spoke pairs `(j,k)->(j,k+1)`, never concatenation edges from the end of one ray to the
start of another. Raw/normalized values are about 0.809456/0.398159 for n=8 and
0.622050/0.370374 for n=12. The raw series is nonstationary; the normalized result declares
the common envelope removal. The numerical receipt retains the pair means and the full data.

## 6. The natural gap zeta and its Gamma transform

[definition] For ideal dimensionless gaps `g_k=g_0 q^k`, 0<q<1, define
`Z_gap(s)=sum_(k>=0) g_k^s` for Re(s)>0, using the real logarithm of each positive gap.

[proved-derived] The geometric series gives
`Z_gap(s)=g_0^s/(1-q^s)`. Its finite-N remainder is
`g_0^s q^(Ns)/(1-q^s)`. The denominator's complex zeros are the logarithmic-scale frequencies
`s=2pi i j/ln q`. This ideal comparison does not identify the measured polygon gaps, whose
angular profile is nonconstant. In particular calibrating g_0 from the first measured gap
and extrapolating geometrically overestimates the total radial span in the measured examples.

[proved-derived] For the polygon source, write U_alpha h(theta)=h(theta-alpha). For Re(s)>0,
the bounded profile f^s and q<1 give the uniformly convergent operator expression

(at a zero profile value use the continuous extension `0^s=0` on this domain)

`Z_polygon(s,theta)=R^s (I-q^s U_alpha)^-1 [f^s](theta)`.

This is the Neumann series of the actual angular transport. A Fourier mode of angular order
mn has multiplier exp(-imn alpha), so a finite Fourier representation has denominators
`1-q^s exp(-imn alpha)`. Extending this to an infinite Fourier/meromorphic expansion requires
its convergence and continuation arguments; the finite ray sample does not supply them.

[proved-derived] The geometric bound `0<=g_k<=R q^k` gives, for real sigma>0, a tail at most
`R^sigma q^(N sigma)/(1-q^sigma)`. At sigma=1, telescoping improves the full remaining gap
sum to exactly r_N because the nested radii tend to zero. Numerical values in the experiment
are high-precision witnesses, not outward-rounded evaluations of this analytic bound.

[proved-derived] For positive dimensionless gaps with sum g_k^sigma finite, set
`H(t)=sum_k exp(-t/g_k)`. The substitution u=t/g_k and absolute convergence give

`integral_0^infinity t^(s-1) H(t) dt = Gamma(s) Z_gap(s)`

on the domain Re(s)>0 where that gap power sum converges. Gamma is the Mellin factor converting
the decaying transport family into its gap spectrum. This is the source map that connects the
spoke question to Gamma and zeta constructions; it does not require an assumed random process.

## Verification and reusable consequences

[established-bounded; computational-witness] `verify_special_values.py` evaluates the Gamma
quotient, Hurwitz derivative combination, the digamma expression for L(1,chi5), and both
dilogarithm identities at 80-digit precision. Residuals are approximately 1e-81. Its truncated
dynamical-zeta sum at z=0.1 agrees to about 1.4e-66 with the rational expression and has its
displayed geometric tail bound. These numerical agreements are not kernel proofs or rigorous
outward intervals. The exact derivations and cited analytic hypotheses above carry the claims.

[definition] This return exemplifies the consolidated method: recover the quadratic relation,
carry its argument transformations into established special functions, derive the source's
appropriate zeta and tail, and keep the actual generator/receiver available to the solver.
Finite operator powers and their recurrences use the common exact matrix/polynomial owner;
an analytic source additionally keeps its domain, branch and remainder. The main frontier
review records the implementation consolidation without creating another zeta subsystem.
