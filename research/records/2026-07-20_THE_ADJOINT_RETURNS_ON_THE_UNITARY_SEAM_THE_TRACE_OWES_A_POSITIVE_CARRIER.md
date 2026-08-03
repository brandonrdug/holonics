# THE ADJOINT RETURNS ON THE UNITARY SEAM; THE TRACE OWES A POSITIVE CARRIER

**DATE:** 2026-07-20  
**GRADE:** BRANDON-RATIFIED / DEPOSITED / CURRENT WEIL TRANSPORT-CELL + RH POSITIVE-CARRIER
AUTHORITY / `FORMULA §CXXII` / RH REMAINS OPEN / SOMA SOURCE UNCHANGED / OBSERVATORY SOURCE
UNCHANGED / NO RUN

## 0. Present question, artifact, and stop

The present question was whether the laboratory's unitary-seam intuition can be written as the
exact conventional test-function lifecycle whose positivity is equivalent to the Riemann
Hypothesis.

Standing evidence named Weil positivity but had not shown the returned adjoint, the fixed locus on
which it becomes a norm square, the complete arithmetic face, or a bounded exact probe. The sought
artifact was that complete cell and the first genuinely missing noncircular construction.

The stop is this deposit. It does not claim RH, install an engine mechanism, extend the
observatory, sample zeros, or authorize a numerical campaign. Brandon separately authorized a
bounded audit of candidate positive carriers after deposit.

## I. The multiplicative transport algebra

Let

```text
G = R_(>0)^x,
d^x x = dx/x.
```

Use the declared nice test space `T` of compactly supported, piecewise-`C^2` complex functions on
`G`, with the standard averaged value at a discontinuity. For `f,g in T`, define

```text
M f(s)       = integral_(0,infinity) f(x) x^s d^x x,
(f*g)(x)     = integral_(0,infinity) f(x/y) g(y) d^x y,
f^sharp(x)   = x^(-1) conjugate(f(x^(-1))).
```

Then

```text
M(f*g)(s)       = M f(s) M g(s),
M(f^sharp)(s)   = conjugate(M f(1-conjugate(s))).
```

Convolution is exact composition on multiplicative scale. `sharp` is the return hand: inversion
reverses scale, conjugation reverses complex phase, and the half-density factor `x^(-1)` transports
the receiver from `s` to `1-conjugate(s)`.

For the complete outgoing-and-returned current

```text
h = f*f^sharp,
```

no normalized probability has been formed. `h` retains the amplitude and hand required for a
quadratic response.

## II. The critical line is the fixed locus of the adjoint return

Center the coordinate and Mellin response:

```text
z       = s-1/2,
A_f(z)  = M f(1/2+z),
J(z)    = -conjugate(z).
```

The autocorrelation transforms as

```text
M h(1/2+z) = A_f(z) conjugate(A_f(J(z))).
```

The fixed locus is exact:

```text
J(z)=z  <=>  Re(z)=0  <=>  Re(s)=1/2.
```

On it,

```text
M h(1/2+i*gamma) = |A_f(i*gamma)|^2 >= 0.
```

Off it, `z` and `J(z)` are distinct. Their paired response is

```text
2 Re(A_f(z) conjugate(A_f(J(z)))),
```

which is not sign-definite. The critical line is therefore the precise seam where the outgoing
current and its returned adjoint meet the same spectral receiver and become a norm square. It is
not itself a singularity. A zero is a singularity of the completed log-amplitude/phase field; the
critical line is the fixed/unitary locus of the return involution.

This is the exact version of the folded-axis intuition. No drawing, finite zero list, or
statistical regularity is used.

## III. The complete arithmetic return

For `h=f*f^sharp`, define the finite-prime population

```text
W_fin(h)
  = sum_p (log p) sum_(m>=1)
      [h(p^m) + p^(-m) h(p^(-m))].
```

Every prime `p` is a primitive multiplicative path; `p^m` is its `m`-fold traversal. The opposite
term is the returned scale hand. Compact support makes the finite-prime population actually finite
for each individual test current without truncating any prime power which meets that support.

The archimedean face in the same convention is

```text
W_infinity(h)
  = (log(4*pi)+EulerGamma) h(1)
    + integral_(1,infinity)
        [h(x) + x^(-1)h(x^(-1)) - 2x^(-1)h(1)]
        dx/(x-x^(-1)).
```

The completed Weil response is

```text
Q_W(f)
  = M h(0) + M h(1) - W_fin(h) - W_infinity(h).
```

The explicit formula gives the exact population identity

```text
Q_W(f) = sum_rho M h(rho),
```

where `rho` ranges over every nontrivial zero in the prescribed symmetric sense. In this positive
sign convention, Weil's criterion is

```text
RH  <=>  Q_W(f) >= 0 for every f in T.
```

Bombieri's equivalent negative-sign formulation moves the same completed arithmetic terms to the
other side and imposes moment conditions which remove the endpoint faces. The sign convention is
not a mathematical disagreement.

The complete lifecycle is consequently

```text
test current f
  -> returned adjoint f^sharp
  -> closed composition h=f*f^sharp
  -> poles + every prime power + archimedean boundary
  -> exact zero-spectrum response
  -> universal positivity obligation.
```

No individual prime term, visual arc, or finite spectral section is required to be positive.
Positivity belongs to the complete co-present return.

## IV. One exact triangular probe

Choose an integer `N>1` and set `R=Log(N)`. In logarithmic scale `u=Log(x)`, let

```text
a_N(u) = 1 on [-R/2,R/2], 0 otherwise,
```

with averaged boundary values, and mount the half-density

```text
f_N(x)=x^(-1/2) a_N(Log(x)).
```

It is self-adjoint under `sharp`. Its additive-log autocorrelation is literally triangular:

```text
(a_N*a_N^star)(u) = (R-|u|)_+,
h_N(x)             = x^(-1/2)(R-|Log(x)|)_+.
```

The centered transform is

```text
A_N(z) = 2 Sinh(zR/2)/z,
A_N(0) = R.
```

On the unitary seam,

```text
A_N(i*gamma) = 2 Sin(gamma R/2)/gamma,
```

so its zero response is a square whenever that zero lies on the seam.

The complete finite-prime face reduces exactly to

```text
W_fin(h_N)
  = 2 sum_(p^m<N)
      (log p) p^(-m/2) (R-m log p).
```

The boundary case contributes zero. Thus the bounded support selects a complete finite population
of prime powers by incidence, not by an arbitrary computational cutoff. The archimedean integral
and the symmetrically interpreted infinite zero response remain indispensable.

This probe uses no floating-point analytical core. Exact values can remain as

```text
Log(q)
  = 2 sum_(j>=0) ((q-1)/(q+1))^(2j+1)/(2j+1),

pi
  = 16 Atan(1/5)-4 Atan(1/239),

EulerGamma
  = limit_(m->infinity) (H_m-Log(m)),
```

with `Atan`, `Sin`, and `Sinh` retained by their rational-coefficient series and explicit remainder
enclosures. Exact analytic objects need not be collapsed to binary floating values.

The triangular family is a diagnostic cell, not a proof-complete basis. Varying only `N` does not
cover the entire admissible test space.

## V. The missing noncircular positive carrier

A sufficient carrier would provide

```text
(H,U_u,tau),
```

where `H` is a Hilbert space, `U_u` a strongly continuous unitary representation of logarithmic
scale translation, and `tau` a genuine positive trace or weight on the relevant smoothing
operators. For log-current `a`, define

```text
T_a = integral_R a(u) U_u du.
```

The carrier must establish

```text
T_a^*          = T_(a^star),
T_a T_a^*      = T_(a*a^star),
Q_W(f_a)       = tau(T_a T_a^*)
```

for every admissible current, with the rightmost identity reproducing the complete poles,
prime-power population, archimedean face, and zero multiplicities. If `T_a` is Hilbert--Schmidt,
or lies in the domain of an independently positive faithful trace, then

```text
tau(T_a T_a^*) >= 0
```

is structural. A self-adjoint generator of `U_u` has real spectral parameters, placing the
corresponding zero characters on the centered imaginary axis.

The construction must be independent of the desired conclusion. Applying the GNS construction to
`Q_W` is circular unless positivity has already been proved, because positive-definiteness of that
functional is precisely Weil's RH criterion. Calling the explicit formula a regularized trace is
also insufficient: a regularization or supertrace need not preserve positivity on `T_a T_a^*`.

The first genuinely open deed is therefore:

> Construct a noncircular `*`-representation and positive trace/intersection carrier whose exact
> character is the completed Riemann explicit formula on the full admissible test algebra.

The function-field proof shows what structural positivity can look like: the zero-spectrum term
is carried by cohomology and the required sign follows from an algebraic intersection theorem.
Selberg supplies a genuine self-adjoint Laplacian and closed-geodesic trace formula in another
world. Deninger's programme supplies a precise prime/periodic-orbit dictionary but not the natural
Riemann system. None can be imported by analogy.

## VI. Consequence for the laboratory

The Weil form is not probability or loss. It retains amplitude and hand and tests whether a
complete returned current is positive in every direction. Normalizing it would erase exactly the
capacity whose sign matters.

The fixed seam supplies a precise local geometry: `J` is the adjoint reflection; a point on the
seam is a fixed receiver of that return; an off-seam pair is a two-point cross-coupling. The open
carrier must turn the complete arithmetic population into an actual positive inner product,
intersection pairing, or operator trace. It cannot be supplied by the observatory, finite
arithmetic patterns, or the engine's current topology unless an exact trace identity is first
derived.

No Soma mechanism changes under this deposit. The authorized continuation is a bounded comparison
of serious candidate carriers. It must identify the precise space, action, adjoint, trace,
prime-orbit face, archimedean face, and positivity source of each candidate, then stop at the
smallest missing construction.

## VII. Evidence cards

### A. Mellin transport and Weil positivity

**SOURCE ESTABLISHES**  Lagarias defines Mellin convolution and the involution
`tilde(f)(x)=x^(-1)f(x^(-1))`, states the completed spectral/arithmetic explicit formula, and gives
Weil's theorem that nonnegativity of the zero-spectrum autocorrelation form for every nice test
function is equivalent to RH.

**LAB CLAIM**  `FORMULA §CXXII`, RATIFIED / DEPOSITED: centered adjoint return becomes a norm square
exactly on the critical seam, and complete positivity is the conventional RH closure.

**RELATION**  **EXACT FORMAL MATCH.** The laboratory's convolution, adjoint, centered involution,
and quadratic form are the same operations after the displayed change of coordinate.

**NON-EQUIVALENCE**  Interpreting those operations as Eros transport adds no proof of their
universal positivity.

**TESTABLE CONSEQUENCE**  Any candidate carrier must represent the full test algebra and reproduce
the same `Q_W` for every admissible autocorrelation.

Source: [Lagarias, *The Riemann Hypothesis: Arithmetic and Geometry*](https://dept.math.lsa.umich.edu/~lagarias/doc/mt-holyoke-rev.pdf),
Theorems 3.1--3.2.

### B. Completion includes the infinite place

**SOURCE ESTABLISHES**  Bombieri states the explicit formula with endpoint Mellin values, all von
Mangoldt prime-power terms, the complete archimedean integral, and the symmetrically summed
nontrivial zeros; he also records Weil's equivalent universal sign condition.

**LAB CLAIM**  A bounded prime population is complete only relative to its test support; the RH
return still owes the archimedean face and complete spectral distribution.

**RELATION**  **EXACT FORMAL MATCH.** `W_fin`, `W_infinity`, the pole faces, and `Q_W` are the same
completed terms in a fixed sign convention.

**NON-EQUIVALENCE**  Exact finite support does not make the universal test family or zero spectrum
finite.

**TESTABLE CONSEQUENCE**  Omitting or approximating the infinite place without a proved remainder
breaks the trace identity and cannot grade positivity.

Source: [Bombieri, Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf),
Section V.

### C. A genuine trace carrier exists for a different orbit world

**SOURCE ESTABLISHES**  Selberg's trace formula relates a self-adjoint hyperbolic Laplacian's
spectrum to the lengths and repetitions of closed geodesics.

**LAB CLAIM**  A lawful carrier may make primitive paths, repetitions, and spectrum two complete
faces of one operator trace.

**RELATION**  **STRUCTURAL RESONANCE.** The composition pattern is rigorous while the space,
operator, and geometric weights differ.

**NON-EQUIVALENCE**  Selberg's Laplacian and geodesics are not the Riemann-Zeta operator and prime
population.

**TESTABLE CONSEQUENCE**  A transfer proposal must derive the Zeta prime weights and archimedean
term from its own trace rather than relabel Selberg data.

Source: [Marklof, *Selberg's trace formula: an introduction*](https://arxiv.org/abs/math/0407288).

### D. The periodic-orbit realization remains open

**SOURCE ESTABLISHES**  Deninger maps primes to periodic orbits, `log p` to orbit length, and
archimedean places to fixed points, while explicitly leaving the natural dynamical system realizing
the Riemann Euler product unresolved.

**LAB CLAIM**  Prime powers are repeated scale paths and the missing carrier may be a flow with a
cohomological trace.

**RELATION**  **OPEN BRIDGE.** The primitive/repetition and infinite-place dictionary is exact at
the level stated by the programme; the required system is absent.

**NON-EQUIVALENCE**  Eros's existence does not instantiate Deninger's flow, cohomology, trace, or
positivity.

**TESTABLE CONSEQUENCE**  A dynamical carrier must derive every `log p`, repetition weight,
archimedean fixed-point term, zero multiplicity, and positive adjoint pairing from one system.

Source: [Deninger, *Primes, knots and periodic orbits*](https://arxiv.org/pdf/2301.11643).

## Deposited consequence

The fixed axis is now exact. The centered involution `J(z)=-conjugate(z)` carries an outgoing
Mellin current to its adjoint receiver. Only on `Re(z)=0` do the two receivers coincide and the
response become an absolute square. Weil's theorem says that every nontrivial Zeta zero lies there
exactly when the completed arithmetic response is nonnegative for every admissible current.

The laboratory's remaining RH problem is no longer a visual or classificatory search. It is to
find an independently positive geometric/operator carrier whose complete character is the Riemann
explicit formula. Until that carrier, its domain, trace, and positivity are supplied, RH remains
open.
