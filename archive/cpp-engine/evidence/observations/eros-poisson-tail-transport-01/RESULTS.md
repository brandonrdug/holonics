# Eros Poisson tail transport 01

**2026-07-22 · finite aperture plus generative remainder · exact boundary transfer · accepted ·
one host run · no engine change · no CUDA**

## Question and stop

This cell asked one general machine question:

> Can a complete object seen through two transform-related charts remain exact while a finite
> participating aperture grows and its unmaterialized remainder advances?

The Gaussian theta relation supplied a bounded fixture. The stop was one aperture `4 -> 5`
replacement, exact lower restriction, predecessor departure, and exact rest/remount. No aperture
search, parameter sweep, numerical `pi`, floating-point causal datum, zeta-zero work, renderer,
CUDA passage, or RH claim entered.

Poisson summation for the Gaussian was inherited source law. The run neither discovered nor proved
it.

## General relation

For either chart `c`, split the complete object at aperture `N`:

```text
C_c = P_c,N + T_c,N
```

where `P` is the finite participating face and `T` is a finite description of the generative
remainder. If an inherited transform law identifies the two complete objects,

```text
C_d = C_r,
```

then the finite mismatch is exactly a boundary relation:

```text
P_d,N - P_r,N = T_r,N - T_d,N.
```

Growing the aperture must therefore transfer the same constituent on both sides of this equation.
It must not reconstruct a new complete object or pretend that the finite face was already
self-dual.

## Gaussian fixture

The two formal shell species are

```text
d_n(t) = exp(-pi*n^2*t),
r_n(t) = t^(-1/2)*exp(-pi*n^2/t),        t > 0.
```

At aperture `N`, the exact generative tails are

```text
T_d,N(t) = 2*sum_(n=N+1)^infinity d_n(t),
T_r,N(t) = 2*sum_(n=N+1)^infinity r_n(t).
```

They are carried without an infinite active population. Each tail retains its next shell,
multiplicity, hand, positive domain, and square-exponent recurrence:

```text
d_(n+1) = d_n*exp(-pi*t*(2*n+1)),
r_(n+1) = r_n*exp(-pi*(2*n+1)/t).
```

The aperture `4 -> 5` event moves shell five out of each tail and into its corresponding partial:

```text
P_d,5 = P_d,4 + 2*d_5       T_d,5 = T_d,4 - 2*d_5
P_r,5 = P_r,4 + 2*r_5       T_r,5 = T_r,4 - 2*r_5
```

In the exact coefficient basis `[d_5,r_5]`,

```text
Delta(P_d-P_r) = [ 2,-2]
Delta(T_r-T_d) = [ 2,-2].
```

Both complete-chart balances are `[+2,-2]`, hence zero. The direct and reciprocal tails advance
from shell `5` to shell `6`; the square-exponent gap is exactly

```text
6^2 - 5^2 = 2*5 + 1 = 11.
```

Since the removed Gaussian term is positive for `t>0`, each new tail is pointwise strictly smaller
than its predecessor. This is a typed order on the declared remainder, not a claim that the prior
finite coefficient metric contracts.

## Causal result

The source supplied one transform/boundary law and one complete aperture-four face. Their source
lineages ended. After exact rest/remount, a later current recruited that law and predecessor from
Standing, supplied the `4 -> 5` objective, and returned one replacement.

```text
predecessor words                 220
successor words                   260
lower restriction exact          true
law recovered from Standing      true
predecessor recovered             true
objective recovered from Current true
old data interface departed      true
old recruit interface departed   true
objective departed               true
live source lineages                0
final rest/remount exact          true
```

The final resting constituent has 934 exact incidences and pins, 936 paths, and 1,643 transport
terms. Its rest identity is:

```text
8c1315b8ed526703fd09f44951c535ca1a254a4a18554971ec43c74afd043a7a
```

## Physical result

The one accepted release run measured:

```text
whole run wall                 12,308 us
user CPU                        7,507 us
system CPU                      6,120 us
RSS high-water              2,420 -> 8,576 KiB
source law                        138 us
predecessor return              1,135 us
growth meeting                    612 us
successor replacement           3,823 us
largest event                     483 regional arcs
hard event limit                1,024 regional arcs
```

The largest event was one regional receiver, so this bounded cell does not claim or need 24-core
saturation. It completed in milliseconds without an iterative campaign.

## Consequence

The prior finite theta result retained a nonzero anti-invariant residual which did not contract in
its declared coefficient metric. This cell identifies the missing interpretation: that finite
residual is the visible side of an exact moving boundary, paired with the complementary tail
difference. Aperture growth changes both sides together while leaving the completed objects
invariant.

What is now established is causal carriage of finite aperture, exact generative remainder, and
boundary transfer through one real replacement lifecycle. What remains open is a construction
that does not merely inherit the Gaussian Poisson transform, its analytic convergence and
continuation in the relevant completed arithmetic setting, the completed trace/Weil carrier, and
the universal positivity implication required for RH.

## Reproduction

```text
cargo check --manifest-path src/soma/Cargo.toml \
  -p life --example eros_formula_ecology
cargo build --release --manifest-path src/soma/Cargo.toml \
  -p life --example eros_formula_ecology
src/soma/target/release/examples/eros_formula_ecology \
  --poisson-tail NEW_REPORT.json
```

The accepted report is [`REPORT.json`](REPORT.json), SHA-256:

```text
ae3072b0c74efdd309fb9904143181c153fbf121d3717eae9cc6b74326c617a2
```
