# Eros theta/Mellin aperture 01

**2026-07-22 · exact finite involution · one shell-growth successor · positive lattice-energy
receiver · accepted · no engine change · no CUDA**

## Question and stop

This cell asked whether a finite theta-side current can grow by one reciprocal lattice shell while
retaining all of the following as causal material through replacement and rest:

- the direct/reciprocal theta arms;
- the Mellin reflection `s <-> 1-s` and fixed axis `s=1/2`;
- the fact that a raw finite truncation is not self-dual;
- its complete anti-invariant residual; and
- an independently positive receiver pairing covariant under the involution.

The stop was aperture `4 -> 5`, exact predecessor departure, and exact remount. No numerical
evaluation of `pi`, floating-point causal data, zero search, analytic continuation, Poisson-limit
claim, completed Weil form, CUDA passage, or RH claim entered.

## The finite object

For each lattice shell `n>=0`, the world carries two formal Gaussian arms:

```text
d_n(t) = exp(-pi n^2 t),
r_n(t) = t^(-1/2) exp(-pi n^2/t).
```

The actual involution is the typed shell swap

```text
J d_n = r_n,
J r_n = d_n,
J^2 = I.
```

The raw direct truncation and its reciprocal image are

```text
Theta_N^d = d_0 + 2 sum_(n=1)^N d_n,
Theta_N^r = r_0 + 2 sum_(n=1)^N r_n = J Theta_N^d.
```

A finite raw truncation does **not** satisfy `Theta_N^d=Theta_N^r`. The carrier therefore keeps
both its invariant and anti-invariant faces:

```text
S_N = (Theta_N^d + Theta_N^r)/2,    J S_N =  S_N,
A_N = (Theta_N^d - Theta_N^r)/2,    J A_N = -A_N.
```

Nothing is discarded:

```text
Theta_N^d = S_N + A_N,
Theta_N^r = S_N - A_N.
```

Growth uses the returned predecessor rather than rebuilding it:

```text
S_(N+1) = S_N + d_(N+1) + r_(N+1),
A_(N+1) = A_N + d_(N+1) - r_(N+1).
```

Thus aperture `4 -> 5` adds exactly the direct and reciprocal arms at `n=5`, carrying the exact
quadratic label `n^2=25`.

## Mellin receipt

For a positive shell, the two formal Mellin receipts are

```text
M[d_n](s) = Gamma(s/2)       (pi n^2)^(-s/2),
M[r_n](s) = Gamma((1-s)/2)   (pi n^2)^(-(1-s)/2).
```

The new shell carries affine coordinates

```text
direct:      s     = 0 + 1*s,
reciprocal:  1-s   = 1 - 1*s.
```

Substituting `s -> 1-s` exchanges them exactly and fixes `s=1/2`. The endpoint shell `n=0` remains
typed apart because its isolated Mellin integral is not one of these convergent positive-shell
receipts. `pi` is a formal constant in the reported analytic expression; it is never collapsed to
a machine float.

## Positive receiver pairing

The experiment deliberately uses a finite lattice-energy coefficient pairing, not the completed
Weil form. Paired arms receive equal exact weight:

```text
w_0=1,
w_n=n^2 for n>0,
<x,y>_N = sum_i w_i x_i y_i.
```

Every weight is positive, and equal weights on the two arms of each shell give

```text
J^T G_N J = G_N.
```

The successor restricts to the predecessor metric exactly. At aperture five:

```text
det(G_5)                  = 207360000
<S_5,S_5>                 = 221/2
<A_5,A_5>                 = 221/2
<S_5,A_5>                 = 0
new shell weight          = 25
```

This proves positivity and involution covariance for the declared finite receiver. It does not
identify this pairing with the global arithmetic trace required by Weil's criterion.

## Causal lifecycle

The source supplied one shell-growth law and one complete aperture-four face. Both crossed as
compact exact regional material and their source lineages ended. The body rested and remounted.

A later objective recruited the law and predecessor from Standing. The world extended that actual
predecessor by one shell pair. Its return consumed the predecessor data interface, predecessor
recruitment interface, and objective while exposing the aperture-five successor. The growth law
remained available.

```text
predecessor words              205
successor words                245
lower restriction exact       true
one shell pair added           true
old data interface departed    true
old recruit interface departed true
objective departed             true
live source lineages             0
rest/remount exact             true
```

The final resting constituent has 873 exact incidences and pins, 875 paths, and 1,536 transport
terms. Its rest identity is:

```text
214367f5bd5354222c98f62c75233a891a8578cf32196b44476661730feffb0b
```

## Physical result

```text
whole run wall            11,546 us
user CPU                   9,149 us
system CPU                 3,813 us
RSS high-water             2,372 -> 8,276 KiB
shell-growth law             128 us
predecessor return          1,042 us
growth meeting                593 us
successor replacement       3,416 us
largest event                 453 regional arcs
hard event limit            1,024 regional arcs
```

The indexed engine handled 453 declared replacement rows. The removed quadratic hot paths would
have visited an estimated 307,134 pairs at the same width. This is one heavy regional receiver;
the result does not claim 24-core saturation.

## What the experiment actually teaches

The finite construction closes the intended representation problem: involution, fixed axis,
positive metric, raw faces, and residual all survive one real successor lifecycle.

It also shows why formal shell pairing alone cannot establish theta reciprocity. In this receiver,
the anti-invariant residual has the same norm as the invariant face. Adding paired shells does not
make it contract. The symmetric face is invariant because the construction applies the exact
projector `(I+J)/2`; that is not a proof that the raw theta current equals its reciprocal image.

The next missing relation is consequently precise: a Fourier/Poisson transport with an exact tail
or boundary receipt and a topology in which the direct and reciprocal lattice currents converge
to one completed theta body. Only after that transport is causal can its Mellin image contribute
more than a declared `s <-> 1-s` atlas. Even that would establish the completed functional equation,
not the universal positive Weil carrier and not RH.

## Reproduction

```text
cargo check --manifest-path src/soma/Cargo.toml \
  -p life --example eros_formula_ecology
cargo build --release --manifest-path src/soma/Cargo.toml \
  -p life --example eros_formula_ecology
src/soma/target/release/examples/eros_formula_ecology \
  --theta-mellin NEW_REPORT.json
```

The accepted report is [`REPORT.json`](REPORT.json), SHA-256:

```text
1d998d88c1810117e6dbc530227e64b827bda1adfc218aa3bada033df7081c3b
```

The source compiled in release and test profiles; the example test harness contains no independent
unit tests. Acceptance comes from the exact runtime predicates above, not from a padded test count.
