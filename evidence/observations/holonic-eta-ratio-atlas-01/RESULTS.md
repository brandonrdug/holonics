# Holonic Eta Ratio Atlas 01

**Status:** COMPLETE / EXACT RATIONAL RECEIVER ATLAS / FIVE SINGLE
CLOSURES / SIX REFINEMENT GRAINS / RECEIPT RE-DERIVED / NO ZERO
ORDINATES SEEDED / NO IEEE FLOATS

## Question

Can the first portion of the nontrivial zeta-zero field be observed directly
as exact rational receiver topology, retaining the composing series current and
the ratios among discovered closures, rather than importing decimal zero
ordinates?

This cell answers that question on

\[
B=\left[\frac25,\frac35\right]\times[12,36]
\subset \mathbb C .
\]

It does not claim to cover the rest of the critical strip or unbounded height.

## Exact source and receiver law

The observed source is

\[
\eta(s)
=\sum_{n\geq1}(-1)^{n-1}n^{-s}
=\left(1-2^{1-s}\right)\zeta(s).
\]

The extra factor has no zero in the scanned real interval, so the eta closures
in this cell are zeta closures.

Every receiver coordinate and every enclosure endpoint is a `BigRational`.
Logarithm, exponential, sine, and cosine are evaluated by rational series with
explicit rational remainder bounds. Zeta is enclosed by Euler--Maclaurin with
exact Bernoulli corrections and an explicit rational remainder. Returning an
intermediate to a dyadic grain means outward enclosure on
\(2^{-96}\mathbb Z\); it is not conversion to a binary floating scalar.

For each rational rectangle:

1. its boundary is subdivided until every segment's complete eta image lies in
   a convex rational rectangle excluding the origin;
2. the endpoint representatives and the actual image curve are therefore
   homotopic inside origin-free rectangles;
3. a rational ray-crossing calculation gives the exact boundary winding; and
4. winding additivity selects a child receiver without supplying a known zero.

## Found closures

The 24 independent unit-height receivers have total winding \(5\). Five have
winding \(1\); every other unit band has winding \(0\). Six lawful refinements
give:

| Closure | Exact ordinate receiver | Width |
|---:|---:|---:|
| 0 | \(\left[\frac{113}{8},\frac{905}{64}\right]\) | \(\frac1{64}\) |
| 1 | \(\left[\frac{1345}{64},\frac{673}{32}\right]\) | \(\frac1{64}\) |
| 2 | \(\left[25,\frac{1601}{64}\right]\) | \(\frac1{64}\) |
| 3 | \(\left[\frac{1947}{64},\frac{487}{16}\right]\) | \(\frac1{64}\) |
| 4 | \(\left[\frac{2107}{64},\frac{527}{16}\right]\) | \(\frac1{64}\) |

Each receiver is invariant under the nontrivial-zero reflection

\[
\rho\longmapsto 1-\overline{\rho}.
\]

Because each contains exactly one zero counted with multiplicity, reflection
cannot send that zero to a distinct member of the same receiver. It fixes the
zero, and therefore

\[
\operatorname{Re}\rho=\frac12
\]

for each of these five independently found closures.

This is a bounded proof, not a decimal comparison with a classical zero table.
It proves that the one closure in each listed receiver lies on the critical
line. It does not exclude additional closures in the parts of
\(0<\operatorname{Re}s<1\) outside \([2/5,3/5]\), and it is not an induction
over all heights.

## Ratio field

The exact successive gaps are:

| Members | Gap receiver | Common continued-fraction prefix |
|---:|---:|---:|
| \(0,1\) | \(\left[\frac{55}{8},\frac{221}{32}\right]\) | \([6,1]\) |
| \(1,2\) | \(\left[\frac{127}{32},4\right]\) | unresolved at first digit |
| \(2,3\) | \(\left[\frac{173}{32},\frac{87}{16}\right]\) | \([5,2]\) |
| \(3,4\) | \(\left[\frac{159}{64},\frac{161}{64}\right]\) | \([2]\) |

The successive gap ratios are:

\[
\begin{aligned}
\frac{g_1}{g_0}
&\in\left[\frac{127}{221},\frac{32}{55}\right],
&\mathrm{CF}&=[0,1,1,2,1],\\
\frac{g_2}{g_1}
&\in\left[\frac{173}{128},\frac{174}{127}\right],
&\mathrm{CF}&=[1,2,1],\\
\frac{g_3}{g_2}
&\in\left[\frac{53}{116},\frac{161}{346}\right],
&\mathrm{CF}&=[0,2].
\end{aligned}
\]

Two ordered projective cross-ratios give different local words:

\[
\begin{aligned}
[0,1,2,3]&:
\left[\frac{417695}{267264},\frac{420291}{264668}\right],
&\mathrm{CF}&=[1,1,1],\\
[1,2,3,4]&:
\left[\frac{152053}{132762},\frac{153162}{131653}\right],
&\mathrm{CF}&=[1,6].
\end{aligned}
\]

The first five closures therefore do not support one constant additive,
multiplicative, continued-fraction, or projective recurrence. Their relation is
not absence of law; it is a changing composition law.

## The composing current

At the midpoint of each final receiver, the artifact retains the first 96 eta
terms, their exact prime valuations, their oriented contributions, every
partial sum, and a rational bound for the entire remaining tail.

Let

\[
c_n(s)=(-1)^{n-1}n^{-s}.
\]

At \(s=\frac12+i\tau\), consecutive terms obey

\[
\frac{c_{n+1}}{c_n}
=-\left(\frac{n+1}{n}\right)^{-s},
\qquad
\Delta\phi_n
=\pi-\tau\log\left(\frac{n+1}{n}\right).
\]

Thus the local turn is controlled by the exact successor ratio
\((n+1)/n\), the receiver ordinate, and the alternating hand. The
implementation does not insert a numeric \(\pi\): the minus sign supplies the
exact half-turn, while logarithm and trigonometric values remain rational
series enclosures.

All 95 consecutive contribution turns are sign-certified in all five paths:

| Closure | Positive turns | Opposite turns | Opposite-turn edges \(n\to n+1\) |
|---:|---:|---:|---|
| 0 | 91 | 4 | \(1,2,3,4\) |
| 1 | 91 | 4 | \(3,4,5,6\) |
| 2 | 89 | 6 | \(1,2,4,5,6,7\) |
| 3 | 89 | 6 | \(2,5,6,7,8,9\) |
| 4 | 88 | 7 | \(1,3,5,6,7,8,9\) |

These sets are neither identical nor monotonically nested. They are shifting
phase windows generated by the same successor law. This is the clearest
recurrence found in this cell: **the rule recurs; its instantiated motif
changes with the receiver.**

The corresponding 96-term partial paths have the following certified axis
crossings:

| Closure | Real-axis crossings | Imaginary-axis crossings | Eight nearest partial returns by rational \(L^1\) upper bound |
|---:|---:|---:|---|
| 0 | 79 | 78 | \(94,96,95,85,86,75,76,77\) |
| 1 | 72 | 72 | \(95,76,88,82,89,96,93,94\) |
| 2 | 69 | 69 | \(91,76,92,80,67,87,71,81\) |
| 3 | 66 | 65 | \(72,65,88,95,92,90,81,79\) |
| 4 | 64 | 63 | \(84,93,89,63,91,95,77,79\) |

The nearest-return ordering is a comparison of rigorous enclosure bounds, not
a claim that a 96-term prefix is the zero. It shows that the closures are
assembled by different partial trajectories even where their boundary
winding has the same species.

## Geometric consequence

For fixed \(\tau\),

\[
c_n(\sigma,\tau)
=e^{-\sigma\log n}
\left((-1)^{n-1}e^{-i\tau\log n}\right).
\]

Changing \(\sigma\) therefore changes the radial weight of each existing ray;
it does not change that ray's direction. The critical-strip receiver is a
family of weighted equilibria of one fixed phase ecology. Reflection compares
the two weightings \(\sigma\) and \(1-\sigma\).

This makes the plausible global RH object more precise. It is not a fixed
ratio among zero ordinates. It is a theorem that a reflection-paired
phase ecology cannot close at two distinct radial weightings. Equivalently, a
receiver-relative convexity, variation, or crossing law for
\(\sigma\mapsto\eta(\sigma+i\tau)\) would force a single closure to occur at
the fixed weighting \(\sigma=1/2\). The five cells above instantiate that
property exactly; they do not yet prove it for every phase ecology.

Here “positive” has no absolute geometric role. The signs used by the
certificate are oriented cross-products and boundary winding relative to a
declared receiver. Reversing the receiver reverses orientation without
changing the closure.

## Receipt verification

The verifier independently checked:

- all 24 band boundaries are closed, continuous, and origin-free;
- every stored polygon winding re-derives from its rational ray;
- every refinement partitions its parent exactly and satisfies
  \(w_L+w_R=w_{\mathrm{parent}}\);
- every selected child and every final receiver carries winding \(1\);
- all 480 retained terms have the declared alternating hand;
- every term's prime valuations multiply back to its ordinal;
- all 480 partial sums re-derive from the preceding sum and contribution at
  the declared exact grain;
- every gap, ordinate ratio, gap ratio, cross-ratio, and reciprocal moment
  re-derives from the final receivers; and
- all 29 `relational-geometry` tests pass.

The physical run used 12 workers on the 12-core / 24-thread Ryzen 9 7900X and
completed in 155,503 milliseconds. No CUDA run was used.

## Artifacts and reproduction

- Lossless complete receipt: `ATLAS.ron.zst`
- Raw RON size: 49,009,322 bytes
- Raw SHA-256:
  `e41047157d38f050cd87590f35ceac1ced1f7d1835d9b479ce01c0c1b121d7f1`
- Compressed size: 652,058 bytes
- Compressed SHA-256:
  `ff9d7dc54a1aa056f60ebcfc1a4f71975661b878df15ed5b696e8886ac1d0326`

Generate:

```sh
cargo run -q -p relational-geometry \
  --example holonic_eta_ratio_atlas -- \
  12 36 \
  src/soma/observations/holonic-eta-ratio-atlas-01/ATLAS.ron \
  12 6
```

Verify after lossless decompression:

```sh
zstd -d \
  src/soma/observations/holonic-eta-ratio-atlas-01/ATLAS.ron.zst \
  -o /tmp/holonic-eta-ratio-atlas-01.ron

cargo run -q -p relational-geometry \
  --example holonic_eta_ratio_atlas -- \
  verify /tmp/holonic-eta-ratio-atlas-01.ron
```
