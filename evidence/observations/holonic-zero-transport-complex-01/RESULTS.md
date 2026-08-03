# Holonic Zero Transport Complex 01

**Status:** COMPLETE / EXACT RATIONAL POST-PROCESS / FIVE CERTIFIED
ZERO RECEIVERS / TEN DISTINCT PAIR SUPPORTS / ONE COMPLETE
TURN-WORD FACTORIZATION / LOCAL COHERENT SHEETS RETAINED / NO IEEE
FLOATS / NO CUDA

## Present question

If each certified nontrivial-zero receiver is treated as a local perspective,
does every pair carry a specific transport procedure, and do third receivers
sometimes factor that procedure into a shorter coherent path?

The source is the already verified
`holonic-eta-ratio-atlas-01`. It supplies five independently isolated
zero-bearing receivers in

\[
\left[\frac25,\frac35\right]\times[12,36],
\]

their six exact refinement decisions, and 96 exact rational-series current
terms at each receiver midpoint. This run does not seed decimal zero
ordinates, regenerate the expensive eta atlas, or substitute a midpoint for
the unknown zero inside its certified receiver.

## Transport object

For receiver \(i\), series ordinal \(n\), and observed feature \(f\), let

\[
x_i^f(n)\in\{-,0,+,\mathrm{open}\}.
\]

The six exact categorical faces used here are:

1. real and imaginary contribution orientation;
2. real and imaginary partial-sum orientation;
3. the oriented turn between consecutive contributions; and
4. the change in squared radial enclosure between consecutive partial sums.

The turn is the exact interval classification of

\[
\det(c_n,c_{n+1})
=
\operatorname{Re}(c_n)\operatorname{Im}(c_{n+1})
-
\operatorname{Im}(c_n)\operatorname{Re}(c_{n+1}).
\]

No angle, decimal coordinate, or numeric \(\pi\) is introduced.

For each pair \(i,j\), define the feature support

\[
D_{ij}^f
=
\{n:x_i^f(n)\ne x_j^f(n)\}.
\]

The complete bounded pair testimony consists of the directed endpoint
values, all six supports, the exact zero-ordinate difference receiver, and the
refinement grains that change. Reversing \(i\to j\) preserves the support but
reverses the carried endpoint hand.

A mediator \(k\) is coherent for feature \(f\) exactly when

\[
x_k^f(n)\in\{x_i^f(n),x_j^f(n)\}
\qquad\text{for every defined }n.
\]

Thus:

- when the endpoints agree, the mediator must retain that value;
- when they differ, the mediator may carry either endpoint value;
- leaving and returning is a detour; and
- assuming a value carried by neither endpoint is a third-value passage.

This is a receiver-relative geodesic law. It does not install one absolute
distance between zeroes.

## The ten pair procedures are distinct

The columns `CR, CI, PR, PI, T, R` give the exact number of changed ordinals
for contribution-real, contribution-imaginary, partial-real,
partial-imaginary, turn, and radial-change faces. The actual directed values
and complete ordinal supports remain in `TRANSPORT.ron`.

| Pair | Exact ordinate-difference receiver | Refinement grains | CR, CI, PR, PI, T, R | Turn support |
|---:|---:|---:|---:|---:|
| \(0,1\) | \([\frac{55}{8},\frac{221}{32}]\) | \(3,6\) | \(44,47,47,48,4,44\) | \(1,2,5,6\) |
| \(0,2\) | \([\frac{695}{64},\frac{697}{64}]\) | \(3\) | \(47,49,49,51,4,46\) | \(3,5,6,7\) |
| \(0,3\) | \([\frac{521}{32},\frac{261}{16}]\) | \(2,5,6\) | \(47,48,48,53,8,39\) | \(1,3,4,5,6,7,8,9\) |
| \(0,4\) | \([\frac{601}{32},\frac{301}{16}]\) | \(1,2,5,6\) | \(46,47,45,51,7,42\) | \(2,4,5,6,7,8,9\) |
| \(1,2\) | \([\frac{127}{32},4]\) | \(6\) | \(51,52,48,55,4,30\) | \(1,2,3,7\) |
| \(1,3\) | \([\frac{601}{64},\frac{603}{64}]\) | \(2,3,5\) | \(47,53,47,53,6,43\) | \(2,3,4,7,8,9\) |
| \(1,4\) | \([\frac{761}{64},\frac{763}{64}]\) | \(1,2,3,5\) | \(50,54,46,47,5,40\) | \(1,4,7,8,9\) |
| \(2,3\) | \([\frac{173}{32},\frac{87}{16}]\) | \(2,3,5,6\) | \(46,45,47,48,4,47\) | \(1,4,8,9\) |
| \(2,4\) | \([\frac{253}{32},\frac{127}{16}]\) | \(1,2,3,5,6\) | \(53,50,46,54,5,46\) | \(2,3,4,8,9\) |
| \(3,4\) | \([\frac{159}{64},\frac{161}{64}]\) | \(1\) | \(53,59,53,64,3,29\) | \(1,2,3\) |

Comparison of the complete six-support plus refinement signatures found no
collision among the ten unordered pairs. In this bounded ecology, “the path
between two zeroes” is therefore not reducible to their height gap. Every pair
has a different exact change word.

## One winding path factors exactly

Let \(N_i\) be the ordinals at which receiver \(i\) carries a negative
consecutive-contribution turn. For receivers \(0,2,3\),

\[
\begin{aligned}
N_0&=\{1,2,3,4\},\\
N_2&=\{1,2,4,5,6,7\},\\
N_3&=\{2,5,6,7,8,9\}.
\end{aligned}
\]

The two legs partition the direct change:

\[
\begin{aligned}
N_0\mathbin{\triangle}N_2
  &=\{3,5,6,7\},\\
N_2\mathbin{\triangle}N_3
  &=\{1,4,8,9\},\\
(N_0\mathbin{\triangle}N_2)
\mathbin{\dot\cup}
(N_2\mathbin{\triangle}N_3)
  &=N_0\mathbin{\triangle}N_3.
\end{aligned}
\]

Consequently,

\[
0\longrightarrow2\longrightarrow3
\]

is coherent at every one of the 95 defined turn ordinals. The reverse path is
equally coherent. There is no turn detour and no third turn value. After the
direct \(0\leftrightarrow3\) edge is factored, the shortest coherent path has
degree two and is uniquely \(0\leftrightarrow2\leftrightarrow3\).

The first leg is supported on

\[
3,\ 5,\ 2\cdot3,\ 7,
\]

while the second is supported on

\[
1,\ 2^2,\ 2^3,\ 3^2.
\]

This is an exact prime-valuation description of the observed partition. Five
receivers are not enough to infer that prime/prime-power separation is a
general law; the result identifies a concrete motif to test at later heights.

Receiver \(1\) lies between \(0\) and \(2\) in height but does not factor the
\(0\to3\) turn word. The transport neighborhood is therefore not ordinary
height adjacency.

## Whole body and local sheets

No single third receiver factors all six faces and the refinement word at
once. At that deliberately strict whole-body grain, all 20 directed edges are
primitive and all 60 oriented triangles contain an interior excursion. This
does **not** erase the turn factorization. It shows that primitivity depends on
which relation the current is carrying.

No feature-level passage assumes a third categorical value anywhere in the
\(60\times6\) feature passages. The defects are leave-and-return excursions.
Nevertheless, a mediator can assemble a whole six-feature tuple unequal to
both endpoint tuples while every individual feature still belongs to one
endpoint. In \(0\to2\to3\), that exact mixed retriangulation occurs at

\[
\{3,4,6,8,9,11,27,31,35,36,37,38,83,84,93,95\}.
\]

This is the computational distinction between:

- introducing an unsupported constituent; and
- composing a new co-present face entirely from endpoint-supported
  constituents.

The strict full-96-word test also contains long local coherent strata:

| Feature | Mediated path | Maximal exact coherent ordinal span |
|---|---:|---:|
| Contribution real | \(3\to2\to4\) | \(23\ldots57\) |
| Contribution imaginary | \(1\to4\to2\) | \(38\ldots73\) |
| Partial-sum real | \(1\to4\to2\) | \(36\ldots69\) |
| Partial-sum imaginary | \(3\to1\to4\) | \(31\ldots73\) |
| Consecutive turn | \(0\to2\to3\) | \(1\ldots95\) |
| Radial change | \(2\to1\to4\) | \(49\ldots95\) |

These are local sheets in series order. A single later excursion must not
retroactively classify an earlier coherent stratum as nonexistent.

## Flat and quotient controls

For every oriented triangle \(i\to k\to j\), the exact rational midpoint
ordinate differences telescope:

\[
(\tau_k-\tau_i)+(\tau_j-\tau_k)=\tau_j-\tau_i.
\]

All 60 controls close. This is the flat coordinate control, not evidence that
the current words are flat.

Naive interval arithmetic gives every mediated zero-receiver difference an
extra width of \(\frac1{32}\). The reason is explicit:

\[
(B-A)+(C-B)
\]

treats the two appearances of the same interval \(B\) as independent. The
extra width is lost dependency in the box quotient, not geometric curvature.
The artifact keeps this foil separate so that representation loss cannot be
reported as a physical or holonic defect.

## Consequence for RH and counterexample search

This computation supports a precise version of the proposed small-world
picture:

- vertices are certified local zero receivers;
- an edge is an exact receiver-to-receiver transformation word;
- neighborhoods depend on the carried feature;
- a coherent mediator factors a direct change without excursion;
- causal degree is the length of a shortest coherent primitive path; and
- local coherent sheets may persist even when the complete current body does
  not globally factor.

It does not prove RH. All five source receivers were already proved to contain
one critical-line closure, and the source scan covers only
\([\frac25,\frac35]\), not the full critical strip.

The same exact receiver machinery can search for a counterexample without
importing known zero ordinates: partition the full strip into rational
receivers, certify boundary winding, refine every nonzero cell, and compare
each isolated receiver with its reflected mate. A cell isolated wholly away
from \(\operatorname{Re}s=\frac12\) would be proof-bearing evidence. Transport
analysis can then classify its relation to the existing ecology, but cannot
replace the winding certificate.

At larger zero counts, all ordered pairs cost
\(O(Z^2MF)\) for \(Z\) receivers, \(M\) retained series ordinals, and \(F\)
features. Enumerating every triangle at \(O(Z^3MF)\) is unnecessary. For a
fixed endpoint pair, admissible mediators can be obtained by intersecting,
over ordinals, the exact receiver sets carrying either endpoint value. Those
intersections are finite categorical bitsets, so independent endpoint pairs
and height bands can run across CPU cores without floats or shared mutable
causality.

The bounded transport derivation itself takes less than one second on the
present machine (`0.637` seconds including process startup, raw-atlas parse,
RON generation, and write). The expensive operation remains exact analytic
zero certification, not pair transport. The existing source atlas used 12
workers; no long rerun was needed here.

## Verification and artifacts

The verifier re-derives the complete report from the 49,009,322-byte raw eta
atlas and compares structural equality.

- Derived artifact: `TRANSPORT.ron`
- Size: 4,507,569 bytes
- SHA-256:
  `de41fc4afa5e3972fb93ec7d1e69def33f1f1309d507cde0a14d55271a0cdb3f`
- Source atlas SHA-256:
  `e41047157d38f050cd87590f35ceac1ced1f7d1835d9b479ce01c0c1b121d7f1`
- Exact-analysis tests: 4 passed

Generate:

```sh
cargo run -q -p relational-geometry \
  --example holonic_zero_transport_complex -- \
  /path/to/ATLAS.ron \
  src/soma/observations/holonic-zero-transport-complex-01/TRANSPORT.ron
```

Verify:

```sh
cargo run -q -p relational-geometry \
  --example holonic_zero_transport_complex -- \
  verify \
  /path/to/ATLAS.ron \
  src/soma/observations/holonic-zero-transport-complex-01/TRANSPORT.ron
```

Compact structural read:

```sh
cargo run -q -p relational-geometry \
  --example holonic_zero_transport_complex -- \
  summarize \
  src/soma/observations/holonic-zero-transport-complex-01/TRANSPORT.ron
```
