# Exact zero navigation: a bounded policy control

**Status:** exact rational computational witness for a declared product of
two quadratic generators. This compares two policies on one source; it is
neither a general zero solver nor an RH result.

## Supplied source and requested consequence

The source Holon has two declared quadratic generators:

\[
f(z)=\bigl((z-(1/10+i/16))^2-1/2\bigr)
     \bigl((z-(1/10+3i/16))^2-1/3\bigr).
\]

The initial receiver is \([0,1]\times[0,1]\). The requested consequence is
a complete separation of its two **interior** zero fibres by horizontal
ports, with one winding-one region per root. Winding-zero regions are
retained as pruned receipts.

The generator-aware policy reads the **supplied quadratic centres and
radicands**, not two supplied root coordinates. For a generator
\((z-c)^2-d\), the rational inequalities
\(c_x^2<d<(1-c_x)^2\) prove
\(c_x+\sqrt d\in(0,1)\) and \(c_x-\sqrt d<0\). Thus each generator has one
interior root at its centre's height. Its real coordinate is an exact
irrational algebraic expression; no float or approximate root is used.
This factor structure is admitted source data, not an inferred discovery.
The fixed-midpoint control receives the same source and certifier but ignores
these generator heights in choosing its cut.

In the foundational Holon law, the oriented rectangles and edges are its
complex; each edge port carries a certified phase passage and its exact
value/remainder witness. Opposite hands on a shared cut cancel its winding
port. The two quadratic factors and the chord
remainder are the source constitution. A cut word is a generator action;
restriction to child rectangles is the scale map. The integer winding and
the isolated-root fibre are receiver faces of that one construction.

## Exact source and port law

For a boundary segment from \(a\) to \(b\), put \(z(t)=a+t(b-a)\), expand
the supplied polynomial exactly as \(P(t)=f(z(t))=\sum_{k=0}^4p_kt^k\), and
let \(L(t)=(1-t)P(0)+tP(1)\). In \(\mathbb Q(i)[t]\) the code forms

\[
M=\sum_{k=2}^4 k(k-1)(|\Re p_k|+|\Im p_k|).
\]

Then \(\sup_{[0,1]}|P''|\leq M\). The linear-interpolation remainder gives
\(\sup_{[0,1]}|P-L|\leq M/8\). The code computes
\(m^2=\min_{0\leq t\leq1}|L(t)|^2\) exactly by projecting the origin to
the rational chord and clamping to its endpoints. It accepts a segment
exactly when \(m^2>(M/8)^2\). This strict inequality certifies that the
homotopy from the actual source image to its chord avoids zero. A refused
segment is bisected until certified. Signed crossings of an exact rational
ray by the certified image polygon give the true boundary winding.

At a horizontal split, the vertical sides are restricted from the parent's
certified paths. A segment straddling the new endpoint is recertified in
two pieces. The new horizontal cut is certified once and reversed for the
other child. The script checks port cancellation and parent-child winding
additivity. The independent factor-containment count checks every region's
winding; it does not produce the polygon crossing result.

## Two deterministic policies

* `fixed_midpoint` bisects the height of every region with winding two.
* `generator_height` cuts at the rational midpoint of the two supplied
  quadratic-centre heights, \((1/16+3/16)/2=1/8\).

The policy grammar ends when each nonempty zero region has winding one.
Costs count new shared cuts, exact source calls at distinct rational points,
segment-certification attempts including refusals, accepted certificates,
and the largest numerator or denominator bit width among recorded sample,
witness and crossing rationals. Arithmetic operation count, factor-supply
cost, wall time and machine-independent bit complexity are not measured.

| Policy | Cuts | Source values | Segment attempts | Accepted | Refused | Recorded bits |
|---|---:|---:|---:|---:|---:|---:|
| Fixed midpoint | 3 | 34 | 67 | 38 | 29 | 87 |
| Generator height | 1 | 26 | 49 | 28 | 21 | 87 |

At least one horizontal cut is necessary to separate the two different
root heights; the generator-height policy meets that lower bound **for cut
count only**. It is not asserted to minimize evaluations or to be globally
optimal among all solver policies.

The [machine-readable receipt](receipt.json) retains each region's ordered
boundary, winding and cut, every accepted segment's exact inequality, and
the costs. Reproduce and independently check it with:

```sh
python3 research/experiments/holonic_zero_navigation/exact_policy.py
python3 research/experiments/holonic_zero_navigation/verify_receipt.py
```

Both scripts use Python's `fractions.Fraction`, with no float sampling. The
verifier reads the saved receipt, recomputes exact source values and segment
inequalities, checks every boundary winding and shared-port cancellation,
and reruns the deterministic policy to audit execution costs. The
factor-containment count is a second source-specific check; this control
does not supply an unfactored polynomial root-count algorithm.

## Connection and limitation

`crates/relational-geometry/src/eta_atlas/core.rs` certifies eta and
zeta-prime boundary jets with rational enclosures and analytic remainders;
`eta_atlas/atlas.rs::descend` reuses certified parent sides and certifies a
new cut. This control isolates that navigation mechanism with an exact
polynomial coefficient remainder. It does **not** compare performance on
eta or zeta, prove source-wide optimality, or include the cost of finding
the useful generator decomposition. The measured improvement is conditional
on this supplied expression, question and two-action grammar.

The next discriminating experiment should use actual eta-atlas receipts and
compare admitted cuts on the same band, charging source-jet work and bit
growth. A generator-derived cut is an improvement only if it certifies the
requested population at lower declared cost on that source. Transport to a
new source additionally needs a proof that its proposed factor or rechart
preserves the divisor and boundary-current receipt.
