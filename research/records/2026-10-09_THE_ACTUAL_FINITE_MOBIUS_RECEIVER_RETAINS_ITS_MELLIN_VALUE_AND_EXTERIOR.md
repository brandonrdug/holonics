# The actual finite Möbius receiver retains its Mellin value and exterior

**Date:** 2026-10-09. **Issues:** #62, #63, #147. **Scope:** the actual finite signed
ordinary-Möbius source, its full positive-ray Mellin reading, its logarithmic
Fourier reading, and its retained exterior energy and complex flux. These are
receiver and ratio charts of the helical pair interaction. They touch phase,
carry, receiver faces and the tube cut; no HNN execution changes.

The sole native queue accepted the three new private source modules with
11 literal axiom queries. Their three accepted prerequisite modules supply
12 earlier queries. Every one prints only `propext`, `Classical.choice` and
`Quot.sound`. The exact accepted source snapshots, public-owner mapping,
kernel results, projected diagnostics and object-part seals are in the
[publication receipt](receipts/2026-10-09-rh-spectral-publication/SOURCE_PUBLICATION_JOIN.json).

The canonical owners below change only actual import paths and the initial
historical-status comments. All other bytes are compared with the accepted
snapshots. This publication preparation does **not** claim a kernel check of
the renamed public module graph or a full library build; the sole queue must
check that graph before integration. The accepted private originals and full
native evidence remain intact outside Git.

## The actual source and its endpoint

For (N\in\mathbb N), define

\[
B_N=\sum_{1\le n\le N}\frac{\mu(n)}n,\qquad
A_N(s)=\sum_{1\le n\le N}\frac{\mu(n)}{n^s},\qquad
r_N(x)=\mathbf1_{(0,1]}(x)+
 \sum_{1\le n\le N}\mu(n)\left\{\frac1{nx}\right\}\quad(x>0).
\]

These use `ArithmeticFunction.moebius`, ordinary `Int.fract`, and finite sums.
In particular, the fractional reading is zero at an integer and the physical
step is one at (x=1). The finite divisor convolution supplies the exact
floor partition. Its pointwise consumer is

\[
N>0,\ x\ge 1/N\quad\Longrightarrow\quad r_N(x)=B_N/x.
\]

The cutoff comes from the actual arithmetic source. It is not a chosen
frequency aperture. `N=0` remains admitted in the finite source and the Mellin
identity below; it is excluded from statements using the cutoff (1/N).

## The full Mellin reading and logarithmic receiver

The fractional-part adapter first uses the cached L-series partial-sum
integral on \(\Re s>1\). It then establishes the regularized-zeta fractional
integral on \(\Re s>0\), and the ordinary-zeta formula on that half-plane
with (s\ne1):

\[
\zeta(s)=\frac{s}{s-1}
 -s\int_1^\infty \{x\}x^{-s-1}\,dx.
\]

The pole term is retained. No infinite Euler or Möbius series is used on the
critical strip. The reciprocal fractional-part integral is joined to the
cached interval-power formula only almost everywhere at its exceptional
endpoint: ordinary `fract(1)=0` differs from the closed-interval power
indicator's value. An explicit singleton exclusion pays that join. The
physical step/dilation identity is separately pointwise, including (x=1).

For every (N\in\mathbb N) and (0<\Re s<1), the checked `HasMellin` result is

\[
\int_0^\infty x^{s-1}r_N(x)\,dx
   =\frac{1-\zeta(s)A_N(s)}s.
\]

Convergence is part of the theorem. With (N>0), (0<\sigma<1), set

\[
g_{N,\sigma}(u)=e^{-\sigma u}r_N(e^{-u}).
\]

This complexified receiver is both `Integrable` and `MemLp ... 2 volume`.
Mathlib's Fourier normalization gives, for (\sigma=\Re s),

\[
\mathcal Fg_{N,\sigma}\!\left(\frac{\Im s}{2\pi}\right)
   =\frac{1-\zeta(s)A_N(s)}s.
\]

The physical measure is Lebesgue (dx) on the full positive ray; the
logarithmic measure is Lebesgue (du) on the full real line. These are not
counting measure or a finite population probability. Each domain theorem
holds for a fixed (N); it supplies no uniform-in-(N) decay.

## The exterior returns to the same receiver

For (N>0), the full squared receiver is integrable and splits exactly:

\[
\int_0^\infty r_N(x)^2\,dx
 =\int_{(0,1/N]}r_N(x)^2\,dx+N B_N^2.
\]

Thus (NB_N^2\) is a nonnegative exterior contribution bounded above by the
full energy. That lower comparison is not an upper estimate for the complete
source. The cut belongs to the interior; the exterior is `(1/N, infinity)`.

More generally, (N>0), (a\ge1/N), and (\Re s<1) suffice for the exterior
Mellin integral; no lower abscissa restriction is needed for this tail alone:

\[
\int_a^\infty x^{s-1}r_N(x)\,dx
 =\frac{B_Na^{s-1}}{1-s},\qquad
\left\|\int_a^\infty x^{s-1}r_N(x)\,dx\right\|
 =\frac{|B_N|a^{\Re s-1}}{\|1-s\|}.
\]

The complex phase and denominator remain explicit. Omitting this term
changes the Mellin receiver. No universal lower denominator margin is
assumed. When the full Mellin theorem is also consumed, its narrower strip
(0<\Re s<1) must still be kept.

## Owners, native receipts and publication gate

| Canonical owner under `lean/HolonicsResearch/Zeta/` | Principal consumer | Private native gate |
|---|---|---|
| `ActualFiniteBeurlingReceiver.lean` | `actual_nb_receiver`, `actual_nb_tail_pointwise` | v83; 4 queries |
| `ActualFiniteBeurlingMellinDomain.lean` | `actual_log_receiver_l1_l2`, `actual_mellin_log_fourier` | v98; 4 queries |
| `ActualFractionalPartZetaSource.lean` | `actual_regularized_zeta_fraction`, `actual_zeta_fraction_integral` | v102; 4 queries |
| `ActualFiniteBeurlingMellinValue.lean` | `actual_finite_receiver_hasMellin`, `actual_finite_receiver_fourier_value` | v149; 4 queries |
| `ActualBeurlingTailEnergy.lean` | `actual_full_energy_balance`, `actual_tail_energy_le_full` | v149; 4 queries |
| `ActualBeurlingCompensatedTail.lean` | `actual_tail_mellin_integral`, `actual_tail_mellin_norm` | v149; 3 queries |

The three v149 compilation receipts distinguish the compiler duration from
the complete bounded wrapper. All quantities below are exact integers; the
wrapper measured/projected ratio is kept as an undivided pair in its receipt.

| Module | Compiler wall ns | Complete compile wrapper ns | Fixed wrapper projection ns | Group peak bytes |
|---|---:|---:|---:|---:|
| Mellin value | 8785735932 | 10712022187 | 21132554884 | 3604746240 |
| Tail energy | 7956354403 | 9783234278 | 21132554884 | 3479560192 |
| Compensated tail | 7060450145 | 8949414043 | 21132554884 | 3428233216 |

These new queue jobs used the queue's authorized (8\cdot2^{30})-byte group
limit, one Lean worker, the fixed CPU/child/deadline policy and no GPU.
Providers were reused without recompilation. All stages released quiescently.
Earlier whole-module rejections are explicitly retained as rejected
predecessors, including their `sorryAx` diagnostics; they are not counted
as accepted queries. This preparation launches no native job and changes no
resource limit.

`verify_publication.py` checks source/receipt hashes, unchanged non-import
proof bytes, all 23 literal printouts, and the atlas/index consuming paths.
It is a publication-integrity check, **not** a Lean compiler. The complete
compiled caches, ordered import graphs and machine-local control receipts
are excluded with their seals and scope stated in the receipt. Only absolute
diagnostic source-location paths are projected to canonical paths; raw
private originals are preserved. No mailbox content is published.

The recorded failures these choices avoid are carrying a located missing
source into a consumer, treating a partial query as whole-module acceptance,
dropping the exterior, and answering a proof failure with a larger limit.
The minimal three prerequisite owners are included because main previously
had none of them; they are not compatibility wrappers or a second source
framework.

## What remains open

The exact finite transform and nonnegative energy identity do not establish
a signed norm upper bound or convergence for an arithmetic coefficient
family. They do not prove a Mertens bound, RH, a de Bruijn–Newman upper bound,
zero-only denominator/phase control, or the complete actual-current bound
including completion and opposite receiver flux. Those analytic obligations
remain in #62. No separate summability or favorable cancellation of the
pieces of that complete expression is inferred here.
