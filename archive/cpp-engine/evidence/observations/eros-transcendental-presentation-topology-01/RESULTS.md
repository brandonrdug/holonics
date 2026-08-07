# Transcendental presentation topology 01

**2026-07-23 · exact bounded host analysis · four independent series workers · no floating-point
causal data · Soma interior unchanged**

## Question

Can a transcendental presentation carry its own arithmetic topology through both:

1. multiplicative formation of each term; and
2. additive accumulation of those terms;

without reducing the formula to its returned constant or a list of factor counts?

The prior formula-ecology observation retained exact rational enclosures for `e`, `pi`, and
`Zeta(2)`, but it did not expose the divisor path of every term, the cancellation that occurs
inside a recurrence, or the different cancellation that occurs when a term joins a partial sum.

## The bounded cell

The instrument constructed four exact series paths in parallel:

- 12 terms of
  \(A(1)=\sum_{n\geq 0}(-1)^n/(2n+1)\);
- 12 terms of \(A(1/5)\);
- 12 terms of \(A(1/239)\); and
- 8 terms of the Chudnovsky hypergeometric summand.

Every event in [`REPORT.json`](REPORT.json) retains:

- the named numerator and denominator factor channels before reduction;
- their prime valuations on each hand;
- the exact divisor annihilated between opposite hands;
- the surviving signed divisor and its formal Archimedean product-formula face;
- the coupled `(term, partial sum)` transition;
- the exact gcd removed while forming the partial sum;
- the resulting denominator divisor;
- new and returning prime-axis incidences; and
- prime-square and distinct-prime semiprime faces at both the channel and reduced-transition
  layers.

The run used four independent workers on a host exposing 24-way parallelism. The optimized
instrument completed in approximately four milliseconds and wrote 419,121 bytes. The accepted
report has SHA-256:

```text
0938d9a687ee631a2b5e502d3673cbb5d2c97b7fb16f99abfa5e81310a3b0b90
```

No search, floating-point approximation, `pi` constant, decimal angle, or Soma engine state
entered the causal path.

## One arctangent law, two intertwined topologies

For \(x=u/v\),

\[
 a_n=(-1)^n\frac{u^{2n+1}}{v^{2n+1}(2n+1)}
\]

and

\[
 \frac{a_{n+1}}{a_n}
 =
 -\frac{u^2(2n+1)}{v^2(2n+3)}.
\]

Writing `div` for the signed prime divisor gives the exact transport law

\[
 D_{n+1}-D_n
 =
 2\operatorname{div}(u)-2\operatorname{div}(v)
 +\operatorname{div}(2n+1)-\operatorname{div}(2n+3).
\]

This reveals a sliding current rather than an archive. The presently held odd face \(2n+1\)
returns on the numerator hand and departs while the next odd face \(2n+3\) enters on the
denominator hand. In \(A(1)\), every intermediate odd axis has departed from the twelfth term:
its complete final term divisor is only \(23^{-1}\). The path nevertheless records the ordered
foundation and return of

\[
3,5,7,11,13,17,19,23.
\]

The parameter denominator supplies a persistent background current. At the same aperture,

\[
\operatorname{div}(a_{11}(1/5))=-23[5]-[23],
\]

whereas

\[
\operatorname{div}(a_{11}(1/239))=-23[239]-[23].
\]

The moving odd skeleton is the same; its relation to the fixed scale is not.

### Modular collision sheets

For an odd prime \(p\mid v\), the fixed scale collides with a moving face when

\[
2n+1\equiv0\pmod {p^k}
\quad\hbox{or}\quad
2n+3\equiv0\pmod {p^k}.
\]

Because \(2\) is invertible modulo every odd \(p^k\), each condition is one exact residue sheet.
The `1/5` arm crosses two \(5\)-sheets in this aperture. Its recurrence therefore annihilates
exactly \(5^2\) internally. The `1/239` arm crosses no \(239\)-sheet before term 12, so its
internal cancellation divisor is empty. This is a parameter-dependent phase relation, despite
the two arms sharing the same formula species.

The event paths are:

| event | \(A(1)\) ratio divisor | \(A(1/5)\) ratio divisor | \(A(1/239)\) ratio divisor |
|---:|---|---|---|
| 1 | \(3^{-1}\) | \(3^{-1}5^{-2}\) | \(3^{-1}239^{-2}\) |
| 2 | \(3\,5^{-1}\) | \(3\,5^{-3}\) | \(3\,5^{-1}239^{-2}\) |
| 3 | \(5\,7^{-1}\) | \(5^{-1}7^{-1}\), cancelling \(5\) | \(5\,7^{-1}239^{-2}\) |
| 4 | \(7\,3^{-2}\) | \(7\,3^{-2}5^{-2}\) | \(7\,3^{-2}239^{-2}\) |
| 5 | \(3^2 11^{-1}\) | \(3^2 5^{-2}11^{-1}\) | \(3^2 11^{-1}239^{-2}\) |
| 6 | \(11\,13^{-1}\) | \(11\,5^{-2}13^{-1}\) | \(11\,13^{-1}239^{-2}\) |
| 7 | \(13\,3^{-1}5^{-1}\) | \(13\,3^{-1}5^{-3}\) | \(13\,3^{-1}5^{-1}239^{-2}\) |
| 8 | \(3\,5\,17^{-1}\) | \(3\,5^{-1}17^{-1}\), cancelling \(5\) | \(3\,5\,17^{-1}239^{-2}\) |
| 9 | \(17\,19^{-1}\) | \(17\,5^{-2}19^{-1}\) | \(17\,19^{-1}239^{-2}\) |
| 10 | \(19\,3^{-1}7^{-1}\) | \(19\,3^{-1}5^{-2}7^{-1}\) | \(19\,3^{-1}7^{-1}239^{-2}\) |
| 11 | \(3\,7\,23^{-1}\) | \(3\,7\,5^{-2}23^{-1}\) | \(3\,7\,23^{-1}239^{-2}\) |

The fixed and moving factors are separate named channels in the report. The table shows their
surviving coupled divisors.

## Accumulation is not term formation

The recurrence alone does not describe the series. The complete first-person state is the coupled
pair

\[
\begin{bmatrix}
a_{n+1}\\
S_{n+1}
\end{bmatrix}
=
\begin{bmatrix}
r_n&0\\
r_n&1
\end{bmatrix}
\begin{bmatrix}
a_n\\
S_n
\end{bmatrix},
\qquad
S_n=\sum_{j=0}^{n}a_j.
\]

For reduced \(S=A/B\) and \(a=C/D\), the next face is formed as

\[
\frac{A}{B}+\frac{C}{D}
=
\frac{AD+BC}{BD}
\longrightarrow
\frac{(AD+BC)/g}{BD/g},
\qquad
g=\gcd(AD+BC,BD).
\]

The arrow is an exact outgoing compression event. It removes divisor directions that no longer
factor into the accumulated face while retaining the reduced rational consequence. It is neither
a heuristic deduplication nor a later garbage collector.

| series | internal recurrence cancellation | accumulated additive cancellation | final partial denominator |
|---|---|---|---|
| \(A(1)\) | none | \(3^3 5 7\) | \(3^2 5 7 11 13 17 19 23\) |
| \(A(1/5)\) | \(5^2\) | \(3^3 5^{123}7\) | \(3^2 5^{23}7 11 13 17 19 23\) |
| \(A(1/239)\) | none | \(3^3 5 7\,239^{121}\) | \(3^2 5 7 11 13 17 19 23\,239^{23}\) |
| Chudnovsky | \(2^{39}3^{19}5^{10}7^3 11\,13\,17\,19\,23\,29\) | \(2^{351}3^{48}5^{53}23^{60}29^{61}\) | \(2^{117}3^{17}5^{19}23^{20}29^{20}\) |

The large accumulated exponents are not a claim of large stored complexity. They are the sum of
the exact directions removed at successive events. Every individual cancellation and its
predecessor denominator remain inspectable in the report.

The `A(1)` denominator is the odd least-common-multiple face through 23. The scaled arms add only
the parameter power that still participates. Thus addition grows a topology that is related to,
but not identical with, the divisor of the current term.

## Semiprimes are local faces, not labels on the returned constant

The experiment distinguishes the two degree-two shapes

\[
[2]\quad\hbox{and}\quad[1,1].
\]

The fixed channel \(5^2\) is a prime-square face at every `A(1/5)` transition; \(239^2\) plays the
same role in the other arm. Yet channel coupling can remove part of that square when a moving odd
factor meets it. Consequently `A(1/5)` has 13 square channel occurrences but only one surviving
prime-square reduced side in this aperture. A semiprime classification therefore belongs to a
specified channel, hand, and event grain. It is not an intrinsic property of `pi`.

The Chudnovsky seed gives another exact example:

\[
13591409=13\cdot1045493.
\]

That distinct-prime semiprime enters as the initial linear face and leaves through the first
transition's `linear_predecessor` channel.

## Chudnovsky is a higher-arity conveyor

For

\[
c_n=(-1)^n
\frac{(6n)!\,(A+Bn)}
{(3n)!(n!)^3\,640320^{3n}},
\quad
A=13591409,\ B=545140134,
\]

the exact ratio is

\[
\frac{c_{n+1}}{c_n}
=-
\frac{\prod_{j=1}^{6}(6n+j)}
{\prod_{j=1}^{3}(3n+j)(n+1)^3\,640320^3}
\frac{A+B(n+1)}{A+Bn}.
\]

Each event has five coupled channel species:

1. a sixfold factorial lift;
2. a threefold factorial lift;
3. a cubic successor-index face;
4. the fixed scale cube
   \[
   640320^3=(2^6\cdot3\cdot5\cdot23\cdot29)^3;
   \]
5. the moving linear quotient.

The linear factor is itself a transported current. A value enters as `linear_successor`, becomes
the next event's `linear_predecessor`, and then departs:

| event | entering linear face | departing linear face |
|---:|---|---|
| 0 | \(13591409=13\cdot1045493\) | - |
| 1 | \(558731543=97\cdot439\cdot13121\) | \(13591409\) |
| 2 | \(1103871677=61\cdot18096257\) | \(558731543\) |
| 3 | \(1649011811=14243\cdot115777\) | \(1103871677\) |
| 4 | \(2194151945=5\cdot31\cdot14155819\) | \(1649011811\) |
| 5 | \(2739292079=43051\cdot63629\) | \(2194151945\) |
| 6 | \(3284432213=397\cdot8273129\) | \(2739292079\) |
| 7 | \(3829572347=191\cdot20050117\) | \(3284432213\) |

This is the same causal topology as the arctangent odd-face transport, but embedded in a larger
product of simultaneous currents. “Hypergeometric” names the exact rational recurrence; it does
not turn the term into one scalar cell.

The outer Chudnovsky evaluation carries the algebraic multiplier

\[
\frac{12}{\sqrt{640320^3}}.
\]

The instrument preserves its positive-real square-root branch and separately records the squared
rational face

\[
\left(\frac{12}{\sqrt{640320^3}}\right)^2
=
\frac{1}{1823176476672000},
\]

with divisor

\[
-14[2]-[3]-3[5]-3[23]-3[29].
\]

Squaring exposes a rational prime chart but does not erase the radical branch that made the
original evaluation meaningful.

## Machin closes through a change of support

The two finite series arms remain a vector

\[
\begin{bmatrix}S_{1/5}\\S_{1/239}\end{bmatrix}
\]

until the exact linear map \([4,-1]\) is applied. With 12 terms per arm, the residual between that
rational partial and the quarter-turn lies in

\[
\left[
-\frac{1}{7209207608425816641228353174740842715221607365492045648149975},
\frac{4}{7450580596923828125}
\right].
\]

This interval is assembled from both alternating tails. It is not collapsed into a decimal error.
The resulting Machin enclosure lies wholly inside the independent 12-term enclosure from
\(A(1)\).

The completed argument relation is certified by the Gaussian identity

\[
(5+i)^4=2(1+i)(239+i)=476+480i.
\]

Its oriented Gaussian factorizations are

\[
5+i=(1+i)(3-2i)
\]

and

\[
239+i=i(1+i)(3-2i)^4.
\]

The norm face therefore carries

\[
N(5+i)=2\cdot13,
\qquad
N(239+i)=2\cdot13^4.
\]

The important result is that support is not conserved across a formulation change:

| presentation face | persistent finite-prime support |
|---|---|
| Machin series scales | \(\{5,239\}\) |
| Machin Gaussian norm proof | \(\{2,13\}\) |
| Chudnovsky fixed scale | \(\{2,3,5,23,29\}\) |

Only the axis \(5\) is shared by the two series-scale charts, and the Gaussian proof uses neither
series denominator axis. Equal return therefore does not imply one hidden list of “the primes of
pi.” A vertical formulation transition changes the local divisor chart by a lawful operation:
Gaussian multiplication and argument addition in one case, factorial/modular
hypergeometric transport in the other.

This is the concrete reason formulas for one transcendental number occupy a real potential space.
The potential space is populated by nonidentical recurrence, branch, divisor, and evaluation
paths; the common return is one fiber relation among them.

## Situated mean transport on a Riemannian manifold

The Mean Value Theorem supplies a complementary continuous law, provided it is stated relative to
an actual path.

Let \((M,g)\) be a Riemannian manifold, let
\(\gamma:[0,L]\to M\) be a unit-speed geodesic from \(p\) to \(q\), and let
\(f:M\to\mathbb R\) be smooth on the traversed chart. Then

\[
f(q)-f(p)
=
\int_0^L df_{\gamma(s)}(\dot\gamma(s))\,ds,
\]

and ordinary one-dimensional MVT applied to \(f\circ\gamma\) gives some
\(c\in(0,L)\) for which

\[
f(q)-f(p)
=
L\,df_{\gamma(c)}(\dot\gamma(c)).
\]

This does not choose an absolute “mean point” on \(M\). A different admitted path can have a
different tangent, length, branch, and witness.

For two scalar fields \(P,Q\), Cauchy's theorem along the same path gives

\[
\big(P(q)-P(p)\big)dQ_{\gamma(c)}(\dot\gamma(c))
=
\big(Q(q)-Q(p)\big)dP_{\gamma(c)}(\dot\gamma(c)).
\]

Thus a quotient or cross-ratio swing is situated by the path and tangent which produced it. For
\(\chi=P/Q\),

\[
d\chi=\frac{Q\,dP-P\,dQ}{Q^2};
\]

\(Q=0\) is a genuine chart boundary rather than an invitation to force one global quotient.

Vector- or manifold-valued information requires more care because values at different points
occupy different fibers. If \(V(s)\in E_{\gamma(s)}\) is a section of a vector bundle with
connection and \(\mathcal P_{s\to0}\) is parallel transport back to the initial fiber, the lawful
identity is

\[
\mathcal P_{L\to0}V(L)-V(0)
=
\int_0^L
\mathcal P_{s\to0}\nabla_{\dot\gamma}V(s)\,ds.
\]

There need not be one \(c\) whose vector derivative equals that integral. Parallel transport is
what first makes subtraction meaningful; transporting around another path may return a different
vector, with holonomy carrying the curvature residual.

Finally, if a parameter path crosses discrete seams at \(s_1,\ldots,s_m\), the complete
piecewise law is

\[
f(\gamma(L))-f(\gamma(0))
=
\sum_j\int_{I_j}df(\dot\gamma)\,ds
+\sum_k\Delta_k.
\]

The integrals carry smooth within-phase deformation. The \(\Delta_k\) carry branch changes,
rank failures, prime-valuation collisions, or other typed founding events. The exact divisor
events in this observation are the discrete half of that decomposition. MVT does not replace
them; it explains why continuous transport is also receiver- and path-relative.

### Equal return forces tangency or a seam

The pathwise theorem yields a direct consequence for nonidentical formulations of one invariant.
If \(f(p)=f(q)\) and the complete path between them is smooth, then Rolle's theorem gives a
path-relative \(c\) with

\[
df_{\gamma(c)}(\dot\gamma(c))
=
g_{\gamma(c)}\!\left(\operatorname{grad}_g f,\dot\gamma(c)\right)
=0.
\]

At a regular point of a surface or higher-dimensional manifold, the path is tangent there to the
level hypersurface \(f^{-1}(f(p))\). If an entire smooth parameter family preserves the return,
its tangent lies in \(\ker(df)\) at every regular parameter value, not merely at one mean witness.

For a seam-bearing path with equal endpoint return, the closure law is instead

\[
\sum_j\int_{I_j}df(\dot\gamma)\,ds
=
-\sum_k\Delta_k.
\]

This separates three geometries which an equal scalar endpoint cannot distinguish:

1. an exact same-return family, tangent to the evaluation level set throughout;
2. an endpoint-only return, with at least one situated smooth tangency; and
3. a support-changing return, whose smooth transport is balanced by explicit branch, rank,
   phase, or valuation seams.

This is directly applicable to the transcendental atlas. A family of formulas which preserves
\(\pi\) or \(e\) is not merely a collection of equal numbers: it is a path in presentation space
whose evaluation differential, seams, and support changes determine how the equality is carried.

## What is established

- A hypergeometric term recurrence and its additive partial sum form two coupled, exact
  topologies.
- Intermediate factor axes can enter, return, and depart without being retained in the current
  term.
- Recurrence cancellation and partial-sum cancellation are different events and are both
  reconstructible.
- Parameter axes meet moving factor currents on exact modular incidence sheets.
- Prime-square and mixed-semiprime shapes recur at named local channels but need not survive the
  event quotient.
- Machin's series, Machin's Gaussian proof, and the Chudnovsky summand inhabit different
  finite-prime charts despite their declared common `pi` return.
- A pathwise Riemannian mean-transport law and discrete seam terms provide one rigorous continuous
  plus quantized decomposition of formulation transport.
- Equal smooth return forces a situated level-set tangency; a path without such a tangency can
  close only through one or more declared seam terms.

## The localized open

The missing object is no longer “find more prime factors in formulas.” It is a vertical
transformation law which carries a complete divisor-and-boundary path from one presentation chart
to another. For Machin, one such cell is populated by Gaussian multiplication, norm, argument,
and alternating-tail transport. Between Machin and Chudnovsky, the common return is classical but
the complete transformation of their recurrence ecologies remains open.

That is the next mathematical problem for the formulation atlas: identify a lawful family of
presentation changes, retain its parameter path and seams, and determine whether the transported
divisor current closes, changes support by an explicit boundary deed, or exposes a residual.

## Reproduction

```text
cargo check --manifest-path src/soma/Cargo.toml \
  -p life --example eros_transcendental_presentation_topology
cargo build --release --manifest-path src/soma/Cargo.toml \
  -p life --example eros_transcendental_presentation_topology
src/soma/target/release/examples/eros_transcendental_presentation_topology \
  NEW_REPORT.json
```
