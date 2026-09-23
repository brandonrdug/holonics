# A positive Weil-square kernel with signed prime and archimedean faces

**Status:** exact symbolic, source-derived falsifier of termwise positivity.
It is an admitted smooth compactly supported Weil-square test. It does not
construct a positive realization of the **complete** xi divisor receiver and
does not prove the Riemann hypothesis.

## Source and exact generator

Put \(\varepsilon=1/16\), \(L=\log 2\), and
\[
b_\varepsilon(x)=
\begin{cases}
\exp\!\left(-1/(1-(x/\varepsilon)^2)\right),&|x|<\varepsilon,\\
0,&|x|\geq\varepsilon.
\end{cases}
\qquad
\phi=b_\varepsilon/\sqrt{\int_{\mathbb R}b_\varepsilon^2}.
\]
Thus \(\phi\) is real, even, smooth, compactly supported and has
\(\int\phi^2=1\). For \(c\in\{-1,1\}\), let
\[
g_c(x)=\phi(x)+c\phi(x-L),\qquad
h_c(t)=\int_{\mathbb R}g_c(u+t)g_c(u)\,du.
\]
This is a two-address generator with a reflected pairing. Its bilateral
Laplace transform is
\[
G_c(s)=\Phi(s)\bigl(1+c\,e^{(s-1/2)L}\bigr),\qquad
\Phi(s)=\int_{\mathbb R}e^{(s-1/2)x}\phi(x)\,dx.
\]
The spectral transform of \(h_c\) is exactly
\[
H_c(s)=G_c(s)\overline{G_c(1-\bar s)}.
\]
Consequently \(h_c\) supplies a smooth compactly supported
[WeilTestFunction](../../../formal/elementary-holonics/ElementaryHolonics/RH/ExplicitFormulaReceiver.lean)
and a [WeilSquare](../../../formal/elementary-holonics/ElementaryHolonics/RH/WeilPositivity.lean).
On the critical line \(H_c(1/2+it)=|G_c(1/2+it)|^2\).
That identity describes the test's positive spectral **kernel**; a positive
sum over the *actual* xi divisor is the still-open source statement.

No decimal or sampled value is used. Since
\[
\log 2=\int_1^2\frac{dt}{t}>\tfrac12>2\varepsilon,
\quad
\log(3/2)=\int_1^{3/2}\frac{dt}{t}>\tfrac13>2\varepsilon,
\]
the translates are disjoint and
\(h_c(0)=2,\ h_c(L)=h_c(-L)=c,\ h_c(2L)=h_c(-2L)=0\).
The support of \(h_c\) lies in radius \(2\varepsilon\) around
\(-L,0,L\). Therefore \(h_c(\log n)=h_c(-\log n)=0\) for every
integer \(n\geq3\). The \(n=1\) von Mangoldt coefficient is zero.
The *entire* prime-power receiver, at every cutoff \(N\geq2\), has one
occupied address.

## Positive Gram and signed source terms

The address autocorrelation Gram is
\[
M_c=\begin{pmatrix}2&c\\c&2\end{pmatrix},\qquad
(a,b)M_c(a,b)^\top=(a+cb)^2+a^2+b^2,\qquad \det M_c=3.
\]
This is a valid positive Gram construction from the source word
\(1+cT\). It does **not** identify \(M_c\) with the global Weil form of xi.

Using the repository's explicit-formula sign convention, the unique
prime term is
\[
P_2(c)=\frac{\log2}{\sqrt2}\bigl(h_c(L)+h_c(-L)\bigr)
      =c\sqrt2\log2.
\]
Either sign occurs while \(M_c\) stays positive. The complete formula
contains \(-P_2\), whose sign also changes with \(c\). Hence neither
each prime term nonnegative nor each negative-prime term nonnegative
can be the missing positivity law.
More generally, for \(g_{a,b}=a\phi+b\phi(\cdot-L)\) the same source
calculation gives \(P_2(a,b)=\sqrt2\,L\,ab\). Its matrix on the two
generator coefficients is
\[
\frac{L}{\sqrt2}\begin{pmatrix}0&1\\1&0\end{pmatrix},
\]
with one positive and one negative eigenvalue. The local prime face is
an oriented cross term, even though the autocorrelation it reads is a
positive-definite kernel.

The [archimedean integrand](../../../formal/elementary-holonics/ElementaryHolonics/RH/ArchimedeanReceiver.lean)
at the exact address \(x=L\) is
\[
A_c(L)=
\frac{e^{-2L}h_c(0)-e^{-L/2}(h_c(L)+h_c(-L))/2}
     {1-e^{-2L}}
=\frac{2-2c\sqrt2}{3}.
\]
It is negative for \(c=1\) and positive for \(c=-1\). This is a
**pointwise density** statement; it says nothing by itself about the
sign of its full integral.

Even the polar face can change sign. Since \(\phi\) is real and even,
\(B=\Phi(0)=\Phi(1)>0\), and the two polar addresses together give
\[
H_c(0)+H_c(1)=B^2(4+3c\sqrt2).
\]
The \(c=-1\) value is negative because \(16<18\).

| Relative phase \(c\) | Gram determinant | \(P_2/\log2\) | \(A_c(L)\) | polar divided by \(B^2\) |
|---|---:|---:|---:|---:|
| \(-1\) | \(3\) | \(-\sqrt2\) | \((2+2\sqrt2)/3>0\) | \(4-3\sqrt2<0\) |
| \(1\) | \(3\) | \(\sqrt2\) | \((2-2\sqrt2)/3<0\) | \(4+3\sqrt2>0\) |

## Rational coefficient populations

The two signs already falsify termwise positivity. To see the population
of source configurations under a common denominator, extend the same
generator to \(c=k/d\), \(-d\leq k\leq d\). The sign of \(c\) is a
zero- or half-turn relative phase; \(|c|\) is its rational amplitude.
This is a distribution of **declared generator coefficients**, not of
xi zeros. For every rational \(c\in[-1,1]\),
\[
\begin{aligned}
h_c(0)&=1+c^2,&h_c(\pm L)&=c,\\
M_c&=\begin{pmatrix}1+c^2&c\\c&1+c^2\end{pmatrix},&
\det M_c&=1+c^2+c^4>0,\\
P_2(c)&=c\sqrt2 L,&
A_c(L)&=(1+c^2-2\sqrt2c)/3,&
H_c(0)+H_c(1)&=B^2(2+2c^2+3\sqrt2c).
\end{aligned}
\]
The exact sign partitions on this interval are:
\(P_2<0\) iff \(c<0\);
\(A_c(L)<0\) iff \(c>\sqrt2-1\);
and the polar face is negative iff \(c<-1/\sqrt2\).
No rational grid point hits either irrational threshold.

Thus the number of negative archimedean samples at denominator \(d\)
is \(d-\lfloor d(\sqrt2-1)\rfloor\), while the number of negative
polar samples is \(d-\lfloor d/\sqrt2\rfloor\). The prime face has
exactly \(d\) negative, one zero and \(d\) positive samples.

| Denominator \(d\) | Prime negative | Local arch negative | Polar negative | Total configurations |
|---:|---:|---:|---:|---:|
| \(8\) | \(8\) | \(5\) | \(3\) | \(17\) |
| \(16\) | \(16\) | \(10\) | \(5\) | \(33\) |

The receipt retains each \(k/d\), its exact Gram determinant, the
three sign readings and the joint sign-class counts. The verifier
rederives both irrational floor thresholds using only integer-square
comparisons.

## What this discriminates

The Holon has an oriented pair of logarithmic addresses, a smooth
constitutive generator, reflected autocorrelation, and several receiver
faces. Its positive Gram law survives both relative phases. The
prime, polar and local archimedean faces change sign because they read
different source transports. A successful source-specific proof would
have to realize the **joined** polar-minus-prime-minus-archimedean
functional as a positive form, preserve the exact explicit formula
and boundary limit, and remain faithful to the complete xi divisor.
Attaching independent positive labels to the three terms is refuted by
this test.

This differs from the existing 12/14-step finite Gram experiment in
[additional-claims.md](../../records/2026-09-06_portable_evidence/additional-claims.md):
that experiment encloses finite **joined** arithmetic Gram entries and
compares them with a bounded spectral population. Here the purpose is
to falsify an unlicensed *termwise* sign inference with one smooth
generator and exact algebra. Neither finite return supplies complete
xi positivity.

Run and check the machine-readable symbolic receipt:

~~~sh
python3 research/experiments/weil_positive_receiver/generate.py
python3 research/experiments/weil_positive_receiver/verify.py
~~~

The [receipt](receipt.json) contains only integers and rational
coefficients of \(\sqrt2\), with \(\log2\) retained as a positive formal
factor. The verifier independently expands the two-address source word,
checks the Gram square identity, and recomputes prime, archimedean and
polar signs by exact rational comparisons. It uses no floating point.
