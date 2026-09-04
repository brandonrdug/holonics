# The quotient family obstructs proportional descendant transport

## Status

Exact analytic derivation from the deposited kernel asymptotic and arithmetic
weight formula.  The finite transport implication and the cross-multiplied
quotient re-indexing are checked in Lean.  The incomplete-Beta asymptotic,
prime harmonic divergence, and real-power estimates are not yet encoded in
Lean.

This result rejects one proposed transport.  It does not reject arbitrary
divisor-supported transport and does not prove or disprove the Riemann
Hypothesis.

## 1. Receiver-relative quotient coordinates

Fix

\[
0<\omega<\frac12
\]

and write

\[
G_\omega(r)=g_\omega^{\langle1\rangle}(r).
\]

Let \(y_\omega\in(0,1)\) be its unique sign seam.  Thus \(G_\omega\) is
negative on \((0,y_\omega)\) and positive on \((y_\omega,1)\).

At a finite scale \(x\), fix a positive receiver cell \(m\) and put

\[
s=\frac{m}{x}\in(y_\omega,1].
\]

Every old divisor \(n\mid m\) has a unique quotient

\[
k=\frac{m}{n},\qquad n=\frac{m}{k}.
\]

Its old-cell condition is

\[
\frac{n}{x}=\frac{s}{k}<y_\omega,
\qquad\text{equivalently}\qquad
k>\frac{s}{y_\omega}.
\]

The positive descendants of \(n\) are \(n\ell\), where

\[
y_\omega<\frac{n\ell}{x}\le1.
\]

In the receiver's quotient frame this is exactly

\[
\frac{y_\omega k}{s}<\ell\le\frac{k}{s}.
\]

`QuotientFamily.lean` certifies the corresponding integer statements without
division by cross-multiplying an exact rational seam.

## 2. The arithmetic coefficient left after re-indexing

The source weight is

\[
c_\omega(n)
=
n^\omega\prod_{p\mid n}(1-p^{-2\omega}).
\]

Consequently,

\[
\rho_\omega(\ell;n)
:=
\frac{c_\omega(n\ell)}{c_\omega(n)}
=
\ell^\omega
\prod_{\substack{p\mid\ell\\p\nmid n}}
(1-p^{-2\omega}).
\]

A prime already present in \(n\) does not found its Euler factor again.
In particular,

\[
0<\rho_\omega(\ell;n)\le\ell^\omega.
\]

The descendant capacity, divided by the old cell's own weight, is therefore

\[
\frac{Z_{\omega,x}(n)}{c_\omega(n)}
=
\sum_{y_\omega k/s<\ell\le k/s}
\rho_\omega\!\left(\ell;\frac{m}{k}\right)
G_\omega\!\left(\frac{s\ell}{k}\right).
\]

The normalized demand contributed to \(m\) by the quotient axis \(k\) is

\[
R_{\omega,s,m}(k)
=
\frac{\left|G_\omega(s/k)\right|}
{\displaystyle
 \sum_{y_\omega k/s<\ell\le k/s}
 \rho_\omega(\ell;m/k)
 G_\omega(s\ell/k)}.
\]

Thus the proportional congestion has the exact quotient-family form

\[
\mathcal C_{\omega,x}(m)
=
\sum_{\substack{k\mid m\\s/k<y_\omega}}
R_{\omega,s,m}(k).
\]

This separates the geometric variables \((\omega,s,k,\ell)\) from arithmetic
incidence, which remains only in \(\rho_\omega(\ell;m/k)\).

## 3. Every sufficiently long quotient axis has a uniform lower load

The deposited small-\(r\) asymptotic is

\[
G_\omega(r)
=
-A_\omega r^{\omega-1}+O(r^{-1/2}),
\qquad A_\omega>0.
\]

Because \(\omega-1<-1/2\), there is \(r_0>0\) such that

\[
|G_\omega(r)|
\ge
\frac{A_\omega}{2}r^{\omega-1}
\qquad(0<r<r_0).
\]

Also let

\[
M_\omega=\max_{y_\omega\le r\le1}G_\omega(r).
\]

For all sufficiently large \(k\), uniformly in
\(s\in(y_\omega,1]\),

\[
\begin{aligned}
\frac{Z_{\omega,x}(m/k)}{c_\omega(m/k)}
&\le
M_\omega
\sum_{\ell\le k/s}\ell^\omega\\
&\le
M_\omega\left(\frac{k}{s}\right)^{1+\omega}.
\end{aligned}
\]

It follows that

\[
\begin{aligned}
R_{\omega,s,m}(k)
&\ge
\frac{A_\omega}{2M_\omega}
\frac{(s/k)^{\omega-1}}{(k/s)^{1+\omega}}\\
&=
\frac{A_\omega}{2M_\omega}
s^{2\omega}k^{-2\omega}\\
&\ge
B_\omega k^{-2\omega},
\end{aligned}
\]

where

\[
B_\omega
=
\frac{A_\omega y_\omega^{2\omega}}{2M_\omega}
>0.
\]

The important fact is the exponent: the receiver-relative load decays only
as \(k^{-2\omega}\), and \(2\omega<1\).

## 4. Primorial receivers overload

For every sufficiently large quotient divisor \(k\mid m\),
`FiniteTransport.lean` says that its normalized demand is an actual
nonnegative summand of the congestion at \(m\).  Hence

\[
\mathcal C_{\omega,x}(m)
\ge
B_\omega
\sum_{\substack{k\mid m\\k\ge K_\omega}}
k^{-2\omega}.
\]

Choose a square-free primorial receiver

\[
m_P=\prod_{p\le P}p
\]

and choose the scale so that \(m_P/x=s\) for any fixed
\(s\in(y_\omega,1)\).  Its complete divisor sum factors:

\[
\sum_{k\mid m_P}k^{-2\omega}
=
\prod_{p\le P}(1+p^{-2\omega}).
\]

Since \(0<2\omega<1\),

\[
\sum_p p^{-2\omega}
\ge
\sum_p\frac1p
=\infty.
\]

Therefore

\[
\prod_{p\le P}(1+p^{-2\omega})\longrightarrow\infty.
\]

Removing the finitely many divisors \(k<K_\omega\) does not change that
divergence.  Thus for every fixed \(0<\omega<1/2\), some primorial receiver
has

\[
\mathcal C_{\omega,x}(m_P)>1.
\]

## 5. Consequence

The proportional descendant flow cannot satisfy its congestion law uniformly
for any \(0<\omega<1/2\).  The candidate fails because multiplicatively rich
receivers inherit too many quotient-axis demands, not because individual old
cells lack positive descendants.

This closes the proportional branch:

- the max-flow formulation remains exact but its full Hall cut is still the
  original RH-equivalent source sign;
- local bounded-degree routing is impossible;
- globally proportional routing is obstructed by divisor entropy; and
- any useful continuation must allocate capacity non-proportionally, avoiding
  highly shared descendants or proving a different source factorization.

The result does not move the RH obligation to a new unproved scalar.  It
removes an invalid proposed carrier.
