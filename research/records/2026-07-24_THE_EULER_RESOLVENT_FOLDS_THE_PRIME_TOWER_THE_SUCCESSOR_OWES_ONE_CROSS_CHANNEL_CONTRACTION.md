# THE EULER RESOLVENT FOLDS THE PRIME TOWER; THE SUCCESSOR OWES ONE CROSS-CHANNEL CONTRACTION

**Date:** 2026-07-24  
**Grade:** AUTHORIZED RH DERIVATION / NORMALIZED EULER RESOLVENT EXACT / SEMILOCAL
POISSON ADMISSION EXACT ON ITS CONVERGENCE DOMAIN / PRIME AND SONIN ENDPOINT AMPLITUDES
JOINED / SUCCESSOR POSITIVITY REDUCED TO ONE CROSS-CHANNEL CONTRACTION / CONTRACTION NOT
YET CONSTRUCTED / SUPPORT CONTINUATION OPEN / RH OPEN / SOMA SOURCE UNCHANGED / NO
NUMERICAL RUN

---

## 0. Present question, insufficiency, observable, and stop

The present proof question was:

> Can the arbitrary prime admission \(S\to S\cup\{p\}\) be realized on one
> enlarged amplitude space whose norm balance produces both the complete
> prime-power current and the turned-aperture connection?

The standing record already supplied:

- the exact completed-defect recurrence
  \[
  D_{S\cup\{p\}}(f)
  =
  D_S(f)-W_p(f*f^\sharp)-\kappa_{S,p}(f);
  \]
- the Euler successor \(J_p=I-p^{-1/2}U_{\log p}\);
- the pulled metric \(G_p=J_p^*J_p\);
- the \(G_p\)-orthogonal successor Sonin projection \(\Pi_p\);
- the exact aperture connection \(\kappa_{S,p}\);
- an independently constructed archimedean base amplitude; and
- the translated-overlap expression for every prime-power current.

This was insufficient because the two signed successor terms were still
written as corrections to an already positive carrier. Nothing showed how
they belonged to one amplitude transport, and merely defining a square root
after assuming the successor defect nonnegative would be circular.

The sought observable was therefore qualitative and operator-valued:

1. a positive endpoint amplitude whose norm change is the whole
   prime-power series;
2. a positive endpoint amplitude whose norm change is the aperture
   connection; and
3. one exact interface for the map which must carry their combined outgoing
   amplitude.

The stopping condition was the first map whose contractivity could not be
derived from the existing arithmetic operators without assuming the desired
Weil sign. No zero census, prime enumeration, floating-point matrix run,
visualization, or Soma construction entered.

---

## I. One normalized resolvent contains every prime-power return

Let \(U\) be unitary, \(0<a<1\), and define

\[
J_a=I-aU,\qquad
G_a=J_a^*J_a,\qquad
d_a=\sqrt{1-a^2}.
\]

Because \(\|aU\|=a<1\), the normalized Euler resolvent

\[
\mathcal R_a
=
d_aJ_a^{-1}
=
d_a\sum_{n\ge 0}a^nU^n
\tag{I.1}
\]

exists in operator norm. Since \(J_a\) is normal,

\[
\mathcal R_a^*\mathcal R_a
=
(1-a^2)G_a^{-1}.
\tag{I.2}
\]

Expanding both inverses gives

\[
(1-a^2)
\sum_{r,s\ge0}a^{r+s}U^{s-r}
=
I+\sum_{m\ge1}a^m(U^m+U^{*m}).
\tag{I.3}
\]

For

\[
a=p^{-1/2},
\qquad
U=U_{\log p},
\qquad
\ell_p=\log p,
\]

the previously derived prime-power aperture-incidence identity turns
(I.3) into

\[
\boxed{
W_p(f*f^\sharp)
=
\ell_p
\left(
  \|\mathcal R_pL_Rf\|^2-\|L_Rf\|^2
\right).
}
\tag{I.4}
\]

Equation (I.4) folds the complete repeated-prime population into one
endpoint change. The terms \(p^m\) are not separate stored constituents.
They are the feedback turns of the one inverse \(J_p^{-1}\).

This does **not** sign \(W_p\). For the translation representation,

\[
\|\mathcal R_a\|^2
=
\frac{1+a}{1-a}>1,
\tag{I.5}
\]

so the observed prime channel expands some modes.

---

## II. The return is the state of a lossless two-port passage

Define

\[
\mathcal J_a
=
\begin{pmatrix}
aU & d_aI\\
d_aI & -aU^*
\end{pmatrix}.
\tag{II.1}
\]

Direct multiplication gives

\[
\mathcal J_a^*\mathcal J_a=I.
\tag{II.2}
\]

The fixed-state equation in its first port,

\[
s=aUs+d_ax,
\tag{II.3}
\]

has the unique solution

\[
s=\mathcal R_ax.
\tag{II.4}
\]

Thus the expansive observed resolvent is already the compression of a
lossless larger relation. This is the correct type of geometry for the
successor proof: a signed local response can be the face of a conservative
larger passage. It does not follow that the completed arithmetic passage has
already been found.

---

## III. Prime admission is exactly the Euler difference on the semilocal population

For a finite receiver \(S\), let

\[
\mathcal M_S
=
\{m\ge1:q\nmid m\text{ for every finite }q\in S\},
\]

and on a domain where the following sum converges absolutely define

\[
(\mathcal E_Sf)(x)
=
|x|^{1/2}
\sum_{m\in\mathcal M_S}f(mx).
\tag{III.1}
\]

For \(p\notin S\),

\[
\mathcal M_S
=
\mathcal M_{S\cup\{p\}}
\mathbin{\dot\cup}
p\mathcal M_S.
\tag{III.2}
\]

If

\[
(V_p\phi)(x)=\phi(px)
\]

on \(L^2(\mathbb R_+^*,d^*x)\), then (III.2) gives

\[
\boxed{
\mathcal E_{S\cup\{p\}}
=
(I-p^{-1/2}V_p)\mathcal E_S
=
J_p\mathcal E_S.
}
\tag{III.3}
\]

Consequently

\[
\boxed{
\mathcal R_p\mathcal E_{S\cup\{p\}}
=
\sqrt{1-p^{-1}}\mathcal E_S.
}
\tag{III.4}
\]

This is the causal population identity behind the Euler metric:

- admitting \(p\) removes the \(p\)-divisible sheet from the predecessor
  population;
- the inverse Euler return reconstructs the predecessor population from the
  admitted one; and
- its feedback expansion produces the complete \(p^m\) tower.

The elementary partition (III.2) is exact. The further global Poisson
summation relation is additional: it joins this multiplicative population
to additive Fourier return and inversion, and fixes compatible
principal-value normalizations. Connes--Consani explicitly identify that
global relation as essential to a semilocal Weil-positivity route.

---

## IV. The turned aperture is also a difference of positive endpoint amplitudes

Let \(P_S\) be the predecessor orthogonal Sonin projection and let \(\Pi_p\)
be the successor projection pulled into the predecessor chart. It is
\(G_p\)-orthogonal. Therefore

\[
\widetilde P_p
=
G_p^{1/2}\Pi_pG_p^{-1/2}
\tag{IV.1}
\]

is an ordinary orthogonal projection.

When the scale-action current \(\Theta_S(f)\) commutes with the Euler metric,
trace cyclicity gives

\[
\boxed{
\kappa_{S,p}(f)
=
\|\Theta_S(f)\widetilde P_p\|_{\mathrm{HS}}^2
-
\|\Theta_S(f)P_S\|_{\mathrm{HS}}^2.
}
\tag{IV.2}
\]

Thus neither signed term in the completed recurrence is now opaque:

- \(W_p\) is the endpoint change of the normalized Euler-return amplitude;
- \(\kappa_{S,p}\) is the endpoint change of the standardized Sonin-aperture
  amplitude.

---

## V. The full successor is exactly one defect-contraction problem

Assume an independently constructed predecessor amplitude

\[
D_S(f)=\|C_{S,R}f\|^2
\tag{V.1}
\]

on a Hilbert current space where all displayed amplitude maps are bounded
and linear. Define

\[
X_{S,p,R}f
=
\left(
  C_{S,R}f,\,
  \sqrt{\ell_p}L_Rf,\,
  \Theta_S(f)P_S
\right)
\tag{V.2}
\]

and

\[
Y_{S,p,R}f
=
\left(
  \sqrt{\ell_p}\mathcal R_pL_Rf,\,
  \Theta_S(f)\widetilde P_p
\right).
\tag{V.3}
\]

Substituting (I.4) and (IV.2) into the exact defect recurrence yields

\[
\boxed{
D_{S\cup\{p\}}(f)
=
\|X_{S,p,R}f\|^2-\|Y_{S,p,R}f\|^2.
}
\tag{V.4}
\]

The following statements are therefore equivalent:

\[
D_{S\cup\{p\}}(f)\ge0\quad\text{for every admitted }f;
\tag{V.5}
\]

\[
\|Y_{S,p,R}f\|\le\|X_{S,p,R}f\|
\quad\text{for every admitted }f;
\tag{V.6}
\]

and the rule

\[
\Gamma_{S,p,R}(X_{S,p,R}f)=Y_{S,p,R}f
\tag{V.7}
\]

extends to a contraction on the closure of the range of \(X_{S,p,R}\).

If \(\Gamma_{S,p,R}\) is constructed independently, the successor amplitude
is forced:

\[
\boxed{
C_{S\cup\{p\},R}
=
(I-\Gamma_{S,p,R}^*\Gamma_{S,p,R})^{1/2}
X_{S,p,R}.
}
\tag{V.8}
\]

This is a genuine narrowing of the proof problem. It is not itself a proof
of RH, because defining \(\Gamma\) only after assuming (V.6) would be
circular.

---

## VI. The first absent object and why it must mix the channels

The first absent object is now exactly:

> an arithmetic construction of
> \(\Gamma_{S,p,R}:X_{S,p,R}f\mapsto Y_{S,p,R}f\)
> whose contractivity follows from its construction rather than from an
> assumed completed Weil sign.

It cannot be block diagonal:

1. the Euler resolvent is expansive on part of the translation spectrum;
2. the Sonin-aperture connection may change either way; and
3. the predecessor remainder is the only already positive reserve in the
   source amplitude.

A valid passage must therefore exchange amplitude among the predecessor
remainder, prime-return, and turned-aperture channels. The global Poisson
relation is the strongest known candidate source because it already joins:

- the semilocal multiplicative population \(\mathcal E_S\);
- Euler admission \(J_p\);
- additive Fourier transform;
- multiplicative inversion;
- Sonin support on a function and its Fourier return; and
- the shared principal-value normalization required by the explicit formula.

The elementary identity \(\mathcal E_{S\cup\{p\}}=J_p\mathcal E_S\) supplies
one arm of that colligation. It does not yet produce the Fourier/Sonin
off-diagonal blocks or prove the resulting map contractive.

Support growth remains a distinct dependency. The published positive
archimedean carrier begins at one bounded base aperture. A complete proof
must continue the same passage jointly through:

\[
(S,R)\longrightarrow(S\cup\{p\},R')
\]

without erasing the translated current which appears when \(p^m<R'\).

This sharpens the construction order. Algebraically, \(\Gamma_{S,p,R}\) is
the first missing map once \(C_{S,R}\) is given. Constructively, the only
published predecessor carrier is at the \(\log 2\) aperture, where every
finite-prime overlap is empty. There is therefore no presently established
nontrivial fixed-\(R\) cell on which to build \(\Gamma\). The first object
reachable from the known base must be one joint support/place colligation,
or an independently proved support continuation followed by the displayed
prime colligation. Treating the larger-support predecessor as already
available would hide the same open theorem in the input.

---

## VII. Exact next proof construction

The next proof work is bounded and has one acceptance condition.

1. Declare a common dense current domain at the first larger aperture for
   the semilocal Poisson map, additive Fourier return, multiplicative
   inversion, logarithmic-current lift, Sonin projections, and the embedded
   archimedean base amplitude.
2. Write the global Poisson intertwiner and
   \(\mathcal E_{S\cup\{p\}}=J_p\mathcal E_S\) on that same domain with the
   principal-value normalization explicit.
3. Extract simultaneously the support-extension blocks and the
   off-diagonal blocks coupling the Euler-return and Sonin-aperture channels
   to the predecessor remainder.
4. Prove, before taking any square root,
   \[
   X^*X-Y^*Y=Z^*Z
   \]
   for an independently constructed \(Z\), or stop at the first domain,
   normalization, or operator-order identity which prevents it.

Only that result would authorize the successor amplitude (V.8). Afterward,
support continuation and exhaustive assembly remain necessary before Weil
positivity—and hence RH—would follow.

---

## Source anchors

- A. Connes and C. Consani, *The Scaling Hamiltonian*,
  especially Conjecture 4.1 and §4.1 on the global and semilocal Poisson
  formula: <https://arxiv.org/abs/1910.14368>.
- A. Connes and C. Consani, *Weil positivity and trace formula, the
  archimedean place*: <https://arxiv.org/abs/2006.13771>.
- A. Connes, C. Consani, and H. Moscovici, *Zeta Spectral Triples*,
  for the contemporary semilocal Sonin-space body:
  <https://arxiv.org/abs/2310.18423>.

## Deposited mathematical objects

- `mathematics/lemmas/normalized-euler-resolvent-return.typ`
- `mathematics/theorems/semilocal-successor-defect-contraction.typ`
- `mathematics/catalogue.typ`
- `papers/riemann-receiver-geometry/main.typ`

No Soma engine source changed.
