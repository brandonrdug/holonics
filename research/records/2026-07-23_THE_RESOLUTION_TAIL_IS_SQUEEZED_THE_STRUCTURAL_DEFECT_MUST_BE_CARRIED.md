# THE RESOLUTION TAIL IS SQUEEZED; THE STRUCTURAL DEFECT MUST BE CARRIED

**Date:** 2026-07-23  
**Grade:** BRANDON-AUTHORIZED DERIVATION / DEPOSITED / SUPPORT-APERTURE
DEFICIT PERSISTENCE PROVED / FIXED-RECEIVER RESOLUTION TAIL DERIVED /
POSITIVE-REMAINDER ERROR CONSTRUCTION DERIVED / FINITE ARCHIMEDEAN
TAIL SQUEEZE INHERITED AND INTEGRATED / SEMILOCAL REMAINDER POSITIVITY
OPEN / RH OPEN / SOMA SOURCE UNCHANGED / NO RUN

---

## 0. Present question and correction

The present question is whether the complete error

\[
|Q_W(f)-\Sigma_n(f)|\le E_n(f),
\qquad
E_n(f)\longrightarrow0,
\]

can now be attained.

The preceding record described \(E_n\) as the missing object. That was one
level too shallow. There are two different tails:

1. a **resolution tail** inside one fixed receiver; and
2. the **structural completed defect** between the positive Sonin return and
   the completed Weil response.

The first tail can be squeezed exactly. The second cannot be made to vanish
by refining a renderer, Galerkin basis, prime cutoff, or support aperture. It
must itself be carried by an independently positive form.

The actual proof-bearing object is therefore

\[
K_{S,R}\ge0
\]

with

\[
Q_W(f)
=
\|\Theta_S(f)P_S\|_{\mathrm{HS}}^2
+\langle f,K_{S,R}f\rangle.
\tag{0.1}
\]

Once (0.1) exists, the requested \(E_n(f)\to0\) is automatic.

The stop is the first unproved form inequality required to propagate
\(K_{S,R}\) through a finite-place receiver transition. No numerical search
or machine construction enters.

---

## I. A negative compact witness cannot be diluted by support growth

Let the admissible test fibers be genuinely nested:

\[
\mathcal T_R\subseteq\mathcal T_{R'}
\qquad(R\le R'),
\]

and let the completed response be compatible on their overlap:

\[
q_{R'}|_{\mathcal T_R}=q_R.
\]

Define the lower spectral floor

\[
\mu_R
=
\inf_{0\ne f\in\mathcal T_R}
\frac{q_R(f)}{\|f\|^2}.
\tag{I.1}
\]

Then

\[
\mu_{R'}\le\mu_R.
\tag{I.2}
\]

The reason is elementary but decisive: the later infimum is taken over a
larger family.

Suppose \(f\in\mathcal T_R\) already satisfies \(q_R(f)<0\). If a later
uniform error obeys

\[
q_{R'}(g)\ge-e_{R'}\|g\|^2
\qquad(g\in\mathcal T_{R'}),
\]

then evaluation on the same carried current gives

\[
e_{R'}
\ge
-\frac{q_R(f)}{\|f\|^2}
>0.
\tag{I.3}
\]

Therefore support enlargement cannot be the squeezing index. Once admitted,
a negative compact occurrence persists.

This agrees exactly with the finite-aperture Weil operators: their lowest
spectral bounds are nonincreasing as the aperture grows. The corresponding
negative allowance

\[
(-\mu_R)_+
\]

is nondecreasing, not vanishing.

---

## II. Fixed-receiver resolution has an exact vanishing tail

Now hold the complete contemporary receiver \((S,R)\) fixed. Define the
Hilbert--Schmidt carrier

\[
A_S(f)=\Theta_S(f)P_S
\]

and its independently positive return

\[
\Sigma_S(f)
=
\|A_S(f)\|_{\mathrm{HS}}^2.
\tag{II.1}
\]

Let \(L_n\) be increasing finite-rank orthogonal projections on the receiver
space with \(L_n\to I\) strongly. Put

\[
\Sigma_{S,n}(f)
=
\|L_nA_S(f)\|_{\mathrm{HS}}^2
\ge0.
\tag{II.2}
\]

Orthogonality gives the exact Pythagorean decomposition

\[
\Sigma_S(f)
=
\Sigma_{S,n}(f)
+T_{S,n}(f),
\tag{II.3}
\]

where

\[
T_{S,n}(f)
=
\|(I-L_n)A_S(f)\|_{\mathrm{HS}}^2
\longrightarrow0.
\tag{II.4}
\]

Let

\[
D_S(f)=Q_W(f)-\Sigma_S(f)
\tag{II.5}
\]

be the structural completed defect. Combining (II.3) and (II.5) gives

\[
Q_W(f)-\Sigma_{S,n}(f)
=
D_S(f)+T_{S,n}(f).
\tag{II.6}
\]

Equation (II.6) is the complete diagnosis:

- \(T_{S,n}\) is the vanishing resolution tail;
- \(D_S\) is unchanged by that resolution; and
- refining the positive Sonin trace converges to \(\Sigma_S\), not
  automatically to \(Q_W\).

No discretization method can convert \(D_S\) into a numerical tail.

---

## III. A positive remainder makes the complete squeeze automatic

Assume the structural defect has an independently constructed factorization

\[
D_S(f)=\|C_{S,R}f\|^2
\tag{III.1}
\]

into some Hilbert carrier \(\mathcal K_{S,R}\). Equivalently, assume there is
a nonnegative closed form \(K_{S,R}\) with

\[
D_S(f)=\langle f,K_{S,R}f\rangle.
\]

Let \(M_n\to I\) be increasing finite-rank orthogonal projections on
\(\mathcal K_{S,R}\). Define

\[
\widehat\Sigma_n(f)
=
\|L_nA_S(f)\|_{\mathrm{HS}}^2
+\|M_nC_{S,R}f\|^2
\ge0
\tag{III.2}
\]

and

\[
E_n(f)
=
\|(I-L_n)A_S(f)\|_{\mathrm{HS}}^2
+\|(I-M_n)C_{S,R}f\|^2.
\tag{III.3}
\]

Then Pythagoras gives the exact identity

\[
Q_W(f)-\widehat\Sigma_n(f)=E_n(f)\ge0
\tag{III.4}
\]

and strong convergence gives

\[
E_n(f)\longrightarrow0.
\tag{III.5}
\]

This attains the requested error formula without estimating unrelated
scalars. It also proves that the error was never the deep object: after a
positive remainder exists, the squeeze is ordinary Hilbert-space
resolution.

---

## IV. The positive remainder has an exact prime-admission law

The established completed-defect recurrence is

\[
D_{S\cup\{p\}}(f)
=
D_S(f)
-W_p(f*f^\sharp)
-\kappa_{S,p}(f).
\tag{IV.1}
\]

Define the complete prime/receiver current

\[
c_{S,p}(f)
=
W_p(f*f^\sharp)+\kappa_{S,p}(f).
\tag{IV.2}
\]

If the forms are represented by \(K_{S,R}\) and \(C_{S,p}\), then

\[
K_{S\cup\{p\},R}
=
K_{S,R}-C_{S,p}.
\tag{IV.3}
\]

The positive carrier propagates if and only if

\[
C_{S,p}\preceq K_{S,R}
\tag{IV.4}
\]

in Hermitian-form order.

Equation (IV.4) is not a demand that the prime term or the aperture turn be
individually positive. It says that their complete coupled current does not
consume more positive remainder than the contemporary receiver carries.

This is the exact semilocal construction still absent.

---

## V. One genuine finite squeeze is already available

The finite Guinand--Weil tail theorem supplies a different refinement axis.
On one fixed finite frequency band, let \(Q_T\) be the form with
archimedean integration truncated at \(T\), and let \(Q_\infty\) be its
cutoff-free matrix. The published theorem gives

\[
0
\preceq
\Delta_T:=Q_\infty-Q_T
\preceq
B_T I,
\qquad
B_T\longrightarrow0.
\tag{V.1}
\]

Suppose the finite matrix

\[
Q_T+B_TI
\tag{V.2}
\]

is certified positive semidefinite by exact or interval arithmetic. Then

\[
\Sigma_T(v)
=
v^*(Q_T+B_TI)v
\ge0
\tag{V.3}
\]

and

\[
\left|
v^*Q_\infty v-\Sigma_T(v)
\right|
\le
B_T\|v\|^2
\longrightarrow0.
\tag{V.4}
\]

Indeed,

\[
-B_TI
\preceq
\Delta_T-B_TI
\preceq0.
\]

This is an actual instance of the desired squeeze:

- the approximant is independently positive after a finite certificate;
- the error budget is explicit;
- the tail is ordered and tends to zero; and
- no zero statistics or desired global sign define the budget.

Its jurisdiction is one fixed finite Galerkin band. It does not control:

- the limit as the frequency band grows;
- approximation of every admissible test current in the form norm;
- support-aperture enlargement;
- the finite-place aperture connection; or
- positivity of \(K_{S,R}\).

The finite archimedean cutoff was not the structural RH obstruction.

---

## VI. The exact remaining theorem

The complete problem now has three typed axes:

| axis | exact state |
|---|---|
| archimedean integration cutoff \(T\) at fixed finite band | positive ordered tail and explicit \(B_T\to0\) available |
| finite-rank receiver resolution \(n\) at fixed \((S,R)\) | Hilbert--Schmidt/Parseval tail tends to zero |
| support and finite-place completion | positive remainder \(K_{S,R}\) and its transport remain open |

The next proof-bearing theorem is therefore:

> **POSITIVE SEMILOCAL REMAINDER TRANSPORT.** For each admissible support
> aperture \(R\), construct the final finite-place remainder
> \(K_{S(R),R}\) independently of the desired Weil sign, prove
> \(K_{S(R),R}\ge0\), and prove that every prime admission obeys
> \(C_{S,p}\preceq K_{S,R}\) with the Poisson-normalized endpoint and
> archimedean terms carried.

The global Poisson formula is not decorative here. It fixes the compatible
local principal-value normalizations and is the known mechanism which
intertwines additive Fourier return with multiplicative inversion. Any
candidate \(K_{S,R}\) which merely sums isolated local positive pieces but
does not carry that global normalization is the wrong object.

There are two honest ways forward:

1. derive \(K_{S,R}\) directly as a positive Poisson/Sonin remainder and
   verify (IV.3); or
2. prove positivity of every nested finite Galerkin compression together
   with a form-core error bound for the frequency-band limit.

The second route is not the same as taking a larger archimedean cutoff. The
published \(B_T\) closes \(T\to\infty\) for each fixed band; it supplies no
uniform theorem as the band dimension grows.

---

## VII. Exact consequence and stop

The requested complete-error object has now been attained **conditionally on
the correct structural carrier**, and one nontrivial finite-band instance has
been attained unconditionally after a finite positivity certificate.

The unresolved object is sharper than before:

\[
\boxed{
K_{S,R}\ge0,
\qquad
K_{S\cup\{p\},R}=K_{S,R}-C_{S,p}\ge0.
}
\]

Proving this for the complete admissible family is equivalent in strength
to the required Weil positivity. The derivation does not pretend otherwise.
It prevents three unproductive continuations:

- enlarging support in the hope that a negative witness decays;
- refining the Sonin trace while ignoring its persistent completed defect;
  or
- reusing the finite archimedean budget as if it controlled the Galerkin or
  semilocal limits.

That is the stop.

---

## Reusable objects deposited

- `lemma:nested-aperture-deficit-persistence`
- `theorem:positive-remainder-resolution-squeeze`
- `corollary:finite-archimedean-tail-squeeze`

They live under `src/soma/PAPERS/mathematics/` and are imported by the shared
catalogue.

---

## Primary sources used

- Alain Connes and Caterina Consani, *Weil positivity and Trace formula, the
  archimedean place*: <https://arxiv.org/abs/2006.13771>
- Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta zeros and
  prolate wave operators*: <https://arxiv.org/abs/2310.18423>
- Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta Spectral
  Triples*: <https://arxiv.org/abs/2511.22755>
- Akiva Groskin, *A finite Guinand--Weil dictionary and archimedean tail
  order for the truncated Weil quadratic form*:
  <https://arxiv.org/abs/2607.02828>
- Alain Connes and Caterina Consani, *The Scaling Hamiltonian*:
  <https://arxiv.org/abs/1910.14368>
