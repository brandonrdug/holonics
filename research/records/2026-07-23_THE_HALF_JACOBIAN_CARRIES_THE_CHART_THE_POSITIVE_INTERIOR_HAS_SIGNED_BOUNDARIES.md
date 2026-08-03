# THE HALF-JACOBIAN CARRIES THE CHART; THE POSITIVE INTERIOR HAS SIGNED BOUNDARIES

**Date:** 2026-07-23  
**Grade:** BRANDON-AUTHORIZED CONSTRUCTION / DEPOSITED / COVARIANT COAREA
CARRIER DEFINED / CHANGE-OF-VARIABLE HALF-DENSITY EXACT / COVARIANT FTC WITH
SIGNED SEAMS EXACT / MELLIN HALF-DENSITY EXACT / EULER METRIC
HALF-JACOBIAN AND POSITIVE SUCCESSOR COMPLEMENT EXACT / DEFECT-COAREA
IDENTITY OPEN / RH OPEN / SOMA SOURCE UNCHANGED / NO RUN

---

## 0. Present question, insufficiency, artifact, and stop

The present question is how the independently positive remainder carrier

\[
Q_W(f)-\Sigma_S(f)=\|C_{S,R}f\|^2
\]

relates to the laboratory's fundamental theorem of calculus, ordinary change
of variables from Cartesian to polar coordinates, logarithmic/Mellin
coordinates, and both Riemannian and Lorentzian hyperbolic coordinates.

The previous remainder construction named the correct proof-bearing object
but remained too close to one operator chart. The standing FTC and
hyperarea records already say that a final boundary face does not reconstruct
its interior: the ordered family of fibers, normal transport, Jacobian,
orientation, and seams carry the sweep. The standing prime-rebase correction
also forbids treating receiver growth as an untouched predecessor block plus
a positive new coordinate.

The required artifact is therefore not another abstract square root and not
a positive scalar assigned to each prime. It is:

1. a receiver-local direct-integral/coarea carrier;
2. its exact half-Jacobian change-of-chart law;
3. its covariant FTC along changing receiver fibers;
4. the distinction between positive contemporary responses and signed
   connection or seam currents;
5. the exact Mellin half-density which produces the critical \(1/2\) chart;
6. the operator analogue \(G^{1/2}\) for an Euler receiver transition; and
7. the precise open identity which would make this geometry the completed
   Weil remainder rather than an adjacent positive construction.

The construction stops at that identity. It does not define the carrier from
\(D_S^{1/2}\), impose a positive contribution per prime, build an enlarged
total arithmetic field, alter Soma, or run a numerical experiment.

---

## I. The first correction: positive state does not mean positive change

Suppose a changing carrier is represented along a receiver path by a section
\(\Psi(t)\) of a Hilbert bundle. Its contemporary response is

\[
D(t)=\|\Psi(t)\|^2\ge 0.
\]

For a metric-compatible connection,

\[
\frac{d}{dt}D(t)
=
2\operatorname{Re}
\left\langle
\Psi(t),\nabla_{\partial_t}\Psi(t)
\right\rangle.
\tag{I.1}
\]

The right-hand side can have either sign. A family of nonnegative norms can
grow, shrink, or turn without becoming negative. If the receiver path crosses
seams \(t_k\), the complete FTC is

\[
\begin{aligned}
\|\Psi(b)\|^2-\|\Psi(a)\|^2
&=
2\operatorname{Re}
\sum_j\int_{I_j}
\left\langle
\Psi,\nabla_{\partial_t}\Psi
\right\rangle dt\\
&\quad+
\sum_k
\left(
\|\Psi(t_k^+)\|^2-\|\Psi(t_k^-)\|^2
\right).
\end{aligned}
\tag{I.2}
\]

This is the correct relation to the exact prime recurrence

\[
D_{S\cup\{p\}}(f)-D_S(f)
=
-W_p(f*f^\sharp)-\kappa_{S,p}(f).
\tag{I.3}
\]

Equation (I.3) is a signed seam current between two contemporary responses.
It is not required to be positive. The requirement is instead that both
endpoint defects admit independently constructed positive carrier faces.

This corrects an overly restrictive first intuition: writing each prime
seam as a new positive square would impose monotonicity which the established
receiver geometry neither requires nor supports. Positivity belongs to the
complete contemporary interior. Loss, boundary motion, and connection
currents describe how that interior changes.

---

## II. A covariant coarea carrier

Fix one contemporary receiver \(\rho\), with admitted current space
\(\mathcal H_\rho\). Let

\[
(\Lambda_\rho,\nu_\rho)
\]

be a measured parameter region, and let

\[
\mathcal K_{\rho,\xi},
\qquad
B_{\rho,\xi}:\mathcal H_\rho\to\mathcal K_{\rho,\xi}
\]

be a measurable field of Hilbert fibers and independently specified
amplitude maps. Define

\[
(C_\rho f)(\xi)=B_{\rho,\xi}f.
\]

When this section is square-integrable,

\[
D_\rho(f)
=
\|C_\rho f\|^2
=
\int_{\Lambda_\rho}
\|B_{\rho,\xi}f\|^2\,d\nu_\rho(\xi)
\ge 0.
\tag{II.1}
\]

This is the covariant coarea carrier. Its positivity is not an assigned
label: it is the Gram response of actual fiber amplitudes.

The carrier is local to \(\rho\). A later receiver has its own parameter
region, fibers, measure, amplitudes, and connection. A temporary transport
may compare those carriers, but it does not imply that the earlier carrier
survives as an unchanged block inside a completed world.

### II.1 Coarea

Let a regular map

\[
I:M^N\to B^k
\]

have normal Jacobian \(J_I\). The coarea theorem gives

\[
\int_M g(x)J_I(x)\,dV_M(x)
=
\int_B
\left[
\int_{I^{-1}(c)}
g(x)\,dA_c(x)
\right]dc.
\tag{II.2}
\]

Thus an invariant fiber does not erase its transverse directions. They
remain as:

- the value \(c\);
- the normal bundle;
- the Jacobian \(J_I\);
- the induced fiber measure \(dA_c\);
- orientation; and
- the ordered sweep through the family of fibers.

If the desired source response uses the unweighted measure \(dV_M\), then
on a regular stratum one may put

\[
g(x)=\frac{\|\psi(x)\|^2}{J_I(x)}
\]

in (II.2). The fiber amplitude then carries the inverse half-Jacobian
\(J_I^{-1/2}\). At \(J_I=0\), this regular representation fails: the
critical locus is a typed rank/discriminant seam and owes its own term.

---

## III. Change of variables moves the Jacobian into amplitude

Let

\[
\Phi:U\to V
\]

be a regular coordinate change and let

\[
J_\Phi(u)=|\det D\Phi(u)|.
\]

For a carrier section \(b(x)\) on \(V\), define the pulled section

\[
\widetilde b(u)
=
J_\Phi(u)^{1/2}R_u b(\Phi(u)),
\tag{III.1}
\]

where \(R_u\) is the unitary identification of the corresponding output
fibers. Then

\[
\int_V\|b(x)\|^2\,dx
=
\int_U\|\widetilde b(u)\|^2\,du.
\tag{III.2}
\]

The square-root Jacobian is therefore not a scalar correction attached after
the event. It is the amplitude transformation required to carry one
quadratic response through another chart.

This gives the exact hierarchy:

\[
\text{coordinate differential }D\Phi
\longrightarrow
\text{metric }(D\Phi)^*D\Phi
\longrightarrow
\text{volume Jacobian}
\longrightarrow
\text{half-Jacobian amplitude}
\longrightarrow
\text{invariant squared response}.
\]

An invertible chart change creates no remainder. A remainder appears only
when the receiver:

- projects away fiber directions;
- truncates an aperture;
- crosses a critical/rank seam;
- identifies multiple lifts; or
- compares nonidentical contemporary carriers.

---

## IV. Cartesian and polar coordinates give an exact model

For

\[
x=r\cos\theta,
\qquad
y=r\sin\theta,
\]

the Jacobian is \(r\), so

\[
\int_{\mathbb R^2}|f(x,y)|^2\,dx\,dy
=
\int_0^\infty\int_0^\Theta
|f(r,\theta)|^2\,r\,d\theta\,dr.
\tag{IV.1}
\]

The amplitude-level chart carries \(r^{1/2}\). The polar point is therefore
not merely \((r,\theta)\); its complete comparison contains the induced
measure and branch.

The angular expansion

\[
f(r,\theta)
=
\sum_{n\in\mathbb Z}f_n(r)e^{in\theta}
\]

gives, by Parseval,

\[
\|f\|^2
=
\|f_0\|^2
+
\sum_{n\ne0}\|f_n\|^2.
\tag{IV.2}
\]

If a receiver reads only the rotationally symmetric mode \(f_0\), then

\[
\sum_{n\ne0}\|f_n\|^2
\]

is a literal positive remainder carrier: the omitted angular/winding
directions.

This model also exposes the boundary:

- away from \(r=0\) and after choosing an angular branch, polar coordinates
  are locally reversible;
- \(\theta\) and \(\theta+\Theta\) present the same Cartesian point while
  retaining different lifts;
- at \(r=0\), the Jacobian loses rank and all angular directions collapse to
  one Cartesian face.

The origin is therefore a genuine seam. Treating it as an ordinary polar
fiber with \(r=0\) would divide away the exact lost direction.

### IV.1 Radial FTC

For a disk,

\[
V(R)
=
\int_0^R\int_0^\Theta r\,d\theta\,dr,
\qquad
V'(R)=\Theta R=A(R).
\tag{IV.3}
\]

The final circle is one face. The disk interior is the ordered radius-indexed
family of circle fibers together with the normal sweep and Jacobian. This is
the finite-dimensional prototype of what a completed remainder carrier
would have to do.

---

## V. Logarithmic transport produces the Mellin half-density

Put

\[
r=e^u,
\qquad
dr=e^u\,du.
\]

Define

\[
(\mathcal U F)(u)
=
e^{u/2}F(e^u).
\tag{V.1}
\]

Then

\[
\int_0^\infty|F(r)|^2\,dr
=
\int_{-\infty}^{\infty}
|(\mathcal UF)(u)|^2\,du.
\tag{V.2}
\]

With

\[
\mathcal M F(s)
=
\int_0^\infty F(r)r^s\,\frac{dr}{r},
\]

ordinary Fourier transformation in \(u\) gives

\[
\widehat{\mathcal UF}(t)
=
\mathcal M F\!\left(\frac12-it\right).
\tag{V.3}
\]

The critical half is therefore the square-root Jacobian needed to carry an
additive \(L^2(dr)\) response into the logarithmic coordinate. On
multiplicative Haar measure \(dr/r\), the logarithmic chart already has unit
Jacobian; the half-density is the transport between those two
normalizations.

For

\[
F^\sharp(r)
=
r^{-1}\overline{F(r^{-1})},
\]

one obtains

\[
\mathcal U(F^\sharp)(u)
=
\overline{(\mathcal UF)(-u)}.
\tag{V.4}
\]

Thus inversion \(r\mapsto r^{-1}\) becomes reflection \(u\mapsto-u\), and
the line \(\operatorname{Re}s=1/2\) is the Fourier/Mellin chart where the
returned pair is a norm square.

This does not prove that every zero lies there. It proves that the \(1/2\)
has simultaneous exact faces as:

- the fixed point of \(s\mapsto1-s\);
- the half-density of logarithmic change of variables; and
- the centered balance between reciprocal scale sheets.

---

## VI. Hyperbolic coordinates separate positive measure from oriented sign

### VI.1 Riemannian hyperbolic polar coordinates

For curvature \(-1\),

\[
ds^2=d\rho^2+\sinh^2\rho\,d\theta^2,
\qquad
dA=\sinh\rho\,d\rho\,d\theta.
\tag{VI.1}
\]

The radial FTC is

\[
A(R)=\Theta\sinh R,
\qquad
V(R)=\Theta(\cosh R-1),
\qquad
V'(R)=A(R).
\tag{VI.2}
\]

This is a positive Riemannian coarea geometry. Relative to the Euclidean
factor \(r\), the hyperbolic factor \(\sinh\rho\) records how rapidly
successive boundary fibers separate. A carrier integrated over these fibers
remains a sum of squared amplitudes.

### VI.2 Lorentzian hyperbolic coordinates

In a Minkowski wedge,

\[
X=\rho\cosh\eta,
\qquad
T=\rho\sinh\eta,
\]

so

\[
dX^2-dT^2
=
d\rho^2-\rho^2d\eta^2,
\tag{VI.3}
\]

and

\[
X+T=\rho e^\eta,
\qquad
X-T=\rho e^{-\eta}.
\tag{VI.4}
\]

The reciprocal pair \(e^{\pm\eta}\) is the exact geometry already present
in the centered prime character. For

\[
x=\varepsilon\log p,
\qquad
\theta=t\log p,
\]

the two normalized sheets are

\[
A_+=e^{-x-i\theta},
\qquad
A_-=e^{x-i\theta},
\]

with

\[
C=e^{-i\theta}\cosh x,
\qquad
N=e^{-i\theta}\sinh x.
\tag{VI.5}
\]

Their positive common metric face is proportional to

\[
\cosh(2x),
\]

while the oriented sheet difference is proportional to

\[
\sinh(2x).
\]

The common face is even and positive. The coupling face is odd and changes
sign under \(x\mapsto-x\). In the \((C,N)\) carrier,

\[
|dC|^2-|dN|^2=d\theta^2-dx^2.
\tag{VI.6}
\]

The raw Lorentzian difference is therefore not a positive remainder carrier.
It records orientation between reciprocal sheets. Any positive carrier must
use a positive common/Gram pairing while retaining the hyperbolic normal
difference as connection or residual information.

This is precisely the division needed by the completed defect:

\[
\text{positive contemporary interior}
\quad\text{versus}\quad
\text{signed normal/connection change}.
\]

---

## VII. The Euler metric has an operator half-Jacobian

Let

\[
J:H\to H'
\]

be the boundedly invertible one-prime receiver transport and set

\[
G=J^*J.
\]

Its polar decomposition is

\[
J=UG^{1/2},
\qquad
U=JG^{-1/2},
\tag{VII.1}
\]

with \(U\) unitary. The positive stretch \(G^{1/2}\) is the
operator-valued analogue of a half-Jacobian:

\[
\|Jv\|_{H'}^2
=
\|G^{1/2}v\|_H^2.
\tag{VII.2}
\]

Let \(\Pi\) be the pulled-back successor projection, which is orthogonal in
the \(G\)-metric. Then

\[
\widetilde P
=
G^{1/2}\Pi G^{-1/2}
\tag{VII.3}
\]

is an ordinary orthogonal projection. Consequently,

\[
\|Jv\|^2
=
\|G^{1/2}\Pi v\|^2
+
\|G^{1/2}(I-\Pi)v\|^2.
\tag{VII.4}
\]

Equation (VII.4) is an exact positive successor decomposition. It does not
freeze the predecessor range: both terms belong to the contemporary
successor metric after transport.

For the Euler event,

\[
J=I-p^{-1/2}U_p,
\qquad
G=(1+p^{-1})I-p^{-1/2}(U_p+U_p^*).
\]

The aperture turn occurs because \(G\) need not commute with the predecessor
projection. Standardizing through \(G^{1/2}\) makes the successor
Pythagorean geometry explicit, but it does not yet identify the positive
complement in (VII.4) with the completed Weil defect.

That missing identification is now sharply typed:

- the Euler transition supplies a genuine operator half-Jacobian;
- the successor aperture supplies a genuine positive complement;
- the explicit formula supplies the exact arithmetic response;
- their equality as the complete remainder is not yet proved.

---

## VIII. The RH-specialized coarea obligation

For every final receiver \((S,R)\), the sought construction is a
receiver-local carrier

\[
C_{S,R}:
\mathcal T_{S,R}
\longrightarrow
\int_{\Lambda_{S,R}}^\oplus
\mathcal K_{S,R,\xi}\,d\nu_{S,R}(\xi)
\]

such that

\[
Q_W(f)-\Sigma_S(f)
=
\|C_{S,R}f\|^2
=
\int_{\Lambda_{S,R}}
\|B_{S,R,\xi}f\|^2\,d\nu_{S,R}(\xi)
\tag{VIII.1}
\]

for every admitted \(f\).

This identity must be constructed independently from:

- Gaussian/Poisson/theta transport;
- Mellin half-density and completed involution;
- the archimedean Sonin/prolate positive remainder;
- finite Euler receiver transport;
- support-aperture motion;
- the receiver connection; and
- all regular and critical boundary terms.

It may not be obtained by assuming \(D_S\ge0\) and taking a formal square
root.

### VIII.1 Chart covariance

Every reparameterization \(\Phi\) must carry the amplitude by

\[
B\longmapsto
|\det D\Phi|^{1/2}R_\Phi(B\circ\Phi)
\tag{VIII.2}
\]

or its appropriate coarea/Radon--Nikodym counterpart, so that (VIII.1) is
the same response rather than an equal-looking scalar from a different
occurrence.

### VIII.2 Prime seam

For \(S'=S\cup\{p\}\), after anchoring the same current in both contemporary
receivers, the endpoint carrier norms must obey

\[
\|C_{S',R}f\|^2-\|C_{S,R}f\|^2
=
-W_p(f*f^\sharp)-\kappa_{S,p}(f).
\tag{VIII.3}
\]

The right side may have either sign. Equation (VIII.3) asks the positive
carrier to reshape through the exact receiver event; it does not ask the
prime to contribute a positive cell.

### VIII.3 Support and critical seams

Smooth support motion is governed by the covariant interior term in (I.2).
Moving boundaries contribute Reynolds/FTC boundary terms. Prime-power
admissions and rank changes contribute typed jumps. Where a Jacobian
vanishes, the regular coarea expression must be replaced by an explicit
critical-stratum term.

If (VIII.1)--(VIII.3) hold for the complete admissible family, then

\[
Q_W(f)
=
\Sigma_S(f)+\|C_{S,R}f\|^2
\ge0,
\]

and Weil's criterion gives RH.

---

## IX. What has and has not been attained

### Attained

1. **A noncircular carrier type.** The carrier is a measured field of
   independently defined amplitudes, not an abstract square root of the
   desired defect.
2. **Exact coordinate covariance.** The square-root Jacobian is the amplitude
   law preserving quadratic response.
3. **Exact coarea interpretation.** Invariant fibers retain their normal,
   Jacobian, measure, orientation, and critical seams.
4. **Exact covariant FTC.** Contemporary carrier norms are nonnegative while
   their connection currents and discrete jumps may be signed.
5. **Exact Mellin half-density.** The logarithmic change \(r=e^u\) produces
   \(e^{u/2}\) and places the unitary Fourier/Mellin response on
   \(\operatorname{Re}s=1/2\).
6. **Exact hyperbolic separation.** The \(\cosh\) common face is positive;
   the \(\sinh\) normal face is oriented and signed.
7. **Exact Euler half-metric.** \(G^{1/2}\) standardizes the changing
   successor aperture and produces a positive contemporary complement.

### Still open

The actual arithmetic amplitude field

\[
B_{S,R,\xi}
\]

and measure

\[
\nu_{S,R}
\]

which make (VIII.1) equal the completed defect have not been constructed.
Neither the operator complement in (VII.4) nor the Riemannian/hyperbolic
examples may simply be declared to be that field.

The open question is no longer “can a positive operator be named?” It is:

> Can the published archimedean positive remainder, Gaussian--Poisson--Mellin
> completion, and semilocal Euler receiver transport be disintegrated into
> one receiver-local covariant amplitude field whose squared norm is exactly
> the completed defect and whose signed seam law is (VIII.3)?

That is the next genuine mathematical edge. No further local visualization,
prime census, or numerical zero experiment answers it.

---

## Reusable objects deposited

- `definition:covariant-coarea-carrier`
- `lemma:mellin-half-density-chart`
- `theorem:covariant-coarea-fundamental-theorem`
- `theorem:metric-half-jacobian-aperture`
- `corollary:coarea-carrier-rh`

They live in `src/soma/PAPERS/mathematics/` and are imported through the
shared catalogue.

