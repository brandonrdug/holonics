# Eros Precessing Chord and Conic Transport 01

**Status:** ACCEPTED  
**Date:** 23 July 2026  
**Primary artifact:** `REPORT.json`  
**Instrument:** `life/examples/eros_precessing_chord_conic_transport.rs`  
**Arithmetic:** exact integers, reduced ratios, rational rotation matrices,
complex ratios, and symbolic inverse-cosine words only; no floating-point
causal datum  
**Execution:** four independent CPU workers on a host exposing 24 hardware
threads  
**Report SHA-256:** `fc8abce95752cb9c10208d11838aeb5c965f94725c044435b70511c1fa90a411`  
**Embedded pre-digest SHA-256:**
`aab1b77275675b49e144686bbf136b5bbc0fa898481f5f81b84447909cedb952`

## The question and stopping condition

Can the reciprocal Smith pair become a discrete moving-chord carrier while
retaining, as separately readable data:

1. its varying complex-plane intersection \(q\);
2. its oriented axis \(u\);
3. the two pole paths \(P_+\) and \(P_-\);
4. their common motion and oriented cross-coupling;
5. the two induced sheet metrics;
6. flat closure versus connection holonomy; and
7. a conic phase boundary?

The prior exact conformal atlas supplied a fixed vertical chord. The prior
retriangulation cell supplied the face law comparing direct and composed
transport. Neither supplied the carrier joining them.

This run stopped after one exact Smith precession, three controlled pole
edges, one two-parameter metric cell, one flat and one curved triangular
face, and one conic-pencil path. It did not sample zeta zeros, fit a
trajectory, evaluate a decimal angle, launch CUDA, change Soma, or render a
camera view.

## The moving chord

An oriented chord is carried by

\[
q_k\in\mathbb Q^2,\qquad
u_k\in S^2(\mathbb Q),\qquad
P_{\pm,k}=q_k\pm r u_k .
\]

Here \(q_k\) is the chord's actual intersection with the declared complex
plane. It is not an outside camera coordinate. The elementary discrete
transport is

\[
q_{k+1}=q_k+\Delta q_k,\qquad
u_{k+1}=U_k u_k,\qquad
P_{\pm,k+1}-P_{\pm,k}
  =\Delta q_k\pm r\Delta u_k ,
\]

where \(U_k\) is an exact frame transport. This is the bounded discrete
differential equation tested by the cell.

The starting reciprocal Smith pair is

\[
P_+=\left(\frac{21}{53},\frac{48}{53},\frac8{53}\right),
\qquad
P_-=\left(\frac{21}{53},\frac{48}{53},-\frac8{53}\right).
\]

It is one chord of squared separation \(256/2809\), not two unrelated
points. Its initial plane intersection is

\[
q_0=\left(\frac{21}{53},\frac{48}{53},0\right).
\]

The exact rational tilt

\[
R_y=
\begin{pmatrix}
24/25&0&7/25\\
0&1&0\\
-7/25&0&24/25
\end{pmatrix}
\]

makes the axis \(u_1=(7/25,0,24/25)\) and moves the plane cut to

\[
q_1=\left(\frac{175}{424},\frac{48}{53},0\right).
\]

The plane no longer bisects the chord: its two directed pole distances are
\(15/424\) and \(113/424\), whose sum remains the exact chord length
\(16/53\). The asymmetry therefore comes from the observer cut through the
same rigid chord, not from changing the chord.

A subsequent precession around the plane normal uses the unit complex phase

\[
\phi=\frac35+\frac45i .
\]

It gives

\[
u_2=\left(\frac{21}{125},\frac{28}{125},\frac{24}{25}\right),
\qquad
q_2=-\frac{1011}{2120}+\frac{463}{530}i .
\]

Both the actual plane intersection and the stereographic axis coordinate
obey the same transport:

\[
q_2=\phi q_1,
\qquad
\zeta(u_2)=\phi\,\zeta(u_1),
\qquad
\zeta(u_1)=7 .
\]

Every pole remains exactly on the unit sphere and all three chord
separations remain \(256/2809\). The two pole paths under this precession are
not forced to have the same spherical arc. Their exact geodesic lengths are
retained without decimal evaluation as

\[
\ell_+=\arccos\left(\frac{210837}{351125}\right),
\qquad
\ell_-=\arccos\left(\frac{5496717}{8778125}\right).
\]

The corresponding chordal squared lengths satisfy
\(\|P'_\pm-P_\pm\|^2=2-2\cos\ell_\pm\) exactly.

## What the two pole paths reveal

For any fixed-\(r\) edge,

\[
\Delta P_\pm=\Delta q\pm r\Delta u .
\]

Adding and subtracting their squared lengths gives two different
observables:

\[
S=\|\Delta P_+\|^2+\|\Delta P_-\|^2
  =2\|\Delta q\|^2+2r^2\|\Delta u\|^2,
\]

\[
D=\|\Delta P_+\|^2-\|\Delta P_-\|^2
  =4r\,\Delta q\mathbin{\cdot}\Delta u .
\]

The normalized swing

\[
\chi=\frac{D}{S}
\]

is not an absolute probability or a reward. It is the oriented proportion
of the edge motion carried by translation--precession coupling. The three
foils isolate its meaning:

| Edge | \(\|\Delta P_+\|^2\) | \(\|\Delta P_-\|^2\) | \(\Delta q\cdot\Delta u\) | \(\chi\) |
|---|---:|---:|---:|---:|
| precession only | \(18/25\) | \(18/25\) | \(0\) | \(0\) |
| orthogonal translation and precession | \(68/25\) | \(68/25\) | \(0\) | \(0\) |
| coupled translation and precession | \(13/25\) | \(73/25\) | \(-3/5\) | \(-30/43\) |

Swapping the pole hand in the coupled row sends
\(\chi=-30/43\) to \(+30/43\) while retaining the common motion. Thus
orientation is discrete and consequential without assigning a scalar state
to either pole in isolation.

## The induced two-sheet metric

For parameters \(\lambda^a\), the pole sheets induce

\[
g^\pm_{ab}
  =\partial_a P_\pm\mathbin{\cdot}\partial_b P_\pm
  =(\partial_a q\pm r\partial_a u)
   \mathbin{\cdot}
   (\partial_b q\pm r\partial_b u).
\]

The exact two-parameter cell returns

\[
g^+=
\begin{pmatrix}
5/4&5/6\\
5/6&10/9
\end{pmatrix},
\qquad
g^-=
\begin{pmatrix}
5/4&-5/6\\
-5/6&10/9
\end{pmatrix},
\]

with determinant \(25/36\) on both sheets. Their common and coupling
factors are

\[
g^{\mathrm{common}}=\frac{g^++g^-}{2}
=
\begin{pmatrix}
5/4&0\\
0&10/9
\end{pmatrix},
\]

\[
g^{\mathrm{coupling}}=\frac{g^+-g^-}{2}
=
\begin{pmatrix}
0&5/6\\
5/6&0
\end{pmatrix}.
\]

The off-diagonal hand is the differential version of the pole-edge
cross-term. Averaging the sheets would preserve total activity while
annihilating precisely the oriented coupling that distinguishes their
paths. The pair \((g^{\mathrm{common}},g^{\mathrm{coupling}})\), however,
reconstructs both sheets exactly.

## Triangular curvature

For a triangular face \(0\to1\to2\), direct transport \(U_{02}\) and
composed transport \(U_{12}U_{01}\) are compared through

\[
H_{012}=U_{02}^{-1}U_{12}U_{01}.
\]

The flat foil uses two quarter-turns and their declared half-turn. It gives
\(H_{012}=I\), zero connection residual, and identical direct and composed
pole placements.

The mixed-axis foil gives

\[
H_{012}=
\begin{pmatrix}
0&0&-1\\
0&-1&0\\
-1&0&0
\end{pmatrix},
\qquad
\frac{\operatorname{tr}H_{012}-1}{2}=-1 .
\]

The direct and composed axes differ by squared distance \(98/25\), as do
both corresponding pole placements. This is an exact discrete curvature
read: the two routes reach the same base vertex but not the same local
frame. The cell constructs this as a controlled foil; it does not claim
that zeta itself supplied this holonomy.

## The conic phase boundary

The independent pencil

\[
Q_\mu(x,y)=x^2+\mu y^2-1
\]

has homogeneous determinant \(-\mu\). The retained path is

\[
\text{ellipse at }\mu=4
\;\longrightarrow\;
\text{circle at }\mu=1
\;\longrightarrow\;
(x-1)(x+1)=0\text{ at }\mu=0
\;\longrightarrow\;
\text{hyperbola at }\mu=-1 .
\]

Circle, ellipse, and hyperbola are different real affine-chart faces of a
nonsingular projective conic. The actual class break is localized at
\(\mu=0\), where the determinant vanishes and the conic becomes two lines.
That discriminant supplies lawful edges or seams to a simplicial carrier;
it does not by itself supply a filled triangle or cause the chord's
precession.

## Consequence

The proposed precessing two-pole figure now has a precise finite carrier:

\[
(q_k,u_k,r)
\quad\stackrel{(\Delta q_k,U_k)}{\longrightarrow}\quad
(q_{k+1},u_{k+1},r),
\]

together with two pole worldlines, their exact induced metrics, and a
connection whose face holonomy distinguishes flat from curved
composition. The “kinks” are therefore not generic intersections in a
flattened drawing. They can be classified as:

- a moved observer cut \(q\);
- an axis reorientation \(u\);
- a nonzero translation--precession coupling \(\chi\);
- a conic discriminant;
- or a nontrivial triangular holonomy.

These are related geometric reads, but none may stand in for the others.

For the RH program, this closes the carrier between the reciprocal Smith
chord and discrete face curvature. It does **not** close the global theorem.
The one proof-bearing relation still absent is a derivation from the
completed zeta/xi field itself which:

1. determines the edge transports and the relevant sheet metric rather
   than choosing them as foils;
2. identifies every nontrivial xi zero mode with that transported
   configuration; and
3. shows that a genuine zero mode cannot retain a nonzero normal chord
   \(\varepsilon\).

The next mathematical move is therefore not a larger zero sweep. It is to
seek that response/connection identity—most naturally as an exact
Hermitian or Weil-type form pulled back to this two-sheet carrier—and test
whether its normal component is forced to vanish while tangential
precession remains.

## Exact artifacts

- [`REPORT.json`](REPORT.json) — complete chord, pole-edge, metric,
  connection-face, conic, and acceptance rows;
- `src/soma/life/examples/eros_precessing_chord_conic_transport.rs` — exact
  bounded four-worker instrument.

Artifact identities:

```text
REPORT.json fc8abce95752cb9c10208d11838aeb5c965f94725c044435b70511c1fa90a411
example     5df197fddd1046e3cc5588bd49f62be97526e1e1aef8d57b40917fd47e2a6d01
```

The Soma receiving law and interior were unchanged.
