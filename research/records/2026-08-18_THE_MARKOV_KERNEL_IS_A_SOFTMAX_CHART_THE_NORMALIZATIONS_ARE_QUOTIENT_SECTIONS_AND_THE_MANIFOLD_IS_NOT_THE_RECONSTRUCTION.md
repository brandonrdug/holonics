# The Markov kernel is a softmax chart, the normalizations are quotient sections, and the manifold is not the reconstruction

**Date:** 2026-08-18
**Kind:** external-research synthesis and correction of the standing softmax/modulus interpretation.
Evidence only; it schedules no construction.
**Truth status:** **established-bounded** for direct reports of the cited papers; **proved-standard**
for classical finite metric, Markov, normalization, and differential identities;
**proved-derived** for the exact quotient, Jacobian, epsilon-inverse, and intertwining expressions
derived here; **interpretation** for the holonic correspondence; **conditional** for proposed
compression and Phoenix uses under named receiver families; **counterexample** where a stronger
standing claim is explicitly refuted; **open** for unbuilt joins.
**Construction boundary:** no executable capability is promoted. The current Phoenix audit is
deposited separately. This record supplies its external mathematical receivers and later
mathematics-codec revisions.

## Primary sources

1. Xingzhi Sun, Danqi Liao, Kincaid MacDonald, Yanlei Zhang, Chen Liu, Guillaume Huguet, Guy Wolf,
   Ian Adelstein, Tim G. J. Rudner, and Smita Krishnaswamy,
   [“Geometry-Aware Generative Autoencoders for Warped Riemannian Metric Learning and Generative Modeling on Data Manifolds,” arXiv:2410.12779v4](https://arxiv.org/abs/2410.12779),
   AISTATS 2025.
2. Laurent Cheret, Vincent Létourneau, Isar Nejadgholi, Chris Drummond, Hussein Al Osman, and Maia
   Fraser,
   [“Manifold-Matching Autoencoders,” arXiv:2603.16568v1](https://arxiv.org/abs/2603.16568),
   2026 preprint.
3. Yonghyeon Lee,
   [“A Geometric Perspective on Autoencoders,” arXiv:2309.08247v2](https://arxiv.org/abs/2309.08247),
   2023.
4. Jimmy Lei Ba, Jamie Ryan Kiros, and Geoffrey E. Hinton,
   [“Layer Normalization,” arXiv:1607.06450v1](https://arxiv.org/abs/1607.06450),
   2016.
5. Michael M. Bronstein, Joan Bruna, Taco Cohen, and Petar Veličković,
   [“Geometric Deep Learning: Grids, Groups, Graphs, Geodesics, and Gauges,” arXiv:2104.13478v2](https://arxiv.org/abs/2104.13478),
   2021, deposited in the predecessor
   [geometric-action record](2026-08-18_THE_ARCHITECTURE_IS_A_DOMAIN_ACTION_THE_GAUGE_CARRIES_THE_SECTION_AND_THE_COARSENING_OWES_ITS_FIBRE.md).

All four newly supplied papers were read completely. Their diagrams, assumptions, experiments, and
appendices were inspected rather than inferred from abstracts.

---

## 0. What the joined source family contributes

**Truth status: interpretation over established-bounded source reports.**

The papers form one useful progression:

~~~text
geometric deep learning
    domain + section + transformation action + locality + scale

geometric autoencoders
    reconstruction does not identify manifold or chart

geometry-aware generative autoencoder
    learned pullback form + off-manifold barrier + geodesic/population transport

manifold-matching autoencoder
    pairwise-distance receiver shapes a bottleneck and approximately preserves selected topology

layer normalization
    translation/scale quotient charts alter parameter geometry and recurrent conduct
~~~

Their common lesson is not that a low-dimensional vector is the manifold. It is that every
representation is a chart selected by an objective and a receiver, and equal reconstruction is
strictly too coarse to identify topology, geometry, dynamics, or causal transport.

The sources also supply the cleanest conventional bridge yet between:

- Gaussian distance kernels;
- softmax normalization;
- Markov transition matrices;
- repeated path transport;
- manifold diffusion;
- distance and pullback geometry;
- quotient charts used by neural normalization.

The holonic correction is that every such chart owes its collapsed fibre, dynamics, receiver scope,
and reopening law.

---

## 1. Reconstruction does not identify the manifold

**Truth status: established-bounded. Source: Lee, Sections 1-3.**

For encoder \(g:\mathbb R^D\to\mathbb R^m\) and decoder
\(f:\mathbb R^m\to\mathbb R^D\), vanilla reconstruction minimizes

\[
\mathcal L_{\mathrm{rec}}
=
\sum_i
\|x_i-f(g(x_i))\|^2.
\tag{A.1}
\]

If \((f,g)\) reconstructs the samples and \(h:\mathbb R^m\to\mathbb R^m\) is an invertible chart
change, then

\[
(f,g)
\longmapsto
(f\circ h^{-1},h\circ g)
\tag{A.2}
\]

has the same reconstruction. The latent solution is therefore a chart-family orbit, not one
identified coordinate system.

A finite sample also lies on infinitely many geometrically different manifolds. Perfect point
reconstruction does not establish:

- correct local connectivity;
- correct differentiable structure;
- metric preservation;
- orientation;
- curvature;
- geodesics;
- a global atlas;
- successor dynamics.

This is a direct external counterexample to any Phoenix or mathematics-codec claim graded only by
round-trip bytes or equal final output.

### Pullback geometry

When \(f\) is smooth with full-rank Jacobian, the induced metric in latent coordinates is

\[
G_f(z)
=
J_f(z)^\top H(f(z))J_f(z),
\tag{A.3}
\]

for declared ambient metric \(H\).

The raw Jacobian basis is chart dependent. A coordinate-invariant tangent-space receiver is the
orthogonal projector

\[
\widehat T_f
=
J_f(J_f^\top J_f)^{-1}J_f^\top.
\tag{A.4}
\]

Its image is a point in a Grassmann manifold. This is the appropriate receiver for comparing tangent
subspaces without identifying one chosen basis with the tangent body.

The geometry hierarchy reviewed by Lee is:

\[
G_f=I
\quad\text{isometry},
\tag{A.5}
\]

\[
G_f=c(z)^{-1}I
\quad\text{conformal chart},
\tag{A.6}
\]

\[
G_f=c^{-1}I
\quad\text{scaled isometry}.
\tag{A.7}
\]

The source usually assumes one global chart and a manifold homeomorphic to \(\mathbb R^m\). That
excludes precisely the multichart, non-orientable, singular, and topology-changing cases the
holonic atlas must retain.

---

## 2. The GAGA construction and its exact boundary

**Truth status: established-bounded. Source: Sun et al., Sections 3-4 and Appendices A-F.**

GAGA trains an encoder \(f_\theta\) and decoder \(h_\phi\) with reconstruction and locally weighted
distance matching:

\[
\mathcal L_{\mathrm{Recon}}
=
\frac1N\sum_i
\|x_i-h_\phi(f_\theta(x_i))\|_2^2,
\tag{G.1}
\]

\[
\mathcal L_{\mathrm{Dist}}
=
\frac1N
\sum_{i<j}
e^{-\zeta d(x_i,x_j)}
\left(
\|f_\theta(x_i)-f_\theta(x_j)\|_2-d(x_i,x_j)
\right)^2.
\tag{G.2}
\]

It extends the embedding with an off-manifold scalar:

\[
f^+(x)
=
\begin{pmatrix}
f_\theta(x)\\
\beta s(x)
\end{pmatrix},
\tag{G.3}
\]

and calls

\[
g_{\mathbb R^n}(X,Y)
=
X^\top J_{f^+}^\top J_{f^+}Y
\tag{G.4}
\]

a warped pullback metric on the data space.

The learned form is used for:

- volume-guided manifold sampling;
- geodesic interpolation;
- population transport through geodesic-guided flow matching.

### The Markov-softmax bridge in Appendix A

The source constructs a Gaussian affinity

\[
K_{ij}
=
\exp\!\left(
-\frac{\|z_i-z_j\|^2}{\sigma}
\right)
\tag{G.5}
\]

and row-normalizes it:

\[
P_{ij}
=
\frac{K_{ij}}{\sum_kK_{ik}}
=
\operatorname{softmax}_j
\left(
-\frac{\|z_i-z_j\|^2}{\sigma}
\right).
\tag{G.6}
\]

The resulting \(P\) is a row-stochastic Markov transition matrix. Its \(t\)-step transport is

\[
(P^t)_{ij}
=
\sum_{i_1,\ldots,i_{t-1}}
P_{ii_1}
P_{i_1i_2}
\cdots
P_{i_{t-1}j}.
\tag{G.7}
\]

This is the exact external bridge requested for Holonic Interactions:

> one Markov entry is a condensed one-step face; a matrix power recomposes the entire weighted
> path family seen by that receiver.

The Markov matrices form a composition monoid. They are not generally a group: diffusion may
collapse distinctions and need not admit a stochastic inverse.

### Serious source limitations

**Truth status: counterexample to stronger readings of the source.**

1. If \(f^+:\mathbb R^n\to\mathbb R^{d+1}\) with \(d+1<n\), then

   \[
   \operatorname{rank}(J_{f^+}^\top J_{f^+})\le d+1<n.
   \]

   The form is positive semidefinite and degenerate, not a Riemannian metric on all of
   \(\mathbb R^n\).

2. Lemma 3.2 assumes a scalar reverse-Lipschitz bound

   \[
   \alpha\|x-y\|
   \le
   |s(x)-s(y)|.
   \tag{G.8}
   \]

   With \(\alpha>0\), this cannot hold globally on a positive-dimensional manifold on which
   \(s\approx0\) at several distinct points.

3. A finite density

   \[
   p(x)\propto e^{-\lambda s(x)}f_{\mathrm{vol}}(x)
   \tag{G.9}
   \]

   concentrates near a manifold. It is not literally supported on it without an infinite barrier
   or a separate projection/restriction.

4. Global strong convexity is restrictive and conflicts with many toroidal, branched, or multimodal
   geometries.

5. Local approximate distance matching does not establish a diffeomorphism or a local isometry.

6. The ULA discretization and final filtering add errors not covered merely by the continuous-time
   convergence statement.

The paper is valuable because its attempted whole-space geometry reveals exactly which rank,
singularity, topology, and support receipts Eros must return before using the word manifold.

---

## 3. Manifold-matching is a distance receiver, not a manifold proof

**Truth status: established-bounded. Source: Cheret et al., Sections 2-6.**

For latent representations \(Z\) and reference representations \(E=u(X)\), MMAE computes

\[
D^Z_{ij}=\|z_i-z_j\|_2,
\qquad
D^E_{ij}=\|e_i-e_j\|_2
\tag{M.1}
\]

and minimizes

\[
R_{\mathrm{MM}}
=
\frac1{n^2}
\sum_{i,j}
\left(D^Z_{ij}-D^E_{ij}\right)^2.
\tag{M.2}
\]

The reference may be the original data or an exterior PCA/UMAP/t-SNE chart. The method
approximately copies that receiver geometry into the latent space and supplies out-of-sample
extension.

The paper invokes persistence stability:

\[
d_B(\operatorname{Dgm}_p(X),\operatorname{Dgm}_p(Y))
\le
2d_{GH}(X,Y),
\tag{M.3}
\]

and a uniform all-pairs error consequence. The trained loss is instead a mean-square batch error.
Writing

\[
\Delta=D^Z-D^E,
\]

we have

\[
\sqrt{R_{\mathrm{MM}}}
=
\frac{\|\Delta\|_F}{n},
\tag{M.4}
\]

while the worst pair only satisfies

\[
\|\Delta\|_\infty
\le
\|\Delta\|_F
=
n\sqrt{R_{\mathrm{MM}}}.
\tag{M.5}
\]

Therefore small average batch loss does not itself prove:

- small worst-pair distortion;
- full-dataset persistence preservation;
- preservation of a continuous manifold;
- preservation of dynamic path transport.

The paper’s own limitation is honest: it approximately preserves selected global Euclidean
geometry, does not explicitly preserve topology, and does not unfold manifolds.

### A distance matrix is a quotient by a group orbit

For coordinates \(x_i\) and Euclidean motion

\[
x_i\mapsto Qx_i+a,
\qquad
Q^\top Q=I,
\tag{M.6}
\]

the complete pairwise distance matrix is unchanged. It is a receiver face of the Euclidean-group
orbit and not source identity.

Classical MDS double-centers squared distances:

\[
H=I-\frac1n\mathbf1\mathbf1^\top,
\qquad
B=-\frac12H(D^{\circ2})H.
\tag{M.7}
\]

When \(B\succeq0\), coordinates can be recovered from its eigendecomposition only up to translation
and orthogonal action. The minimal exact Euclidean embedding dimension is

\[
\operatorname{rank}(B).
\tag{M.8}
\]

Thus the paper’s reference and bottleneck dimensions are decoupled as matrix shapes, but exact
realizability is not:

\[
R_{\mathrm{MM}}=0
\quad\Longrightarrow\quad
\operatorname{rank}(B)\le d.
\tag{M.9}
\]

### Not naive compression

The complete distance matrix has \(n(n-1)/2\) pair entries. It is not generally a smaller storage
than \(n\) points in a low-dimensional chart. Its value is receiver factorization:
every distance-only future question factors through it.

A holonic condensation of such material owes:

- the declared distance receiver family;
- the Euclidean group orbit collapsed by that receiver;
- any PCA or preprocessing fibre;
- exact Gram rank and singular locus;
- residual when no \(d\)-dimensional realization exists;
- topology, orientation, connection, intervention, and chronology receivers capable of reopening
  the quotient.

---

## 4. Markov is a receiver property and compression is lumpability

**Truth status: proved-standard for the Markov condition; interpretation for the holonic reading.**

A Markov chain is a state chart in which the present retained state suffices for the requested
future. If the selected state omits relevant history or morphology, Markovity is itself a
compression claim.

For a partition \(q:X\to C\), exact quotient dynamics require strong lumpability:

\[
q(x)=q(x')
\Longrightarrow
\sum_{y:q(y)=b}P(x,y)
=
\sum_{y:q(y)=b}P(x',y)
\quad
\text{for every block \(b\)}.
\tag{K.1}
\]

Let \(C\) also denote the state-to-block incidence matrix. Lumpability is the intertwining law

\[
PC=C\overline P.
\tag{K.2}
\]

The exact defect is

\[
\Delta_{\mathrm{lump}}
=
PC-C\overline P.
\tag{K.3}
\]

Only when \(\Delta_{\mathrm{lump}}=0\) does a quotient Markov chain carry every block-level successor
history exactly.

This is the conventional counterpart of receiver-exact compression. When it fails:

- the within-block states are not dynamically equivalent;
- shortest separating histories belong in the ReconstructionFiber;
- an approximate transition fit is not exact condensation;
- pairwise geometric closeness does not repair the dynamic defect.

The current **receiver_exact_compression** owner computes the analogous stable future partition and
shortest separators without assuming the exterior word Markov.

---

## 5. Softmax is a projective chart before it is probability

**Truth status: proved-standard.**

For logits \(z\in\mathbb R^n\), define positive weights

\[
a_i=e^{z_i},
\qquad
Z=\sum_i a_i.
\tag{S.1}
\]

Then

\[
\operatorname{softmax}(z)
=
\frac{a}{Z}.
\tag{S.2}
\]

This factors as:

~~~text
additive potential section
→ componentwise exponential
→ positive multiplicative ray
→ unit-sum simplex section
~~~

The common additive coordinate is gauge:

\[
\operatorname{softmax}(z+c\mathbf1)
=
\operatorname{softmax}(z).
\tag{S.3}
\]

The ratio family retains every difference:

\[
\frac{p_i}{p_j}
=
e^{z_i-z_j},
\qquad
\log\frac{p_i}{p_j}
=
z_i-z_j.
\tag{S.4}
\]

Thus softmax gives a smooth chart

\[
\mathbb R^n/\operatorname{span}\{\mathbf1\}
\cong
\operatorname{int}\Delta^{n-1}.
\tag{S.5}
\]

Its inverse fibre is

\[
[z]
=
\{z+c\mathbf1:c\in\mathbb R\}.
\tag{S.6}
\]

No statistical ontology is necessary. The same normalized section can be declared as:

- barycentric coordinates;
- conductance shares;
- normalized compatibility;
- aperture allocation;
- a Markov transition row.

Probability becomes the interpretation only when the receiver declares a stochastic transition or
sampling law.

### What “modulus” can mean rigorously

The user’s intuition survives in three bounded senses:

1. \(K_{ij}\) in GAGA begins from the squared metric modulus
   \(\|z_i-z_j\|^2\).
2. \(Z=\|a\|_1\) is the total positive magnitude/current under an \(\ell^1\) receiver.
3. Softmax chooses one section of a positive projective ray by imposing total one.

“Remainder” should name the quotient class or a discrete allocation residual, not ordinary
real-number modulus. Literal Euclidean division of each \(a_i\) by \(Z\) is uninformative because
\(0<a_i\le Z\).

For an exact finite allocation of \(N\) indivisible carriers with integer conductances \(w_i\),

\[
Nw_i=q_iW+r_i,
\qquad
W=\sum_iw_i,
\qquad
0\le r_i<W,
\tag{S.7}
\]

the \(q_i\) are allocated carriers and the \(r_i\) are the exact unresolved remainders. Dropping
those remainders is the lossy step. This is a discrete realization of normalized shares, not an
identity claiming that real-valued softmax is modular arithmetic.

### Correction to the standing section-modulus prose

**Truth status: counterexample.**

Softmax factors out a common additive coordinate; it does not itself center the logits or force
their first moment to vanish. One may choose a centered representative of the quotient, but that is
a second chart choice.

The paper record
**THE_JUNCTION_IS_A_HALF_TWIST_AND_A_MODULUS_IS_WHAT_A_DECLARED_QUOTIENT_RETAINS**
overstates three points:

- softmax and section modulus do not literally “fix the same gauge” unless a shared centering
  receiver is separately declared;
- the current **SectionModulus** is an unweighted symbolic-surprisal second moment and extreme fibre,
  while softmax produces a \(p\)-weighted covariance;
- \(\operatorname{Var}_{p_\beta}(z)\) is a cumulant derivative and is not generally monotone in
  temperature for arbitrary logit populations.

The correct relationship is that both are members of a family of centered quadratic receivers with
different pivots and measures.

---

## 6. The softmax Jacobian is a weighted local Laplacian

**Truth status: proved-standard.**

For inverse temperature \(\beta\),

\[
J_{\mathrm{softmax}}
=
\beta(\operatorname{diag}(p)-pp^\top).
\tag{S.8}
\]

It factors as

\[
\frac1\beta J_{\mathrm{softmax}}
=
\operatorname{diag}(\sqrt p)
\left(
I-\sqrt p\,\sqrt p^\top
\right)
\operatorname{diag}(\sqrt p).
\tag{S.9}
\]

It annihilates the additive gauge:

\[
J_{\mathrm{softmax}}\mathbf1=0.
\tag{S.10}
\]

Its quadratic form is

\[
v^\top J_{\mathrm{softmax}}v
=
\beta
\left(
\sum_i p_iv_i^2
-
\left(\sum_i p_iv_i\right)^2
\right)
=
\beta\operatorname{Var}_p(v).
\tag{S.11}
\]

Equivalently it is the Laplacian of a complete local contact graph with conductances

\[
w_{ij}=\beta p_ip_j.
\tag{S.12}
\]

This does not make softmax a completed diffusion event through time. It supplies:

- one local equilibrium chart;
- one weighted centered quadratic geometry;
- one differential/adjoint conductance law.

Causal diffusion additionally owes incidence, capacity, boundary, chronology, current, constitutive
transport, and return.

At the uniform section \(p_i=1/n\),

\[
J_{\mathrm{softmax}}
=
\frac{\beta}{n}
\left(
I-\frac1n\mathbf1\mathbf1^\top
\right).
\tag{S.13}
\]

This is exactly the LayerNorm centering projector up to scale. Away from uniformity it is its
capacity-weighted analogue.

---

## 7. Sigmoid is the two-port chart

**Truth status: proved-standard.**

\[
\sigma(x)
=
\frac{e^x}{1+e^x}
=
\operatorname{softmax}(x,0)_1,
\tag{N.1}
\]

\[
\frac{\sigma(x)}{1-\sigma(x)}
=
e^x.
\tag{N.2}
\]

For two potentials \(a,b\),

\[
\frac{e^a}{e^a+e^b}
=
\sigma(a-b).
\tag{N.3}
\]

The two-node Jacobian/Laplacian is

\[
\sigma(x)(1-\sigma(x))
\begin{pmatrix}
1&-1\\
-1&1
\end{pmatrix}.
\tag{N.4}
\]

At finite exact \(x\), the odds chart is invertible. A sigmoid gate is therefore a ratio pivot
between two named branches, such as:

~~~text
carry existing standing
against
admit returned construction
~~~

The later mixture

\[
(1-\sigma(x))u+\sigma(x)v
\tag{N.5}
\]

becomes a quotient only if the separate branch lineage is discarded. Thresholding, saturation in a
finite representation, quantization, or a zero-temperature limit creates further collapsed fibres.

---

## 8. RMS is quadratic density, and RMSNorm is an epsilon-dependent chart

**Truth status: proved-standard and proved-derived.**

For \(x\in\mathbb R^d\),

\[
\operatorname{RMS}(x)
=
\sqrt{\frac1d\sum_i x_i^2}
=
\frac{\|x\|_2}{\sqrt d}.
\tag{N.6}
\]

The operations are:

~~~text
square each oriented contribution
→ add the quadratic population
→ divide by the admitted coordinate population
→ take the root back to amplitude dimension
~~~

Holonically, RMS is the uniform quadratic capacity density of the declared section about the fixed
zero pivot. It is a magnitude receiver. The signed/oriented population that produced it remains the
construction.

Let

\[
a_R(x)
=
\frac{x^\top x}{d}+\epsilon,
\qquad
R_\epsilon(x)
=
G\frac{x}{\sqrt{a_R(x)}},
\tag{N.7}
\]

with learned diagonal gain \(G\).

### Ideal epsilon-zero RMSNorm

For \(\epsilon=0\) and nonzero \(x\),

\[
R_0(\lambda x)=R_0(x)
\qquad
\text{for \(\lambda>0\)}.
\tag{N.8}
\]

It chooses the RMS-one section of a positive radial orbit. The collapsed fibre is the positive ray.
Negative scale reverses orientation and must not be silently included in the same gauge.

### Nonzero epsilon

For \(\epsilon>0\), nonzero gains, and no finite-precision collapse, radial magnitude is recoverable.
Removing the gain for clarity and putting

\[
y=\frac{x}{\sqrt{x^\top x/d+\epsilon}},
\qquad
q=\frac{y^\top y}{d},
\]

gives

\[
q=\frac{v}{v+\epsilon},
\qquad
v=\frac{x^\top x}{d},
\tag{N.9}
\]

and

\[
x=
\sqrt{\frac{\epsilon}{1-q}}\,y.
\tag{N.10}
\]

Thus \(R_\epsilon\) maps \(\mathbb R^d\) into the open ball
\(\|y\|<\sqrt d\) and stores radius as distance to its boundary. It is not an exact radial quotient.

**Counterexample:** Gemma’s source declares
\(\epsilon=10^{-6}\). Therefore the live roadmap sentence “RMSNorm discards magnitude” is false of
the exact source mathematics. The horizon interpretation remains valid only for:

- the \(\epsilon=0\) idealization;
- a declared projective/directional receiver;
- or a later quantized quotient which actually collapses radii.

A pre-norm residual body also retains the raw \(x\) beside \(F(R_\epsilon(x))\), so the complete
layer retains information its branch chart may quotient.

### Local derivative and adjoint

\[
DR_\epsilon(x)
=
G
\left[
a_R^{-1/2}I
-
\frac1d a_R^{-3/2}xx^\top
\right].
\tag{N.11}
\]

On \(x^\perp\), the ungained eigenvalue is \(a_R^{-1/2}\). On the radial direction \(x\), it is

\[
\epsilon a_R^{-3/2}.
\tag{N.12}
\]

The radial direction enters the kernel exactly at \(\epsilon=0\). For \(\epsilon>0\) and nonzero
gains, the local map is full rank.

This derivative is an identity plus one rank-one correction. Its transpose/metric adjoint is the
complete local causal-adjoint law; a generic global autograd cabinet is unnecessary for this
operation.

---

## 9. LayerNorm is translation quotient plus radial chart, not a rotation

**Truth status: proved-standard and proved-derived. Source: Ba, Kiros, Hinton, Sections 3 and 5.**

Define the centering projector

\[
P
=
I-\frac1d\mathbf1\mathbf1^\top,
\qquad
c=Px=x-\mu(x)\mathbf1.
\tag{N.13}
\]

LayerNorm is

\[
a_L(x)=\frac{c^\top c}{d}+\epsilon,
\qquad
L_\epsilon(x)
=
G\frac{c}{\sqrt{a_L(x)}}+b.
\tag{N.14}
\]

It first quotients common-mode translation along \(\operatorname{span}\{\mathbf1\}\), then applies
the centered radial chart in \(\mathbf1^\perp\).

For \(\epsilon=0\), its orbit fibre is

\[
x\sim\lambda x+t\mathbf1,
\qquad
\lambda>0.
\tag{N.15}
\]

For \(\epsilon>0\), common shifts still collapse exactly, but centered radius remains recoverable by
the analogue of (N.10).

Its derivative is

\[
DL_\epsilon(x)
=
G
\left[
a_L^{-1/2}P
-
\frac1d a_L^{-3/2}cc^\top
\right].
\tag{N.16}
\]

It always annihilates \(\mathbf1\). The centered radial eigenvalue is
\(\epsilon a_L^{-3/2}\); centered directions orthogonal to \(c\) have eigenvalue \(a_L^{-1/2}\)
before gain.

### Pivot and orientation

“Pivoting” is mathematically apt: the arithmetic mean moves the local origin to the population’s
neutral axis.

“Rotation” is only partially apt:

- LayerNorm does not rotate the section;
- it projects out one common axis and normalizes radius;
- it preserves the centered direction;
- orthogonal transformations preserving \(\mathbf1\) preserve its mean/variance receiver;
- learned coordinatewise gain and bias generally break that rotational symmetry.

The LayerNorm paper’s parameter-geometry analysis does show why large normalized weight norms make
changes of orientation harder under learning. That is a statement about the Fisher/pullback
geometry and effective learning rate, not a claim that LayerNorm itself rotates the state.

### Time parity

LayerNorm recomputed at each RNN step with shared gain and bias is a recurring local chart law. It
can stabilize recurrent dynamics. It does not:

- close a causal loop;
- prove physical time reversal;
- certify Kirchhoff circulation;
- establish time parity.

The adjoint reverses composition order. It does not reverse physical time. Time parity remains a
property of completed propagation and return.

---

## 10. One family of quadratic pivots

**Truth status: interpretation on proved-derived expressions.**

| mechanism | pivot and measure | selected chart | collapsed fibre |
|---|---|---|---|
| softmax | \(p\)-weighted axis | unit-sum positive simplex | common additive potential |
| sigmoid | two-port difference | open unit interval | common two-port potential |
| RMSNorm, \(\epsilon=0\) | fixed zero, uniform quadratic measure | RMS-one sphere | positive radius |
| RMSNorm, \(\epsilon>0\) | fixed zero, uniform quadratic measure | open ball | none before later quotient |
| LayerNorm, \(\epsilon=0\) | moving arithmetic mean | mean-zero RMS-one sphere | mean and positive radius |
| LayerNorm, \(\epsilon>0\) | moving arithmetic mean | centered open ball | common mean |
| SectionModulus | symbolic-surprisal mean plus extreme fibre | undivided second moment/extreme pair | none until a quotient is declared |
| distance matrix | pairwise Euclidean metric | Euclidean-orbit receiver | rigid motion and any prior projection fibre |
| tangent projector | local tangent subspace | Grassmann point | choice of tangent basis |
| pullback metric | local differential geometry | SPD or semidefinite cone | chart coordinates, subject to rank |
| Markov lumping | successor-equivalent state partition | quotient chain | within-block histories |

These are nonlinear geometric compressions and chart choices over:

- simplices;
- spheres and open balls;
- Grassmannians;
- positive-definite or semidefinite cones;
- Euclidean group orbits;
- homeomorphism/diffeomorphism chart families;
- Markov quotient state spaces.

They are not all projections onto a low-rank linear subspace.

---

## 11. Compression law

**Truth status: interpretation and conditional.**

The papers make the difference between naïve linear compression and holonic compression explicit:

### Naïve/ordinary compression faces

- low bottleneck dimension;
- reconstruction MSE;
- pairwise-distance MSE;
- parameter count;
- matrix rank;
- file bytes.

### Holonic compression

A condensation is lawful only when:

1. a receiver family is declared;
2. every requested successor history factors through the compressed section;
3. the complete decoder or realization is carried;
4. collapsed group orbits and predecessor populations are returned;
5. topology, orientation, connection, dynamics, and intervention alternatives remain reopenable;
6. exact work and artifact-plus-decoder cost are reported;
7. a richer receiver refines the quotient instead of invalidating it silently.

For Markov interactions, condition 2 becomes lumpability. For a distance receiver it becomes exact
Euclidean realizability modulo its group orbit. For normalization it becomes receiver invariance
under the appropriate translation/scale family. For a manifold chart it becomes atlas
compatibility, not mere point reconstruction.

---

## 12. Audit obligations carried forward

The external source family adds these checks to Phoenix and the mathematics codec:

- equal output or round-trip bytes do not identify the manifold, chart, topology, or transport;
- every pullback “metric” reports rank and singular locus;
- every normalization identifies its group action, selected section, epsilon, and remaining fibre;
- every Markov compression returns a lumpability/intertwining receipt or its full defect;
- every distance compression returns complete pairwise residual, maximum defect, Gram rank, and
  richer separating receivers;
- every softmax probability claim first declares the Markov or sampling receiver;
- every RMSNorm horizon claim distinguishes epsilon-zero idealization from the actual epsilon chart;
- every LayerNorm pivot declares its normalized population and does not claim rotation or time
  parity without a transport return;
- every interval or stochastic approximation propagates its remainder through downstream
  operations;
- every geometry learned from finite samples remains plural outside the receiver family that
  founded it.

---

## 13. Final synthesis

**Truth status: interpretation.**

The joined mechanism is:

~~~text
caused local occurrences
→ founded metric or compatibility section
→ exponentiated positive affinity
→ softmax projective chart
→ optional Markov receiver
→ path-family transport P^t
→ receiver-stable state quotient
→ exact lumpability or retained dynamic defect
→ manifold, topology, orientation, and chart receivers reopen what distance collapsed
~~~

RMSNorm, LayerNorm, sigmoid, and softmax are not unrelated neural conveniences. They are local
chart choices over different transformation families and quadratic receivers. Their differences
are load-bearing:

- softmax removes one common additive potential;
- sigmoid is its two-port ratio chart;
- ideal RMSNorm removes positive radius;
- epsilon RMSNorm retains radius in a bounded chart;
- LayerNorm also removes the common-mode pivot;
- Markov normalization turns a ratio row into a stochastic receiver;
- compression begins only when future histories factor through the resulting state.

This makes the user’s non-statistical softmax interpretation mathematically sound in its core and
more precise at its boundary:

> Softmax is an exponential/projective chart. It becomes probability only at a declared stochastic
> receiver. Its “remainder” is the collapsed additive-potential fibre, or a separately constructed
> discrete allocation residual, not ordinary real-number modulus.
