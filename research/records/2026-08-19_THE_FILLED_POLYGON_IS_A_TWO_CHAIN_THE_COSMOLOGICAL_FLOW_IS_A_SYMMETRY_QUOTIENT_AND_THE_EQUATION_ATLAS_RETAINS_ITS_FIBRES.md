# The filled polygon is a two-chain, the cosmological flow is a symmetry quotient, and the equation atlas retains its fibres

**Date:** 2026-08-19
**Kind:** foundational mathematical synthesis and exterior equation-atlas design. Evidence and
research material only; this record schedules no construction.
**Truth discipline:** classical statements are marked **proved-standard**; displayed algebra first
derived in this record is **proved-derived**; correspondences into holonics are **interpretation**;
proposed future uses are **conditional**; missing physical or executable joins are **open**. No
Millennium problem, physical quantum dynamics, cosmological model, Navier--Stokes construction, or
mathematics-codec executable capability is promoted here.

## Primary sources and standing owners

**Truth status: established-bounded.**

External sources inspected for this synthesis:

1. Eric W. Weisstein, [“Polygon”](https://mathworld.wolfram.com/Polygon.html), [“Convex
   Polygon”](https://mathworld.wolfram.com/ConvexPolygon.html), [“Concave
   Polygon”](https://mathworld.wolfram.com/ConcavePolygon.html), [“Convex
   Hull”](https://mathworld.wolfram.com/ConvexHull.html), [“Carathéodory's Fundamental
   Theorem”](https://mathworld.wolfram.com/CaratheodorysFundamentalTheorem.html), and [“Happy End
   Problem”](https://mathworld.wolfram.com/HappyEndProblem.html), MathWorld.
2. Douglas N. Arnold, Richard S. Falk, and Ragnar Winther, [“Finite element exterior calculus: from
   Hodge theory to numerical stability,” arXiv:0906.4325](https://arxiv.org/abs/0906.4325).
3. Sean M. Carroll, [“Lecture Notes on General Relativity,”
   arXiv:gr-qc/9712019](https://arxiv.org/abs/gr-qc/9712019).
4. Xingzhi Sun et al., [“Geometry-Aware Generative Autoencoders,”
   arXiv:2410.12779](https://arxiv.org/abs/2410.12779); Laurent Cheret et al.,
   [“Manifold-Matching Autoencoders,” arXiv:2603.16568](https://arxiv.org/abs/2603.16568); Yonghyeon
   Lee, [“A Geometric Perspective on Autoencoders,”
   arXiv:2309.08247v2](https://arxiv.org/abs/2309.08247v2); and Michael M. Bronstein et al.,
   [“Geometric Deep Learning,” arXiv:2104.13478](https://arxiv.org/abs/2104.13478).

Standing repository owners are not replaced: `TABLET_THE_FLOW`, `TABLET_THE_MANIFOLD`,
`TABLET_THE_TURN`, `TABLET_THE_CHART`, `TABLET_THE_COMPRESSION`, `TABLET_THE_OPERATIONS`,
`TABLET_THE_REASONING_CYCLE`, `THE_SURFACES_ARE_PATHS`, the reusable Typst mathematics library,
`simplicial`, `holonic_complex`, `contact_gluing`, `exact_linear`, `analytic_field`, `diffusion`,
`receiver_exact_compression`, and the formulation-span owners.

---

## 1. The joined result

**Truth status: interpretation.**

The requested ideas form one chain only after four distinctions are kept intact:

```text
smooth field or section
  -> integrate over oriented cells
  -> discrete cochain and boundary incidence
  -> receiver quotient / compression
  -> possible rank, phase, or topology wall
  -> retained reconstruction fibre
```

A polygon is the smallest unusually complete example. Its boundary is a discrete one-cycle; its
filled lamina is a two-chain; its metric lives in lengths and turns; its dynamics require an added
constitutive law; its projection is receiver-relative; and its smooth/discrete comparison commutes
through Stokes. The same separation scales to meshes, manifold autoencoders, geometric networks,
fluids, circuits, and symmetry-reduced cosmology.

The strongest unification is therefore not “all these equations are identical.” It is:

> Every lawful reduction names the source complex, transported structure, receiver family,
> collapsed population, boundary, and condition under which the quotient reopens.

---

## 2. The filled polygon is not merely a closed line

### 2.1 Boundary, closure, and filling

**Truth status: proved-standard.**

Let \(P=(v_0,\ldots,v_{n-1})\) be a cyclically ordered planar vertex population, with
\(v_n=v_0\). Its oriented polygonal boundary is the one-chain

\[
B_P=\sum_{i=0}^{n-1}[v_i,v_{i+1}].
\tag{P.1}
\]

It is **closed** because

\[
\partial B_P=0.
\tag{P.2}
\]

A **filled polygonal lamina** is stronger: it is an oriented two-chain \(F_P\) satisfying

\[
\partial F_P=B_P.
\tag{P.3}
\]

For a simple Jordan polygon in the plane, \(F_P\) is the closure of the bounded component of
\(\mathbb R^2\setminus B_P\), with its orientation. For a triangulation

\[
F_P=\sum_a \epsilon_a[v_{a0},v_{a1},v_{a2}],
\qquad \epsilon_a\in\{+1,-1\},
\tag{P.4}
\]

every interior edge occurs twice with opposite induced orientation, leaving only \(B_P\).

This gives the rigorous distinction MathWorld's “filled polygon” language needs:

- **closed** means the boundary of the boundary vanishes;
- **filled** means the one-cycle is itself the boundary of an admitted two-chain.

On a domain with nontrivial first homology, a closed one-cycle need not bound inside that domain.
“Closed” and “filled” are therefore not synonyms.

### 2.2 Triangle fullness

**Truth status: proved-standard.**

For three non-collinear points (a,b,c) in a real affine plane, the filled triangle is the
two-simplex

\[
\Delta(a,b,c)
=
\{\lambda_0a+\lambda_1b+\lambda_2c:
  \lambda_i\ge0,
  \lambda_0+\lambda_1+\lambda_2=1\}.
\tag{P.5}
\]

With

\[
\Phi(u,v)=a+u(b-a)+v(c-a),
\qquad u\ge0, v\ge0, u+v\le1,
\tag{P.6}
\]

the definite interior integral is

\[
\int_{\Delta(a,b,c)}1\,dA
=
\frac12\left|\det(b-a,c-a)\right|.
\tag{P.7}
\]

The oriented area retains the hand:

\[
A_{\mathrm{or}}(a,b,c)
=
\frac12\det(b-a,c-a).
\tag{P.8}
\]

The ordinary positive area is the modulus receiver \(|A_{\mathrm{or}}|\), which deletes
orientation. The triangle did not become filled because an integration routine returned a real
number; it was filled because an admitted two-simplex had the declared boundary. The integral is a
receiver face of that object.

### 2.3 Polygonal area and winding

**Truth status: proved-standard.**

For a simple oriented polygon \(v_i=(x_i,y_i)\), Green's theorem gives

\[
A_{\mathrm{or}}(P)
=
\frac12\oint_{B_P}(x\,dy-y\,dx)
=
\frac12\sum_i(x_i y_{i+1}-x_{i+1}y_i).
\tag{P.9}
\]

For a self-intersecting polygon this is algebraic area weighted by the winding number:

\[
A_{\mathrm{wind}}(P)
=
\int_{\mathbb R^2}\operatorname{wind}(B_P,z)\,dA.
\tag{P.10}
\]

An even--odd fill and a nonzero-winding fill are different receiver conventions. A self-crossing
source cannot be assigned one “filled interior” until that convention is declared. Holes are
carried by oppositely oriented inner boundaries.

### 2.4 Complex coordinates do not automatically add a spatial axis

**Truth status: proved-standard.**

The complex plane is a two-dimensional real vector space:

\[
\mathbb C\cong\mathbb R^2,
\qquad z=x+iy.
\tag{P.11}
\]

A planar polygon with complex vertices therefore remains an ordinary real two-dimensional
polygon. Its oriented area is

\[
A_{\mathrm{or}}(P)
=
\frac12\operatorname{Im}\sum_i\overline z_i z_{i+1}
=
\frac1{2i}\oint_{B_P}\overline z\,dz.
\tag{P.12}
\]

A complex-valued integrand may carry phase, moment, or another paired receiver; it does not by
itself prove an extra physical direction or prevent a triangle from being seen. A complex
one-dimensional manifold is real two-dimensional. A genuinely higher-dimensional face requires a
different ambient real dimension, bundle, embedding, or receiver—not merely the glyph (i).

### 2.5 Lamina as transport surface

**Truth status: conditional.**

A simple polygonal lamina is a piecewise-linear two-manifold with boundary. A leaf blade, vertebral
lamina, plate, membrane, or mesh may likewise be modeled as a two-dimensional body only where its
local links satisfy the manifold condition. Branch junctions, tears, pinches, and attachments may
instead be singular complexes.

Geometry becomes an energy-distribution mechanism only after a constitutive structure is attached:
metric, thickness, density, stiffness, conductivity, refractive index, absorption, boundary load,
or another local law. The same lamina can carry different ecologies under different constitutive
maps. Shape constrains transport; shape alone is not the transport.

---

## 3. The smooth-to-discrete transition is clearest at Stokes

### 3.1 The exact commuting seam

**Truth status: proved-standard.**

Let \(K\) be an oriented cellulation of a smooth manifold and let
\(\omega\in\Omega^k(M)\). Integration defines the de Rham cochain

\[
(\mathcal R_K\omega)(\sigma^k)=\int_{\sigma^k}\omega.
\tag{S.1}
\]

Stokes gives the exact commutation

\[
\delta\,\mathcal R_K\omega
=
\mathcal R_K(d\omega),
\tag{S.2}
\]

because

\[
(\delta\mathcal R_K\omega)(\sigma^{k+1})
=
\int_{\partial\sigma^{k+1}}\omega
=
\int_{\sigma^{k+1}}d\omega.
\tag{S.3}
\]

This is the cleanest non-hand-waved smooth/discrete seam in the framework:

```text
smooth differential form --integrate over cells--> discrete cochain
          | d                                  | delta
          +---------------- commutes -----------+
```

Whitney forms and finite-element exterior calculus supply a return from simplicial cochains to
piecewise-polynomial forms while preserving the differential complex. Approximation error remains
a separate receiver; incidence and cohomology need not be sacrificed to obtain a finite carrier.

### 3.2 Polygonal curvature is an atomic measure

**Truth status: proved-standard.**

For a smooth plane curve parameterized by arc length \(s\),

\[
d\theta=\kappa(s)\,ds.
\tag{S.4}
\]

For a polygon, curvature is concentrated at vertices. If \(\delta_i\) is the signed exterior turn,

\[
\kappa_P=\sum_i\delta_i\,\delta_{v_i},
\qquad
\sum_i\delta_i=w\,\tau_0,
\tag{S.5}
\]

where \(w\) is winding and \(\tau_0\) is one full turn. A smooth curvature density has become a
discrete population without losing its integrated return. In Regge-type geometry the same move
places curvature on codimension-two hinges:

\[
\varepsilon_h
=
\tau_0-\sum_{\sigma\supset h}\theta_{h\sigma}.
\tag{S.6}
\]

This is already the repository's exact hinge-deficit posture. It is also why a triangulated
surface is more than a graph: oriented two-cells and their shared hinges carry structure which an
edge list alone cannot return.

### 3.3 Where a phase wall appears

**Truth status: interpretation.**

The smooth/discrete change is not itself always a phase transition. A phase wall appears when the
continuing transport class changes: an oriented minor crosses zero, a Jacobian rank drops, a cell
attaches or detaches, a cycle becomes a boundary, an edge crossing changes the planarization, or a
local trivialization cannot continue. The visible coordinate may move smoothly while the
incidence, rank, stabilizer, or reconstruction fibre changes discretely.

---

## 4. Arc calculus: the typed replacement for an untyped pi glyph

### 4.1 Full turn, half turn, and arc differential

**Truth status: proved-derived.**

Choose one flat circular calibration receiver with radius \(r_0>0\), circumference \(C_0\), and arc
length \(s\). Define

\[
\tau_0:=\frac{C_0}{r_0}
\quad\text{(one full turn)},
\qquad
\varpi_0:=\frac{\tau_0}{2}=\frac{C_0}{2r_0}
\quad\text{(one half turn)}.
\tag{A.1}
\]

The angular coordinate and its differential are

\[
\theta=\frac{s}{r_0},
\qquad
d\theta=\frac{ds}{r_0}
\tag{A.2}
\]

for a circle, and \(d\theta=\kappa(s)ds=ds/r_c(s)\) for a curve with local radius of curvature
\(r_c(s)\). Thus \(C_0\) and \(r_0\) are not the same species: each is a length, but \(C_0\) is an
integrated boundary path and \(r_0\) is a radial crossing. Only their declared ratio is a
dimensionless turn calibration.

### 4.2 Correction of the proposed exponent chain

**Truth status: proved-derived.**

The half-turn is

\[
180^\circ=\varpi_0=\frac{C_0}{2r_0},
\tag{A.3}
\]

not \(\varpi_0/2\). Under the conventional radian glyph, \(\varpi_0=\pi\). Euler's identity gives
\(e^{i\varpi_0}=-1\), hence

\[
2^{e^{i\varpi_0}}=2^{-1},
\qquad
\varpi_0\,2^{e^{i\varpi_0}}=\frac{\varpi_0}{2},
\tag{A.4}
\]

which is a quarter-turn, not \(180^\circ\). The exponentiation changes a scalar magnitude; it does
not encode the arc's winding lineage. The correct concavity test for a simple polygon is simply

\[
\alpha_i>\varpi_0
\tag{A.5}
\]

for at least one interior angle \(\alpha_i\).

For varying edge directions \(\theta_i\), use the principal signed turn

\[
\delta_i
=
\operatorname{Arg}_{(-\varpi_0,\varpi_0]}
\left(e^{i(\theta_{i+1}-\theta_i)}\right),
\qquad
\sum_i\delta_i=w\tau_0.
\tag{A.6}
\]

This retains the local \(\theta_i\), the total winding \(w\), and the branch aperture separately.

### 4.3 Circular and hyperbolic charts

**Truth status: proved-standard.**

The identity

\[
(\sin\theta+\cos\theta)^2
+
(\sin\theta-\cos\theta)^2
=2
\tag{A.7}
\]

is correct. It is the norm preservation of a scaled Hadamard rotation; the total deletes
\(\theta\). A separating face is, for example,

\[
(\sin\theta+\cos\theta)^2
-
(\sin\theta-\cos\theta)^2
=2\sin(2\theta).
\tag{A.8}
\]

Likewise

\[
\cosh^2t-\sinh^2t=1,
\qquad
\tanh^2t+\operatorname{sech}^2t=1.
\tag{A.9}
\]

Their sum is \(2\). But

\[
(\coth^2t-1)+(1-\operatorname{csch}^2t)=1,
\tag{A.10}
\]

not \(2\). The intended bridge remains valuable: circular rotations preserve the positive form
\(x^2+y^2\), while hyperbolic boosts preserve the indefinite form \(x^2-y^2\):

\[
R(\theta)^TR(\theta)=I,
\qquad
L(t)^TJL(t)=J,
\quad J=\operatorname{diag}(1,-1).
\tag{A.11}
\]

Analytic continuation joins their complex formulations; it does not make their real signatures,
causal cones, or receivers identical.

---

## 5. Convexity, concavity, hulls, and the triangle quantum

### 5.1 Convexity and reflex turns

**Truth status: proved-standard.**

A filled set \(K\subseteq\mathbb R^d\) is convex exactly when

\[
(1-t)x+ty\in K
\quad
\text{for all }x,y\in K,\ t\in[0,1].
\tag{C.1}
\]

For a simple planar polygon, convexity is equivalently the common weak sign of all consecutive
edge cross products. Strict convexity requires nonzero turns of one hand. Concavity means
nonconvexity; for a simple polygon it is equivalent to at least one reflex angle
\(\alpha_i>\varpi_0\).

The optics analogy needs its constitutive term. A positive convex lens commonly converges and a
concave lens diverges under its refractive-index hypotheses; mirrors reverse that everyday naming,
with a concave mirror converging and a convex mirror diverging. Focusing is determined by interface
orientation, curvature, propagation hand, and impedance/refractive law together—not by the word
“convex” alone.

### 5.2 Hull and Carathéodory

**Truth status: proved-standard.**

The convex hull is

\[
\operatorname{conv}(S)
=
\left\{\sum_j\lambda_jp_j:
  p_j\in S,\ \lambda_j\ge0,\ \sum_j\lambda_j=1\right\}.
\tag{C.2}
\]

Carathéodory's theorem states that in real affine dimension (d), each point of the hull uses at
most (d+1) source points. Therefore every point of a planar convex hull lies in a filled triangle
whose vertices come from (S).

**Truth status: interpretation.**

This is the exact sense in which the triangle is the quantum of planar convex filling: it is the
smallest simplex whose barycentric population can carry every point of the convex hull. It does not
say that one fixed triangle reconstructs the whole polygon, or that triangles alone supply a
constitutive physics.

### 5.3 Happy Ending and combinatorial aperture

**Truth status: proved-standard.**

For every \(n\ge3\), sufficiently many planar points in general position contain \(n\) points in
convex position. The known classical bounds include

\[
2^{n-2}+1
\le g(n)
\le
\binom{2n-4}{n-2}+1,
\tag{C.3}
\]

with later improvements to the upper bound; the exact general value remains open. The known values
(g(3),g(4),g(5),g(6)) are (3,5,9,17). The binomial coefficient counts a combinatorial aperture;
it is not itself the generator of convexity.

The polygon boundary is a Hamiltonian cycle in its own cycle graph by construction. Convexity does
not imply that an arbitrary graph on those vertices is Hamiltonian. Visibility, obstacle, and
transport graphs require their own incidence.

---

## 6. Manifold autoencoders, GDL, and phase walls

### 6.1 An autoencoder is a chart pair with a reconstruction fibre

**Truth status: interpretation.**

For an encoder and decoder

\[
E:X\to Z,
\qquad
D:Z\to X',
\tag{M.1}
\]

the latent point (E(x)) is not the manifold and a small reconstruction loss is not a topology
certificate. The lawful object includes

\[
\mathcal F_R(z)
=
\{x\in X:q_R(D(E(x)))=q_R(D(z))\},
\tag{M.2}
\]

the receiver-relative population which the latent/output face cannot separate.

Where (D) is differentiable, the pullback form

\[
g_Z(z)=J_D(z)^T J_D(z)
\tag{M.3}
\]

is positive semidefinite. It is a Riemannian metric only where \(J_D\) has the required full rank.
A phase/rank wall occurs where a maximal minor vanishes, the kernel dimension changes, or a chart
transition can no longer continue. One chart's coordinate singularity is not enough; the defect
must survive lawful recharting or change the receiver-visible fibre.

### 6.2 Distance matching and Markov kernels are receiver quotients

**Truth status: interpretation.**

The manifold-matching autoencoder preserves a selected pairwise-distance receiver. Complete
distances quotient translation and orthogonal orientation. A Gaussian kernel and row
normalization give

\[
K_{ij}=\exp(-d_{ij}^2/\sigma),
\qquad
P_{ij}=\frac{K_{ij}}{\sum_kK_{ik}}
=
\operatorname{softmax}_j(-d_{ij}^2/\sigma).
\tag{M.4}
\]

Only after (P) is declared a stochastic receiver does it become a Markov transition. Its
(t)-step entry sums the weights of all length-(t) paths. A quotient of states is dynamically
exact only under lumpability, equivalently an intertwining such as

\[
PC=C\overline P
\tag{M.5}
\]

for a declared condensation map (C), or with the full defect retained.

### 6.3 GDL supplies the scale/action chart

**Truth status: interpretation.**

Geometric deep learning's local equivariant map, constitutive nonlinearity, coarsening, and global
readout become:

```text
founded incidence
  -> equivariant local transport
  -> local interaction
  -> receiver condensation with fibre
  -> invariant face
```

At a critical point, correlation length grows and a fixed local receptive field ceases to separate
the relevant successors. GDL's scale hierarchy and renormalization-style block transformations are
therefore natural exterior instruments for phase analysis, but a coarsening is holonically lawful
only when future consequences factor or its reconstruction fibre and shortest separator return.

### 6.4 Four different changes

**Truth status: proved-derived.**

The following must not be conflated:

| event | exact question |
|---|---|
| rechart | is the transition invertible on the same body? |
| rank transition | did a kernel/image dimension change? |
| phase transition | did the maximal continuing transport stratum or constitutive branch change? |
| topology change | did incidence, homology, or the homeomorphism type change? |
| compression transition | did the declared receiver family change which interiors factor? |
| compactification | was a noncompact direction completed, bounded, or identified by a specified construction? |

A moduli-space path may cross a discriminant where topology changes, but merely moving in moduli
space does not imply topology change. Compactification may be a geometric completion or a physical
dimensional reduction; it is not a synonym for pressure, phase transition, or smaller storage.

---

## 7. Friedmann is a symmetry-reduced Einstein--fluid chart

### 7.1 The arc-calibrated Einstein expression

**Truth status: proved-derived.**

Using the fixed flat half-turn calibration \(\varpi_0=C_0/(2r_0)\), the Einstein equation can be
written without an untyped decimal or bare pi glyph as

\[
G_{\mu\nu}+\Lambda g_{\mu\nu}
=
\frac{8\varpi_0G_N}{c^4}T_{\mu\nu}.
\tag{F.1}
\]

This is an exact notational rebase of the standard equation because \(\varpi_0\) is the conventional
flat half-turn in radians. It is **not** permission to replace the coupling by a local varying
\(C(x)/r(x)\). Such a substitution would define a different theory and would owe covariance,
dynamics, dimensions, and evidence. The repository's “settled/bent/growing circle meter” remains an
interpretive receiver comparison; it does not derive physical general relativity.

### 7.2 Friedmann equations in the same calibration

**Truth status: proved-standard for the standard equations; proved-derived for the arc rebase.**

For a homogeneous, isotropic FLRW spacetime with scale factor \(a(t)\), Hubble rate
\(H=\dot a/a\), spatial-curvature sign \(k\), mass density \(\rho\), and isotropic pressure \(p\),

\[
H^2
=
\frac{8\varpi_0G_N}{3}\rho
+\frac{\Lambda c^2}{3}
-\frac{k c^2}{a^2},
\tag{F.2}
\]

\[
\frac{\ddot a}{a}
=
-\frac{4\varpi_0G_N}{3}
\left(\rho+\frac{3p}{c^2}\right)
+\frac{\Lambda c^2}{3},
\tag{F.3}
\]

and stress--energy conservation gives

\[
\dot\rho
+3H\left(\rho+\frac{p}{c^2}\right)=0.
\tag{F.4}
\]

If \(\epsilon=\rho c^2\) is used instead, the first matter term is
\(8\varpi_0G_N\epsilon/(3c^2)\), and the continuity law is
\(\dot\epsilon+3H(\epsilon+p)=0\). The density convention must travel with the equation.

### 7.3 The cosmological constant has two lawful unit faces

**Truth status: proved-derived.**

In geometric units of the field equation,

\[
[\Lambda]=L^{-2}.
\tag{F.5}
\]

Moved to the matter side, it has vacuum energy-density and mass-density faces

\[
\epsilon_\Lambda
=
\frac{\Lambda c^4}{8\varpi_0G_N},
\qquad
\rho_\Lambda
=
\frac{\Lambda c^2}{8\varpi_0G_N},
\qquad
p_\Lambda=-\epsilon_\Lambda.
\tag{F.6}
\]

Thus energy per volume and inverse-length-squared are two unit charts joined by the gravitational
coupling; neither is an untyped “curvature time.”

### 7.4 Why this is a compression and not a complete fluid

**Truth status: interpretation.**

FLRW symmetry collapses spatial dependence, shear, vorticity, anisotropic stress, and heat flux.
The complete Einstein--matter field has been projected into a few invariant faces
\((a,H,k,\rho,p)\). This is an exceptionally strong symmetry quotient with an enormous
reconstruction fibre. It is the cosmological analogue of the autoencoder warning: a compact latent
chart can carry the requested invariant evolution while failing to reconstruct local turbulence,
inhomogeneity, gravitational radiation, or topology.

---

## 8. Friedmann and Navier--Stokes meet through conservation, not identity

### 8.1 The direct bridge

**Truth status: proved-standard.**

Both relativistic perfect-fluid cosmology and classical fluid mechanics begin with local
conservation plus a constitutive law. The relativistic law is

\[
\nabla_\mu T^{\mu\nu}=0.
\tag{N.1}
\]

For an FLRW comoving congruence, expansion is

\[
\Theta=\nabla_\mu u^\mu=3H,
\tag{N.2}
\]

while shear, vorticity, and spatial acceleration vanish. The temporal projection of (N.1) is
(F.4). The spatial projection is trivial under exact homogeneity because there is no pressure
gradient to drive a local flow.

In Newtonian variables, compressible continuity and momentum are

\[
\partial_t\rho+\nabla\!\cdot(\rho u)=0,
\tag{N.3}
\]

\[
\rho(\partial_tu+u\!\cdot\nabla u)
=
-\nabla p+\nabla\!\cdot\tau+f.
\tag{N.4}
\]

The Hubble flow \(u(t,x)=H(t)x\) has \(\nabla\cdot u=3H\), so homogeneous continuity reduces to
an ordinary equation. Friedmann cosmology is therefore a symmetry-reduced gravitational fluid
system; it is not Navier--Stokes with a different name.

### 8.2 Pressure is a reaction face, not a conserved scalar

**Truth status: proved-standard.**

In incompressible flow, \(\nabla\cdot u=0\) is a constraint. Pressure acts as the Lagrange-multiplier
reaction which keeps the velocity in the divergence-free subspace; it is determined nonlocally by
a Poisson-type equation after taking divergence of momentum. Pressure is not conserved. Momentum
and energy balances are the conserved currents under their hypotheses.

**Truth status: interpretation.**

This supports the repository's hardware-fluid rule: “pressure” may be a receiver-indexed local
constraint reaction to incompatible flux and capacity, never a stored global scalar which chooses
the route. Viscosity must be a constitutive dissipation/transport term; a queue count or worker
count is not viscosity.

### 8.3 Incompressible does not mean infinitely uncompressible

**Truth status: proved-standard.**

An incompressible-fluid model holds density fixed, usually because density changes are negligible
over the admitted pressure, velocity, and time scales. Driving the material outside that regime can
activate compressibility, ionization, chemistry, nuclear reactions, or gravitational collapse. At
that point the constitutive body and its equations changed; the original approximation did not
claim to govern the new phase.

**Truth status: interpretation.**

The holonic compression analogue is precise: a quotient may be exact for the declared successor
family and fail when the aperture expands. Crossing the material's constitutive discriminant
reopens the fibre. “Incompressible” is not “nothing can be compressed”; it is “density is not a
load-bearing receiver coordinate inside this regime.”

---

## 9. Probability, Born, softmax, sigmoid, and loss

### 9.1 Born is a quadratic projective receiver

**Truth status: proved-standard.**

For a quantum state \(|\psi\rangle\), positive measurement operator \(E_i\), and its pure-state
density operator
\(\rho=|\psi\rangle\langle\psi|/\langle\psi|\psi\rangle\), the Born receiver is

\[
p_i
=
\frac{\langle\psi|E_i|\psi\rangle}
     {\langle\psi|\psi\rangle}
=
\operatorname{Tr}(\rho E_i),
\qquad
\sum_iE_i=I.
\tag{Q.1}
\]

For an orthonormal basis projector \(E_i=|i\rangle\langle i|\),

\[
p_i=\frac{|\psi_i|^2}{\sum_j|\psi_j|^2}.
\tag{Q.2}
\]

Global nonzero scale and global phase are projective gauges. Probabilities in one basis also delete
relative phase information which a different interference receiver can reopen. The squared modulus
is therefore a genuine quotient, but the physical Born rule additionally requires the Hilbert
space, positive measurement operators, tensor/composition law, dynamics, and calibrated apparatus.
It does not follow from the word “holonic” or from bra--ket notation.

### 9.2 Softmax and Born share a positive section but use different generators

**Truth status: proved-derived.**

Softmax is the positive-ray section

\[
p_i=\frac{e^{z_i/T}}{\sum_je^{z_j/T}},
\qquad
z\sim z+c\mathbf1.
\tag{Q.3}
\]

If one constructs amplitudes

\[
\psi_i=e^{z_i/(2T)}e^{i\phi_i},
\tag{Q.4}
\]

then the Born probabilities of the coordinate projectors equal softmax:

\[
\frac{|\psi_i|^2}{\sum_j|\psi_j|^2}
=
\operatorname{softmax}_i(z/T).
\tag{Q.5}
\]

This is an exact bridge, not an identity of ontologies. Softmax exponentiates real potentials and
deletes one common additive coordinate; Born squares complex amplitudes and, at one measurement
face, deletes phase. The amplitude phases \(\phi_i\) remain invisible to (Q.5) but visible to other
projectors.

### 9.3 Sigmoid, Ising, and phase response

**Truth status: proved-standard.**

Binary softmax is sigmoid:

\[
\sigma(x)=\frac{e^x}{1+e^x},
\qquad
2\sigma(x)-1=\tanh(x/2).
\tag{Q.6}
\]

For an Ising spin in local field \(h_i^{\mathrm{eff}}\),

\[
\Pr(s_i=+1\mid s_{\partial i})
=
\sigma(2\beta h_i^{\mathrm{eff}}),
\qquad
\mathbb E[s_i\mid s_{\partial i}]
=
\tanh(\beta h_i^{\mathrm{eff}}).
\tag{Q.7}
\]

The finite sigmoid is a smooth ratio chart. A thermodynamic phase transition appears only through
the coupled recurrence and/or infinite-size limit, where a free-energy derivative becomes
nonanalytic or multiple stable branches coexist. One softmax row is not already a phase transition.

### 9.4 Loss is a receiver covector, not the information itself

**Truth status: interpretation.**

Cross-entropy

\[
\mathcal L(q,p)=-\sum_iq_i\log p_i
\tag{Q.8}
\]

compares two declared probability faces. It cannot see a phase or causal distinction already
deleted by that receiver. A coordinate-basis Born loss may grade magnitudes correctly while missing
relative phase; a distance loss may preserve pairwise geometry while missing orientation and
holonomy; a next-token loss may miss plural successor structure.

The holonic loss object is therefore the returned receiver covector together with the population
it could not separate, its lineage, and the local adjoint transport. Scalar loss is a useful face,
never the complete information change.

---

## 10. Time parity supplies cancellation; the physical law supplies what is conserved

### 10.1 The common chain skeleton

**Truth status: proved-standard.**

For an oriented two-simplex,

\[
\partial[v_0v_1v_2]
=
[v_1v_2]-[v_0v_2]+[v_0v_1],
\qquad
\partial^2[v_0v_1v_2]=0.
\tag{T.1}
\]

In a triangulated lamina, every internal edge cancels between the two faces which induce opposite
hands.

**Truth status: interpretation.**

This is the exact combinatorial content of causal time parity. It explains why the triangle is the
minimal filled carrier of opposed internal incidence.

### 10.2 What parity does not establish alone

**Truth status: proved-standard.**

The identity \(\partial^2=0\) does not specify which physical quantity is conserved. A conserved
current requires a representation/constitutive law and a closed boundary. Noether's associations
are:

- time-translation invariance \(\to\) energy, when such a global symmetry exists;
- spatial translation invariance \(\to\) momentum;
- rotational invariance \(\to\) total angular momentum;
- a declared \(U(1)\) symmetry \(\to\) charge current.

Rotational **inertia** is not generally conserved; angular momentum \(L=I\omega\) is conserved in
the absence of external torque while (I) may change. Quantum spin is an intrinsic representation
label, and total angular momentum conservation still requires rotational symmetry. Rest mass is not
a universal conserved quantity in relativistic reactions; stress--energy is locally conserved.

Voltage and pressure are not conserved charges. Voltage is a potential difference/line integral;
pressure is an isotropic stress or constraint reaction. Their loop and gradient balances arise from
field and constitutive laws.

### 10.3 Circuits and complete returns

**Truth status: proved-standard.**

With node--edge incidence (B), edge current (j), stored node charge (q), and source (s),

\[
\dot q+Bj=s.
\tag{T.2}
\]

Kirchhoff current balance is the storage-free/source-free receiver. For a cycle matrix (Z),

\[
Z^Tv=0
\tag{T.3}
\]

holds for electrostatic/quasistatic potential drops; with changing magnetic flux the generalized
loop law carries the induced electromotive return rather than falsely reporting zero. Under
compatible current and voltage laws, Tellegen's theorem gives the power balance.

**Truth status: interpretation.**

The circuit makes the general rule explicit: completion around a loop cancels internal incidences,
but charge storage, source, admittance, electromagnetic induction, and dissipation determine the
actual conserved or departed population. “Time parity causes every conservation law” is too strong;
time parity is the common cancellation geometry through which a typed law can conserve.

---

## 11. Phase transitions, stress--energy, and cosmological flow

### 11.1 Landau--Ginzburg is the missing local bridge

**Truth status: proved-standard.**

A scalar or complex order parameter \(\phi\) may carry a free-energy density

\[
f[\phi]
=
\frac{a(T)}2|\phi|^2
+\frac b4|\phi|^4
+\frac\kappa2|D\phi|^2
+\cdots.
\tag{L.1}
\]

The sign and degeneracy of \(a(T)\), the symmetry of \(\phi\), boundary conditions, and fluctuations
determine the phase structure. The gradient term makes domain walls and defects carry stress. A
first-order transition has coexistence/latent heat and a discontinuous first derivative of free
energy; a continuous transition has a continuous order parameter with divergent or singular
higher response in the thermodynamic limit.

For superfluids a global complex phase is an order parameter. For superconductors the phase is
gauge-coupled; electromagnetic response and the Anderson--Higgs mechanism matter. The squared
magnitude of an order parameter is not automatically a Born probability.

### 11.2 Stress--energy carries the phase into Friedmann

**Truth status: conditional.**

When a physical field theory supplies a covariant action, variation with respect to the metric
produces its stress--energy tensor. A phase transition may change vacuum energy, pressure,
equation-of-state parameter, anisotropic stress, sound speed, or defect population; those changes
then alter the Friedmann source through \(\rho\) and \(p\). Temperature is not inserted directly into
Einstein's equation. It changes the material state and constitutive stress--energy.

A homogeneous Friedmann receiver sees only the spatially averaged perfect-fluid faces. Local
nucleation, vortices, magnetic domains, turbulence, and propagating walls lie in its reconstruction
fibre until perturbation and local-field receivers are admitted.

### 11.3 Magnetic alignment and compression

**Truth status: interpretation.**

Magnetization is a macroscopic quotient of a population of local orientations. Compression may
remove microscopic permutations while retaining the order parameter, susceptibility, domain
incidence, and response to an external field. At criticality the correlation length grows, so a
fixed local quotient ceases to be successor-complete. The quotient must refine, carry a nonlocal
generator, or return obstruction.

This is the exact relationship among softmax temperature, sigmoid magnetization, GDL coarsening,
and holonic compression: the score chart supplies local positive ratios; the interaction graph and
thermodynamic/causal recurrence determine the phase; the receiver family determines which
microscopic distinctions may lawfully collapse.

---

## 12. Knots, hypergeometry, crystals, primes, Hodge, RH, and Navier--Stokes

### 12.1 Projection is not source intersection

**Truth status: proved-standard.**

A knot is an embedding \(S^1\hookrightarrow\mathbb R^3\). A crossing in a planar diagram is a
receiver incidence with over/under data, not a self-intersection of the source curve. A knot has no
canonical enclosed planar area; a spanning surface, projection, or variational criterion must be
declared. Polyhedra, polychorons, and polytopes similarly require their full face incidence and
oriented boundary maps; one scalar “area” cannot replace the cell complex.

### 12.2 Crystal and prism readings

**Truth status: conditional.**

A computational body may be read as a prism or crystal only after it carries:

- a lattice or recurring incidence;
- a phase/group transport and holonomy;
- a founded propagation operator;
- a wavelength/spectrum receiver derived from that operator;
- boundary, diffraction/refraction law, and reconstruction testimony.

Then reciprocal-lattice and Bragg-type receivers can return coherent directions. Without those
items, “information wavelength” is a visualization, not a physical or mathematical invariant.

### 12.3 Prime constraints are receiver- and ring-relative

**Truth status: proved-standard.**

An integer prime area constrains an axis-aligned rectangle with integer side lengths because the
factorization is taken in \(\mathbb Z\). It does not constrain a rectangle with arbitrary positive
real side lengths in the same way. Likewise a trigonometric value such as
\(\sqrt2/2\) strongly constrains a unit-circle angle under a specified rational-angle/symmetry
receiver, but arbitrary analytic expressions can present the same value.

Primality, irreducibility, and caustic concentration become one transport question only after the
factorization category, operator, and receiver are declared. An irreducible in one ring may factor
after extension.

### 12.4 The honest RH/Hodge/Navier connection

**Truth status: interpretation.**

The filled-polygon distinction “cycle versus boundary” is the elementary homological seam relevant
to Hodge theory. On a Riemannian manifold a differential form decomposes, under the standard
hypotheses, into exact, coexact, and harmonic parts:

\[
\omega=d\alpha+\delta\beta+h.
\tag{H.1}
\]

In incompressible flow, the divergence-free constraint and pressure projection are naturally read
through this complex; finite-element exterior calculus preserves the differential incidence under
discretization. That is a real bridge between geometry and fluid computation.

Prime recurrence enters zeta through the Euler product in its convergent half-plane:

\[
\zeta(s)=\prod_p(1-p^{-s})^{-1},
\qquad \operatorname{Re}s>1.
\tag{H.2}
\]

The shared themes are global reconstruction from local cells, boundary versus non-boundary cycles,
scale, and singular continuation. They do not prove the Riemann Hypothesis, the Hodge Conjecture,
or three-dimensional Navier--Stokes regularity. The repository's Millennium rows remain receiver
maps naming where a deed would begin, not evidence that a problem moved.

---

## 13. The exterior equation atlas

### 13.1 Why it exists

**Truth status: definition.**

The new seed store is
[`research/equation-atlas/README.md`](../equation-atlas/README.md). It is a curated exterior research chart of
equation formulations and evidence-backed relations. It is not the runtime topology, an equation
parser, an AST, a CAS, a solver, a proof checker, or the semantic owner of mathematics.

The reusable Typst library under `papers/source/mathematics/` continues to own declared
definitions, lemmas, theorems, corollaries, and proofs. The exterior atlas instead makes prominent
formulations available as machine-readable material, with context, hypotheses, units, receiver,
collapsed fibre, source, and explicit boundary.

### 13.2 Stored objects

**Truth status: definition.**

`equations.jsonl` contains one JSON object per **formulation occurrence**. Its stable identifier
does not assert intrinsic mathematical identity. Equal displays from different sources remain
different occurrences until a comparison owner establishes a relation.

`relations.jsonl` is a directed multigraph. Every edge names:

- source and target occurrence;
- relation species;
- hypotheses;
- receiver under which the relation holds;
- truth grade;
- non-equivalence or open boundary.

`manifest.json` binds the schema, record counts, byte extents, and SHA-256 digests. It certifies the
stored exterior chart, not the truth of its mathematical contents.

`schema.json` defines the storage contract. All numerics inside equations remain strings; no float
is allowed to become semantic data. The atlas may be mounted later by the mathematics codec as
exterior material, but merely reading it would be reference consultation—not mathematical
recovery, training, or native conduct.

### 13.3 Graph law

**Truth status: conditional.**

The future recovered graph must have the form

```text
exterior formulation occurrence
  -> source/layout incidence
  -> plural typed operation complexes
  -> ordered transport and co-present fronts
  -> exact value/proof/render receivers
  -> residual and shortest separator
  -> ReconstructionFiber
```

Semantic edges such as `derives`, `rebase`, `quotient`, `adjoint`, `curvature`, or `conserves` may
enter native standing only when an existing owner returns their hypotheses and defect. The JSON
edge is research testimony, never an instruction to the engine.

---

## 14. Falsifiers and refusal language

**Truth status: conditional.**

The synthesis refuses or remains open when any of the following occurs:

1. a closed polygonal one-cycle is called filled without an admitted two-chain or fill rule;
2. a self-intersecting polygon receives ordinary area from shoelace without a winding/even--odd
   convention;
3. a complex coordinate is counted as an extra physical dimension without an ambient real chart;
4. a triangle's positive area deletes orientation with no quotient receipt;
5. a smooth/discrete claim fails the commuting differential/boundary test;
6. a topology change is inferred from a coordinate rechart, latent width, node count, or spectrum;
7. a manifold pullback form is called Riemannian where its Jacobian is rank-deficient;
8. a GDL coarsening or Markov quotient lacks exact factorization or a complete defect/fibre;
9. a half-turn is written as \(\varpi_0/2\), or a dimensionful length is exponentiated as if it were
   a turn;
10. convexity alone is said to determine optical convergence without medium and boundary hand;
11. the fixed flat arc calibration in Einstein/Friedmann is replaced by a varying local ratio
    without defining a different covariant theory;
12. Friedmann symmetry reduction is reported as complete Navier--Stokes or local cosmological
    fluid reconstruction;
13. pressure, voltage, rotational inertia, or rest mass is called universally conserved;
14. \(\partial^2=0\) is said to supply a physical conservation law without a represented current and
    boundary;
15. a softmax row is called a Born rule or phase transition without the missing Hilbert,
    interaction, recurrence, and receiver structure;
16. a probability loss grades a distinction already deleted by its measurement face;
17. compactification, compression, phase transition, and topology change are used as synonyms;
18. a prime-number geometry omits the ring, lattice, or factorization receiver;
19. the equation atlas is treated as recovered native mathematics, training, or a scheduler;
20. any RH, Hodge, or Navier--Stokes resemblance is promoted into progress on the corresponding
    Millennium problem.

---

## 15. Final synthesis

**Truth status: interpretation.**

The user's geometric intuition survives the corrections in a stronger form:

```text
triangle
  = minimal filled oriented cell
  = first exact interior whose internal boundary cancels

polygon / lamina
  = population of those cells plus winding, metric, and boundary

mesh / manifold chart
  = compatible local cells plus transitions, curvature, and open singularities

autoencoder / GDL coarsening
  = receiver chart over that body, exact only for named future consequences

softmax / sigmoid / Born face
  = positive projective sections with different generators and different deleted fibres

fluid / circuit / cosmology
  = conserved current plus constitutive law, observed through different symmetry and boundary quotients

phase transition
  = a discriminant event where continuation, rank, stabilizer, incidence, or constitutive branch changes
```

The simplest rigorous location of the smooth-to-discrete transition is not a mysterious collapse.
It is the commuting map from differential forms to cochains, with a filled triangle as the first
nontrivial cell and Stokes as the exact transport law. From there, curvature becomes hinge deficit,
flow becomes cochain current, conservation becomes a typed boundary return, and compression becomes
a declared quotient whose fibre can reopen.

**Truth status: open.**

The live body does not yet recover this equation atlas into mathematical sections, execute the
mathematics-codec vertical deed, derive physical Born dynamics, enact Friedmann cosmology, complete
Navier--Stokes, or infer knot/RH/Hodge structure from the new material. Those are separate future
returns. This deposit supplies the equations, distinctions, and graph contract needed to ask them
without rebuilding the conceptual foundation again.
