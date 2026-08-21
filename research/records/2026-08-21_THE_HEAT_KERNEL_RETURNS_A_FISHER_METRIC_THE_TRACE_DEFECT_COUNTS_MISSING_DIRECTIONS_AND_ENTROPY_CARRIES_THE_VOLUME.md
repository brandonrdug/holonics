# The heat kernel returns a Fisher metric, the trace defect counts missing directions, and entropy carries the volume

**Date:** 2026-08-21  
**Kind:** external-paper reading and mathematics-codec/GDL intermediary. It schedules nothing.  
**Primary source:** Jian Ge,
[“Heat kernel geometry and Gromov’s volume growth conjecture,” arXiv:2608.13553v1](https://arxiv.org/abs/2608.13553),
submitted 2026-08-13. The fetched 33-page PDF is 432,489 octets, SHA-256
`9518ea5939a53650f82d7b016e017df5e7cacfc1d8728e0ac2aaa25bf68fc4e5`.

**Truth boundary:** statements attributed to the paper are `historical` descriptions of an external
arXiv v1 or `conditional` under its hypotheses. The holonic/GDL correspondences are
`interpretation`. This record does not independently certify the new proof, promote the paper to
`proved-standard`, or construct an M0 capability.

## 1. The external theorem claimed

[historical] The paper states that if a complete, connected, noncompact Riemannian
\(n\)-manifold, \(n \geq 3\), satisfies

\[
\operatorname{Ric}_g \geq 0,
\qquad
\operatorname{Scal}_g \geq 1,
\]

then a dimension-only constant \(C_n\) gives

\[
\operatorname{Vol}_g B(p,R) \leq C_n R^{n-2}
\]

for every \(p\) and \(R>0\). The exponent is sharp on
\(S_a^2 \times \mathbb R^{n-2}\).

[conditional] Everything below inherits completeness, stochastic completeness, positive time, the
curvature conventions, regularity, and integrability hypotheses used by the paper. The pole
variable \(x\), output variable \(y\), and heat time \(t\) are distinct typed ports.

## 2. A manifold enters probability space through heat

[definition] With minimal heat kernel \(H(x,y,t)=e^{-h(x,y,t)}\), define

\[
d\mu_{x,t}(y)=H(x,y,t)\,d\operatorname{Vol}_y,
\qquad
\Phi_t(x)=H(x,\mathord\cdot,t)\,d\operatorname{Vol}.
\]

The heat map lands in probability densities. Its normalized Fisher pullback is the heat covariance

\[
\mathsf G_x(t)
  =2t\,\Phi_t^*g_F
  =2t\int_M d_xh\otimes d_xh\,d\mu_{x,t}.
\]

[conditional] Under \(\operatorname{Ric}\geq0\), the paper obtains

\[
0\leq\mathsf G_x(t)\leq g_x.
\]

On Euclidean space the normalization makes \(\mathsf G=g\).

[interpretation] \(\mathsf G_x(t)\) is a scale-indexed receiver section. Its eigenvectors are
directions visible to heat at scale \(\sqrt t\), and its eigenvalues are directional capacities in
the declared metric comparison. It is not the manifold, a learned latent metric, or an intrinsic
dimension by itself.

## 3. The trace is a scalar shadow of a tensor defect

[definition] The paper defines the heat-dimension defect

\[
\mathsf E_x(t)=\frac t2\left(n-\operatorname{tr}_g\mathsf G_x(t)\right),
\qquad
0\leq\mathsf E_x(t)\leq\frac{nt}{2}.
\]

[interpretation] The tensor \(g-\mathsf G\) retains orientation and anisotropy; its trace collapses
those directions to one scalar face. Calling \(\mathsf E\) “missing dimensions” is lawful only at
this heat/Fisher receiver.

[historical] On the sharp model \(S_a^2\times\mathbb R^{n-2}\), the large-time heat metric tends to

\[
0_{TS_a^2}\oplus I_{\mathbb R^{n-2}},
\]

so the trace tends to \(n-2\). The two lost directions are a returned model calculation, not a
general quotient map.

## 4. The defect has a centered source

[definition] Let

\[
\mathsf D_x(t)=\int_M
  \left|\operatorname{Hess}_x h_x-\frac{\mathsf G_x(t)}{2t}\right|^2
  d\mu_{x,t}
\]

and

\[
\mathsf Q_x(t)
 =4t^2\mathsf D_x(t)
  +|g_x-\mathsf G_x(t)|^2
  +2t\langle\operatorname{Ric}_x,\mathsf G_x(t)\rangle.
\]

[conditional] The paper derives the pole-variable source identity

\[
\square_x\mathsf E_x(t)=\frac12\mathsf Q_x(t),
\qquad
\square_x=\partial_t-\Delta_x.
\]

[interpretation] The three summands of \(\mathsf Q\) are not one undifferentiated “loss”:

- centered Hessian variance;
- squared covariance/metric deficit;
- curvature coupled to the visible heat directions.

Their sum is a source only inside the declared pole-variable heat equation. This is a precise
analogue for a holonic source section, not a claim that software loss is physical stress-energy.

## 5. Two source passages carry curvature into volume

[historical] The geometric core of the paper is the heat-averaged estimate

\[
P_s(\mathsf Q_\bullet(t))(z)
 \geq 2-C_n(t^{-1}+s^{-1})^{1/3}.
\]

A smooth spectral cutoff isolates the lowest covariance eigenline on the region where it is
separated. A weighted Weitzenböck estimate bounds the heat mass of the region where the source lies
below \(2-\varepsilon\).

[definition] For the paper’s normalized Nash entropy \(\mathsf S\), the second pole-variable source
identity is

\[
\square_x(-\mathsf S_x(t))=\frac{\mathsf E_x(t)}{t^2}.
\]

[historical] Minimal heat-potential comparison propagates the source twice:

\[
\mathsf Q\longrightarrow\mathsf E\longrightarrow-\mathsf S,
\]

yielding

\[
\mathsf S_x(T)\leq-\log T+C_n.
\]

The Li–Yau heat-kernel estimate then converts entropy decay to the asserted
\(R^{n-2}\) volume-growth bound.

[interpretation] This is a genuine causal diffusion chain: it has a semigroup, constitutive PDE,
positive source, boundary/integrability hypotheses, chronology, and an exterior geometric
consequence. It therefore satisfies far more of the causal-calculus diffusion contract than generic
message aggregation or attention.

## 6. Relation to geometric deep learning and autoencoders

[interpretation] The decoder pullback \(J_D^TJ_D\) and the heat Fisher pullback
\(2t\Phi_t^*g_F\) are both pullback quadratic forms, but they are not identical:

| heat construction | autoencoder/GDL comparison | retained difference |
|---|---|---|
| \(\Phi_t:M\to\mathcal P(M)\) | encoder/feature map | target is probability densities founded by the heat kernel |
| Fisher metric | declared ambient/feature metric | statistical metric on densities |
| \(2t\Phi_t^*g_F\) | decoder/feature pullback | scale and diffusion law are constitutive |
| eigenline cutoff | local spectral/gauge chart | exists only on a separated spectral region |
| \(n-\operatorname{tr}\mathsf G\) | effective-dimension receiver | trace discards directional geometry |
| heat semigroup | message propagation | satisfies a stated PDE and stochastic completeness |

[interpretation] The paper supplies a concrete scale-dependent geometric receiver that GDL’s
general blueprint leaves abstract. It does not recover a manifold from samples, learn a connection,
or prove an equivariant neural architecture.

## 7. Compression boundary

[interpretation] The exponent \(n-2\) is a macroscopic volume-growth consequence of the heat defect.
It is not by itself receiver-exact compression. No encoder/decoder factorization, lumpability
intertwiner, or complete `ReconstructionFiber` is returned.

[conditional] A later holonic use may ask whether the eigenvalues/eigenprojections of \(\mathsf G\)
found a lawful scale quotient. It must retain:

- the full tensor before taking the trace;
- the spectral-gap region and its complement;
- the smooth cutoff and cutoff energy;
- pole/output lineage;
- heat time and semigroup law;
- the defect source and entropy/volume receivers.

## 8. M0 source fixture

[open] The paper is valuable natural M0 material, but the complete 33 pages are too broad for the
first separating deed. The bounded natural-source control is:

- PDF page 5: pole/output distinction, Fisher pullback, \(\mathsf G\), and \(\mathsf E\);
- PDF page 10: the pointwise source identity \(\square_x\mathsf E=\mathsf Q/2\);
- vector/text layer and a raster rendering admitted as separate testimony;
- ambiguity controls on \(x/y\), \(G/g\), \(\mathsf E/E\), tensor product versus multiplication,
  subscripts, \(t/2\), and \(\square_x\).

[open] The synthetic companion remains harmonic conjugation. It supplies a known projective
incidence complex and affine degeneration; the paper supplies real born-digital mathematical
layout. M0 asks only whether source/layout incidence survives the two chart families and returns
their disagreement fibre. It does not ask the engine to prove the paper or interpret the symbols.

## 9. Falsifiers and cautions

[open] Before this source supports a stronger claim:

- independent experts must scrutinize the arXiv-v1 proof and its imported analytic estimates;
- a pole derivative may not be silently exchanged with an output derivative;
- \(\operatorname{tr}\mathsf G\) may not replace \(\mathsf G\);
- a spectral eigenline may not be extended through a gap-closing locus without a returned
  obstruction;
- heat-visible dimension may not be identified with topological, Hausdorff, latent, or model
  dimension;
- Nash entropy may not be identified with softmax entropy without an explicit map and boundary;
- the volume exponent may not be advertised as an exact codec factor.

[interpretation] The paper’s strongest contribution to this project is the typed chain

\[
\text{heat probability map}
\to \text{Fisher pullback}
\to \text{directional trace defect}
\to \text{centered curvature source}
\to \text{entropy decay}
\to \text{volume-growth receiver}.
\]

It is a rigorous external example of diffusion producing geometry-dependent information loss while
retaining the source terms that caused it.
