# The architecture is a domain action, the gauge carries the section, and the coarsening owes its fibre

**Date:** 2026-08-18
**Kind:** external-research synthesis and later-audit instrument. Evidence only; it schedules no
construction.
**Truth status:** **established-bounded** for the report of the cited paper at its declared scope;
**proved-standard** only where a standard mathematical definition or theorem is stated separately;
**interpretation** for the structure-preserving correspondence to holonics; **conditional** for the
proposed Phoenix and mathematics-codec uses under their named hypotheses; **open** for every
unbuilt join.
**Construction boundary:** no executable capability is promoted. The active Phoenix work, its
blueprints, and [CONSTRUCTION_STATE.md](../../CONSTRUCTION_STATE.md) are untouched by this record.
**Intended use:** after the current Phoenix dissection and compression work returns, this record is
an independent architecture audit and a source of exact candidate identities, defects, compression
tests, and falsifiers. It is then an intermediary to the
[mathematics-codec blueprint](../../blueprint/THE_MATHEMATICS_CODEC_RECOVERS_THE_OPERATION_COMPLEX_AND_EVERY_RESULT_RETURNS_AS_A_RECEIVER_FACE.md),
not a replacement for it.

## Primary source

Michael M. Bronstein, Joan Bruna, Taco Cohen, and Petar Veličković,
[“Geometric Deep Learning: Grids, Groups, Graphs, Geodesics, and Gauges,” arXiv:2104.13478v2](https://arxiv.org/abs/2104.13478),
2021, DOI
[10.48550/arXiv.2104.13478](https://doi.org/10.48550/arXiv.2104.13478).

The complete 160-page PDF was read, including the 127-page expository body and bibliography.
Section and printed-page references below are to that version.

---

## 0. What this source contributes

**Truth status: established-bounded.**

This paper is the strongest exterior reference found so far for the proposition that familiar
neural architectures are not isolated species. Its central move is the Erlangen Programme:
classify a geometry by the transformations and invariants it admits, then derive the associated
architecture from the domain, transformation family, locality, deformation stability, and scale
separation.

It explicitly treats:

- convolutional neural networks;
- group-equivariant CNNs;
- graph neural networks;
- Deep Sets;
- Transformers;
- equivariant message-passing networks;
- intrinsic mesh CNNs;
- recurrent neural networks and LSTMs;

as realizations of one geometric architecture blueprint over different domains and transformation
families.

The paper is a tutorial and synthesis. It is not primarily a new theorem, a trained system, or an
experimental model. Its authors say that they are systematizing the field and “connecting the
dots” between methods that are repeatedly reinvented and renamed across application domains
(Preface, pp. 1-2).

The source explicitly bounds itself to representation-learning architecture and inductive bias.
It does not centrally develop generative modelling, self-supervised learning, reinforcement
learning, optimization, loss design, or regularization procedures (Introduction, pp. 4-5).
Consequently, it is load-bearing for architectural unification and not for a theory of hexis,
autograd, MTP, denoising diffusion, Phoenix cultivation, source-detached remount, or ablation.

---

## 1. The paper’s correction is also ours

**Truth status: established-bounded.**

The Preface diagnoses a “zoo” of architectures with too few unifying principles. Its remedy is not
to choose the correct architecture. It is to identify the common mathematical constraints from
which the architectures arise.

That is a direct external precedent for the user’s position:

> Architectures are differently efficient codecs and transport realizations over mathematical
> spaces; they are not ontologically separate kinds of intelligence.

The paper’s unification is narrower than holonics. It unifies representation-learning
architectures through geometry. It does not unify caused occurrence, changing topology,
irreversible quotients, world-mediated return, durable morphology, or apparatus. The overlap is
therefore real and bounded rather than rhetorical.

---

## 2. The source object: domain, section, and action

**Truth status: proved-standard for the definitions; established-bounded for their use in the
paper. Source: Sections 3.1-3.2, pp. 12-19.**

The paper begins with a domain \(\Omega\), a vector space of channels or fibre values \(C\), and the
space of signals

\[
\mathcal X(\Omega,C)
=
\{x:\Omega\longrightarrow C\}.
\tag{GDL.1}
\]

A transformation group \(G\) acts on the domain. The action induces an action on sections:

\[
(g.x)(u)=x(g^{-1}u).
\tag{GDL.2}
\]

A linear representation is a homomorphism

\[
\rho:G\longrightarrow GL(V),
\qquad
\rho(gh)=\rho(g)\rho(h).
\tag{GDL.3}
\]

A receiver \(f:\mathcal X(\Omega)\to Y\) is invariant when

\[
f(\rho(g)x)=f(x),
\tag{GDL.4}
\]

and a section-valued passage \(F:\mathcal X(\Omega,C_{\mathrm{in}})
\to\mathcal X(\Omega,C_{\mathrm{out}})\) is equivariant when

\[
F(\rho_{\mathrm{in}}(g)x)
=
\rho_{\mathrm{out}}(g)F(x).
\tag{GDL.5}
\]

The distinction is essential. Intermediate constructions generally transform equivariantly.
Only a declared output receiver may identify the transformed population and return an invariant
face.

### Automorphism and isomorphism remain separate

An automorphism is a structure-preserving invertible map from a body to itself. An isomorphism is a
structure-preserving invertible map between two bodies. Source-presentation identity, denoted-value
equality, receiver equality, isomorphism, and occurrence identity are not interchangeable.

### Structure is a subgroup ladder

Adding structure restricts the transformations that preserve it. A larger transformation group
admits fewer invariants because it identifies a larger orbit; passage to a subgroup permits more
invariants. This gives an exterior mathematical instance of a quotient/refinement ladder:

\[
H\subseteq G
\quad\Longrightarrow\quad
\text{\(G\)-invariance collapses at least the distinctions collapsed by \(H\)-invariance.}
\tag{GDL.6}
\]

This does not select a correct group. It says what follows once the group action has been declared
and exhibited.

---

## 3. The three geometric priors

### Symmetry and equivariance

**Truth status: established-bounded. Source: Section 3.1, pp. 12-17.**

Symmetry restricts the function family to transports that commute with a declared group action.
This is an inductive bias: the architecture is constructed so that the commuting law holds.
The paper does not establish that the symmetry was discovered from material.

### Deformation stability

**Truth status: established-bounded. Source: Section 3.3, eqs. 4-5, pp. 19-22.**

Small deformations do not form a group: composing two transformations inside a small aperture may
leave it. The paper therefore does not invent an approximate symmetry group. It introduces a
deformation cost \(c(\tau)\), vanishing on the exact symmetry group, and asks for a bound

\[
\|f(\rho(\tau)x)-f(x)\|
\le
C\,c(\tau)\|x\|.
\tag{GDL.7}
\]

For varying domains it writes

\[
\|f(x,\Omega)-f(\widetilde x,\widetilde\Omega)\|
\le
C\|x\|\,d_{\mathcal D}(\Omega,\widetilde\Omega).
\tag{GDL.8}
\]

The norm is a receiver face of a complete discrepancy. The deformation cost and the domain
distance are declared instruments, not invariants recovered by the paper.

### Scale separation

**Truth status: established-bounded. Source: Section 3.4, pp. 22-27.**

For a coarsened domain \(\Omega_j\) and map
\(P_j:\mathcal X(\Omega)\to\mathcal X_j(\Omega_j)\), the paper expresses local stability as

\[
f\approx f_j\circ P_j.
\tag{GDL.9}
\]

The intent is to separate local interactions from long-range ones by moving through a hierarchy of
coarser domains. The approximation sign carries no general exact remainder or reopening rule.
This is the place where the paper and receiver-exact holonic condensation differ most sharply.

---

## 4. The Geometric Deep Learning blueprint

**Truth status: established-bounded. Source: Section 3.5, Figure 8, pp. 27-30.**

The architecture factorization is

\[
f
=
A\circ\sigma_J\circ B_J\circ P_{J-1}
\circ\cdots\circ
P_1\circ\sigma_1\circ B_1.
\tag{GDL.10}
\]

Its pieces are:

- \(B_j\): local equivariant maps;
- \(\sigma_j\): local nonlinear maps;
- \(P_j\): coarsening maps;
- \(A\): a global invariant readout.

The paper correctly presents this as a list of geometric constraints rather than a single required
implementation. It is a factorization shared by architecture families.

### The holonic reading

**Truth status: interpretation.**

The same word reads:

| GDL factor | holonic species |
|---|---|
| \(B_j\) | local typed transport through caused incidence |
| \(\sigma_j\) | local constitutive response or interaction |
| \(P_j\) | receiver-relative quotient or condensation |
| \(A\) | invariant receiver face |
| composition | ordered transport word with port lineage |

The factorization may be used as an exterior architecture chart. It must not become a universal
layer ontology. In particular:

- locality comes from actual incidence, not an authored radius;
- a nonlinearity must commute with the declared feature representation;
- a coarsening returns its collapsed population and reopening rule;
- a global invariant readout is a face and cannot act as machinery;
- distinct ordered words remain distinct even when their final face agrees.

---

## 5. The five geometric domains

**Truth status: established-bounded. Source: Section 4 and Figure 9, pp. 30-68.**

The “5G” taxonomy is pedagogical rather than a theorem, but the mathematics it organizes is useful:

| exterior domain | structure and transformation | architecture face |
|---|---|---|
| grid | translation | CNN |
| group or homogeneous space | global group action | group CNN |
| graph | permutation and local adjacency | GNN |
| geodesic manifold | metric and isometry | intrinsic/mesh CNN |
| gauge bundle | local frame and structure group | gauge-equivariant network |
| temporal grid | ordered recurrence and bounded time warping | RNN/LSTM |
| complete or masked relational graph | permutation plus attention and position | Transformer |

The table is not an architecture registry for Eros. It is a cross-codec test population over which
the same action, locality, connection, scale, and receiver questions can be posed.

---

## 6. Graphs, attention, and message transport

### Graph locality

**Truth status: established-bounded. Source: Sections 4.1 and 5.3, pp. 31-35 and 77-80.**

For a graph \(G=(V,E)\), node features and adjacency are synchronized under a permutation:

\[
X\mapsto PX,
\qquad
A\mapsto PAP^\top.
\tag{GDL.11}
\]

A graph-valued passage is permutation equivariant when

\[
F(PX,PAP^\top)=PF(X,A).
\tag{GDL.12}
\]

The paper constructs local equivariant functions by applying one permutation-invariant local law to
each neighborhood.

### Three GNN transport families

**Truth status: established-bounded. Source: Figure 17 and Section 5.3, pp. 78-80.**

The paper organizes practical GNNs as:

\[
\text{convolutional}
\subseteq
\text{attentional}
\subseteq
\text{message-passing}
\tag{GDL.13}
\]

in representable function families under its displayed forms.

This is not an equivalence of training, work, memory, topology, or causal ecology. It is a useful
foreign transport-function taxonomy for Phoenix dissection.

### Transformers

**Truth status: conditional under the paper’s stated set/graph aperture. Source: Section 5.4,
pp. 80-83.**

Unmasked self-attention on an unordered set can be represented as an attentional GNN over a complete
graph. Softmax-normalized attention coefficients may then be read as a feature-dependent soft
adjacency face.

This statement does not transfer unchanged to a causal or sliding-window Transformer:

- the causal mask makes the predecessor incidence directed;
- a sliding window removes candidate contacts;
- positional encoding adds a grid or group-action prior;
- residual transport, normalization, MLP interaction, and chronology are outside the simple
  complete-graph attention equation;
- a post-softmax coefficient does not prove source adjacency, physical interaction, or causality.

The lawful holonic reading is:

> The mask declares the candidate predecessor aperture; attention returns a compatibility and
> transport face over that aperture; later receiver consequences decide which contacts are
> load-bearing.

### Softmax

**Truth status: interpretation.**

The paper’s “soft adjacency” language supports using normalized attention as an adjacency receiver.
It does not support making softmax the topology. In holonic terms, normalized coefficients are
relative ratio faces over a declared candidate population. Their denominator couples the local
population, but neither nonzero mass nor maximal mass founds contact.

An intervention that changes attention weights in a value-null direction must not silently create
or remove source edges. A mask intervention must move the admitted predecessor incidence.

---

## 7. Diffusion is part of the architecture discussion

**Truth status: established-bounded for the paper; interpretation for the correspondence. Source:
Sections 4.4, 4.6, and 5.3, pp. 52-65 and 78-80.**

The paper defines the Laplace-Beltrami operator

\[
\Delta=\nabla^\ast\nabla,
\tag{GDL.14}
\]

and relates it to heat diffusion, wave propagation, intrinsic geometry, and spectral filtering.
In its graph discussion, local neighborhood aggregation is variously called diffusion,
propagation, or message passing.

This materially supports keeping diffusion inside the architecture synthesis rather than treating
it as unrelated to autoregression or logit transport.

The correspondence is conditional. Generic learned aggregation becomes causal-calculus diffusion
only after declaring and returning:

- caused incidence;
- local capacity or stalk;
- constitutive operator;
- boundary;
- chronology or event interval;
- current;
- conservation, departure, positivity, or other named law;
- receiver;
- reconstruction testimony.

The paper does not discuss modern generative diffusion, stochastic denoising, DiffusionGemma, or
MTP. It is evidence for geometric/operator diffusion, not for those distinct schedules.

---

## 8. Manifolds, fibres, gauges, and connections

**Truth status: proved-standard for the mathematical definitions; established-bounded for their use
in the paper. Source: Sections 4.4-4.5, pp. 44-61.**

The paper’s strongest correspondence to holonics is its insistence that:

1. a geometric vector is not its coordinate array;
2. vectors at different base points live in different fibres;
3. they cannot be compared or aggregated without transport;
4. a local frame is arbitrary and may not determine the underlying object;
5. a smooth global frame may not exist;
6. transport can be path dependent;
7. loop return is holonomy.

### Gauge transformations

For a rank-\(d\) bundle over \(\Omega\), a gauge transformation is a local group-valued map

\[
g:\Omega\longrightarrow G.
\tag{GDL.15}
\]

If a section has local coordinates \(x(u)\) in frame \(\omega_u\), a change of frame
\(\omega'_u=\omega_u\circ g_u\) changes its coordinate representation as

\[
x'(u)=\rho(g_u)^{-1}x(u)
\tag{GDL.16}
\]

while leaving the underlying section unchanged.

Gauge is therefore an invertible local change of frame. It is not a synonym for camera projection,
pooling, OCR collapse, a scalar receiver, or any other lossy face.

### Parallel transport before interaction

The paper’s gauge-equivariant convolution has the form

\[
(x\star\Theta)(u)
=
\int_{\Omega}
\Theta(u,v)\rho(g_{v\to u})x(v)\,dv,
\tag{GDL.17}
\]

where \(g_{v\to u}\) transports a value from the fibre at \(v\) into the fibre at \(u\) before the
interaction.

This is an exterior conventional expression of a typed local interaction:

~~~text
section at v
→ connection transport along a declared path
→ section in the fibre at u
→ local constitutive response
→ receiver section at u
~~~

If alternative paths produce different returns, the difference is holonomy and may not be
silently equated.

### Two different meanings of fibre

A vector-bundle fibre is the local value space over a base point. A ReconstructionFiber is the
receiver-indexed population of alternative predecessors or continuations collapsed by a quotient.
They may interact in one construction and they are not the same object.

---

## 9. Meshes, discretization, and functional maps

**Truth status: established-bounded. Source: Section 4.6, pp. 61-68.**

A triangular mesh is treated as a graph plus oriented triangular face incidence. Under manifold-mesh
hypotheses, local vertex links are disk-like and the mesh approximates a surface. These hypotheses
do not apply to arbitrary graphs, singular complexes, or non-manifold meshes.

### Polynomial and rational operator filters

For a founded Laplacian \(\Delta\), polynomial filters have the form

\[
p(\Delta)
=
\sum_{k=0}^{r}\alpha_k\Delta^k.
\tag{GDL.18}
\]

They are local to an \(r\)-hop neighborhood, but the physical radius represented by \(r\) changes
with mesh resolution.

Rational and Cayley filters can be more stable across resolution, but they introduce nonlocal,
decaying tails and require solution/inversion. Their inverse is a response/preimage transport with
kernel, cokernel, singular locus, and reconstruction fibre. It is not automatically a rebase.

### Functional maps

Rather than require point-to-point identity between two discretizations, the paper uses a linear
map between function spaces

\[
C:\mathcal X(\Omega)\longrightarrow\mathcal X(\Omega').
\tag{GDL.19}
\]

Under its stated orthogonality and area-preservation conditions, an operator transforms as

\[
Q'=CQC^\top.
\tag{GDL.20}
\]

This is a useful external model for:

- remeshing;
- cross-resolution mathematical graphics;
- transporting an atlas between different lattice populations;
- comparing a foreign lifted model with a native ecology;
- changing discrete carriers without claiming their vertices are identical.

The paper also warns that direct high-frequency Laplacian eigenvectors are unstable under small
domain perturbations. Spectral agreement is a receiver face and does not identify the body.

---

## 10. Recurrence, time warping, and the SSM bridge

**Truth status: established-bounded for the paper; interpretation for the SSM correspondence.
Source: Sections 5.7-5.8, pp. 89-101.**

The recurrent update is

\[
h^{(t)}=R(z^{(t)},h^{(t-1)}).
\tag{GDL.21}
\]

The paper interprets gated recurrent networks through a time reparameterization
\(\tau:\mathbb R_+\to\mathbb R_+\). Using a first-order Taylor approximation, it derives

\[
h^{(t+1)}
=
\Gamma(z^{(t+1)},h^{(t)})
R(z^{(t+1)},h^{(t)})
+
\bigl(1-\Gamma(z^{(t+1)},h^{(t)})\bigr)h^{(t)}.
\tag{GDL.22}
\]

The gate is interpreted as fitting the local derivative \(d\tau/dt\). The derivation is bounded:

- it uses a first-order approximation;
- destructive time contractions may remove intermediate information;
- it establishes invariance of a model class, not zero-shot invariance of one trained model under
  every time warp.

This is nevertheless useful for the SSM discussion. It gives an exterior geometric account of a
learned discrete step size and a transition between continuous and discrete time charts. It does not
supply the full SSM state and observation equations.

---

## 11. The holonic correspondence and its boundary

**Truth status: interpretation.**

| paper object | holonic reading | necessary correction |
|---|---|---|
| domain \(\Omega\) | situated base/incidence body | Eros may recover incidence rather than receive it a priori |
| section \(x\) | carried local construction | no internal data/program distinction |
| group \(G\) | admitted reversible transformation family | action must be exhibited and non-vacuous |
| representation \(\rho\) | enactment on typed ports/fibres | abstract group and matrix chart remain separate |
| equivariance | commuting transport square | return the full defect when it fails |
| invariance | receiver quotient | retain collapsed distinctions |
| receptive field | local caused incidence | no authored radius as topology |
| nonlinearity | local constitutive response | must commute with nontrivial fibre representations |
| coarsening | condensation | exact factorization or certified defect plus ReconstructionFiber |
| gauge | local invertible frame | not every receiver or projection |
| connection | typed local transport | preserve path and hand |
| holonomy | loop-return defect | never reduce first to a scalar |
| Laplacian diffusion | exact local transport generator | add capacity, boundary, chronology and return |
| functional map | cross-discretization section transport | state hypotheses and lost fibres |
| spectrum | operator-indexed receiver face | spectrum never identifies the source body |

The paper begins with domain, signal, and architecture as separate supplied objects. Holonics begins
with situated occurrences and caused incidence, permits the topology to change, and denies an
internal data/program distinction. The correspondence is therefore an embedding of a conventional
architecture description into the broader causal calculus, not an identity.

---

## 12. What the live body already owns

**Truth status: established-bounded for the cited owners at their implemented apertures, inspected
2026-08-18.**

| owner | existing bounded return |
|---|---|
| [gauge.rs](../../crates/holonic-structure/src/gauge.rs) | refuses a declared gauge whose action is empty or trivial and exhibits the moved population |
| [ported_operation.rs](../../crates/holonic-engine/src/ported_operation.rs) | typed foreign ports, operation words, fronts, candidates, realization defects and exact linear charts |
| [structure_group.rs](../../crates/holonic-engine/src/structure_group.rs) | finite group elements, group-valued connections, conjugacy-class holonomy, commutators, abelianization loss and double covers |
| [lattice_gauge.rs](../../crates/holonic-engine/src/lattice_gauge.rs) | exact finite lattice-gauge representations, plaquette holonomy, gauge action and transfer readings |
| [causal_body.rs](../../crates/holonic-engine/src/causal_body.rs) | event-indexed incidence, exact reversible connections, holonomy generators, receiver-local sections and changing sheaf fields |
| [diffusion.rs](../../crates/holonic-engine/src/diffusion.rs) | exact finite oriented diffusion with capacities, conductances, boundary source, current, conservation and energy testimony |
| [sheaf_diffusion.rs](../../crates/holonic-engine/src/sheaf_diffusion.rs) | exact cellular sheaf, restriction maps, Hodge operator, event transport and inverse certificate |
| [chain.rs](../../crates/holonic-structure/src/chain.rs) | ordered composition, rebase, path defect and closed-loop holonomy |
| [simplicial.rs](../../crates/holonic-engine/src/simplicial.rs) and [holonic_complex.rs](../../crates/holonic-engine/src/holonic_complex.rs) | exact oriented local incidence, higher cells, local transport, closed-hull coarsening and retained child structure |
| [contact_gluing.rs](../../crates/holonic-engine/src/contact_gluing.rs) and [gluing.rs](../../crates/holonic-engine/src/gluing.rs) | orientability, seams, local/global obstruction and exact Mayer-Vietoris connecting return |
| [receiver_exact_compression.rs](../../crates/holonic-engine/src/receiver_exact_compression.rs) | receiver quotient, successor refinement, collapsed population and shortest separator |
| [exact_linear.rs](../../crates/holonic-engine/src/exact_linear.rs) | exact matrix products, applications, factorization, preimage fibres, rebase receipts and metric adjoints |

These owners establish that the paper does not authorize a new GeometricDeepLearning subsystem.
The next action is an attempted composition.

---

## 13. The exact missing seam

**Truth status: open.**

The inspected owners stop at one precise boundary:

- **structure_group** owns abstract finite group-valued transport and deliberately chooses no
  representation;
- **ported_operation** owns typed ports, operation words, fronts, and exact realization;
- **causal_body** owns connections and local receiver sections;
- **Chain** owns composition and defect;
- **receiver_exact_compression** owns quotients and separators.

No general joined return currently accepts an operation complex with

\[
(G,\rho_{\mathrm{in}},\rho_{\mathrm{out}})
\]

and returns:

- closure, identity and inverse of the action;
- representation homomorphism;
- stabilizers and orbit;
- a non-vacuous action witness;
- exact equivariance square;
- complete equivariance defect;
- deformation alternatives and bounded receiver face;
- scale condensations and reopened fibres.

The missing relation is the enacted representation

\[
U_H:G\longrightarrow\operatorname{Aut}(H)
\tag{H.1}
\]

joined to the typed ports of a mathematical or lifted transport.

For a passage \(F\), define the exact action defect

\[
\Delta_g(F)
=
F\circ\rho_{\mathrm{in}}(g)
-
\rho_{\mathrm{out}}(g)\circ F.
\tag{H.2}
\]

The passage is exactly equivariant at the declared section family when

\[
\Delta_g(F)=0
\quad
\text{for every admitted \(g\in G\)}.
\tag{H.3}
\]

A scalar norm of \(\Delta_g(F)\) is a receiver face. The complete defect section and the
transformations that produced it are the return.

This should be a receipt composed through existing owners, not an EquivarianceEngine.

---

## 14. An action, stability, and scale receipt

**Truth status: conditional design expression.**

For a mathematical or lifted section, the optional geometric-action panel is

\[
\mathsf A
=
\left(
\Omega,
\mathcal S,
G,
\rho_{\mathrm{in}},
\rho_{\mathrm{out}},
m,
\nabla,
\omega,
\Delta,
\operatorname{Stab},
\{P_j\},
\mathcal F
\right),
\tag{H.4}
\]

where:

- \(\Omega\) is the situated base or incidence body;
- \(\mathcal S\) is the exact structure being preserved;
- \(G\) is the admitted transformation family;
- \(\rho_{\mathrm{in/out}}\) enact its action on typed ports;
- \(m\) is a declared metric, if one exists;
- \(\nabla\) is a connection or parallel-transport law;
- \(\omega\) is the local gauge atlas;
- \(\Delta\) is the complete commutation-defect population;
- \(\operatorname{Stab}\) is a receiver-specific deformation receipt;
- \(P_j\) are scale condensations;
- \(\mathcal F\) is the complete ReconstructionFiber.

Every panel member is optional only by type. An absent group, metric, connection, scale action, or
receiver is returned as absent and may not be filled by a default.

---

## 15. The Phoenix dissection and compression supplement

**Truth status: conditional under a declared candidate group, exact source mouth, typed ports, and
receiver family.**

This section is the intended audit instrument after the current Phoenix worktrack returns.

### The dissection asks per operation

For each lifted operation or transport word:

1. What is the actual input and output section family?
2. Which predecessor incidence is admitted by mask, locality, chronology, or connection?
3. Which candidate transformations act on the input and output ports?
4. Does that action move the admitted material?
5. Does the realized transport intertwine the two actions?
6. What exact defect remains?
7. Is the defect visible to the declared future receiver family?
8. Does the transport close inside a smaller operator algebra?
9. Which distinctions does any proposed condensation collapse?
10. Which held-out intervention reopens them?

### Transformer-specific questions

For a Gemma-like site, ask without assigning an answer:

| foreign face | geometric question |
|---|---|
| causal or sliding-window mask | what directed predecessor incidence is actually admitted? |
| RoPE or other positional action | which group or semigroup acts on which sub-bundle? |
| query/key contact | which compatibility face is invariant or equivariant under that action? |
| normalized attention | which ratio face crosses the local horizon, and what phase was deleted? |
| value/output transport | which section is transported along each admitted contact? |
| normalization | which magnitude or frame is quotiented, and what fibre remains? |
| MLP gate/up/down | which local constitutive response is enacted? |
| residual return | which standing is retained and which transported difference returns? |
| tower chronology | which operator words genuinely compose and which branches are co-present? |

The paper supplies questions and candidate identities. Source testimony and interventions settle
them.

---

## 16. Exact intertwiner decomposition of a lifted transport

**Truth status: conditional. Hypotheses:** \(G\) finite, the exact coefficient field admits division
by \(|G|\), \(\rho_{\mathrm{in/out}}\) are verified representations, and \(W\) is an exact linear
transport between their typed fibres.

Define the finite-group average

\[
\Pi_G(W)
=
\frac{1}{|G|}
\sum_{g\in G}
\rho_{\mathrm{out}}(g)\,
W\,
\rho_{\mathrm{in}}(g)^{-1}.
\tag{H.5}
\]

Then \(\Pi_G(W)\) is an intertwiner:

\[
\Pi_G(W)\rho_{\mathrm{in}}(h)
=
\rho_{\mathrm{out}}(h)\Pi_G(W)
\qquad
\text{for every \(h\in G\)}.
\tag{H.6}
\]

### Derivation

\[
\begin{aligned}
\Pi_G(W)\rho_{\mathrm{in}}(h)
&=
\frac1{|G|}
\sum_{g\in G}
\rho_{\mathrm{out}}(g)
W
\rho_{\mathrm{in}}(g^{-1}h)
\\
&=
\frac1{|G|}
\sum_{k\in G}
\rho_{\mathrm{out}}(hk)
W
\rho_{\mathrm{in}}(k^{-1})
\\
&=
\rho_{\mathrm{out}}(h)\Pi_G(W),
\end{aligned}
\tag{H.7}
\]

after rebasing the finite group index.

The exact residual is

\[
R_G(W)=W-\Pi_G(W).
\tag{H.8}
\]

This produces a dissection:

~~~text
lifted exact transport W
→ equivariant intertwiner component Pi_G(W)
→ symmetry-breaking residual R_G(W)
→ receiver question over the residual
→ exact condensation or retained fibre
~~~

### Compression use

If the intertwiner space

\[
\operatorname{Hom}_G(V_{\mathrm{in}},V_{\mathrm{out}})
\]

has a small exact basis \(\{E_i\}\), then

\[
\Pi_G(W)=\sum_i c_iE_i.
\tag{H.9}
\]

The coefficients \(c_i\), verified representations, basis transports, and residual may be smaller
than the original dense chart. This is genuine compression only for receiver families through
which the residual’s requested consequences factor. Otherwise \(R_G(W)\) remains part of the native
model.

This mechanism is a concrete bridge from GDL symmetry constraints to Phoenix dissection. It does
not assume the source transport is symmetric, and a nonzero residual is a result rather than a
failure.

### Nulls and controls

- a random rebase that is not a symmetry must produce a nonzero action defect;
- an untrained same-shape model is a null for apparent intertwiner dimensions;
- a candidate group whose action is trivial on every relevant section is refused;
- different candidate groups must not be compared through a scalar residual norm alone;
- a receiver-blind residual may condense only with its complete preimage population retained.

---

## 17. Polynomial, rational, and word compression

**Truth status: conditional.**

The paper’s operator-filter discussion gives a second Phoenix question. For a founded operator
population \(Q_1,\dots,Q_s\), does a lifted word \(W\) close in the algebra they generate?

The polynomial arm asks whether

\[
W=\sum_{\alpha}c_{\alpha}Q_{\alpha_1}\cdots Q_{\alpha_k}
\tag{H.10}
\]

over a finite material-derived word population.

The rational arm asks whether

\[
B(Q)W=A(Q)
\tag{H.11}
\]

for exact operator polynomials \(A,B\), returning kernel, cokernel, singular and preimage fibres
when \(B(Q)\) is not a rebase.

The complete transport word remains the construction. A polynomial or rational expression is a
compiled chart or condensation whose scope is decided by receivers and reconstruction, not by
shortness.

This is the relevant matrix-chain compression question. It is not “multiply all layer matrices and
call the product the model.”

---

## 18. The autograd analogue suggested by the bundle formalism

**Truth status: interpretation. The paper motivates the typing and does not derive this mechanism.**

For a differentiable section transport

\[
F:\mathcal X\longrightarrow\mathcal Y,
\]

the differential transports local perturbations forward:

\[
dF_x:T_x\mathcal X\longrightarrow T_{F(x)}\mathcal Y.
\tag{H.12}
\]

Reverse-mode differentiation is naturally typed as the pullback on dual fibres:

\[
dF_x^\ast:
T^\ast_{F(x)}\mathcal Y
\longrightarrow
T^\ast_x\mathcal X.
\tag{H.13}
\]

Consequences:

- a returned difference lives in a receiver cotangent fibre;
- differences at different base points or charts cannot be accumulated without rebase or parallel
  transport;
- the metric adjoint depends on declared local metrics;
- a gauge transformation acts on the primal and dual fibres by compatible representations;
- curvature appears when alternative transport paths return different dual sections;
- the complete path and defect precede any scalar gradient norm.

This gives a precise mathematical reading to the requested holonic analogue of autograd:
receiver differences pulled backward through the dual of the same typed transport ecology, with
connection, chart, metric, lineage, and holonomy retained.

The live **metric_adjoint** work in **exact_linear** is a bounded linear instance. A general nonlinear
and event-indexed construction remains open.

---

## 19. What the paper does not establish

**Truth status: established-bounded for the source boundary; open for the named Eros capabilities.**

The source does not establish:

- recovery of the domain or symmetry group from caused material;
- background-independent or changing topology;
- an internal elimination of the data/program distinction;
- exact no-float semantic execution;
- receiver-indexed ReconstructionFibers;
- exact compression with decoder and successor-history factorization;
- a causal constitutive diffusion law for every GNN aggregation;
- modern generative diffusion;
- MTP or next-token generation;
- loss/scoring design for holonic cultivation;
- a general autograd replacement;
- Phoenix lifting or dissection;
- durable hexis;
- world-mediated return;
- source-detached rest and remount;
- targeted morphological ablation;
- mathematical OCR, exact proof production, or the mathematics codec.

Its symmetry groups and domains are normally supplied as inductive priors. An architecture designed
to be equivariant has not thereby discovered the symmetry. Its approximate real-valued computation
does not meet the production no-float contract.

---

## 20. Falsifiers for the later audit and codec revision

### Action and equivariance

- Apply every declared transformation to the input and all typed ports. The intermediate section
  must move through the output representation.
- A declared invariant receiver may remain fixed only after the equivariant section has moved.
- A group whose action moves no admitted material is refused.
- A family of maps failing identity, composition, or inverse cannot be used as \(G\).
- A non-symmetry with an equal-magnitude face must produce a nonzero complete defect.

### Gauge and connection

- Independently rebase local frames and transform the connection. The result must agree after
  output rebase.
- Rebase features without the connection; the control must fail.
- A sphere, non-orientable surface, or singular atlas must defeat a fictitious smooth global gauge.
- Two paths around curvature must return holonomy rather than silent equality.
- A lossy camera or pooling projection must not be classified as a gauge.

### Attention topology

- Intervene on a causal/window mask; admitted predecessor incidence must move.
- Change attention weights along a value-null direction; no source edge may be founded from that
  weight change alone.
- Remove positional action; the declared grid or chronology symmetry must move.
- An unmasked complete-graph reading may not be carried into a masked model.

### Scale and condensation

- Refine or remesh while holding physical support fixed. Hop radius alone must not masquerade as
  scale invariance.
- Enlarge the future receiver family. An over-aggressive quotient must reopen.
- Inject one fine local defect invisible to the coarse receiver and visible to the richer one; the
  ReconstructionFiber must contain it.
- A coarsening with no decoder or separating population fails.

### Diffusion

- A learned aggregation failing the declared incidence, boundary, chronology, constitutive,
  conservation, semigroup, or return laws remains propagation and is not called causal diffusion.
- A diffusion claim must exhibit currents and stored/departed content, not only the next feature
  array.

### Spectrum and operator chart

- Rotate a repeated eigenspace basis; the underlying invariant claim must not move.
- Present an isospectral or receiver-indistinguishable control; spectrum alone may not identify the
  body.
- A rational operator whose denominator is singular must return kernel, cokernel and preimage
  alternatives instead of an inverse.

### Phoenix compression

- The proposed group action must be non-vacuous on the actual lifted section population.
- \(\Pi_G(W)\) must satisfy the intertwiner square exactly.
- \(R_G(W)\) must reconstruct \(W\) exactly before receiver condensation.
- Removing a residual visible to a held-out receiver must move that receiver.
- A smaller serialization without receiver factorization and decoder is not compression.

---

## 21. Revisions reserved for the mathematics-codec fold

**Truth status: open.**

When this research is promoted into the mathematics-codec blueprint, the smallest coherent revision
is:

1. cite the paper in the blueprint’s external-comparison header;
2. add “The Geometric Deep Learning correspondence and its boundary” after the AlphaEvolve section;
3. extend the MathematicalSection with the optional action panel \(\mathsf A\);
4. add an action, stability, and scale receipt after constraint-driven elaboration;
5. add **DeclaredGauge**, **structure_group**, **lattice_gauge**, **causal_body**, **diffusion**, and
   **sheaf_diffusion** to the standing-owner crosswalk;
6. add a group/action/equivariance panel to proposal evaluation;
7. extend the mesh receipt with local frames, connections, functional maps, orientability,
   singular links, and physical-scale calibration;
8. add one nontrivial action, an equivariant intermediate face, an invariant final face, a bounded
   deformation, and a reopening coarsening to the first vertical deed;
9. add the falsifiers in §20.

No such blueprint revision is made by this research record. The intended sequence is:

~~~text
Claude’s current Phoenix dissection/compression return
→ independent audit against its own blueprint
→ supplement with this geometric-action research
→ derive corrections and new exact identities against the actual return
→ revise the mathematics-codec blueprint coherently
~~~

---

## 22. Final synthesis

**Truth status: interpretation.**

The paper supplies a rigorous industry-facing bridge:

~~~text
grids ↔ groups ↔ graphs ↔ geodesics ↔ gauges
CNN ↔ group CNN ↔ GNN ↔ Transformer ↔ mesh CNN ↔ RNN
~~~

through:

~~~text
domain
→ section
→ transformation action
→ local equivariant transport
→ nonlinear response
→ scale condensation
→ invariant receiver
~~~

Holonics begins where this bridge stops:

~~~text
situated caused occurrence
→ founded and changing incidence
→ typed local section
→ recovered or declared action
→ exact connection and transport word
→ full commutation defect
→ receiver-indexed quotient with ReconstructionFiber
→ causal diffusion and return
→ durable changed morphology
→ source-detached continuation and ablation
~~~

The source should therefore be cited as an external mathematical precursor for architectural
unification, gauge-equivariant section transport, deformation stability, and scale separation.
It should not be cited as prior art for the full causal, learning, exact-compression, or
world-mediated claims of holonics.

The practical result is one precise audit question:

> Which transformations act on each lifted section, which transports intertwine those actions,
> which defects remain, and which declared future receivers can lawfully forget them?

That question can dissect, compress, and compare CNNs, GNNs, Transformers, recurrent systems,
meshes, SSM-like transports, and future lifted architectures without treating any one of them as
the ontology.
