# HNN model formula and library composition

[project-postulate] This is the model-level design used by the
[Athena blueprint](plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md).
The [roadmap](plans/THE_ROADMAP.md) orders its construction and
[CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md) records implementation. HNN is a network of
interacting, adaptive mathematical operators. Athena is its first product. The construction
uses the framework's circuit, field, differential, inference and compression laws directly.

[definition] A Transformer is also executable generating mathematics. Its architecture supplies
compositions of contractions, attention, reactions and normalizations; its parameters and
execution state supply their contemporary operands. HNN generalizes the organization and
representations of such operators. It does not add a further faculty between computation and
intelligence. Safetensors, an ONNX graph and a world save serialize different portions of an
executable system. The model specification must say which laws interpret that data.

## 1. The model, its dynamics and its output

[definition] Use the [encapsulated Holon operations](HOLON.md#high-level-holonic-interactions)
to formulate this model: chart-presented tensor kets |H⟩_F, receiver bras ⟨r|, operator
application, tensor interaction, contraction and adjoint variation. The tuple below is the
model's state specification, not its public computational notation. Interaction diagrams
carry these objects on oriented lines and their actual maps at vertices.

[definition] Write the situated model as

```text
M = (K, Θ, x),                 y_F = ρ_F(b_H(x)).
```

K is the oriented contact complex, including its boundary ports and chart transitions; Θ is
the constitutive operator material; x contains the active currents and internal modes.
Their numerical representations may be sparse sections, tensors, factors, recurrences or
correlated parameter families. K is not a semantic classifier. The components need not share
one shape, one spatial grain or a universal clock. At a specified interaction, the joined
ports determine which restrictions of these objects participate.

[definition] b_H is the outwardly available field/current at the selected holonic boundary.
It can be an identity/readout port in a computational chart. Another internal region or an
exterior system can receive it; it need not be a deliberately requested message. The
[computational Holon](HOLON.md) supplies the elementary object and operator contract.

[definition] The executable model is a composition of those actual operators:

```text
x ↦ boundary injection
  ↦ incident transport and interaction
  ↦ constitutive reaction and internal dynamics
  ↦ requested output projection.
```

An implementation must instantiate the maps below; the four arrow labels alone are not a
model. Repeated or recursive compositions operate on the same material, and can return a
joint field, trajectory or text section. Learned material can change between or within those
compositions through its specified variation. A public input selects a task and output ports,
not a different learning engine. A speculative output and a committed step evaluate the same
generating law with their respective ownership effects.

### Generation as field refinement and boundary radiation

[project-postulate] Generation develops a joint field or configuration through the model's
constituted dynamics. Its integration/refinement coordinate is not an output-token index.
Image, acoustic, geometric and symbolic outputs are receiver charts of that construction.
Streaming may expose available parts, but must not replace joint generation with independent
per-coordinate predictions. A text codec cannot schedule the model's evolution.

[definition] Let ξ parameterize a prepared latent/partial field and h the actual restricted
environment, internal material and boundary data. A generative chart is

```text
x(τ₀)=I_h(ξ),
∂_τ x = F_(Θ,K)(x,h,τ),
y_F(τ)=ρ_F b_H(x(τ)),
u_B=C_(B←H) b_H(x).
```

F is composed from transport, constitutive reaction, inference/score and integration
operators; its signature alone does not implement it. C is an actual coupling to another
region, possibly within the same larger model. Local evolution can use stored currents
and internal clocks without a fresh user message. Voluntary communication can shape the
boundary activity but does not define whether it can affect another region.

[definition] Classical denoising diffusion uses the corruption chart
`x_t=√ᾱ_t x_0+√(1-ᾱ_t) ε`. A learned noise/score field drives generative refinement of the
whole latent field. The usual variance step is
`x_t=√(1-β_t)x_(t-1)+√β_t ε`. Convolutional networks can parameterize that field with shared
kernels and multiscale connections. DiffWave refines whole acoustic waveforms without
autoregressive sample generation. [Image diffusion](https://arxiv.org/html/2006.11239v2),
[acoustic diffusion](https://arxiv.org/html/2009.09761v3).

[conditional] For forward SDE `dx=f dt+g(t) dW`, an exact score and the density/regularity
hypotheses give probability-flow ODE `dx=[f-(g²/2)∇log p_t]dt`. Integrating from the prior end
gives the same one-time marginals as the corresponding SDE, not the same stochastic paths
or a unique historical input. This is a deterministic generative realization, not a
requirement to add a sampler to every native operation.
[Score-based construction](https://arxiv.org/html/2011.13456v2).

[definition] The initial latent may be a supplied noise realization, structured modes or an
unresolved joint family. Zero current, an unseen region, uncertainty and stochastic noise
are different operands. Stable heat smoothing alone does not synthesize a learned
distribution; the learned/refined constitutive field supplies its structure. Known
observations constrain appropriate coordinates while generation can continue elsewhere
without a singleton causal preimage or complete historical reconstruction.

[project-postulate] The native consumer takes a whole resident section/family, its refinement
law and boundary constraints, and emits the joint generated section through the existing
body. Image/acoustic arrays and symbolic sections enter through their shape/transport maps.
The two-current wave chart and character readout are local specializations, not the general
generation algorithm. Inspect joint generation and composition before introducing a token
loop or another fixed assay.

[proved-derived; formal-checked] `Holon.ofEvolution` realizes generation in the elementary
Holon type. Its encoding theorem equates full and reduced generation when their maps
commute; its composition equivalence carries one latent population through two refinements.
Neither binding requires a trajectory archive or independent output marginals.

### One object, its charts and its recursive geometry

[definition] A computational Holon is the same situated field across its local, modal and
receiver charts. Let `K` be its oriented cell incidence, `Γ(K)` the compatible current/field
sections and `Φ_Θ` the actual nonlinear operation on current, material and geometry. A chart
restriction `r_α` gives `|H⟩_α=r_α|H⟩`; compatible restrictions on an overlap are related by
its declared transition. A head reads/transports such currents. Composing heads, reactions
and time steps acts on the same Holon; a layer diagram is an execution chart, not a set of
physically separated planes. If local restrictions do not close dynamically, retain the
coupling, interior modes and residual rather than treating each chart as an autonomous object.

[definition] The carrier can have toroidal cycles, curved transport tubes and overlapping
field domains, with higher cells recording their joints. `simplicial::SimplicialComplex`
provides oriented surface stars/links and hinge changes; `algebraic::GradedCausalComplex`
provides arbitrary-grade incidence with `∂²=0`; `analytic_field` supplies torus phase charts;
connection/holonomy owners transport current around actual paths. A torus is not a generic
hypersphere, and an aggregate intensity isosurface does not expose all of its constituent
cycles. An embedding into a displayed 3D scene is a receiver of these relations. Interlinked
cores, intersecting support domains and actual constitutive contact are separately specified.

[definition] Fractal geometry can arise within the operation's invariant, survivor or
receiver-arrival populations while the number of state axes remains fixed. For a fixed
recurrence `Φ` and receiving region A, the **first-arrival** populations are

```text
A_0=A,
A_(n+1)=Φ^(-1)(A_n) \ A,
x∈A_n  iff  Φ^[n](x)∈A and Φ^[k](x)∉A for every k<n.
```

[proved-derived; formal-checked] `HolonicRecurrentEcology.FirstArrival` proves that
characterization and its covariance under a state-chart equivalence with the transported
recurrence and receiver. Preimage here means all compatible initial conditions, not reverse
time or a chosen inverse. Repeated stretching, folding, passage near saddle regions and
restriction can produce fine interleaving. A small sampled dimension or a finite picture
alone neither proves infinite-scale fractality nor replaces this generator.

[definition] A basin figure uses a declared family `z(a,b)=z₀+a u+b v` or a valid manifold
section. Its coordinates label initial conditions for **one** full recurrence. Color may
read first arrival, decoded settling or another specified consequence. Its nonlinear
trajectories live in the full state space; the two plotted axes and 3D embeddings need not
be dynamically invariant. A zoom recomputes that restricted family. It does not place more
copies of the complete model in a grid. Nonlinear dynamics also need not be globally
contractive; do not choose a uniform contraction merely to make the demonstration settle.

[definition] Intrinsic metric/measure and the admitted family determine dimension. For a
compact receiver family, box dimension uses `lim_(ε→0) log N(ε)/log(1/ε)` when that limit
exists. An uncertainty fraction `f(ε)~ε^α` gives section-boundary dimension `d-α` only under
its sampling and scaling hypotheses. Carrier/stratum dimension, phase-space dimension,
fractal dimension and effective receiver rank are separate quantities. A chart of twelve
phase coordinates does not force its invariant or survivor geometry to have dimension twelve;
a two-dimensional basin plot does not reduce the complete field to two dimensions.

[established-bounded; computational-witness] The
[intrinsic phase-field reference](../research/experiments/intrinsic_holonic_flow/README.md)
constructs six interlinked toroidal domains, a conforming volume subcomplex with shared
contact cells, and a twelve-phase nonlinear map. Two normalized phase-comparison potentials
and a sigmoid local reaction act on this one state. The linked geometry, changing head
weights, paired flow histories and successively resolved arrival sections are its different
receivers. This is a supplied analytic constitutive example, numerically evaluated outside
the native runtime. It is not a reproduced trained-model experiment. The older fifteen-channel
linear reference remains evidence for its differential and material step; it does not provide
the main generative or fractal geometry of the model.

[proved-derived] The linked carrier and its common cell complex also admit a concrete
incompressible material motion. At unit nondimensional density, put
`u=(0,-χxz,χxy)`, `p_hyd=χ²x²(y²+z²)/2`, and `f=(χ²x(y²+z²),0,0)`.
Then `div u=0`, `Δu=0`, and `(u·∇)u=-∇p_hyd+f`, giving a local forced Euler/Navier–Stokes
field for any constant viscosity. Its exact flow is
`F_t(x,y,z)=(x,y cos(χxt)-z sin(χxt),y sin(χxt)+z cos(χxt))`, with determinant one and
inverse `F_(-t)`. Advect the torus domains and every shared cell by the same map; linking,
incidence and containment are preserved. The reference uses `χ=1/8`, `0≤t≤1`.
A circulating point/current has velocity `u(F_t X)+DF_t·X_dot`; omitting either term would
separate internal motion from the material carrying it. The graphical edges sample these
curved images, not an assumption that the underlying cells stay affine in space.

[definition] In that reference `q,p∈T^6`, `s^h_ij=β_h cos(2π(q_i-q_j-φ_ij))` on the
geometrically admitted incidence, `a^h=softmax(s^h)`, and `g_i=σ(-cos(2πq_i))`. The potential
and its complete gradient are

```text
V(q)=κ/(2π) Σ_i softplus(-cos(2πq_i))
     -κγ/(2π H) Σ_h β_h^(-1) Σ_i log Σ_(j∈E_i) exp(s^h_ij),
∂V/∂q_i=κ[g_i sin(2πq_i)
          +γ/H Σ_(h,j)(a^h_ij+a^h_ji) sin(2π(q_i-q_j-φ_ij))].
q'=q+κ sin(2πp),                 p'=p-∇V(q')      (mod 1).
```

[proved-derived] The two substeps are exact flows of complementary periodic Hamiltonians,
so their composition preserves the canonical form `Σ_i dq_i∧dp_i` and phase volume. It need
not preserve one unsplit energy or converge to a fixed point. The full derivative includes
inbound and outbound attention and the sigmoid/softmax differentials; omitting one changes
the Hamiltonian field. A detector's first reception is an output without requiring global
settling. Dissipative material and incidence changes can be composed through their own laws;
the conservative instance does not declare them absent from HNN.

### Recursive generators, scale and transcendental operations

[definition] Repeated latent generation is `x_(n+1)=F_Theta(x_n,h)`. Its tangent evolves by
`J_(n+1)=DF_Theta(x_n,h) J_n`; both are executable recurrences. A single iteration may refine
an entire field. Fractal basins of that recurrence describe sensitivity of its routes or
settling times; their finite-resolution measurements are not tensor rank or a proof that
all algorithms must traverse the same difficult routes.

[definition] A separated IFS specialization can use `S(H)=union_i F_i(H)` and an attractor
`H=S(H)`. With contracting similarities and the stated separation condition, dimension D
obeys `sum_i r_i^D=1`. The maps, their scale and relevant branch constraints are the compact
construction. A lattice is one resolved realization, not the only way to compute it.
The existing `FractalPacking` owner proves that specialization's restriction laws. The
recurrence, preimage, tube, connection and scale owners supply the broader construction.

[definition] Functional calculus supplies generators: `exp(tA)` evolves a linear field;
`exp(i theta)` carries torus phase with period 2π; logarithms read relative scale; Gamma
recurrences carry analytic blocks. Domains, branches and remainders belong to the operation.
A periodic bounded field generally has no limit at one added point at infinity; retain its
phase chart instead. These laws are not merely floating-point constants or ornamental
references to fractals.

### Capacitive, inductive and dissipative realization

[definition] The [paper synthesis](../research/records/2026-09-14_TRANSFORMER_FIELDS_TROPICAL_CELLS_AND_FRACTAL_GENERATORS.md)
places field transport, reaction, recursive generation and the following physical
realizations in one operator algebra. Published Transformer charts supply useful instances;
their fixed token base, frozen-key limits and empirical basin measurements do not choose
HNN's topology or impose a universal limit on generation.

[definition] On a finite real electrical chart, let d map node potentials to oriented edge
drops. Let C and L be positive symmetric storage maps and R nonnegative resistance. The
network equations are

```text
q = C φ,                 λ = L j,
q_dot + d* j = b,
λ_dot + R j = d φ + e_ind.
```

q is stored charge, φ potential, j branch current, λ linked flux, b injected current and e_ind
an induced electromotive field. The adjoint d* uses the stated pairings. Units are coulombs,
volts, amperes, webers, farads, henries and seconds in this chart. Anisotropic maps, complex
phase coordinates, nonlinear constitutive relations and changing incidence extend these
operands through their respective laws; they do not replace the equations with object labels.

[proved-derived] In a fixed carrier with differentiable material, the stored energy satisfies

```text
H = (φ* C φ + j* L j)/2,
H_dot = φ* b + j* e_ind - j* R j - (φ* C_dot φ + j* L_dot j)/2.
```

The internal powers cancel through the adjoint incidence. This is a calculable generalization
of V=IR with storage, induction and changing material. For a changing population, transfer
charge/flux and boundary work through the actual contact map; equal array indices do not
identify those quantities. [PortEnergyHeat](../formal/elementary-holonics/ElementaryHolonics/Physics/PortEnergyHeat.lean),
[CoupledIncidence](../formal/elementary-holonics/ElementaryHolonics/Physics/CoupledIncidence.lean)
and [ConstitutiveModulation](../formal/elementary-holonics/ElementaryHolonics/Physics/ConstitutiveModulation.lean)
are the existing formal owners.

[definition] Port-Hamiltonian form, `x_dot=(J-R)∇H+B u`, is an available energy-chart realization
with skew J, nonnegative R and power output `B*∇H`. Its graph interconnection is an established
compositional construction. A learned reaction or nonlocal attention field need not itself be
a gradient flow; use its actual Jacobian and balance. The model need not wait for a universal
Hamiltonian representation of every neural operator.
[Graph interconnection](https://arxiv.org/abs/1107.2006),
[neural graph realization](https://arxiv.org/abs/2405.17163).

### The existing native scattering operator

[established-bounded; source-inspected] The current operative field already supplies a concrete
complex boundary/interior operation. With incident current u, stored interior current b and
contact matrix D, its normalized unit-admittance chart is

```text
A = I + D D*,
A v = 2(u + D b),
w = v-u,                 b_next = D* v-b.
```

This map couples external and internal currents. It is implemented by the operative field and
its resident kernels. D is operator material, not a descriptor to append to a separate example.
The next application uses w and b_next through its physical/contact transport. A model assembled
from this operation directly computes those currents; fitting a second matrix to its outputs
is a distinct surrogate-model task and is justified only when that task is intended.

[project-postulate] Extend the existing `NativeCoupledBody` application owner to execute the
field's constituted transport and the required local generator/reaction maps from their shared
resident material. The field and coupled representation must not become independently trained
copies of one purported model. The field can still be an independent physical environment when
an application actually requests learning that environment. Existing normal fitting remains a
valid local material law; it does not determine the entire architecture.

```mermaid
flowchart LR
    U[Input field or encoded request] --> D[Oriented contact transport]
    X[Stored currents and internal modes] --> D
    M[Constitutive operators and contact geometry] --> D
    D --> S[Scattering, reaction and coupled evolution]
    S --> X
    S --> Y[Joint output at requested ports]
    Y --> L[Observed discrepancy or task differential]
    L --> A[Adjoint through the same operators]
    A --> M
    C[Mode factors, recurrence and boundary memory] --- S
```

## 2. Transformer, convolution, SSM and diffusion operators

### One connected tensor computation

[definition] In a finite chart write the computational Holon as `|H_l>_F`, with current
`X_l ∈ C^(sites × channels)` and situated incidence `E_l`. A head is one pair of query/key
charts and a transported value chart on that same object. A layer composes those maps:

```text
Q_h=X_l W_Qh,  K_h=X_l W_Kh,  V_h=X_l W_Vh,
s_hij=β Re <Q_hi,K_hj> + b_hij,                  j ∈ E_l(i),
a_hij=μ_j exp(s_hij)/Σ_(k∈E_l(i)) μ_k exp(s_hik),
Y_hi=Σ_(j∈E_l(i)) a_hij U_hij V_hj,
Z_l=X_l + Concat_h(Y_h) W_O,
g_l=σ(G_l Z_l+c_l),
X_(l+1)=N_l[Z_l+g_l ⊙ R_l(Z_l;Θ_l)].
```

[definition] `U_hij` transports values between the participating frames; its unit/phase
or general constitutive law is declared. `N_l` is the specified normalization, `R_l` the
local reaction and `g_l` a binary participation chart. These are typed tensor operations,
not seven new engines. Head indices label parallel charts; layer indices label composition.
Neither index determines a physical level or a text-generation clock. The general HNN
incidence and current/material equations in §1 decide which maps and subdivisions apply.
The earlier native `operative_atlas` actually composes Q/K/V, RoPE, masked multihead contact,
output contraction, residuals and gated reaction through `NativeFullOperatorSession`.
The active constitutive field's normalized receiver and contact adjoints are separate owners;
the presence of the earlier graph does not connect that graph to this field automatically.

[definition] Attention is the dependence of transported current on these situated
comparisons, including its sensitivity to changing input, phase and material. A normalized
coefficient is one chart of participation. For one row,

```text
da_j=a_j(ds_j-Σ_k a_k ds_k),
dY=Σ_j a_j U_j dV_j + Σ_j a_j dU_j V_j
    + Σ_j a_j(ds_j-E_a ds) U_j V_j.
```

[proved-derived] The last term curves participation through
`J=diag(a)-a aᵀ`, a positive semidefinite covariance/Laplacian with constant-shift null
direction. A head can suppress a large but common perturbation while responding strongly
to a smaller difference that changes its participating current. Softmax is not an all-to-all
incidence rule: its denominator ranges over the admitted contacts. Sigmoid is the two-channel
restriction `σ(s)=exp(s)/(exp(s)+1)` with derivative `σ(s)(1-σ(s))`. Changing a previously absent
edge requires the separate incidence law; the derivative on a fixed support does not open it.

[established-bounded; implemented-exact] The
[connected reference computation](../research/experiments/connected_holonic_field/README.md)
uses fifteen complex toroidal channels, two normalized heads, two composed layers, a sigmoid
gate, a phase-sensitive dissipative contact, an observed material step and a whole-field
resolvent. Its exact rational `K=exp(s)` specialization lives in
[`exponentiated_ratio::NormalizedKernel`](../crates/holonic-engine/src/exponentiated_ratio/transport.rs).
It accepts supplied positive rational K, hence `s=log K`; it does not silently approximate a
general exponential of arbitrary query/key products. Its generated field drives the new
synopsis figures through the existing geometric decoder. This is executable reference
composition on the CPU; the native model assembly still belongs to the active field/body.

### Existing classical and modal restrictions

[definition] A Transformer chart evaluates `Q=XW_Q`, `K=XW_K`, `V=XW_V`, then

```text
α_ij = μ_j exp(s_ij) / Σ_k μ_k exp(s_ik),
a_i = Σ_j α_ij V_j.
```

s includes the declared Q/K pairing, scale, positional terms and contact mask. Head/output
maps, residual addition, local nonlinear reaction and normalization complete the block. The
[Transformer mathematics paper](https://arxiv.org/html/2510.03989v2) expresses these as field
operators and split evolution. Our [September 12 derivation](../research/records/2026-09-12_FRACTAL_MODES_LIFT_ATTENTION_INTO_MASS_PRESERVING_GENERATOR_COMPRESSION.md)
already corrected its projection conventions and supplied the entropic and modal relations.

[proved-derived; formal-checked] For kernel-equivalent source classes, keep
`m_c=Σ μ_j` and `p_c=Σ μ_j V_j`; the same attention is
`a_i=(Σ_c k_ic p_c)/(Σ_c k_ic m_c)`.
The pair (mass,current) is associative; normalized means alone are not.
[AttentionModeCompression](../formal/elementary-holonics/ElementaryHolonics/Computation/AttentionModeCompression.lean)
owns this law. The Rust `exact_linear::KernelModeReduction` constructs an exact finite
factorization, transports its signed current columns, and tests action closure. This reusable
library result has not yet been bound to the native HNN model's operator execution.

[definition] Convolution shares the transport kernel by relative position; sparse graph
transport uses actual edges. A fixed SSM `x_next=A x+B u` has output
`y_k=R A^k x_0+Σ_(j<k) R A^(k-1-j)B u_j+D u_k`. Its internal state, convolution and resolvent
represent one operation. Selective coefficients require ordered, varying maps. A diffusion
model composes its drift/score/reaction and integration operators, with an initial field and
any declared stochastic law. The [architecture charts](../formal/elementary-holonics/ElementaryHolonics/Computation/HolonicArchitectureCharts.lean)
and [composition guide](HNN_COMPOSITION.md) retain these specializations. HNN construction
reuses these operations rather than requiring their names to determine its topology.

## 3. Learning is variation of these operators

[proved-derived] Differentiate the native scattering equation at its producing D, u and b:

```text
A δv = 2δu + 2δD b + 2D δb - (δD D* + D δD*)v,
δw = δv-δu,
δb_next = δD* v + D*δv-δb.
```

These equations determine the tangent map. Its adjoint transports an output covector back to
the incident current, stored current and contact coefficients using the same factorization.
For a composition, the chain rule composes these tangents and reverses their adjoints. That
is the precise relationship to forward evaluation and backpropagation. The implementation
must include the induced change of contact transport as well as local coefficient changes.
The existing operative material-response and causal-propagation owners contain those terms.

[definition] A specified scalar objective supplies one output covector. With predicted
probability p and observed probability q, cross-entropy has `dℓ=(p-q)·ds` at softmax logits;
`q-p` is its negative gradient. For half squared probability error the gradient is
`J_p(p-q)`, and the descent return is `J_p(q-p)`. Scalar loss is a lawful comparison in this
chart. The cotangent and its operator pullback contain the directional update information.
A chosen constitutive metric maps that covector to a material displacement; numerical step
size and constrained realization belong to that update law. An adjoint is not a physical
reversal of time, and a unit metric is not a theorem of universal learning dynamics.

[definition] In the normalized-current chart `Y=aV`, a receiver covector `G=∂ℓ/∂Y`
pulls back to `∂ℓ/∂s_ij=a_ij <G_i,V_j-Y_i>` and `∂ℓ/∂V=aᵀG` when the frame transport is
identity. The general chart also pulls back through `U`, Q/K and the metric. The reference
owner exposes both operands and their exact pairing identity. Its declared Euclidean
material step uses `∂ℓ/∂K=(∂ℓ/∂s)/K`, updates positive K and refuses a step crossing the
present positive support. This local objective and supplied step are explicit, not a
universal gradient or an assertion that every physical relaxation minimizes that loss.

[proved-derived] Integration also has a differential. For the fixed-field restriction
`x_(k+1)=λ B_Θ x_k+(1-λ)h`, `x*=(I-λ B_Θ)^(-1)(1-λ)h`. Its material sensitivity solves
`(I-λ B_Θ) dx*=λ(dB_Θ)x*+(1-λ)dh` at fixed λ. For two shared layers `B=L²`,
`dB=(dL)L+L(dL)`. Thus learning, internal refinement and the decoded output are linked
by one chain rule; differentiating only a final readout would omit this induced change.

[established-bounded; source-inspected] Existing normal material supplies another concrete
learning law: for features f and targets t, accumulate `H=H_0+Σ ff*`, `B=B_0+Σ tf*`, then solve
`WH=B`. Mixed current/material features and the declared prior belong in f and H_0. This
stores the relevant statistics, not every training sample. Exact preimage and factorization
solvers infer other unknown functions. The model uses the law appropriate to its operator;
requiring every result to infer its own update rule creates an unrequested infinite regress.

[definition] Learning contact structure additionally changes K or its local carrier. A
rank/separation result can expose a direction absent from the present representation; actual
incidence and constitutive transport decide how it attaches. A change in rank is not obtained
by pretending that a fixed-dimensional derivative includes new coordinates. Use chart
transition maps and the existing contact-birth/extension owners at that transition.

## 4. Lattice and mode representations of the same dynamics

[definition] Let `ξ=E_t x` encode active dynamics and let `D_t ξ` decode the requested observable
ρ_t x. For an executed step T_t the exact compilation conditions are

```text
E_(t+1) T_t = U_t E_t,          D_t E_t = ρ_t.
```

For differentiable changing encoders, the corresponding rate is
`ξ_dot=E_dot x+E x_dot`. The E_dot term is part of the dynamics, not an optional bookkeeping
correction. A representation that has closed factors or statistics can execute directly in
those coordinates. A lattice representation is used where local interactions need its
distinguishing coordinates. Representation selection follows the computed factorization,
coupling and receiver defect, with the caller's accuracy/resource objective where applicable.
No manually assigned lattice/mode label supplies this decision.

[proved-derived; formal-checked] The existing reflected-interior law, for
`x_dot=A x+B z+f`, `z_dot=C x+D z+g`, and `z=K x+r`, is

```text
r_dot=(D-KB)r+(C+DK-KA-KBK-K_dot)x+g-Kf.
```

The residual can be another evolving mode or a memory realization; keeping it does not require
replaying the past. The same law explains a boundary whose present response hides circulating
interior dynamics. The source owner is
[ReflectedBoundaryMemory](../formal/elementary-holonics/ElementaryHolonics/Physics/ReflectedBoundaryMemory.lean).

[proved-derived; formal-checked] With `x_next=A x+B z+f`, eliminating arbitrary z in the next boundary encoding
is exact precisely when `E_next A=U E` and `E_next B=0`. The native reduction task can construct
this through the existing exact receiver factorization of `E_next[A B]` through `[E 0]`.
A returned null-space separator identifies an omitted influence. With a constrained z-family,
factor only that family; this unrestricted criterion must not become a stronger universal gate.
The same condition at each step yields the reduced recurrence by induction.

[definition] Approximation measures the actual projected residual and propagates its error
through the admitted dynamics. Exact invisibility, tolerated difference and physical
dissipation are different calculations. A weak perturbation can be amplified later; a strong
one can be decoupled from the task. Thus attention is governed by coupling, phase, sensitivity
and the task's ongoing dynamics, not a universal amplitude threshold. The tree's physical
effects continue in its environment; an HNN need represent only the effects required by its
interactions. No reconstruction of every cause is implied.

## 5. The circuit, fluid, membrane and magnetic design connection

### Friction, leader formation and return propagation

[definition] The finite phase contact `δ=y-u x`, `|u|=1`,
`x'=x+α conjugate(u)δ`, `y'=y-αδ` has the exact balance
`|x|²+|y|²-|x'|²-|y'|²=2α(1-α)|δ|²` for `0≤α≤1`.
It acts on signed/complex relative slip and deposits a nonnegative energy difference.
In the connected reference this is an actual operator between attention and the next layer;
the figures use its computed input, output and deposited quantity. A physical unit calibration
is additional data; softmax weights themselves are not electrical conductances.

[definition] The existing conducting-fluid construction explains the higher-level lightning
analogy through coupled equations, not through a branching shape:
`Γ_e=n_e u-μ_e n_e E-D_e∇n_e`,
`∂_t n_e+div Γ_e=S_ion+S_photo-S_attach-S_recomb`,
`div(εE)=ρ`. A leader changes conductivity, channel geometry and capacitance; the return
current then propagates in that changed material. Along a resolved channel,
`∂_s V=-∂_t(LI)-RI+e` and `∂_s I=-∂_t(CV)-GV+i` retain induction, storage,
leakage and forcing. The [fluid/leader guide](FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS.md)
contains the source chain and energy/material derivatives.

[interpretation] For HNN this suggests deriving a new contact from oriented potential and
the local constitutive/material differential, then integrating current on the changed
operator. The leader corresponds to changing admissible transport; the return corresponds
to its realized current. A finite fixed-support attention derivative models the second
operation's sensitivity, not the first operation's birth of a channel. A physical leader's
computed trajectory requires the ionization and boundary data in those equations. The
synopsis displays this extension as a coupled-law diagram and does not present its finite
normalized field example as a plasma simulation.

[definition] Membrane transport uses the same arrangement of stored quantities, interfaces
and flux laws, with species-specific operands. For example, local near-equilibrium transport
can use `J_i=-Σ_j L_ij ∇μ_j`, continuity
`∂_t c_i+div(c_i v+J_i)=r_i`, and electrochemical potential
`μ_i=μ_i^chem+z_i F φ`. Surface storage and interface conditions join the two sides. Osmosis
also couples pressure, solvent flux and friction; charge-only diffusion does not exhaust it.
An energy-variation derivation supplies their coupled terms.
[Membrane interaction derivation](https://arxiv.org/abs/1806.00646).

[definition] The complex Euler/Navier–Stokes chart similarly joins advection, pressure,
viscous transport and boundary flux. For `U=a+i b`, complex-bilinear advection contains
`(a·∇)a-(b·∇)b` and `(a·∇)b+(b·∇)a`; deleting b changes the real dynamics. These equations
and the moving-boundary/friction constructions already appear in the information-chemistry
papers and [fluid guide](FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS.md). Neural signal fields
can instantiate the same operator constructions with their computational units. A literal
biological or astronomical model additionally supplies its actual material and boundary laws.

[established-bounded; source-inspected] The existing
[discrete induction owner](../formal/elementary-holonics/ElementaryHolonics/Millennium/HolonicDiscreteInduction.lean)
states `d_1 e=-ΔΦ`, proves `d_1 d_0=0`, and separates induced electromotive circulation from
conductive response `j=σ e`. It calls a nonzero divergence-free branch current an eddy at that
declared receiver. Magnetic order, conductivity, inductance, excitation frequency and geometry
are distinct operands. Ferrites' high electrical resistivity suppresses eddy losses; ferrimagnetic
order alone does not prove absence of eddies, and ferromagnetic order does not imply chaos.
[TDK material explanation](https://www.tdk-electronics.tdk.com/en/373562/tech-library/articles/applications-cases/applications-cases/thin-and-efficient-power-transmission/980554).

[interpretation] The proposed eddy/no-eddy equivalence is therefore a boundary-response
equivalence. Partition the device into observed modes x and circulating modes z and use the
operator criterion in §4, or the full memory term when it does not close. Removing a conducting
loop can alter phase, damping and readout; a zero present divergence does not erase those effects.
The original parametron uses a pumped nonlinear resonant circuit and phase selection. Its
computational analogue needs oscillator, coupling, damping and readout maps, not a magnetic
material name as an activation function.
[Goto's original paper](https://ethw-images.s3.us-east-va.perf.cloud.ovh.us/ethw/3/33/Goto_IRE4708.pdf).

## 6. What synthesis must deliver to the library

[definition] Mathematical vocabulary names operands and operations, not extra faculties.
Existing API names remain compatible. In explanations, expand the following shorthand:

| Shorthand | Required mathematical meaning |
|---|---|
| Source | The particular incident current, forcing, parameter family or boundary datum in an equation; its dependencies need not be a saved origin history. |
| Return | Identify the result: outward current, reflected wave, cotangent, measured discrepancy or ordinary function value. |
| Condition | Name the restricted variables or constraints. If a weight update is meant, give the differential, normal equation or preimage operation instead. |
| Formation | Name the geometric/contact change, coefficient inference or generated mode and the equation that constructs it. |
| Successor | State the transition and its local clock/ordering; this ownership term supplies no learning criterion. |
| Preserve | Specify the conserved physical quantity, commuting representation map or bounded output difference. Physical propagation does not impose an event archive on the computational model. |

[definition] An initial condition and a forcing/source term are legitimate mathematical
concepts. Their unqualified use as implementation requirements is what loses the content.
The same applies to a successor state in a recurrence: causal order does not replace the
recurrence equation, and computing its adjoint does not reverse physical entropy production.

[project-postulate] Synthesis identifies a common operation across the research instances,
constructs its typed executable realization in the existing mathematical owner, and makes the
model's actual operator composition consume it. Unification reconciles duplicate laws and
representations through their explicit transformation. A shared vocabulary, an additional
example, a re-export or a theorem-to-file table alone does not complete that construction.

[definition] The [Rust library guide](RUST_FRAMEWORK.md#mathematical-operators-and-model-assembly)
names the existing packages, numeric representations, actual consumers and unresolved
connections. Lean statements specify identities, domains and hypotheses; constructive
algorithms implement them in Rust/CUDA and are checked at their numerical representation.
Noncomputable existence proofs require an algorithmic realization. Lean itself remains exterior
verification; neither an import restriction nor that separation forbids a reusable ML library.

[project-postulate] The first model assembly uses the existing operative transport, its
material variation, coupled joint readout and applicable mode/recurrence encoding as one
operation. Its current and material must refer to the same evolving contact geometry.
The existing public session then exposes this operation to the task's encoded request and
output. The blueprint specifies this integration; its completion is judged from the invoked
model and actual generated product, with its accuracy and execution costs. Broad conversation
development uses that model instead of replacing it with a fixed-field fitting experiment.
