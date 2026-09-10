# Equational laws, world tubes and Athena's producing return

## Construction consequence

[definition] Athena's next implementation joins an actual situated prediction, its declared
receiver and an addressed observed return. The current source-actuation, local-law, neighborhood
and rest constructions remain dependencies. The revised [blueprint](../../docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md)
names the owner, operands, state change and checks for that join, then the emission receiver and
further contextual composition. The [roadmap](../../docs/plans/THE_ROADMAP.md) remains the sole order.

[project-postulate] The direct September 10 research thread asks that equational theories guide
Holonics generally and that this synthesis make the paused AC plan concrete. Its follow-up names
world tubes as the existing owner of volumes carrying internal transport. Direct-message source:
`~/.codex/sessions/2026/09/10/rollout-2026-09-10T10-04-43-01a08c47-6302-7d02-a90f-619bdd5b5145.jsonl`,
user messages at lines 1888 (21:19:29 UTC) and 2039 (21:23:45 UTC), containing the three supplied
references and “world tubes, duh”. No cultivation is
started by this review. Research comparisons do not impose a new gate on the existing programme.

## Equational theories: compare laws before architecture names

[established-bounded; source-inspected] The Equational Theories Project explores implication and
non-implication between magma identities, initially 4,694 laws with at most four operations up to
its symmetry/relabeling convention. Its reviewed source revision is
`bb5a9b5fe78c376ce1725529f235f8d574630b9f`.[^etp] A magma supplies one total binary operation;
this signature is deliberately much smaller than a full situated, stateful HNN operation.

[definition; source-inspected] `FreeMagma` represents terms as binary trees. `MagmaLaw` pairs two
terms. Satisfaction evaluates them under every variable assignment in a chosen magma; semantic
entailment quantifies over all models of the premise theory. `derive` explicitly retains axiom,
reflexivity, symmetry, transitivity, substitution and congruence steps. Implication is one-way;
two theories have the same models only when the implications run both ways.[^laws]

[proved-standard; source-inspected] The project's `Completeness` and `Soundness` identify
semantic entailment with existence of an equational derivation. The quotient term algebra is
the separating model when a proposed identity is not derivable. This is a constructive research
pattern for exposing what a set of laws actually identifies, rather than declaring two objects
equivalent because their diagrams look similar.[^complete]

[definition] For Holonics, retain the typed signature and actual composition:
`X <- W_f -> Y`, with source population, joins, conditions, state, receiver and complete successor.
The algebraic term is a chart of that passage. Substitution must land in the receiving domain;
a change of material can change that domain. A law of the value projection alone does not
identify occurrences, retained fibres, chronology, implementation cost or independent execution.
A many-sorted/partial theory or category of admitted passages is the appropriate enlargement;
encoding everything into an unqualified magma would discard the distinctions being studied.

[proved-derived; formal-checked] This enlargement already has its semantic equality owner:
[`CausalRelevance`](../../formal/elementary-holonics/ElementaryHolonics/Foundation/CausalRelevance.lean).
For admitted generators T and receivers R,

\[
x\sim y\iff\forall r\in R,\;\forall w,\quad r(T_wx)=r(T_wy).
\]

It is the greatest generator-stable relation inside present receiver agreement. In additive
charts its invariant kernel descends through the existing joint quotient. Thus the useful
connection to equational theories is **congruence under admitted continuation**. A syntactic
rewrite is reusable only after its interpretation preserves that continuation. The source law,
receiver family and any executable decoder remain explicit. No runtime proof search or replacement
law registry follows from this comparison.

### Three distinctions with returned witnesses

[counterexample; computational-witness] The commutative, idempotent operation `a◇b=(a+b)/2`
is not associative: `(0◇0)◇4=2`, while `0◇(0◇4)=1`. Retaining `(sum,mass)` restores associative
addition; projection reads the weighted mean. This recovers the earlier tetrahedral normalization
example: loss of weight was a lost compositional operand, not a mysterious geometric failure.
The exact arithmetic is in [witness.py](../experiments/athena_equational_transport/witness.py).

[proved-standard; source-inspected] ETP's law 3994 implies law 3588 on finite magmas, but an
explicit operation on the naturals refutes the unrestricted implication. On the finite image of
multiplication, one-sided inverse maps become two-sided inverses. That inference fails for the
infinite model.[^infinite] Finite-dimensional coordinates, a finite mesh and a finite carrier
closed under its operation are different hypotheses. A finite sample of assignments establishes
none of these closure laws for a growing ecology.

[counterexample; computational-witness] For the source's natural-number operation, use XOR for
two even operands; `y+2` if only y is even; truncated `x−2` if only x is even; and zero for two
odd operands. At x=y=z=1, law 3588 compares 0 with 2. The witness additionally checks law 3994 on
512 assignments in the declared aperture; the all-natural proof belongs to the cited source,
not to that finite test. Its source operation is not truncated to an eight-element magma.

[established-bounded; source-inspected] ETP also constructs Austin laws with nontrivial infinite
models but only trivial finite models.[^austin] The architectural use is to distinguish an
abstract realization from a closed bounded-state implementation. A finite generator can describe
an infinite family of words or windings; executing or distinguishing arbitrary members still
requires its actual representation, decoder and resources. Compactness of a formula does not
supply an unlimited resident state or a universal efficient knot algorithm.

## Neural architectures as concrete specializations

[definition] A useful shared finite chart is

\[
j_i=\sum_{e:j\to i} C_e(M,o,z_i,z_j),\qquad z_i^+=R_i(M,o,z_i,j_i),\qquad y=b(z^+).
\]

Incidence, the transported operands, parameter sharing, response and retained state determine
which construction this is. The formula is not a requirement that every holon use scalar
summation or synchronous updates. The existing `FiniteLocalCurrentEcology` and
[composition guide](../../docs/HNN_COMPOSITION.md) already carry the relevant local-state law.

| Chart | Actual specialization | Law that can identify a realization | Distinction that remains |
|---|---|---|---|
| Perceptron / MLP | Affine contraction followed by a declared response; serial layers retain intermediate state | Matrix factorization and composition under matching nonlinear maps | An activation cannot generally be moved across a contraction |
| CNN | Offset-indexed incidence with translation-tied weights | Convolution/translation equivariance with transported boundaries and stride | Arbitrary dense or spatially varying coefficients need not obey it |
| Message-passing GNN | Edge-dependent messages and a permutation-compatible neighborhood receiver | Simultaneous vertex/edge relabeling transports the whole update | Incidence and edge features remain; a set of node values alone is insufficient |
| Attention | Query/key comparison, normalized participation, value transport and retained residual | A fixed participation chart acts linearly on values | Changed query/key state changes that chart; a frozen attribution is incomplete there |
| Linear SSM | `h_t=A h_(t-1)+B x_t`, `y_t=C h_t+D x_t` | The finite convolution and recurrent realizations agree with initial state retained | Equality of finite outputs alone does not give an all-history minimal state |
| Selective SSM | Input-dependent transition/input/readout maps | Ordered affine-map composition and its actual scan law | Generally no single fixed convolution kernel |
| Diffusion / restoration | A current evolves through a declared generator; restoration has its own conditioned law | Heat semigroup or discrete generator identities at the admitted metric | Corruption, learned reverse response and nonlinear transport are different maps |

[established-bounded; source-inspected] Message-passing research explicitly unifies several graph
architectures; S4 uses structured state-space/convolutional realizations; Mamba makes transition
parameters depend on the input and uses a recurrent scan.[^mpnn][^s4][^mamba] The shared passage
vocabulary therefore removes unnecessary architecture naming barriers while preserving the laws
that make particular realizations effective. It does not claim equal trained functions or costs.

[proved-derived] For fixed A,B,C,D and h₋₁,

\[
y_t=CA^{t+1}h_{-1}+\sum_{s=0}^t CA^{t-s}B x_s+D x_t.
\]

Induction on t proves the formula by substituting the preceding state equation; it retains the
initial-state term. The exact witness checks a nonzero-initial-state instance. Conversely the
selective scalar recurrence `h'=(1+x)h+x`, from zero, returns 3 on `(1,1)` but 1 on each of
`(1,0)` and `(0,1)`. Additivity fails, excluding a fixed linear convolution for this family.

[established-bounded; source-inspected] Circuit Tracing separates learned cross-layer feature
maps from prompt-specific interactions. Its local attribution construction freezes attention and
normalization denominators and retains reconstruction-error nodes. Its addition study restricts
attention to features active on a declared arithmetic domain. Large virtual weights can connect
features that never jointly affect the observed computation; activity and interventions matter.[^circuits]

[interpretation] The reusable HNN lesson is a separation between standing material, currently
admitted interaction, and the producing response. A positive scalar attribution cannot replace
causal incidence. Interventions should change actual source/current maps and retain the full
returned difference. A replacement graph needs its source-to-target map and remainder; local
faithfulness is not whole-architecture equivalence. Transformer Explainer supplies a useful
visual pattern for keeping source paths and residual branches visible, while its GPT-2 layout
remains one specific realization.[^explainer]

## The concrete Athena gap

[established-bounded; source-inspected] Review base `c60093b0` contains these decisive sources:
`examples/conversation_wave.rs:105–204` mounts parts and chooses actuation or local-stencil
development; lines 218–270 generate and save a numerical trajectory. `native/section_input.rs`
mounts the exterior alphabet but contains no generated-current-to-symbol emission. These paths
live in `crates/holonics-hna/`. The driver currently does not bind a reply to a situated prediction.

[established-bounded; source-inspected] In the engine's
`native_ecology/constitutive_fibre/field/material_transport/normal/direct/wave/`, `actuate.rs`
retains source and before/after joint fibres; `receive.rs` explicitly updates the next-current
pair `(p,c)->(c,v)`; `develop.rs` updates from supplied sections while retaining current occurrence
identity. `NormalWaveStep` exposes current and fibre. `ResidentNormalMaterial::prepare` supplies
staged bounded-source normal calculation. The missing binding is between these actual producing
operands and the addressed returned observation, not missing local learning or missing rest.

[counterexample; computational-witness] Start with one observation φ₀=(1,1,0), η₀=3/2 from
the zero-mean unit prior. Then H=I₃+φ₀φ₀ᵀ, B=η₀φ₀ᵀ, target energy 9/4 and the exact normal
reference P=BH⁻¹=(1/2,1/2,0). Its difference-chart prediction at z=(0,1) is 2. If an observed 3 corrects that prediction, φ=(1,1,0), η=2 and the normal update
is `(7/10,7/10,0)`. If 3 instead follows the generated 2 as a new next-current observation,
φ=(1,2,1), η=1 and the update is `(1/2,3/8,−1/8)`. Sherman–Morrison gives both exactly:

\[
P^+=P+\frac{(\eta-P\phi)\phi^\top H^{-1}}{1+\phi^\top H^{-1}\phi}.
\]

Both source vectors satisfy the actual plane relation φ₁=φ₂−φ₃. These are exact normal-reference
updates; the native applied M retains its separate realization bound. The distinction is the
producing comparison. No defect is alleged in `receive(v)` under its
next-current contract. The plan now requires the return to address the actual producing joint,
compose its receiver map and stage one complete successor. A response in an incompatible chart
requires its actual lift/fibre, not reinterpretation by equal width or a chosen center.

[proved-derived] When the same material also determines source actuation, the full finite response
retains both dependencies. For `v̂=c_s+Mφ(z_s)`, add and subtract `M⁺φ(z_s)` to obtain
`δv̂=δc_s+δM φ(z_s)+M⁺(φ(z_s⁺)−φ(z_s))`. The first normal packet conditions on retained z_s;
it is not the full derivative through earlier actuation. Its later-conduct comparison uses the
complete successor. An objective requiring the longer return must compose the actual producing
adjoint, without turning that into a universal full-history prerequisite. This recovers the
existing changing-receiver defect calculus in the concrete architecture.

[definition] The next packets are: producing comparison and development on the actual situated
current; native emission with an exterior codec; then further local-law/neighborhood and scale
composition as actual returned distinctions require. Existing local generators, normal response,
source actuation, condition ecology and rest remain returned. No `NormalWaveCurrent` conversion
to the older `NativeCirculationSession` is assumed. No universal full-history adjoint or global
architecture adapter is made a prerequisite. The blueprint states finite checks at each new join.

## Thickness continues through the existing world tube

[definition] The earlier ribbon half-width `w=1/3` and normal offset `w/4=1/12` were declared
embedding/display parameters. The ratio was not recovered from arithmetic strings or a physical
thickness law. The yellow faces represented `∂S × I`: the side boundary that joins the two lifts
of a one-sided surface's original boundary. This was a shell construction.

[proved-standard; source-inspected] A Möbius band has χ=0 and its regular neighborhood is a
solid torus. Möbius shorts are a punctured Klein bottle, χ=−1; their regular neighborhood is a
genus-two handlebody.[^shorts] Twisting an embedded solid torus changes geometric/framing data
but does not turn its boundary into genus two. The earlier exact incidence witness separately
checks both covers and shells. The new volume figure explicitly shows finite polyhedral bodies.

[definition] The existing `Transport/WorldTube.lean` composes clocked spans, membrane/current,
outward receiver and returned difference. `WorldTubePotential` transports the complete face
through resegmentation and boundary scale. `Physics/ConstitutiveWorldTube` supplies the concrete
constitutive state; `FourTorusParametronCurrent::{clockedCurrent,currentHistory}` binds actual
currents and the admitted scale square at grains 1 and 2. These existing owners are the
continuation of thickness, current and motion; no new volume subsystem is introduced.

[conditional] For a regular moving spatial region Kτ and a space-time current J=(ρ,j), its
world tube W is `{(τ,x):s≤τ≤t, x∈Kτ}`. Space-time Stokes gives

\[
\int_{K_t}\rho-\int_{K_s}\rho
+\int_{\Sigma_{lat}}J\cdot n
=\int_W\operatorname{div}_{\tau,x}J.
\]

The lateral term includes boundary motion through the space-time normal. For a material boundary
it is the relative flux `(j−ρ v_boundary)·n_spatial` integrated in time. A static three-volume
sweeps a four-dimensional world tube; a swept triangle is a three-dimensional world-sheet cell.
The exact prism witness cancels internal tetrahedral faces and returns end caps plus lateral
faces, with boundary squared zero. This instantiates the boundary algebra, not every PDE premise.
Topology-changing cobordisms can still satisfy Stokes; an extra defect is needed only when the
chosen passage omits a join/current or fails its boundary law, not merely because topology changes.

### Polygonal linked bodies and an exact fluid motion

[proved-derived; computational-witness] Two closed integral polygons are

\[
A=(-2,-2,0),(2,-2,0),(2,2,0),(-2,2,0),
\]
\[
B=(0,0,-1),(3,0,-1),(3,0,1),(0,0,1).
\]

B crosses A's +z-oriented spanning square once downward, giving `lk(A,B)=−1`. The other
vertical edge lies outside the disk. These are exact polygonal unknots with nontrivial linking;
no sampled smooth centerline supplies their identity. Their minimum ℓ∞ separation is 1. Choose
radius r=1/4 within `0<2r<1`; the two rectangular-annulus thickenings are disjoint. Each closed
triangular shell has V=16,E=48,F=32,χ=0; exact oriented volumes are 4 and 5/2. The radius is a
chosen admissible cross-section parameter tied to clearance, not a unique constitutive thickness.

[proved-derived] The shear `Fτ(x,y,z)=(x+τz,y,z)` has determinant one and inverse F₋τ. It
advects these complete bodies under `u=(z,0,0)`: divergence, convective acceleration and Laplacian
of u vanish. With constant pressure and zero force it satisfies incompressible Euler and NS for
any viscosity. This is an exact local/whole-space shear source, not periodic finite-energy data
for a Millennium endpoint. Linking and body volumes persist because the flow is an ambient
volume-preserving isotopy. The loops are material loops, not claimed vortex centerlines.

[proved-derived; computational-witness] Their circulation under this particular u is 0 and −6.
On each edge, `∫z dx=(z_i+z_(i+1))(x_(i+1)−x_i)/2`. Shear adds `τ∮z dz=0`, proving constancy
for every τ; the rational witness checks times 0,1/2,1. Existing `NavierStokesKelvin` supplies
curve-integral and conditional balance owners; its generic momentum-to-material-loop derivation
is still stated as work. The present explicit shear pays that source independently.

[proved-standard; source-inspected] Discrete Elastic Rods already treats polygonal centerlines,
edge material frames, discrete parallel transport, bending and twist, including dynamic knot
examples.[^rods] Smooth curves and polygonal curves can each be exact mathematical sources.
The relevant computational question is which geometry, motion and receiver a realization retains.
Knot type, geometric bending/twist, integral homology torsion and connection torsion have different
types. Standard Einstein geometry uses a torsion-free Levi-Civita connection; precession need not
imply connection torsion.[^gr] Our framed passages must state the actual connection and constitutive law.

## Hodge, primes and elliptic sources retain different data

[definition] Hodge decomposition separates exact, coexact and harmonic parts after a complex,
metric and boundary conditions are given. Betti numbers read topology; the nonzero spectrum
also depends on geometric/constitutive data. Integral torsion can disappear under real/rational
coefficients. The Hodge conjecture further asks for algebraic-cycle realization of rational
Hodge classes on smooth projective varieties; it is not the classification of arbitrary surfaces.
These distinctions already belong to the [relevance canon](../../docs/canon/THE_RELEVANCE_HYPOTHESIS.md).

[proved-derived; formal-checked] `NavierStokesTorusFourier::nonzeroModeHodgeReconstruction` inverts
curl on a nonzero divergence-free Fourier mode by `û=i(k×ω̂)/(2π|k|²)`.
`NavierStokesHodgeBandReconstruction::openPeriodicHodgeJacobianBandProjector_eq_actual` composes
it into the actual finite Jacobian band, with no infinite-convergence claim. `HolonicTorusKnots`
constructs coprime slope embeddings and retains full integral winding behind finite phase probes.
These are available specialized passages, not obligatory neural layers.

[established-bounded; source-inspected] The current RH line retains the ξ/heat source and the
remaining inequality `Λ_DN≤0`; a mesh Laplacian is not that arithmetic operator. The BSD owner
separates point counts, Frobenius coefficients and a declared analytic L-datum from the rank
comparison. `BirchSwinnertonDyer.lean::LDatum` states its analytic existence boundary explicitly;
`UniversalBSD` retains a curve-scoped formulation. Complex elliptic curves are genus-one complex
tori, but that topology alone does not retain their rational/arithmetic realization.

[counterexample; computational-witness] For `E_n:y²=x³−n²x`, n=1 and n=2, the point-count receiver
at good prime 5 returns Frobenius traces −2 and +2. The witness checks primes 3,5,7,11,13 through
the actual finite-field equation. The two complex genus-one surfaces thus have distinguishable
arithmetic faces. These finite coefficients determine neither analytic rank nor BSD. The useful
architecture consequence is to carry the source that realizes a spectral face, rather than infer
it from topology or a shared spectrum label.

### An actual arithmetic sign transport

[proved-derived] The two preceding curves give more than a shared genus. Over `Q(√2)`,
`f(X,Y)=(2X,2√2 Y)` carries `Y²=X³−X` to `y²=x³−4x`: both sides become
`8(X³−X)`. The Galois involution `√2↦−√2` changes f by the elliptic involution
`(x,y)↦(x,−y)`. This is a concrete sign-valued transport on an arithmetic source.

[proved-derived] For every odd prime p, writing χ for the quadratic character extended by
χ(0)=0 gives `a_p(E_n)=−sum_x χ(x³−n²x)`. Substitute x=2X in the n=2 sum;
2 is invertible and χ(8)=χ(2), so

\[
a_p(E_2)=\chi_p(2)\,a_p(E_1).
\]

This proves the twist relation from the actual finite-field source, without an analytic-rank
claim. The exterior witness verifies its five declared prime receivers. Arithmetic sign transport
and the orientation character of a Möbius loop are representations into `{+1,−1}` on different
source groups. Their reusable common operation is transport with retained character; identifying
the source groups or their spectra would require an additional map. This is the precise level at
which the geometric and arithmetic pictures can already compose in the framework.

## Verification and integration

[established-bounded; process-audit] The exterior rational/integer witness returns the law
counterexamples, producing-cut update, SSM realization, linked polyhedral bodies, material shear,
circulation, swept-cell boundary and elliptic counts. No native code or formal imports change.
The updated blueprint, architecture consumers and roadmap preserve existing returned scope and
name the next concrete composition. `python research/experiments/athena_equational_transport/witness.py` exits 0. The twenty-page
Typst build exits 0; changed plates 17–20 are rendered and visually inspected, and eleven current
PNG exports return. The producing-cut example is calibrated from one source-plane-admissible
observation of the unit-prior normal law. Review also verifies the distinction between the exact
normal reference P and the applied M. Cargo/Lean builds are unnecessary for these exterior
witness and documentation changes.

## Sources

[^etp]: Terence Tao and contributors. [Equational Theories Project](https://github.com/teorth/equational_theories), reviewed revision `bb5a9b5fe78c376ce1725529f235f8d574630b9f`.
[^laws]: Same project. [MagmaLaw.lean](https://github.com/teorth/equational_theories/blob/bb5a9b5fe78c376ce1725529f235f8d574630b9f/equational_theories/MagmaLaw.lean), `derive`, `satisfiesPhi`, `satisfies`, `models`; [FreeMagma.lean](https://github.com/teorth/equational_theories/blob/bb5a9b5fe78c376ce1725529f235f8d574630b9f/equational_theories/FreeMagma.lean).
[^complete]: Same project. [Completeness.lean](https://github.com/teorth/equational_theories/blob/bb5a9b5fe78c376ce1725529f235f8d574630b9f/equational_theories/Completeness.lean), `Soundness`, `FreeMagmaWithLaws`, `Completeness`.
[^infinite]: Same project. [Infinite models chapter](https://github.com/teorth/equational_theories/blob/bb5a9b5fe78c376ce1725529f235f8d574630b9f/blueprint/src/chapter/infinite_models.tex), propositions 3994⇒3588 for finite models and its unrestricted countermodel.
[^austin]: Same project. [InfModel.lean](https://github.com/teorth/equational_theories/blob/bb5a9b5fe78c376ce1725529f235f8d574630b9f/equational_theories/InfModel.lean), Austin equations 28770 and 374794.
[^circuits]: Emmanuel Ameisen et al. [Circuit Tracing: Revealing Computational Graphs in Language Models](https://transformer-circuits.pub/2025/attribution-graphs/methods.html), March 27, 2025, local replacement model, global weights, addition and limitations sections.
[^explainer]: Polo Club. [Transformer Explainer](https://poloclub.github.io/transformer-explainer/), reviewed September 10, 2026; GPT-2 visual computation chart.
[^mpnn]: Justin Gilmer et al. [Neural Message Passing for Quantum Chemistry](https://arxiv.org/abs/1704.01212), 2017.
[^s4]: Albert Gu, Karan Goel and Christopher Ré. [Efficiently Modeling Long Sequences with Structured State Spaces](https://arxiv.org/abs/2111.00396), 2021, revised 2022.
[^mamba]: Albert Gu and Tri Dao. [Mamba: Linear-Time Sequence Modeling with Selective State Spaces](https://arxiv.org/abs/2312.00752), 2023, revised 2024.
[^shorts]: [Topological Classification of Vittorio Giorgini's Sculptures](https://archive.bridgesmathart.org/2020/bridges2020-121.pdf), Bridges 2020, figure 11; disk/ribbon regular-neighborhood construction and exact cover/shell witness in the preceding plate source.
[^rods]: Miklós Bergou, Max Wardetzky, Stephen Robinson, Basile Audoly and Eitan Grinspun. [Discrete Elastic Rods](https://www.cs.columbia.edu/cg/rods/), ACM SIGGRAPH 2008.

[^gr]: Sean M. Carroll. [Lecture Notes on General Relativity](https://arxiv.org/abs/gr-qc/9712019), 1997, connection and curvature treatment.
