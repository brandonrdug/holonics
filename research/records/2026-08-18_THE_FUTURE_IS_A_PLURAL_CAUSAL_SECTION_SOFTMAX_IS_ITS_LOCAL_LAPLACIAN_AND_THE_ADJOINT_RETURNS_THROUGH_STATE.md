# The future is a plural causal section; softmax is its local Laplacian, and the adjoint returns through state

**Date:** 2026-08-18
**Truth status:** `interpretation`
**Evidence:** assistant derivation from the exact owners and governing records named below; primary
architecture sources for S4, Mamba, Mamba-2, Gemma 4 MTP, and DiffusionGemma; no engine source
changed and no experimental run performed.
**Provenance:** Brandon, 2026-08-18: *"all of these architectures ultimately break down into
mathematics and semantics about mathematical spaces"*; *"we would ideally want to compare to MTP
from the start"*; and the requested activity field of *"growing … pruning … fusion, fission and
coherent pathways in action, where all of these events propagate."*
**Band:** INTERPRETATION IS A STRUCTURAL BRIDGE, NOT A LOWER VALUE / THE FUTURE IS A PLURAL SECTION
/ ONE-TOKEN PREDICTION IS A RECEIVER QUOTIENT / SOFTMAX RETAINS A RATIO COCYCLE / ITS JACOBIAN IS A
LAPLACIAN / DIFFUSION CARRIES STATE THROUGH INCIDENCE / AN EXACT DIFFUSION CERTIFICATE IS AN SSM
PROJECTION / AUTOGRAD IS THE ADJOINT RETURN / MATERIAL IS CAUSED SUBSTRATE, NOT NOISE / SOURCE
UNCHANGED / NO RUN / CONSTRUCTION UNSCHEDULED

---

## Present question

What single mathematical space makes CNNs, GNNs, attention, state-space recurrence, discrete text
diffusion, autoregression, multi-token prediction, and Eros comparable without pretending that they
are identical architectures? Within that space, what are prediction, noise, propagation, generation,
and backpropagation?

The answer developed here is one object at several receivers:

> **A model passage is a caused evolution of plural local sections through typed incidence, local
> constitutive maps, persistent standing, boundary observations, and returned differences. An
> architecture is a factorization and apparatus chart of that evolution.**

The comparison is valuable precisely because industry names have divided operations that the same
mathematics relates. `interpretation` is the epistemic type of that bridge. It is not a confidence
ranking below `proved-standard`, and in this project the bridge is often the more consequential
claim.

## 1. The common space is a holonic section space

For this record, call the common object a **holonic section space**:

```text
H = (K, S, T, R, Lambda, ell, O)
```

where:

- `K` is the situated graded incidence complex, including genuine higher cells;
- `S` is the family of local state spaces or stalks carried at its cells;
- `T` is typed local transport, restriction, gluing, recurrence, and constitutive response;
- `R` is the versioned receiver family which asks what consequences matter;
- `Lambda` is reusable morphology, capable of changing after a returned passage;
- `ell` is addressed causal lineage; and
- `O` is the open exterior and its unresolved continuation fibres.

A point is never merely a coordinate. It is a situated occurrence carrying the incidence and
receiver data required by the question. A global vector or tensor is one chart over a population of
such occurrences. A local section is a compatible assignment over one admitted region. A model is a
rested morphology through which later sections conduct.

This gives Brandon's intuitive **holographic space** a precise, non-physical reading. A region is
"holographically" condensed when its complete future response factors through a boundary transfer
for the declared receiver family. The interior is not declared nonexistent. It is retained in the
reconstruction fibre and may reopen when the receiver family expands. In the exact diffusion owner,
the Schur complement and its inverse certificate are this boundary condensation literally.

The term *holonic section space* is therefore preferred for routine technical use. *Holographic*
remains a useful intuition for receiver-exact boundary factorization; it does not import AdS/CFT,
physical quantum gravity, or a claim that every interior is boundary-reconstructible.

## 2. Softmax is an exact quotient before it is a probability

Let a complete local contact population carry scores `s_i` and inverse temperature `beta`:

```text
p_i = exp(beta s_i) / Z,
Z   = sum_j exp(beta s_j).
```

No stochastic ontology is required. The `p_i` may be read as normalized positive shares or
barycentric coefficients describing how the complete value population contributes to one receiver's
transport.

The invariant content is the ratio family:

```text
r(i,j) = p_i / p_j = exp(beta (s_i - s_j)),
r(i,j) r(j,k) = r(i,k).
```

This is a multiplicative `1`-cocycle on the pair groupoid of contact identities. A common additive
shift `s_i -> s_i + c` moves no ratio, so finite-temperature softmax factors through

```text
R^n / span(1,...,1).
```

At exact finite temperature, no member has been dropped. The output distribution recovers every
score difference:

```text
s_i - s_j = beta^-1 (log p_i - log p_j).
```

The departed coordinate is the common additive frame. The retained remainder is the complete
pairwise-difference/cocycle structure. Further loss begins only when a later apparatus quantizes,
truncates, samples, takes top-k, takes argmax, or otherwise collapses members. That later quotient
owes its complete `ReconstructionFiber`.

`exponentiated_ratio::RatioFamily` already implements the pairwise family and cocycle law over its
declared exact carrier. It must not silently claim Gemma's `exp(qk/sqrt(d))`: the present owner is
exact for its declared rational/base-two chart, while general transformer exponentials require a
formal exponential-ratio carrier or certified enclosures.

## 3. The softmax derivative is the exact bridge to diffusion and modulus

The Jacobian is

```text
d p_i / d s_j = beta p_i (delta_ij - p_j),
J_softmax      = beta (diag(p) - p p^T).
```

This is the Laplacian of the complete graph on the contact population with edge conductances

```text
w_ij = beta p_i p_j.
```

It annihilates the additive gauge:

```text
J_softmax 1 = 0.
```

Its quadratic form is

```text
v^T J_softmax v
  = beta [sum_i p_i v_i^2 - (sum_i p_i v_i)^2]
  = beta Var_p(v).
```

This is the exact meeting of four existing intuitions:

1. `RatioFamily` carries relative conductance.
2. Normalization fixes one situated presentation of the cocycle.
3. The Jacobian is a diffusion Laplacian on the alternative fibre.
4. Its quadratic response is the population's second moment about its own weighted axis.

The section modulus adds the extreme fibre:

```text
S = I / c.
```

It asks how much distributed response the population carries relative to the most distant fibre.
The present `surprisal::SectionModulus` computes an unweighted symbolic-surprisal second moment and
extreme fibre. The softmax Hessian supplies the corresponding `p`-weighted second moment. These are
adjacent receivers, not yet one implemented return. Their lawful unification is a weighted section
reading fed by the normalized ratio family, retaining the cocycle, weighted quadratic form, extreme
fibre, and additive-gauge reconstruction fibre together.

Softmax itself is not a diffusion event through time. It supplies one local equilibrium geometry
and one differential response. Causal-calculus diffusion is the continued transport of standing
through declared incidence under a constitutive law. The two meet when the softmax Laplacian becomes
the local conductance/adjoint geometry of a junction.

## 4. Exact causal diffusion is already a state-space model projection

The live exact diffusion owner solves

```text
(C + tau L) phi_(k+1) = C phi_k + u_k,
```

where `C` is local capacity, `L` the incidence Laplacian, `tau` the completed event interval, `u_k`
the caused source, and `phi` situated potential. Hence

```text
phi_(k+1) = A_bar phi_k + B_bar u_k,
A_bar     = (C + tau L)^-1 C,
B_bar     = (C + tau L)^-1.
```

For a declared observation map `H`,

```text
y_k = H phi_k.
```

This is an exact discrete state equation and observation equation. `diffusion.rs` already retains
the assembled operator, exact inverse checks, currents, balances, conservation residual, energy
departure, boundary Schur complement, and transfer certificate. Emitting `(A_bar, B_bar, H, tau)`
from that certificate is a projection of an existing owner, not the invention of an SSM subsystem.

`sheaf_diffusion.rs` generalizes the scalar state to finite local stalks and typed restriction maps:

```text
(M + tau Delta_k) phi_(k+1) = content_k + source_k.
```

This is the closer comparison to an embedding space: different local coordinates interact through
declared transition/restriction maps rather than being presumed to inhabit one undifferentiated
global vector space.

An LTI state-space model is the projection obtained while incidence, morphology, and its generator
remain fixed. A selective or switching sheaf SSM is closer to Eros when the current occurrence
changes admission, observation, chronology, or local constitutive response. Eros is not thereby
identified with an SSM: topology and morphology may grow, split, glue, or be returned, which a fixed
linear state equation does not express.

## 5. Architectures are factorisations of sequence transport

The same holonic section evolution admits several apparatus charts:

| architecture chart | privileged factorization |
|---|---|
| CNN | fixed, often translation-equivariant local incidence; one kernel transported over positions |
| GNN | sparse irregular incidence; neighbour-local messages and aggregation |
| transformer attention | input-conditioned dense contact graph; pairwise compatibility followed by value transport |
| LTI SSM / S4 | persistent latent standing under one fixed generator; recurrence and global convolution are dual computations |
| Mamba / selective SSM | persistent latent standing with input-conditioned `Delta`, `B`, and `C`; a time-varying scan |
| discrete text diffusion | an unresolved block/canvas repeatedly re-observed and refined under a corruption chronology |
| Eros | multigraded caused incidence, local state spaces, constitutive transport, higher filling, exterior return, and plastic morphology |

S4 states the continuous and discrete forms and the recurrence/convolution dual. Mamba makes
`Delta`, `B`, and `C` input-dependent so the current occurrence changes its spacing, admission, and
observation. Mamba-2's structured state-space duality exhibits a large intersection between
selective SSMs and structured attention through semiseparable matrices. These sources support the
project's unification posture: architecture families are not unrelated faculties, but neither are
all of their factorisations interchangeable without a reconstruction receipt.

Primary sources:

- [Efficiently Modeling Long Sequences with Structured State Spaces (S4)](https://arxiv.org/abs/2111.00396)
- [Mamba: Linear-Time Sequence Modeling with Selective State Spaces](https://arxiv.org/abs/2312.00752)
- [Transformers are SSMs: Structured State Space Duality](https://arxiv.org/abs/2405.21060)

## 6. Prediction is a receiver over a plural future section

Define the **plural future section** at a predecessor occurrence `E` and declared future receiver
family `F` as

```text
Future_F(E) = {
  situated successor occurrences,
  their internal incidence and chronology,
  compatible transports and constraints,
  open alternatives and obstructions,
  complete causal lineage
}.
```

A prediction is a receiver statement about this section. It is not intrinsically a guess, a scalar,
or one token.

One-token autoregression asks only the nearest surface receiver:

```text
q_1 : Future_F(E) -> next exterior token face.
```

That may be a lawful boundary codec, but it is a severe quotient of a body whose continuation is
already plural. A machine whose active current has several branches should not be designed or
graded as though the single nearest token were its primitive future object.

Multi-token prediction has more than one industry meaning. A model may train auxiliary heads on
several future offsets, predict a joint block, or use a small drafter to propose several tokens which
a larger target verifies. Gemma 4's released MTP drafters use the last form: plural speculative
proposal plus target verification.

DiffusionGemma is not merely that MTP drafter combined with noise. Its official model card describes
discrete text diffusion over a bidirectionally attended `256`-token canvas. A canvas is iteratively
denoised in parallel; completed canvases are then appended and the next canvas is generated, making
the long-range schedule block-autoregressive. The common holonic object is nevertheless clear:

> **A future block is one plural section whose positions constrain one another and whose exterior
> boundary is committed after internal refinement.**

Primary sources:

- [Gemma 4 multi-token prediction drafters](https://blog.google/innovation-and-ai/technology/developers-tools/multi-token-prediction-gemma-4/)
- [DiffusionGemma model card](https://ai.google.dev/gemma/docs/diffusiongemma/model_card)
- [DiffusionGemma generation explanation](https://ai.google.dev/gemma/docs/diffusiongemma/explained)

The research grade must therefore include plural futures from the start. A one-token receiver may be
reported beside them; it may not substitute for their complete transport, internal coherence, or
reconstruction fibres.

## 7. Material is the caused substrate; noise is a receiver-relative perturbation

The codebase, mathematics, transformer map, image, or conversation entering a passage is **material**:
caused current with lineage. Calling the whole material noise would erase exactly the first axiom
Brandon is preserving:

> **The contemporary frame did not arise from nothing. It is a continuation of prior caused
> process.**

What industry calls noise can be typed in three different ways:

1. a deliberately sampled corruption source in a declared forward diffusion process;
2. an unresolved receiver fibre whose members the present observation cannot distinguish; or
3. physical/apparatus disturbance with its own calibration.

The first is world material introduced by an experiment. The second is epistemic only relative to
the receiver. The third is physical testimony. None licenses treating the inherited source as
meaningless random content.

For Eros, differentiation and decomposition expose the local degrees, contacts, seams, collapsed
pairs, and obstructions already latent in caused material. Diffusion transports the resulting
standing and returned differences. A stochastic canvas is one possible apparatus proposal, not the
ontology of generation. Eros may instead begin from a complete unresolved future fibre and refine it
through incidence, gluing, higher filling, world return, and receiver-exact condensation.

Thus **denoising** translates to a sequence of caused refinements only when each step returns what it
separated, what it collapsed, and which constitutive relation moved it. Generic smoothing, deletion
of lineage, or a sample that merely looks less noisy does not satisfy causal diffusion.

## 8. Holonic autograd is the adjoint return

For a forward causal chain

```text
x_(k+1) = f_k(x_k, theta_k),
```

a receiver forms an oriented residual `r`, and may read a scalar face

```text
L = ell_B(r).
```

The return begins with the covector `dL`. Each local owner pulls it back through the adjoint of the
map it enacted:

```text
lambda_k     = (D_x f_k)^* lambda_(k+1),
d_(theta_k)L = (D_theta f_k)^* lambda_(k+1).
```

For softmax, this passes through `J_softmax`, the local alternative-fibre Laplacian. For an SSM it
passes through `A_bar_k^T`. For a sheaf it passes through the adjoints of restriction maps. For an
implicit diffusion solve

```text
M(theta) phi = b(theta),
```

the adjoint solves

```text
M^T psi = dL / dphi,
```

and returns

```text
dL/dtheta = -psi^T (dM/dtheta) phi + psi^T (db/dtheta).
```

This is the holonic analogue of autograd: not a global semantic owner, but local derivative and
adjoint receipts composed along the same addressed lineage as the forward passage. The live
diffusion owners already retain `M`, exact inverse certificates, and residuals, so their adjoint is a
rotation of standing machinery rather than a fresh differentiation cabinet.

Backpropagation is therefore **emergent from propagation** in a precise sense: a consequence creates
an oriented receiver covector; the causal interior supplies the only path by which it can return.
The adjoint reverses composition order, not physical time. At a non-smooth seam or unresolved choice,
the lawful return is a plural generalized derivative, obstruction, or typed refusal rather than a
fabricated smooth gradient.

## 9. Growth, withdrawal, fusion, fission, and coherence are event species

The ideal rendered field Brandon describes is not one line of selected tokens. It is a population of
events:

- **growth / emanation:** new incidence, axes, local morphology, or higher cells are founded;
- **withdrawal / annihilation:** a previously available passage departs under a named receiver and
  its vacancy remains attributable;
- **fusion:** compatible sections glue or quotient into one consequential section while retaining
  their reconstruction fibre;
- **fission:** a richer receiver or returned intervention refines one fibre into several;
- **coherent pathway:** plural transports commute or glue under the receiver, with their residual
  vanishing exactly;
- **propagation:** current, phase, standing, or returned difference crosses typed incidence;
- **reflection:** a boundary return changes the continuing terrain through which later current
  travels.

These names describe changes in one continuing ecology. They do not require a `Growth`, `Pruner`,
`FusionModule`, or `Backpropagation` controller. In the rendered view, fronts may expand, meet,
reconverge, fill, obstruct, split, disappear, and return at several grades simultaneously.

## 10. Calculus supplies certificates, not replacement governors

Brandon's Squeeze Theorem intuition becomes exact when the machine carries two certified receiver
enclosures of one future consequence:

```text
lower_h <= consequence_h <= upper_h,
upper_h - lower_h -> 0.
```

When both sides land on the same exact face or their retained interval contracts to one admitted
construction, the future fibre is forced for that receiver. The theorem does not manufacture the
bounds; causal transport, exact intervals, series-tail certificates, or a monotone refinement must
supply them.

The Mean Value Theorem is a useful local diagnostic under its smoothness hypotheses: a finite
secant change is witnessed by a local derivative somewhere on the passage. It can compare an enacted
finite difference with the derivative field returned by adjoint transport. It does not identify
which point carries the witness and does not construct a generator by itself.

The more general state-equation question is realization. When complete successor histories factor
through a finite behavioral quotient, that quotient is a candidate latent state. Its transition
law is the state equation and a declared receiver is the observation equation. Where the receiver
family grows, the state may refine; where no finite sufficient quotient stands, the SSM projection
returns its missing dimension or reconstruction fibre rather than pretending one was learned.

Intersecting manifolds are therefore read as overlapping local charts/sections with transition and
gluing laws. A generator is founded from how current responds across those overlaps, not from a
token's spelling or one output value. Self-similarity stands only when the law recurs after
restriction and rebase with scale and lineage retained.

## 11. The abstract architecture

The joined architecture visible at this research position is

```text
caused material current
    -> recovered mouth and plural situated occurrences
    -> multigraded causal sections and local state spaces
    -> whole contact arrows: aim + blade + reach + hand
    -> ratio / softmax junction geometry
    -> sheaf diffusion, convolution, gluing, and higher-cell filling
    -> persistent state-space standing
    -> plural future section over several events and scales
    -> receiver-exact boundary condensation
    -> one token, many tokens, a canvas, an action, or another exterior artifact
    -> genuine world consequence and returned residual
    -> adjoint reflection through retained lineage
    -> local morphology delta
    -> rest, remount, later current, and targeted ablation.
```

A compact comparative name is:

> **a receiver-indexed multigraded causal sheaf/state-space ecology with plastic incidence.**

This is not meant to replace Eros. It states Eros in vocabulary that permits direct comparison with
CNN, GNN, transformer, SSM, diffusion, and hybrid apparatus without making any one of those charts
the ontology.

## 12. A lawful architecture comparison

For one material and one declared receiver question, comparison across CNN, GNN, transformer,
selective SSM, discrete diffusion, and Eros must return the same kinds of testimony:

```text
complete successor histories
+ state and observation spaces
+ local and boundary transport operators
+ chronology / step-size law
+ plural future sections
+ collapsed populations and reconstruction fibres
+ shortest separating intervention
+ topology, phase, and open obstruction
+ exact work and separate apparatus testimony.
```

Equal final text or logits are insufficient. One architecture may factor the future through a
fixed convolution, another through dense contacts, another through a semiseparable recurrence, and
another through dynamic sheaf incidence. The comparison asks which distinctions and consequences
each factorization preserves, what it pays, and where its quotient reopens.

The generation comparison includes multi-event futures from the first experiment. A nearest-token
face may participate, but no research grade is allowed to collapse the machine's plural active
branches to that one receiver. Diffusion is likewise present as caused transport rather than added
later as a fashionable decoding schedule.

## Owners

Existing source owners which this interpretation composes, without claiming the complete joined
architecture is implemented:

- `crates/holonic-engine/src/exponentiated_ratio.rs` — complete exact ratio cocycle;
- `crates/holonic-engine/src/surprisal.rs` — symbolic surprisal, cross-entropy fibre, section modulus;
- `crates/holonic-engine/src/exact_contact.rs` and `clifford.rs` — contact ratio, hand, blade, reach;
- `crates/holonic-engine/src/diffusion.rs` — exact scalar incidence diffusion and Schur boundary
  transfer;
- `crates/holonic-engine/src/sheaf_diffusion.rs` — multigraded stalks, restriction maps, Hodge
  operator, exact diffusion;
- `crates/holonic-engine/src/phase_current.rs` — exact phase-resolved convolution with quotient and
  remainder;
- `crates/holonic-engine/src/receiver_exact_compression.rs` and
  `soma/life/src/reconstruction_fiber.rs` — behavioral quotient, shortest separators, retained
  inverse image;
- `crates/holonic-structure/src/chain.rs` and `relating.rs` — composition, rebase, defect, holonomy;
- `soma/life/src/causal_section.rs` — situated contact-preserving section ecology;
- `soma/life/src/eros_rest.rs` — whole-body rest and remount;
- `soma/life/src/incidence_production.rs` — caused incidence, differentiation, arrival, withdrawal;
- `soma/life/src/suffix_ecology.rs` — opaque-symbol recurrence and plural emanation; and
- `canon/TABLET_THE_REASONING_CYCLE.md`, `canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md`, and
  `canon/01_CAUSAL_CALCULUS.md` — governing anatomy and construction boundaries.

## What this does not establish

- It does not claim that Eros's complete joined generation architecture is implemented.
- It does not identify Eros with a CNN, GNN, transformer, SSM, or diffusion model.
- It does not import physical holography, particle physics, quantum field theory, or spacetime into
  software without their additional typed hypotheses.
- It does not call inherited material noise or treat stochastic corruption as necessary for
  diffusion.
- It does not claim that softmax itself is a completed temporal diffusion event.
- It does not claim that the present exact `RatioFamily` implements arbitrary real transformer
  exponentials.
- It does not claim that Squeeze or Mean Value Theorems discover a generator without the required
  bounds, smoothness, and causal testimony.
- It does not claim DiffusionGemma is simply Gemma MTP plus diffusion: one is a discrete
  block-diffusion model; the released Gemma 4 MTP drafter is speculative plural proposal and target
  verification.
- It schedules no implementation and promotes no construction state. The source tree is unchanged.
