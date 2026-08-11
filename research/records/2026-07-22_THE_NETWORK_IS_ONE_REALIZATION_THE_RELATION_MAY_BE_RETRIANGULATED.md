# THE NETWORK IS ONE REALIZATION; THE RELATION MAY BE RETRIANGULATED

**Status:** BRANDON-RATIFIED CORRECTION / DEPOSITED / FIXED-BASIS TRANSFORMER INTERPRETATION

> **Currency note (2026-08-11):** the refusal below to promote an approximate total-active-parameter
> count was correct when deposited and can now be lifted with a citable source: **104B active**,
> `arXiv:2607.24653` (Kimi K3 technical report). The refusal's discipline — no approximate count
> promoted into fact — is retained; only the number's availability changed.
REGRADED / ARCHITECTURAL REWRITE DERIVED BUT UNSCHEDULED / SOMA INTERIOR UNCHANGED

## 1. The correction

The intended hypothesis is not that a developed neural skill can be preserved by ranking its
connections and cutting away the weak ones. A trained neural configuration is one realization of
a contextual transformation relation. Other internal factorizations may conduct sufficiently
similar receiver-relative consequences with less computation, memory movement, communication,
residency, latency, or energy.

The July 21 inherited-hexis authority already posed the correct question:

> How can acquired hexis become a persistent relational population whose locally compatible
> constituents can activate, specialize, compose, depart from physical residency, and return
> without requiring the entire ancestral body to participate in every current?

The later OLMo layer-7 experiment answered a narrower question. It measured exact contributions of
chosen hidden coordinates inside one fixed gated-MLP factorization. Its arithmetic remains exact,
but it incorrectly promoted those coordinate summands into independent neural laws and called one
small receiver-specific aperture a compressed hexis. This deposit supersedes that interpretation.

## 2. A neural network is a factorization, not a unique ontology

Write a network realization as

```text
F_theta = f_L circle ... circle f_2 circle f_1.
```

The parameters, channels, layers, residual paths, and expert boundaries belong to that
realization. Even a linear factorization is non-unique:

```text
B A = (B G^-1) (G A)
```

for compatible invertible `G`. Elementwise nonlinearities restrict which changes of basis can
cross them, but permutations and activation-compatible compensated scalings still produce many
parameterizations of one realized function. Conversely, changing the internal factorization can
change width, depth, skip incidence, expert partition, or carrier dimension while preserving a
declared exterior relation.

Three operations must therefore remain typed apart:

1. **carrier rebase or gauge** — coordinates change while incidence and the realized exterior law
   remain fixed;
2. **combinatorial retriangulation or refactorization** — the internal complex changes while a
   declared boundary relation is held; and
3. **metric or physical redistribution** — memory placement, communication distance, residency,
   latency, and energy change around the abstract relation.

This is the neural instance of the distinction already made in `ELEMENTARY_MECHANICS.md` between
carrier rebase, combinatorial rewrite, and metric hinge motion. Neural efficiency generally owes
the second and third operations. A fixed-coordinate activation census performs neither.

Relevant mathematical precedents include exact function-preserving changes between network
specifications in [Net2Net](https://arxiv.org/abs/1511.05641) and the permutation, scaling, and
additional non-identifiabilities studied in
[Hidden Symmetries of ReLU Networks](https://proceedings.mlr.press/v202/grigsby23a.html). These do
not prove that any smaller architecture can inherit any developed competence. They establish the
more elementary point that a neural parameterization is not a unique identity of its realized
relation.

## 3. The simplicial face of attention

An `n`-simplex is the convex hull of `n+1` affinely independent vertices. Its points have unique
barycentric coordinates

```text
x = sum_i alpha_i v_i,   alpha_i >= 0,   sum_i alpha_i = 1.
```

A zero coefficient places the point on a face. A simplicial complex closes under faces and lets
simplices meet along actual common faces. The abstract complex and one geometric realization of it
must remain distinct. The relevant elementary source is
[Foundations of Simplicial Complexes, §3](https://arxiv.org/html/2512.01323v1#S3).

For one softmax-attention receiver,

```text
alpha_(ij) = exp(q_i dot k_j) / sum_m exp(q_i dot k_m),
o_i = sum_j alpha_(ij) v_j.
```

At that event and candidate population, `o_i` lies in the convex hull of the current values. It is
a point in a genuine simplex only where those values are affinely independent; otherwise the
realized face is lower-dimensional or degenerate. The receiver query supplies one contact chart,
the keys address candidate sources in that chart, the normalized coefficients give deterministic
receiver-relative barycentric participation, and the values carry transported material.

Context changes the queries, keys, values, and often the admitted candidate population. It
therefore reorients the local complex rather than merely changing weights on one timeless field.
A masked source leaves this event-local face; it is not globally deleted. Residual addition,
multi-head composition, and output projection carry the result beyond this one convex chart and
rebase it into later overlapping complexes.

This supplies one rigorous face of the proposed gyrating simplicial manifold. A triangle is not a
scalar cell. It records a co-present relation, a possible comparison of composite and direct paths,
and a possible hinge for rewrite. Wolfram-style hypergraph replacement supplies arbitrary-arity
incidence and local rewrite; simplicial incidence supplies faces, boundaries, orientation, and
composition; actual transport supplies the receiver-relative law.

3Blue1Brown's neural-network series is useful here because it treats a network as composed
transformations and visually distinguishes distributed feature directions from literal
one-neuron concepts: [neural networks](https://www.3blue1brown.com/lessons/neural-networks/),
[attention](https://www.3blue1brown.com/lessons/attention/), and
[MLPs and superposition](https://www.3blue1brown.com/lessons/mlp/).

## 4. Attention acts across several independent architectural axes

“Attention” is not one primitive.

### Sequence incidence

Softmax attention explicitly constructs event-local source-to-receiver incidence over a retained
context. Kimi Delta Attention instead folds longitudinal relation into an evolving associative
state. Its delta-rule core has the form

```text
S_t = (I - beta_t k_t k_t^T) S_(t-1) + beta_t k_t v_t^T,
o_t = S_t^T q_t.
```

The standing first removes or corrects its present prediction along `k_t`, then writes the new
`k_t -> v_t` association. KDA refines scalar forgetting into finer channel-wise control. It is a
finite associative standing, not an explicit retained edge to every past token and not identical
to arbitrary softmax attention. See [Kimi Linear](https://arxiv.org/abs/2510.26692).

### Depth incidence

A conventional residual stack carries an effectively fixed accumulation of prior layer changes.
[Attention Residuals](https://arxiv.org/abs/2603.15031) lets a layer conditionally mix earlier layer
outputs, making depth adjacency input-dependent. The later
[Delta Attention Residuals](https://arxiv.org/abs/2605.18855) proposal instead routes changes
`h_(i+1)-h_i` and adds them to the immediate residual standing. These are depth-transport designs;
they are distinct from Kimi Delta Attention's sequence-state update.

### Transformation-family incidence

Mixture-of-experts routing selects which nonlinear transformation families participate.
[LatentMoE](https://arxiv.org/abs/2601.18089) projects a token into a lower-dimensional latent
carrier, routes and conducts expert transformations there, and projects the result back. Reduced
carrier width lowers memory and all-to-all communication cost, allowing the budget to be
reinvested into more total experts and richer active combinations. This is architectural
redistribution rather than post-hoc pruning.

Kimi K3 combines all three axes: KDA across sequence, AttnRes across depth, and Stable LatentMoE
across transformation families. Its public architecture names 2.8 trillion total parameters and
16 of 896 routed experts active at a selected event. The public page does not yet state one exact
total-active-parameter count, so this deposit does not promote an approximate count into fact.
See [Kimi K3](https://www.kimi.com/blog/kimi-k3).

Total parameters name the available parameter reservoir of one architecture. Active parameters
name the paths physically touched for one current under its routing law. An active set is not a
detachable skill: it depends on context, shared transforms, routing, training ecology, and later
composition. Nevertheless, an alternative architecture may place transformations which commonly
cohere into a more local and less expensive physical distribution.

## 5. Local duality, Chi, probability, and loss

An absolute `M` containing one preferred final realization is unnecessary. Let `M_i` be local
regions or charts with overlap maps

```text
g_(ij) : U_(ij) subset M_i -> U_(ji) subset M_j.
```

Where a common description continues, the transition maps satisfy a local cocycle relation. Two
neural factorizations are dual at a declared overlap when their external transport diagrams
commute there, even if their interior cells, coordinates, depth, and expert partitions differ.
Composition around a loop may return nontrivially; this path-dependent return is a holonomy face.
This is the useful local mathematical content of the string/M-theory comparison, not a claim of one
physical universal M-field.

For two paths `gamma_1,gamma_2 : a -> b`, the primary comparison is the complete parallel pair

```text
Chi(gamma_1,gamma_2) = (T_(gamma_1), T_(gamma_2)).
```

Where both maps are invertible, `T_(gamma_2)^-1 T_(gamma_1)` is a possible returned-holonomy
quotient. Where an additive chart is lawful, their difference is a possible residual. A projective
cross-ratio is one scalar chart of such comparison when four situated projective positions are
actually supplied. None is the universal identity of `Chi`.

An attention coefficient is therefore not absolute probability or truth. It is a deterministic
conditional quotient over one admitted candidate population. Changing that population changes the
quotient. Loss is the typed noncommutation or residual between expected/admitted transport and
actual returned transport at a declared boundary. A scalar training objective may project that
residual through an explicit update law; it does not become reward, punishment, correctness, or the
complete missing relation.

## 6. Exact regrade of the layer-7 cell

The exact run in `observations/eros-transformer-contextual-hexis-01/` remains useful evidence:

- the gated MLP was exactly decomposed into its chosen hidden-coordinate summands;
- contemporary context changed their contribution values and the source-selected population;
- different receiver quotients required different fixed-basis population sizes;
- the complete exact dyadic residual was retained; and
- the selected carriers crossed Soma, outlived their source lineages, conducted, and remounted.

Its interpretation changes as follows:

| Earlier term | Current reading |
|---|---|
| singleton law or single-neuron expert | separately addressable coordinate summand in one fixed gated-MLP factorization |
| five-law hexis | five-summand, source-selected sign-orientation aperture |
| compressed hexis | fixed-basis contextual participation census for one declared quotient |
| independent neural constituency | not established; channel identity changes under lawful reparameterization |
| learned routing or architectural efficiency | not measured; the source supplied incidence after a complete exact census |

The `5/8192` result preserved five selected output signs. It did not preserve magnitude, order,
BF16 identity, exact field, downstream continuation, skill, or a portable transformation law. Exact
identity required all 8,192 summands in that fixed basis. The result neither proves nor refutes that
a differently factored ecology could conduct a comparable contextual relation more efficiently.

This also restores the existing compression authority. Compression is every event's emitted
factorization of distinctions inactive at its declared consequential boundary. It is not defined
as choosing a small adequate subset from one ancestral coordinate system.

## 7. Boundary after deposit

The appropriate future probe is a boundary-preserving architectural rewrite: calibrate exact
rebases, choose a bounded trained transformation with materially different contexts and downstream
continuation, construct alternative internal complexes, compare complete receiver-relative
consequences and residuals, and measure computation, memory movement, communication, residency,
latency, and energy. LatentMoE is one instructive precedent, not the prescribed Eros architecture.

That construction is deliberately unscheduled. Brandon requested discussion and a discrete
mathematical abstraction of transport, foil, and hexis before another build.

## Decisive local relations

- `RESEARCH/2026-07-21_THE_INHERITED_FIELD_IS_HEXIS_THE_CURRENT_MOUNTS_ITS_RELATIONAL_REGION.md`
- `ELEMENTARY_MECHANICS.md`
- `RESEARCH/2026-07-21_THE_HYPERGRAPH_SUPPLIES_THE_REWRITE_THE_TRIANGLE_CARRIES_THE_COMPARISON.md`
- `RESEARCH/2026-07-22_THE_EXPERT_IS_THE_CONTEXTUAL_HEXIS_THE_MIXTURE_IS_THE_EMANATING_FIELD.md`
- `observations/eros-transformer-contextual-hexis-01/RESULTS.md`
