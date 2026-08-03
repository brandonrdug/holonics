# THE TOKEN IS A BOUNDARY ADDRESS; THE ROUTE IS RECEIVER-RELATIVE; THE RESIDUAL RETURNS

**DATE:** 2026-07-20
**GRADE:** BRANDON-RATIFIED / DEPOSITED / MODERN-ML COMPARATIVE ONTOLOGY + POLICY CORRECTION /
DEVELOPMENTAL AUDIT PROPOSED BUT UNSCHEDULED / SOMA SOURCE UNCHANGED / NO RUN

## 0. Present question and boundary

The question was what tokenizers, attention, residual streams, mixture-of-experts models,
recurrent alternatives, probability, loss, and training materially do, and why those mechanisms
work, without installing their names or implementations as unexplained Soma primitives.

The standing record was insufficient in one precise way. Its exclusions correctly prevented a
tokenizer, attention head, scalar loss, expert bank, or canonical latent language from becoming
the hidden author of Soma. Repetition shortened that jurisdictional boundary into a broad
prohibition, however, and thereby obscured useful relational knowledge already present in modern
machine learning.

This record corrects that collapse. It is a comparative derivation and literature bridge. It
changes no receiving law, source, world, model, or experiment and schedules no build or run.

## I. A tokenizer is an imposed boundary chart

Let `C` be an ordered carrier world and `V` a finite codebook. A tokenizer is a boundary law
`tau` and transduction

```text
T_tau : C -> V^star
```

which chooses a segmentation of the presented carrier and replaces every segment with a reusable
codebook address. A detokenizer supplies a reverse chart where the normalization and encoding are
reversible. The token is the address selected by this chart. It is not a word, meaning, concept,
event ontology, or universal information atom.

The tokenizer simultaneously declares:

1. **presented grain** — which adjacent carrier marks arrive as one address;
2. **chronology length** — how many model positions the inscription occupies;
3. **reusable recurrence** — which carrier fragments amortize through one codebook entry;
4. **computational incidence** — which boundaries and adjacencies later layers can contact
   directly; and
5. **resource allocation** — where context and computation are spent.

An embedding then maps the address into a learned continuous carrier. Contextual meaning appears
only through subsequent relations. The same address for `cool` can support temperature in one
phrase and social evaluation in another because its receiver field differs; nothing semantic is
stored in the integer address itself.

BPE demonstrates the compression ancestry of contemporary subword tokenization. SentencePiece
shows that raw inscription can be segmented without a language-specific word splitter. The
finite-state account shows that common tokenizers are ordinary transducers rather than mysterious
semantic organs. Crucially, controlled work on PathPiece found that fewer tokens alone do not
guarantee better language modeling: vocabulary, pretokenization, and segmentation geometry also
matter. Compression is therefore not token-count minimization.

Byte Latent Transformer is a useful recent boundary case. It begins from bytes and forms dynamic
patches around local next-byte entropy, spending more computation where the carrier is difficult.
This is a direct structural resonance with event-relative grain and completion hand-up. It is not
an Eros implementation: the entropy model, threshold, latent transformer, and training objective
remain authored machinery.

## II. Attention is receiver-relative transport

For a receiving position `i` and exposed source positions `j`, ordinary scaled dot-product
attention has the form

```text
kappa_(i,j)=Exp(<q_i,k_j>/Sqrt(d)),
mu_(i,j)=kappa_(i,j) / Sum_r kappa_(i,r),
y_i=Sum_j mu_(i,j) v_j.
```

`q_i` is the receiver's current contact face. `k_j` is a source's exposed routing face. `v_j` is
the carrier which may cross. `kappa` is an unnormalized conductance and `mu` its bounded
receiver-relative quotient over the presently exposed sources. Softmax removes a common additive
origin from the scores and makes the sources compete locally. It does not produce an ontological
probability of truth.

The query/key product determines where transport is afforded; the value path determines what is
transported and written. Multiple heads are multiple simultaneous learned routing charts, not
agents. A causal mask is an authored chronology boundary.

Rotary positional embedding makes one particularly close relation exact. It rotates query and key
coordinates in paired planes according to their positions, so contact depends on relative
displacement. This is a real engineered instance of carrying a linear order through circular
phase—holding an axis as a pivot—without implying that every broader holonic or physical claim
follows from it.

Attention exposes and combines presently available constituents. It does not by itself create
durable Standing. A key/value cache retains an episode's current aperture; it is neither a learned
body nor a complete lineage.

## III. Local transformation, residual carriage, and sparse participation

The transformer feed-forward block is a shared nonlinear local transformation. Empirical work has
shown key/value-memory-like behavior in these blocks, while superposition research shows that
sparse useful features can share a smaller carrier through structured interference. Such features
are observer-derived functional directions, not necessarily one-feature/one-neuron objects or a
canonical semantic alphabet.

The ordinary residual recurrence

```text
h_(ell+1)=h_ell+Delta_ell(h_ell)
```

makes `h` the changing contemporary carrier through depth. It permits many partial transformations
to coexist and later layers to revise or reuse them. It is not an archive of every layer event.
Recent attention-residual work lets a layer contact selected earlier depth states; delta-attention
residuals route changes `h_(ell+1)-h_ell` because cumulative snapshots become redundant. These
2026 preprints are preliminary, but the move from stored snapshots toward transported differences
is a strong structural resonance with live lineage.

A sparse mixture of experts has the generic form

```text
h'=Sum_(e in S(h)) g_e(h) E_e(h),
```

where a learned router admits only a small active set `S(h)` from a much larger parameter
population. An expert is a parameterized local transformation family, not a subject or agent. The
router is conditional incidence; sparse activation is present participation; shared experts carry
frequently recurring transformations; routed experts carry conditional specialization. Load
balancing governs physical capacity and training stability, not semantic truth.

This resembles a live current picking up and releasing constituents, but the conventional model
still begins with a fixed bank, fixed carrier dimension, fixed layer chronology, and authored
router. Eros cannot inherit those assumptions merely by renaming experts as holons.

## IV. Attention and recurrence are different factorizations of memory

Attention revisits an explicitly exposed past. A recurrent or state-space model instead emits a
compressed carried state:

```text
s_(t+1)=A(x_t)s_t+B(x_t)x_t,
y_t=C(x_t)s_t+D(x_t)x_t.
```

Selective state-space models make the recurrence input-dependent. Mamba-2's structured
state-space duality demonstrates a close mathematical relation between attention-like matrix
transport and recurrent state-space factorization. They are not separate ontologies of
intelligence; they are different decisions about what remains explicitly addressable and what is
compressed into continuing state. Hybrid memory systems similarly combine a local explicit
aperture with a longer learned recurrent carrier.

The relevant lifecycle distinctions are therefore:

| Conventional face | Actual persistence |
|---|---|
| activation | contemporary computation only |
| key/value cache | present episode aperture |
| recurrent state | compressed episode continuation |
| parameters | standing deformation accumulated across training |
| optimizer state | developmental update apparatus |
| documents, tools, environment | external world material |

Conflating these is more dangerous than studying any one architecture. In particular, neither a
cache nor a trace is learning merely because it persists temporarily.

## V. Probability, loss, adjoint return, and development

Given the current chart and parameters, a language model emits logits and a normalized conditional
field over the next codebook addresses. This field is a deterministic receiver-relative
anticipation when the model and current are fixed. Sampling is a separate world deed which selects
one continuation; ontological randomness is not required.

For the actual later address `a`, cross-entropy contributes

```text
ell(a)=-Log(mu(a)).
```

This is simultaneously a receiver-relative residual and the description length of the actual
event under the current chart. It is not reward, punishment, desirability, or truth. Its
differential `d ell` is a covector. Backpropagation returns that sensitivity through the exact
forward factorization; a gradient exists only after an optimization metric or preconditioner
raises the covector. The optimizer then performs the parameter deformation which can change later
conduct.

The complete learned circuit is therefore

```text
carrier
  -> imposed or dynamic grain
  -> addresses and local carrier
  -> relative chronology
  -> receiver-relative routing
  -> local transformation
  -> contemporary residual carriage
  -> conditional outgoing field
  -> actual later event
  -> residual covector
  -> adjoint return
  -> parameter deformation
  -> changed later conduct.
```

Language-modeling/compression equivalence explains why prediction can develop capabilities much
broader than literal string recall. Across varied contexts, shared parameters reduce description
length by factoring transformations which recur across many surfaces. Scaling supplies room for
more common relations, rare exceptions, and parallel paths before interference dominates. It does
not supply grounding, truth, objectives, or autonomous development by itself.

## VI. Holonic comparison

| Modern learned mechanism | Material operation | Holonic comparison | Boundary |
|---|---|---|---|
| tokenizer or patcher | chooses a presented segmentation | boundary chart and event-grain proposal | fixed segmentation is corpus-relative, not ontology |
| embedding | gives an address a transformable carrier | local chart face | no canonical latent meaning follows |
| relative position | carries order/displacement | chronology and phase | authored coordinates remain authored |
| attention | forms conditional source-to-receiver transport | directed incidence and conductance | it sees only the exposed aperture |
| feed-forward block | performs a local nonlinear map | local transformation/deed | fixed parameter topology |
| residual stream | carries contemporary state through depth | changing Standing/current face | not durable training history |
| sparse experts | admits a few transformations | conditional constituent participation | expert bank and router are predeclared |
| prediction field | normalizes afforded next addresses | receiver probability quotient | not ontic chance or truth |
| loss differential | describes the actual event's mismatch | oriented residual | not reward or action selector |
| backpropagation | returns sensitivity through the path | adjoint consequence return | requires a declared differentiable world |
| optimizer | deforms future parameter conduct | developmental standing change | metric and update law are authored |
| recurrence/state space | folds past into a carried state | emitted compression | may erase relations not retained by its state |

The common core is **conditional transport under bounded capacity**. Modern architectures work by
predeclaring a carrier, grain, chronology, transformation family, memory factorization, residual,
and update law, then developing useful geometry inside that enclosure. Eros asks which of those
relations can instead arise through world events, live topology, completion, consequence, and
return. It need not pretend the engineered examples are irrelevant in order to remain distinct.

## VII. Policy correction

The current protection is refined to three separate judgments:

1. **Scientific comparison is admissible.** Tokenization, attention, experts, gradients,
   recurrence, and conventional training may be studied to determine the relations they actually
   implement.
2. **World and observer use is admissible.** A tokenizer, model, compiler, differentiable
   instrument, or learned transducer may be a lawful external constituent when its action and
   provenance are explicit.
3. **Primitive inheritance is not licensed.** No tokenizer, attention governor, scalar-loss
   governor, expert bank, optimizer, or canonical latent language enters Soma merely because the
   comparison is productive. An internal relation requires its own derivation from the live event
   lifecycle and a demonstrated need.

Accordingly, `no X inside Soma by analogy` must never again be shortened to `do not learn from X`.

## VIII. Consequence and proposed research direction

The broad literature pass is sufficient for orientation. The next useful work is not another
architecture survey and not an implementation. It is a read-only comparative audit of the engine
and prior worlds asking:

1. where the existing machine already chooses or receives grain;
2. where it forms conditional transport and local transformation;
3. what persists only for an event, across an episode, or in durable Standing;
4. which observations actually demonstrate history-conditioned later conduct;
5. whether returned residual or material consequence altered the later contact law; and
6. whether the repeatedly missing nonidentical correspondence is absent from Soma, absent from
   the world ecology, or merely presented at the wrong grain.

Only the smallest unresolved relation discovered by that audit should trigger targeted external
research. Likely research families are dynamic grain formation, continual credit assignment,
sparse conditional computation, recurrent memory consolidation, and developmental curricula, but
none is scheduled or presumed necessary by this record.

The cached developmental-kernel question remains open in a sharper form:

> What lawful return, persistence, and deformation—if any—must supplement the current receiving
> law so that ordinary experience grows useful correspondence between later nonidentical
> structures?

## IX. Primary literature used

- Sennrich, Haddow, and Birch, [subword units and BPE](https://arxiv.org/abs/1508.07909).
- Kudo and Richardson, [SentencePiece](https://arxiv.org/abs/1808.06226).
- Cognetta and Okazaki, [tokenization as finite-state transduction](https://aclanthology.org/2025.cl-4.2/).
- Schmidt et al., [Tokenization Is More Than Compression](https://aclanthology.org/2024.emnlp-main.40/).
- Pagnoni et al., [Byte Latent Transformer](https://arxiv.org/abs/2412.09871).
- Vaswani et al., [Attention Is All You Need](https://papers.neurips.cc/paper/7181-attention-is-all-you-need.pdf).
- Su et al., [Rotary Position Embedding](https://arxiv.org/abs/2104.09864).
- Geva et al., [feed-forward layers as key-value memories](https://aclanthology.org/2021.emnlp-main.446/).
- Elhage et al., [Toy Models of Superposition](https://transformer-circuits.pub/2022/toy_model/index.html).
- Singh et al., [induction heads in controlled in-context learning](https://proceedings.mlr.press/v235/singh24c.html).
- Olsson et al., [induction heads and in-context learning](https://arxiv.org/abs/2209.11895).
- Shazeer et al., [sparsely-gated mixture of experts](https://arxiv.org/abs/1701.06538).
- Fedus, Zoph, and Shazeer, [Switch Transformers](https://www.jmlr.org/beta/papers/v23/21-0998.html).
- Dai et al., [DeepSeekMoE](https://arxiv.org/abs/2401.06066).
- Gu and Dao, [Mamba](https://arxiv.org/abs/2312.00752).
- Dao and Gu, [structured state-space duality / Mamba-2](https://arxiv.org/abs/2405.21060).
- Delétang et al., [Language Modeling Is Compression](https://arxiv.org/abs/2309.10668).
- Kimi Team, [Attention Residuals](https://arxiv.org/abs/2603.15031).
- Kimi Team, [Delta Attention Residuals](https://arxiv.org/abs/2605.18855).
- Anthropic, [On the Biology of a Large Language Model](https://transformer-circuits.pub/2025/attribution-graphs/biology.html).
