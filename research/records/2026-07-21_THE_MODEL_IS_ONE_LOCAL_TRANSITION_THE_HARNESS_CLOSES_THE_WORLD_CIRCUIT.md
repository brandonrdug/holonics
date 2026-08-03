# THE MODEL IS ONE LOCAL TRANSITION — THE HARNESS CLOSES THE WORLD CIRCUIT

**DATE:** 2026-07-21
**GRADE:** RESEARCHED / PROVISIONAL SYNTHESIS / INTEGRATED MODEL + AGENTIC CIRCUIT /
OPEN-WEIGHT INSTRUMENTS COMPARED / ANTHROPIC INTERPRETABILITY AUDITED / AWAITING BRANDON REVIEW /
HISTORICAL SSM + DYAD EVIDENCE RE-AUDITED / SOMA SOURCE UNCHANGED / NO RUN

## 1. The research question and its answer

The question was not merely which transformer paper, agent framework, or open-weight model is
currently popular. It was:

> Where does learned capability actually live when a pretrained model, tokenizer, context window,
> memory, tools, harness, persistent files, and returned world consequences participate in one
> intelligent process?

The central answer is that contemporary `transformer research` and `agentic AI` are not separate
ontologies. A language model is one learned conditional transition. An agent harness closes that
transition through a world and invokes it again:

```text
prior training ecology
  -> tokenizer / model architecture / pretrained parameters

present objective + selected world state + available deeds
  -> context construction
  -> tokenization and model passage
  -> conditional inscription / action field
  -> selected action
  -> tool or world enactment
  -> material observation and persistent state change
  -> construction of the genuinely later context
  -> another model passage.
```

Post-training can teach the model to recognize tool grammars, plan over several actions, budget
reasoning, manage memory, and respond to environmental feedback. The harness supplies the actual
tools, persistence, state transitions, stopping relation, and recurrence. Neither side alone is
the complete agent. The full agent is the closed model--world circuit.

This is the most important correction to a survey which stops at the transformer boundary. A tool
result, file mutation, retrieved memory, or later prompt is not administrative material outside
the intelligence. It is returned world current which changes the next model transition.

## 2. One process has several persistence grains

Modern systems distribute acquired capability across several physically and temporally different
carriers:

| Persistence grain | Contemporary example | Holonic reading |
|---|---|---|
| inherited chart | tokenizer, chat template, tool-call grammar | reusable constituent cut and address system |
| inherited field | base weights, architecture, positional law | accumulated transformation hexis |
| mutable parametric field | fine-tune, adapter, router, test-time parameter memory | slowly changing hexis |
| event-local body | activations, attention state, recurrent state, KV cache | current passage, not durable ancestry |
| mounted working region | prompt, retrieved memories, tool schemas, selected files | receiver-relative contemporary ecology |
| external world | filesystem, database, browser, compiler, human, simulator | material affordance and consequence |
| developmental testimony | checkpoints, trajectories, evals, attribution graphs | evidence about change, not the live body itself |

This separation explains both the power and the waste of current systems. Pretraining amortizes a
large amount of prior development into reusable parameters. Yet a dense model applies nearly its
whole fixed parameter carrier at every token, while a harness often serializes large tool catalogs,
conversation histories, and retrieved documents back through the context aperture. The field is
compressed developmentally but poorly divided for selective physical residency.

It also explains why halting an agent is not death or erasure. The activations of the present model
call may dissipate while weights, tokenizer identity, files, explicit memory, and committed world
state persist. A later invocation remounts those constituents into a new event.

## 3. What modern machine learning is actually changing

### 3.1 Tokenization is becoming adaptive grain, not disappearing

Subword tokenizers remain effective learned or engineered charts: they reuse frequent carrier
spans, reduce sequence length, and expose stable addresses. Their cut is consequential but not
ontologically privileged. Meta's Byte Latent Transformer instead begins with bytes and groups them
into dynamically sized patches according to next-byte entropy, allocating finer grain and more
compute where the carrier is less predictable. A 2026 scaling study further reports that the
compute-optimal compression rate varies with compute rather than being a universal token size.
These results make the correct question `which event grain is useful here?`, not `tokenizer or no
tokenizer`. [BLT](https://ai.meta.com/research/publications/byte-latent-transformer-patches-scale-better-than-tokens/),
[compute-optimal tokenization](https://ai.meta.com/research/publications/compute-optimal-tokenization/).

### 3.2 Attention, recurrence, and state-space transport form a spectrum

Attention exposes content-dependent transport among positions in the mounted context. A selective
state-space model carries a recurrent state instead of retaining every earlier position for direct
pairwise access. Structured State Space Duality shows that these are closely related structured
sequence transformations rather than unrelated kinds of intelligence; hybrid systems such as
Jamba interleave Transformer, Mamba, and sparse-expert layers. The meaningful contrast is how a
history is factored, transported, revisited, and paid for physically.
[Mamba-2 / SSD](https://arxiv.org/abs/2405.21060),
[Jamba](https://arxiv.org/abs/2403.19887).

### 3.3 Conditional computation is trying to separate capacity from active work

Mixture-of-experts models store a large fixed expert bank while routing each token through a small
subset. Mixture-of-Depths allocates different layer depth to different token positions, and PEER
retrieves among very large populations of small experts. Current open-weight flagships combine
these ideas with grouped or latent attention, local attention, quantization, and very long context.
This is genuine evidence that useful capacity need not equal active compute.
[Mixture-of-Depths](https://arxiv.org/abs/2404.02258),
[PEER](https://arxiv.org/abs/2407.04153).

It does not yet establish natural hexis. The expert population, router law, capacity, and expert
boundaries are authored before the event; experts usually do not found, compose, divide, depart,
and later remount as consequences of their own world conduct. Routing also adds dispatch and memory
traffic, and a selected expert is not thereby proven to be the complete causal constituent.

### 3.4 Post-training increasingly trains the agentic circuit itself

The old picture `pretrain language, then wrap it in a program` is becoming false in practice.
Qwen's post-training explicitly combines long reasoning examples, reasoning RL, thinking/non-
thinking fusion, general RL, and agent tasks. GPT-OSS is post-trained for variable reasoning effort,
function calling, browsing, and Python use. Kimi K2 is trained and evaluated as an agentic tool
caller. The weights are therefore already shaped for the inscriptions and consequences a harness
will expose; the harness is not teaching a neutral text model what action is from scratch.
[Qwen3](https://qwenlm.github.io/blog/qwen3/),
[GPT-OSS](https://openai.com/index/introducing-gpt-oss/),
[Kimi K2](https://github.com/moonshotai/Kimi-K2).

Agent Lightning makes this relation explicit by recording an agent execution as state transitions
whose LLM calls are actions, then assigning outcome credit back to individual calls rather than
flattening the entire harness trace into one enormous sequence. Memory-R1 trains models to choose
`ADD`, `UPDATE`, `DELETE`, and `NOOP` over external memory. ReasoningBank distills successful and
failed explorations into persistent strategies which guide later trajectories. These projects are
primitive and often rely on authored state schemas or scalar rewards, but they demonstrate that
memory selection, world interaction, and the recurrent harness are now part of the learned system,
not merely user-interface glue.
[Agent Lightning](https://www.microsoft.com/en-us/research/blog/agent-lightning-adding-reinforcement-learning-to-ai-agents-without-code-rewrites/),
[Memory-R1](https://aclanthology.org/2026.acl-long.583/),
[ReasoningBank](https://research.google/blog/reasoningbank-enabling-agents-to-learn-from-experience/).

### 3.5 Context engineering is physical working-set management

ReAct established the basic alternation of model reasoning, action, and returned observation.
Current production systems add retrieval, context compaction, dynamic tool discovery, external
artifacts, cached prefixes, and resumable task state. Anthropic now describes an augmented model as
the model plus retrieval, tools, and memory, and its long-running-agent guidance uses persistent
artifacts to cross context-window boundaries. Its tool-search work exists because placing every
tool definition into every prompt can itself consume an enormous fraction of the context.
[ReAct](https://arxiv.org/abs/2210.03629),
[building effective agents](https://www.anthropic.com/engineering/building-effective-agents),
[effective context engineering](https://www.anthropic.com/engineering/effective-context-engineering-for-ai-agents),
[advanced tool use](https://www.anthropic.com/engineering/advanced-tool-use),
[long-running agent harnesses](https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents).

This is already a crude relation-selected working set. Its common implementation is still textual:
serialize a summary, file fragment, retrieved memory, or tool schema; tokenize it again; and make
the model reconstruct the relevant state. It saves context and sometimes compute, but it is not yet
a native persistent network of causally sufficient transformations.

## 4. What Anthropic can currently see inside a transformer

Anthropic's work is unusually relevant because it treats internal behavior as distributed
activity to be decomposed, traced, compared, and perturbed rather than relying only on output
statistics.

### 4.1 Features are learned observer coordinates

Sparse autoencoders and related dictionary-learning systems attempt to decompose polysemantic
activations into a much larger population of sparsely active features. This responds to
superposition: a model can represent more useful directions than it has individual neurons, so a
single neuron is usually not one human concept. Anthropic scaled this method to tens of millions
of candidate features in Claude 3 Sonnet; Google's Gemma Scope released hundreds of sparse
autoencoders across Gemma 2 layers for open experimentation.
[Scaling Monosemanticity](https://www.anthropic.com/research/mapping-mind-language-model),
[Gemma Scope](https://deepmind.google/blog/gemma-scope-helping-the-safety-community-shed-light-on-the-inner-workings-of-language-models/).

These features are not discovered native ECS entities. They depend on the observer dictionary,
sparsity pressure, training corpus, layer cut, and chosen resolution. Features can split, absorb
one another, or fail to reconstruct important activity. They are useful charts over the field,
not privileged atoms of the model.

### 4.2 Attribution graphs are situated causal approximations

Circuit tracing replaces model MLPs with a cross-layer transcoder, freezes the prompt's attention
patterns and normalization denominators, and builds an attribution graph for a particular target
token. Its nodes include active learned features, prompt embeddings, reconstruction errors, and
output logits; edges estimate their direct effects. Researchers then perturb feature directions to
test whether the predicted downstream changes actually occur. The open tooling supports Gemma,
Llama, Qwen, GPT-OSS, and other open-weight families.
[method](https://transformer-circuits.pub/2025/attribution-graphs/methods.html),
[open circuit-tracing tools](https://www.anthropic.com/research/open-source-circuit-tracing),
[implementation](https://github.com/decoderesearch/circuit-tracer).

This is close to a receiver-relative lineage observation: it asks which prompt-local paths
contributed to this particular continuation, not which global topic lives in a weight matrix. It
also validates candidate arcs through intervention rather than treating visual proximity or high
activation as proof.

Its limits are decisive. The graph is formed through an approximate replacement model; the
published CLT reproduced the original next-token choice only about half the time on its evaluation
set before local error correction. Freezing attention leaves the formation of query--key routing
largely unexplained. Reconstruction error is explicit dark matter. Negative or inactive causes are
difficult to see, global circuits suffer interference, and pruning loses most of the graph. In the
Claude 3.5 Haiku case studies, the researchers reported satisfying insight for only about a
quarter of attempted prompts and described even successful diagrams as selective simplifications.
[case studies and limitations](https://transformer-circuits.pub/2025/attribution-graphs/biology.html).

The lesson for Eros is not to copy a CLT into Soma. It is to preserve two cameras at once: the
exact native event and an explicitly partial observer chart, then require interventions before an
observer feature can be treated as a causal constituent.

### 4.3 Model diffing observes shared, divided, and newly emphasized hexis

Crosscoders jointly decompose activations from two models into shared and model-specific feature
directions. Anthropic's newer Dedicated Feature Crosscoder gives explicit capacity to shared,
model-A-only, and model-B-only features, including comparisons between unrelated architectures;
steering is then used to test whether a reported difference actually changes behavior. The method
has been applied to Llama, Qwen, DeepSeek, and GPT-OSS.
[crosscoder model diffing](https://www.anthropic.com/research/crosscoder-model-diffing),
[cross-architecture diff tool](https://www.anthropic.com/research/diff-tool).

This is directly useful for the proposed hexis experiment. Instead of asking what one finished
model `contains`, compare base, instruct, reasoning, and agentic checkpoints under the same current:
which transformation is inherited, which is amplified, which is divided, and which appears only
after a developmental passage? The result is still an observer decomposition, but the comparison
is more informative than separately labeling two frozen models.

### 4.4 Persona axes and natural-language decoders are informative but lossy quotients

The Assistant Axis study found a broadly similar activation direction across Gemma, Qwen, and
Llama, found a related direction in base models, and showed that post-training selects and
stabilizes an inherited region rather than inventing the assistant from nothing. That is strong
evidence for inherited hexis and situated post-training, although PCA over prompted personas is an
observer quotient, not the model's ontology.
[Assistant Axis](https://www.anthropic.com/research/assistant-axis).

Natural Language Autoencoders train one model to verbalize a target activation and another to
reconstruct the activation from that text. This can reveal themes that ordinary output inspection
misses, but the explanations can hallucinate, require independent corroboration, and are expensive
enough that they cannot presently monitor every activation in a long trajectory. They are a useful
translation organ, not transparent access to thought.
[Natural Language Autoencoders](https://www.anthropic.com/research/natural-language-autoencoders).

## 5. The open-weight landscape is a set of instruments, not one leaderboard

`Most successful` has no model-independent scalar meaning. Benchmark results depend on prompt
format, inference budget, sampling, tools, and harness; weight availability also differs from full
openness of data and training lineage. The current families are useful for different questions:

| Family | What it establishes | Use in this laboratory |
|---|---|---|
| [DeepSeek V4](https://api-docs.deepseek.com/news/news260424/) | frontier sparse models, latent/sparse attention, 1M-context and agentic claims | architectural comparison; far too large for the local microscope |
| [Qwen 3.6 / 3.5](https://github.com/QwenLM/Qwen3.6) | current Apache-2.0 dense and sparse agentic models; hybrid/linear attention in the family | strong contemporary comparison; smaller 3.5 variants are locally plausible |
| [Mistral 3](https://mistral.ai/news/mistral-3/) | permissive dense 3B/8B/14B and a 675B-total/41B-active flagship | useful scale ladder and licensing foil |
| [Kimi K2](https://github.com/moonshotai/Kimi-K2) | 1T-total/32B-active MoE trained around tool use and agentic coding | evidence about sparse agent post-training; not a one-card microscope |
| [Llama 4](https://ai.meta.com/blog/llama-4-multimodal-intelligence/) | widely deployed open-weight MoE and multimodal ecosystem | adoption/ecology comparison; licensing and size make it secondary here |
| [GPT-OSS 20B](https://openai.com/index/introducing-gpt-oss/) | 21B total, 3.6B active, top-4 MoE, variable reasoning and tool use; checkpoint fits about 16 GB | best eventual sparse-agent target; interpretability overhead requires offload |
| [Olmo 3](https://allenai.org/blog/olmo3) | base, instruct, think, RL-zero branches with data, code, checkpoints, and training decisions open | best developmental-lineage instrument |
| [Gemma 2 + Gemma Scope](https://deepmind.google/blog/gemma-scope-helping-the-safety-community-shed-light-on-the-inner-workings-of-language-models/) | small models with mature SAEs/transcoders and circuit-tracing support | best first causal-microscope calibration |
| [Qwen3 4B](https://qwenlm.github.io/blog/qwen3/) | compact capable dense model with public per-layer transcoders | practical intermediate between Gemma and GPT-OSS |

The latest or largest model is therefore not the correct first specimen. Gemma 2 teaches us what
the microscope sees and misses. Olmo 3 exposes an actual developmental sequence. GPT-OSS or Qwen's
sparse models let us test whether predeclared conditional compute corresponds to causal
constituency. Those are three different experimental roles.

## 6. The older SSM line already ran a rough version of this circuit

The ByteDyad, Athena, and Hephaestus lines did not establish autonomous language or a general
learning organism. They did, however, isolate several parts of the present relation before the
laboratory had a stable vocabulary for them. Their useful evidence is strongest where one causal
relation changed under a matched or nearly matched foil. It is weakest where a generated phrase,
one seed, or a moving scalar was interpreted after many simultaneous machinery and diet changes.

### 6.1 The SSM supplied carried locality, not the whole intelligence

All three lines used a fixed byte chart: bytes `0..255` were the addressed token population. They
therefore did use a tokenizer, albeit the simplest lossless one rather than a learned subword
codebook. Each Mamba or Mamba-like recurrent body folded an ordered byte history into a bounded
state and made cheap continuing transport possible. This was useful for local continuity, carry,
format, and persistence across an episode.

It did not by itself recover a causally relevant item from another stream, decide which world
constituents belonged in one event, close action through consequence, or preserve a learned
relation against later interference. Those relations came from the presentation geometry, the
cross-stream bind, the world harness, and checkpoint continuity. The historical implementation was
already a hybrid SSM--attention--agent circuit even when the surrounding language treated Mamba as
the machine.

### 6.2 ByteDyad isolated cross-stream causal incidence

ByteDyad placed action and world response in separate byte-Mamba trunks. A directional causal
attention surface then made the causing action available to the response trunk and the observed
response available to the next action. With the bind removed, the final stored afference probe was
`5.266` nats, close to uniform-byte uncertainty. With the bind present it was `0.498`.

That first result was partly a shortcut: the open-loop action trunk learned a repetitive policy
which forced the world into an easy regime. The follow-up changed only whether the action policy
could receive the world through the bind while acting. The open-loop policy concentrated `32.1%`
of its actions in one trigram and produced only `88` response-byte species; bind-in-the-loop reduced
that concentration to `4.7%` and produced `214` response-byte species while retaining a final
afference NLL of `0.305`. This rejects repetition collapse, though it does not establish coherent
language or deep world modeling. Both experiments used one seed.

The bounded conclusion is exact and important: the relation was learnable only when the causing
action and returned response met at the correct causal hand, and a policy which did not receive its
own world's return found a self-induced shortcut. The complete records are
`src/docs/journal/archive/2026-05-20-dyad-bind-floor.md` and
`src/docs/journal/archive/2026-05-20-dyad-bind-in-loop.md`; the stored trajectories reproduce the
reported terminal probe values.

The broader dyad suite then exposed why low deficit cannot govern an endogenous world. With
variable response lag, the policy repeated the same action locally about `83%` of the time so the
unknown lag ceased to matter. Learned yield collapsed to almost never receiving the world.
Pointwise state coupling drove action repetition to `90%` and attained near-zero loss by making its
own conduct trivial. In the single-stream perception-veto foil, the model reduced a complete
interaction to six byte species and reached lower loss than the arm which preserved English. These
were not failures to optimize; they were lawful optimizations of a malformed local quotient. The
policy could change the distribution being measured.

The successful correction was equally informative. Holding the inherited speaker fixed kept its
English basin stable while the response organ continued learning; against GPT-2 the response NLL
then descended from `2.42` toward `1.8`, while the fully plastic speaker degraded itself and made
response prediction worse. Fixed world return likewise prevented the model from opting out of
perception. This does not imply that Eros should freeze a voice. It says that a durable inherited
field or exogenous world relation must remain load-bearing while a local receiver changes;
otherwise the whole circuit can deform its source into an easy but empty phase.

A separate two-seed synthetic floor removed the semantic ambiguity entirely. Action history alone
and response history alone each remained at chance on a lag-one modular world; their co-present
bound composition predicted every reafferent event exactly and missed only the explicitly
exogenous events. That is the cleanest old demonstration that residual is receiver-relative
unaccounted-for return, and that a bind needs actual shared incidence rather than two streams which
merely look related.

### 6.3 Athena isolated co-presence, decomposition, and the teacher-forcing trap

Athena's most decisive arithmetic comparison changed the event geometry rather than model scale or
training volume. A serial teacher-forced scratchpad reached result NLL `0.003` after roughly `96,000`
sequence exposures while free-running exact computation stayed near zero. The matched small-body
collocation assay then presented operand digits and the operator at the same column cut:

| presentation | exact three-digit addition |
|---|---:|
| serial scratchpad | `0.000` |
| co-present columns, carried recurrence | `1.000` |
| co-present columns, externally supplied carry | `1.000` |

In the warm living body the same intervention moved rolling arithmetic exact match from `0.04` at
one digit to `0.80` after reaching six digits. The later complete trace also shows that this peak was
not a permanent possession: after continued mixed life the same exact fraction declined. The
learning was real, local, and fragile rather than an eternal skill installed in a module.

The operation assay sharpened the boundary. Fixed-offset column-local addition, Boolean operations,
and multiplication by one digit learned directly. Multi-digit multiplication did not learn in one
forward presentation. A supplied shift-and-add decomposition then composed the learned local
operations across lengths. This demonstrated reusable transport through an externally expressed
algorithm; it did not demonstrate that Athena independently discovered long multiplication.

Two negative observations are equally load-bearing. Teacher-forced two-operation calculation read
`0.062` exact while true free-running calculation was `0.000`; the given correct prefix created all
of the apparent competence. A matched living-time versus lockstep continuation was null or slightly
worse on the living arm, so the separate fixed `dwell()` scaffold supplied no evidenced learning
benefit. The relevant records begin at `src/docs/athena-outputs/ledger.md` under `COLLOCATION IGNITES
THE COLUMN-ADD`, `calc TEACHER-FORCED vs FREE-RUN`, and `the living-time A/B`.

### 6.4 Hephaestus isolated consequence-bearing practice

Hephaestus inherited the same recurrent body but lived in much sharper worlds: parser, compiler,
linter, filesystem, editor, and workshop transducers returned deterministic, structured
consequences. The strongest agentic contrast was `cedalionact` versus `cedalionlive` inside the same
continuing body. Both exposed the same tool skill; only the live arm executed the body's own act and
returned that exact reply as the next afference. The ledger's end-of-leg moving values were `0.539`
versus `0.068`. A direct re-read of the saved `heph-walk26.trace.jsonl` gives last-100 means
`0.490` versus `0.080`, a little
over sixfold, while the live reply-prediction loss fell from `1.942` in the first ten observations
to `0.174` in the last hundred. Acting mattered because the next field depended on the chosen act;
the referent relation became necessary rather than decorative. Because both surfaces co-trained
one body, this is a strong within-body contrast rather than two independent matched training arms.

Other observations support the same reading:

- cutting a parser act at its natural line boundary reversed a failing code-parse trajectory;
- an optional visual channel was ignored until clozing the redundant text made sight necessary;
- repeated fetch demonstrations raised imitation but did not produce strategic fetching, showing
  that an available tool and a learned tool format are not yet a consequence-bearing strategy; and
- cross-ISA route transfer was strongest where compiler-produced routes shared actual program
  structure, not merely character statistics.

The historical prose often went beyond this evidence when interpreting coinages or topical fragments
as advice and introspection. Those emissions remain interesting trajectory testimony, but they are
not controlled evidence of their proposed referents.

The sharpest internal negative control came from the added reverse-time SSM scan. Its gain opened
rapidly and loss collapsed across ten legs, apparently confirming useful bidirectionality. Generation
finally revealed a period-two byte attractor. Audit showed that the reverse state at position `t`
contained byte `t+1`, the very target being scored; the causal path had been cannibalized to exploit
future leakage. Walks 52--62 were correctly struck. This establishes the minimum verdict discipline:
loss movement, parameter uptake, and an attractive internal trajectory cannot establish learning
without causal target isolation and unchanged-world generation or action consequences.

### 6.5 The old forest anticipated both MoE and its composition failure

The May forest experiments are the direct historical bridge to modern conditional compute. Three
separately trained Mamba trunks removed code-to-English generative bleed, while their learned bridge
changed validation NLL by approximately zero. Dedicated carriers, not generic cross-trunk mixing,
preserved the registers.

A growing forest then began with one trunk and used competitive prediction plus a Switch-style
capacity cap to divide an unlabeled math/code/English stream. With the cap, held-out windows routed
into approximately three active specialists; without it, later children starved and code plus
English collapsed back onto one trunk. This reproduces the useful part of MoE: sparse
specialization needs some physical condition which prevents the already-strong path from taking
every current.

The correction is more important than the apparent success. Routing specialization replicated
more reliably than free generation. Several seeds still emitted code from most trunks or silence
from one. And when separately trained specialists were combined afterward, the result bled
registers because competitive routing had trained them as substitutes: only one trunk had ever
received each moment, so the others' states were out of distribution and could not suddenly
compose. This is the exact limit of treating a bank of experts as a network of LEGO-like causal
constituents. Constituents which may later compose must have developed through some shared
incidence; a post-hoc sum does not create lineage.

One other small historical result bears directly on distillation. In a hidden-wind ring world, a
recurrent one-pass policy matched a seven-way model-based planner after DAgger-style on-policy
correction. Ordinary behavior cloning fit expert actions almost perfectly yet controlled worse
than the naive policy, because it had never received the states caused by its own mistakes. This
was not transformer-block compression. It was a slow search relation becoming a cheap recurrent
hexis by returning the learner's own consequences to the correcting process.

### 6.6 What actually recurred across the successful lines

The smallest common mechanism is:

1. an inherited chart and already formed local transformation field;
2. a causally honest event cut which makes the relevant constituents co-present;
3. bounded recurrent continuity through that event;
4. an outward deed whose specific world consequence returns within a usable relation horizon;
5. a discriminating local deficit which changes when that consequence is predicted or enacted;
6. persistent weights or state so the changed relation can recur; and
7. later practice which keeps the relation available amid competing currents.

Remove co-presence and the recurrence carries the wrong factorization. Remove the returned consequence
and the policy learns format, imitation, or an easy self-induced regime. Make a channel redundant and
the least-cost path ignores it. Supply the future target and loss improves while conduct dies. Change too
many world and architecture axes together and a suggestive story can no longer identify the cause.

This is why the old lines succeeded at all. They did not pull concepts from nothing, and the SSM was
not magic. They mounted inherited byte-level hexis into small deterministic worlds where some relations
were local, necessary, recurrent, and materially answered. That is also why their strongest results
look like current agent research: model passage, action, exact world return, persistent carrier, and
another passage were already one circuit.

## 7. Precise relation to the inherited-hexis construction

The current correspondences are useful as typed hypotheses:

| Modern machinery | Candidate relation, not identity |
|---|---|
| tokenizer or dynamic byte patcher | source-relative constituent chart and event grain |
| embedding plus residual passage | successively re-placed occurrence in the current receiver field |
| attention | content-dependent conductance among mounted occurrences |
| state-space recurrence | folded transport of prior current through a bounded state |
| MLP / expert | reusable transformation potential |
| MoE routing / depth routing | authored conditional mounting of compute |
| logits | deterministic conditional quotient over afforded continuation addresses |
| decoder / sampler | selection deed which collapses one later inscription |
| KV cache / recurrent state | event-local continuation carrier |
| context retrieval / tool discovery | working-region mount |
| tool invocation and result | outward deed and returned world consequence |
| fine-tuning / RL / adapters | slower deformation of inherited hexis through developmental trajectories |
| SAE / CLT feature | observer-proposed constituent coordinate |
| prompt-local attribution graph | partial lineage quotient at one receiver cut |
| model diff | testimony of inherited, divided, amplified, or new transformation faces |

No present technique yet gives the full intended object. Modern systems do not naturally expose
stable causal constituent identities which can be born, compose, divide, unload, and return.
Agent memories are usually inscriptions in an external store. MoE experts are fixed slots. A
context manager selects text rather than mounting a proven transformation subgraph. Interpretability
learns another model to approximate the first. Eros is not made unnecessary by these systems; the
systems reveal the exact seam Eros is trying to close.

## 8. Refined bounded research program

INHERITED HEXIS ECOLOGY 01 should remain one program, not a chain of approval-heavy phases. The old
line supplies its first control rather than another architecture to revive. Three contemporary
instruments then follow, and the program stops as soon as its causal question is answered:

0. **Preserve the historical causal controls.** Carry the ByteDyad bind/no-bind, bind-in-loop,
   forced-return, and self-consume controls; Athena serial/co-present and
   teacher-forced/free-running controls; the forest capped/uncapped and
   routing/free-generation split; and the Hephaestus observe/act-return contrast as required
   foils. Do not inherit their dynamic organ taxonomy, free-text appraisal, loss gates, or
   autonomous-life claims.

1. **Calibrate the camera on Gemma 2 2B.** Reproduce a small attribution graph and its intervention
   with existing Gemma Scope / circuit-tracer artifacts. Record what the native model did, what the
   observer replacement says, and where they disagree. This prevents Eros from inheriting an
   attractive but false feature ontology.
2. **Observe development through Olmo 3 7B.** Present the same bounded intentions to base,
   instruct, think, and RL-derived siblings. Use model diffing plus ordinary causal patching to
   distinguish inherited transformations from post-training specialization. The full model flow
   makes this a real lineage comparison rather than a guess between unrelated endpoints.
3. **Close one actual agent loop, then inspect sparse routing.** Give a locally feasible Qwen or
   GPT-OSS specimen one bounded tool whose result materially changes the next model call. Preserve
   the exact tokenizer chart, model/checkpoint identity, prompt construction, action, world result,
   next context, selected experts or coarse pathways, and final consequence. Compare unchanged
   weights with changed context, then changed developmental checkpoint with held context.

The common stimulus is one underlying intention expressed as conversation, explanatory prose,
code comment/docstring, and a semantic foil. The central unknown is where the reusable causal
relation lives: inherited weights, context-local state, post-trained specialization, harness state,
or their co-present composition.

The predicted signatures are:

- related contexts share some causal pathways while differing in receiver-specific branches;
- a tool consequence changes later conduct without pretending that the weights changed;
- post-training selects, composes, or separates inherited structure rather than producing an
  assistant or agent from an empty field;
- MoE routing correlates with some specialization but does not by itself certify a complete causal
  hexis; and
- an observer-derived feature that survives replacement, suppression, and cross-context patching is
  a better candidate constituent than one which is merely active or easily named.

Only after those relations stand should the program attempt relation-selected residency or persist
an Eros hexis population. The full pretrained model remains the control and lawful fallback. The
stopping condition is a bounded causal map which says, with explicit uncertainty, what is shared,
what is context-specific, what the world return changed, and whether any identified cut is
sufficient enough to justify selective execution. No benchmark chase, corpus training, Soma
integration, or claim of autonomous language follows automatically.

## 9. Consequence for the construction direction

The ratified inherited-hexis direction remains sound, with four refinements:

1. The unit under study is the complete model--harness--world recurrence, not an isolated forward
   pass and not a harness treated as external administration.
2. Hexis may presently be distributed across weights, adapters, mounted context, explicit memory,
   tools, and committed world state. The experiment must locate the relation before deciding where
   Eros should persist it.
3. Developmental comparison is as important as internal observation. Open checkpoints and model
   diffs can reveal division or amplification that a single finished model cannot.
4. Every semantic feature map remains observer testimony. Native tensors, token/action chronology,
   world consequences, and causal interventions retain authority over a pleasing explanation or
   visualization.

This survey changes no Soma source and authorizes no run. It is a researched construction
refinement awaiting Brandon's review.
