# DeepSeek V4.1: shared standing, contact and contextual transformation

[definition] This is Brandon's September 10 requested architecture study, alongside the continuing
AC session. It contributes a source comparison, explicit maps and bounded separating witnesses.
It does not revise the AC order, replace its active implementation, or claim a native V4.1 adapter.

## Sources and authority

[established-bounded; source-inspected] Read the official [DeepSeek-V4.1-Flash technical
report](https://huggingface.co/deepseek-ai/DeepSeek-V4.1-Flash/blob/main/DeepSeek_V41_Tech_Report.pdf),
especially §§2–3, §4.2 and §6; visually inspected the CED, CSA2 and mHC equation/diagram pages.
The downloaded 51-page PDF reports creation September 10 05:49:49 UTC. Its SHA-256 is
`ba68e2e40408125ae6d2f63a9a241b61c73910691c74ec1a2a7023c851eac08d`.
The contemporaneously retrieved official model API reports revision
`dba1be0a40aa45a94ad051997016db3960a90277`, created September 10 02:17:58 UTC.
The hash identifies this exterior source file, not model identity or semantic authority.
The report's experimental results below are author-reported testimony, not independent replication.

[established-bounded; source-inspected] Recovered the prior [architecture
review](2026-09-09_ARCHITECTURE_CHARTS_REQUIRE_COMPOSED_MECHANISMS_AND_FINITE_CONSTRUCTION_RETURNS.md),
August 18 [architecture](2026-08-18_THE_ARCHITECTURE_IS_A_DOMAIN_ACTION_THE_GAUGE_CARRIES_THE_SECTION_AND_THE_COARSENING_OWES_ITS_FIBRE.md)
and [plural-future/normalization research](2026-08-18_THE_FUTURE_IS_A_PLURAL_CAUSAL_SECTION_SOFTMAX_IS_ITS_LOCAL_LAPLACIAN_AND_THE_ADJOINT_RETURNS_THROUGH_STATE.md),
and revisited [Attention Is All You Need, §3](https://arxiv.org/html/1706.03762v7).
The latter describes learned query/key compatibility, transported values, multiple heads, residual
standing and position-wise nonlinear transformations. Attention is one component of its Transformer.

[established-bounded; source-inspected] Direct user messages were recovered from
`~/.codex/sessions/2026/09/06/rollout-2026-09-06T13-59-42-01a07885-13f1-7351-b539-996e18049602.jsonl`:
September 10 UTC, lines 33668 (00:32), 34008 (00:57), 35341 (03:35), 35430 (03:46),
and 35632 (04:39). Paraphrased: recover classical mechanisms and commuting maps; transport Holons
across media; identify elementary excitation; replace the historical-source/byte construction with
productive generators; repair and continue. The latest request asks for this separate study.
Private raw logs are not deposited. Current canon, retractions and the complete roadmap were read.

[established-bounded; source-inspected] Repository inspection began at
`afe0ff046c18c71aa64a98529057e21f23d263b7`. The parallel worktree already modified the normal-wave
owners and blueprint and contained untracked `wave/develop.rs` and
`crates/holonics-hna/examples/conversation_wave.rs`. Their inspected behavior is explicitly
work-in-progress testimony. This review changes no native source and runs no CUDA workload.

## What DeepSeek actually changed

[established-bounded; source-inspected] The following rows summarize the report, at its own scope.
Its improvements combine architecture, training and deployment choices; aggregate benchmark gains
do not isolate the causal contribution of each component.

| Component | Actual operation | Architectural consequence |
|---|---|---|
| Causal encoder–decoder, §2.2 | Twenty causal encoder layers produce hidden states; decoder global KV is projected from those states. Twenty decoder layers retain their own local SWA computations. | Most prompt positions need only encoder processing plus global projections. Decoder local-state reconstruction remains additional work. This is a causal language-model split, unlike a bidirectional translation encoder. |
| CSA2, §§2.3–2.3.1 | Full creates global KV/indexer keys and indices. Reindex shares those KV/keys but selects again with a new indexer query. Reuse shares KV and the latest selected indices. | All three modes still compute fresh main queries, local SWA KV and attention outputs. Reuse does not mean copying a previous response. |
| Layer arrangement, Figure 3 and §4.2.1 | Encoder: two SWA layers, then three groups of Full + five Reuse, at compression ratio 2. Decoder: Full + three Reuse, then four groups of Reindex + three Reuse, at ratio 1. | Forty blocks have four global KV-producing layers. Decoder global KV is shared across all twenty decoder layers and remains uncompressed along the sequence axis. |
| Hierarchical indexer, §2.3.2 | The first decoder indexer scans all visible positions, selects its own top 512 and builds a pool of up to 16,384 positions using block maxima. Four later indexers select within that pool. | Later searches are bounded for fixed pool size; the initial scan still grows with context. Modes and pool restriction are trained architectural choices, not proven causal irrelevance. |
| MoE, §4.2.1 | Each block combines one shared expert and six selected from 384 routed nonlinear experts. | Contact selects information; expert transformations change its representation. These are different computational roles. |
| Single-Pass mHC, §2.4.1 | Four residual streams; input mixing uses the preceding block's coefficients, while current standing produces coefficients for subsequent use. | Changing a dependency enables fused resident execution. It is a modified learned recurrence, not an algebraically identical scheduling of the old mHC. |
| Engram, §2.4.2 | Two modules provide 196B parameters in hashed 2/3/4-gram embedding tables, with context-aware integration. Deterministic addresses permit prefetch. | Conditional memory supplies material for further computation. A retrieved embedding is not a stored final answer or an identified semantic object. |
| DSpark, §2.4.3 | Three draft blocks produce five positions; a Markov head models their dependence and a confidence head helps schedule verification. | Parallel proposal retains inter-position dependence; throughput scheduling is distinct from the backbone's response law. |
| Quantization and bounded replay, §§2.4.4, 3.2 | Main KV uses roughly four bits plus scales; SWA remains FP8. Missing SWA state is reconstructed from a shortened replay. | Precision and replay deliberately change states. The report explicitly says suffix states can depend on cache-hit position. |

[established-bounded; source-inspected] DeepSeek reports 552B backbone parameters plus 196B Engram
parameters, with 8B activated during prefill and 16B during decode. It reports 890 global KV bytes
per token, approximately one-quarter V4-Flash global cache, and approximately one-eighth persistent
cache under its deployment comparison. These numbers do not mean an 8B-resident consumer model,
constant total context memory, or a demonstrated energy saving on Brandon's machine.
The 45T-token pretraining and subsequent training also matter to its resulting usefulness.
Section 6 explicitly retains sparse-selection and approximate-reconstruction robustness limits.

## Transformation as situated difference

[definition] Use Brandon's broad sense of transformation: a caused input/output passage whose
difference is read in context. Write the complete operation as

```text
T : (Athena_t, occurrence_t) -> (emission_t, Athena_(t+1)).
Athena_t includes current, constitutive material, incidence, conditions and chronology.
```

An input and an output need not have the same type. Their comparison therefore retains explicit
source/receiver charts and joining relation, rather than assuming that subtracting token numbers
defines their difference. In a common additive chart, a residual expression is valid. Eros names
composition/development of this operation; Athena names its particular continuing body. Eros is
not DeepSeek's encoder and Athena is not its decoder. Encoding and response formation can both
occur within the same HNN operation.

[definition] Four maps make this account operational: how an occurrence excites situated current;
how current and standing jointly determine contact and reaction; how the resulting section reaches
the receiver; and how an actual observed difference changes later reusable conduct. The next
operation consumes that complete successor. Calling all four maps a transformer leaves their
construction unspecified.

[proved-derived] Attention exposes two independently important changes. On a common finite
admitted population, let `a = sum_j alpha_j v_j` and `a' = sum_j alpha'_j v'_j`. Adding and
subtracting `sum_j alpha'_j v_j` gives the exact finite identity

```text
a' - a = sum_j alpha'_j (v'_j - v_j) + sum_j (alpha'_j - alpha_j) v_j.
```

The first term changes the transported material; the second changes its participation. For
different sparse supports use their union and extend absent weights by zero. This finite identity
still holds at a top-k switch, where a differential description may fail.

[proved-derived] On a differentiable fixed-support chart with
`alpha_j = exp(s_j) / sum_k exp(s_k)`, differentiating the quotient gives
`d alpha_j = alpha_j (d s_j - sum_k alpha_k d s_k)`. Substitution yields

```text
d a = sum_j alpha_j d v_j + sum_j alpha_j (v_j - a) d s_j.
```

For dot-product scores, `d s_j = (k_j · d q + q · d k_j)/sqrt(d_k)` at fixed dimension.
Even with unchanged stored keys/values and unchanged selected population, a changed query can
change the response. The complete return through that attention map includes its participation
term; updating only a value map does not differentiate the same map. This is not a demand that
all HNN learning implement full backpropagation.

[established-bounded; source-inspected] Existing formal owners already cover relevant pieces:
`HolonicArchitectureCharts.AttentionChart.{weight,output,ecology_step_eq_output}` and
`AttentionChart.Block.ecology_step_eq_output` bind normalized contact and standing/reaction.
`HolonicAdjointNormalization.NormalizedExponential` carries common-shift invariance,
`laplacianReturn`, zero total return and the weighted-variance identity. Its algebraic Laplacian
results must not be misreported as a newly kernel-checked derivative of every V4.1 component.
The differential calculation above is a displayed derivation, not a new Lean build.

## The analogous native construction

[interpretation] The useful correspondence has three separate objects: reusable material,
the current applicable interaction population, and the current response. Their maps are:

```text
source occurrence --existing source chart--> excitation s
current native standing ------------------> condition c
(s,c) --admitted interaction--> joined current --local law/reaction--> response
observed comparison --producing relation return--> changed material + successor standing
```

The intended preserved diagram is the existing native/chart operation square, on complete
successors when continuation is claimed. Its first derivation target is a finite conditional
interaction that changes the response under changed actual standing while reusing the same law.
Its falsifier is a pair of admitted conditions that the chosen source map collapses but a required
future receiver separates. Limits: this correspondence alone neither implements adaptive routing
nor establishes a conversation learner or a DeepSeek-equivalent native operator.

[established-bounded; source-inspected] The necessary starting owners already exist:

| Needed role | Existing owner | Actual boundary |
|---|---|---|
| Joint source/condition dependence | `ResidentConstitutiveFibre` bilinear contact, with source, condition and their complex product | A local admitted relation, not universal semantic context |
| Shared standing and observation-founded change | `resident/neighborhood.rs::ResidentGeneratorNeighborhood` | `read` and `advance` receive a caller-selected member; shared condition does not itself discover incidence or implement an MoE router |
| Whole-family continuation | Constitutive image/preimage and condition-contact owners | Preserve joint correlation and admitted domain; arbitrary nonlinear family image is not inferred |
| Reusable local response | `ResidentNormalMaterial` and `ResidentNormalWave` | The current source plane and response law have the limited expressivity analyzed below |
| Nonlinear local computation and returned factors | Full-operator `Contract`, `CausalContact`, `Hadamard`, `Add`, nonlinear/rebase primitives and operative return | Supported source graph and artifact dependencies remain; these are not automatically plugged into the new conversation body |
| Reuse of an actual numerical passage | `holonic_intelligence/operative_reuse.rs::NativeForwardReuse` | Complete segments, producing origins and dependency reopening; it does not skip the contemporary developmental occurrence |
| Consequence-based reduction | `receiver_history_compression/observable.rs::ObservableMomentReceiverHistoryCompression::found` | Closes quadratic receiver forms under admitted generator pullbacks and retains the kernel; exterior exact construction is not a resident arbitrary-nonlinear compiler |

[interpretation] CED suggests amortizing source processing into a native section that multiple
different responses can use. That section must preserve the distinctions those responses need.
An active conversation state, a learned reusable law and an archived conversation are different
objects. Current-state retention is necessary where it carries future effects; deleting all
transient standing would not implement generator compression. A mandatory record of every
past occurrence is equally unnecessary. The applicable receiver family determines the distinction.

[interpretation] CSA2 suggests sharing a law/section without freezing its use. The corresponding
native operation can re-evaluate interaction under changed current while retaining the producing
material. Reusing the same interaction population can still permit fresh local reaction. Learned
sharing and memoization differ: tying two maps is an architectural hypothesis trained as such;
memoizing a computation requires unchanged dependencies; a quotient requires preserved declared
future consequences. None follows merely from matching dimensions or equal observed faces.

[conditional] If shared material `M` contributes to outputs through maps `f_l(M)`, then for a
smooth scalar comparison its covector return is `sum_l (D f_l(M))* lambda_l`, including every
participating consumer. This follows by differentiating the fan-out composition. Shared storage
does not justify returning only through its first use. It is the return-side consequence of reuse,
already consistent with the producing-morphology and staged-publication rules.

[interpretation] Hierarchical selection suggests using coarse receiver information to locate
potentially participating fine regions, then refining within them. The candidate population and
the actual interaction are distinct. A receiver-bound approximation may omit some effects with
an explicit remainder; a hard relevance score does not establish their causal absence. Changed
receiver/conditions can reopen the population. This is a comparison for the existing incidence,
restriction and scale owners, not permission to install a semantic classifier.

[interpretation] Engram supplies a useful separation between remembered material and computation
over it. The native counterpart is rested conditional transport, as already described by hexis.
A token hash is an exterior storage address, not a Holon identity. Importing n-gram lookup as the
interior contextual mechanism would repeat the lexical-atlas error. Conversely, that error is no
reason to prohibit a legitimate exterior address from locating native material.

[interpretation] mHC connects retained standing, conditional mixing and response in one continuing
map. Its practical lesson is to account for material dependencies and resident memory traffic.
Moving a coefficient to a previous cut changes a law; it needs its own return comparison.
DSpark suggests evaluating several compatible future positions together. HNN already has joint
future-family constructions; multiplying separate marginal possibilities would lose their joins.
Speculative execution, if later implemented, must stage differences under one owner and commit only
the admitted successor. Confidence scheduling neither defines truth nor adds a certainty gate to
ordinary generation.

## A precise limit of the current conversation source map

[established-bounded; source-inspected] The inspected `SymbolCurrentChart` maps exterior symbols
to unit basis currents. `conversation_wave.rs` constructs local section comparisons
`x_j = (c_j-c_(j-1), c_j, c_(j-1))`, `y_j = c_(j+1)-c_j`, then develops the same normal material.
The source occurrence sections can depart. `develop_section` changes material while retaining
the actual generative pair; it does not assert that unrelated message boundaries are adjacent.
The implementation therefore supplies useful local-law development and honest provenance.
It does not mount the neighborhood's bilinear condition interaction into this source map.

[proved-derived] At fixed ideal material, write the linear response as
`R(x) = W_delta x_delta + W_c x_c + W_p x_p`. The joined normal-wave recurrence is

```text
p_next = c
c_next = c + R(c-p,c,p)
       = (I + W_delta + W_c)c + (W_p - W_delta)p.
```

Thus this fixed-material source attachment is a linear recurrence on `(p,c)`. Composing its
operator powers does not introduce products between independent current components. State or
material changes and nonlinear exterior feedback have their separate effects; this statement
does not classify the entire developing HNN as linear. An expressive contextual source supplied
to a linear readout could change the conclusion about the complete input/output map.

[counterexample; computational-witness] The ideal normal sufficient statistics
`H = I + sum x_j x_j*`, `B = sum y_j x_j*`, target energy, observation count and initial pair
are identical for the two binary-symbol source sections `000100` and `001000`. Both contain exactly
the local triples `000`, `001`, `010`, `100`, once each, and begin with `00`. Consequently the
unique ridge-normal map `B H^-1`, seed and every ideal fixed-material continuation are identical.
Yet the third-symbol receiver separates the original sources. This refutes sufficiency of this
compression for that receiver; it does not require all models to reproduce a past source.
No native wire-equivalence or CUDA numerical-reordering claim was tested here.

[proved-derived] The collision follows directly from equality of the summand populations; it is
not a precision problem. More accurate fitting of those same moments cannot recover the lost
distinction. If a future task needs that distinction, a contextual state/source interaction must
retain it before the quotient, or the quotient must retain the corresponding unresolved family.
The same issue can occur in acoustic or image charts that aggregate locally equal patterns while
discarding relevant larger arrangement. It is not a UTF-8-specific defect.

[interpretation] The productive continuation of AC is therefore composition of learned local
laws with actual conditioned standing and interactions, measuring what each composition adds.
The relevant comparison is whether identical exterior source faces under different caused
conditions yield appropriately different internal currents and later responses, and whether
transporting both source and conditions preserves the declared relation. Increasing the stencil
length alone supplies no such law. This is the already-authorized contextual attachment question,
not a replacement AC campaign, a demand for all-history differentiation or a new benchmark gate.

## Reuse with an honest future difference

[proved-derived] A zero present receiver difference does not license future reuse: with receiver
`r(x,y)=x`, states `(0,0)` and `(0,1)` agree now, but the generator `(x,y)->(y,x)` separates them
after one step. The exact exterior witness returns this example. It explains why the existing
observable owner closes receiver forms under generator action instead of comparing only the
current output. The dropped coordinate need not be raw history; it can be a compact latent mode.

[conditional] For a projected continuation satisfying a declared local defect bound `delta_t`
and receiver-chart Lipschitz bound `L_t`, the existing changing-receiver composition law gives
`e_(t+1) <= delta_t + L_t e_t`. Iteration yields

```text
e_n <= (product_(t=0..n-1) L_t)e_0
       + sum_(k=0..n-1) delta_k product_(t=k+1..n-1) L_t.
```

This follows by induction. It is useful when its hypotheses are available and its receiver asks
the relevant question; it is not an assumed stability guarantee for arbitrary language dynamics.
The full defect/fibre remains prior to the scalar bound. DeepSeek's reported small replay effect
is empirical testimony; it supplies neither this bound nor exact restart for HNN. Holonics can
use bounded approximations without mistaking them for exact invisibility.

## Returned verification and integration boundary

[established-bounded; computational-witness] Ran
`python3 research/experiments/2026-09-10-transformer-comparison/witness.py`; exit 0.
The [script](../experiments/2026-09-10-transformer-comparison/witness.py) and
[receipt](../experiments/2026-09-10-transformer-comparison/receipt.json) retain the exact local-map
collision, a fresh response on unchanged stored values/support, the two-term finite attention
difference and the future-separating hidden-coordinate example. Integer/rational calculations are
exterior apparatus, not a fixture learner or new native model. No Cargo, CUDA or Lean check is
claimed; their source was not changed by this review.

[definition] The [composition guide](../../docs/HNN_COMPOSITION.md) links this return. The parallel
session retains ownership of its current implementation and the roadmap retains construction
order. The useful result is an explicit distinction between retained material, current interaction,
local transformation and observation-founded development, with a concrete source-map obstruction
and existing owners to compose through it. Athena-alpha attainment remains unchanged.
