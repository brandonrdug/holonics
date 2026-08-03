#import "@preview/unequivocal-ams:0.1.2": theorem, proof
#import "../lib/holonics.typ": *

#let learning = [
#pagebreak(weak: true)
= J3. Learning, inherited ecology, and modern ML <j3>

#local-contents((
  ([Persistence classes are not one memory], <j3-persistence>),
  ([A network is one factorization], <j3-factorization>),
  ([Exact inherited law after source departure], <j3-inherited-law>),
  ([Contextual factorization and its boundary], <j3-context>),
  ([Cultivation: changed later conduct and interference], <j3-cultivation>),
  ([Completion into a local transformation], <j3-completion>),
  ([Partial translation atlas], <j3-atlas>),
  ([Parent-on-OPEN substitution], <j3-parent-open>),
  ([Probability, loss, and learning], <j3-loss>),
))

Modern machine learning supplies lawful inherited technology: tokenizers, embeddings, trained
weights, attention, parsers, optimizers, and datasets may enter as Current or Standing when their
source and role are declared. The scientific task is not to pretend they are absent. It is to
distinguish what was inherited, what the event formed, what later stood, and what later conduct
changed.

== Persistence classes are not one memory <j3-persistence>

A tokenizer is a boundary chart
$
  T_tau:C -> V^*
$
which segments an ordered carrier and emits codebook addresses. A token is neither a word nor a
semantic atom. The chart chooses grain, chronology length, adjacency, and computational cost
before learned conduct begins.

For one scaled dot-product attention receiver,
$
  kappa_(i,j)=exp((q_i dot k_j)/sqrt(d)),
  quad
  alpha_(i,j)=kappa_(i,j)/(sum_m kappa_(i,m)),
$
$
  o_i=sum_j alpha_(i,j) v_j.
$
Query and key expose contact; value carries what crosses; softmax normalizes the admitted local
population. The weights are deterministic receiver quotients, not truth probabilities. Causal
masking is an authored chronology boundary. A key/value cache is episode state, not trained
Standing or complete lineage.

#proposition[
  If the values $v_1,...,v_n$ lie in a real affine space, then the softmax output $o_i$ lies in
  their convex hull. It has unique barycentric coordinates exactly when the admitted values are
  affinely independent.
]

#proof[
  Every $alpha_(i,j)>0$ and $sum_j alpha_(i,j)=1$, so $o_i$ is a convex combination. Barycentric
  coordinates relative to the listed vertices are unique exactly when no nontrivial affine
  dependence preserves both the coefficient sum and the resulting point.
]

#attention-geometry-figure() <attention-simplex>

The attention face is therefore a genuine simplex only under affine independence. Context can
change the vertices, the coordinates, and the candidate population. A zero or negligible
coefficient restricts one event-local face; it does not delete a universal constituent.
The staged key--query, relevance-grid, weighted-value, and residual presentation used by
3Blue1Brown is especially effective because each visual answers one operation before the view
zooms back out to the whole block @threeblue-attention. @attention-simplex adopts that explanatory
discipline while keeping the journal's stricter occurrence and receiver distinctions.

Residual depth recurrence
$
  h_(ell+1)=h_ell+Delta_ell(h_ell)
$
carries a changing activation state. Parameters, activations, optimizer state, recurrent state,
episode cache, and external world material are different persistence classes. Calling all of them
“memory” erases the causal cut which a learning claim needs.

#source-note[
  This comparative ontology is fixed in #link("../../FORMULA.md")[Formula §CXXVI] and its complete
  source map,
  #link("../../RESEARCH/2026-07-20_THE_TOKEN_IS_A_BOUNDARY_ADDRESS_THE_ROUTE_IS_RECEIVER_RELATIVE_THE_RESIDUAL_RETURNS.md")[
    The token is a boundary address
  ]. The transformer equations follow @vaswani2017; their holonic interpretation is a project
  derivation, not a claim made by that paper.
]

== A network is one factorization <j3-factorization>

A trained configuration realizes a contextual relation
$
  F_theta=f_L compose dots compose f_1.
$
Its channels, layers, residual branches, and expert boundaries belong to that realization. Even a
linear factorization has gauge:
$
  B A=(B G^(-1))(G A)
$
for invertible $G$. Nonlinearities restrict lawful transformations, but permutations, compensated
scalings, and function-preserving architecture transformations still separate realized function
from internal coordinate identity @chen2015.

#definition[
  A *neural retriangulation* is a change of internal factorization which preserves a declared
  exterior relation on a named receiver family. It is stronger than coordinate rebase and
  independent of physical redistribution.
]

To establish such a retriangulation, equality on a training sample is insufficient. The two
factorizations need a declared overlap or test family, complete exterior comparisons, structured
residuals, and physical measurements appropriate to the claim. If latency or energy is part of
the thesis, algebraic equivalence alone cannot supply it.

The fixed-basis OLMo observations below should therefore be read as exact coordinate censuses, not
discoveries of invariant experts or detachable skills.

#architecture-axes-figure() <architecture-axes>

@architecture-axes prevents the word “attention” from collapsing three independent directions.
The public Kimi K3 account distinguishes longitudinal Kimi Delta Attention, selective residual
transport across depth, and sparse Stable LatentMoE routing across transformation families
@kimi-k3. That modern architectural overview is a useful visual analogue for holonics because it
shows several incidence axes at once; it is not evidence that the architecture realizes Eros.
Likewise, distributed feature directions and superposition must not be redrawn as one concept per
neuron @threeblue-mlp.

== Exact inherited law after source departure <j3-inherited-law>

The first law-ecology experiment carried two exact dyadic linear laws into cellular Standing:
a calibration matrix and a $2 times 2$ restriction from OLMo 2. Source lineages departed.
Held-out currents later recruited each law from public radiation and produced the exact product.
No-Standing, wrong-interface, and retired-interface foils refused. A declared oriented rebase
replaced each law; the successor conducted after exact rest/remount.

For the calibration:
$
  M=mat(1,1;1,2),
  quad
  x=mat(5;8),
  quad
  M x=mat(13;21).
$
After the declared right rebase,
$
  M'=mat(1,2;1,3),
  quad
  M' x=mat(21;29).
$
This closes source-to-Standing carriage and later source-absent conduct at the cut. The update law
was supplied; the machine did not infer a general rebase.

== Contextual factorization and its boundary <j3-context>

For OLMo 2 layer 7, one fixed-basis factor contribution is
$
  g_j(x_c)="SiLU"((W_"gate" x_c)_j)(W_"up" x_c)_j,
$
$
  E_(c,j,a)=g_j(x_c) W_"down"[a,j],
  quad
  y_(c,a)=sum_(j=0)^8191 E_(c,j,a).
$
An exact census on five receiver axes selected six coordinate summands across three contexts.
Four were common; prose exchanged one summand. The same five-summand membership in conversation
and code-comment still produced different exact outputs because contemporary activations differed.

The important receiver dependence is numerical:

#figure(
  table(
    columns: (1.35fr, auto, auto, auto, auto),
    inset: 4pt,
    stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
    table.header(
      [*Context*],
      [*sign*],
      [*order*],
      [*sign + abs.*],
      [*BF16*],
    ),
    [conversation], [5], [1,936], [5,092], [7,819],
    [prose], [5], [2,775], [5,557], [7,652],
    [code comment], [11], [5,017], [5,017], [7,858],
  ),
  caption: [Smallest stable population size for four nested receiver faces in one fixed OLMo
  factorization. Exact dyadic identity required all 8,192 summands in every context.],
) <hexis-boundaries>

The five-summand aperture preserved only the orientation $(-,-,-,+,+)$. It did not preserve
magnitudes or axis order. The approach to the stricter boundaries was nonmonotone. This is
evidence against identifying one small coordinate cut with a context-independent skill.

#source-note[
  Exact evidence:
  #link("../../observations/eros-transformer-contextual-hexis-01/RESULTS.md")[Transformer
  contextual hexis 01]. Its original “expert” interpretation is explicitly superseded by
  #link("../../RESEARCH/2026-07-22_THE_NETWORK_IS_ONE_REALIZATION_THE_RELATION_MAY_BE_RETRIANGULATED.md")[
    The network is one realization; the relation may be retriangulated
  ]. The arithmetic remains accepted.
]

== Cultivation: changed later conduct and interference <j3-cultivation>

An online cultivation passage began with the six fixed-basis factors and admitted at most 32 new
factors when a declared five-axis orientation-plus-order face remained OPEN. Over nine currents,
15 new factors entered Standing, producing 21 of 8,192 factors. Two later currents closed with no
source return even though the original six-factor body remained OPEN:

#figure(
  table(
    columns: (1fr, auto, auto, auto),
    inset: 4pt,
    stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
    table.header(
      [*Later current*], [*original six*], [*then-Standing*], [*new retrieval*],
    ),
    [prose - relevant after], [OPEN], [closed under 19], [0],
    [code comment - irrelevant before], [OPEN], [closed under 20], [0],
  ),
  caption: [Matched learning contrast. Earlier returned factors participated in later closure.],
) <learning-contrast>

This satisfies the J1 learning criterion at the declared face. It also revealed interference:
two currents which would close under the original six were reopened by intervening cultivation and
needed one further factor. Growth was contextual deformation, not monotone accumulation of
universally helpful parts.

Three frozen changed-operation holdouts preserved only the coarse orientation; signed order
remained OPEN. Selection scanned 122,685 candidates and upstream OLMo still supplied the full
activation field. The result is cultivation evidence, not a portable skill or efficiency result.

== Completion into a local transformation <j3-completion>

A later experiment formed a deterministic rank-six chart. Let
$G in QQ^(6 times 8192)$ be six exact activation rows, choose the first rank-raising pivot columns
$P=[0,1,2,3,4,5]$, put $A=G[:,P]$, and let
$Y in QQ^(6 times 5)$ be the receiver output. Exact elimination formed the unique local law
$
  A K=Y,
  quad K in QQ^(6 times 5).
$
The six lower training rows crossed, were recovered from Standing, and then handed into one
higher constituent carrying $K$. Their data and recruitment interfaces departed.

The law reproduced all six training rows, as square interpolation guarantees. The informative
contrast was later context:

#figure(
  table(
    columns: (1fr, auto, auto, auto),
    inset: 4pt,
    stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
    table.header([*Population*], [*currents*], [*RIDE*], [*OPEN*]),
    [training conversation/prose], [6], [6], [0],
    [related code-comment], [3], [1], [2],
    [changed operation order], [3], [0], [3],
  ),
  caption: [Exact receiver comparison for the completed rank-six local law.],
) <retriangulation-results>

Only one related holdout RIDEd. Every other holdout retained a complete exact rational residual,
with zero fabricated FOUND. The experiment therefore demonstrates local completion and later
participation, not global architectural equivalence.

== Partial translation atlas <j3-atlas>

Conversation and prose also supplied 74 partial maps across 102 intervention sites where they
agreed exactly at either an emitted-lineage receiver or a declared-world-affordance receiver.
The code-comment chart was held out during map formation. After source departure, the later query
recovered all 74 maps and invented none at 28 unsupported sites. At the held-out boundary:

#figure(
  table(
    columns: (1fr, auto, auto, auto),
    inset: 4pt,
    stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
    table.header([*Receiver*], [*maps*], [*RIDE*], [*OPEN*]),
    [emitted lineage], [38], [34], [4],
    [declared-world affordance], [68], [64], [4],
  ),
  caption: [Held-out translation-atlas result. The union contains 74 sites, 66 commuting maps,
  and 8 maps with at least one exact OPEN bit.],
) <translation-atlas>

The atlas is local in the strict sense: repeated consequence across two charts became Standing;
a third chart either conducted through it or exposed its residual. Site identity and consequence
faces were source-supplied. Cross-model alignment and grounded downstream conduct remain open.

== Parent-on-OPEN substitution <j3-parent-open>

The rank-six relation was then placed before the full retained parent projection
$
  P_R(g)=sum_(j=0)^8191 g_j W_(R,j).
$
The local law could substitute only when the deepest applicable Standing receiver was singleton
and its face matched the derived face. Otherwise the complete parent was called once and returned
the exact residual
$
  r=P_R(g)-E_R(g_P).
$

In a fixed six-current passage, one held-out receiver RIDEd before parent evaluation and five
remained OPEN. The exact work at that receiver was:

#figure(
  table(
    columns: (1fr, auto, auto),
    inset: 4pt,
    stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
    table.header([*Path*], [*products*], [*accumulations*]),
    [always-parent foil], [245,760], [245,760],
    [selective parent], [204,800], [204,800],
    [derived local work], [180], [180],
    [omitted parent work], [40,960], [40,960],
  ),
  caption: [Exact rational work at the declared five-axis parent receiver.],
) <parent-work>

After the five residual returns, six independent source-absent probes recovered the receiver
faces without another parent call. This is an operational use of OPEN: it returned to the source
relation and cultivated later support. It is not end-to-end model acceleration. Upstream
activations, the full MLP output, decoding, CUDA, latency, memory traffic, and energy were outside
the measured cut.

#source-note[
  The evidence chain is
  #link("../../observations/eros-self-emanated-law-01/RESULTS.md")[Self-emanated law 01],
  #link("../../observations/eros-pretrained-ecology-cultivation-01/RESULTS.md")[Pretrained ecology
  cultivation 01],
  #link("../../observations/eros-contextual-retriangulation-01/RESULTS.md")[Contextual
  retriangulation 01],
  #link("../../observations/eros-transformer-translation-atlas-01/RESULTS.md")[Transformer
  translation atlas 01], and
  #link("../../observations/eros-parent-on-open-substitution-01/RESULTS.md")[Parent-on-OPEN
  substitution 01].
]

== Probability, loss, and learning <j3-loss>

For a declared local continuation population, a recurrence quotient
$
  Q_D(tau)=N_D(tau)/(sum_u N_D(u))
$
describes supported continuation at receiver $D$. It is not a substance of chance or truth. A
cross-entropy scalar can be a useful differentiable receiver residual, but the causal object is
the mismatch between afforded and actual later continuation. Backpropagation carries the adjoint
of a performed differentiable construction; an optimizer applies a declared metric and update
law; sampling is another world deed.

This yields a typed learning circuit:
$
  "grain" -> "address" -> "transport" -> "transformation",
$
$
  "transformation" -> "outgoing field" -> "later event" -> "residual",
$
$
  "residual" -> "adjoint return" -> "parameter deformation" -> "changed conduct".
$
Conventional ML fixes much of this ecology in advance and learns within it. Eros asks which of
these relations can themselves form, complete, depart, and later recur. The question is
comparative, not a ban on inherited machinery.

#evidence-note(
  [Inherited pretrained structure can become Standing, participate in later contextual conduct,
  and support receiver-relative fallback.],
  [Exact dyadic/rational bounded measurements with matched controls.],
  [Six current observation records plus the fixed-basis interpretation correction.],
  [No invariant skill decomposition, learned universal router, broad transfer, English response
  policy, model-integrated acceleration, autonomous objective, or end-to-end efficiency is
  established.],
)
]
