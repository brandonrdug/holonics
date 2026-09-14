# HNN composition: section, operation, return and chart

[definition] HNN is a developing network of situated sections and interactions. Athena names
its first intended product. Eros names composition and formation within the network; automata
label HNN-based solvers using its traversal constructions. This guide describes the shared
mathematical assembly and its actual owners. It is not a new runtime or a proposed generic
`Holon` wrapper around unrelated implementations. The [deep review](../research/records/2026-09-09_ARCHITECTURE_CHARTS_REQUIRE_COMPOSED_MECHANISMS_AND_FINITE_CONSTRUCTION_RETURNS.md)
retains direct-message provenance, architecture comparisons and the repaired formal reaction.

[definition] The [HNN network contract](plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#the-hnn-network-and-its-mathematical-contract)
joins these mathematical owners into the intended product construction. This guide explains
their mechanics; the blueprint owns their implementation contracts, the roadmap owns order,
and CONSTRUCTION_STATE alone owns the current position.

[interpretation] The [DeepSeek V4.1 comparison](../research/records/2026-09-10_DEEPSEEK_V41_SEPARATES_SHARED_STANDING_CONTACT_AND_CONTEXTUAL_TRANSFORMATION.md)
separates reusable material, current interaction and fresh response, and maps them to these
existing owners. Its exact local-stencil collision identifies a limit of the current conversation
source chart; its finite attention difference separates changes to transported values from changes
to their participation. This informs the existing contextual attachment work without changing AC
order or installing a DeepSeek architecture.

## Context names a situated causal boundary

[project-postulate] Brandon's September 13 clarification makes the scope explicit: context is
the situated boundary over intersecting trees of events, with the material and flux that make
their continuation possible. Lead HNN construction with that evolving incidence and interior–
exterior transport. A text prefix, a local condition vector h and an instantaneous array each
present a particular face of it. None independently defines the complete causal situation.

[definition] On an admitted event-order chart, take a causal past P closed under predecessors.
Its cut exposes the incoming/outgoing incidences crossing P and the retained interfaces to its
interiors. Intersecting event branches join through their actual shared occurrence/port maps;
their joint constraints, phase and local clock comparisons travel with the join. At receiver F,
the relevant restriction is the part that can participate through the admitted transport and
future receiver family. This is a definition over the existing occurrence diagram, not a demand
for a global synchronized lattice or for storing every ancestor. A spatial incidence graph may
contain circulation even when its successive events are ordered causally.

[definition] The restricted boundary carries its medium's current, storage, constitutive
response, changing incidence, and the retained interior response needed for subsequent conduct.
An exterior face can therefore be small while its realization has nested dynamics. The local
ports `s=S_e(q,o)` and `h=C_e(q,o)` in the blueprint are restrictions of that situation. The
condition port h is an operand of one law; it is not a replacement definition of context.
In current prose name the actual operand: event cut, incident current, held charge, material,
source restriction, interior return, or receiver. Use the shorthand only with that scope stated.

[established-bounded; source-inspected] `Foundation/AddressedBoundary.lean::boundary_join`
cancels the matched middle face using its pullback joining equality.
`Transport/WorldTube.lean::ClockedSpan.comp` retains both occurrence clocks, receiver faces
and obstructions. Native `current_world.rs::NativePathChart` realizes an ordered path incidence
chart; `causal_traversal.rs::ExactReactiveTraversalInteraction` separates arriving current,
retained storage, material and feedback into the next morphology. These are existing owners
and specializations, not evidence that a one-dimensional path implements every event complex.

### Material, capacitance and changing incidence

[definition] In a fixed finite capacitive chart, let phi be real potential, C positive symmetric
capacity, d the oriented incidence, and W nonnegative branch conductance. Stored charge is
`q=C phi`; the dissipative response is `L phi=d* W d phi`. Conservation with injection b gives

```text
partial_t(C phi) = -L phi + b.
```

This equation states what the material stores and how flux crosses its actual connections.
The electrical realization uses its voltage, capacitance, conductance and time units. Other
media supply their corresponding constitutive storage and flux law. Capacitance here is a
material relation, not a synonym for an allocated context length or a scalar model capacity.

[proved-derived] For differentiable C on that fixed carrier,

```text
E = phi* C phi / 2,
E_dot = phi* b - phi* L phi - phi* C_dot phi / 2.
```

The material-rate term follows from differentiating charge and energy together. For constant
C, backward Euler gives `(C+dt L) phi_next=C phi+dt b_next`; thus the existing implicit diffusion
solve is also a state-space step. With changing C the charge-conserving step uses C_next on
the left and C_previous on the right. A changed node/port population additionally needs the
actual transfer of stored charge between carriers and its boundary work. Coordinate relabeling,
physical coupling change and birth/removal of a port are different transformations.

[established-bounded; source-inspected] `Physics/CoupledIncidence.lean` carries branch drops,
quadratic storage and the generalized `K v=omega² C v` mode relation.
`Physics/PortEnergyHeat.lean` carries driven capacitive/inductive response, heat and changing
storage. `Physics/ConstitutiveModulation.lean` carries incidence/material/state changes.
A Hamiltonian chart supplies the energy and its symplectic or quantum evolution; dissipative
and driven terms retain their additional laws. The instantaneous graph specifies admissible
couplings, while the material specifies their action. The Hamiltonian operator and a Hamiltonian
path through a graph denote different constructions; neither is implicit merely in having nodes.

### State-space, convolution and diffusion are connected realizations

[proved-derived] For the linear recurrence and receiver
`x_(k+1)=A x_k+B u_k`, `y_k=R x_k+D u_k`, induction gives

```text
y_k = R A^k x_0 + sum_(j=0)^(k-1) R A^(k-1-j) B u_j + D u_k.
```

This is a retained interior realization and its causal convolutional boundary response,
including the initial-state return. For varying maps, `A^k` becomes the ordered transition
product and the kernel depends on both event positions. Input-dependent material can make
that entire map input-dependent. Its composition remains useful even where translation
symmetry no longer provides one shared convolution kernel. The spatial analogue
`y(v)=sum_delta K(delta)x(v-delta)` shares transport by relative displacement on its declared
translation chart; irregular/changing incidence uses the corresponding addressed operators.

[established-bounded; source-inspected] `Computation/HolonicArchitectureCharts.lean` owns
state-space fold composition, the linear recurrence, convolution equivariance and graph-current
specializations. S4 develops a structured SSM with efficient convolutional evaluation;
Mamba's input-dependent SSM parameters use selective recurrent computation. These external
constructions help identify realizable state/transport laws; they prescribe no HNN architecture.
[S4](https://arxiv.org/abs/2111.00396), [Mamba](https://arxiv.org/abs/2312.00752).

[proved-derived] The same fixed-operator convolution has the generating function
`sum_(j>=0) R A^j B z^j = R(I-zA)^(-1)B`, as a formal power series or on its analytic
convergence domain. A recurrence, convolution kernel and rational resolvent can therefore
encode the same boundary response. Initial standing still contributes its separate transported
term. This gives the existing factor/recurrence work a direct SSM application without imposing
token-by-token execution or claiming that every changing nonlinear system has a fixed resolvent.
S4's construction explicitly evaluates this generating function through structured Cauchy
operations. [S4, sections 2.4 and C.3](https://arxiv.org/pdf/2111.00396).

[proved-derived; formal-checked] Integration by reflection retains the same interior return.
For `x_dot=A x+B z+f`, `z_dot=C x+D z+g` and `z=Kx+r`, the new
`Physics/ReflectedBoundaryMemory.lean` gives

`r_dot=(D-KB)r+(C+DK-KA-KBK-K_dot)x+g-Kf`.

The [fluid construction](FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS.md) supplies the matching
memory kernel and MHD mixed interactions. A local SSM can realize such a returning interior;
a static boundary matrix omits it unless the required residual/forcing terms close. This is
why changing geometry and stored current belong in the generating operation itself.

[proved-derived] With constant coefficients, Laplace-domain elimination exhibits the connection
directly: the boundary operator is `sI-A-B(sI-D)^(-1)C`, and its source is
`x(0)+f_hat+B(sI-D)^(-1)(z(0)+g_hat)` wherever the transform and inverse are defined.
Thus dynamic Schur response, the interior semigroup memory and the SSM resolvent are three
representations of this same coupled equation. The initial interior source survives each one.

[definition] Deterministic diffusion conducts a field through its constituted evolution.
Probabilistic diffusion conducts a declared source measure through transition kernels.
Generative denoising supplies an evolution formed from data/constraints that carries an initial
field toward product receivers. Its denoising index, event time, physical time and wall time
are separately named clocks. An unconditional generator still has initial state, material,
domain, schedule and receiver conditions; it needs no text prompt to have a situated source.

[established-bounded; source-inspected] DDPM defines a forward Gaussian corruption process and
a formed reverse Markov chain starting from a Gaussian source. Its progressive sample production
is a concrete example of generation through successive whole-field transformations.
[Ho, Jain and Abbeel](https://arxiv.org/pdf/2006.11239). The existing
`Computation/HolonicDiffusionCharts.lean` proves finite Markov composition and expectation
transport and supplies a collapse example separating a forward kernel from an inverse.
The formed reverse law and its source distribution provide the generative information.

[definition] Include the initial field and any later sampling innovations in a complete source
xi. Conditional on xi, a realized generating trajectory is `Gamma_(Theta,b)(xi)`; its output
measure is the pushforward of the declared xi measure through the product receiver. This gives
noise, deterministic execution, retained preimages and probability their respective places.
It does not assert that an arbitrary forward diffusion has an inverse or that denoising is
physical reversal of the source events. Nonlinear drift and interactions may form new structure;
the operation is more than choosing among a fixed list of stored responses.

### Joint prediction is a boundary section of the future

[definition] For source family F and admitted complete transitions T_j, the prospective joint
receiver is

`Gamma_m(F)={(rho_1 T_1 x, rho_2 T_2 T_1 x, ..., rho_m T_m ... T_1 x) : x in F}`.

Each T_j carries the current, material, incidence and clock changes of its actual passage.
This is one family with shared producing variables. A requested output can be a spatial field,
multiple future faces, a section of a trajectory or a text block. A one-token receiver and a
multi-token receiver choose different faces of this construction; they do not define its interior.

[established-bounded; source-inspected] The cited multi-token-prediction work uses several
future-token heads over shared producing material. Its particular independent-head objective
does not by itself specify every correlation of a joint future distribution.
[Gloeckle et al.](https://arxiv.org/abs/2404.19737). The native `read_wave_word`, family receiver
and coupled producing-cut owners explicitly retain shared future coordinates at their declared
scope. Releasing those coordinates through a receiver is output, whether or not their medium
has a token codec. Scheduling several outputs together requires their actual dependency map.

[project-postulate] The next construction therefore composes the evolving event boundary,
stored interior current, constitutive interaction and requested joint release. Native source/
condition restrictions and source-null contrasts are local tools within that assembly. They
are not an independent context-extraction stage or a prerequisite to every kind of inference.
Inspect the actual lattice/field conduct and output; use the dynamic reflection defect when
encoding it. The roadmap and blueprint retain the concrete implementation order and bindings.

## Holonic Encoding

[definition] **Holonic Encoding** names the situated formation and reuse of causal
transformation representations through the existing occurrence, current, interaction, receiver
and compression owners. It is HNN's general counterpart of tokenization. An encoded constituent
carries addressed ports, actual joining incidence, conditions, chronology, receiver/decoder and
Preimage Fibre. Its grain can be a path, loop, coupled field or region; overlapping grains remain
available through their actual shared occurrences. A serialized symbol handle is an exterior face.

[project-postulate] The operative grain is recurring transformation, as retained in the
[encoding recovery](../research/records/2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md).
The historical BPE/path-fold and autoencoding constructions inform this composition; global
frequency, a permanent segmentation or a manually authored semantic classifier does not found it.
Text, vision and acoustics supply different source/receiver charts to the same developing ecology.

[definition] Static reconstruction and continuing conduct have separate comparisons. The encoder
E and receiver decoder D serve D E=ρ at their admitted scope; exact dynamic compression also
serves E′ T=U E across the actual material/clock change. A partial learned relation retains its
comparison and compatible family. π's analytic remainder is one instance of a retained omitted
contribution; language does not inherit a known π-like continuation law.

[established-bounded; source-inspected] Current text uses `SymbolCurrentChart`'s supplied unit
symbol basis and `NativeCoupledWaveSession`; it is not a learned autoencoder or general encoding
faculty. The existing host observable-moment closure gives an exact local reference, while
`ResidentGeneratorNeighborhood` supplies native condition contact and local formation. Their
needed wave/source/receiver binding is specified in the Athena blueprint; it is not supplied by
a shared row width or by adding a token table.

[definition] The Complex Parametron retains quadratures and coupled incidence before taking a
phase/sign/intensity receiver. The clocked torus cut retains (q,z,r,clock) and its actual passage
law. Those constructions guide phase-sensitive encoding, with real source timing and receiver
orientation retained. They do not assign a pump frequency to a character or impose a torus on
every datum. The recovered record names exact formal, resident, optical and acoustic owners.

## The architecture as explicit passages

[definition] A **Holonic Solver** navigates admitted representations of a source constraint,
returns their executable action and receiver/decoder with its domain and fibre, and compares
their complete work in a declared resource chart. The
[first exact synthesis return](../research/records/2026-09-11_HOLONIC_SOLVER_NAVIGATES_EXACT_GENERATOR_FACTORIZATIONS.md)
composes existing rational preimage solving with bilinear tensor certificates and π/e/Gamma
transfer blocks. For HNN use, a factorization of a pure local operation does not automatically
preserve an entire mutable ecology: source, clock, emission, material and successor must cross
the actual implementation map. Lean remains exterior to native conduct.

[definition] **Hephaestus** labels tools and utility models, including code generators;
**Hephaestus Automata** names task-scoped application instances of this construction.
The [design](HEPHAESTUS_AUTOMATA.md) connects code/tool and mathematical requests,
shared constituent actions, changed receivers, catalytic morphology and resident handoff.
An operator's application constraint does not create another learning law or an independent
engine. Eros composes at each nested scope; Athena retains the wider available construction.

[definition] The current [receiver edition](../research/papers/rendered/hnn-information-chemistry.pdf)
uses the repository-local [receiver](../research/papers/source/packages/holonic-receiver/README.md)
and [engraving](../research/papers/source/packages/holonic-engraving/README.md) packages. Its twenty-eight
plates expose complex source/current, projection and visibility, field-derived hatching,
orientation, entropy, curved GR reception and shadows on white paper with black phase fields.
The [stress/knot continuation](../research/records/2026-09-10_STRESS_ENERGY_AND_SCATTERING_WAVES_RETAIN_THE_KNOT_AND_ITS_RECEIVERS.md)
adds prime knots, a chain, exact propagating wave/heat states, fluid/circuit and stress-energy
diagrams, quantum/Feynman attachments, and three Lean energy/observer owners.
The [woven ecology continuation](../research/records/2026-09-10_WOVEN_FIELD_ECOLOGIES_RETURN_OPTICAL_HORIZONS_AND_REMOTE_CONFORMATION.md)
adds a collective field horizon, actual four-field shorts passage, optical/local-gravity receiver
comparisons and abstract allosteric domains, with phase-contact/gauge and intensity-defect laws.
The [sequence/kinetic return](../research/records/2026-09-10_SEQUENCE_FOLD_AND_REACTION_CURRENT_MAKE_THE_CAUSAL_THOUGHT_CHAIN_CONCRETE.md)
makes sequence-conditioned folding, steric feedback and biochemical turnover explicit, and maps
their causal-chain consequences into the existing Athena producing-return handoff.
The [twenty-plate composition atlas](../research/papers/rendered/hnn-composition-atlas.pdf) preserves
the preceding Athena/Eros, layer, arithmetic, diffusion, manifold and source-return diagrams,
with [editable companion source](../research/papers/source/papers/hnn-information-chemistry/composition-atlas.typ).

[established-bounded; implemented-exact] The [receiver return](../research/records/2026-09-10_RECEIVER_ENGRAVING_RETAINS_COMPLEX_CURRENT_AND_SUPERSEDES_THE_PAINTED_ATLAS.md)
keeps complex vertices, supplied currents, incidence, camera/analyzer data, exact source mark
parameters and omitted fibres in a shared Typst/SVG packet. It exhibits a regular C³ flow with a
singular real receiver, a curl-bearing extension, and a present-color equality separated by later
contact with a reference. These are exterior receiver realizations; the native emission binding
in the Athena blueprint remains its own implementation packet.

## The assembly has several distinct roles

| Role | Carried relation | Existing owner and implementation boundary |
|---|---|---|
| Situated occurrence | Actual source/target, local frame, conditions and lineage; co-presence alone is not contact | Formal `Holon`, `CausalNaturalHolon`, `AddressedPassage`; native `NativeFieldOccurrence`, emission/anchor and lineage owners |
| Section and incidence | Local values/potentials over addressed carriers; links retain orientation and actual joins | `NativeCarrierChart`, `NativeFactorizedSection`, native spool sections and field contact population; resident sections are physical storage, not semantic identity |
| Constitutive operation | Transport, interaction/aggregation and reaction using the target's prior standing | `FiniteLocalCurrentEcology`, `HolonicRecurrentEcology`; generic full-operator primitives and the separate constitutive-field law |
| Return and plasticity | Actual comparison, producing factors, covector or other derived response, metric/constitutive update and its finite successor | `SituatedLearningReturn`, `GradientProposal`, `FactorizedLinearOverlay`; field material/contact returns and full-operator local/recurrent returns |
| Receiver and compatible causes | Joint future section, declared measurement, retained Preimage Fibre and separating histories | `ReceiverTransformer`, `DynamicReceiverChart`, `CausalRelevance`, native current/fibre/material receivers |
| Reuse and scale | Restriction, rebase, generator/decoder and the future consequences preserved | Leader jets, fractal restrictions, sheaf diffusion, spool incidence, source-map/current journals and receiver-history compression |
| Realization and persistence | Device placement, exact codewords/series, residency, transfer, checkpoint and exterior presentation | `ResidentSurface`/passages, source/rest owners, `NativeSavedSession`, alpha checkpoint, tensor/ONNX intake/export charts |

[definition] These are responsibilities within one operation, not seven sequential engines.
The successor includes changed state and morphology. A readout, borrowed producer or receiver
view does not clone that owner. An older frozen-morphology chart remains a valid comparison
without defining inference universally as frozen morphology.

## Local standing is part of reaction

[proved-derived; formal-checked] In the finite homogeneous chart,

```text
current(target) = sum_source J(morphology, occurrence, state, target, source)
next(target) = R(morphology, occurrence, target, state(target), current(target)).
```

`FiniteLocalCurrentEcology` now carries both arguments to R. The graph specialization previously
substituted zero for `state(target)`; it is repaired. Complete graph update/relabeling and the
no-contact retention control are verified. This chart does not require a universal scalar local
state: its Carrier is a parameter, and dependent carrier/shape transport has its own existing
owner. Native field kernels do not acquire a new reaction merely because the formal signature
has been corrected.

[definition] A finite paired reflection is one constitutive choice. A state-conditioned contact
is another. A joined product, a nonlinear local response, a retained-state update and an exterior
receiver are mathematically different operations. The model assembly must say which actually
occurs and how it affects later conduct. Listing all as “phase transport” hides their differences.

## A tensor is an operation chart, not just a file payload

[definition] For a finite admitted family, a linear transport has a matrix chart; a multilinear
interaction contracts a tensor product; a general neural map composes these with local reactions
and state. For example, pairwise compatibility, value transport, a normalized ratio family and
reaction can form an attention chart. Translation-tied coefficients form a convolution chart.
Sparse incidence forms a graph chart. Retained state plus observation forms an SSM chart.
None supplies the entire model merely by assigning it that architecture's name.

[definition] `NativeOperationPrimitive` already includes contraction, causal contact, Hadamard
product, addition, nonlinear response and rebase. `NativeOperatorNode` records their incidence
in the admitted full-operator chart. These owners demonstrate an executable mathematical graph;
their inherited configuration, supported shapes and local law restrictions remain explicit.
They are not to be copied into an unrelated second graph system or installed as an entire
Transformer inside native Athena.

[definition] The common comparison is a source-qualified realization map. A coefficient tensor
and its axes can be projected or reindexed while preserving the operation; a lossy projection
retains its complete defect and admitted receiver scope. Safetensors stores those coefficients;
ONNX may serialize their operation graph. Soulkiller recovers and restricts productive operations
and returns native material plus a cold witness. Eros develops the material. Export makes the
opposite comparison on an actual target graph; storage round trips alone do not perform it.

## The missing native attachment is explicit

[established-bounded; source-inspected] The existing field and full-operator paths already share
resident-section execution apparatus. Their semantic assemblies differ. The active field
selects a material source from `NativeMaterialTransportSource` and uses a paired constitutive
law. The full operator assembles a richer word of generic primitives but retains its supported
source graph and artifact dependencies. The `holonics` facade exposes both owners; it does not
make their model states interchangeable.

[established-bounded; implemented-exact] The [first finite native assembly](../research/records/2026-09-09_AC1_AC2_THE_HOLON_FIELD_OWNS_ASSEMBLY_AND_OBSERVED_RETURN.md)
now uses the existing `OperativeContextual` feature `Q(1,s) tensor Q(1,c)`, where c is the actual
operative standing including interior current. Its material factors, joint source/condition
pullback and producing paired return retain their original scope. This is recovery and
composition of existing mechanisms, not the installation of a new nonlinear law.

[historical] The field/model wrapper and byte-cultivation adapters were
[removed from the live SDK](../archive/implementations/2026-09-09-byte-field-cultivation/README.md).
The [representation audit](../research/records/2026-09-09_THE_BYTE_CLOCK_AND_OCCURRENCE_EXPANSION_ARE_NOT_GENERATOR_CULTIVATION.md)
records why generic API factoring, per-occurrence material and source archive persistence did
not establish productive generator organization. Their local comparisons remain evidence.

[definition] The first replacement attachment uses the existing `ResidentConstitutiveFibre`
as local learned generator material. Its relation basis carries source/condition conduct and
its full receiver fibre; independent relation formation, not occurrence count, changes rank.
`ConstitutiveFibreRest` adds validated rest/remount of that law without the observation population.
Current returns compose through the existing resident current ports. A whole HNN must still
compose these local generators, incidence, nonlinear response, scale and applicable fibres.

[established-bounded; implemented-exact; computational-witness] The [joint-family return](../research/records/2026-09-09_LEARNED_GENERATORS_COMPOSE_THROUGH_JOINT_FIBRES_AND_RETURNS_REFINE_THE_SOURCE.md)
now supplies composition through plural currents: the source and receiver remain actual objects,
their joint affine fibre preserves correlation, and partial source coverage is explicit. A
downstream observation restricts the source through that joint object. The original-condition
check permits its returned constraint to meet existing actual condition current; the prior
current determines the still-free component. This changes subsequent native conduct without
selecting an external cause or retaining a chain of past image/current objects.

[definition] `ResidentGeneratorNeighborhood` now composes those local owners around an explicitly
shared condition field. The particular law supplies dependence; membership supplies no coefficient.
Its received passage prepares condition reaction, forms local material, and publishes the complete
successor under one move owner. This is a declared neighborhood chart, not a claim that every Holon
contacts every other Holon. Its rest separates applicable laws, actual current and latest received
constraint evidence. Wider incidence, scale changes and source attachments retain their own maps;
the local construction does not replace them with a source archive.

[definition] `ResidentNormalMaterial` attaches the already-derived accumulated normal response
to resident current operands. It retains exact source geometry and cross-source phase, with
fit discrepancy separate from numerical solve error. Its reports retain the complete bounded
response, and its update stages the existing normal calculation before publication. The actual
source/receiver chart still determines what a supplied observation means; this objective is not
an authored semantic score or proof that an observed response is a correct answer.

[definition] Whole-section input now uses `ResidentConstitutiveSection` and the generic local
difference receiver. `receive_section` fits the common successor after all supplied observations;
it does not install a new source coordinate for each observation. Its returned before/after
fields retain actual operator cuts. Bounded outputs can enter the normal current port intact.
The exterior Unicode/symbol-basis attachment is one declared source chart; its local stencil
does not define every medium's geometry or all language context.

[established-bounded; measured] The [boundary/interior return](../research/records/2026-09-13_BOUNDARY_AND_INTERNAL_CURRENTS_FEED_JOINT_HNN_PREDICTION.md)
now binds actual outgoing and operative internal-current enclosures into normal formation
and the coupled HNN's joint forecast. Enclosed targets preserve their moment-error terms.
The source task fixes material and contact population after preparation; it infers a local
five-coordinate field transition from eight returns and measures a later field comparison.
The native source retains all internal coordinates, including a nonzero pair hidden by its
present aggregate. This is a consuming source specialization within the full event-boundary
assembly; changing incidence/material still requires its own action and mixed-return map.

[established-bounded; implemented-exact] The [empirical return](../research/records/2026-09-13_EMPIRICAL_RETURNS_KEEP_SOURCE_FIBRES_AND_FORM_THE_NEXT_PREDICTION.md)
now binds a later observed state through `NativeCoupledBody::observe`. It forms the existing
normal moments from the producing source and condition, with `eta=y-c_s` and `delta=y-v_s`
retained as different receivers. Affine and dependent bodies use this same operation. A later
parameter constraint reaches an earlier prediction through the existing joined-word pullback;
the earlier source marginal alone does not establish that correlation. Local normal formation
and wave transport keep separate clocks, and remount retains the historical producing map.
The nine-observation field consumer, two-member parameter family and their next forecasts
are verified at the scopes recorded there.

## Producing comparison and architecture laws

[definition] The [mass–energy synthesis](MASS_ENERGY_AND_CAUSAL_TRANSPORT.md) places the
recent architecture, source, mode and prediction work within one physical account. Invariant
mass reads complete rest energy; momentum, radiation and field energy read its transported
configuration. Wave/heat and constitutive response connect the actual generators; sufficient
mode reduction preserves the complete admitted future and its energy/phase/current receiver.
The resulting models are computational-biology/neuroscience and physical modelling work at
their declared scopes, not a separate non-intelligent mathematical activity.

[definition] The [predictive-release return](../research/records/2026-09-12_PREDICTION_IS_PREPARED_TRANSPORT_AND_RELEASE_IS_BOUNDARY_CURRENT.md)
connects prepared internal modes, release into the medium, subsequent transport and receiving
contact. A current can be output-null now but potent under a later admitted action; reduction
therefore uses the declared future family. Prediction is that family's prospective image.
Probability measures unresolved source conditions through the deterministic pushforward.
The release/landing solver, observer boundary current and changing-capacitance work are
actual returned consumers; no neural activation counter or trajectory archive is introduced.

[definition] The [periplus/time-complement return](../research/records/2026-09-12_PERIPLUS_REBASE_AND_TEMPORAL_RESIDUES_JOIN_GAMMA_ZETA_AND_HODGE.md)
joins passive modal rebasing, complementary residues and actual return transport. A backward
adjoint transports a comparison covector; it is not the physical inverse of the forward
process. Forensic reconstruction means a compatible generating class or newly prepared
realization, not an exact historical snapshot. The Gamma cocycle, ζ code receiver and temporal
Hodge construction supply actual equations and consuming owners for this connection.

[proved-derived; formal-checked] The [transformer/fractal-mode lift](../research/records/2026-09-12_FRACTAL_MODES_LIFT_ATTENTION_INTO_MASS_PRESERVING_GENERATOR_COMPRESSION.md)
composes normalized contact kernels with Gibbs/KL inference and associative `(mass,current)`
summaries. Gram/exterior dependence excludes a redundant independent direction while its
amplitude joins the retained coefficients; generator descent preserves this elimination
through every admitted word. Explicit fractal restriction/scale laws and propagated summary
defects connect recursive representations to the code receiver. The molecular application
must preserve marked catalytic currents as well as body occupancy.

[established-bounded; implemented-exact] `exact_linear::KernelModeReduction` derives a modal
encoding/decoder from an actual kernel, preserves mass and signed phase currents, and compiles
a source action or returns its separating fibre. The exact six-source/two-mode application
uses the shared owner; it supplies no new native runtime law. The source review also repairs
the Transformer paper's outward-normal sign and constant-input normalization domain.

[proved-derived] The same record defines a lifted complex logarithmic cross-entropy for
`z_i=√q_i exp(iθ_i)`. Its excess over the source self-reading is
`D_KL,₂(p||q) - (2i/ln 2) Σ_i p_i(θ_i-φ_i)`: real code excess and oriented mean phase defect.
Coherent class currents add before this logarithmic receiver, retaining interference and
its possible zero. This explicit finite-sum derivation is not yet a separate Lean owner.

[definition] The [equational/world-tube review](../research/records/2026-09-10_EQUATIONAL_LAWS_AND_WORLD_TUBES_MAKE_ATHENAS_NEXT_PASSAGE_EXPLICIT.md)
connects ETP's congruence/implication/countermodel method with the existing future-stable receiver
relation. MLP, convolution, graph, attention, SSM and diffusion charts share elementary passages,
while incidence, parameter sharing, nonlinearity and retained state determine which laws apply.
A fixed linear SSM has an exact convolutional realization including initial state; a selective
transition need not. The review returns exact examples instead of asserting universal equivalence.

[established-bounded; source-inspected] `ResidentNormalWave::actuate_section` now transports the
actual joint current under fixed material. `predict`/`receive_prediction` now bind an observed
return to its producing joint and material cut, including pending rest. The conversation example
exercises an explicit same-part observed-tail chart; general reply relations still require their
actual source/receiver association. Native basis selection, exterior symbol emission and ordinary emitted-source re-entry now share
`NativeWaveSession`; its [verified return](../research/records/2026-09-11_ATHENA_EMITS_THROUGH_A_RESIDENT_RECEIVER_AND_REENTERS_ITS_SUCCESSOR.md) retains the full source family, pending phase and delivery cursor. Coupled organization remains
the next binding in the [blueprint](plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md).
`receive(v)` keeps its distinct next-current meaning. Applied transport carries stored M and
actual source/rounding bounds; the normal-reference family remains a separate declared receiver.
The [source return](../research/records/2026-09-10_ATHENA_RETURNS_OBSERVATIONS_TO_THEIR_PRODUCING_JOINT.md)
records the exact checks and wider-run scope.

[definition] The [final computational review](../research/records/2026-09-10_TENSION_DYNAMICS_BECOME_ATHENAS_COMPUTATIONAL_CONSTRUCTION.md)
now fixes the first conditional response as `η ∈ L_j((c−p,c,p),h)` with actual join `(c,c+η)`.
The blueprint makes the bounded source/target lift, resident basis receiver, single move owner and
staged local-law/condition publication explicit. Coupled organization is part of the construction;
its first finite chart does not claim that a fixed linear wave is the entire HNN architecture.

[definition] The geometric continuation uses existing `WorldTube`, `WorldTubePotential`,
`ConstitutiveWorldTube` and clocked torus owners. Local frames, material currents and complete
boundary faces travel together. A Hodge reconstruction, knot framing or arithmetic spectral map
is used when its actual source and receiver call for it; none is a compulsory block in every HNN.

[definition] The [linked-contact rendering return](../research/records/2026-09-10_RECEIVER_ENGRAVING_RETAINS_COMPLEX_CURRENT_AND_SUPERSEDES_THE_PAINTED_ATLAS.md)
now instantiates the Turn tablet's friction-as-coupling relation: rounded links share a real contact
patch, equal/opposite forces constrain their movement, and their relative current supplies an
exact heat/complex-interface return. Zero total force retains nonzero dissipative work. This is
an exterior constitutive instance of the need for a paired source and future receiver; it does
not prescribe a fixed viscosity or energy-decrease gate for native learning.

## Partial conduct and comparison

[definition] Useful restricted behavior can arise before every mechanism learns or every chart
commutes exactly. Compare the actual dependency being exercised: local sensitivity, preservation
of standing, conditioned interaction, acquisition of an observed relation, later reuse or
response under a changed circumstance. Derivative checks establish the differentiated map;
learned behavior establishes its observed scope. Neither is replaced by prose quality, entropy,
the number of tests or a requirement to return through the entire history.

[proved-derived; formal-checked] `ChangingReceiver.passageDefect_comp` preserves an exact
nonlinear finite defect and `norm_passageDefect_comp_le` transports its norm under a declared
bound. This allows an approximate chart to carry a receiver tolerance through a finite
continuation. Exact every-word commutation belongs to the stronger exact compression claim.
Neither theorem demands that all compatible causes be individually enumerated or identified.

[definition] Text, audio and visual material meet this same assembly through different source
and receiver charts. A byte boundary, PCM sample clock or raster/mesh coordinate does not found
the native interaction class. The Apple temporal owners offer actual section/clock/condition
construction to compare. Bringing their physics or codecs into a new model requires the actual
source law; the shared abstraction alone does not establish a multimodal learner.

[definition] The [blueprint](plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md)
defines finite construction returns; [the roadmap](plans/THE_ROADMAP.md) orders them and
[CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md) states the current position. The product ambition
persists across those returns and does not turn each local research question into a requirement
to complete general intelligence.
