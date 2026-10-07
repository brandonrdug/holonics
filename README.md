# Holonics

Holonics is Brandon's research programme: a mathematical, physical and computational framework
for how situated things exist, interact, change and become observable. It starts from the reality
of difference: nothing is observed except as a difference that some receiver can read. Its
ambition is a theory of everything in that sense, and a machine built from it that is useful on
ordinary hardware. The ideal is 20 W, about what a brain uses: cost should follow the causal
extent actually in play, not the size of what is stored.

Brandon directs the work. Codex owns implementation, builds, tests, formal integration and
repository integration. Claude contributes architecture, derivation and review. The work is public
so that anyone who finds it
can see what we think, how far it has come, and where everything is. Nothing here is for sale. A
claim holds only with its stated grade and evidence ([reading a claim](#reading-a-claim)), and the
failures are kept alongside the successes.

[What we think](#what-we-think) ·
[What exists now](#what-exists-now) ·
[What has not worked](#what-has-not-worked) ·
[Where everything is](#where-everything-is) ·
[Reading routes](#reading-routes) ·
[How the work is done](#how-the-work-is-done) ·
[Building and checking](#building-and-checking)

## What we think

These are the project's definitions and postulates, stated plainly. Each linked owner carries its
grade and its evidence.

**A thing is a Holon.** The elementary object is a law with ports, not a state:
`H = (K, ∂_A; Π; 𝒟; 𝓔; G; π)`. It has a complex of oriented cells and their incidence, ports whose
flow and effort pair to power, a power-neutral interconnection, the material law it runs in (its
constitution), navigators with their keys and clocks, and restrictions between scales. A Holon is
a whole and a part at once: Holons joined at ports form a Holon, and the joined whole with its
retained constituents is a **Holarchy**.
[The elementary objects](docs/ELEMENTARY_OBJECTS.md) · [the Holon](docs/HOLON.md)

**Observation is reception.** A receiver is a role that a participating Holon plays. Reading
changes both participants and returns a receipt, a field of readings over a partition, each region
in its own frame and clock. There is no global scalar and no privileged clock. Time passes in
**aeons** (containers of causality), divided into **epochs** at a receiver's section; a **cycle**
is a closed loop, a completeness rather than a duration.
[The receiving Holon](docs/RECEIVER_HOLARCHY.md)

**Compression is intelligence is navigation.** Brandon's slogan names the line we build. To
understand a stream is to find what made it: its navigator and the key (the initial configuration)
that set it going. A short description is the evidence that you found it. Landmarks are the faces
where navigators' paths converge. Learning is locating keys, the way the Bombe inferred an Enigma
key by closing loops over a menu of contacts: inference targets the process that made the data,
not a blind search over keys.
[Keys, locks and navigation](docs/ELEMENTARY_OBJECTS.md#keys-locks-and-navigation) ·
[the line](docs/THE_MACHINE.md#the-line-the-rebuild-serves)

**The HNN is a morphodynamic circuit.** The Holonic neural network is a continuing field of complex
parametron rings, annular rings that store, oscillate and lock, joined by helical pair contacts,
which slip, dissipate and address. Its geometry and constitution govern motion; admitted motion
can change geometry and couplings, with its work accounted for. Information is phase and winding
on the rings. Learning deposits a comparison actually reached into the constitution. **Dynamic
Geometry** and **Asymmetric Potential** name aspects of this same construction, with their
consumers still subject to the gates below. A graph, tree or weight matrix is a declared chart of
the continuing circuit.
[The machine](docs/THE_MACHINE.md) · [the HNN formula](docs/HNN_FORMULA.md) ·
[language and operators](docs/ELEMENTARY_OBJECTS.md#the-morphodynamic-circuit) ·
[helical geometry](docs/HELICAL_GEOMETRY.md) · [winding and carry](docs/WINDING_CARRY_AND_PLACEMENT.md)

**Memory is a quotient, not a tape.** Retention is a quotient sufficient for every admitted future,
including admitted actions. The constitution suffices but need not be minimal. Its representation
keeps the decoder and unresolved fibre that future receivers may read.

**Loss is the logarithm of a ratio.** Comparing a produced Holon with its target gives a relative
transport `R`. The loss is `log R`, whose winding is the branch of the logarithm, and its
derivative `R⁻¹dR` is the learning covector. Cross-entropy is one face of it, and it is physical:
flux across a section. Its excess over the entropy, the relative entropy `D(p‖q)`, is the free
energy over equilibrium (in units of `k_BT`) and the entropy produced along a passage.

**Probability is a receiver's geometry.** Bayes' rule is a translation in the log-odds chart. Two
point reflections (Swings) compose to a translation, and the same step is the replicator equation
of population genetics, with likelihood as fitness. The Fisher metric is the pullback of the
amplitude sphere.
[Record](research/records/2026-09-27_PROBABILITY_IS_A_RECEIVER_GEOMETRY_BAYES_IS_THE_RATIOS_TRANSLATION_AND_THE_EGGS_PERIOD_IS_HYPERGEOMETRIC.md)

**A receiver keeps a population of eggs.** An *egg* is a candidate source read whole: a navigator
with its genome (its description) and its phenotype (the faces it emits). A receiver reading an
unknown stream weighs a population of eggs by their description lengths and updates it by Bayes.
- Families fall **dormant** and wake again.
- They **die** by exchange: the dead mass passes to the survivors, and the seed is kept.
- New families are **born** from reserved mass.
- Families **compose at ports**, where a keystone conditions the others.

[The egg](docs/ELEMENTARY_OBJECTS.md#the-egg-a-generator-read-as-a-whole)

**Arithmetic is exact.** There is no floating point inside the machinery:
- values are ratios with their remainders, and integers are carried with their factorization;
- algebraic and transcendental quantities are their constraint identities (π and `e` are
  navigators, and a float is one of their faces);
- measurements are reported exactly, as `3 + 1/16 + ε` bits and never as a decimal.

**Mathematics is terrain.** The Riemann hypothesis, the Hodge conjecture, complex Euler and
Navier–Stokes, and Birch–Swinnerton-Dyer are targets for the same compression and landmark
discovery, not a separate project. **None of them is solved here.** The work on them consists of
partial derivations, formal lemmas and located obstructions, each graded.
[The targets](docs/ELEMENTARY_OBJECTS.md#the-targets) ·
[the RH work](research/records/2026-09-26_THE_ZERO_GAS_IS_A_COMPLEX_BURGERS_FLOW_AND_RH_NEEDS_A_SOURCE_LAW_AT_TIME_ZERO.md)

**Athena** is the first intended product. It is a local program that takes a person's request and
conversation context and returns a grounded response, or a justified refusal, together with a
receipt of what it used. **It does not exist yet** ([below](#what-exists-now)). The names Athena,
Eros (the collective formative organization) and Hephaestus (a planned solver and code
application) carry no machinery.

## What exists now

The source and receipt snapshot below is **October 6, 2026**, checked at
[`3c67beee`](https://github.com/brandonrdug/holonics/commit/3c67beee7f656798f912c974f12c482ea12c5e42).
The September 24 reset retained what functions; earlier implementations remain in git history.
[CONSTRUCTION_STATE](CONSTRUCTION_STATE.md) owns current position, and
[THE_REBUILD](docs/plans/THE_REBUILD.md) owns order. This README routes those owners rather than
repeating their measurement ledger.

| Present construction | Evidence and limit |
|---|---|
| The Holon law, exact ratio/ring arithmetic, frames, screws, winding, navigators, receivers and release | [`crates/holonics`](crates/holonics), with the [operator contract](docs/ELEMENTARY_OBJECTS.md#operator-contract) and Lean counterparts |
| HNN host and resident CUDA word, source moments, paired adjoint, comparison, deposition and reception carry | [`holonics::hnn`](crates/holonics/src/hnn), [`holonics-cuda::hnn`](crates/holonics-cuda/src/hnn); [carry receipt](research/records/2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md). Per-law parity is scoped to its actual fixture. |
| Exact source entrance through the producing `Encoded` chart; the card steps by located digits | [Entrance tests](crates/holonics/tests/source_entrance.rs), [encoding/ingest receipt](research/records/2026-10-05_THE_FIELDS_ENTRIES_TAKE_ONLY_THE_ENCODED_SOURCE.md). A refused occurrence moves nothing; a failed device open is discarded. |
| Host save and cold continuation of contemporary material, charts, clock and arrived comparison | [Cold-restore tests](crates/holonics/tests/resident_cold_restore.rs), [PR #384](https://github.com/brandonrdug/holonics/pull/384). This establishes the declared host continuation cases; card passage restore and broader adaptive retention keep their own gates. |
| Nonlinear loaded parametron with an executed-domain certificate and carried pump cycle | [Quartic domain](research/records/2026-10-05_THE_QUARTIC_STEP_NEEDS_AN_EXECUTED_DOMAIN_BEFORE_A_LOCK.md), [continuing component](research/records/2026-10-05_THE_LOADED_COMPONENT_CARRIES_ITS_ADMITTED_PUMP_CYCLE.md). The ordinary rounded word and whole nonlinear field are separate joins. |
| Located-key release and two-sided repair on declared known-truth terrain | [Pair comparison](research/records/2026-10-05_THE_PAIR_GAIN_IS_THE_JOINED_BANKS_LOG_DETERMINANT.md), [reflection repair](research/records/2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md). These receipts do not establish useful learned physical repair. |
| Landmark-tree compression and receiving populations | Historical scoped readings in [CONSTRUCTION_STATE](CONSTRUCTION_STATE.md#measured-receiving-faces); the count tree earns most of the text compression. Compression scores are not generation acceptance. |
| Lean mathematics and the expression atlas | [`lean/`](lean/README.md), [`docs/atlas/`](docs/atlas/README.md); each law keeps its hypotheses, consumer and epistemic grade. |

**Athena remains incomplete.** Meaningful autonomous physical repair and a useful decoded boundary
have not passed their acceptance. A native response must join its producing chart, source clock,
learned receiving material, preserved remainder and continuing carry. Teacher-forced next-cell
scores, component tests and restore fixtures each establish their own narrower claim. The actual
output, whole, decides usefulness; the spent diagnostic split stays spent, and the separate
evaluation partition stays closed.

**The next learning receipt must distinguish the relations learned.** Keep each source head,
producing chart, cohort, seed, damage and mechanism with its own result. The
[pair-gain receipt](research/records/2026-10-05_THE_PAIR_GAIN_IS_THE_JOINED_BANKS_LOG_DETERMINANT.md)
explicitly measures regressions on repeated request spaces; the
[reflection-repair receipt](research/records/2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md)
uses separate damage/read cohorts. Their totals do not form one U6 acceptance bar. A result
dominated by the common class does not establish acquired relations: report the distinguishing
damaged cells and intact clamps, compare the same declared source/receiver task before and after
reached deposition on the respective contemporary material, and check the retained result through
cold continuation. The physical consumer still
needs the charted source-opening and receiving-error pullbacks joined at their producing operands;
the published opening balance alone does not establish that learning path. This public status
credits completion only at published source and consuming receipts.

The [foundation supplement](docs/plans/HNN_ATHENA_FOUNDATION.md) joins dynamic geometry, asymmetric
potentials and receiver-relative tolerance to the existing owners. An asymmetric potential is a
constitutive proposal; its generic adaptive HNN consumer is not established by the symmetric
quartic component.

| Current responsibility | Existing issue and acceptance |
|---|---|
| Codex HNN coordinator: host capacity, rekey, save, Lean and integration | [#73](https://github.com/brandonrdug/holonics/issues/73), formal obligations [#62](https://github.com/brandonrdug/holonics/issues/62); continuation must preserve the source/clock/remainder relation. |
| Codex CUDA worker: device consumers and one build queue | [#76](https://github.com/brandonrdug/holonics/issues/76); consume the same host relation, with actual capacity, refusal parity and card restore receipts. |
| Codex physical-repair worker: producing chart, source clock and receiver decoding | [#73](https://github.com/brandonrdug/holonics/issues/73), product acceptance [#148](https://github.com/brandonrdug/holonics/issues/148); show the learned physical output and its receipt. |
| Codex mathematical implementation, with Claude derivation/review | [Targets and extraction #146](https://github.com/brandonrdug/holonics/issues/146), [Hodge #20](https://github.com/brandonrdug/holonics/issues/20), [tower #22](https://github.com/brandonrdug/holonics/issues/22), [junction #23](https://github.com/brandonrdug/holonics/issues/23), [neck sources #32](https://github.com/brandonrdug/holonics/issues/32); exact formal scope stays in [#62](https://github.com/brandonrdug/holonics/issues/62). |

RH, Hodge, complex Euler/Navier–Stokes and BSD remain attached to the same construction.
The [comma/ghost record](research/records/2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md)
joins exact nonclosure and turn/boost normality with six explicitly owed statements. Recursive
coarse-graining and the RH source-law join remain pending research, alongside the Navier–Stokes
response bound and the Hodge receiver. The comma calculations and gap interpretations prove no RH
claim. The [program index #63](https://github.com/brandonrdug/holonics/issues/63) routes this breadth.

## What has not worked

Failures are published with the same care as results.
- **Rings and contacts on text.** Campaign 2's ring and contact laws are lawful and pass parity,
  but add no bits on text.
  [Record](research/records/2026-09-26_CAMPAIGN_TWO_THE_RINGS_AND_CONTACTS_ARE_LAWFUL_AND_ADD_NO_BITS_ON_TEXT.md)
- **The loaded resonator** closes its power balances, but loses to the default HNN by `8/16 + ε`
  bits over the development cells, before its own `887`-bit material description is charged.
  [Record](research/records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md)
- **Rejected receivers.** Each is listed with its receipt among the
  [retired choices](research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md#h-retired-choices):
  - a Born-rule receiver failed its development criterion, and stays only as a measured receiver;
  - second-arrival founding lost, and was retired;
  - a per-port conversation reader lost to the flat stream, and was retired.
- **The earlier machine.**
  - A C++/CUDA engine was archived on August 7, after five days.
  - A prototype HNN machine and its Athena prototypes (August and September) were retired at the
    September 24 reset.
  [Lessons from those prototypes](research/records/2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md)
- **Withdrawn claims.** [RETRACTIONS](docs/RETRACTIONS.md) records the claims withdrawn and why.
  One example is a theorem "renderer" whose output bodies had been authored, not inferred.

## Where everything is

**Guides** (current law, in the elementary objects' vocabulary)

| Guide | Subject |
|---|---|
| [THE_MACHINE](docs/THE_MACHINE.md) | The HNN in its geometry and its law; start here |
| [ELEMENTARY_OBJECTS](docs/ELEMENTARY_OBJECTS.md) | The vocabulary and the operator contract: each operation with its owner |
| [HOLON](docs/HOLON.md), [HNN_FORMULA](docs/HNN_FORMULA.md) | The computational Holon; the full law the HNN implements, including the source and release contract |
| [RECEIVER_HOLARCHY](docs/RECEIVER_HOLARCHY.md) | Receivers, receipts, perspective, flux and compression; probability as a receiver's geometry |
| [HOLONIC_NOTATION](docs/HOLONIC_NOTATION.md) | Kets, bras, faces, frame transports and ports |
| [HELICAL_GEOMETRY](docs/HELICAL_GEOMETRY.md), [WINDING_CARRY_AND_PLACEMENT](docs/WINDING_CARRY_AND_PLACEMENT.md) | Screws, helices, carry, lock addresses, cell holonomy and towers |
| [CONSTRAINT_MODES_AND_RECEIVER_FACES](docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md), [ANALYTIC_FLUX_AND_RECEIVING_BASINS](docs/ANALYTIC_FLUX_AND_RECEIVING_BASINS.md) | Constraint modes, chart transitions and analytic receiving basins |
| [HOLONIC_FLUID_CONSTRUCTION](docs/HOLONIC_FLUID_CONSTRUCTION.md), [FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS](docs/FLUID_REFLECTION_AND_CONCENTRATED_INTERIORS.md) | Euler, stress, diffusion, lightning and concentrated interiors from the half-turn and Holon interactions |
| [MASS_ENERGY_AND_CAUSAL_TRANSPORT](docs/MASS_ENERGY_AND_CAUSAL_TRANSPORT.md) | Mass–energy, causal transport and generative intelligence |
| [FORMAL_FRAMEWORK](docs/FORMAL_FRAMEWORK.md) | How the Lean framework's subjects connect |

**Plans and position**
- [THE_REBUILD](docs/plans/THE_REBUILD.md) gives the order of work and the forward plan.
- [CONSTRUCTION_STATE](CONSTRUCTION_STATE.md) gives the current position.
- The [issues](https://github.com/brandonrdug/holonics/issues) carry each open step. #63 is the
  parent, and #62 lists every owed formal statement.

**Formal mathematics.** [`lean/`](lean/README.md) is one Lake package with two libraries:
- `Holonics`, the foundation, is the import closure of `Holonics.Framework`;
- `HolonicsResearch` holds everything else, including the zeta, Hodge, fluid, elliptic-curve and
  gauge work.

**Code**
- [`crates/holonics`](crates/holonics) is the host library. Its modules are `holon`, `ratio`,
  `geometry`, `navigator`, `receiver`, `holarchy`, `aeon`, `compression`, `physics` and `hnn`.
- [`crates/holonics-cuda`](crates/holonics-cuda) is the CUDA driver and the resident HNN.
- [`accelerators/`](accelerators/README.md) holds device-only builds.

**Research**
- [Research reading routes](research/records/README.md) route the dated records from July 10, 2026
  on. Each route starts from a guide and follows its records to
  their owners.
- The [research entry](research/README.md) explains what each research surface is for.
- The [notebook](research/notebook/README.md) holds symbolic derivations and local Lean checks.
  [`hnn_design`](research/notebook/hnn_design/README.md) holds the HNN's measurement harnesses and
  receipts.
- The [papers](research/papers/README.md) are Typst sources and rendered PDFs and plates.
- [`research/design`](research/design) and [`research/fixtures`](research/fixtures) hold design
  studies and fixed inputs.

**Atlas and history**
- The [expression atlas](docs/atlas/README.md) holds the derived expressions as tab-separated
  rows. It is written for the agents, but anyone can search it by object, operation or classical
  name.
- The [canon](docs/canon/README.md) is the historical doctrine (45 dated files), read through the
  elementary objects.
- [RETRACTIONS](docs/RETRACTIONS.md) is the capability and retraction history.
- [External resources](docs/references/EXTERNAL_RESOURCES.md) lists the outside sources the
  research draws on.
- The pre-reset tree is [`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734).
  Branch leftovers are on `archive/leftovers-2026-09-24`, and an Apple-silicon (Metal) port is on
  `codex/apple-silicon`.

**Searching.** Search a subject's objects and its operations, not just its name:

```bash
rg -i 'contact|slip' docs/atlas/                   # the atlas, by object or operation
rg -i 'Farey|Ford' docs/atlas/                     # the atlas, by classical name
rg --files research/records | rg -i 'helic|torus'  # records by title
rg -n 'replicator' docs lean crates research       # everywhere current
git grep -n 'NormalizedKernel' 13f8c734            # the pre-reset tree
```

## Reading routes

- **Machine learning or compression.** Start with [THE_MACHINE](docs/THE_MACHINE.md), then the
  [HNN routes](research/records/README.md#hnn-the-continuing-object-and-its-consumer), then the
  [landmark tree](research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md)
  and the [population](research/records/2026-09-27_THE_EGG_IS_A_GENERATORS_GENOME_SELECTION_IS_BAYES_AND_THE_FACES_OF_INTEGERS_ARE_MOIRES_OF_GRATINGS.md).
  Historical authored arithmetic families were retired under the no-catered-machinery law.
- **Mathematics.** Start with [ELEMENTARY_OBJECTS](docs/ELEMENTARY_OBJECTS.md), its
  [targets](docs/ELEMENTARY_OBJECTS.md#the-targets) and the
  [RH upper-bound record](research/records/2026-09-14_THE_HALF_CENTRED_FACE_AND_THE_DE_BRUIJN_NEWMAN_UPPER_BOUND.md). To find any expression by name, search
  the atlas's `targets.tsv` and `arithmetic.tsv` (`rg -i 'Farey' docs/atlas/`).
- **Physics.** Start with the [fluid construction](docs/HOLONIC_FLUID_CONSTRUCTION.md),
  [mass–energy](docs/MASS_ENERGY_AND_CAUSAL_TRANSPORT.md) and the atlas's `physics.tsv`.
- **Formal methods.** Start with [`lean/README`](lean/README.md) and `Holonics.Framework`.
- **GPU and exact computation.** Start with `crates/holonics-cuda` and the hardware law in
  [CLAUDE.md](CLAUDE.md#the-objects-governing-laws).

## How the work is done

- **Direction and decisions.** Brandon sets the direction and acts as a lens on the research. The
  agents make the technical and mathematical decisions and record each, with its reason, where its
  law lives: in its owner, its guide or a dated record.
- **Practice.** The working practice is written for the agents in [CLAUDE.md](CLAUDE.md) and
  [AGENTS.md](AGENTS.md). It covers exact arithmetic, "recover before implementing", deletion as
  consolidation, and privacy.
- **Checks.** A change passes `cargo check`, then the tests of the laws it touched. A kernel change
  also runs the GPU suite alone on an idle card, and a Lean change runs the Lean build.
- **Execution.** Codex keeps one build/admission queue. Reuse receipts for unchanged checked inputs;
  project changed work from measured cost, enforce the fixed deadline and report an overrun as
  incomplete. The [waiting audit](research/records/2026-09-30_AUDIT_WAITING_DEADLINES_AND_CONCURRENCY_THE_WORKERS_BLOCKED_ON_THEIR_OWN_RUNS.md)
  records the repeated waiting and raised-limit failures this practice addresses.
- **Formal counterparts.** A new law lands with its Lean counterpart, or names the obligation it
  leaves in #62.
- **What we have learned about working this way.** The
  [workflow record](research/records/2026-09-27_THE_WORK_READ_FROM_ITS_CONVERSATIONS_AND_HISTORY_CONVERGES_WHERE_ACCEPTANCE_IS_FIXED_BEFORE_THE_CLAIM.md)
  reads our conversations and history: what went wrong on the way to a product, what worked, and
  the practice adopted.
- **Private data.** The conversation datasets behind Athena's measurements live in an ignored
  `.local/` directory. Only counts, bits and hashes are published.
- **History.** The work began in May 2026 in a private laboratory repository. Its papers,
  mathematics corpus and 305 of its records were brought here when this repository began on
  August 3, 2026.
  - A C++/CUDA engine was archived after five days.
  - The work moved to Rust and Lean.
  - On September 24 the repository was reset to what functions, and it is being rebuilt one law at
    a time.

### Reading a claim

Every material claim carries one truth-status grade, defined in
[EPISTEMIC_GRADES](docs/canon/EPISTEMIC_GRADES.md):
- `definition`
- `project-postulate`: a discipline the project adopts, not a theorem
- `proved-standard` or `proved-derived`
- `established-bounded`: a result for a declared construction, with its evidence
- `conditional`
- `interpretation`: a proposed correspondence with a falsifier, not an identity
- `conjecture`
- `counterexample`
- `open`
- `historical`

Records are dated history, written in the vocabulary of their date. The
[elementary objects](docs/ELEMENTARY_OBJECTS.md) govern where the two differ; for example, a
record's "generator" is now a navigator and its "session" is now an aeon.

## Building and checking

You need a Rust toolchain for edition 2024 (1.88 or newer) and, for the formal library, Lean `v4.33.0` through `elan`, with
Mathlib, CSLib and PhysLib fetched by Lake. The CUDA crate builds without a CUDA toolkit: it
reports that its kernels are absent and refuses to open a card.

```bash
cargo check --workspace --all-targets          # everything compiles
cargo test -p holonics                         # the host laws
mkdir -p .local
flock .local/gpu.lock cargo test -p holonics-cuda -- --include-ignored --test-threads=1
bash tools/lean_check.sh                       # the Lean foundation, Holonics
bash tools/lean_check.sh HolonicsResearch      # the research library
```

## License

Holonics is dual-licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.
Third-party material keeps its own notices.
