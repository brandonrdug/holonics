# Holonics

Holonics is Brandon's research programme: a mathematical, physical and computational framework
for how situated things exist, interact, change and become observable. It starts from the reality
of difference: nothing is observed except as a difference that some receiver can read. Its
ambition is a theory of everything in that sense, and a machine built from it that is useful on
ordinary hardware. The ideal is 20 W, about what a brain uses: cost should follow the causal
extent actually in play, not the size of what is stored.

Brandon works on it with two AI agents, Claude (Anthropic) and Codex (OpenAI), which write most of
the code, proofs and records under his direction. The work is public so that anyone who finds it
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

**The machine is geometry.** The HNN (Holonic neural network) is a continuing field of complex
parametron rings, annular rings that store, oscillate and lock, joined by helical pair contacts,
which slip, dissipate and address. Information is phase and winding on the rings. Learning deposits
into the material of the contacts a comparison actually reached. A weight matrix is one chart of
this object, never the object.
[The machine](docs/THE_MACHINE.md) · [the HNN formula](docs/HNN_FORMULA.md) ·
[helical geometry](docs/HELICAL_GEOMETRY.md) · [winding and carry](docs/WINDING_CARRY_AND_PLACEMENT.md)

**Memory is a quotient, not a tape.** What a system retains is the least it must keep so that
every future it admits reads alike: the future-sufficient quotient of its constitution. It is not
a log of events, and not a replay.

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

As of September 27, 2026. The repository was reset on September 24 to what functions, and is being
rebuilt from the elementary objects. Everything earlier is in git history.
[Construction state](CONSTRUCTION_STATE.md) · [the rebuild plan](docs/plans/THE_REBUILD.md) ·
[tracking issue #63](https://github.com/brandonrdug/holonics/issues/63)

| Built | Where |
|---|---|
| The Holon law and its operators: exact ratio and ring arithmetic, geometry (frames, screws, winding), navigators, receivers, standing and release | [`crates/holonics`](crates/holonics) |
| The HNN's first two campaigns (source moments, rings, contacts, the receiving word, deposition), on the host and resident on an NVIDIA card, each law with host/card parity | `holonics::hnn`, [`crates/holonics-cuda`](crates/holonics-cuda) |
| The landmark tree: a context-tree-weighting receiver stored where its paths part, whose count registers carry at a ceiling | `compression::landmark::context`, `kernels/tree.cu` |
| The receiving population of eggs: dormancy, death as exchange, birth, composition at ports, an evolved prior | `receiver::population` |
| Terrain with known truth: moiré sheets, tree sources, rotor cribs, switching aeons, digit products and prime streams | `holarchy::terrain` |
| The Lean mathematics: 1,514 files and over 22,000 theorem and lemma declarations on Mathlib, with no `sorry` and no declared axioms (12 finite checks use `native_decide`) | [`lean/`](lean/README.md) |
| The expression atlas: 2,697 derived expressions, identities, bounds and counterexamples, each with its owner and grade | [`docs/atlas/`](docs/atlas/README.md) |

**Measured.** A *cell* is one symbol of a stream: a byte, or a letter marking a channel or a
section. Code lengths are in bits, and `ε` is the remainder below the reading's grain of 1/16
bit. *Held out* means the later part of a stream, scored after that measurement's choices were
made on the earlier part. A tail once scored becomes development data for later choices. The
comparisons are classical online compressors: order-0 and order-1 byte counters, and PPM-2
(prediction by partial matching with two bytes of context). The text measurements use Brandon's
private conversation data, which is never published: only its counts, bits and hashes are.
- **Standing cut (text; 6,148 cells, the last 1,190 held out).** The full HNN codes
  `3 + 1/16 + ε` bits a cell held out, strictly below order-0, order-1 and PPM-2. This is the
  landmark tree weighed with the rings' wave.
  - The tree does nearly all of it. The wave earns `5 − 13/16 − ε` bits over the held-out cells
    after its selection charge, and has not paid for its computation.
  - This tail has since been used in development.

  [Record](research/records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md)
- **Wide cut (text, `2²⁰` cells, the last `2¹⁷` held out).** The landmark tree alone, at depth
  `48`, codes `1 + 15/16 + ε` bits a cell, below PPM-2. This counts contexts only; it is not the
  full HNN.
  [Record](research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md)
- **Curated conversation stream.** Channels are ports, turns are epochs and conversations are
  aeons. Against the flat stream of the same bytes, the population's code differs by
  `−1820 + 9/16 + ε` bits on its development cells and by `−535 + 8/16 + ε` bits on the held-out
  tail. This is on the development partition only, and says nothing yet about answers.
- **Terrain with known truth.** The true family is among the population's declared candidates. The
  test is that selection finds it and pays only its description:
  - base-10 digit products code at exactly their truth, `108857 + 3/16 + ε` bits, against the
    landmark tree's `273520 + 7/16`;
  - a prime stream codes in `15 + 9/16 + ε` bits, the key's description, against the tree's
    `161780 + 3/16`.

  [Record](research/records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md)

**Not yet.** Athena answers nothing today. The next steps are fixed in advance in the
[forward plan](research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md#the-forward-plan-september-27):
1. release text from the population (F4);
2. build Athena-0 (F5), whose responses Brandon judges blind against a retrieval control.

The data's evaluation partition stays unread until that judgement, and is read once. The owed
formal statements are listed in [#62](https://github.com/brandonrdug/holonics/issues/62).

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
- [Research reading routes](research/records/README.md) are the best way into the 1,253
  dated records, from July 10, 2026 on. Each route starts from a guide and follows its records to
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
cargo test -p holonics-cuda -- --include-ignored --test-threads=1  # on an idle NVIDIA card
bash tools/lean_check.sh                       # the Lean foundation, Holonics
bash tools/lean_check.sh HolonicsResearch      # the research library
```

## License

Holonics is dual-licensed under [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.
Third-party material keeps its own notices.
