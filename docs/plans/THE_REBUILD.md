# The rebuild

**Status: active, September 28.** Tracked in #63. This plan is the one order. The laws live in their
guides and owners; [CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md) is the position; the
[construction record](../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md)
keeps the history this plan replaced: steps 0–8, the step-4 design and its five campaigns, and the
forward plan F0–F6 as it stood.

## The unified plan (September 28)

[definition; agent-inferred] Brandon, September 28: "tie together all of our plans and designs and then
proceed with the necessary next items", so that the codebase does not become overgrown or frayed.
Three read-only audits of that day (plans and guides; Rust owners and consumers; Lean, atlas,
notebook, records and #62) located the fraying, and GPT-6 Astra reviewed the draft against them.
Its corrections are folded in.

### 1. One Holarchy, its laws, and what is not yet joined

- **The architecture** [interpretation]. The machine is one Holarchy ([THE_MACHINE](../THE_MACHINE.md)).
  Its receiving role is a population: the receiver mixes its constituent families by Bayes, the
  discrete replicator. The landmark tree is one family; a field-derived predictor (today the combined
  tree-and-wave face `q_C`) is another; terrain navigators and composed eggs are others. This settles
  the containment the guides stated both ways (the population inside the field, the field inside the
  population): the population is the receiving composition at the field's port. It does **not**
  establish that the population or its statistical families are Holons joined at power ports; that
  join is open (§4).
- **The laws, each under its own hypotheses.**
  - Quadratic port dynamics obey `Holon/Deposition.learned_energy_balance`,
    `dE/dτ = −⟨e, Re⟩ + ⟨e, Le⟩ + ⟨e, Bu⟩ + ½⟨x, Q̇x⟩`, whose kinematic reading is the motion
    primitives (objects §3, `Geometry/Motion`) where `Q` is invertible and `R` symmetric. Singular
    storage and discrete junction scattering keep their own laws.
  - Statistical receivers obey their own update and code identities: the tree's counts (a node's
    split moves by `a′ − a = (y − a)/(N + 2)`), the population's telescope `∏_t q_t = Σ_f π_f L_f`,
    dormancy's fixed share over switching paths. They carry no stated energy, units or ports.
  - Deposition governs every reached change of constitution in both.
  - Their physical interconnection is an explicit construction obligation, not a consequence.
- **Retention** is the future-sufficient quotient (action-sufficient where the machine acts), taken
  at aeon boundaries (objects §8). The HNN's structural collapse releases learned material and cannot
  be reopened; species collapse keeps seeds and shares and can split. Each keeps its recoverability
  condition.
- **Release** is one decision law whose arms are the certified draw, the threshold commit, the probe
  and the typed refusal. Today three rules realize it apart (§3, U3).
- **Charts.** Text, arithmetic, motion and image are boundary charts of the one machine. Brandon,
  September 28: the physical computation is the ideal, and framing the machine as text prediction
  makes the problem harder. The construction proceeds from the motion. Text is one chart, and its
  product, Athena-0, keeps its independent acceptance (the gates below).

### 2. What exists, read against it

| Part | State |
|---|---|
| Landmark tree | earns: standing cut `3 + 1/16 + ε` a cell held out; unseen agent text about `1 + 12/16` bits a byte |
| Population | codes known-truth terrain at its truth among declared families; the egg alone is F0's byte predictor; no library owner calls it (the harnesses do) |
| Field (rings, contacts, word, deposition, wave) | lawful on host and card; `5 − 13/16 − ε` held-out bits on the standing cut through `q_C`; campaign 2 and the loaded resonator added none; its wave and resonator states live inside one word |
| Chase (F6) | reception at truth on 16 arenas; action captures in 164 ticks against 3,704 and 366; the at-once acceptance failed; its decision rule is a capture-basin planner, not the specified log-odds commit |
| Retention | Lean `Foundation/Standing`; Rust `receiver::standing` is used only by tests; two collapses do not use it |
| Release | three rules: `receiver::release` (the HNN), the population's draw pipeline, the chaser's decision |
| Mixtures | five constructions, sharing the ideal telescope but differing in conditioning, transitions and carriers: digit-local joins (`JoinTree`, `FaceJoins`), the whole-cell `receiving::Mixture`, the population's telescope with death, dormancy's fixed share over switching paths, and the retired `LocalMixture` |
| Motion primitives | proved in `Geometry/Motion`; no Rust consumer |

### 3. The order

Each item fixes its owners, its consumer equation, its acceptance and its failure branch before it is
measured, and keeps every inherited gate below verbatim.

#### U0. Consolidate (no new law) — carried out September 28

The receipts are in [CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md) and the commits that name U0.

The deliverable is a smaller, consistent tree. Acceptance: each retirement names the owner that keeps
its law, or writes the law into its guide or record first; nothing live consumes what is retired;
every duplicated law has one owner that the others cite; the gates pass (check, tests, Lean, atlas).
- **Rust.** Retire, with exports, tests, registrations and atlas rows in the same commit:
  `population::local` and `hnn_population_local` (its executed floor's switching bound is recorded
  first); `hnn_tokens`; `hnn::born` and `hnn_born` (Lean `HNN/BornFace` stays); F1's
  `population::{words, sectioned_words}`, `terrain::words` and `hnn_word_probe`;
  `Mixture::switching`; `navigator::reflection`; `holon::reaction`, `landmark::identity` and
  `landmark::primitive` with `aeon::zeta`, each after its unformalized argument is written down;
  `landmark::constraint`; `exponentiated::transport`; the CUDA word path's unused wrappers; the
  completed drivers `hnn_diagnose`, `hnn_lattice_growth`, `hnn_curated`, `hnn_terrain`,
  `hnn_release_terrain` (its checks kept as law fixtures). Their library dependencies stay: the crib
  helpers and `grain_logits` feed live paths. `hnn_population` stays, with its live routes. Rename the
  half-turn (`swing` → `half_turn`), junction scattering (`junction_swing` → `junction_scattering`),
  the chase's `Policy` and `Constitution`, `Founding.epoch` and the "sign generator".
- **Lean.** One owner, cited by the rest, for the half-turn word law, the sling, the moving-metric
  energy law, Bayes and KT; the junction's declarations renamed; retired-crate docstrings repinned;
  `TARGETS_FORMAL_CATALOG.md` retired.
- **Guides and indexes.** One owner per definition; the operator contract gains the population and
  the terrain; the old Swing wording goes; stale status sections are rewritten; this plan replaces the
  old order, and the construction record keeps the history; the measurement protocol and the guards
  move to THE_MACHINE; #62 becomes the current obligation list; the atlas README states its tags and
  shards; the notebook and records READMEs become routes.
- **Kept, with an actual consumer or a date.** `receiver::standing`, `compression::face_map` and
  `hnn::modes` (a test-only chain) and `receiver::release`'s unconsumed half and `causal_chord` are
  kept only until U2 and U3 decide them, by a named call or by retirement; no other retained subtree
  is exempt. `physics::*` is kept for the fluid operators U4 names; the rest of it is decided in U4.

#### U2. One retention contract, and F0's memory

Owners: `receiver::standing` (Lean `Foundation/Standing`), `hnn::retention`, `population::species`,
`compression::landmark::context`.
- **Contract.** Both collapses share the abstract factorization law (`standingLaw_exists_iff_future_factors`)
  with action-sufficient futures, through their own carriers: the HNN's structural collapse keeps its
  refusal to reopen; species collapse keeps seeds, shares and its certified future. No dense global
  representation is forced on either.
- **F0's memory experiment, early** (the measured product obstruction: 2,653 bytes of standing a cell
  read). Merge the tree's contexts where the decoding and continuation squares hold under every
  admitted action and deposit, not merely where present faces or validation code agree; then measure
  the storage.
- **Acceptance.** The collapses' laws and tests unchanged; on a fresh F0 split, pinned before running
  with its standing budget, the merged tree's standing per cell falls strictly while its conditional
  byte-and-stop code stays within the pinned margin of the unmerged tree's. The squares are checked, or
  the merge is refused for that context.
- **Failure.** The standing stays; the refused contexts and their separators are reported.

#### U3. One release contract

Owners: `receiver::release`, `population::{releasing, sampling, family_release, text_release}`,
`population::chaser`.
- **Contract.** Every emission is a `ReleaseReturn` of one decision law; its arms are the certified
  draw (the inverse CDF), the threshold commit, the probe and the typed refusal. `P_release = P_scored`
  is kept, and so are the stop law, the unresolved draw mass and the refusals. The chaser's rule is
  declared as what it is, a capture-basin commit with an information probe; the specified sequential
  test on accumulated log-odds is either built as its own arm or the F6 law is amended to the built
  rule, explicitly.
- **Acceptance.** Every existing receipt is reproduced exactly through the one law: the face laws, the
  stop law, the unresolved draw mass, the refusals and the full receipts of F4's views and the chase.
  The inverse-CDF theorem does not turn selectively emitted mass into the full mixture, so no claim
  rests on it.
- **Then** F4's second stage, `Q_R` (its gate below).

#### U1. One machine: the receiving composition at the field's port

Owners: `hnn::receiving`, `hnn::reference`, `receiver::population`, `compression::landmark::context`.
It consumes U2's and U3's contracts.
- **Consumer equation.** The HNN's receiving face is the population's face over the two families it
  already weighs, the tree and the combined face `q_C` (tree grain logits plus the wave), with matched
  priors, the same per-cell prequential order (deposits inside a receiving window included), one
  authoritative tree update, and the existing combined-face covector, phase comparison and
  window-level wave deposition. `q_C` lives in `ℚ(θ)`, so the family contract carries an algebraic
  face or an enclosure, or a declared rational chart with its residual. Zero likelihood stays exact
  death, never a positive floor.
- **Acceptance.** First, exact identities on small fixtures between `receiving::Mixture` and the
  population on the declared families. Then, on the standing cut, the two executions' codes differ by
  at most a bound derived from their charts (β rounding against the enclosures), pinned before the
  run, host and card. Aggregate agreement alone is not acceptance.
- **Then F2's adoption gate, unchanged:** a field family is adopted for text only if the charged
  population code is strictly shorter than without it and its complete work fits the declared
  response and passage budgets (the gate below).
- **Failure.** The separating term is named, and the two mixtures stay, recorded.

#### U4. Motion running

Owners: a Rust motion owner in `geometry` (the move pair `(v, v′)` over `ℚ(i)`, its kind and its pivot
where one exists), `holarchy::terrain::{chase, pursuit}`, then the named operators of `physics::fluid`.
- **The rebase** (with U1, independent of it). The chase carries `(v, v′)` undivided; its traction law
  `|v′ − v|² ≤ r²` reads as the disk of admitted moves; walls, speed caps, traction, demand timing and
  held slips are preserved; a zero opening velocity and a stop are explicit cases with no division and
  no pivot. Acceptance: every chase receipt is unchanged.
- **The measured next failure first.** The machine misses the truth-only least on 5 of 16 seeds while
  its opening fibre is wide; that is the next loop's subject, before any new terrain.
- **F6's switches and attribution** follow U2 and U3 (they touch the action-sufficient future and the
  release law).
- **F6's action acceptance stays as written, and its failure stays visible.** The next measurement
  is on a fresh, unfiltered population of seeds with its aggregate capture, regret and win/tie/loss
  criteria declared before the run. The subset of seeds that admit a win beyond every control is
  reported separately, as a conditional reading, never as the acceptance.
- **Then** a fluid-cell terrain from the named `physics::fluid` operators (the pressure as the
  incompressibility grip, doing no work; viscosity as friction on the strain; time advance and the
  pressure solve, which `physics::fluid` still owes), then the motor chart (its gate below).

#### U5. Clocks are aeons

A receiving window is an `aeon::Epochs` reading, a pump period an `aeon::Cycle`, and the machine's
clocks instantiate `navigator::Clock`. Acceptance: the section and carry correspondence is proved or
checked exactly, and every exposure is at parity.

#### U6. The text chart

F0's next loop is U2's memory experiment; F4's second stage follows U3; F5 follows F0 and F4. The
curated source gains its intervals (source contract item 9), measured as a charged comparison
against the source without them. Their gates below are unchanged.

#### U7. The targets, alongside

Every existing target obligation stays (RH, Hodge, complex Euler and Navier–Stokes, BSD, their Lean
and #62). The motion primitives add these, each graded and each with its Lean piece:
- Navier–Stokes as free fall on the volume-preserving rearrangements (Arnold), the pressure as a
  workless grip, viscosity as friction on the strain alone (frame indifference); helicity conserved
  without friction; vortex stretching as the strain boosting the vorticity (Beale–Kato–Majda);
- phase volume changing only through the boost's trace;
- purity, for RH and Hodge: the boost pinned by the weight, the turn free (Deligne's torus);
- the de Bruijn–Newman flow: de Bruijn's strip law `y² ≤ Δ² − 2t` for polynomials, the barrier's
  winding as conservation of faces across a surface;
- Turing's method as the clocked turn (ticks on the line against the total winding); Sturm and
  Prüfer shooting as the leap.

#### U8. Hardware and curation

F3's gate (below) when the product deadline needs the card; parity for every change to the existing
resident HNN made by U1, U3 or U5 (the GPU suite, alone on an idle card); Lean curation (#147);
equation extraction (#146).

### 4. The open joins and the learner's necessities, each disposed

| Item | Disposition |
|---|---|
| The tree and population as Holons joined at power ports | open; U1 names its missing maps and balances; owed in #62 |
| Campaign 3's descended lattice chart, card parity, finite-deposit stability, persistent dormancy across an aeon and the concrete-ring bridge | deferred: built when U2 decides `hnn::modes`; owed in #62 |
| Mode release, FOUND by interconnection, far-field moment quotient `V_m` | deferred to after U3; owed in #62 |
| Encoding, Context and JointPrediction (joint against marginal witnesses) | U6, after U1; the continuation-transport discovery of F1's after-note stays live |
| Concrete-tick diamond, complete word-sensitivity certificate | owed in #62 |
| The carry word's runtime consumer, relative completeness, action-sufficient descent in Lean, Hearing's consumer | U5 (carry word); owed in #62 (the rest) |
| F4's decoder, producing keys, causal provenance, grain and fibre, release squares | U3 and F4's gate |
| F5's cold restore, atomic native transition, truthful health receipts | F5's gate |
| Moving-continuum electromagnetic reception | deferred; owed in #62 |
| Persistent motion of the wave and resonator between words | open: the word-local states leave at the word's end; built only with a consumer and a falsifier |
| Timing and intervals | U6 (source item 9), charged |
| Calibration (predicted against realized surprise) | U3's receipts report it |
| Gain by precision, and the hazard ladder | U2 (deposition step by reading precision) and U1 (the switch rate), each with its acceptance before adoption |
| Regeneration from the quotient | kept as the identity that regenerated passages add no evidence in expectation; no training on them |
| The ring-search experiment (rings as the search for keys, not as predictors) | restored: after U1, on the moiré and rotor terrains, it measures search work against enumeration and menu propagation, and basin mass against a declared prior, with a nonlocking control ([learner record §2](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#2-the-rings-as-the-search)); residual-founded transport discovery first ([§14.1](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#141-birth)) |
| The F6 law's threshold commit against the built planner | U3 |

### 5. The waves

- **Wave A:** U0, three workers on disjoint paths (Rust; Lean, atlas and #62; guides and indexes),
  with this plan written by the primary.
- **Wave B:** U2's contract and F0's memory experiment; U3's contract; U4's rebase (disjoint).
- **Wave C:** U1, consuming U2 and U3; then F2's gate and the ring-search experiment; U4's next loop.
- **Wave D:** U5 and U6; U8's parity with each change to the resident HNN; U7 alongside every wave.

### 6. The former labels

| Former | Now |
|---|---|
| Steps 0–3 | complete (construction record) |
| Step 4 (the HNN law), campaigns 1–2 | built; U1–U5 join it |
| Campaign 3 (modes, dormancy, founding) | U2 decides `hnn::modes`; the rest in §4 |
| Campaign 4 (the motor chart), F6 | U4 |
| Campaign 5 (encoding, context, prediction) | U6; §4 |
| F1 (words) | its failure branch holds: bytes stay; the continuation-transport after-note stays live (§4) |
| F2 (the field as a family) | U1 and its gate |
| Step 5, F3 | U8 and its gate |
| Step 6 | U7 |
| Step 7 | U0, U8 |
| Step 8, F4, F5 | U3, U6 and their gates |
| F0 | U2's memory experiment, U6 and its gate |

## The gates (inherited verbatim)

[definition] The product and terrain gates of the forward plan of September 27, kept word for word:
the U-items above consume them and change none. Owners their receipts name that U0 retired
(`LocalMixture`, `hnn_tokens`, F1's word family, `hnn::born`, `Mixture::switching`) are at commit
`2d34b819`. Their receipts are in the records they cite and in
the [construction record](../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md).

### F0. The predictor on unseen families (the release's gate; #73, #148)

[definition; agent-inferred; [audit and diagnosis](../../research/records/2026-09-28_THE_FORWARD_PLAN_STOPPED_AT_TRANSFER_THE_POPULATION_MEMORIZES_FAMILIES_AND_ITS_STANDING_IS_AN_INDEX.md)]

**The diagnosis** (the first loop, done September 28, re-reading F4's development passage by
component). On unseen families the population codes the bytes `−2430 + 8/16 + ε` bits below the flat
tree, half its gain on the choosing families. F4's whole-stream `+1346 + 1/16 + ε` is the cost of the
section letters and the request pointer, which the flat stream never codes. The rate on unseen agent
text is about `1 + 12/16` bits a byte, a PPM-class rate: its releases carry real words (580 of 758
word tokens) and are not yet legible. The standing is 10,983 bytes a cell. The posterior sits wholly
on the admitted egg, and the trees beyond depth 24 add at most 20 bits.

- **Builds on.** `receiver::population` with its dormancy and fixed share,
  `compression::landmark::context`, the merges, `Context/Merge.merge_cost_mass_iff`, the hazard ladder
  and continuation transports ([Astra's review](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#146-gain)),
  and the family-split scripts.
- **The comparison.** Like with like. The code of the bytes (and of each response's stop, which a
  release must predict), given the observed sections, is read against the flat tree on the same
  bytes. Section letters that a conversation supplies are observed, not predicted, so they are not
  charged to either side. Whole-stream codes stay reported.
- **Candidates**, each adopted by the choosing families alone:
  1. **Drop what carries no share. Adopted September 28.** On the choosing families the posterior
     sits on the admitted egg, so the population becomes the egg alone (`hnn_population f0-egg`).
     - Validation bytes are unchanged, `−2430 + 8/16 + ε` against flat, and choosing bytes
       improve by 2 bits, since no family names are paid.
     - The standing falls from 11,513,530,863 to 2,781,355,912 bytes (from 10,983 to 2,653 a cell).
     - Peak resident memory falls from 10.8 GB to 3.4 GB, and the passage from 272,849 to
       166,113 ms.
  2. **A family wins where it is closest: measured, not adopted, September 28**
     ([record](../../research/records/2026-09-28_A_NUMBER_IS_A_HELIX_ITS_BASE_IS_A_FACE_AND_A_FAMILY_WINS_WHERE_IT_IS_CLOSEST.md#5-the-population-a-family-wins-where-it-is-closest);
     [receipt](../../research/notebook/hnn_design/README.md#f0-candidate-2-a-family-wins-where-it-is-closest-september-28)).
     `receiver::population::LocalMixture` keeps each member's posterior at each gating context,
     the last `d` cells (node-local Bayes; Lean `Population.{local_telescope, local_mixture_code,
     local_of_constant}`). Its executed chart holds a member at `2^(−64)` of its context's leader,
     which also makes it return at `64 + log₂ M` bits (`hnn_population f0-local`, the eight
     declared families).
     - The choosing role chose `d = 0` from `{0, 1, 2}`, charged 2 bits. On the choosing stream the
       rung `d = 0` read `−247 + 0/16 + ε` against `d = 1` and `−259 + 0/16 + ε` against `d = 2`.
       The gating ladder in space is not adopted.
     - Validation bytes read `−2727 + 1/16 + ε` against flat. Against the egg alone they read
       `−298 + 8/16 + ε`, and `−296 + 8/16 + ε` with the 2 bits charged. The choosing bytes agree,
       charged, at `−3 + 12/16 + ε`.
     - The gain is dormancy in time. Over the whole passage the mixture codes `254 + 14/16 + ε`
       bits below its best single member, which no static mixture can do; exact whole-passage
       Bayes over the same families reads as the egg alone.
     - The standing returns to 10,983 bytes a cell (11,513,530,846 bytes), from 2,653. The passage
       takes 263,687 ms at an 8.4 GB peak, and streaming the standing raises the peak to 14.2 GB.
     - The switching in time is a floor declared as the chart's width, not the hazard ladder.
       Its segment telescope in Lean is owed (#62).
     - **Not adopted.** The choosing families decide: their charged bytes read `−3 + 12/16 + ε`
       against the egg alone and their whole stream about 7 bits above it. The gain rides on the
       floor, a switching law entered as a width (`K = 64`) and never compared with the declared
       fixed share, and it costs four times the standing for under one bit in 1,700 bytes. The egg
       alone stays F0's byte predictor. Mixing similar context models is not the lever on the rate.
  3. **Word contexts. Learned tokens as the alphabet: not adopted, September 28.** A tree over
     learned merge tokens (`hnn_tokens`: K = 256, depth 4 tokens, both chosen on choosing alone)
     codes the validation bytes `77906 + 10/16 + ε` bits above the flat byte tree (`1 + 15/16`
     against `1 + 13/16` bits a byte). Its releases hold fewer real words (836 of 1,527 against
     580 of 758), fused across merge boundaries. A token as an opaque index loses the byte tree's
     sharing: words with common spellings share no counts. Its standing is 389 bytes a cell.
     Words therefore enter as an **added** family, winning only where they are closest (candidate
     2), never as a replacement alphabet. Continuation transports stay promoted by
     `π_G P_G > π_C P_C`.
  4. **A learned lens** under source item 10.
- **Standing.** Every receipt reports standing bytes a cell. A standing budget is pinned before each
  run.
- **Readings of released text, monitored and never forced** (Brandon, September 28): paired
  delimiters (quotes, brackets, backticks, bold), valid UTF-8, and the word-shape rate against the
  choosing vocabulary (`release_legibility.py`). The first releases: 24 texts and 8 typed refusals;
  580 of 758 word tokens real, against 3,139 of 3,306 in the controls; backticks even in 14 of 24,
  against 32 of 32.
- **Acceptance.** On a fresh development-family split never used for a diagnostic, the conditional
  byte-and-stop code on the validation families is strictly below the flat tree's by a margin
  pinned before the run, within the standing and passage budgets. The release readings are
  reported beside it.
- **If it fails.** The byte population stays a compression result, and F4's curated release and F5
  wait. The chase terrain (F6) carries the architecture's tests.

### F2. The field as a family (step 4; #73)

[established-bounded; source-inspected] The [F2 pin and preflight](../../research/records/2026-09-27_F2_FIELD_FAMILY_GATE.md)
found that the proposed full passage exceeds the budget and the bounded probe is below the
field's admitted `n*`. The resident exposure also lacks a per-cell rational field face for the
population's `Family` contract. A corrected `n*`-sized host field exposure read one held-out
development passage in 363,330 ms, but supplies no population field-family comparison or
adoption. The field remains dormant for text until that consumer is built.

- **Builds on.** `hnn::receiving`, `hnn::reference::expose`, `receiver::population` and its work
  receipts.
- **New.** A field family in `receiver::population`. Its learning covector is the declared target
  minus its own face, while `q_population = Σ_f w_f P_f` scores the passage. Its declaration is
  charged once, in the prior.
- **Acceptance.** It is adopted for text only if both hold on the pinned validation families:
  - the charged population code is strictly shorter than without the field;
  - its complete work fits the declared response and passage budgets.

  Field work, memory and code are reported separately.
- **Budget.** At the recorded costs (card about 104 ms a two-cell window), a serial field-and-
  population passage over the standing cut exceeds ten minutes. It is projected, and run as a
  bounded probe if the projection fails.
- **If it fails.** The field stays dormant for text, kept and not run, with the decision recorded.


### F3. The resident population (step 5; #76)

- **Scope.** The curated population's selected family, its mixture and its receipts, ported as a
  bounded resident path. Each family that stays on the host is named, with its reason in #76.
- **Acceptance.**
  - Faces, code enclosures, deaths and receipts equal the host's on pinned fixtures and on one
    curated passage.
  - The report gives population-only card time against population-only host time, the transfer,
    the peak card memory and the capacity census.
  - Acceleration is claimed only if the resident path is faster within capacity.
- **If no family completes resident.** F3 fails, and a host Athena may still proceed.


### F4. Release (campaign 5 into step 8)

[established-bounded; measured] The [pinned split and receipt](../../research/records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md)
record one held-out development-family passage. The F4 failure branch applies: the score-identical
next-face view is built, but the text-release carrier is incomplete, and the charged validation
stream is above the flat control. The evaluation partition remains closed.

[established-bounded; F5 development continuation] A [private diagnostic](../../research/records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md)
now branches contemporary choosing standing, plans request incidence, samples a family once from
the posterior enclosure and follows its exact face to a section stop. On one response a fresh
branch verified the population's scored face before all 179 bytes and the stop and checked UTF-8
and the append-scalar square in 15,826 ms warm. The posterior's unresolved draw region,
producing-key/causal relation, compatible-source fibre and product health are retained as missing
terms; this is not F4 acceptance.

- **Builds on.** `receiver::release`, the generic release law.
- **New.** The population's text-release consumer.
- **Law.** A request conditions the same face that scores a complete response, its stopping section
  included: `P_release(y | request, Θ) = P_scored(y | request, Θ)`. Each release carries:
  - its decoder;
  - the keys;
  - its causal provenance (the egg and keys that produced each face);
  - the grain and fibre;
  - a typed refusal where it declines.

  `D E = ρ` and `E_next T = U E` are checked, or a separator is returned.
- **Terrain acceptance.**
  - Exact continuation is required only on deterministic terrain (the moiré, the arithmetic),
    after a future-equivalent key is located.
  - On stochastic terrain the conditional faces are compared with the known source, never one
    drawn stream against its entropy.
- **Curated.** Development responses are inspected against a request-aware retrieval control:
  answering with the most similar earlier request's recorded response.
- **Deadline.** A warm-response deadline is pinned.
- **If it fails.** The machine is a predictor, not yet a releasing product.

- **Second stage, after the first receipt** ([review](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#143-release)). The release becomes
  receiver-conditioned: `Q_R(e | s) ∝ 1_(A_K(s))(e) P₀(e | s) L_R(z | e, s) 2^(−c_R(e))`, the unique
  minimizer of `D(Q ‖ P₀) + E_Q[c_R − log₂ L_R]` on the viable emissions. Then
  `P_release = P_scored^release = Q_R`, timing and stopping included, and `P₀` is the reported
  control. Each section compares release, waiting, a viable probe and a typed refusal, each with a
  declared cost. The receipt carries `P₀`, `Q_R`, `Z_R`, the comparison and the delay price. A
  cheaper later turn is not by itself value.


### F5. Athena-0: the first product outcome (step 8; #148)

[established-bounded; development only] The [F5 pinned diagnostic and gate](../../research/records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md)
have a one-protocol atomic exterior checkpoint/replay fixture, a certified private native
request path and a 32-request diagnostic pass: 24 provisional UTF-8 candidates, eight typed
failures, 314,527 ms of choosing preparation plus warm work, and no evaluation read. Eleven of
those requests have unresolved declared parents; the other 21 have one-occurrence context.
The split was used to refine the release route, so it is spent for diagnostics and cannot serve
as F5 acceptance. The product protocol refuses the provisional text for missing native health,
key/causal provenance and compatible-source fibre. Versioned exact codecs now cover the tree,
boundary/admitted eggs and a tagged population in small continuation fixtures. On the actual
choosing standing, the full tagged stream occupies 6,256,005,986 bytes; its development restore
passed the next-face/receive square at 16,287,236,096 bytes sampled peak RSS. An independent cold
restore, a memory-bounded single-file atomic native protocol join and truthful product receipts
remain open; the JSON/base64 fixture is not the large-state path. Freeze the law
and pin a fresh untouched development split before F5's acceptance pass or evaluation.

- **Definition.** A local interaction on this machine (one RTX 4080 SUPER of 16 GiB, 20 GB of RAM
  admitted). It accepts a visible human request and its declared conversation context, and returns
  a relevant, grounded text response or a justified refusal, with a receipt.
- **Built for it** (the lessons record's requirements):
  - one command vocabulary with human, JSON and JSONL views;
  - one atomic checkpoint of standing, cursor and pending comparisons;
  - exactly-once output and byte-identical resume;
  - each response's numerical health (radius, robust count, operator bound, contraction),
    provenance and costs by kind, refusing any face that covers the simplex;
  - private sources and diagnostics kept owner-only.
- **Gates before the evaluation partition opens.** The pinned retrospective requests and the
  restart check pass on development.
- **Evaluation, once.** On every eligible evaluation request, Athena releases before its recorded
  reply is read. **Brandon judges** (September 27: "I'd want to do it"), blind, under a rubric
  frozen before the split is read.
  - For each request he sees two responses side by side in a hash-seeded random order, Athena's
    and the retrieval control's, with nothing that names their source.
  - He marks each response as answers, justified refusal, or fails, and marks which of the two is
    better or that they tie.
  - The judging surface shows him the request, its declared context and the two responses, and
    nothing private beyond what he already owns.
  - The unblinding key is written after his marks are committed.
- **Acceptance.**
  - More than half of the outputs answer, or justifiably refuse; an answerable refusal counts as a
    failure.
  - The releases win more than they lose against the request-aware retrieval control built from
    development only.
  - Nothing private is disclosed.
  - A warm response returns within one minute, within the declared memory limits.
- **Reported beside it, not as acceptance.** The conditional code of the recorded replies, against
  the request-blind population, PPM-2 and the flat tree.
- **If any gate fails.** Athena-0 has not been reached.


### F6. Motion: the chase terrain, then the motor chart (campaign 4; #27, #148)

[definition; agent-inferred; Brandon's derivation, September 27, [record](../../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#13-the-chase-terrain)]
The machine has only read recordings; here it first moves, against another's constitution.

- **Builds on.** `holarchy::terrain` (terrain with known truth, the `Switching` pattern of declared
  families), `receiver::population` (families, mixture, dormancy's fixed share, composition),
  `receiver::release` (`DecisionRule`), `holarchy::gluing`, `geometry::screw` and Lean
  `Transport/SerialScrewChain`.
- **New.** A chase terrain, `holarchy::terrain::chase`:
  - an exact, bounded 2D arena over a rational lattice with a declared tick, each cell with a
    friction class `μ` from a declared finite set of rationals. The walls make forced turning
    possible: in an open arena a faster runner moving straight away is never caught;
  - a fast runner (speed bound `v_R`) whose velocity change per tick is admitted only if
    `|Δv|² ≤ (μ g h)²` on its cell, which bounds a pure turn's radius below by `v_R²/(μg)`. A demand
    beyond traction slips (a declared hybrid law): the runner keeps its tangent velocity for a declared number of ticks. Its
    evasion navigator and key are drawn from a declared family, which is the terrain's truth;
  - the chaser, the machine: slower (`v_C < v_R`), of a larger traction class, every emitted motion
    satisfying its own bound exactly;
  - two switches: a lag channel (observation `d` ticks late) and a faulty sensor (one of three
    independent, time-aligned channels reports a rotated heading on declared aeons; two channels
    detect a fault but cannot locate it).
- **Law.**
  - Reception: the population reads the runner's passage and selects its constitution (speed bound,
    traction per friction class, slip law, policy family).
  - Action: each chaser motion is released as a threshold commit, a sequential test on accumulated
    log-odds whose threshold is priced by the declared cost of a tick. Each emission carries its
    predicted consequence, and the directed covector (predicted against unfolding) is read at the
    action.
  - Deposition only at the locus a covector reached: a loop-closure reading across the three
    observation channels attributes each error to the mover or to a channel. The channel menu meets
    the separation condition: a defect on at most `k` edges is located uniquely only when the
    circuit matrix's kernel holds no nonzero vector of support at most `2k`.
  - Retention is action-sufficient: no merge of runner constitutions that an admitted probe would
    separate. Where the fibre is wide, the chaser may emit the probe with the greatest
    `I(Θ; Y | h, do(a))`.
  - Capture: the agents' quadrance is at most a declared capture radius squared.
- **Reception acceptance.** On hash-seeded arenas the selected fibre is future-equivalent to the
  truth under the admitted actions; the exact family is required only where a probe separates it.
  Its code is within a declared margin of the truth code, and strictly below the landmark tree
  reading the same passage.
- **Action acceptance.**
  - Over pinned seeds, capture takes strictly fewer ticks in sum, and in more than half of the seeds,
    than both controls under the same traction bound: pure pursuit and constant bearing.
  - The traces show turns forced across low-friction cells, with the runner's slips counted.
  - With the switches on, capture still beats both controls, the fault is located on exactly the
    aeons it is active, and lag-caused errors deposit nothing in the chaser's constitution.
- **Reported beside it, not as acceptance.**
  - The cornering receipt: the runner's robust viability kernel in the arena, tick by tick, under
    the machine's play and under each control. Capture should come from shrinking it.
  - Brandon's own play through a small exact interface, with real intervals: the human baseline,
    and data with real flux.
- **Budget.** A few thousand ticks per seed in exact arithmetic on the host, projected against ten
  minutes and the host memory before it runs. No card is needed.
- **If it fails.** A reception failure locates the birth problem on terrain whose truth is known. An
  action failure leaves a receiver without a controller, reported as a terrain result.
- **Then the motor chart.** Pinned before fitting: a public recording, its skeleton, its units, the
  horizon, the split and a constant-velocity control. The HNN's motor consumer preserves the ordered
  screw transport and `⟨w, Jθ̇⟩ = ⟨Jᵀw, θ̇⟩`, and releases a reachable endpoint at its declared grain
  or returns the complete joint fibre and residual. Acceptance: a held-out endpoint residual strictly
  smaller than the control's, within budget; otherwise the exact geometry is reported with no claim
  of motor usefulness.

## Protocol

- **Pinned families.** Before each new validation the item pins disjoint development families for
  choosing and for validation, drawn from the dataset's development partition by a declared
  hash-seeded split. It also pins the consumer, the charges, the baselines, the acceptance and a
  deadline.
- **The evaluation partition.** F5 alone opens it, once, after every product gate has passed on
  development.
- **Budgets.** Each full passage is projected before it runs, against ten minutes, 20 GB of host
  memory and the card's 16 GiB. A failed projection admits a bounded probe, never a full-passage
  claim.


## Rules of the rebuild

- **Build forward from the elementary objects.** Each new owner states which object and law it
  implements ([operator contract](../ELEMENTARY_OBJECTS.md#operator-contract)), and which part of
  the line it serves: the navigators, terrain, kernel, cokernel and landmarks it touches.
- **Port deliberately.** A law or kernel is ported from history (`13f8c734`) when a step needs it.
  It is read, rewritten against the current objects, and tested by the law it implements. Nothing
  is restored wholesale, and nothing is kept for compatibility.
  - Where to look: the census at `13f8c734` locates history's owners
    ([`RUST_R0.tsv`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/census/RUST_R0.tsv), [`LEAN_R0.tsv`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/census/LEAN_R0.tsv)),
    and so does the manifest on `archive/leftovers-2026-09-24`.
  - Each port is recorded in its step's issue as history path → new owner → law → test.
- **Do not port** what the retention audit and the lessons record retired:
  - the per-occurrence tape and frozen-cut replay;
  - `returns` journals and completed-update archives;
  - slot, session and episode wires;
  - byte and nibble codecs;
  - Q/K/V caches and foreign forward graphs taken whole;
  - any Lean in the HNN pipeline;
  - floats inside a law.
- **One library for the laws, one backend for the card.** `holonics` builds without CUDA.
  `holonics-cuda` depends on it and realizes its operations. Brandon's `codex/apple-silicon`
  (September 7, built on the retired engine) becomes `holonics-apple`. It implements the HNN
  execution port only after the host reference exists, with parity per law.
- **The hardware surfaces advance with the laws** (Brandon, September 25: "you should not have
  been neglecting the hardware surfaces"). The resident realization (step 5, `holonics-cuda`, and
  later `holonics-apple`) is not scheduled after step 4: each campaign's laws land with their
  device kernels and host parity checks, and an exposure runs resident. The host reference stays
  the parity target; the measurement that took one core for hours (the lattice word's
  [record](../../research/records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md), addendum) is the lesson.
- **Lean first for new mathematics.** A new law lands with its Lean statement, or names its
  obligation in #62.
- **Tests are written per law** as each owner is built: one fast test per stated law, plus one
  host/device parity check per kernel family. An inherited test stays only if it checks a stated
  law of its owner. The testing protocol (Brandon, September 25: "I wouldn't tolerate this"):
  - a test proves its law on the smallest fixture that exhibits it; no test builds a campaign's
    declared field;
  - a test runs in well under a second in a debug build, and the whole `cargo test -p holonics`
    stays within seconds; a test that needs longer is a measurement;
  - measurements (bit curves, timings, real cuts) are notebook examples run once in release,
    reported with their command and result as receipts, never gates;
  - a check that an optimization changes no value runs once on the real case as a receipt, and the
    suite keeps only its small-fixture law;
  - cost is a property of the representation: a law that is local and block-sparse is implemented
    and certified block by block, never by assembling a dense global object (guard 14).
- **A development harness decides; the held-out pass confirms once** (Brandon, September 26: "the
  lean needs to consolidate, issue hygiene is also bad, handle the step 4 'behind its own pace'
  thing properly as well"; the rules are agent-inferred, [record](../../research/records/2026-09-26_STEP_FOURS_PACE_AND_THE_LIBRARY_CONSOLIDATING_WHILE_IT_GROWS.md)).
  - Every predictive hypothesis (a letter family, a depth, a grain, a mixture component) is first
    measured prequentially on the development cells with `hnn_landmark`. The full exposure, host
    and card with its held-out pass, runs once per campaign at its end, and otherwise only when a
    law changes the word itself.
  - Law gates are the laws' own tests: a worker runs the gates of CLAUDE.md for what it changed,
    lowest first; the primary integrates on those receipts and re-runs only the gates the
    integration itself changes.
  - Campaigns on disjoint owners run together, each with its own success receipt. Each campaign's
    new law lands at its consuming owner and retires any duplicate in the same change.
- **Exact arithmetic.** No floats inside a law or the machine (CLAUDE/AGENTS, governing laws).


## History

[historical] The [construction record](../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md)
keeps, word for word, what this plan replaced on September 28: the status of September 27, the forward
plan F0–F6 with its receipts, why the repository was reset, the order of steps 0–8, the laws found
alongside them, and the step-4 design with its five campaigns, its port map and its retired choices.
The measurement protocol and the guards moved to [THE_MACHINE](../THE_MACHINE.md#measurement).

### The Decisions index

In this table, (a) to (e) and (h) name sections of the construction record's step-4 design; (f) is
[THE_MACHINE's measurement](../THE_MACHINE.md#measurement) and (g) its
[guards](../THE_MACHINE.md#guards-that-make-the-rejected-forms-impossible); "Rules of the rebuild" is
above.

[historical] Until September 27 this plan kept a numbered log, Decisions 1 to 39. Brandon,
September 27: the numbered Decisions were a habit of the agents, not his instruction. The
[unity audit](../../research/records/2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md) dissolved the log: each law now lives in its guide or owner with its source,
each measurement in its dated record, and each retired choice in (h). Dated records, the notebook
and some Lean module docs keep the numbers, and this table resolves them; the Lean names that cited
them now state their law (`depth_one_is_the_whole_cell_table`, `first_arrival_is_the_full_tree`,
`compacted_is_the_full_tree`, September 27). A Rust owner's module doc is
`crates/holonics/src/hnn/<name>.rs`, except the receiving tree's, which is
`crates/holonics/src/compression/landmark/context.rs`.

| # | Subject | Where it lives now |
|---|---|---|
| 1 | The medium changes only by deposition and, at an aeon boundary, by the collapse | (a), "The light is the change" (law and source); guard 11 |
| 2 | Selective stepping; participation fixed by keys | (a), "Stepping is selective" and "The nonlinearity lives in finitely many key and lock classes" |
| 3 | Local propagation | [THE_MACHINE](../THE_MACHINE.md), "No global solve" (Brandon's rulings); (a), "The causal cone" |
| 4 | Changes, not states | (a), "The light is the change" |
| 5 | Participation is the junction Swing's anchor, one exponent per contact | (a), "Participation is the Swing's anchor" |
| 6 | Retention is the collapse onto what the admitted future distinguishes | (a), "Retention" (law and source) |
| 7 | Exact inside, grain only at the face | (a), "Exact charts" (law and Brandon's rulings) |
| 8 | Rings close by default | (a), "A ring is a closing rotor by default" (law and Brandon's ruling) |
| 9 | The contact carries its own constitution | (a), "The contact carries its own constitution" |
| 10 | Keys lead; key location | `hnn::keys` module doc; (d), campaign 1, "Data → menu" |
| 11 | Far fields carry moments | (a), "Far fields carry moments" |
| 12 | Release goes through modes | (a), "Release through modes" |
| 13 | The pending read | (a), "The pending read" |
| 14 | The port | (c) |
| 15 | The return keeps the word's own waves or checkpoints | (a), "The return holds no tape" |
| 16 | Every campaign on the standing real cut (Brandon, August 26) | (f), "The cuts and their protocol" |
| 17 | Owners, not new nouns | (a), "The types `holonics::hnn` adds" |
| 18 | `GeneratorSourceEpisode`'s directed-contrast law moves before the file retires | (b), "Retired with campaign 1" (done; the file is retired) |
| 19 | Guards are types and lints, not source scans | (g), introduction |
| 20 | Campaign order | (d) |
| 21 | Campaign 1's declarations | (d), campaign 1 |
| 22 | Deposition on a declared carrier lattice | Lean `HNN/LatticeDeposit`; (a), "The deposited constitution, on its declared carrier lattices"; [record](../../research/records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md) §5 |
| 23 | The standing real cut | (f), "The cuts and their protocol"; `research/notebook/hnn_design/standing_cut.py` |
| 24 | Every transient and inverse on a declared lattice with a certified residual | `hnn::chart` module doc, Lean `HNN/LatticeWord`; [record](../../research/records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md), addendum |
| 25 | The hardware surfaces advance with the laws (Brandon, September 25) | Rules of the rebuild |
| 26 | Campaign 1's first repair | (h); its open stands in `hnn::moment`; [record](../../research/records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md), addendum |
| 27 | The region table | (h); Lean `HNN/RegionCounts`; [record](../../research/records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md), addendum |
| 28 | The landmark tree (Brandon, September 25) | `compression::landmark::context` module doc; merges in (d), campaign 5; [derivation](../../research/records/2026-09-25_THE_COMPRESSION_IS_OF_LANDMARKS_A_TREE_COCYCLE_AND_MERGES_PRICED_BY_THEIR_CODE_LENGTH_PAIR.md), [measurement](../../research/records/2026-09-26_THE_LANDMARK_TREE_COMPRESSES_THE_STANDING_CUT_BELOW_PPM_TWO.md) |
| 29 | Prequential scoring | (f), "The cuts and their protocol"; `compression::landmark::context`, "The measurement is prequential" |
| 30 | The likelihood mixture; the source's normalized open | `hnn::receiving::Mixture`, `hnn::moment::PopulationChart`; [record](../../research/records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md) |
| 31 | Step 4's pace (Brandon, September 26) | Rules of the rebuild, "A development harness decides"; Order, step 7; [record](../../research/records/2026-09-26_STEP_FOURS_PACE_AND_THE_LIBRARY_CONSOLIDATING_WHILE_IT_GROWS.md) |
| 32 | The declared stop prior | `compression::landmark::context`, "The declared stop prior"; [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §1 |
| 33 | The Born face | (h); [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §2 |
| 34 | Weighing is local | `compression::landmark::context`, "Weighing is local"; (h); [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §3 |
| 35 | The wide cut | (f), "The cuts and their protocol"; [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §4 |
| 36 | Second-arrival founding | (h); [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §5 |
| 37 | Stored at the faces where paths part | `compression::landmark::context`, "Stored at the faces where paths part"; [record](../../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §6 |
| 38 | The loaded resonator | `hnn::ring` module doc; [THE_MACHINE](../THE_MACHINE.md), the egg paragraph; [record](../../research/records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md) |
| 39 | A landmark's storage has a capacity | `compression::landmark::context`, "A landmark's storage has a capacity"; [record](../../research/records/2026-09-27_A_LANDMARKS_STORAGE_HAS_A_CAPACITY_AT_ITS_CEILING_IT_CARRIES.md) |
