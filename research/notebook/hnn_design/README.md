# HNN design measurements

[definition] The exterior harnesses behind the HNN's measured receipts: exact Python scripts and
cargo examples that run the crate's host reference and owners. This page is a route. The
[index](#index) names each harness, what it measures, its command and its record; the
[receipts](#receipts) follow, per harness and then by date, each pointing to its record. A
harness's declarations are in its own header (the Rust `//!` header or the Python docstring).
Commands run from the repository root.

## Conventions

The Rust measurements run the crate's exact host reference (`holonics::hnn::Reference`), which
the Python scripts do not reimplement, as cargo examples of the `holonics` crate. Their integers
outside the law are milliseconds and the declared counts each header derives (the held-out length
from the joint clock's mean aeon). They print no float and no decimal:
- bits are enclosures with exact endpoints, read at the receiver's grain `L_R = 16` through
  `GrainCell::of` as `n + k/16 + ε` (the carry `n`, the phase class `k` and the fibre
  `0 ≤ ε < 1/16`, exact);
- a comparison is an exact ordering with the exact difference of the enclosures, read the same way;
- a ratio is reduced, with its integer quotient and remainder;
- a mean of milliseconds is the integer quotient with its remainder, `q rem r over N`.

The receipts below quote the grain cell `n + k/16 + ε`; the exact fibres are in each command's
output. The development control's cut is pinned: `docs/plans/THE_REBUILD.md` at commit
`fed5488ce70eb5ffbc90f2f03d23638be9d69189` (171,754 bytes). Each example reads it with `git show`,
never from the live file.

`exterior.rs` is the notebook's shared exterior boundary: the cut file and its manifest
(`read_cut`, `manifest_number`), the process's resident set (`resident_set`, read from the
kernel's status for the `wide` mode's receipt) and the exact presentation of readings. The
examples include it by `#[path]`.

## Index

Each harness with what it measures, its command and its record. A Rust harness is a cargo
example of `holonics` (`hnn_exposure` also of `holonics-cuda`); its header states its
declarations and every mode. A Python script needs only the standard library unless its
docstring says otherwise.

| Harness | What it measures | Command | Record |
|---|---|---|---|
| `hnn_exposure.rs` | Campaign 1's exposure on a cut: the model face (the receiver's population over the landmark tree and the combined face), the baselines, keys, aeons and the first law; on the host or the card (`realization card`); the loaded resonator (`resonator source`); F2's adoption gate (`gate f2`: the population with and without the field on the held-out cells, work, memory and budgets) | `cargo run --release -p holonics --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all` | [campaign 1 meets its criterion](../../records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md), [the resonator](../../records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md), [campaign 2](../../records/2026-09-26_CAMPAIGN_TWO_THE_RINGS_AND_CONTACTS_ARE_LAWFUL_AND_ADD_NO_BITS_ON_TEXT.md), [F2's adoption gate](../../../docs/plans/THE_REBUILD.md#f2-the-field-as-a-family-step-4-73) |
| `hnn_landmark.rs` | The landmark tree (count-only): the depth sweep and prequential passage; `letters`, `prior`, `wide`, `compact`, `capacity` | `cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin` | [below PPM-2](../../records/2026-09-26_THE_LANDMARK_TREE_COMPRESSES_THE_STANDING_CUT_BELOW_PPM_TWO.md), [at scale](../../records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md), [capacity](../../records/2026-09-27_A_LANDMARKS_STORAGE_HAS_A_CAPACITY_AT_ITS_CEILING_IT_CARRIES.md), [campaign 2](../../records/2026-09-26_CAMPAIGN_TWO_THE_RINGS_AND_CONTACTS_ARE_LAWFUL_AND_ADD_NO_BITS_ON_TEXT.md) |
| `hnn_population.rs` (with `hnn_population_{composition,evolution,curated,census,u2,birth}.rs`) | The egg population: terrain (`tree`, `moire`, `crib`, `switching`, `standing`), `composition`, `evolution`, `species`, the curated source (`curated`, with `merges`), `f4`, F0's egg (`f0-egg`, `f0-census`), U2's acceptance run (`u2-acceptance`), residual-founded transport discovery (`birth-probe`, `birth`) | `cargo run --release -p holonics --example hnn_population -- <mode>` | [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md), [F4](../../records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md), [the forward plan](../../records/2026-09-28_THE_FORWARD_PLAN_STOPPED_AT_TRANSFER_THE_POPULATION_MEMORIZES_FAMILIES_AND_ITS_STANDING_IS_AN_INDEX.md), [U2's acceptance run](../../records/2026-09-28_U2_F0S_MEMORY_ACCEPTANCE_RUN_PINNED_BEFORE_ITS_SPLIT_IS_READ.md), [residual-founded transport discovery](../../records/2026-09-28_RESIDUAL_FOUNDED_TRANSPORT_DISCOVERY_PINNED_BEFORE_ITS_SEEDS_ARE_READ.md) |
| `hnn_chase.rs` | F6's chase terrain: the reception phase, the action phase's choosing sweep (`choose`) and its acceptance (`action`, with U4's move reading and U3's release reading); U4's next loop: the failure's diagnosis (`diagnose`) and the fresh population (`fresh`); F6's switches and their attribution (`switches`) | `cargo run --release -p holonics --example hnn_chase` | [the learner must move](../../records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md) (no dedicated record; the receipts below) |
| `hnn_ring_search.rs` | The ring-search experiment: the bank of HNN rings (`hnn::ring::PumpedRing`) as proposal dynamics for keys on the blind and parity moirés and the rotor crib, against enumeration, menu propagation (`hnn::keys`) and the nonlocking control, all work charged; the basins of the undriven bank against the Stern–Brocot mass law; `bank`, `preflight`, `diagnose <seed>`, `run` | `cargo run --release -p holonics --example hnn_ring_search -- run` | [the rings as a search for keys](../../records/2026-09-28_THE_RINGS_AS_A_SEARCH_FOR_KEYS_PINNED_BEFORE_THE_RUN.md) |
| `exterior.rs` | The shared exterior boundary the examples include | | |
| `standing_cut.py` | Pins the standing real cut (`6148`) and the wide cut (`wide 1048576`) | `python3 research/notebook/hnn_design/standing_cut.py 6148` | [campaign 1 meets its criterion](../../records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md), [at scale](../../records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) |
| `curated_source.py`, `curated_incidence.py` | The curated source, its pinned cut and flat twin; the admitted relations on the cut | `HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/curated_source.py 1048576` | [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md) |
| `development_families.py`, `family_passage.py` | The F-items' and U2's family splits and their joined passages | `HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/development_families.py [F1 \| F2 \| F5 \| U2 \| F2V2]` | [F4](../../records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md), [U2's acceptance run](../../records/2026-09-28_U2_F0S_MEMORY_ACCEPTANCE_RUN_PINNED_BEFORE_ITS_SPLIT_IS_READ.md) |
| `f1_dictionary.py`, `f1_validation_part.py` | F1's dictionary on choosing cells; its bounded held-out part | `HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/f1_dictionary.py` | [F1](../../records/2026-09-27_F1_WORD_ALPHABET_GATE.md) |
| `f2_capacity_probe.py` | F2's capacity-admissible byte-chart cut; with `F2V2`, the adoption gate's probe over the fresh split and the declared validation passage's counts | `HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/f2_capacity_probe.py [F2 \| F2V2]` | [F2](../../records/2026-09-27_F2_FIELD_FAMILY_GATE.md), [THE_REBUILD F2](../../../docs/plans/THE_REBUILD.md#f2-the-field-as-a-family-step-4-73) |
| `f4_retrospective.py` | F4's selected requests and retrieval control | `HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/f4_retrospective.py` | [F4](../../records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md) |
| `f5_retrospective.py`, `f5_dev_request.py`, `f5_request_bundle.py`, `f5_context.py`, `f5_blind_input.py` (tests: `f5_context_tests.py`) | F5's requests, contexts and blind cases | `HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/f5_retrospective.py` | [F5](../../records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md) |
| `athena_protocol.py`, `athena_file_protocol.py`, `athena_file_checkpoint.py`, `athena_dev_gate.py`, `athena_blind.py` (tests: `athena_*_tests.py`) | Athena-0's exterior protocol, checkpoint transport, development gate and blind judging surface | `HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/athena_dev_gate.py` | [F5](../../records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md), [the atomic standing audit](../../records/2026-09-27_F5_ATOMIC_STANDING_OWNER_AUDIT.md) |
| `release_legibility.py` | Count-only readings of released text | `python3 research/notebook/hnn_design/release_legibility.py <releases.json>` | [the forward plan](../../records/2026-09-28_THE_FORWARD_PLAN_STOPPED_AT_TRANSFER_THE_POPULATION_MEMORIZES_FAMILIES_AND_ITS_STANDING_IS_AN_INDEX.md) |
| `field.py`, `power.py`, `swing_power.py`, `word_bits.py`, `critical_cayley.py`, `bits2.py`, `collapse_check.py`, `collapse_bezout.py`, `release.py`, `capacity.py`, `deposit_bits.py`, `propagation.py` | The step 4 design review: power balance, bit growth, the causal diamond, capacity `n*`, key location by propagation | `python3 research/notebook/hnn_design/power.py` | the step 4 design ("The step 4 design scripts" below) |
| `hnn_lattice_growth.rs` | The deposited constitution's bits, the integral chart's equality, the path's openness (retired September 28, receipts below, last at commit `2d34b819`) | `cargo run --release -p holonics --example hnn_lattice_growth -- growth chain 128 declared` | [the deposition remainder](../../records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md) |
| `hnn_diagnose.rs` | Campaign 1's located failure (retired September 28, receipts below, last at commit `2d34b819`) | `cargo run --release -p holonics --example hnn_diagnose -- cut-file .local/cuts/standing-real-cut-campaign-1.bin` | [the located failure](../../records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md) |
| `hnn_born.rs` | The Born receiver beside the tree (retired September 28, receipts below, last at commit `2d34b819`) | `cargo run --release -p holonics --example hnn_born -- cut-file .local/cuts/standing-real-cut-campaign-1.bin` | [at scale](../../records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) |
| `hnn_curated.rs` | The curated cut as typed letters against the flat tree (retired September 28, receipts below, last at commit `2d34b819`) | `cargo run --release -p holonics --example hnn_curated -- curated .local/cuts/curated-cut.bin .local/cuts/curated-flat-cut.bin` | [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md) |
| `hnn_terrain.rs` (with `hnn_terrain_arithmetic.rs`) | The landmark tree on terrain a declared Holarchy made; `arithmetic` (retired September 28, receipts below, last at commit `2d34b819`) | `cargo run --release -p holonics --example hnn_terrain -- tree 2` | [the Holarchy and its aeons](../../records/2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md), [the faces of integers](../../records/2026-09-27_THE_EGG_IS_A_GENERATORS_GENOME_SELECTION_IS_BAYES_AND_THE_FACES_OF_INTEGERS_ARE_MOIRES_OF_GRATINGS.md) |
| `hnn_release_terrain.rs` | The population's release checks on known-truth terrain (retired September 28, last at commit `2d34b819`; its receipt is in its record) | `cargo run --release -p holonics --example hnn_release_terrain` | [F4](../../records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md) |
| `hnn_word_probe.rs` | F1's exact byte-word work preflight (retired September 28, receipts below, last at commit `2d34b819`) | `cargo run --release -p holonics --example hnn_word_probe -- <dictionary> <cut> <byte-count> [terminated]` | [F1](../../records/2026-09-27_F1_WORD_ALPHABET_GATE.md) |
| `hnn_tokens.rs` | F0 candidate 3: learned tokens with the tree over them (retired September 28, receipts below, last at commit `2d34b819`) | `cargo run --release -p holonics --example hnn_tokens -- probe .local/cuts/curated-f4-passage-cut.bin` | [the forward plan](../../records/2026-09-28_THE_FORWARD_PLAN_STOPPED_AT_TRANSFER_THE_POPULATION_MEMORIZES_FAMILIES_AND_ITS_STANDING_IS_AN_INDEX.md) (no dedicated record) |
| `hnn_population_local.rs` (`hnn_population f0-local`) | F0 candidate 2: a family wins where it is closest (retired September 28, receipts below, last at commit `2d34b819`) | `cargo run --release -p holonics --example hnn_population -- f0-local .local/cuts/curated-f4-passage-cut.bin .local/cuts/curated-f4-passage-flat-cut.bin` | [a number is a helix](../../records/2026-09-28_A_NUMBER_IS_A_HELIX_ITS_BASE_IS_A_FACE_AND_A_FAMILY_WINS_WHERE_IT_IS_CLOSEST.md) |

## Receipts

The per-harness receipts come first, moved from this page's preamble; the dated sections
follow in their order, each pointing to its record.

### The pinned cuts

Record: [campaign 1 meets its criterion](../../records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md) (the standing cut), [the landmark tree at scale](../../records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) (the wide cut), [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md) (the curated source).

**The standing real cut** (THE_REBUILD Decision 23; campaign 1's `Cut` row). `standing_cut.py`
reads the private exposure dataset (`holonics.conversation-exposure.v1`) and writes the pinned cut
and its manifest to `.local/cuts/`. Scope and counts only: the dataset's 24,768 occurrence families
split at its temporal cut into 22,449 development, 617 evaluation and 1,702 deferred; the
development stream is 15,462,581 bytes; the cut is its last 6,148 cells (`n*`), the final 1,190
held out, and the evaluation partition is not read (it stays unspent for step 8's splits).
`cut-file <path>` runs campaign 1's exposure on it, reading the held-out range from the manifest;
the pinned public text is the notebook's development control. The cut's hashes are recorded in #73.

**The wide cut** (THE_REBUILD Decision 35). `standing_cut.py wide 1048576` writes the development
stream's last `2^20` cells, the final `2^17` held out (one eighth), to `.local/cuts/wide-real-cut.*`
(mode 0600), with the whole cut's, the development part's and the held-out part's hashes in its
manifest. It holds the standing cut as its tail, so the standing cut's cells (development and
held out alike) lie in the wide cut's held-out range, and the evaluation partition stays unread.
`2^20` is the largest power of two within the memory cap (`hnn_landmark -- … wide`, stage 0).

**The curated conversation source** (campaign 5's input under
[the source contract](../../../docs/HNN_FORMULA.md#the-source-and-release-contract); #73, #148).
`curated_source.py` (stdlib only, run once, writing only into `.local/cuts/`, the directory mode
0700 and each file created mode 0600, never widened first) reads the
exposure's development partition alone (the evaluation and deferred families are parsed for their
partition label only) and writes the curated development stream (`curated-source.bin`, one u16 code
a cell), its incidence (`curated-source.incidence.jsonl`: ports, cell ranges, parents and relations
by occurrence ordinal and capture coordinate), its manifest, the pinned cut and the same bytes as a
flat cut. **Privacy**: every file stays in `.local/`; the script and the reader print counts, bits
and hashes only, never any text, and these are development receipts under the contract, not a
milestone. Its declarations (agent-inferred from the
[data rules](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/CONVERSATION_DATA.md)):
- **the chart**: the UTF-8 bytes of each visible part (0..255) and twelve **section letters**, coded
  cells `256 + 3k + c` for `k` in (`open`, `switch`, `turn`, `part`) and `c` in (human, agent,
  tool), `|A| = 268`: a part opens with one letter, so a channel's change is coded, never supplied;
- **the sections follow the declared turn**, each letter read against the previous emitted
  occurrence: `open` opens a conversation's aeon, `switch` enters another conversation (sessions
  interleave in the declared order), `part` stays in the previous occurrence's declared turn (the
  provider's `turn_id`) or is a further part of one record, and `turn` is the next epoch of the
  same aeon: a new declared turn or, where no `turn_id` is declared, the record boundary (the
  fallback). A return into a conversation whose declared turn continues is a `switch` (the letter
  marks the aeon change; agent-inferred), counted apart;
- **the ports**: human ← part kinds `human-text`, `human-command`; agent ← `agent-text`; tool ←
  `tool-call`, `tool-result` (declared; no exposure variant carries either); harness ← views
  flagged `control-surface`, every captured view after a family's first (a presentation mirror),
  and nonvisible `harness-text` references, all references only; `human-material` (no text) stays a
  reference on the human port; `container-has-copied-session-meta` marks the container, so its
  views stay on their author's port; a mirror is harness only when its visible parts (kinds and
  text) equal its family's first view's by hash, and a development family with a mirror that
  differs or a nonempty `conflicts` is refused (deferred, counted), never resolved;
- **incidence**: the provider's `parent_id` and the `comparison-request` and
  `later-human-after-agent` relations, each resolved to an earlier occurrence or kept unresolved;
  `previous_record` is `event − 1` in every development view (the capture predecessor), so it is a
  coordinate, never a parent. The admitted receivers (the contract's item 7: request→response and
  response→later-human, the `comparison-request` and `later-human-after-agent` relations) are
  carried in the incidence file and consumed by `receiver::population::admitted` ("The admitted
  receivers" below).

Counts: 22,449 development families (617 evaluation and 1,702 deferred, read for their partition
label only), 87 conversations, 22,395 occurrences with cells; human 2,142 parts and 1,557,801
cells, agent 20,253 parts and 13,795,626 cells, tool none; the harness holds 53 control views (188
parts, 86,548 bytes), 133 mirror views (139 parts, 122,606 bytes) and 270 `harness-text`
references, none in the stream. **Checks**: all 133 mirror views equal their family's first view by
hash, none differs; all 22,449 development families have empty `conflicts`; none refused. **The
letters** `open` 64 human and 22 agent, `switch` 283 and 4,057, `turn` 1,649 and 5,343, `part` 146
and 10,831 (before the declared turn was read: `turn` 1,795 and 16,174, `part` none). By path: the
15,600 occurrences that declare a `turn_id` give `open` 36 and 22, `switch` 145 and 3,257, `turn`
1,026 and 137, `part` 146 and 10,831; the 6,795 without one fall back to the record boundary,
`open` 28 and 0, `switch` 138 and 800, `turn` 623 and 5,206; no record has a second part with cells.
1,429 declared turns; 3,194 switches return into their conversation's continuing declared turn; no
declared turn is re-entered after another of its conversation. The stream is 15,375,822 cells.
Parents: 15,664 none declared, 6,782 outside (no development occurrence holds that event), 3
resolved; `comparison-request` 16,698 resolved and 3,555 outside; `later-human-after-agent` 1,374
and 757. **The pinned cut** is the stream's tail from its first letter at or after `len − 2^20`:
1,048,228 cells (`n* = 2^20`), the final eighth (`cells // 8`, 131,028) held out; development
65,101 human, 850,622 agent and 1,477 letters (`open` 6 human and 5 agent, `switch` 33 and 302,
`turn` 40 and 305, `part` 5 and 781), held out 34,687, 96,191 and 150 (`open` 2 and 0, `switch` 5
and 26, `turn` 15 and 91, `part` 0 and 11). The flat cut is its 1,046,601 bytes, held out from
915,723, byte for byte the flat cut before the sections followed the declared turn (its hashes
unchanged).

**The script** (`curated_source.py`; the preamble table's row until September 28): The curated conversation source under the source contract (above): the development partition's parts on their ports (human, agent, tool; the harness as references), section letters as coded cells, incidence resolved or kept open, the pinned cut's tail and its flat twin of the same bytes; counts and hashes only

**Receipts.** 22,395 occurrences with cells in 87 conversations; sections from the declared turn (`part` 10,977, `turn` 6,992: 1,163 new declared turns and 5,829 record boundaries); 133 mirrors equal their first views, no conflicts, none refused; the cut 1,048,228 cells (1,627 letters), the flat twin 1,046,601 bytes

**Through the population** (`hnn_population.rs curated`; the dated section "The curated source through the population" below): The curated cut through the egg population (campaign 5): the curated cell tree and the typed tree (the channel read once at the section) as families, and the boundary egg (the part clock ⊳ the typed tree and the letter tree through the hazard law on a partition learned by priced merges on the development cells, the declared partition and the refused stage read on the same cells), one passage over the whole cut against the flat tree at `D = 48`; `merges` runs the learning alone; development receipts, counts and bits only Receipts: The boundary egg selected (`−log₂ w = 0 + 0/16 + ε`); learned classes 167 values → 4 (declared 6), shares refused (`7/16` above); the whole curated stream charged against the flat stream: development `−1072 + 15/16 + ε` (declared `−950 + 9/16`), held out `−369 + 8/16 + ε` (declared `−415 + 3/16`)

### The step 4 design scripts

Record: the step 4 design (THE_REBUILD) and #62; no dedicated record.

[established-bounded; measured] The exact-arithmetic scripts behind the measured numbers in the
[step 4 design](../../records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md#step-4-design-the-hnn-law) and its #62 item on
bounded bit growth ("Step 4 (#73) owed"). Every measured value is a `fractions.Fraction` or an exact
integer, so each number is exact and seeded; `capacity.py` bisects on the exact integer test and
certifies each `n*` at `n* − 1` and `n*`, with no float anywhere. No script prints a float or a decimal
(a decimal is a collapse): `field.exact` prints a short ratio as `n/d (q rem r over d)`, its integer
quotient and remainder, and a long one as its integer quotient `q` plus its remainder's exact
enclosure between continued-fraction convergents with denominators at most `2^12`,
`q + e, e in [a/b, c/d]`, with the exact ratio's size in bits. They need only the Python 3 standard
library. Run one from the repository root:

```sh
python3 research/notebook/hnn_design/power.py
```

`field.py` is the exact reference of the revised tick: junction scattering (a parallel adaptor), the
Cayley ring element with its passive part `W_s` and its contrast port `W_c` driving inside the
midpoint, the contact's midpoint two-port and the global power. Its defaults (`W_s = W_c = 0`) draw
exactly what the earlier scripts drew. `power.py`, `release.py` and `word_bits.py` import it. The
scripts come from four rounds: the first revision's re-run of the first review's measurements
(`bits2.py`), the second review, R2 (`swing_power.py`, `critical_cayley.py`, `collapse_check.py`),
the second revision (the rest), and the third revision, answering R3 (`power.py`'s contrast-port
cases, the counting `capacity.py` and the time-indexed `release.py`). `word_bits.py` takes about
90 s and `capacity.py` about 6 min (375,000 ms in the last run); the rest take seconds.

| Script | What it measures | The design's number it reproduces |
|---|---|---|
| `power.py` | The global power `P` over 8 ticks on six rings of widths 4, 2, 4, 6, 2, 4: the six-cycle plus a chord | Lossless: `P` is constant exactly. Dissipative: `P(t) − P(t+1)` equals the dissipation exactly at every tick. With the contrast port `W_c ≠ 0`: `P(t+1) − P(t) = Π_c` exactly; with dissipation, passive `W_s` and `W_c` together, `P(t+1) − P(t) = −dissipation + (W_s term ≤ 0) + Π_c` exactly at every tick, and `Π_c` takes both signs over 8 starting states. With `W_c` 8 times larger the balance stays exact and `P` grows in 8 ticks by `P(8)/P(0) = 244 + e`, `e in [2626/3871, 251/370]` (an exact ratio of 7,580 bits) |
| `swing_power.py` | Junction scattering's power with one exponent per ring against one per contact | Per ring (not conserved): `73199/1920` (38 rem 239 over 1920) at tick 0, `50 + e`, `e in [3683/3851, 285/298]` at tick 5, `43 + e`, `e in [1577/3270, 1074/2227]` at tick 6. Per contact: `648509/23040` (28 rem 3389 over 23040) at every tick |
| `word_bits.py` | The bits of the change within one word, and the change released or carried from word to word | One word: 77, 482, 1,461, 3,512 and 7,623 bits at 2, 4, 8, 16 and 32 ticks. Released: at most 963 bits over 32 words of 6 ticks. Carried: 11,728, 24,057, 48,707 and 98,004 bits after 8, 16, 32 and 64 words (about 90 s) |
| `critical_cayley.py` | A lossless Cayley storage wave that persists across words | 77 → 6,272 bits over 256 words |
| `bits2.py` | The reaction read from the state or from the sheet class; the local junction scattering's causal cone; the source moment on a non-closing and on a closing ring; the first design's case (5) | 46 → 804,289 bits in 7 ticks; 44, 85, 127, 209, 374 and 705 bits; rings {0, 2}, then {0, 1, 2, 3, 5}, then all six; 7, 34, 146 and 592 bits; 1, 2, 3, 5, 7 and 9 bits; no collapse 47, 221, 912 and 1,831 bits. It prints the first design's truncation, "3, 5, 7, 7, max 52", under a WITHDRAWN label (R2 C2a) |
| `collapse_check.py` | Case (5) under the spectral projector by a Sylvester solve, and under the certified release | 72, 74, 77, 78, max 121 bits; the certified release refused at 32 of 32 boundaries. Its first line is the withdrawn truncation, labelled so |
| `collapse_bezout.py` | The same spectral projector by Bezout over ℚ[x], independent of the Sylvester solve | 72, 74, 77, 78, max 121 bits |
| `release.py` | The time-indexed causal diamond by the design's two recursions (reach and observe), on a path of six rings (source ring 0, receiving ring 2) | At `A = 2` (`e_last = 3`, `e_max = 4`): 72 of 156 constitution entries released (the separable form releases 44); every released item replaced by arbitrary values leaves every admitted reading identical over 20 injections; replacing any one retained item changes a reading, 12 of 12. The rim case `A = 1` (`e_last = 2`): every element released, 132 of 156; identical readings; 8 of 8 retained items tight |
| `capacity.py` | The capacity `n*` by counting: the least `n` with `N(n) < \|A\|^n`, certified by exact integers at `n* − 1` and `n*`; the moment's dense code as a reading | `n* = 137` on three rings of periods 3, 4, 5 over `\|A\| = 2`; 6,148 cells on campaign 1's declared field; 8,577 for one byte ring of period 7 with `Δ = {1}`; 3,641,698 for eight source rings of period 16 (8,421,376 slots). The dense code: 135 bits at `n = 128` and 138 at 144 on the control; about 117,000 cells for the period-7 ring; for the eight rings, with uniform counts, below the source for good from 4,243,457 cells (the dense code over the source bits `9472/9375` (1 rem 97 over 9375) at `n = 4,200,000`, `132608/134375` at `n = 4,300,000`) |
| `deposit_bits.py` | The bits of a deposited map under the per-locus normal law | `R` at `γ = 1`: 155, 176, 180, 196 bits after 8, 32, 128, 256 deposits; at `γ = 1/2`: 1,001, 5,172, 22,477, 46,784. `E` at `γ = 1`: 612, 3,237, 14,852 bits after 8, 32, 128 deposits |
| `propagation.py` | Ring-key location by propagation over the data → menu map, `d = 7`, against brute force over all 5,040 plugboards | Propagation equals brute force at 322–3,822 steps against 35,280. The fibre holds the truth; a `δ = 1` chain leaves 35–42 members; 16 independent crib pairs pin the rotor-gauge orbit (7 members); a random cut gives an empty fibre |

### `hnn_exposure`

Record: [campaign 1 meets its criterion](../../records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md), [campaign 2](../../records/2026-09-26_CAMPAIGN_TWO_THE_RINGS_AND_CONTACTS_ARE_LAWFUL_AND_ADD_NO_BITS_ON_TEXT.md), [the resonator](../../records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md).

`hnn_exposure.rs` runs campaign 1's exposure, `Reference::campaign_one().expose(&field, &cut)`, and
prints its complete readout and the host's wall time by phase. Its header states the declarations
(the cut's first `N` cells, `n* = 6,148` by default, `cells all`; the held-out tail; the deadline
`windows K`) and the card realization (`realization card`, as an example of `holonics-cuda`).

```sh
cargo run --release -p holonics --example hnn_exposure -- windows 8
cargo run --release -p holonics --example hnn_exposure
python3 research/notebook/hnn_design/standing_cut.py 6148   # n*, printed by hnn_exposure
cargo run --release -p holonics --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all
# the same exposure on the card (the device port, holonics_cuda::hnn::Resident), under the GPU lock
flock .local/gpu.lock cargo run --release -p holonics-cuda --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all realization card
```

**Campaign 2's tree on the card** (the receiving parametron's landmark tree mirrored by
`holonics_cuda::hnn::tree::CardTree`: every window's splits in cell order and every deposit's
opened-path update on the card, the class faces completed on the host; the compare phase under the
hardware law, `hnn::reference::compare_phase`). Its wall time is read on the development windows
alone (the deadline stops before the held-out range, so no held-out cell is read), and the card's
line prints the tree's parts:

```sh
flock .local/gpu.lock cargo run --release -p holonics-cuda --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all windows 2479 realization card
```

Receipt of September 26 (2,479 windows over the 4,958 development cells, every window deposited,
no held-out target scored; the RTX 4080 SUPER; wall times exterior, integer ms or µs, a window's
mean as the quotient and remainder over 2,479): the readout outside the wall times and the traffic
is identical, line for line (2,660 lines), to campaign 1's code on the same windows (commit
`7d93b291`), and the mirror's founded count equalled the host tree's after every deposit. The
exposure took 238,149 ms (`96 rem 165` ms a window)
against campaign 1's 284,760 ms (`114 rem 2154`). By phase, campaign 1 → campaign 2, per window:
the compare phase (holon and covector) `29 rem 2236` → `10 rem 1687` ms (`compare_phase`: the tree
at the grain beside the mixture score and the Holon ratio); the tree read (the campaign 1 phase: the
tree faces and the combined faces) `1665 rem 253` → `1674 rem 770` µs, with the tree's transfers
`92 rem 782` µs apart and the deposits' mirror updates `279 rem 1187` µs (their transfers
included); the word's refine read `2034 rem 1065` → `2029 rem 1102` µs; the host's deposit
(`Constitution::deposited`, the normal laws) `50 rem 1023` → `50 rem 917` ms, now the largest
phase. The tree's own parts over every read (compare and re-read: 9,916 phases, 4,958 cells
deposited), per window: the card's reads `153 rem 647` µs, the host's class faces from the splits
`212 rem 77` µs, the combined faces in `ℚ(θ)` (`ReceivingPhases::combine`) `2914 rem 299` µs, the
transfers `347 rem 811` µs, the updates' launches `96 rem 1378` µs. The combined faces, not the
tree, now hold the tree read's time.

**What it measures** (`hnn_exposure.rs`; the preamble table's row until September 28): Campaign 1's exposure protocol (design (d)) on the standing real cut (`cut-file`) or the public development control, and its complete readout (design (f)). It prints the bits on the training and held-out targets against uniform, order-0 and order-1 KT and PPM of order 2, with the verdict against order-0; the model's face is the mixture of the landmark tree's face and the combined face (the primary's ruling A); beside it, the tree face alone (Decision 28: the receiving parametron's tree at each cell's causal address read at the grain, no wave, at the model's constitution and address, from the compare's receipt) and the combined face alone (tree plus wave), each baseline against them, and the combined face against the tree (the wave's contribution); the course by aeon (each aeon's model, tree and combined code lengths and the mixture's `log₂ β` at its boundary) and the mixture's end (`log₂ β`, rebases, drift). Every window is compared and then deposited, held-out windows included (Decision 29). It prints `Kt` with the published keys against the literal over the cells read. Per key location, it prints each ring's fibre, orbits, fallback, failing loop, candidates, propagation work and re-keying jump. Per aeon, it prints the length, lift points, readings, epochs, collapse, the first law (exchange, deposition, total and change, each checked to telescope) and the face against the literal (`code + gain = literal`, checked). It prints the state and constitution bits per source bit with and without the collapse, the constitution's curve by carrier per commit, the budget stop or deadline, the work counted, the executed word's readout (Decision 24: the declared precisions, the charts' refinements with their starts, steps and largest certificate, the remainders the words and their returns released, and the tick balances' residuals against their certified bounds), and the host's wall time by phase (refine read, release, compare read, tree transfer, tree read, holon and covector, `pull_back`, `compose`, `deposited`, tree deposit, re-read and ingest, with the rest of the exposure; on the card, the tree's parts), with the host's tree read per window against the word's (the refine read)

**Receipts.** **After the review (September 26; the window scored in cell order, the tree alone on its exact face):** held out (1,190 cells) the model reads `3671 + 9/16 + ε` bits (a cell `3 + 1/16 + ε`), the tree's exact face `3677 + 12/16 + ε`, the tree at the grain `3678 + 2/16 + ε`, the combined face `3671 + 9/16 + ε`; model − order-0 `−1996 + 12/16 + ε`, model − order-1 `−1494 + 11/16 + ε`, model − PPM-2 `−252 + 5/16 + ε`, `L_C − L_T` and `L_model − L_T` each `−7 + 13/16 + ε` bits in all (development `−19 + 12/16 + ε` and `−18 + 12/16 + ε`); `log₂ β` at the aeon boundaries `−2 + 9/16`, `−8 + 10/16`, `−12 + 2/16`, `−17 + 2/16`, `−21 + 0/16`, `−25 + 9/16` at the end (each `+ ε`); host 399,911 ms, card 353,499 ms, the readouts identical line for line (3,303 lines) outside the wall times and the traffic ([record](../../records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md)). The receipts before the review, which read the tree alone at the grain and one `β` a window: receipts of September 26, this tree, prequential (Decision 29), on the standing real cut (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all`, then with `realization card`; 3,074 windows, 3,074 deposits, complete, no budget stop), bits a cell at `L_R = 16`, held out (1,190 cells) and development (4,958): **Decision 28's receiving face with the mixture (ruling A)**: the model `3 + 1/16 + ε` and `3 + 10/16 + ε`, the tree face alone `3 + 1/16 + ε` and `3 + 10/16 + ε`, the combined face `13 + 10/16 + ε` and `8 + 2/16 + ε`, online order-0 `4 + 12/16 + ε` and `4 + 15/16 + ε`, order-1 `4 + 5/16 + ε` and `5 + 1/16 + ε`, PPM-2 `3 + 4/16 + ε` and `3 + 12/16 + ε`; held out in all, model − order-0 `−1989 + 1/16 + ε` (the campaign criterion met), model − tree `−1 + 9/16 + ε`, combined − tree `12606 + 5/16 + ε`; `log₂ β = 35109 + 9/16 + ε` at the end (`W = 28`, 6,146 rebases, drift `5843235441809495541881131462031789/2^126` bits); host 471,824 ms, card 376,507 ms, the readouts identical line for line (3,281 lines) outside the wall times and the traffic. **With the indexed normalized open (ruling B)**: the model, the tree face alone and the combined face each `3 + 1/16 + ε` held out and `3 + 10/16 + ε` on development; held out in all, model − tree `−7 + 1/16 + ε` (development `−18 + 9/16 + ε`), combined − tree `−7 + 1/16 + ε`, model − order-0 `−1996 + 9/16 + ε`, model − order-1 `−1494 + 8/16 + ε`, model − PPM-2 `−252 + 1/16 + ε`; by aeon (the course), combined − tree `−1 + 3/16`, `−6 + 0/16`, `−5 + 3/16`, `−6 + 13/16`, `−6 + 9/16`, `−4 + 12/16` and `log₂ β` `−2 + 12/16`, `−7 + 2/16`, `−12 + 11/16`, `−17 + 5/16`, `−22 + 11/16`, `−25 + 6/16` (each `+ ε`; `W = 28`, 6,146 rebases, drift `11686470883619335088690741741329703/2^127` bits); `|describe|` 1,431 bits, `Kt` `23176 + 10/16 + ε` against the literal 49,184; the constitution 4,722,117 bits; host 405,500 ms (131 rem 2806 over 3,074 a window), card 355,065 ms (115 rem 1555 over 3,074), the readouts identical line for line (3,289 lines) outside the wall times and the traffic. The host's tree read per window: 1,720 µs against the card's word (refine read) at 2,110 µs (a #76 debt). The enclosures' exact endpoints are in the print. The earlier laws' and trees' smokes and receipts (Decision 27's among them) are in git history. **The host realization on the standing real cut** (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all windows 24`, run from the repository root, 24 windows on 24 workers): 6,729 → 1,352 ms a window. Per window, before → after: refine read 453 → 198, release 21 → 9, compare read 452 → 0 (the compare takes the refine's kept read), holon and covector 16 → 9, `pull_back` 1,420 → 253, `compose` 2,597 → 479, `deposited` 1,238 → 147, re-read 494 → 218, ingest 0 → 0, the rest 33 → 35. The readout outside the wall times is identical, line for line, to the tree before the change (the bits and code lengths, `Kt`, the constitution's curve, the state and the work). **Campaign 1's first-law exposure** (`hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all`, 3,074 windows; 477,915 ms on the host in the resident exposure's receipt below): its receipt is recorded in #73. **The lattice word** (Decision 24): below the table

**The lattice word's receipt** (Decision 24; `crates/holonics/src/hnn/chart.rs`). Every inverse the
word executes is a certified lattice chart, every transient is carried with error feedback, and the
return pulls back through the executed charts' transposes. The run is `hnn_exposure -- cut-file
.local/cuts/standing-real-cut-campaign-1.bin cells all windows 24`, from the repository root, 24
windows on 24 workers. The tree before is `c690f76d`, the exact word.

- **Declared precisions**, by rule: charts on `2^(−38)ℤ`, certificate target `2^(−19)`, transients on
  `2^(−15)ℤ`.
- **Wall time: 1,349 → 129 ms a window**, the two binaries run back to back on the same host.
  Per window, before → after:

  | Phase | Before | After |
  |---|---|---|
  | refine read | 200 | 11 |
  | release | 10 | 0 |
  | compare read | 0 | 0 |
  | holon and covector | 9 | 8 |
  | `pull_back` | 251 | 4 |
  | `compose` | 477 | 3 |
  | `deposited` | 143 | 55 |
  | re-read | 219 | 20 |
  | ingest | 0 | 0 |
  | the rest | 36 | 24 |

  The re-read's 20 ms is a word (about 12 ms) and the Holon ratio's code length (about 8 ms).
- **Bits.** On the 48 training targets the model takes, in this tree's rerun, exact
  `[30354970831364957692165135403267/2^96, 15177485415682478846138748501305/2^95]` bits, which read
  `383 + 2/16 + ε` at `L_R = 16` (the receipt at `53db0a8a` recorded only an outward decimal
  enclosure, which contains it). The exact word's enclosure before lies in the same grain cell and
  above it; it was recorded only as a decimal, so its exact endpoints and the exact difference are
  owed (rerun at `c690f76d`). The law changed.
  The verdicts are unchanged: below uniform, above order-0 KT (`327 + 5/16 + ε`), order-1 KT and
  PPM.
- **Kt.** `|Field::describe|` grows from 1,369 to 1,403 bits, because it codes the word's
  precisions. `Kt` goes from `1768 + 2/16 + ε` (the exact word's; exact endpoints owed, rerun at
  `c690f76d`) to exact `[142779733439106052737404000930051/2^96,
  71389866719553026368758181264697/2^95]` bits, `1802 + 2/16 + ε` (this tree's rerun).
- **Inside the word.** The peak bits of the change fall from 5,649 to 32, and the work's peak bits
  from 18,615 to 60.
- **The constitution's curve** changes only through the deposits' samples: 1,110,084 → 1,108,108
  bits at commit 24. The residuals each deposit releases fall, because the returns' covectors now
  have bounded denominators; both trees' released bits a deposit were recorded only as decimals
  (exact readings owed; rerun at `c690f76d` and `53db0a8a`).
- **The resident** counts the executed charts: 2,426,004 → 2,545,660 bits.
- **Charts.** 384 refinements, 16 a window. The 90 cold starts are the rings after each deposit,
  whose warm certificates were recorded only as decimals (exact readings owed; rerun); none fell
  back to an exact inverse, where one exact inverse of the 26-wide ring took 27,700 µs. 831 rounded
  Newton–Schulz steps. The largest certificate is `526198678409/2^58` against the target
  `2^(−19) = 549755813888/2^58`: below it by `23557135479/2^58`.
- **Released remainders.** The words released 5,573 nonzero forward remainders (the largest
  `2^(−16)`, 475,823 bits) and the returns 11,936 adjoint remainders (the largest `2^(−16)`, 927,125
  bits); their ℓ1 sums were recorded only as decimals (exact readings owed; rerun at `53db0a8a`).
  This tree's rerun (after `41cbd056`) releases 5,573 forward remainders, ℓ1 sum
  `438949721590752728797/2^73`, 476,141 bits, and 11,935 adjoint remainders, ℓ1 sum an exact ratio
  of 831 bits in `[368/4067, 155/1713]`, 926,820 bits.
- **Balances.** All 72 tick balances close up to their residuals within their certified bounds. The
  largest residual and its bound were recorded only as decimals (exact readings owed; rerun at
  `53db0a8a`). This tree's rerun: the largest residual
  `24189175054009847231496313928325525947359/2^147` against its bound
  `145513756276589703458585123821562965016963/2^146`, below it by
  `266838337499169559685673933714800404086567/2^147`.

**The resident exposure's receipt** (rebuild step 5, Decision 25; `holonics_cuda::hnn::Resident`,
`crates/holonics-cuda/src/hnn/port.rs`). The device port runs every word on the card (the charts'
Newton–Schulz refinement and certificates, the word's open, ticks and receiving read in one launch,
its return in one launch, the moment's ingest) and keeps on the host what the port plan assigns it
(the faces in `ℚ(θ)`, the Holon ratio, the tick balances, the composition, the deposit's prox step,
the ledger, keys and collapse). Run from the repository root on the RTX 4080 SUPER, the host's
command first, then the card's, back to back.

- **Parity.** The readouts are identical line for line outside the wall times: 79 lines at
  `windows 24` and 2,663 lines on the full cut. `holonics-cuda`'s `port_tests.rs` asserts every
  `InteractionReturn` equal in lockstep (the chain control, generic constitutions, campaign 1 on
  drawn bytes, deferred compares, a releasing collapse, refusals, and the standing cut's first 24
  windows).
- **Realization.** The word and its return are each one block of 256 threads (the entry's lowered
  ceiling), four rows a thread over the widest stage (the 1,024 logits).
- **Wall time.** 24 windows: host 120, card 113 ms a window. Full cut (3,074 windows): host
  477,915 ms (155 ms a window), card 334,358 ms (108 ms a window). Per window, host → card:

  | Phase | 24 windows | Full cut |
  |---|---|---|
  | refine read | 11 → 2 | 34 → 3 |
  | release (the card's includes the tick balances, read on the host) | 0 → 2 | 0 → 2 |
  | holon and covector | 8 → 8 | 9 → 9 |
  | `pull_back` | 4 → 1 | 4 → 2 |
  | `compose` | 3 → 3 | 9 → 9 |
  | `deposited` | 47 → 45 | 38 → 39 |
  | re-read (the card's includes the successor's publication) | 20 → 20 | 33 → 17 |
  | ingest | 0 → 0 | 0 → 0 |
  | the rest | 23 → 28 | 24 → 25 |

  What remains is the host's exact arithmetic the port plan keeps there: the deposit's prox step
  (38 ms), the faces' code lengths in `ℚ(θ)` (about 9 ms in the re-read and 9 in the holon), the
  composition (9 ms).
- **Across the bus**, per window on the full cut: 173 kB for the words (plans, operands, records
  with the logits, certificates, moved operators and charts; two words a window), 25 kB for the
  return, 20 kB for the publication's moved words (16 octets each), 56 octets for the ingest. The
  full cut ran before a word's operands crossed as its weights only (its chart slots are gathered on
  the card), which moves less a word (the saving in octets: exact reading owed; rerun): 220 → 183
  kB a window at `windows 24`.

### `hnn_landmark`

Record: [below PPM-2](../../records/2026-09-26_THE_LANDMARK_TREE_COMPRESSES_THE_STANDING_CUT_BELOW_PPM_TWO.md), [the landmark tree at scale](../../records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md), [capacity](../../records/2026-09-27_A_LANDMARKS_STORAGE_HAS_A_CAPACITY_AT_ITS_CEILING_IT_CARRIES.md), [campaign 2](../../records/2026-09-26_CAMPAIGN_TWO_THE_RINGS_AND_CONTACTS_ARE_LAWFUL_AND_ADD_NO_BITS_ON_TEXT.md).

`hnn_landmark.rs` measures the landmark tree (count-only, `holonics::compression::landmark::context`),
executed on its declared dyadic lattice. Its header states every mode's declarations and stages:
the default passage (Decision 28: the depth sweep on the development cells, then the prequential
passage against the online baselines and the reference oracle), `letters` and `letters contacts`
(campaign 2's development harness with its constant-slot controls), `prior` (Decision 32),
`wide` (Decision 35), `compact` (Decision 37) and `capacity` (Decision 39). The `local` mode
(Decision 34, commit `89460425`) and the `converge` mode (Decision 36, commit `d137e8a6`) are
retired with their realizations; their laws stay in Lean
`Compression/Landmark/Context/{LocalWeighing,ConvergenceFounding}`.

```sh
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters contacts
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin prior
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin wide .local/cuts/standing-real-cut-campaign-1.bin
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin compact
cargo run --release -p holonics --example hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin capacity
```

**What it measures** (`hnn_landmark.rs`; the preamble table's row until September 28): The landmark tree (Decision 28, count-only; `compression::landmark::context`) on the standing real cut, executed on its declared dyadic lattice: the depth sweep on the development cells, then the prequential run of the tree (its executed lattice face) and the online baselines (uniform, order-0 and order-1 KT, PPM of order 2) over the same cells in the same order, every cell scored before its own deposit; the tree's strict ordering against order-0, order-1 and PPM-2; the derived widths, the β chart's rebases and drift, the rule's bound and the largest certified per-cell residual; the hot path's wall times; the executed face's cost against the reference oracle (the ideal tree weighting in ℚ), cell by cell; `prior`: Decision 32's stop-prior decision on the development cells (every law of the declared family with its own depth sweep, charged), where campaign 2's constant-slot controls found their bits, and the held-out pass once for the chosen law; `local`: Decision 34's oracles at the digit, cell and dyadic-cell grains and its three local laws (at each landmark, in each digit tree, across epochs) on the development cells, charged, with one held-out pass for each law that codes below the tree; `wide`: Decision 35's pass on the wide cut (the memory's derivation, the depth, then one prequential passage of the `½` tree, Decision 34's adopted law and the baselines, read on the development and held-out cells and the standing cut's parts, and ordered); `compact`: Decision 37's tree stored at the faces where paths part on the wide cut (the declared doubling family and its budget, `D = 6` against the full arena within their certificates, the depth sweep with each depth's nodes, label letters, allocated bytes and wall time, the choice charged, then one held-out passage of the chosen tree beside Decision 28's tree at `D = 6` and the baselines, ordered); `capacity`: Decision 39's capped register on the wide cut at `D = 48` (the family `c ∈ {∞, 5, 7, 9, 11}` charged 3 bits, the check that `c = ∞` reproduces Decision 37's development code, each ceiling's development passage, the choice charged, then one held-out passage of the chosen ceiling against Decision 37's recorded held-out tree and PPM-2); Decision 36's `converge` mode is retired with its Rust realization (commit `d137e8a6`)

**Receipts.** **Decision 39's capped register** (`hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin capacity`; September 27; the wide cut, development 917,504 cells, held out the final 131,072; `D = 48`, `n* = 2^20`, `L_R = 16`; bits at the grain, each `+ ε`, exact enclosures; wall times exterior, one host). `c = ∞` reads `1801940 + 12/16` (Decision 37 reproduced, 20,223 ms). The ceilings on the development cells, `c = 5, 7, 9, 11`: `1950535 + 3/16`, `1827589 + 1/16`, `1804070 + 6/16`, `1801600 + 13/16`; against `c = ∞` `+148594 + 7/16`, `+25648 + 5/16`, `+2129 + 9/16`, `−340 + 1/16`, each decided; every passage 10,985,626 nodes and 1,371,879,880 occupied bytes, 19,940 to 20,259 ms. **The development cells choose `c = 11`**, charged 3 bits `−337 + 1/16` below `c = ∞` and below every other ceiling. Held out, once: `258018 + 5/16` (`1 + 15/16` a cell); against Decision 37's recorded `258201 + 3/16` charged 3 bits within `[−180 + 1/16, −180 + 3/16]` (uncharged `[−183 + 1/16, −183 + 3/16]`), against PPM-2's recorded `395598 + 8/16` charged 6 bits within `[−137575 + 12/16, −137575 + 14/16]`, each decided below; 12,542,969 nodes, 23,762 ms. The harness took 124,486 ms, its resident peak 1,690,034,176 bytes. The code falls with `c` through the declared family's edge. The earlier receipts: **Decision 37's tree stored where paths part** (`hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin compact`; September 26, at commit `2fb0c1c0`'s widths, `W` from `n*` alone; bytes are allocated capacity, not occupancy; the wide cut, development 917,504 = `2^17·7` cells, held out the final 131,072 = `2^17`; `n* = 2^20`, `L_R = 16`, `B = 8`; bits at the grain, each `+ ε`, exact enclosures). **The family, stated before any passage**: `D = 6, 12, 24, 48, 73` (73 the carriers' limit at `n*`, `M_p = 62`, `W = 43`), charged `⌈log₂ 5⌉ = 3` bits; about two minutes a passage, four the stop; each passage's projection (5,108,662,272 to 7,839,154,176 bytes) checked against the cap and the kernel's available memory (18,988,195,840 to 19,624,865,792 bytes) and admitted. **`D = 6` on the development cells**: the full arena `1822006 + 1/16` (Decision 35's reading, reproduced), 4,620,707 nodes, 914,361,060 allocated bytes, 16,436 ms, its certified residuals summing to `521 + 3/16`; the compacted tree `1822006 + 1/16`, 2,784,875 nodes, 435,033 label letters, 477,104,868 allocated bytes, 14,291 ms, residuals `484 + 1/16`; compacted − full `[−505516772782985345855/2^96, −505516772782985345853/2^96]` bits: equal within their certificates. **The sweep** (development, bits in all): `D = 12` `1802252 + 14/16` (8,527,193 nodes, 3,635,287 label letters, 1,920,994,548 allocated bytes, 22,078 ms), `D = 24` `1801962 + 7/16` (10,664,559; 13,760,234; 1,996,493,076; 23,988 ms), `D = 48` `1801940 + 12/16` (10,985,626; 35,373,218; 2,097,158,484; 24,936 ms), `D = 73` above it by `[51135399609700288000155/2^93, 204541598438801152000621/2^95]` (11,066,401; 58,176,774; 2,202,018,284; 25,133 ms): each step down decided (`−19754 + 12/16`, `−291 + 9/16`, `−22 + 4/16`), the last rise far inside the certificates (`9 + 2/16` at `D = 48`, `4 + 9/16` at `D = 73`): **`D = 48`**, charged 3 bits, below Decision 28's tree at `D = 6` charged its 3 (`⌈log₂ 6⌉`, Decision 35's family; the union of both families would charge each 4) by `−20066 + 10/16`. **Held out** (131,072 cells, once): the compacted tree at `D = 48` `258201 + 3/16` (`1 + 15/16` a cell), Decision 28's tree at `D = 6` `261616 + 4/16` (re-read, choosing nothing), PPM-2 `395598 + 8/16`, order-1 `496687 + 2/16`, order-0 `631713 + 1/16`; charged 3 bits it lies below Decision 28's tree by `−3416 + 15/16`, PPM-2 by `−137395 + 11/16` (a cell `−2 + 15/16`), order-1 by `−238483 + 1/16`, order-0 by `−373509 + 2/16`, each decided by disjoint exact enclosures; its development part equals the sweep's. **The scale checks** (the whole passage at `D = 48`): 12,542,969 nodes, 40,352,545 label letters, 2,097,158,516 allocated bytes (`167 rem 2482693 over 12542969` a node), 48,903,767 β rebases (1,048,556 at the most-rebased node), the largest node drift `1647016151/2^48` bits, the largest certified residual a cell `2224648115/2^46` bits within the rule `11132562458119/2^48`, 29,052 ms; Decision 28's whole passage 19,126 ms. The harness 177,535 ms; the process's resident peak 1,594,884,096 bytes. **Re-measured once with the splits counted in `W`** (`hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin compact` at the retirement of the full arena; `W = 37, 39, 41, 43, 44` at `D = 6, 12, 24, 48, 73`): every reading above at the grain is reproduced (the codes, `D = 48`, the held-out passage and each ordering); the rise at `D = 73` is now `[402375638051304080257559/2^96, 402375638051304080257561/2^96]`; the bytes occupied (96 a node, 16 a child-table entry, 4 a label letter) are 313,643,028 at `D = 6`, 969,583,660, 1,249,468,440, 1,371,879,880 at `D = 48` and 1,472,140,904 (development; allocated 477,104,868 to 2,202,018,284), and 1,566,219,572 over the whole passage at `D = 48` (allocated 2,097,158,516); the harness 168,704 ms. **Decision 36's convergence founding** (the retired `converge` mode, commit `d137e8a6`; `hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin converge .local/cuts/standing-real-cut-campaign-1.bin`; September 26; the wide cut, development 917,504 = `2^17·7` cells, held out the final 131,072 = `2^17`; `n* = 2^20`, `L_R = 16`, `B = 8`; bits at the grain, each `+ ε`, exact enclosures). **The memory and the carriers**: on the standing cut the convergence-founded tree at `D = 6` founds 20,514 nodes and holds 26,382 pending first arrivals in 4,131,412 allocated bytes (202 bytes a founded node, the pending records charged to them); a passage founds at most `n B + 2^B − 1 = 8388863` nodes and holds at most `n B = 8388608` pending records at every depth, a resident bound of 3,389,100,652 bytes at every depth, within the 20 GB cap; the carriers admit `D ≤ 73` at `n*` (`M_p = 62`, `W = 43`, the largest operand 127 bits). **The cost, stated before the sweep** (`… converge … probe 6,12,24`, 50,033 ms): development passages of 12,205, 18,317 and 19,372 ms, founded nodes levelling (3,409,859 at `D = 12`, 3,597,947 at `D = 24`); a serial sweep to `D = 73` would take at most 73 such passages (`73 · 19372 = 1414156` ms), so it ran five depths at once (`⌊20·10^9/3389100652⌋ = 5` trees at the a-priori bound, each counted alone on its worker by the thread-local counter): 4 chunks, 72,120 ms. **The depth** (development, bits in all, `D = 1, …, 20`): `3433804 + 4/16`, `2716633 + 9/16`, `2152956 + 2/16`, `1916443 + 9/16`, `1856891 + 11/16`, `1841335 + 3/16`, `1833763 + 0/16`, `1830634 + 13/16`, `1828577 + 14/16`, `1827901 + 13/16`, `1827448 + 4/16`, `1827348 + 10/16`, `1827279 + 1/16`, `1827258 + 4/16`, `1827211 + 14/16`, `1827199 + 5/16`, `1827197 + 7/16`, `1827193 + 0/16`, `1827190 + 13/16`, `1827191 + 8/16` (above `D = 19`, decided): **`D = 19`**, charged `⌈log₂ 20⌉ = 5` depth bits and `⌈log₂ 2⌉ = 1` for the founding law. Founded nodes 8,646, 69,900, 246,411, 569,438, 1,037,859, 1,580,412, 2,100,875, 2,544,950, 2,889,388, 3,137,243, 3,303,988, 3,409,859, 3,475,298, 3,515,422, 3,540,063, 3,555,658, 3,566,370, 3,574,188, 3,580,220, 3,585,039; pending records 1,401 at `D = 1` to 3,702,226 at `D = 19`; allocated bytes 1,788,100, 14,289,172, 33,032,548, 132,123,060 (`D = 4, 5`), 264,243,796 (`D = 6`), then 528,485,028 to 528,486,068 (`D = 7..20`, the table's power-of-two capacity); a passage 3,563 ms at `D = 1` to 20,751 ms at `D = 20`. **Against Decision 28's `½` tree at `D = 6`**, both read in one whole-cut passage (the convergence tree's development code equals the sweep's): development `1827190 + 13/16` against `1822006 + 1/16`; charged 6 bits against 4 (`⌈log₂ 6⌉` for Decision 35's depths and the founding bit), the convergence tree lies **above** by `5186 + 12/16` (uncharged `5184 + 12/16`): **the development cells choose Decision 28's founding at the first arrival**. **Held out** (131,072 cells, once): the convergence tree `261125 + 0/16` (`1 + 15/16` a cell), Decision 28's tree `261616 + 4/16`, PPM-2 `395598 + 8/16`, order-1 `496687 + 2/16`, order-0 `631713 + 1/16`; the convergence tree charged 6 bits lies **below** Decision 28's charged 4 by `−490 + 11/16` (uncharged `−492 + 11/16`), below PPM-2 by `−134468 + 7/16` (a cell `−2 + 15/16`), order-1 by `−235557 + 14/16` and order-0 by `−370583 + 15/16`, each decided by disjoint exact enclosures; on the standing cut's held-out part it reads `2385 + 2/16` against Decision 28's `2408 + 9/16`. **The scale checks** (the whole passage): the convergence tree at `D = 19` founds 4,091,017 nodes and holds 4,237,673 pending records, 208,414,756 stored bits and 671,092,356 allocated bytes (`164 rem 165568 over 4091017` a node) in 21,267 ms, against Decision 28's 5,110,443 nodes, 129,708,315 stored bits, 914,360,948 allocated bytes and 17,445 ms; its largest `u128` operand 127 bits, 53,320,535 β rebases (1,048,398 at the most-rebased node), 192 carrier releases (`R = 86`), the largest node drift `1808141319/2^46` bits, the rule's bound a cell `4651452039175/2^48` bits (below `1/L_R`) and the largest certified per-cell residual `39027026149/2^48` bits, within it. **What it located**: the path grows one depth a recurrence (a node meets arrivals only while its parent is present, Lean `Compression/Landmark/Context/ConvergenceFounding`'s conditional note), so on the passage's early cells the convergence tree reads shallower than a tree founded to `D` at the first arrival and codes above it; on the held-out tail, where contexts have recurred, its deeper landmarks code below it with fewer allocated bytes. The harness 112,898 ms; the process's resident peak 2,189,045,760 bytes. **Decision 35's wide cut** (`hnn_landmark -- cut-file .local/cuts/wide-real-cut.bin wide .local/cuts/standing-real-cut-campaign-1.bin`; September 26; `2^20` = 1,048,576 cells, held out 917,504..1,048,576 (`2^17` = 131,072 cells, one eighth) from the manifest, development 917,504 = `2^17·7` cells and 7,340,032 digits; `n* = 2^20`, `L_R = 16`, `B = 8`; bits at the grain, each `+ ε`, exact enclosures). **The memory**: on the standing cut the `½` tree at `D = 4` holds 63,320 nodes in 8,260,020 allocated bytes, 131 bytes a node (`130 rem 28420 over 63320`), the baselines 50 bytes a cell (`49 rem 3396 over 6148`); the resident bound `3 (n B D + 2^B − 1)` bytes a node `+ n` bytes a cell at `D = 4` reads 13,183,468,546 bytes at `2^20`, within Brandon's 20 GB cap, and 26,366,837,298 at `2^21`, above it: `2^20` is the largest power of two within the cap, and at `2^20` the depth is capped at `D ≤ 6` (`D = 7` bounds 23,032,025,537 bytes). **The depth** (development, 51,066 ms): bits a cell `3 + 11/16`, `2 + 15/16`, `2 + 5/16`, `2 + 1/16`, `2 + 0/16`, `1 + 15/16` for `D = 1..6` (`1822006 + 1/16` in all at `D = 6`), strictly decreasing to the cap: `D = 6`, charged 3 bits; the widths (`M_p`, `W`, `C`) from 50, 31, 81 at `D = 1` to 55, 36, 91 at `D = 6`. An uncapped probe (not a receipt) kept decreasing to `D = 16` (`1801976 + 15/16`): the cap binds. **Decision 32's family at scale** (an earlier full run, stopped after this stage and not repeated: 529 laws, `J = ⌈log₂(2^20 · 8)⌉ = 23`, each with its own sweep within `D ≤ 6`, 2,561,831 ms on 17 workers, resident peak 9,423,376,384 bytes): every law chose `D = 6`, and `½` lies strictly below all 528 others by disjoint enclosures, the nearest `(2, 1)` at `+136 + 11/16`, then `(3, 1)` at `+281 + 10/16`, the global rung `j = 2` at `+6746 + 12/16`: `½` is still first at scale. **One passage at `D = 6`** (every cell scored before its own deposit). The `½` tree's scale checks: the largest `u128` operand 127 bits; 5,110,443 nodes, 129,708,315 stored bits and 914,360,948 allocated bytes (`178 rem 4702094 over 5110443` a node, above the 131 measured on the standing cut; the bound's a-priori 50,331,903 nodes a tree at 131 bytes, 6,593,479,293 bytes, hold it); 43,968,100 β rebases (1,048,555 at the most-rebased node) and 1,664 carrier releases (`R = 90`); the largest node drift `22333373133/2^46` bits; the rule's bound a cell `7421708304497/2^48` bits (below `1/32`), the largest certified per-cell residual `7340494295/2^42` bits, within it. **Development** (bits a cell, and in all): the `½` tree `1 + 15/16` (`1822006 + 1/16`), the adopted law `1 + 15/16` (`1820751 + 8/16`), order-0 `4 + 12/16` (`4382811 + 1/16`), order-1 `3 + 12/16` (`3480545 + 7/16`), PPM-2 `2 + 15/16` (`2731136 + 5/16`), uniform 8. **Held out** (131,072 cells): the `½` tree `1 + 15/16` (`261616 + 4/16`), the adopted law `1 + 15/16` (`261566 + 11/16`), order-0 `4 + 13/16` (`631713 + 1/16`), order-1 `3 + 12/16` (`496687 + 2/16`), PPM-2 `3 + 0/16` (`395598 + 8/16`), uniform 8. **The orderings**, each decided by disjoint exact enclosures: Decision 34's adopted law (`½` with `(1, 3)` at `π_½ = ½`), charged 15 bits (`⌈log₂ 4082⌉ = 12` for the family it was chosen from and the depth's 3) against the `½` tree charged its 3, lies **below** it held out by `−38 + 7/16` (uncharged `−50 + 7/16`; a cell `−1 + 15/16`, within one grain) and on development by `−1243 + 7/16` (uncharged `−1255 + 7/16`): the stop mixture's gain transfers and holds out. The `½` tree charged 3 bits lies **below PPM-2** held out by `−133980 + 11/16` (a cell `−2 + 15/16`: more than one bit a cell and less than `1 + 1/16`), below order-1 by `−235068 + 2/16` and order-0 by `−370094 + 3/16`, and on development below PPM-2 by `−909128 + 11/16` (a cell `−1 + 0/16`); the adopted law charged 15 bits lies below PPM-2 held out by `−134017 + 2/16`. **The standing cut's cells** (the wide cut's tail, held out here, read at the wide standing): the `½` tree codes the standing held-out part in `2408 + 9/16` (`2 + 0/16` a cell) against `3677 + 12/16` (`3 + 1/16`) on the standing cut alone, and its lead over PPM-2 there grows from `−246 + 7/16` uncharged to `−1204 + 4/16`; on these cells the adopted law lies **above** the tree, uncharged, by `+2 + 12/16` (the standing held-out part) and `+0 + 15/16` (its development part), each decided: its held-out gain at scale is made on other cells. **Costs**: the harness 109,950 ms: the depth sweep 51,066 ms, the tree's passage 17,324 ms (counted), the adopted law's 39,504 ms (10,220,886 nodes and 264,647,533 stored bits in its 2 trees, 5,927,552 join rebases, no release, the joins' largest drift `202192655467/2^48` bits), the baselines 1,851 ms; the process's resident peak 1,271,214,080 bytes. The same passage built with overflow checks reproduced every enclosure, and on the standing cut as both cuts the mode reproduces Decision 34's held-out receipt (the adopted law charged 15 bits `−7 + 12/16` below the tree and `−249 + 4/16` below PPM-2, the tree `−243 + 7/16` below PPM-2). **Decision 34's development decision** (`hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin local`; September 26; 4,958 development cells and 39,664 digits, the held-out range cut away before anything is read; bits at `L_R = 16`, each `+ ε`, exact enclosures). The `½` tree reads `18067 + 2/16` (`3 + 10/16` a cell), its depth `D = 4` charged 3 bits common to every law. **The oracles** `Σ_u min(ℓ_T(u), ℓ_X(u)) − L_T` (before any price): the Born members at the digit grain from `−3283 + 7/16` (`Dyadic`, `χ = 1`) to `−4440 + 14/16` (`Position`, `χ = 2`), at the cell grain from `−1271 + 6/16` to `−1531 + 9/16` (`Dyadic`, `χ = 128`, whose face alone reads `4 + 3/16` a cell), at the dyadic-cell grain only `−11 + 0/16` to `−46 + 3/16`; the stop laws at the dyadic-cell grain from `−174 + 12/16` (`(1, 4)`) and `−172 + 2/16` (`(1, 3)`), and the least law in every unit `−2750 + 8/16` (digit), `−1871 + 10/16` (cell), `−244 + 9/16` (dyadic cell, 107 of 154 opened). **At each landmark** (288 members: 18 Born members × rungs `j = 1..16`, charged 9 bits; the price its family charge, the oracle's gain `4439 + 1/16`): the least is `j = 2` with `Dyadic`, `χ = 1` (an order-0 dyadic face mixed into each landmark), `−61 + 11/16` uncharged and `−52 + 11/16` charged below the tree; the other members from `0 + 0/16` to `−55 + 9/16` uncharged; the largest certified residual a cell `3170175577490309307/2^72` bits. **In each digit tree** (4,082 members: `½` against each other law at the incumbent's rungs `j = 1..16`, and the balanced global ladder and whole family, charged 12 bits; the price one bit a dyadic cell opened plus the charge, 166, against the best pair's oracle gain `173 + 3/16`; the least law in every dyadic cell refused, its naming 1,232 bits against `244 + 9/16`): the least is `½` with `(1, 3)` at `π_½ = ½`, `−133 + 7/16` uncharged (campaign 2's one-slot control exactly) and `−121 + 7/16` charged below the tree, strictly below every other member; the balanced ladder `−15 + 13/16`, the balanced family `+21 + 10/16`. **Across epochs** (234 members: 18 Born members × `α = 2^(−j)`, `j = 1..13`, charged 8 bits; the price the best switching sequence's naming, its exact Viterbi dominance bound less the oracle, plus the charge, `1473 + 9/16` against the best member's cell-grain gain `1530 + 6/16`): Decision 30's plain mixture reads `+1 + 0/16` for every member; the least is `α = 2^(−7)` with `Dyadic`, `χ = 256`, `−106 + 9/16` uncharged (its dominance bound `−65 + 2/16`) and `−98 + 9/16` charged below the tree. **Held out** (1,190 cells, once for each of the three; the tree `3677 + 12/16`, order-0 `5666 + 12/16`, order-1 `5164 + 13/16`, PPM-2 `3923 + 4/16`): **only the stop-weight mixture codes below the tree**: `3659 + 8/16` (`3 + 1/16` a cell), charged its 12 bits `−7 + 12/16` below the `½` tree, and charged 15 bits below order-0 by `−1993 + 12/16`, order-1 by `−1491 + 11/16` and PPM-2 by `−249 + 4/16`, each decided; the owner's `StopMixture` reproduces the joins' development code exactly. The node-local law reads `3685 + 15/16`, charged `+17 + 3/16` above the tree, and the switching mixture `3681 + 0/16`, charged `+11 + 4/16` above: their development gains do not hold out. **Costs**: the mixture carries two trees (126,640 nodes, 2,923,100 stored bits against the `½` tree's 63,320 and 1,426,180), its whole passage 122 ms against 41 ms, 37,910 join rebases, the joins' largest drift `172309355861276769/2^68` bits. Wall: the reads 85,174 ms (the Born members together, `Dyadic` `χ = 256` 84,472 ms), node-local 1,941 ms, the joins 10,299 ms, switching 13,286 ms, the held-out pass 62,881 ms, the harness 201,663 ms. **Decision 32's stop-prior decision** (`hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin prior`; September 26; 4,958 development cells, the held-out range cut away before the sweep; bits at `L_R = 16`, each `+ ε`): `J = ⌈log₂(6148 · 8)⌉ = 16`, so 256 laws (the global ladder `j = 1..16`, then the pairs `(j_0, j_(≥1))`), the choice charged `⌈log₂ 256⌉ = 8` bits; every law chose `D = 4` of 5 depths tried (3 bits). The `½` tree (`j = 1`) codes `18067 + 2/16` in all (`3 + 10/16` a cell), as Decision 28's sweep. Every other law is decided **above** it by disjoint exact enclosures: the global rungs `j = 2` by `68 + 1/16`, `j = 3` by `325 + 11/16`, rising to `j = 16` by `2063 + 7/16`; the per-depth laws from `(1, 2)` by `32 + 7/16` to `(15, 16)` by `2032 + 15/16`. **The choice: `½`**, strictly below every other law; charged 11 bits (8 + 3). **Where the constant-slot controls found their bits** (development, 154 dyadic cells opened; the `½` tree's dyadic cells sum to its code length): the control of `r` slots is the per-depth law `(1, r + 1)` joined with the `½` tree per dyadic cell (the test `landmark_constant_slots_are_the_per_depth_prior`, exact in ℚ), and a join codes within `[Σ_h min, Σ_h min + 154]`: `Σ_h min(L_(½,h), L_(law,h)) − L_½` is `−150 + 11/16` for `(1, 2)` (below `½` at 98 dyadic cells), `−172 + 2/16` for `(1, 3)` (91), `−174 + 12/16` for `(1, 4)` (89), `−168 + 6/16` for `(1, 5)` (86), each enclosing campaign 2's measured control (`−114 + 2/16`, `−133 + 7/16`, `−131 + 7/16`, `−124 + 10/16`). By digit level the least join gains at every level (level 0 `−54 + 5/16`, 1 of 1 dyadic cell; level 7 `−27 + 5/16`, 31 of 63), so the preference is per digit tree, not per depth or level; the least law in every dyadic cell reads `−244 + 9/16` uncharged, and naming it costs 8 bits a dyadic cell. **Held out** (1,190 cells, once, the chosen law at `D = 4`): `3 + 1/16` a cell, identical to the `½` tree; charged 11 bits, below order-0 by `−1979 + 15/16` (a cell `−2 + 5/16`), order-1 by `−1477 + 14/16` (`−2 + 12/16`), PPM-2 by `−235 + 7/16` (`−1 + 12/16`), each decided; against the `½` tree charged its 3 bits, above by the family's 8 bits. Wall: the sweep 16,873 ms (256 laws together on 24 workers), the dyadic split 22,628 ms, the held-out pass 488 ms (tree and baselines) and 225 ms (the `½` tree). **Campaign 2's development harness** (`hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin letters`; September 26; 4,958 development cells, no held-out cell read; bits in all at `L_R = 16`, each `+ ε`): the cell-only tree reproduces its sweep (`D = 4`, `18067 + 2/16`, `3` depth bits). Every one of the 30 clock-only families chose `D = 4` and is charged 8 bits (`5 + ⌈log₂ 5⌉`); every `Δ_tree` is decided **positive** by disjoint exact enclosures: at the period grains from `42 + 5/16` (rings 2 and 3) to `46 + 6/16` (rings 1 and 3), at the sheet grain from `16 + 12/16` (ring 2; uncharged `8 + 12/16`) to `34 + 0/16` (rings 1 and 3); the least charged family (ring 2's sheet) lies above the cell-only tree by `[1327838923698184517193391047693/2^96, 1327838923698184517193391057605/2^96]` bits. **The choice: the cell-only family** (`hnn::receiving::letter_family`); the clock-only phase classes carry no code-length evidence past the join's charge (at most one bit a dyadic cell opened) and their description. The harness ran in 36,678 ms. **Campaign 2's contact letters** (`… letters contacts`; September 26; the same 4,958 development cells, no held-out cell read; bits in all at `L_R = 16`, each `+ ε`): the exposure's development part on the host (2,479 windows, stopped at cell 4,958, 2,480 commits, no budget stop; 311,021 ms) read every contact a **rotation** at every commit, its whole census rotations (`K_a ≻ 0`, `C_a ≻ 0`: contact 0 → 1 ten, 1 → 2 fourteen, 2 → 3 twenty-two, 3 → 0 ten). The derived bounds are `(P, Q) = (1000, 142)` for `0 → 1`, `(142, 12)` for `1 → 2`, `(12, 0)` for `2 → 3` and `(0, 1000)` for `3 → 0`: ring 3 never winds within an aeon, so contacts 2 and 3 always read `Unlocked`, and with the constant kind their letters are constant (one feature code read). 42 families were declared (30 clock-only, 12 contact; three contact sets whose code passes 32 bits are not declarable), each charged `⌈log₂ 43⌉ = 6` bits plus `⌈log₂ 5⌉ = 3` depth bits; every one chose `D = 4`. **The constant-slot controls** (uncharged, against the cell-only tree): one slot `−114 + 2/16`, two `−133 + 7/16`, three `−131 + 7/16`, four `−124 + 10/16`: `r` constant slots after each cell make the stop weight at every cell depth past the first `1 − 2^(−(r+1))` rather than `1/2` (the constant letter's node sees its parent's counts, so `q = ½k + ½(½k + ½Π) = ¾k + ¼Π` at one slot), and the join mixes that tree with the cell tree, so the reweighting alone codes the development cells below the cell-only tree; it is the tree law's, not a letter's. **`Δ_tree`**: the informative contact families are decided **positive**: contact `0 → 1` (22 feature codes read) `45 + 0/16`, `1 → 2` (12 codes) `34 + 9/16`, both `42 + 13/16`, with the constant contacts `29 + 2/16` to `44 + 2/16`; the constant contact families are decided negative, `−105 + 2/16` (contact 2 or 3 alone, exactly the one-slot control's `−114 + 2/16` plus their 9 bits) and `−124 + 7/16` (both). The clock-only families, now charged 9 bits: period grains `43 + 5/16` to `47 + 6/16`, sheet grain `17 + 12/16` to `35 + 0/16`, all positive. **`Δ_letters`** is decided **positive for every family**: the constant contact families by exactly their `9` bits of description (`[8 + 15/16 + ε, 9 + 0/16 + ε]`), the informative contact families by `148 + 7/16` (`1 → 2`) to `176 + 11/16`, the clock-only families by `131 + 9/16` (ring 2's sheet) to `179 + 15/16`. **The choice: the cell-only family**: no letter, clock or contact, codes below the cell-only tree and its slots' control by its description; the lock addresses that vary carry less than the reweighting they ride on, and the site kinds are constant on the passage. The harness ran in 365,572 ms, the development pass included. Receipt of September 26, the lattice tree (`hnn_landmark -- cut-file .local/cuts/standing-real-cut-campaign-1.bin`; 6,148 cells, held out 4,958..6,148 from the manifest; `n* = 6,148`, `L_R = 16`, `B = 8`). **The widths** by depth (`M_p = ⌈log₂(3 B L_R (2n* + 2)(n* D² + 2D + 1))⌉`, `W = ⌈log₂(12 B L_R n* D²)⌉`, `C = M_p + W`): `D = 1` 35, 24; `D = 2` 37, 26; `D = 3` 38, 27; `D = 4` 39, 28, `C = 67`; `D = 5` 40, 28. **The sweep** (development, 4,958 cells, bits a cell): `D = 1` `4 + 0/16 + ε`, `D = 2` `3 + 12/16 + ε`, `D = 3` `3 + 10/16 + ε` (in all `18152 + 8/16 + ε`), `D = 4` `3 + 10/16 + ε` (`18067 + 2/16 + ε`), `D = 5` `3 + 10/16 + ε` (`18098 + 7/16 + ε`, above `D = 4`): `D = 4`, charged `⌈log₂ 5⌉ = 3` bits. **Held out** (1,190 cells, bits a cell): the tree `3 + 1/16 + ε`, uniform 8, online order-0 KT `4 + 12/16 + ε`, online order-1 KT `4 + 5/16 + ε`, PPM-2 `3 + 4/16 + ε`; the tree, charged its 3 bits, lies **below** order-0 by `−1987 + 15/16 + ε` bits (a cell `−2 + 5/16 + ε`), below order-1 by `−1485 + 14/16 + ε` (a cell `−2 + 12/16 + ε`) and below PPM-2 by `−243 + 7/16 + ε` (a cell `−1 + 12/16 + ε`), each by disjoint exact enclosures: Decision 28's criterion holds on the lattice. **Development** (bits a cell): the tree `3 + 10/16 + ε`, order-0 `4 + 15/16 + ε`, order-1 `5 + 1/16 + ε`, PPM-2 `3 + 12/16 + ε`; the tree below all three (`−6468 + 1/16 + ε`, `−7257 + 12/16 + ε`, `−666 + 10/16 + ε` bits). **The charts**: 63,320 nodes, 1,426,180 stored bits; 122,267 rebases (6,129 at the most-rebased node); the largest node drift certificate `|log₂ β̂ − log₂ β| ≤ 2016117919/2^43` bits; the rule's bound a cell `6192141373081/2^48` bits (below `1/32`); the largest certified per-cell residual at most `19659010511/2^44` bits. **The oracle** (`β` at `W_o = 130` bits, 58,737 rebases, its own rule below `2^(−48)` bits a cell): the executed face's cost over the ideal lies in `[−1490254332995924151010153/2^95, −2980508665991848302007893/2^96]` bits on the development cells and `[−35737173259935118265357/2^92, −142948693039740473060687/2^94]` on the held-out cells, inside `(−2^(−14), 0)` and `(−2^(−16), 0)`; every cell's observed deviation (at most `2584284295/2^48` bits) lay within its certificate. **Wall** (integer ms and µs): the sweep 846 ms; the prequential run 49,653 ms, all of it the baselines' `log2_enclosure` readings (`hnn::reference`), the tree's own prequential run (receive, code length and sum of every cell) 217 ms and its passage alone 42 ms; one all-class face read (256 classes) at the final standing 91 µs, the held-out addresses' 1,190 reads 80,744 µs in all (`67 rem 1014` over 1,190 µs a read); a clone of the final tree 2,065 µs; the oracle's run 10,861 ms. The rational-face tree of the first receipt (its faces about 3,000 bits) took 56,757 ms for the prequential run and 216,970 ms for its two sweeps. A second run reproduced every value outside the wall times

### `hnn_lattice_growth` (retired September 28, last at commit `2d34b819`)

Record: [the deposition remainder](../../records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md).

`hnn_lattice_growth.rs` runs in three modes, which its header states:

```sh
cargo run --release -p holonics --example hnn_lattice_growth -- growth chain 128 declared
cargo run --release -p holonics --example hnn_lattice_growth -- growth campaign 40 declared
cargo run --release -p holonics --example hnn_lattice_growth -- equality chain 8 declared
cargo run --release -p holonics --example hnn_lattice_growth -- equality chain 32 declared
cargo run --release -p holonics --example hnn_lattice_growth -- equality chain 32 normal
cargo run --release -p holonics --example hnn_lattice_growth -- equality campaign 8 declared
cargo run --release -p holonics --example hnn_lattice_growth -- openness configurations
cargo run --release -p holonics --example hnn_lattice_growth -- openness uniform
cargo run --release -p holonics --example hnn_lattice_growth -- openness cut
```

**What it measures** (`hnn_lattice_growth.rs growth`; the preamble table's row until September 28): The deposited constitution's exact bits after each deposit under the budgeted lattice law (precision `k_m = 2⌊log₂ m⌋ + 1` at the locus's deposit clock since its founding), split into lattice entries, carried remainders and solved charts, with the widest carried remainder, the residuals each deposit releases and their bits, the entries whose lattice coordinate moved, the wall time of each refine, compare and deposit with the projected wall time of an exposure of `n*` cells and of the declared population, and (at the first aeons) the largest move of the admitted logits between `Θ` and `Θ + r`, in grains

**Receipts.** Budgeted law under Decision 27's receiving law (receipts of September 25, this tree: the receiving map by the prox step, the receiving parametron's region class masses beside it; Decision 26's and the earlier laws' receipts are in git history). **`growth chain 128 declared`** (the chain control, declared steps, 128 deposits): the bits rise and level off near 29,000 (1,011 at the mount, 16,063 at 16, 25,247 at 64, 28,870 at 128: entries 7,416, remainders 16,684 on 516 carried entries, solved 4,770); the widest remainder 51 bits; 22 aeon boundaries release no locus and leave the bits unchanged; 39,189 residuals released over the 128 deposits (3,300,441 bits; reported, never retained); per refine 2 rem 60 over 128 ms, per compare 9 rem 93 over 128 ms and per deposit 11 rem 60 over 128 ms; the carried remainders move the admitted logits by `0`, `275/512`, `1123509/2^22`, `4623/2^20`, `4979521/2^24` and `20386641/2^24` of a grain at the first six boundaries: above one grain at the sixth only (`1 rem 3609425 over 2^24` grains, `|Δf|` reading `0 + 1/16 + ε` at `L_R = 16`), where Decision 26's law passed one grain at four of the six (the word-level certificate is owed, #62). **`growth campaign 40 declared`** (campaign 1's declared field over the pinned cut, `fed5488c…:docs/plans/THE_REBUILD.md`, 171,754 bytes; declared steps, 40 deposits): 388,880 → 388,882 → 931,522 → 1,135,697 → 1,211,919 bits at the mount and deposits 1, 16, 32, 40, against `B_Θ = 2^33` (the class masses' prior takes 197,376 of the mount's 321,048 entry bits: 257 regions of 256 masses `1/2`, each `1 + 2` bits; at 40: entries 527,151, remainders 481,647 on 16,421 carried entries, the widest 45 bits, solved charts 203,121); the deposits 4, 16, 32 and 40 release 14,986, 15,690, 15,920 and 15,928 residuals of 1,448,673, 1,660,783, 1,696,533 and 1,696,102 bits (595,419 residuals and 62,121,716 bits over the 40; reported, never retained); no aeon boundary within 40 deposits; per refine 12 rem 30 over 40 ms, per compare 17 rem 11 over 40 ms and per deposit 77 rem 38 over 40 ms, so `n* = 6,148` cells (3,074 windows) project to 331,915 rem 6 over 40 ms (4,730 ms for the 40 deposits). Superseded, with no command in this tree (an earlier law, or the live file before the cut was pinned): the exact law on the chain control, 1,126 → 10,883 → 623,415 bits over two deposits (249 s for the second); the lattice with the remainders released at the aeon collapse; campaign 1 on the live file of 194,092 bytes; and both receipts before the lattice word, whose sizes and wall times were recorded only as decimals (git history)

**What it measures** (`hnn_lattice_growth.rs equality`; the preamble table's row until September 28): The integral chart's equality with the termwise rational arithmetic, on the real cases: at every deposit each update recomputed over `Rat` alone (`ΔH`, `ΔW`, `Δh_x`, `Δx` with `Ratio`'s product), the carry's accounting `x' + r' + e = x + r + Δ` checked on every carried entry, each normal law's solved chart checked against its certificate (Decision 24: the exact left residual `‖1 − X̂H‖∞` at most the chart's certified `δ`), counted on an unmoved and on a moved Gram, and the receiving parametron's landmark deposit exactly (Decision 28): the staged steps are one per target of the window, in cell order, each at its phase's causal address, and the published tree has passed exactly those cells more (Decision 27's class-mass check, below, is its superseded predecessor)

**Receipts.** Every value equal (receipts of September 25, this tree, under Decision 27's receiving law). **`equality chain 8 declared`**: 4,752 carried entries, 32 solved charts certified on an unmoved Gram and 8 on a moved one, 160 class masses exact (189 ms). **`equality chain 32 declared`** (the chain control, 32 deposits at the declared steps): 19,008 carried entries (594 a deposit), 160 solved charts certified, 107 on an unmoved Gram and 53 on a moved one, 640 class masses exact (20 a deposit: the chain's 5 regions of 4 classes) (867 ms). **`equality chain 32 normal`** (the factor steps off): 19,008 carried entries, 118 solved charts on an unmoved Gram and 42 on a moved one, 640 class masses exact (770 ms). **`equality campaign 8 declared`** (campaign 1 on the pinned cut, 8 deposits at the declared steps): 760,648 carried entries (95,081 a deposit), 12 solved charts certified on an unmoved Gram and 36 on a moved one, 526,336 class masses exact (65,792 a deposit: 257 regions of 256 classes) (2,412 ms). The earlier laws' receipts are in git history

**What it measures** (`hnn_lattice_growth.rs openness`; the preamble table's row until September 28): Campaign 1's source-to-receiver path attenuation `2^(−Σ_a β_a Q_a/2)` within the receiver's last epoch against its grain `1/L_R` (review C2)

**Receipts.** **`openness configurations`**: open at 4,328 of the 5,005 phase configurations of the four rings. **`openness uniform`**: open on 2,627 of the 3,074 receiving windows of `n* = 6,148` uniform bytes (SplitMix64 from seed 0). **`openness cut`**: open on 73,740 of the 85,877 receiving windows of the pinned cut (the ratio `73740/85877` is reduced). Superseded, with no command in this tree: 83,703 of 97,046 on the live file of 194,092 bytes, and 2,607 of 3,074 on an unrecorded uniform draw

### `hnn_diagnose` (retired September 28, last at commit `2d34b819`)

Record: [the located failure](../../records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md).

`hnn_diagnose.rs` locates campaign 1's failure on the standing cut (review E1: the located cause
before campaign 2). It runs the exposure protocol step for step through the host reference's
`ExecutionPort` and reads between the port's methods, so it changes no law and adds no accessor; it
reproduces the exposure's bits first, as its check. Its four sections are the candidate causes:
the decoder (the mean logit vector's static face, the read features' rank and dormant component,
and the least-squares oracle `R = y wᵀ` scored through the machine's own face), learning (per
deposit the exact update of `R` and `E_0` from the carry's accounting, the leverage `zᵀX̂'z` and
the read logits' executed move, the prior's reading `R_0 z` against the learned part, the covector's
phase share, and the bound `Σh ≤ ln det H_T`), the keys (on synthetic cribs generated by the
declared ring with a true key, and on the standing cut the crib's best injective partial closure
against its own shuffles), and the source and encoding (capacity against `n*`, the path's openness,
online KT given the rings' phase classes, the source ring's bins, and the recent cells' share of the
current bin). Its receipt and reading are the
[located-failure record](../../records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md):

```sh
cargo run --release -p holonics --example hnn_diagnose -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
```

**What it measures** (`hnn_diagnose.rs`; the preamble table's row until September 28): Campaign 1's located failure on the standing real cut (review E1): campaign 1's protocol step for step through the port (held-out windows discarded, not the prequential exposure's), with the decoder's, learning's, the keys' and the source's readings between its methods. Under Decision 28 its decoder readings take the landmark tree's grain logits at each phase's causal address out of the machine's face and read the wave alone

**Receipts.** Not rerun under Decision 27. Receipt of September 25, under the receiving law before Decision 26 (at `13d6bb92`; `hnn_diagnose -- cut-file .local/cuts/standing-real-cut-campaign-1.bin`, 614 s for the exposure; its rerun with the exact print reads the same values). The exposure's bits reproduce exactly (held-out `7 + 9/16 + ε` against order-0 KT `4 + 12/16 + ε`, bits a cell at `L_R = 16`). Held out, bits a cell through the machine's face: the declared prior's reading `R_0 z` alone `10 + 9/16 + ε`, the machine `7 + 9/16 + ε`, the learned part alone `6 + 11/16 + ε`, the least-squares oracle `R = y wᵀ` on the machine's own features `5 + 0/16 + ε` (`4 + 15/16 + ε` in-sample), the static order-0 face `4 + 12/16 + ε`. The prior's reading holds a share in `[51/56, 3713/4077]` of the held-out logits' energy; `Σh = 141 + ε`, `ε ∈ [2871/3571, 3154/3923]`, against `ln det H_T ∈ [62482/407, 621904/4051]`, below it by `[30317/2588, 26768/2285]`; the constant's reach from ring 2's dormant mode lies in `[3255/4057, 1108/1381]`. Keys: the truth in the fibre on 128 of 128 synthetic cribs; on the cut every fibre empty and the best injective partial closure within its shuffles at 15 of 16 ring-locations. Source: online KT given `τ_0 mod 5` `4 + 14/16 + ε` and given the whole configuration `7 + 12/16 + ε`, against order-0's `4 + 12/16 + ε`; the recent cells a median `1/132` of the source ring's current bin. The reading is the [located-failure record](../../records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md)

### `hnn_born` (retired September 28, last at commit `2d34b819`)

Record: [the landmark tree at scale](../../records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) (the Born face measured negative).

`hnn_born.rs` measures the Born receiver (THE_REBUILD Decision 33, `holonics::hnn::born`, Lean
`HNN/BornFace`) on the standing cut's development cells, beside the landmark tree's current law
(the receiver's declaration through `hnn::receiving::landmark_declaration_with`, cell-only, `D =
4`): each cell scored before its own deposit, for the Born face alone, the tree alone and Decision
30's likelihood mixture of the two (`hnn::receiving::Mixture`, `β` stepped by `q_T(x)/q_B(x)` on the
landmark β chart; retired at THE_REBUILD U1, history at `19f1eb61`). The declared family is both emissions (`Position`: a pair of operators per digit
position; `Dyadic`: a pair per dyadic cell, the tree's forced split) at every register width
`χ = 2^j`, `j ≤ J`, the cost bound (`14·4^J·B·n_dev ≤ 2^37` complex products a passage: `J = 8`),
stopping before a width the receiver's carrier refuses at the declared population (at `n* = 2^20`
the solve's residual needs 128 bits at `χ = 32`), charged `⌈log₂⌉` of the members tried; each
population's faces are multiplied and enclosed once (`context::PassageCode`). The choice is the
least charged development mixture; a held-out pass runs only if it codes below the tree by
disjoint enclosures. It prints each member's widths,
code lengths at the grain, the orderings mixture − tree and Born − tree, `log₂ β`, the receiver's
chart receipts (the solve's refinements and certificate, the preconditioner's refreshes, the
state's rebases) and the wall time a digit:

```sh
cargo run --release -p holonics --example hnn_born -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
```

Receipt of September 26 (development cells only, 4,958 cells and 39,664 digits; no held-out cell
read; wall times exterior, one host, the run alone): the tree reads `3 + 10/16 + ε` bits a cell
(`18067 + 2/16 + ε` in all). Eighteen members were tried (both emissions, `χ = 1, …, 256`), charged
`⌈log₂ 18⌉ = 5` bits. The Born face alone, bits a cell (`+ ε` each), by `χ = 1, 2, 4, …, 256`:
`Position` `5 + 14/16`, `5 + 14/16`, `5 + 12/16`, `5 + 8/16`, `5 + 2/16`, `4 + 13/16`, `4 + 9/16`,
`4 + 9/16`, `4 + 7/16`; `Dyadic` `4 + 13/16`, `4 + 13/16`, `4 + 14/16`, `4 + 10/16`, `4 + 8/16`,
`4 + 6/16`, `4 + 5/16`, `4 + 3/16`, `4 + 4/16`. The least is `Dyadic`, `χ = 128`: Born − tree
(charged) `2780 + 8/16 + ε` bits in all, `8/16 + ε` a cell, and `log₂ β` ends at `2775 + 8/16 + ε`.
Every member's mixture codes above the tree by disjoint enclosures, mixture − tree (charged)
`6 + 0/16 + ε` in all for all eighteen: the mixture's own `½` prior bit plus the charge, as the
telescope `∏ q = ½W_T + ½W_B` gives when `L_B > L_T`. The least charged mixture is `Dyadic`,
`χ = 16`; no member codes below the tree, so no held-out pass ran. The charts: every solve certified
within at most 4 refinements, the largest certificate below `2^(−C)`, no preconditioner refresh, and
a build with overflow checks reproduced every reading. A digit costs, `Dyadic`: `17 rem 5712 over
39664` µs at `χ = 16`, `365 rem 14640 over 39664` µs at `χ = 128`, `1253 rem 22008 over 39664` µs
at `χ = 256` (`Position` `1175 rem 6800 over 39664`); the harness took 168,717 ms.

### `hnn_curated` (retired September 28, last at commit `2d34b819`)

Record: [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md).

`hnn_curated.rs curated` reads the cut as typed letters: each tick's bundle is its cell with its
channel (3 letters) and its section letter (4), `LetterFamily::new([3, 4])`, against the same tree
on the flat bytes and the curated cell tree (letters as cells, no slots); each the `½` prior and
the KT node, stored where paths part, depths doubling from 6 to its carriers' deepest, charged, the
curated family charged one bit more. `200135` ms in all (the sweeps, run together, `144313` ms;
the held-out passages `53996` ms), against `196696` ms before the sections followed the declared
turn.

```sh
HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/curated_source.py 1048576
cargo run --release -p holonics --example hnn_curated -- curated .local/cuts/curated-cut.bin .local/cuts/curated-flat-cut.bin
```

[established-bounded; measured] Development cells (bits at `L_R = 16`, each `+ ε`, exact
enclosures in the output; the reading before the sections followed the declared turn in
brackets): the flat tree chooses `D = 48` of `6, 12, 24, 48, 73` (`1800742 + 1/16`, unchanged), the
curated cell tree `D = 48` of `6, 12, 24, 48, 69` (`1804816 + 6/16`; `1804014 + 8/16`), the typed
tree `D = 16`, its carriers' deepest (`P = 4D + 2`), of `6, 12, 16` (`1803437 + 13/16`;
`1803629 + 11/16`); the typed tree charged lies `−1380 + 7/16` below the cell tree (`−386 + 2/16`)
and is the curated source's tree. On identical bytes it codes below the flat tree: human
`146345 + 8/16` against `147346 + 0/16` (`−1001 + 7/16`; `−910 + 9/16`; `2 + 3/16` against
`2 + 4/16` a cell), agent `1651317 + 6/16` against `1653396 + 1/16` (`−2079 + 5/16`;
`−1379 + 8/16`), every byte `−3080 + 13/16` (`−2288 + 2/16`). Its 1,477 section letters cost
`5774 + 15/16` (`3 + 14/16` a letter; `5175 + 6/16`, `3 + 8/16` a letter). Reading the declared
turn moves the letters by `+599 + 8/16` and the bytes against the flat tree by `−792 + 10/16`
(exact enclosures of the two runs' difference), the whole by `−192 + 2/16`: the whole curated stream
charged, `1803440 + 13/16`, lies `+2695 + 12/16` above the flat stream's bytes alone
(`+2887 + 9/16`). PPM-2 reads `2732822 + 4/16` on the curated stream (its letters `6233 + 6/16`;
`2731908 + 12/16`, `5288 + 0/16`) and `2729576 + 9/16` on the flat; order-0 `4388967 + 2/16`
(`4388015 + 3/16`) and `4370438 + 1/16`; each tree lies below PPM-2 on its own stream by
`−929382 + 9/16` (`−928277 + 14/16`) and `−928832 + 8/16`. **Held out, once**: the flat tree
`258233 + 7/16` (human `76584 + 8/16`, agent `181648 + 14/16`, unchanged), the typed tree
`258072 + 12/16` (human `76036 + 6/16`, agent `181353 + 14/16`, 150 letters `682 + 7/16`, `4 + 8/16`
a letter; `258105 + 10/16`, `76091 + 12/16`, `181365 + 3/16`, `648 + 11/16`, `4 + 5/16`); on
identical bytes human `−549 + 13/16` (`−493 + 3/16`), agent `−296 + 15/16` (`−284 + 4/16`), every
byte `−844 + 13/16` (`−777 + 7/16`); the whole curated stream charged, with its sections, lies
`−161 + 4/16` below the flat stream's bytes alone (`−128 + 3/16`; the letters moved by
`+33 + 12/16`, the bytes by `−67 + 5/16`, the whole by `−33 + 1/16`); PPM-2 `395832 + 1/16`
(`395728 + 5/16`) and `395425 + 15/16`, each tree below it by `−137757 + 11/16` (`−137620 + 4/16`)
and `−137190 + 7/16`. [agent-inferred] The channel changes only at a section letter, yet as a slot
it repeats in every bundle, and the enlarged tree's path depth (`D + 3D + 2`) caps the typed tree
at `D = 16`, where the deeper cell tree reads agent cells lower (`1651288 + 0/16` at `D = 48`
against the typed tree's `1651317 + 6/16`): the tree needs a letter family per channel (each port
its own tree, the channel read at its section), not a channel slot in every bundle. The standing
cut and the wide cut stay the regression controls.

**What it measures** (`hnn_curated.rs curated`; the preamble table's row until September 28): The curated cut read as typed letters (channel and section slots) against the flat tree on identical bytes and the curated cell tree: each tree's doubling depth sweep on the development cells, charged, per channel and at the section letters, beside order-0 and PPM-2, then one held-out passage; development receipts, counts and bits only

**Receipts.** Development: bytes `−3080 + 13/16 + ε` below the flat tree, the letters `5774 + 15/16 + ε`, the whole `+2695 + 12/16 + ε`; held out: bytes `−844 + 13/16 + ε`, the whole with its letters `−161 + 4/16 + ε`

### Loaded resonator comparison (Decision 38)

Record: [the resonator returns its wave](../../records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md).

The exposure now accepts `resonator source` (default `resonator none`). It declares one loaded
resonator on source ring 0: the ring's unit parametron supplies C/K, D is the campaign's initial
passive rate I/4, no pump is declared, and the scalar material amplitudes start at 1. The same
exposure protocol scores the faces before their deposits and charges the initial material.
No value is selected by this passage. The standing cut remains development material.

Run a `2⁵`-window development pilot first. Admit the full passage only if its exact wall-time
projection fits ten minutes per realization; a deadline or refusal is an incomplete receipt.
Run the GPU work alone under the repository lock after the law suites.

```sh
cargo run --release -p holonics --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all windows 32 resonator source
flock .local/gpu.lock cargo run --release -p holonics-cuda --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all windows 32 realization card resonator source
# after each realization passes its cost projection, omit `windows 32` for its full passage
```

[Decision 38's receipt](../../records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md)
records exact host/card agreement over the full passage. The loaded family loses to the default
HNN on development and scored-tail cells, before its extra material description, so
`resonator none` remains the default. The final dissipation amplitude is `273/256`. Its loaded
power balance and reached covectors establish the consumer needed by campaign 3. The exposure
also prints each final gain's carried remainder, what reached the family below its lattice's
unit; the word balances' bound covers the resonator's solve and split, and the interconnection's
defect is zero by construction for a loaded port (the September 27 repair in the same record).

### Terrain a declared Holarchy made (the record of September 27, §3.3 and §5)

Record: [the Holarchy and its aeons](../../records/2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md) (`hnn_terrain`, retired September 28, last at commit `2d34b819`).

`hnn_terrain.rs` runs the count-only landmark tree on terrain whose truth is exact
(`holonics::holarchy::terrain`; its header states the declarations). These are **development
receipts, not milestones**: the conversation cut stays the living substrate and the milestone
(Brandon's ruling of August 26), and no claim here is joined to the cut's. Every terrain is drawn
by the seeded draw `20260927`; each run takes under four seconds.

```sh
cargo run --release -p holonics --example hnn_terrain -- tree 2
cargo run --release -p holonics --example hnn_terrain -- tree 4
cargo run --release -p holonics --example hnn_terrain -- moire
```

**Tree sources** over bits (faces on `1/16`, `n = 2^16` cells, the `½` tree at `D = d + 2`,
`L_R = 16`; each reading `n + k/16 + ε`, the exact endpoints in the output):
- `d = 2`: `|S| = 3` leaves `[00] [01] [1]`, stationary `(3/16, 5/16, 1/2)`; the rate
  `h = 7/2 − (63/256) log₂ 3 − (95/256) log₂ 5 − (33/256) log₂ 11 − (65/256) log₂ 13` bits a cell,
  `n·h = 56543 + 13/16 + ε`. The tree codes `56464 + 2/16 + ε` (PPM-2 `56562 + 1/16 + ε`); the
  redundancy `code − n·h = −80 + 4/16 + ε` (the passage's own code lies below `n·h`), and against
  the source's own code of the realized cells `27 + 1/16 + ε`, below the ideal tree's weighting
  bound `Γ(S′) + Σ(½ log₂ n_s + 1) + b = 7 + (24 + 7/16 + ε) + 2 = 33 + 7/16 + ε` (the headline
  `½|S| log₂ n + Γ(S′) = 31`); with the chart's certified drift (`n` times the largest per-cell
  residual) the bound is `222 + 11/16 + ε`. The recovered tree is the drawn one, all 16
  addresses agreeing.
- `d = 4`: `|S| = 8` leaves, rate `0 + 11/16 + ε` a cell, `n·h = 47257 + 8/16 + ε`; the tree codes
  `47134 + 11/16 + ε` (PPM-2 `51349 + 4/16 + ε`); the redundancy `−123 + 3/16 + ε`, against the
  source's own code `51 + 4/16 + ε`, below the ideal bound `22 + (55 + 5/16 + ε) + 2 = 79 + 5/16 + ε`
  (headline `86`). The recovered tree has 7 leaves: it merges the drawn `[0000]` and `[0001]`,
  whose drawn faces are both `(9/16, 7/16)`, so it is the source's minimal tree (the coarsest tree
  reading the same faces) exactly, all 64 addresses agreeing with it and 56 with the drawn spelling.

**The moiré** (3 gratings, denominators up to `2^4`, `n = 2^14` cells): rates and phases
`14/15 @ 5/15`, `4/15 @ 10/15`, `11/16 @ 12/16`; joint and least period `240 = 2^4·3·5`; the locks
`7/2`, `224/165`, `64/165` (the contact law over one joint period reads `7/2`, `19/14`, `7/18`);
the rate zero; the key description `⌈log₂ 862³⌉ = 30` bits (`862 = 2·431`). The harness's depth
rule (`choose_depth_within`: `D` rises while the code falls strictly) **stops below the terrain's
determining depth `D*`**, at the first plateau of the code in `D`:
- parity color (`D* = 14`): chosen `D = 10`, code `2016 + 6/16 + ε` (the key description plus
  `1986 + 6/16 + ε`), each later period `17 + 13/16 + ε` by period 67; the code by depth reads
  `D = 10, 11: 2016 + 6/16, 2018 + 6/16`, `D = 12, 13: 1501 + 12/16, 1501 + 13/16`, `D = 14: 993 + 5/16`
  (each `+ ε`). At the control `D = D* = 14` (the truth's, never a choice) the code is
  `993 + 5/16 + ε`, the periods `245 + 3/16`, `209 + 5/16`, `102 + 2/16`, `57 + 6/16`, then
  `17 + 7/16` (period 7), `4 + 2/16` (31), `1 + 14/16` (67), `5 + 14/16 + ε` a period over periods
  4 to 67: the zero-rate terrain's code is its first periods plus the tree's own learning,
  `963 + 5/16 + ε` bits past the key's 30;
- sheet tuple (`D* = 8`): chosen `D = 5`, code `5427 + 1/16 + ε`, `62 + 10/16 + ε` a period by period
  67; at `D* = 8` the code is `1549 + 0/16 + ε`, `2 + 15/16 + ε` by period 67. Online order-0,
  order-1 and PPM-2 read `16391 + 5/16`, `16394 + 6/16`, `16165 + 8/16` (parity) and
  `48632 + 0/16`, `36798 + 10/16`, `17406 + 13/16` (tuple).

### The arithmetic terrain (the record of September 27 on the faces of integers, §7 and §9)

Record: [the faces of integers](../../records/2026-09-27_THE_EGG_IS_A_GENERATORS_GENOME_SELECTION_IS_BAYES_AND_THE_FACES_OF_INTEGERS_ARE_MOIRES_OF_GRATINGS.md) (`hnn_terrain arithmetic`, retired September 28, last at commit `2d34b819`).

`hnn_terrain.rs`'s `arithmetic` mode (`hnn_terrain_arithmetic.rs`, its header states the
declarations) runs the same count-only tree on `holonics::holarchy::terrain::arithmetic`, through
the prequential harness, and reads **the code on each cell class separately** (`tree_prequential`
with the class's cells as the scored-apart range, one tree run a class, every cell scored before
its own deposit) against its truth: the operand cells at `2L log₂ b` bits a record, exactly, and
every determined cell at zero. These are development receipts, not milestones. Each run states its
cost first; the mode takes about 40 seconds in all (products 14, 8 and 9 seconds, primes 3, 5 and
under 1), its peak resident set `158064` to `158504` kB over two runs, whose readings agree exactly.

```sh
cargo run --release -p holonics --example hnn_terrain -- arithmetic
```

**Products** (`L = 4` digits least significant first, `k = 2`, `2^12` records `a ⊗ c = P ;` of 19
cells drawn by the seed `20260927`, `n = 77824 = 2^12·19`; per class the operand cells
`32768 = 2^15`, the marks `12288 = 2^12·3`, the product's trailing `8192 = 2^13`, middle
`16384 = 2^14` and leading `8192` cells; each reading `+ ε`):

| base | chosen `D` | passage (PPM-2) | operands (truth) | marks | trailing | middle | leading |
|---|---|---|---|---|---|---|---|
| 2 | 13 | `41557 + 8/16` (`122726 + 13/16`) | `33179 + 11/16` (`32768`) | `1524 + 0/16` | `1422 + 4/16` | `3966 + 1/16` | `1465 + 6/16` |
| 10 | 5 | `273520 + 7/16` (`286584 + 13/16`) | `114394 + 15/16` (`32768 + 32768 log₂ 5 = 108852 + 15/16`) | `41600 + 2/16` | `26466 + 6/16` | `60508 + 10/16` | `30550 + 4/16` |
| 16 | 4 | `320308 + 10/16` (`342827 + 13/16`) | `137510 + 1/16` (`2^17`) | `41831 + 7/16` | `32396 + 10/16` | `72206 + 12/16` | `36363 + 10/16` |

A cell, in the same order: base 2 `1 + 0/16`, `0 + 1/16`, `0 + 2/16`, `0 + 3/16`, `0 + 2/16`; base 10
`3 + 7/16`, `3 + 6/16`, `3 + 3/16`, `3 + 11/16`, `3 + 11/16`; base 16 `4 + 3/16`, `3 + 6/16`,
`3 + 15/16`, `4 + 6/16`, `4 + 7/16`. The operands exceed their entropy by `411 + 11/16`,
`5542 + 0/16` and `6438 + 1/16` bits. At the control `D = 18` (the record span `4L + 2`, declared,
never chosen) the passages read `41624 + 12/16`, `273781 + 11/16` and `320400 + 12/16`, and every
class within a few hundred bits of the chosen depth's. The leading fibre is one reading wide in
`2285`, `790` and `711` records, two in `1811`, `2737` and `2734`, three in none, `569` and `651`.

In base 2 the `2^8` operand pairs recur sixteen times on average, and the tree at `D = 13` nearly
memorizes the table: every determined cell costs at most `0 + 3/16` a cell. In bases 10 and 16 the
pairs never repeat (`10^8` and `2^32` pairs against `2^12` records), the tree stops at `D = 5` and
`4`, and every determined cell, the marks included, costs between `3 + 3/16` and `4 + 7/16` bits a
cell, near a digit's own code: the tree reads neither the trailing face nor the record's position.
A suffix context cannot reach past the drawn digits between a cell and what determines it (the
mark `⊗` follows the previous `;` by `L + 1` cells, with `L` drawn digits between), so every face
here, being placed by digit position, is out of its reach.

**Primes** over `[0, 10^4)` (`1229` primes, itself prime; the density `1229/10000`): the density's
code `10^4 H(1229/10^4) = 40000 log₂ 10 − 17542 log₂ 7 − 8771 log₂ 179 − 1229 log₂ 1229`
(`8771 = 7²·179`) reads `5376 + 6/16 + ε` bits; through the faces `n mod 2`, `6`, `10` and `30`,
`4034 + 14/16`, `3188 + 0/16`, `3580 + 4/16` and `2682 + 14/16`. The truth of every cell is zero.
- Base 10, four digits most significant first and the primality cell (`n = 50000 = 2^4·5^5`):
  chosen `D = 4`, the passage `161780 + 4/16` (PPM-2 `171808 + 13/16`); the digit cells
  (`40000`) `146345 + 2/16`, `3 + 10/16` a cell; the primality cells (`10000`) `15435 + 1/16`,
  `10058 + 11/16` above the density's code and `11854 + 13/16` above the face `n mod 10`'s. At the
  control `D = 5`: `146596 + 9/16` and `15369 + 7/16`.
- Base 6, six digits (`n = 70000 = 2^4·5^4·7`): chosen `D = 6`, the passage `164718 + 10/16`; the
  digit cells (`60000`) `145167 + 12/16`, `2 + 6/16` a cell; the primality cells `19550 + 13/16`,
  `14174 + 7/16` above the density's code and `16362 + 12/16` above the face `n mod 6`'s. At the
  control `D = 7`: `145595 + 8/16` and `19343 + 2/16`.
- The bare indicator (`n = 10^4`): chosen `D = 1`, `5150 + 6/16` (order-1 KT `5149 + 6/16`, order-0
  `5383 + 5/16`); against the density's code the difference reads `−227 + 15/16 + ε`, the tree below
  it (its count follows the density's fall along the window, and its one cell of context reads that
  no two primes past 3 are adjacent); it lies `1115 + 8/16` above the face `n mod 2`'s code and
  `1962 + 5/16` above `n mod 6`'s.

The primality cell pays for its position as the products' marks do, so on the digit emission it
codes above the density's code, and the counter's digits (an odometer, determined by the record
before) cost `2 + 6/16` to `3 + 10/16` a cell.

**What the arithmetic families need from the population owner** (`receiver::population`; the next
construction, not this step): the population's eggs must be able to address a cell by its place in
a declared record, which the suffix tree cannot. A **record clock** (a navigator on the record's
period, `4L + 3` or `L + 1`, keyed at its offset) makes the marks and positions cost zero once
located. A **convolution-and-carry egg** reads the operands' digits by place relative to that
clock, carries the winding as its state, and emits the product's digits (its genome: `b`, `L`, the
order and the layout, with a declared description cost). A **counter egg** is the odometer's
increment with carry. A **sieve egg** lays the gratings `p ∤ b` on the leading index with their
classes, founded at the gaps (the terrain's open founding law), beside the cheap faces of the
declared base. The population needs a declared prior carrying each egg's description cost (Kraft
mass declared), the tree kept as one egg, and a per-class reading of the prequential code, so that
selection is gauged class by class against these truths; one run partitioned by class in
`hnn::reference` would replace the one run a class used here.

#### Population release checks on known-truth terrain (September 27; retired September 28)

`hnn_release_terrain.rs` (at [`2d34b819`](https://github.com/brandonrdug/holonics/tree/2d34b819/research/notebook/hnn_design/hnn_release_terrain.rs)) ran three checks
by the seed `20260927`; its receipt at that commit, now the law fixtures
`receiver::population::releasing_tests::terrain`:
- **The full-future check.** On the grating keys of a moiré of two rings over `ℤ/5` (sheet tuples),
  the population's face is one-hot on the truth at tick 4, yet the surviving keys part at tick 5
  within the joint period 20: the exact face `(2/3, 1/3, 0, 0)` against truth class 0. A one-hot
  present face is a candidate, and it counts as future-equivalent only across the whole joint
  period.
- **Products.** The composed record-clock/carry key first predicts a determined cell at cell 3 of
  the one-digit binary record `1·1`, and every later determined face matches the product's truth
  through the record stop.
- **The stochastic face.** The receiving tree (`D = 3`, the `½` stop prior) over a drawn binary tree
  source reads 1,024 cells: none of its faces equals the identified conditional truth face, each
  separator an exact difference; the first, at tick 0, is `±223696213/2^30`.

## The egg population on terrain (rebuild step 4 item 4, September 27)

Record: [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md).

`hnn_population.rs` runs the egg population (`holonics::receiver::population`: a receiver's
Bayesian mixture over declared navigator families, the discrete replicator, each family dying
exactly at zero likelihood) on the terrains above, and asks whether it selects the family that made
each. These are **development receipts, not milestones**; the conversation cut stays the milestone.
Every run takes under half a second except `switching`: the sheet tuple's in seconds, the parity
color's in about two minutes, its dormant family carrying tens of thousands of joint keys.

```sh
cargo run --release -p holonics --example hnn_population -- tree 2
cargo run --release -p holonics --example hnn_population -- tree 4
cargo run --release -p holonics --example hnn_population -- moire parity
cargo run --release -p holonics --example hnn_population -- moire sheets
cargo run --release -p holonics --example hnn_population -- crib
cargo run --release -p holonics --example hnn_population -- switching [parity | sheets]
cargo run --release -p holonics --example hnn_population -- standing .local/cuts/standing-real-cut-campaign-1.bin
```

The declared population on each terrain: the receiving tree (cell-only, `½` stop prior) at every
depth of the ladder `D ∈ {1, 2, 4, 8, 16, 32}`, and one key family of the terrain's kind. Seven
families, each named by `⌈log₂ 7⌉ = 3` bits: the Kraft mass is `7/8`, its unused `1/8` declared, and
the prior is `1/7` a family. Survivor filtering enumerates at most `2^24` keys. Each reading is
`n + k/16 + ε`, the exact endpoints in the output. `−log₂ w` is a family's posterior in bits.

- **Tree source `d = 2`** (the terrain section's source): the population codes `56463 + 14/16 + ε`,
  `−80 + 0/16 + ε` against `n·h` and `26 + 14/16 + ε` above the source's own code of the realized
  cells. It selects the tree at `D = 2`, the source's depth: its code alone is `56462 + 0/16 + ε` and
  its posterior `−log₂ w = 0 + 15/16 + ε`, decided above one half. The trees at `D ≥ 4` read
  `3 + 0/16 + ε` each, and `D = 1` reads `5931 + 4/16 + ε`. The grating keys (`k = 3`, `q ≤ 2^3`,
  parity) die at cell 15. The selected tree recovers the drawn tree `[00] [01] [1]` exactly.
- **Tree source `d = 4`**: the population codes `47134 + 9/16 + ε`, `−123 + 1/16 + ε` against `n·h`
  and `51 + 2/16 + ε` above `code_θ(x)`. It selects the tree at `D = 4`, whose posterior is
  `0 + 11/16 + ε`; `D = 8, 16, 32` read `2 + 15/16 + ε` each. The grating keys die at cell 13, and
  the selected tree recovers the minimal tree exactly (16 of 16 addresses).
- **Moiré, parity color, `k = 3`, `q ≤ 2^3`**, drawn by the seed from `N_8 = 122 = 2·61` gratings a
  ring, so `122³ = 1815848 = 2³·61³` keys:
  - The drawn gratings are `5/7 @ 0/7`, `3/8 @ 6/8` and `7/8 @ 6/8`; the joint period is
    `56 = 2³·7`, the least period `14 = 2·7`, and `D* = 7`.
  - The grating family keeps **720 = 2⁴·3²·5** survivors, the drawn key among them: every key that
    emits the same parity word, one species of the face map's quotient over generators. The species
    is wider than a gauge orbit. By denominators it is `(7, 8, 8)` 384, `(3, 6, 7)` 144,
    `(2, 7, 7)` 96 and `(4, 4, 7)` 96: 336 survivors hold no period-8 pair and 384 no `5/7` ring
    (for example `1/2 @ 1/2`, `1/7 @ 3/7`, `1/7 @ 5/7`). Besides the rings' permutations it holds
    each ring's mirror, the half-turn of a rate `p ↦ p + q/2` on an even `q` (two such rings cancel
    their flips on the odd ticks) and coincidences across denominators. **The parity class locates
    the word, neither the rates nor the rings** (a brute force over the `122³` keys:
    `the_parity_fibre_is_one_word_not_one_rate`).
  - Its code is `log₂ 122³ − log₂ 720 = 11 + 4/16 + ε`, against the key description
    `log₂ 122³ = 20 + 12/16 + ε` (`⌈⌉ = 21`).
  - The population codes `14 + 1/16 + ε`, the family's code plus its naming `log₂ 7`, and selects the
    gratings: their posterior is `0 + 0/16 + ε`, the tree kind's `66 + 0/16 + ε`. The best tree
    (`D = 8`) codes `78 + 13/16 + ε` alone.
  - At `q ≤ 2^4` the parity class's `862³ = 640503928 = 2³·431³` keys are refused, and the refusal
    names the owed Bombe, parity-constraint propagation on the joint clock torus.
- **Moiré, sheet tuple, `k = 3`, `q ≤ 2^4`**, the terrain section's moiré, factorized per ring
  (`862 = 2·431` keys a ring):
  - Each ring keeps **2** survivors: its grating and its mirror `(q − p)/q`, the phase half-turned about the
    centre of the ring's upper sheet arc (`c ↦ ⌈q/2⌉ + q − 1 − c mod q`). A half-turn sheet cannot
    tell a ring from its mirror, its half-turn. The pairs are `14/15 @ 5/15 ~ 1/15 @ 2/15`,
    `4/15 @ 10/15 ~ 11/15 @ 12/15` and `11/16 @ 12/16 ~ 5/16 @ 11/16`.
  - The family's code is `log₂ 862³ − 3 = 26 + 4/16 + ε`, against the key description
    `29 + 4/16 + ε` (`⌈⌉ = 30`).
  - The population codes `29 + 0/16 + ε` and selects the gratings (the tree kind's posterior
    `1521 + 5/16 + ε`). The tree at `D = 8 = D*` codes `1549 + 0/16 + ε` alone, the recorded
    control; the recorded parity control at `D* = 14` is `993 + 5/16 + ε`.
- **Rotor crib**: campaign 1's period-7 ring, locked at every port so it steps each tick, behind a
  drawn plugboard, `n = 2^10`. The family's keys are the start, the key and the plugboard,
  `7·7·7! = 246960 = 2⁴·3²·5·7³` of them:
  - It keeps **7** survivors: the rotor-gauge orbit at the drawn start, the drawn key and plugboard
    among them.
  - Its code is `log₂ 35280 = 15 + 1/16 + ε`: the start's `log₂ 7`, plus the key description
    `log₂(7·7!)` (`⌈⌉ = 16`), less the gauge's `log₂ 7`.
  - The population codes `17 + 14/16 + ε` and selects the rotor keys. The best tree
    (`D = 16, 32`) codes `375 + 12/16 + ε`.
  - Ring 2's `11²·11! = 4829932800 = 2⁸·3⁴·5²·7·11³` keys are refused, and the refusal names the
    built Bombe, `hnn::keys::locate_ring`.
- **Aeon switching, the dormant grating: campaign 3 at the population** (#73; grating 0 of the
  parity moiré silent in the odd aeons, which run `2^10` to `2^11` cells). The truth: 11 switches,
  at cells 1223, 3018, 4511, 5730, 6761, 8104, 9672, 11548, 12879, 14341 and 15518. A switch pays
  `j = ⌈log₂ n⌉ = 14` bits at `α = 2^(−14)` (the `log₂` of its positions), and the positions' own
  count reads `log₂ C(n − 1, 11) = 128 + 11/16 + ε`. Four populations read the same cells: the
  static one (trees and the static gratings, `M = 7/8`), the one with dormancy (and the dormant
  gratings, eight families of 3 bits, `M = 1`), the born one (the static one founding the dormant
  gratings from its reserved `1/8` at a section, every `2^8` cells, whose residual passes the 3-bit
  charge) and the reseeding one (the static one re-founding its dead gratings' seed).
  - **Sheet tuple:**
    - Static: the gratings die at cell 1223, where class 4 arrived against their certain 5, ring 0's
      factor exhausted. Their mass (`−log₂ w = 0 + 0/16 + ε`) passes to the trees, `1 + 9/16 + ε`
      bits of it to each of `D = 8, 16, 32`. The population codes `688 + 6/16 + ε` (the recorded
      receipt), `667 + 12/16 + ε` above the unswitched `20 + 9/16 + ε`.
    - With dormancy: ring 0's grating and mirror are held through every silent aeon (survivors
      `[2, 2, 2]` at every checkpoint, the fibre's mass `−log₂ = 0 + 0/16 + ε`). At the silent
      aeon's end the layer is believed dormant (`−log₂ P(active) = 12 + 6/16 + ε`); 64 cells after
      its return it is active again (`−log₂ P(dormant) = 13 + 15/16 + ε`). The static gratings'
      death passes their mass (`0 + 13/16 + ε`) to the dormant family. The population codes
      `169 + 9/16 + ε`: `149 + 0/16 + ε` above the unswitched, `−5 + 0/16 + ε` against the unswitched
      plus 14 bits a switch, `20 + 4/16 + ε` above the unswitched plus `log₂ C(n − 1, 11)`; the
      dormant family is selected (`−log₂ w = 0 + 0/16 + ε`). Alone it codes `166 + 9/16 + ε` against
      its bound `176 + 1/16 + ε` (`log₂ 122³ − log₂ 2³` and the truth path's fixed-share code), with
      a certified drift of `1406097/2^62` bits. On the unswitched moiré the dormancy costs
      `0 + 1/16 + ε`.
    - Born: the dormant gratings are founded at cell 1280 (the section's residual `384 + 3/16 + ε`),
      charged 3 bits; the population codes `572 + 7/16 + ε`, having paid the trees' `404 + 12/16 + ε`
      before the birth.
    - Reseeding: the dead gratings' seed (8 keys, each ring's grating and mirror) is re-founded 11
      times at charges of 4 to 14 bits; five newborns live through an active aeon (born at 3072,
      5888, 8192, 11776 and 14592, each dying at the next silent cell), but by their birth the trees
      have re-read the returning pattern: `688 + 9/16 + ε`. Re-founding at a section pays only where
      the other families cannot re-read a returning face within the section.
  - **Parity color:**
    - Static: the gratings die at cell 1223, where class 1 arrived against their certain 0 (the
      joint factor exhausted). Their mass passes to the trees, `1 + 8/16 + ε` bits of it to `D = 8`
      and `1 + 9/16 + ε` to each of `D = 16, 32`. The population codes `252 + 9/16 + ε` (the recorded
      receipt), `238 + 7/16 + ε` above the unswitched `14 + 1/16 + ε`.
    - With dormancy: the drawn key is held through every silent aeon among 64032 joint survivors
      (`−log₂ mass = 9 + 4/16 + ε`: with a layer per ring the word's whole fibre survives). At a
      silent aeon's end each ring's dormancy reads `−log₂ P = 1 + 9/16 + ε`: the parity class cannot
      tell which ring sleeps, as it cannot tell the rates. 64 cells after the return every ring is
      active again (`−log₂ P(dormant) = 12 + 5/16 + ε`). The static gratings' death passes their
      mass (`0 + 13/16 + ε`) to the dormant family. The population codes `163 + 4/16 + ε`:
      `149 + 3/16 + ε` above the unswitched, `−5 + 3/16 + ε` against the unswitched plus 14 bits a
      switch, `20 + 7/16 + ε` above the unswitched plus `log₂ C(n − 1, 11)`; the dormant family is
      selected. Alone it codes `160 + 4/16 + ε` against its bound `171 + 6/16 + ε`
      (`#S_σ = 208 = 2⁴·13` joint keys along the truth's path), with a certified drift of
      `25654856001/2^60` bits. On the unswitched moiré the dormancy costs `0 + 1/16 + ε`. The
      population with dormancy reads the passage in 35 s on the host.
    - Born: founded at cell 1280 (the section's residual `72 + 9/16 + ε`), charged 3 bits; the
      population codes `231 + 5/16 + ε`.
    - Reseeding: the 720-key seed is re-founded 9 times (charges of 4 to 12 bits); five newborns live
      through active aeons, born at the sheets' cells; `252 + 12/16 + ε`.
- **The standing-cut regression** (`standing`; the trees alone, `D ∈ {1, …, 32}`, each named by 3
  bits, `M = 3/4`): the population selects `D = 4` (`−log₂ w = 0 + 0/16 + ε`) and codes
  `21747 + 8/16 + ε` over the 6,148 cells. On development (4,958 cells) it reads
  `18069 + 11/16 + ε` against the recorded `½` tree at `D = 4` (`tree_prequential`)
  `18067 + 2/16 + ε`, `2 + 9/16 + ε` above; held out (1,190 cells) it reads `3677 + 12/16 + ε`
  (`3 + 1/16 + ε` a cell) against the tree's `3677 + 12/16 + ε`, the campaign 1 receipt's exact
  face, `0 + 0/16 + ε` apart.

#### The curated source's own navigators, measured and retired (commit `38b0b81c`, reverted)

A tree per port (each channel's bytes on its own conversation span, the part's end coded as a
boundary) and a section navigator (a letter tree on the section epochs and a recency-rank tree for a
switch's target) were measured against the flat stream. Bits at `L_R = 16`, each `+ ε`:

| | per-port reader | typed reader (kept) |
|---|---|---|
| every byte vs flat, development | `+24904 + 14/16` | `−3080 + 13/16` |
| every byte vs flat, held out | `+10264 + 8/16` | `−844 + 13/16` |
| whole stream charged vs flat, development | `+30878 + 2/16` | `+2695 + 12/16` |
| whole stream charged vs flat, held out | `+10956 + 1/16` | `−161 + 4/16` |

What it located:
- **Separate trees lose the landmarks the ports share.** A reply and its request quote each other,
  and the human port's 65101 bytes are too few to learn from alone.
- **A shared tree still does not help.** One tree shared by all ports on the same
  per-conversation spans codes its bytes `−2168 + 12/16` below flat, still above the typed reader,
  which also reads the tail of the request a part answers.
- **The boundary is the cost.** The section cost splits into the boundaries (where a part ends:
  human `849 + 1/16` over 84 ends, agent `3139 + 4/16` over 1392), the letter kinds
  (`1839 + 12/16`, `1 + 3/16` a letter) and the switch targets (`139 + 0/16` over 335).

The typed reader stays. Campaign 5 needs a joint address across ports (the shared landmarks) and a
cheaper boundary: the part's end predicted by more than its bytes.

### Eggs composed at ports: the arithmetic eggs (rebuild step 4 item 6, September 27)

Record: [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md).

`hnn_population.rs`'s `composition` mode (`hnn_population_composition.rs`, its header states the
declarations) runs the composed eggs of `holonics::receiver::population::{composition,
arithmetic}` (Lean `Compression/Landmark/Context/Composition`) on the terrain notebook's arithmetic
terrains, drawn by the same seed. These are **development receipts, not milestones**. The mode
reads each terrain once, partitioned by cell class (`Population::receive_partitioned`), in about
57 seconds in all (products 7, 7 and 6 seconds; primes 15 and 22, the sieve at the counter's
unheld port counting every start a cell on the host's cores), its peak resident set under
`58400` kB.

```sh
cargo run --release -p holonics --example hnn_population -- composition [products | primes]
```

The population on each terrain: the receiving tree at the depth the terrain notebook's sweep chose
on the same cells (products `13`, `5`, `4`; primes `4`, `6`), and the composed egg, each named by
one bit (`M = 1`). Every class code of the tree inside the population reproduces the arithmetic
terrain's recorded class codes exactly (the table above), a cross-check of the partition's reading.

**Products** (`record clock ⊳ carry egg`: the clock of period 19 keyed by its offset, the carry egg
uniform on the operand phases, deterministic on the marks and, by the terrain's convolution and
carry, on the product's phases). In every base the clock locates its offset `0` (posterior `1`) in
the first record, and the composed egg codes **exactly** the truth: the operands' entropy plus the
clock's key, `2^12 · 8 log₂ b + log₂ 19`, its difference from the truth enclosed in
`[−1/2^95, 1/2^96]` bits. The population codes the truth plus one bit (its naming; the difference in
`[1 − 1/2^96, 1 + 1/2^96]`). Per class (each `+ ε`; the operands' truth `32768`, `108852 + 15/16`,
`131072`; every other class's truth zero):

| base | class | tree | composed egg | population | the clock's value here |
|---|---|---|---|---|---|
| 2 | operands | `33179 + 11/16` | `32769 + 7/16` | `32770 + 5/16` | `409 + 5/16` |
| 2 | marks | `1524 + 0/16` | `2 + 12/16` | `2 + 14/16` | `1521 + 2/16` |
| 2 | trailing, middle, leading | `1422 + 4/16`, `3966 + 1/16`, `1465 + 6/16` | `0 + 0/16` each | `0 + 0/16` each | the tree's |
| 10 | operands | `114394 + 15/16` | `108854 + 6/16` | `108855 + 3/16` | `5539 + 11/16` |
| 10 | marks | `41600 + 2/16` | `2 + 12/16` | `2 + 15/16` | `41597 + 2/16` |
| 10 | trailing, middle, leading | `26466 + 6/16`, `60508 + 10/16`, `30550 + 4/16` | `0 + 0/16` each | `0 + 0/16` each | the tree's |
| 16 | operands | `137510 + 1/16` | `131073 + 7/16` | `131073 + 11/16` | `6436 + 5/16` |
| 16 | marks | `41831 + 7/16` | `2 + 12/16` | `3 + 8/16` | `41827 + 15/16` |
| 16 | trailing, middle, leading | `32396 + 10/16`, `72206 + 12/16`, `36363 + 10/16` | `0 + 0/16` each | `0 + 0/16` each | the tree's |

The composed egg's location of the clock is paid in the first record, `1 + 7/16` on its operand
cells and `2 + 12/16` on its marks (together `log₂ 19 = 4 + 3/16 + ε`); after it every determined
cell's face is exactly one. The determined cells together (`45056 = 2^12·11`) cost the composed egg
`2 + 12/16 + ε` against the tree's `8377 + 13/16`, `159125 + 8/16` and `182798 + 9/16` (a cell
`0 + 2/16`, `3 + 8/16`, `4 + 0/16`). In all the tree reads `41557 + 8/16`, `273520 + 7/16` and
`320308 + 10/16`, the population `32773 + 3/16`, `108858 + 3/16` and `131077 + 3/16`. **The record
clock's value**, the joint code without it against with it (without the clock neither the carry
egg nor anything else here has a port, so the population without it is the tree alone), is
`8784 + 4/16`, `164662 + 4/16` and `189231 + 6/16` bits, beside its own description of
`log₂ 19 = 4 + 3/16 + ε` bits and one naming bit.

**Prime streams** over `[0, 10^4)` (`record clock ⊳ (counter ⊳ sieve)`: the clock of period
`L + 1`, the counter's start survivor filtered under each clock key, the sieve reading the
counter's port). The truth of every cell is zero and the keys' description is
`log₂ (L + 1) + L log₂ b`: `log₂ 5 + 4 log₂ 10 = 15 + 9/16 + ε` in base 10,
`log₂ 7 + 6 log₂ 6 = 18 + 5/16 + ε` in base 6. The composed egg locates the clock's offset `0` and
the counter's start `0` among `10^4 = 2^4·5^4` and `46656 = 2^6·3^6` starts, and codes **exactly**
the keys' description (the difference in `[−1/2^95, 1/2^96]`): `15 + 9/16 + ε` on the digit cells
and `0 + 0/16 + ε` on the primality cells in base 10 (`18 + 5/16` and `0 + 0/16` in base 6),
against the tree's `146345 + 2/16` and `15435 + 1/16` (`145167 + 12/16` and `19550 + 13/16`). The
population codes `16 + 9/16 + ε` and `19 + 5/16 + ε` (its one naming bit above); the clock's value
reads `161763 + 10/16` and `164699 + 5/16`.

**The counter's value** (the sieve's keystone), against the sieve at the counter's unheld port
under the located clock (`Composed::primes_unheld_counter`: each tick the sieve meets the counter's
uniform prior pushed through the port, never filtered): the unheld reading codes the digit cells
at `132879 + 7/16` (`log₂ 10` a digit, `3 + 5/16` a cell) and the primality cells at
`5376 + 6/16`, the window's density code exactly (the counter's range is the window); in base 6,
`155100 + 8/16` and `5404 + 11/16`, `28 + 4/16` above the window's density code because the
counter's range `6^6` holds a sparser density than `[0, 10^4)`. The counter's value is
`138240 + 3/16` and `160486 + 14/16` bits, beside its key's `log₂ 10^4` and `log₂ 6^6`.

**The sieve's work** over the window, the face that decided each integer (the cheap faces first):
in base 10 the last digit `5999` (2: `4999`, 5: `1000 = 2^3·5^3`), the digit sum (3) `1334`, the
alternating sum (11) `242 = 2·11^2`, the 21 gratings `7..=97` `1219 = 23·53`, below two `2`, and
the gaps of every grating `1204 = 2^2·7·43` (the primes past 97; the 25 primes up to 97 are decided
by their own face); in base 6 the last digit `6666` (2: `4999`, 3: `1667`), the digit sum (5)
`667 = 23·29`, the alternating sum (7) `381 = 3·127`, the 43 gratings `11..=211` `1102 = 2·19·29`,
the gaps `1182 = 2·3·197`.

### The evolved prior and species collapse (rebuild step 4 item 7, September 27)

Record: [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md).

`hnn_population.rs`'s `evolution` and `species` modes (`hnn_population_evolution.rs`, its header
states the declarations) run `holonics::receiver::population::{evolution, species}` (Lean
`Compression/Landmark/Context/Evolution`). These are **development receipts, not milestones**.
`evolution` reads its twelve aeons in `3922` ms and `species` its three terrains in under two
seconds (exterior wall).

```sh
cargo run --release -p holonics --example hnn_population -- evolution
cargo run --release -p holonics --example hnn_population -- species
```

**The evolved prior across aeons.** Twelve declared aeons, three cycles of four terrains, each drawn
by the seed plus the aeon's index: a moiré's parity color (`k = 3`, `q ≤ 2^3`, `2^12` cells), a tree
source (depth 2 over bits, `2^12` cells), products in base 2 (`L = 4`, `k = 2`, `2^8` records of 19
cells) and a prime stream in base 10 (`L = 3` over `[100c, 1000)` in cycle `c`). Each aeon declares
the tree at every depth of the ladder and the catalogue's key family for its alphabet (the parity
gratings on both binary terrains, `clock ⊳ carry`, `clock ⊳ (counter ⊳ sieve)`): seven families of
3 bits, the static prior `1/7` at `M = 7/8`. The evolved population declares the same families at
`M π(f)`, `π(f) = ½ D(f) + ½ · 1/7`, from the counts retained so far; the counts are the only
history kept. After the twelfth aeon they read, as (declared, selected, died): the gratings
`(6, 3, 3)`, the tree at `D = 2` `(12, 3, 0)`, `clock ⊳ carry` `(3, 3, 0)`,
`clock ⊳ (counter ⊳ sieve)` `(3, 3, 0)`, the other five trees `(12, 0, 0)`.

| aeon | terrain | selected (its evolved prior) | static | evolved | evolved − static |
|---|---|---|---|---|---|
| 0 | moiré `5/7 @ 0/7, 3/8 @ 6/8, 7/8 @ 6/8` | gratings (`1/7`) | `14 + 1/16` | `14 + 1/16` | within `2^(−96)` |
| 1 | tree source | tree `D = 2` (`8/63`) | `2847 + 14/16` | `2848 + 1/16` | `0 + 2/16` |
| 2 | products | `clock ⊳ carry` (`8/63`) | `2055 + 0/16` | `2055 + 3/16` | `0 + 2/16` |
| 3 | primes `[0, 1000)` | `clock ⊳ (counter ⊳ sieve)` (`8/63`) | `14 + 12/16` | `14 + 15/16` | `0 + 2/16` |
| 4 | moiré `5/6 @ 2/6, 4/5 @ 3/5, 1/3 @ 2/3` | gratings (`72/371`) | `15 + 8/16` | `15 + 1/16` | `−1 + 8/16` |
| 5 | tree source | tree `D = 2` (`118/623`) | `3277 + 5/16` | `3277 + 0/16` | `−1 + 11/16` |
| 6 | products | `clock ⊳ carry` (`17/91`) | `2055 + 0/16` | `2054 + 10/16` | `−1 + 9/16` |
| 7 | primes `[100, 1000)` | the prime egg (`17/91`) | `14 + 12/16` | `14 + 6/16` | `−1 + 9/16` |
| 8 | moiré `5/8 @ 3/8, 3/7 @ 5/7, 6/7 @ 6/7` | gratings (`209/917`) | `16 + 6/16` | `15 + 12/16` | `−1 + 5/16` |
| 9 | tree source | tree `D = 2` (`284/1281`; the static population selects none) | `2916 + 9/16` | `2916 + 7/16` | `−1 + 13/16` |
| 10 | products | `clock ⊳ carry` (`26/119`) | `2055 + 0/16` | `2054 + 7/16` | `−1 + 6/16` |
| 11 | primes `[200, 1000)` | the prime egg (`26/119`) | `14 + 12/16` | `14 + 2/16` | `−1 + 6/16` |

Each reading is `+ ε`. By cycle the evolved population codes `0 + 8/16`, `−2 + 8/16` and
`−3 + 14/16` against the static one, and over the twelve aeons `15294 + 6/16` against
`15297 + 6/16`, `−4 + 15/16` (exact `[−60206255015575805798155076523/2^94,
−60206255015575805798155076517/2^94]`). In every aeon its code lies within the bound: the selected
family's code plus `−log₂` of its evolved prior. What it located:
- **The evolved prior moves only the naming.** At `λ = ½` a family's prior lies in
  `[1/14, 4/7]` against the static `1/7`: it saves at most 2 bits an aeon and costs at most one.
  The first cycle meets each kind before its count exists, at a Dirichlet face thinned by the
  others' selections (`8/63 < 1/7`), and pays `0 + 2/16` an aeon; once a kind has been selected the
  later aeons of that kind cost less, reading `−1 + 5/16` to `−1 + 13/16` against the static
  population in the third cycle. The mixture's code moves by less than the selected family's prior
  where other families keep mass (the tree source's deeper trees).
- **A family that keeps winning is founded sooner; one that keeps dying later.** The key family's
  founding charge `−log₂ m_f` falls from 3 bits as its selections accumulate: the arithmetic eggs'
  to `2 + 6/16 + ε` by the third cycle (two selections each), the gratings' to `2 + 1/16 + ε` at
  aeon 9 (three selections). The gratings die on every tree source, and their deaths thin their
  pseudo-count to `σ = 7/22` at aeon 9's opening: their prior reads `347/1281`, where the KT
  pseudo-count `½` would give `33/119`.

**The work each family spent** (the cost receipt's counts, beside description and code): the
parity gratings read `6574260` emissions on the first moiré (every one of the `1815848` keys at the
first cell, the survivors after); the tree at `D = 2` deposited `4096` cells and holds `9` nodes;
`clock ⊳ carry` weighed `4924` keystone keys and formed `256` digit products; the prime egg read
`8317` counter emissions and weighed `4006` keystone keys on `[0, 1000)`, and its sieve's window
was decided once, `1000 = 2^3·5^3` integers: `2` below two, the last digit `599` (2: `499`,
5: `100`), the digit sum (3) `134`, the alternating sum (11) `24`, the gratings `7..=31` `84`
(`35, 17, 11, 9, 7, 3, 2`), and `157` gaps, the primes past `31`. No family here is pumped against
dissipation, so none reports pump work.

**Species collapse relative to the admitted future.** Each terrain is read whole by its population
(the `moire` and `crib` modes'), then its key family is collapsed over the whole future:
- **The parity moiré** (`k = 3`, `q ≤ 2^3`, `2^14` cells): its `720 = 2^4·3^2·5` survivors are one
  species at posterior 1 (the representative `1/7 @ 5/7, 1/7 @ 3/7, 1/2 @ 1/2`). The population
  codes `14 + 1/16 + ε` before and after; its face, the family's posterior and its own code are
  unchanged.
- **Relative to a growing admitted future**, at cell 9 where `3816 = 2^3·3^2·53` parity keys
  survive: over the next 1, 2, 4 and 8 ticks they form 2, 4, 14 and 27 species, and 27 from 8 ticks
  on and over the whole future. A species of a short future splits when the future grows; the word
  a surviving key emits is fixed 8 ticks ahead.
- **The sheet tuple** (`k = 3`, `q ≤ 2^4`, `2^14` cells): each ring's grating and its mirror are one
  species, `2·2·2` members to 1: `1/15 @ 2/15 ~ 14/15 @ 5/15`, `4/15 @ 10/15 ~ 11/15 @ 12/15` and
  `5/16 @ 11/16 ~ 11/16 @ 12/16`. The population codes `29 + 0/16 + ε` before and after.
- **The rotor crib** (`2^10` cells): its 7 survivors, the ring's rotor-gauge orbit, are one species:
  their transition tables agree at every stage of the rotor's period. The population codes
  `17 + 14/16 + ε` before and after.

### The curated source through the population (campaign 5, September 27)

Record: [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md).

`hnn_population.rs`'s `curated` mode (`hnn_population_curated.rs`, its header states the
declarations) reads the curated cut through `holonics::receiver::population` (the typed tree
`TreeFamily::sectioned` over `compression::landmark::context::sections`, and `boundary`: the part
clock, the hazard law and the boundary egg; Lean `Composition.{stagedFace_nonneg,
stagedFace_sum_one, staged_chain_rule, staged_code}`). These are **development receipts, not
milestones**; the script and the reader print counts and bits only. One passage over the whole cut:
the population `341975` ms (its development cells `302233` ms), the flat tree `23885` ms, the peak
resident set `11617918976` bytes.

```sh
cargo run --release -p holonics --example hnn_population -- curated .local/cuts/curated-cut.bin .local/cuts/curated-flat-cut.bin
```

The population: eight families of 3 bits (`M = 1`), each the `½` stop prior and the KT node at
`n* = 2^20`, `L_R = 16`: the curated cell tree at `D = 6, 12, 24, 48, 69`, the typed tree (the
channel slot) at `D = 6, 12`, and the boundary egg on the typed tree at its deepest, `D = 22`, with
the letter tree at `D_L = 12`. Its byte tree read alone is the egg's unheld port. The development
sweep (a scratch probe on the development cells alone) chose the egg's byte tree among 3, its hazard
among 45 laws and its letter tree among 11, charged `2 + 6 + 4 = 12` bits; the flat tree is charged
its recorded sweep, 3 bits. Bits at `L_R = 16`, each `+ ε`, exact enclosures in the output.

The sweep, development cells only:
- **The byte tree.** The channel slot alone reads deeper than the typed reader's `[channel, kind]`:
  at `D = 21` the whole curated stream `1802554 + 5/16` against `1803437 + 13/16` at `D = 16`; its
  bytes within the bytes (below the root digit) human `145767 + 6/16`, agent `1647583 + 14/16`,
  against `146171 + 14/16` and `1648474 + 13/16`, and the cell tree at `D = 48`'s `147084 + 1/16` and
  `1648455 + 4/16`.
- **The boundary is the byte tree's root digit.** On the chart `256 + 12` the odometer's first digit
  splits the bytes from the letters, and costs `6638 + 1/16` (`[channel, kind]`), `6562 + 0/16`
  (channel) and `6637 + 1/16` (cell tree). 1426 of the 1477 letters follow a `.` (1439 a sentence
  close), 37 another byte, and one opens the cut.
- **The hazard.** A KT face per `(channel, position class, last byte's class)` reads `5517 + 14/16`;
  the declared partition (after a sentence close: channel, kind, the phase's and the carry's dyadic
  classes; otherwise: channel and the last byte's class) `4624 + 8/16`; the receiving tree over the
  port's letters `4531 + 13/16`, and each cell's two-face mixture with the tree's root at least
  `4473 + 14/16` (neither declared).
- **The letters.** The letter tree on the section epochs `1839 + 12/16` at `D_L = 12` (the retired
  section navigator's), typed by the part each letter closed (its length's base-8 digits and its last
  byte's class) `1815 + 0/16`.

[established-bounded; measured] **The passage.**

| | development (915,723 bytes, 1,477 letters) | held out (130,878 bytes, 150 letters) |
|---|---|---|
| human bytes, population against flat | `145988 + 3/16` against `147346 + 0/16`: `−1358 + 2/16` | `76011 + 1/16` against `76584 + 8/16`: `−574 + 8/16` |
| agent bytes, population against flat | `1649328 + 1/16` against `1653396 + 1/16`: `−4068 + 0/16` | `181231 + 2/16` against `181648 + 14/16`: `−418 + 3/16` |
| every byte against flat (typed reader) | `−5426 + 3/16` (`−3080 + 13/16`) | `−992 + 12/16` (`−844 + 13/16`) |
| section letters (typed reader) | `4467 + 6/16`, `3 + 0/16` a letter (`5774 + 15/16`) | `567 + 7/16`, `3 + 12/16` a letter (`682 + 7/16`) |
| **whole curated stream charged against the flat stream** (typed reader) | **`−950 + 9/16`** (`+2695 + 12/16`) | **`−415 + 3/16`** (`−161 + 4/16`) |
| the boundary egg; its byte tree alone | `1799780 + 11/16`; `1802545 + 4/16` | `257809 + 11/16`; `258165 + 14/16` |
| posterior: the egg; the next (typed tree `D = 12`) | `0 + 0/16`; `3041 + 2/16` | `0 + 0/16`; `3446 + 14/16` (after every cell) |
| human hazard: at the closes; on the bytes (the tree's root, together) | 84 closes `413 + 6/16` (retired per-port reader `849 + 1/16`); `220 + 12/16` (`609 + 15/16` against `634 + 2/16`) | 22 closes `126 + 1/16`; `71 + 0/16` (`198 + 4/16` against `197 + 2/16`) |
| agent hazard: at the closes; on the bytes (the tree's root, together) | 1392 closes `2237 + 5/16` (retired `3139 + 4/16`); `1751 + 15/16` (`5951 + 1/16` against `3989 + 5/16`) | 128 closes `269 + 11/16`; `169 + 12/16` (`576 + 14/16` against `439 + 8/16`) |
| letters: the letter tree; the byte tree's own | `1815 + 0/16`; `2642 + 0/16` (retired navigator `1839 + 12/16`) | `171 + 9/16`; `389 + 4/16` |
| the part clock's value (boundary; letters) | `2764 + 8/16` (`1937 + 8/16`; `827 + 0/16`) | `356 + 3/16` (`138 + 8/16`; `217 + 10/16`) |

The flat tree reproduces its recorded codes exactly. The other families: the cell tree at
`D = 48` and `69` `1804816 + 6/16` on development, `258668 + 1/16` held out; the typed tree at
`D = 12` `1802821 + 13/16` and `258215 + 7/16`.

What it located:
- **The whole curated stream codes below the flat stream of the same bytes, on development and
  held out**, its sections paid: the curated structure now pays for itself.
- **The boundary is paid where the agent's part ends.** The hazard at the agent's closes costs
  `1 + 9/16` a close against the retired reader's `2 + 4/16`, and the agent's whole indicator falls
  from the byte tree's `5951 + 1/16` to `3989 + 5/16`. On the human port the part clock is no
  better than the byte tree's own root (agent-inferred: its 84 ends are too few for the partition's
  cells to learn).
- **The letters are read from the part they close.** The letter tree codes a letter in `1 + 3/16`
  bits against the byte tree's own `1 + 12/16`.
- **The channel slot alone is the better byte reader**: read once at the section, it lets the typed
  tree reach `D = 22`, where the `[channel, kind]` tree stops at `16`. Alone, though, it reads the
  held-out cells `93 + 2/16` (at the grain) above the `[channel, kind]` reader (`258165 + 14/16` against
  `258072 + 12/16`); the egg's sections carry it below.

### The admitted receivers (campaign 5, September 27)

Record: [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md).

The source contract's item 7 consumed ([HNN_FORMULA](../../../docs/HNN_FORMULA.md#the-source-and-release-contract);
`holonics::receiver::population::admitted`, `holonics::compression::landmark::context::spans`; Lean
`Composition.{stagedFace_nonneg, stagedFace_sum_one}` at each tick's stage map and
`{staged_chain_rule, staged_code}` at `σ = id`; #73, #148). `curated_incidence.py` (stdlib only,
run once, writing only into `.local/cuts/`, each file mode 0600, printing counts and hashes only)
places the curated source's relations on the pinned cut: a relation is declared when its reading
part and its target both open a part in the cut. The `curated` mode's population now holds the
admitted egg in the boundary egg's place (its inner egg, reported from its own receipt). These are
development receipts; the script and the reader print counts and bits only. One passage over the
whole cut: the population `302669` ms (its development cells `261545` ms), the flat tree `23296`
ms, the peak resident set `10491265024` bytes.

```sh
HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/curated_incidence.py
cargo run --release -p holonics --example hnn_population -- curated .local/cuts/curated-cut.bin .local/cuts/curated-flat-cut.bin
```

**The declared relations** (892): requests 678 development and 117 held out; later human returns 77
and 20. Not declared: requests whose target no development occurrence holds 711 and 11, whose
target has no cells 3, none declared 1; later human returns before the cut 1, none declared 6 and 2.

**The laws.** A response is located on its request's span (the longest suffix of the part that
recurs in the span, and the span's byte after it). At a located length of at least 4 the copy stage
factors the boundary egg's face: a KT face of whether the located byte comes next, per cell of the
length's dyadic class above 4 (4 classes) and the boundary egg's own odds of the located byte
(`⌊log₂(q/(1 − q))⌋`, 8 classes a side), the miss stage the boundary egg's face renormalized off the
located byte. The later human part is read against the response it follows under the same law, as
a receipt only: its faces never enter the family's. The request's pointer is coded at each agent
letter and charged to the curated stream: held or not (a KT face per section kind and the previous
agent part's held state), the same request as the previous agent part's or not (per section kind),
else its rank among the human parts received (its dyadic class in unary, its offset uniform).

**The development probe** (`admitted_probe`, a scratch command on the development cells alone, the
boundary egg under the request's stage, `123460` ms, resident `3087818752` bytes), each law's staged
code against the boundary egg's on its own ticks, bits at `L_R = 16`, each `+ ε`:

| least, length classes, odds classes a side | agent ticks read | copies | staged − boundary egg |
|---|---|---|---|
| 1, 6, 8 | 382,505 | 94,435 | `−1555 + 0/16` |
| **4, 4, 8** (chosen) | 66,346 | 33,174 | `−1863 + 5/16` |
| 8, 3, 8 | 9,122 | 5,987 | `−1120 + 11/16` |
| 4, 4, 0 | 66,346 | 33,174 | `+30772 + 15/16` |
| 1, 6, 0 | 382,505 | 94,435 | `+156406 + 8/16` |
| 2, 5, 8 | 258,285 | 77,886 | `−1669 + 7/16` |
| 16, 2, 8 | 952 | 804 | `−366 + 10/16` |
| 4, 4, 4 | 66,346 | 33,174 | `−1561 + 0/16` |

The pointer's code among 3 (development, the request's, each `+ ε`): held per section kind
`2116 + 2/16`; per section kind and the previous agent part's held state `1374 + 0/16`; with the
same request as the previous agent part's `1109 + 1/16` (chosen; the latter two read by an exact
scratch product of the same faces, the chosen one reproduced by the passage). Charged:
`⌈log₂ 8⌉ + ⌈log₂ 3⌉ = 5` bits beside the boundary egg's 12, so 17.

[established-bounded; measured] **The passage.**

| | development (915,723 bytes, 1,477 letters) | held out (130,878 bytes, 150 letters) |
|---|---|---|
| agent bytes, population against flat, with the admitted receivers | `1647460 + 7/16` against `1653396 + 1/16`: `−5936 + 6/16` | `180898 + 11/16` against `181648 + 14/16`: `−751 + 12/16` |
| agent bytes, population against flat, without (commit `40ab94cf`) | `−4068 + 0/16` | `−418 + 3/16` |
| the request receiver on its agent bytes, against the boundary egg | 66,333 bytes, 33,174 copies: `−1868 + 6/16` | 20,974 bytes, 10,262 copies: `−333 + 9/16` |
| at its closes | 13: `+4 + 15/16` | 5: `+0 + 11/16` |
| the request's pointer (agent letters, held) | 1,393, 678: `1109 + 1/16` | 128, 117: `159 + 1/16` |
| **the receiver's value, its pointer paid** | **`−754 + 6/16`** | **`−173 + 6/16`** |
| every byte against flat | `−7294 + 9/16` | `−1324 + 5/16` |
| **whole curated stream charged against the flat stream** (before) | **`−1699 + 15/16`** (`−950 + 9/16`) | **`−583 + 10/16`** (`−415 + 3/16`) |
| the later human return, conditioned on the response against unconditioned (receipt) | 19,053 bytes, 9,111 copies: `−470 + 12/16`; 10 closes `+0 + 9/16` | 12,391 bytes, 6,080 copies: `−457 + 11/16`; 2 closes `+0 + 5/16` |
| the later human's pointer (human letters, held; receipt) | 84, 77: `213 + 6/16` | 22, 20: `38 + 4/16` |
| retention: cells held at once, at most | 31,239 | 35,323 |

The human bytes and the other families read exactly as before (the receipt never enters the face):
human bytes `145988 + 3/16` and `76011 + 1/16`, the boundary egg `1799780 + 11/16` and
`257809 + 11/16`. The admitted egg is selected at posterior `0 + 0/16` after both populations.

What it located:
- **A response is read against its request, and it pays for its pointer.** On the agent bytes it
  reads, the request's port lowers the code by `1868 + 6/16` over 66,333 bytes on development and
  `333 + 9/16` over 20,974 held out (under `1/16` a byte each); its pointer paid, `−754 + 6/16` and
  `−173 + 6/16` remain. The copy stage must weigh the inner egg's own odds: without the odds classes
  every law codes far above the boundary egg (the tree already predicts most quoted bytes).
- **A later human return is predicted by what it answers**, as an observation: `−457 + 11/16` over
  12,391 held-out human bytes read against the response they follow, never trained into the
  response's reading.
- **Most requests are not held**: 711 of 1,393 development agent parts reach a request no
  development occurrence holds, so their port stays unheld.

### Merges: learned byte classes and shared counts (campaign 5, September 27)

Record: [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md).

`hnn_population.rs curated` now learns the boundary egg's hazard partition by merges before the
passage (`holonics::receiver::population::merge`; Lean `Compression/Landmark/Context/Merge`),
decided on the development cells only, and reads the declared partition and the refused stage on
the same cells as comparison hazards (they enter no face). `merges` runs the learning alone
(`1154` ms, the part clock only). The readings below were measured with the boundary egg in the
population (built beside the admitted receivers, before the two were joined; the joined passage is
the last subsection). One passage over the whole cut: the population `299549` ms (its development
cells `262472` ms), the flat tree `23149` ms, `324569` ms in all, the peak resident set
`11288145920` bytes.

```sh
cargo run --release -p holonics --example hnn_population -- curated .local/cuts/curated-cut.bin .local/cuts/curated-flat-cut.bin [merges]
```

**The law** (`merge`'s header). A priced merge of count cells is accepted exactly when it lowers
the complete code, `P(G)·W_G(z) < P(G′)·W_(G′)(z′)` (`merge_cost_mass_iff`), with `W` the blocks'
KT masses and `P` the restaurant mass at `α = ½` (a merge of blocks of `a` and `b` values multiplies
it by `2·(a + b − 1)!/((a − 1)!(b − 1)!)`, `restaurant_merge_ratio`), decided by integer product
bounds. The pair of largest gain is merged first; a stage is adopted only when its complete code
(its development code plus its description) falls below the stage before it, the declared classes
being the sweep's law. The hazard's 47 laws (45 probed and the two stages) keep the sweep's charge at
12 bits, and the adopted description is charged beside it.

[established-bounded; measured] **The learning, on the 917,199 deposits of the development cells**
(424 fine cells; the declared partition's 175 cells code `4623 + 8/16`):

| stage | cells before → after | merges accepted (undecided) | development code; description | adopted |
|---|---|---|---|---|
| 1. last-byte classes (167 values met of 257, the channels as lanes) | 167 values → 4 classes (of 1, 2, 2 and 252 values; the declared 6) | 163 (0) | `4458 + 3/16`; `43 + 10/16` | yes: the complete code against the declared, `−122 + 6/16` (in-sample) |
| 2. shared counts (a port's cell merged into another's at one rest) | 172 → 131 cells | 41 (0) | `4417 + 4/16`; `41 + 6/16` | no: `7/16` above stage 1 |

The frozen standing's release reading: the 172 learned cells read 105 distinct faces (merging them
would change no face at the end of development; a deposit separates them).

[established-bounded; measured] **The passage** (the learned partition in the egg; bits at
`L_R = 16`, each `+ ε`):

| | development (915,723 bytes, 1,477 letters) | held out (130,878 bytes, 150 letters) |
|---|---|---|
| **whole curated stream charged against the flat stream** (declared, commit `40ab94cf`) | **`−1072 + 15/16`** (`−950 + 9/16`), charged `55 + 10/16` | **`−369 + 8/16`** (`−415 + 3/16`), charged `55 + 10/16` |
| the boundary egg (declared) | `1799615 + 7/16` (`1799780 + 11/16`) | `257812 + 6/16` (`257809 + 11/16`) |
| the hazard, learned against declared on the same cells | `−166 + 11/16` | `+2 + 10/16` |
| human hazard: at the closes; together (declared) | 84 closes `367 + 7/16`; `575 + 5/16` (`413 + 6/16`; `634 + 2/16`) | 22 closes `113 + 6/16`; `192 + 15/16` (`126 + 1/16`; `197 + 2/16`) |
| agent hazard: at the closes; together (declared) | 1392 closes `2139 + 8/16`; `3882 + 14/16` (`2237 + 5/16`; `3989 + 5/16`) | 128 closes `277 + 9/16`; `446 + 5/16` (`269 + 11/16`; `439 + 8/16`) |
| the refused shares: human at the closes; together; the whole hazard, the learned classes against the shares | `360 + 14/16`; `545 + 11/16`; `40 + 15/16` | `119 + 0/16`; `208 + 9/16`; `−16 + 10/16` |
| cells met: declared; learned; with the shares | 175; 172; 131 | 187; 184; 143 |
| the part clock's value (boundary; letters) | `2929 + 13/16` (`2102 + 12/16`; `827 + 0/16`) | `353 + 8/16` (`135 + 13/16`; `217 + 10/16`) |

The declared comparison reproduces the first step's hazard rows exactly (`413 + 6/16` over 84
human closes, `2237 + 5/16` over 1392 agent closes, `126 + 1/16` and `269 + 11/16` held out), and
the byte tree alone and the letter tree are unchanged (`1802545 + 4/16`, `1815 + 0/16`).

Differences are read on the grain as printed, `n + k/16 + ε` with `n` the floor (so `−5 + 13/16`
is `−(4 + 3/16) + ε`). What it located:
- **The learned classes compress the development cells and do not carry to the held-out cells.**
  With their description paid, the curated stream against the flat stream moves from `−950 + 9/16`
  to `−1072 + 15/16` on development, and the hazard they learn reads `2 + 10/16` above the declared
  one held out (the human's `−5 + 13/16`, the agent's `6 + 13/16`), so with the charge the held-out
  stream moves from `−415 + 3/16` to `−369 + 8/16` against the flat stream. The development gain is a
  valid code of the development cells (the partition is transmitted first); the classes it found (a
  class of one value and two of two, beside the rest) are ends the held-out tail does not repeat.
- **The human port's cells merged into the agent's lower the human's hazard at the closes and raise
  it on the bytes**: at the closes `360 + 14/16` against the declared `413 + 6/16` over 84 on
  development and `119 + 0/16` against `126 + 1/16` over 22 held out, but the human's whole hazard
  held out is `208 + 9/16` against the learned classes' `192 + 15/16`. The stage's 41 merges save
  `40 + 15/16` on development, `7/16` less than their description, and the refusal holds held out:
  the learned classes alone read the held-out hazard `−16 + 10/16` against the shares.
- **The merge criterion is the complete code and nothing else**: 204 merges accepted, none
  undecided, and each stage's adoption decided by exact enclosures. Held-out transfer is not part of
  it; a stage that transfers needs more development ends or an admitted future that prices the
  transfer.

#### The admitted receivers with the learned classes (September 27)

The two joined: the admitted egg's inner boundary egg reads the learned hazard partition (the
declared partition and the refused shares its comparison hazards), and the curated stream is
charged the sweep's 17 bits (the hazard among 47) and the learned partition's description
`43 + 10/16`, `60 + 10/16` in all, beside the request's pointer. The learned partition changes the
inner egg's face, so the copy stage's odds classes and its miss stage move with it and a comparison
hazard prices the hazard alone. Development therefore chooses the partition in the admitted egg by
the whole curated stream on the development cells against the admitted egg with the declared
partition on the same cells (commit `9ad357fc`'s reading, its grain cell's exact enclosure,
`RECORDED_WHOLE`); the held-out cells are read once and choose nothing. One passage over the whole
cut (the command above, no mode): the merges `1147` ms, the population `274898` ms (its
development cells `237229` ms), the flat tree `24216` ms, `300625` ms in all, the peak resident set
`14326317056` bytes.

[established-bounded; measured] **The passage** (bits at `L_R = 16`, each `+ ε`):

| whole curated stream charged against the flat stream | development | held out |
|---|---|---|
| **the admitted receivers with the learned classes** (this passage) | **`−1820 + 9/16`** | **`−535 + 8/16`** |
| the admitted receivers with the declared classes (commit `9ad357fc`) | `−1699 + 15/16` | `−583 + 10/16` |
| the learned classes without the receivers (the merges' passage above) | `−1072 + 15/16` | `−369 + 8/16` |
| the declared classes without the receivers (commit `40ab94cf`) | `−950 + 9/16` | `−415 + 3/16` |

| | development | held out |
|---|---|---|
| human bytes, population against flat (with the declared classes) | `−1371 + 4/16` (`−1358 + 2/16`) | `−565 + 0/16` (`−574 + 8/16`) |
| agent bytes, population against flat (with the declared classes) | `−5944 + 10/16` (`−5936 + 6/16`) | `−750 + 5/16` (`−751 + 12/16`) |
| every byte against flat (with the declared classes) | `−7315 + 15/16` (`−7294 + 9/16`) | `−1315 + 6/16` (`−1324 + 5/16`) |
| the request receiver on its agent bytes against the boundary egg | 66,333 bytes: `−1868 + 9/16` (`−1868 + 6/16`) | 20,974 bytes: `−331 + 2/16` (`−333 + 9/16`) |
| the receiver's value, its pointer paid (`1109 + 1/16`, `159 + 1/16`) | `−754 + 9/16` (`−754 + 6/16`) | `−172 + 15/16` (`−173 + 6/16`) |
| the later human return against unconditioned (receipt) | `−470 + 10/16` (`−470 + 12/16`) | `−456 + 1/16` (`−457 + 11/16`) |
| the boundary egg; its hazard, learned against declared on the same cells | `1799615 + 7/16`; `−166 + 11/16` | `257812 + 6/16`; `+2 + 10/16` |
| the admitted egg (selected at posterior `0 + 0/16`) | `1797752 + 15/16` | `257482 + 4/16` |

The inner boundary egg reads exactly as in the merges' passage (the egg, the hazard stages, the
comparisons and the part clock's value `2929 + 13/16` and `353 + 8/16`), and the learning
reproduces its receipt (4 classes adopted, the shares refused). What it located:
- **Development adopts the learned classes in the admitted egg**: the whole stream `−1820 + 9/16`
  lies below the declared classes' `−1699 + 15/16`, a difference at the grain of `−122 + 10/16`
  against the classes' `−122 + 6/16` without the receivers. The two receivers compose: the request
  receiver's value moves by `3/16` at the grain and the classes' gain by `4/16`.
- **Held out, read once and choosing nothing, the learned classes cost what they cost alone**: the
  whole stream `−535 + 8/16` lies above the declared classes' `−583 + 10/16`, a difference at the
  grain of `47 + 14/16` (without the receivers `46 + 5/16`): the description `43 + 10/16`, charged
  to the held-out stream as well, the learned hazard `2 + 10/16` above the declared on the held-out cells, and `1 + 10/16`
  more where the copy stage reads the moved inner odds. The joined egg still codes the held-out
  stream below the flat stream and below both receiver-free eggs.

### F4 release and the disjoint development families (September 27)

Record: [F4](../../records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md).

The [F4 pin and receipt](../../records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md)
names the hash-seeded choosing/validation family split, each private cut's hash, the complete
release acceptance and the failure branch. `development_families.py` writes the owner-only
membership; `curated_source.py` and `curated_incidence.py` take a role; `family_passage.py` shifts the
validation cut's own incidence without inventing a relation across the split. The one held-out
passage is:

```sh
cargo run --release -p holonics --example hnn_population -- f4 .local/cuts/curated-f4-passage-cut.bin .local/cuts/curated-f4-passage-flat-cut.bin
```

It finished in 307,213 ms at a 10,330,435,584-byte peak resident set. The charged curated code
against the flat byte stream was `−1477 + 5/16 + ε` bits on choosing and `+1346 + 1/16 + ε` on
validation (`L_R = 16`, `0 ≤ ε < 1/16`). The validation result is above the control. The exact
next-face identity and planned request incidence are built, but the text decoder, producing
keys/provenance, grain/fibre and release square are not. F4 remains a predictor under its pinned
failure branch. `f4_retrospective.py` selected 32 development-validation requests and made a
request-aware retrieval control without reading those requests' recorded responses; the scoring
passage is separate and cannot be used as a prospective release standing. The evaluation partition
has not been read.

### F1 word alphabet pin (September 27)

Record: [F1](../../records/2026-09-27_F1_WORD_ALPHABET_GATE.md) (`hnn_word_probe`, retired September 28, last at commit `2d34b819`).

The independent [F1 pin and receipt](../../records/2026-09-27_F1_WORD_ALPHABET_GATE.md) fix the
word terrain, charged parse/termination law, byte-population baseline, one held-out passage,
resource gate and failure branch. Its private split has 17,957 choosing and 4,492 validation
families. A chosen 272-word dictionary (all singleton bytes and 16 learned pairs) costs 3,301
bits under the pinned declaration. Its exact receiver took 8,981 ms for 128 choosing bytes, so a
full passage projects far beyond ten minutes and was refused. The single bounded held-out part
has 113 bytes and its actual END; its prequential mass equalled the sum over its parses exactly in
6,910 ms. The sectioned 268-class adapter's small exact fixtures pass. No charged whole-stream
word-code win is claimed, and bytes remain the text chart.

### F2 field-family preflight (September 27)

Record: [F2](../../records/2026-09-27_F2_FIELD_FAMILY_GATE.md).

The [F2 pin](../../records/2026-09-27_F2_FIELD_FAMILY_GATE.md) fixes an independent
development-family split and both the full and bounded passage budgets. The full serial field
passage projects beyond ten minutes. The first bounded cut was below the field's `n* = 6,148`;
the corrected private byte cut at `n*` read 4,096 choosing and 2,052 held-out validation bytes
once in 363,330 ms on the host. `Reference::expose` provides aggregate code rather than the
per-cell rational face required by a population family. The field cannot be inserted or
validated by substituting its odometer covector for a probability. No F2 held-out
**field-family** reading has run, and the evaluation partition remains closed.

### F2 adoption gate on the receiving population (September 28)

Record: [THE_REBUILD F2](../../../docs/plans/THE_REBUILD.md#f2-the-field-as-a-family-step-4-73)
(the pins and the receipt).

```sh
cargo run --release -p holonics-cuda --example hnn_exposure -- cut-file .local/cuts/f2v2-gate-probe.bin cells all realization card gate f2
```

The run used a fresh split (`F2V2`, 18,068 choosing and 4,381 validation families) and the
6,148-cell probe at `n*` (4,096 choosing and 2,052 validation byte cells). It ran once on the
card, at the pins' commit `89bc9b8b`, and took 328,939 ms at a 502,538,240-byte peak.
- **Code.** On the validation cells, the receiver's population with the field codes
  `7450 + 1/16 + ε`. The population over the tree alone codes `7460 + 2/16 + ε`. The difference,
  `−11 + 15/16 + ε`, is strictly below zero.
- **Work.** The run takes `107 rem 21` ms a window; the tree alone takes 432 ms in all. The host's
  deposit is `54 rem 712` ms of each window.
- **Budgets.** The longest validation response projects to 1,009,824 ms, against a 60,000-ms
  budget. The declared validation passage projects to 27,989,242 ms, against 600,000 ms.
- **Verdict.** Not adopted. The field stays dormant for text.

### F5 development-only release and product protocol (September 27)

Record: [F5](../../records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md), [the atomic standing audit](../../records/2026-09-27_F5_ATOMIC_STANDING_OWNER_AUDIT.md).

The [F5 pin and receipt](../../records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md) fix a separate
hash-seeded development-family split, prospective-request order, context rule, blind rubric and
privacy. That split was used to refine the release route and is now a **diagnostic**, so an
untouched development split is still owed before F5 acceptance. The evaluation partition remains
closed. Private request and response text never enters the tracked tree or public readouts.

`hnn_population f5-native` follows the population's interval face only where an exact draw forces
one class across its fibre. `f5-family` samples one family from the enclosed posterior and follows
its exact face; `f5-family-verify` replays the resulting candidate on a fresh branch, capturing
the population's scored face before every byte and its stop. The first candidate had 179 UTF-8
bytes, the same private hash after full-path verification, 180 checked faces, and 15,826 ms full
warm time. The full request-only diagnostic bundle (`f5-bundle`) trained choosing standing once
and branched 32 times in 314,527 ms of preparation plus warm work: 24 provisional UTF-8 paths,
four invalid UTF-8 refusals, one over-aperture request and three no-stop paths. Longest warm
request: 20,760 ms. These are path and resource receipts, not answer-quality or product claims.

The exterior `athena_protocol.py` fixture uses one Ask/Inspect/Checkpoint vocabulary and one
atomic owner-only checkpoint with standing bytes, cursor, pending comparisons, incomplete input
tail and a replayable pending output. Fourteen fixture tests pass, including durable staging of a
complete frame until its native result commits; presenting the provisional native
path without health/provenance/fibre produces the typed `incomplete-release-receipt` refusal and
replays it with zero new native calls. `f5_context.py` recovers actual provider-parent context:
21 complete one-occurrence packets and 11 unresolved-parent refusals on the diagnostic requests.
`athena_blind.py` has a 32-case owner-only development package with source-hidden sides, no marks
or unblinding key; it has not been shown for judgment. Exact native standing codecs now cover
Landmarks, PassageCode, TreeFamily, BoundaryEgg, AdmittedEgg and a tagged Population on small
continuation fixtures. A choosing-only `f5-checkpoint-census` measured 6,256,005,521 bytes in
the eight family payloads and 6,256,005,986 bytes in the full population stream; the complete
stream took 13,266 ms with a 9,897,873,408-byte sampled RSS peak, without printing source
content. The choosing-only `f5-checkpoint-restore` durably wrote that stream and restored the
same cursor, face and next receive with a 16,287,236,096-byte sampled RSS peak; its manifest was
reconstructed from choosing source, so this is a decoder check. The file-backed v2 fixture
streams standing and protocol metadata into one owner-only atomic file. At this actual standing
size its synthetic typed-refusal `Ask` committed in 7,706 ms, replayed without a second Engine
call, and used 22,323,200 bytes peak RSS in Python. An independent cold restore, live atomic
protocol transition and full product health/provenance/fibre receipts are still owed.

### F0: the predictor on unseen families, the first diagnosis (September 28)

Record: [the forward plan stopped at transfer](../../records/2026-09-28_THE_FORWARD_PLAN_STOPPED_AT_TRANSFER_THE_POPULATION_MEMORIZES_FAMILIES_AND_ITS_STANDING_IS_AN_INDEX.md).

The [audit and diagnosis](../../records/2026-09-28_THE_FORWARD_PLAN_STOPPED_AT_TRANSFER_THE_POPULATION_MEMORIZES_FAMILIES_AND_ITS_STANDING_IS_AN_INDEX.md)
re-ran F4's development passage with the standing counted after the passage:

```sh
cargo run --release -p holonics --example hnn_population -- f4 .local/cuts/curated-f4-passage-cut.bin .local/cuts/curated-f4-passage-flat-cut.bin
```

It ran in 272,849 ms at a 10,843,217,920-byte peak resident set.
- **Bytes.** On the validation families the population's bytes code `−2430 + 8/16 + ε` below the flat
  tree (human `−415 + 1/16`, agent `−2015 + 7/16`). On the choosing families they coded
  `−4591 + 8/16 + ε`.
- **Structure.** The whole-stream `+1346 + 1/16 + ε` is the section letters (`3333 + 10/16 + ε`), the
  request pointer (`402 + 0/16 + ε`) and the charges, none of which the flat stream codes.
- **Standing.** 11,513,530,863 bytes for the population (10,983 a cell), against 1,358,603,467 for
  the flat tree (1,298 a cell).
- **Families.** The posterior sits on the admitted egg alone, and the cell trees beyond depth 24 add
  at most 20 bits.

`release_legibility.py` reads the diagnostic releases, their retrieval controls and the requests,
and prints counts only: paired delimiters, the backtick, straight-quote and bold parities, and the
word-shape rate against the choosing vocabulary. Of the native releases, 24 are texts and 8 are
typed refusals. 580 of their 758 word tokens are in the choosing vocabulary, against 3,139 of 3,306
in the controls and 1,817 of 1,932 in the requests. Backticks come out even in 14 of 24 releases,
against 32 of 32 controls.

**F0's first candidate, adopted: the admitted egg alone.** The command is
`hnn_population f0-egg <curated cut> <flat cut>` (the receipts below read its byte tree at the deepest
depth, 22 ticks, as the route did through commit `d31c8b37`; since U2's acceptance run it declares
the byte tree at 12 ticks). On the choosing families the posterior sat wholly
on the admitted egg, so the population drops the seven trees:
- validation bytes are unchanged, `−2430 + 8/16 + ε` against flat, and the choosing bytes read
  `−4593 + 5/16 + ε`, 2 bits better with no family names to pay;
- the standing is 2,781,355,912 bytes after 1,048,243 cells, 2,653 a cell, against 10,983 for all
  eight families and 1,298 for the flat tree;
- the passage takes 166,113 ms at a 3,400,306,688-byte peak resident set, against 272,849 ms at
  10,843,217,920 for all eight families.

### U2: the standing census of F0's egg (September 28)

Plan: [U2](../../../docs/plans/THE_REBUILD.md#u2-one-retention-contract-and-f0s-memory); the rules are
derived in `compression::landmark::context` ("Which merges and releases are future-sufficient").

```sh
cargo run --release -p holonics --example hnn_population -- f0-census .local/cuts/curated-f4-passage-cut.bin
```

Read-only; counts and bytes only (`hnn_population_census.rs`). The admitted egg alone, built by the
F0 route's constructor, reads F4's development passage; its byte tree (the typed tree at `D = 22`
ticks) is censused node by node after the choosing families and after the whole passage. The run
took 107,150 ms at an 8,656,285,696-byte peak, inside its projection (ten minutes, 20 GB).
- **The standing.** After 1,048,243 cells the egg's standing is 2,781,355,790 bytes (2,653 a cell,
  remainder 367,111; the population's recorded 2,781,355,912 adds its 122-byte header). Its byte
  tree holds 2,779,334,141: 27,181,970 nodes (2,609,465,824 bytes) and 42,458,078 label letters
  (169,832,312).
- **Exact for the declared receiver.** The readings kept beside the state 1,196,006,680 bytes (1,140
  a cell); the boundary contexts 10,184; nodes past the admitted depth 0; letters no label reads
  4,044,396 (3 a cell).
- **Charged coarsenings.** Once-reached leaf chains (17,782,143 nodes) 1,857,086,636 bytes (1,771 a
  cell); the depth cut at 12 ticks 622,696,768 (594 a cell), at 6 ticks 2,080,631,512 (1,984 a cell).
- **Refused.** Siblings with equal present counts merged into one register 867,135,528 (827 a cell).
- **After the choosing families alone** (524,091 cells): the tree 1,387,905,377 bytes, the readings
  1,136 a cell, the once-reached chains 1,766, the depth cut at 12 ticks 484.

### U2: the acceptance run of F0's memory (September 28)

Record: [U2's acceptance run](../../records/2026-09-28_U2_F0S_MEMORY_ACCEPTANCE_RUN_PINNED_BEFORE_ITS_SPLIT_IS_READ.md)
(its pins, commit `d6feae7e`, precede the split); plan:
[U2](../../../docs/plans/THE_REBUILD.md#u2-one-retention-contract-and-f0s-memory).

The fresh split and its passage (counts and hashes in the record):

```sh
HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/development_families.py U2
HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/curated_source.py 524288 choosing U2
HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/curated_source.py 524288 validation U2
HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/curated_incidence.py choosing U2
HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/curated_incidence.py validation U2
HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/family_passage.py U2
cargo run --release -p holonics --example hnn_population -- u2-acceptance .local/cuts/curated-u2-passage-cut.bin .local/cuts/curated-u2-passage-flat-cut.bin
```

`hnn_population_u2.rs` executes the pins: the conditional byte-and-stop code at `L_R = 16` (every
byte, and the section letters' mass at each response's stop), the candidates read on the choosing
families, the choice (admissible within `m = 1214` bits of the unmerged tree, charged 2 bits; the
least standing), one validation reading of the chosen candidate against the unmerged egg and the flat
tree, and the standing whole, its readings line (44 bytes a byte-tree node) and without it. The run
was made once at commit `d31c8b37`, in 262,138 ms at an 8,620,863,488-byte peak; a dry run on F4's
passage (already a diagnostic) had projected 269,015 ms and 9,366,650,880 bytes.
- **The choice** (523,671 choosing cells): the depth cut at 12 ticks `+96 + 0/16 + ε` charged
  against the unmerged tree, admissible; the once-reached leaf chains released at each `open` letter
  and the join `+18693 + 8/16 + ε`, not admissible (its release and path retired, at `d31c8b37`).
  Chosen: the depth cut.
- **Validation** (524,133 cells, read once): the cut, charged 2 bits, `+224 + 12/16 + ε` above the
  unmerged tree (within `m`); against the flat tree's bytes, its bytes `−2132 + 13/16 + ε` and its
  bytes with the stops `−810 + 9/16 + ε` (the unmerged tree `−2356 + 0/16 + ε` and
  `−1035 + 12/16 + ε`).
- **Standing after the passage** (1,047,804 cells): the unmerged egg 2,778,320,830 bytes (2,651 a
  cell; readings 1,140; without them 1,511), the cut 2,147,915,516 (2,049; readings 915; without them
  1,134). **The acceptance passes**: `f0-egg` now declares its byte tree at 12 ticks
  (`curated::F0_BYTE_DEPTH`), and `f0-census` reads the unmerged egg it replaced.

### F6 chase terrain: the reception phase (September 28)

Record: no dedicated record; the law is in [the learner must move](../../records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md) and the motion's first consumer in [the motion record](../../records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md) (§7).

```sh
cargo run --release -p holonics --example hnn_chase
```

`holarchy::terrain::chase` is the first terrain on which a mover meets another's constitution
(THE_REBUILD F6; campaign 4, #27, #148). A `16 × 16` lattice arena of `4 × 4` friction patches
(ice `1/2`, grass `1`, track `3/2`; `g = 8`, `h = 1/2`, `ℓ = 1`) admits a runner's velocity
change only if `⟨Δv, Δv⟩ ≤ (γ μ g h²/ℓ)²`. The runner demands as on the ground it last pushed
from, so a demand fails, and slips for its declared hold, where the ground under it has dropped
to a lower class. Walls clamp the step and zero the crossing velocity. A scripted pure pursuer
(speed `3/2`, traction `2`) ends the passage at capture, `Q ≤ 2`. The cells are the runner's
realized moves, slips and wall meetings: 69 moves, 71 letters. The reception population is
`receiver::population::ChaseFamily`: one family per candidate of the declared 40 (speeds `2, 3`,
traction coefficients `1, 3/2`, holds `1, 2`, flee, circle both ways, zig-zag at periods `2` and
`3`), each 6 bits, with escape mass `2^(−12)`.

The receipt covers 16 hash-seeded arenas (seeds `20260927` to `20260942`) with passages of at most
`2^8` ticks, 9 of them ended by capture (5 to 30 ticks). Each is read in at most 53 ms on the
host. On all 16:

- the population's selected fibre, read exactly as its greatest `π_f L_f`, is the surviving
  fibre and holds the truth;
- its code lies within the 6-bit naming margin of the truth family's own code;
- its code lies strictly below the landmark tree's least code over depths `1, 2, 4, 8`.

Six of the sixteen seeds, read at `L_R = 16` (the harness prints every seed with exact endpoints):

| Seed | Truth | Cells | Slips (onsets/ticks), walls | Population | Truth's own | Tree's least | Fibre | Future classes (5 ticks) |
|---|---|---|---|---|---|---|---|---|
| 20260928 | `[19]` v 3, γ 3/2, hold 1, circle cw | 256 | 19/19, 21 | `4 + 6/16 + ε` | `0 + 1/16 + ε` | `324 + 10/16 + ε` | 2 | 1 |
| 20260931 | `[36]` v 2, γ 1, hold 2, zig-zag 3 | 256 | 12/19, 6 | `5 + 6/16 + ε` | `0 + 1/16 + ε` | `619 + 5/16 + ε` | 1 (selected) | 1 |
| 20260934 | `[39]` v 3, γ 3/2, hold 2, zig-zag 3 | 256 | 8/15, 16 | `5 + 6/16 + ε` | `0 + 1/16 + ε` | `519 + 12/16 + ε` | 1 (selected) | 1 |
| 20260935 | `[37]` v 3, γ 1, hold 2, zig-zag 3 | 9, captured | 0/0, 0 | `3 + 5/16 + ε` | `0 + 0/16 + ε` | `42 + 14/16 + ε` | 4 | 2: `{33, 37}`, `{32, 36}` |
| 20260937 | `[7]` v 3, γ 3/2, hold 2, flee | 256 | 0/0, 16 | `4 + 6/16 + ε` | `0 + 1/16 + ε` | `370 + 1/16 + ε` | 2 | 1 |
| 20260941 | `[15]` v 3, γ 3/2, hold 2, circle ccw | 5, captured | 0/0, 0 | `1 + 5/16 + ε` | `0 + 0/16 + ε` | `16 + 11/16 + ε` | 16 | 1 |

A single candidate survives on 5 seeds. Every plural fibre on a passage the pursuer did not end
early differs only in its slip hold: no slip was demanded, or each slip was followed by a wall
meeting or another slip, where both holds emit alike. The fibres read as the record's
identifiability law (§14.10). Seed `20260935`'s passage ends before the runner shows its speed, so
speeds 2 and 3 survive together, and an admitted pursuer word of five ticks parts them into two
future classes. There the exact family is required only once that probe is emitted, which is the
action phase (item 13). The circle navigators ignore the pursuer, so no admitted word parts their
holds. The runs above are development receipts on terrain whose truth is exact. The action phase
(the machine as chaser, threshold commits, the switches, cornering) is not built.

### F0 candidate 3: learned tokens with the receiving tree over them (September 28)

Record: no dedicated record; THE_REBUILD's F0 carries the outcome, after [the forward plan stopped at transfer](../../records/2026-09-28_THE_FORWARD_PLAN_STOPPED_AT_TRANSFER_THE_POPULATION_MEMORIZES_FAMILIES_AND_ITS_STANDING_IS_AN_INDEX.md) (`hnn_tokens`, retired September 28, last at commit `2d34b819`).

`hnn_tokens` builds THE_REBUILD's F0 candidate 3 as a token lens: byte-pair merges learned on the
choosing role, read by the existing receiving tree (`TreeFamily`, cell-only letters over the token
alphabet, the `½` stop prior, `L_R = 16`), against the flat byte tree on the same bytes. The
computational object is the helical pair interaction: the token navigator meeting the receiving tree
at its section. It touches **faces and placement** (each token's face at its address) and the
**tower thread** (a merge is a coarsening whose restriction is its bytes; no token crosses a section);
the helix, the pair, the cell holonomy and the tube stay attached through the tree's owner.

```sh
cargo run --release -p holonics --example hnn_tokens -- probe .local/cuts/curated-f4-passage-cut.bin
cargo run --release -p holonics --example hnn_tokens -- f0 .local/cuts/curated-f4-passage-cut.bin .local/cuts/curated-f4-passage-flat-cut.bin .local/cuts/f0-token-dictionary-f4.bin
cargo run --release -p holonics --example hnn_tokens -- release .local/cuts/curated-f5-choosing-cut.bin .local/cuts/f5-blind-input.json .local/cuts/f0-token-releases.json .local/cuts/f0-token-dictionary-f5.bin 256 4
HOLONICS_ROOT=<main checkout> python3 research/notebook/hnn_design/release_legibility.py .local/cuts/f0-token-releases.json
cargo test -p holonics --example hnn_tokens
```

[definition; agent-inferred] **The law** (the example's header states it in full).
- Merges are learned greedily by pair count within parts, ties to the least pair; a section letter is
  never an operand. Frequency is the proposal order; the choosing role's charged code accepts `K`.
- The canonical parse applies the merges in learned order, left to right without overlap, and decodes
  exactly. It is one admitted parse, so its prequential code is a prefix code for the bytes.
- `K ∈ {2^8, 2^10, 2^12}` and the depth `D ∈ {2, 3, 4, 6}` tokens are chosen together by the choosing
  role's charged code: the stream plus the dictionary's description, `2⌈log₂(256 + i)⌉` bits for
  merge `i` and the Elias-gamma `K`. The sweep over 12 rungs is charged `2 + 2 = 4` bits.
- Releases draw by exact inverse CDF on the tree's face, realized as the descent of its dyadic heap
  (atlas `receiver.population-descent-inverse-cdf`). The full-face selection at K = 4,096 took
  1,143 ms for 16 draws, projecting past ten minutes for 32 releases, so it checks the descent instead:
  on its first 4 draws of each release, and at every exact cumulative boundary in the tests.

Tests: the parse decodes exactly and equals the learned stream at every prefix; no merge crosses a
section letter; over every byte string of at most 5 bytes on a 2-byte chart, the exact masses of
`open · parse(x) · stop` sum below one; the descent equals `select_family_class`; the description and
the JSON reading.

**Projection.** The bounded probe (the first `2^15` choosing tokens a rung) projected the choosing sweep
at 16,891 ms and each token passage below 5,000 ms, beside the flat tree's recorded 21,581 ms. The
releases projected 9,300 ms of descents and 9,144 ms of checks. Every run passed its projection.

**Choosing receipts** (F4's choosing role, 524,091 cells: 523,389 bytes and 702 letters). 4,096 merges
learned in 105 ms. The charged code, stream plus description, at `L_R = 16`:

| K (description) | D = 2 | D = 3 | D = 4 | D = 6 |
|---|---|---|---|---|
| 256 (4,623 bits) | `1241129 + 15/16 + ε` | `1216344 + 6/16 + ε` | **`1215631 + 5/16 + ε`** | `1215821 + 3/16 + ε` |
| 1,024 (20,495) | `1262795 + 14/16 + ε` | `1265531 + 4/16 + ε` | `1267600 + 9/16 + ε` | `1268368 + 3/16 + ε` |
| 4,096 (93,199) | `1322614 + 5/16 + ε` | `1327600 + 11/16 + ε` | `1328763 + 15/16 + ε` | `1329123 + 11/16 + ε` |

- **Chosen: K = 256, D = 4.** Its enclosure is decided below every other rung, by `189 + 13/16 + ε`
  below the next (K = 256, D = 6). The stream alone also orders K = 256 first.
- The F4 dictionary is 2,072 bytes, SHA-256
  `8f7623aed2bb831dc20311ed2553991e8292c430252853d5a6aa3de2291a86e9`, owner-only in `.local/cuts/`.

**Validation, read once** (523,236 bytes in 257,278 byte tokens and 916 letters). The flat tree
reproduces its recorded reading exactly.

| Validation bytes | Token tree (K = 256, D = 4) | Flat tree (D = 48) | Tokens against flat |
|---|---|---|---|
| human (30,841) | `67961 + 3/16 + ε` | `62604 + 5/16 + ε` | above by `5356 + 13/16 + ε` |
| agent (492,395) | `963744 + 6/16 + ε` | `891195 + 9/16 + ε` | above by `72548 + 13/16 + ε` |
| every byte | `1031705 + 10/16 + ε`, a byte `1 + 15/16 + ε` | `953799 + 15/16 + ε`, a byte `1 + 13/16 + ε` | |
| **like with like**, charged 4 and 3 | `1031709 + 10/16 + ε` | `953802 + 15/16 + ε` | **above by `77906 + 10/16 + ε`**, a byte `0 + 2/16 + ε` |
| with the dictionary's 4,623 bits too | | | above by `82529 + 10/16 + ε` |

- The section letters, coded by the token tree only: `2961 + 0/16 + ε` over 916 letters.
- On the choosing role the token bytes are `110838 + 0/16 + ε` above flat, like with like.

**Standing and work.**
- The token tree's standing is 407,818,583 bytes and the dictionary 2,072, together 407,820,655 bytes
  after 1,048,243 cells: 389 a cell, remainder 54,128. The flat tree's is 1,298 a cell and the
  admitted egg's 2,653.
- The token passage took 6,060 ms at a 1,446,195,200-byte peak resident set. The flat tree took
  22,922 ms. The whole run took 53,325 ms at a 4,414,365,696-byte peak, dominated by encoding the
  flat tree's standing.

**Releases on the spent F5 requests** (development diagnostics, never evaluation). The merges were
learned on the F5 choosing cut the same way at F4's chosen K = 256, and the tree at D = 4 read all of
it: 522,206 cells in 263,408 tokens, a 220,523,223-byte standing, 3,198 ms. The F5 dictionary is
2,072 bytes, SHA-256 `dbaedde4f6ee3756a571cd9596a1329e35d879808715054453e1e5f437858742`. The seed is
`20260928 + i` for request `i`, with a stop at a section letter or 600 bytes.
- **Outcomes.** 16 releases stopped at a section letter and 14 reached the cap. Two are typed
  refusals for invalid UTF-8.
- **Draws.** 11,358 bytes were released from 6,292 tokens drawn. 127 draws were checked equal to the
  full face's certified inverse CDF.
- **Resources.** The longest request took 153 ms, and the run 6,665 ms at a 790,351,872-byte peak.
- The owner-only releases, `f0-token-releases.json`, have SHA-256
  `1b0e23e954edf4919d49a1c905e23d2c59b5a6421ac2b663b9e091c54b5ea412`.

`release_legibility.py` counts against the F5 choosing vocabulary (6,325 words); counts only:

| Reading | Byte releases (F5 native) | Token releases | Controls | Requests |
|---|---|---|---|---|
| texts (typed refusals) | 24 (8) | 30 (2) | 32 | 32 |
| word tokens in the vocabulary | 580 of 758 | 836 of 1,527 | 3,139 of 3,306 | 1,817 of 1,932 |
| backticks even | 14 of 24 | 21 of 30 | 32 of 32 | 32 of 32 |
| `()` balanced | 16 of 24 | 15 of 30 | 32 of 32 | 32 of 32 |
| `[]` / `{}` balanced | 17 / 21 of 24 | 20 / 17 of 30 | 32 / 32 | 32 / 32 |
| straight quotes / bold even | 22 / 16 of 24 | 22 / 19 of 30 | 32 / 32 | 32 / 32 |

The token releases' word rate is below the byte releases': `836·758 = 633,688 < 580·1,527 = 885,660`.
Their backtick parity rate is above: `21·24 = 504 > 14·30 = 420`.

[interpretation] **Not adopted: the token tree codes above flat on unseen families, and its releases do
not move to whole words.**
- The charged code rises with `K` at every depth. The choosing role chose the smallest rung, K = 256,
  so the lens pulls back toward bytes.
- The receiving tree reads a token as an opaque odometer index. Tokens that share bytes share no
  counts, and a context of four tokens is sparse where a byte context of the same span is not.
- On F4's held-out passage the byte cell tree at `D = 6` codes the whole curated stream, bytes and
  letters, at `970145 + 1/16 + ε`. The token tree's bytes alone lie above that, at
  `1031705 + 10/16 + ε`.
- F0's byte code stays the admitted egg's.

### F0 candidate 2: a family wins where it is closest (September 28)

Record: [a number is a helix](../../records/2026-09-28_A_NUMBER_IS_A_HELIX_ITS_BASE_IS_A_FACE_AND_A_FAMILY_WINS_WHERE_IT_IS_CLOSEST.md) (`hnn_population f0-local`, retired September 28, last at commit `2d34b819`).

`receiver::population::LocalMixture` builds THE_REBUILD's F0 candidate 2 as a new composed family
(the [record](../../records/2026-09-28_A_NUMBER_IS_A_HELIX_ITS_BASE_IS_A_FACE_AND_A_FAMILY_WINS_WHERE_IT_IS_CLOSEST.md),
§5): a `Family` whose members are families. It forwards every cell to each member and keeps, at each
gating context `c` (the last `d` curated cells), each member's weight `π_f ∏ P_f` over the cells met
earlier in `c`. Its face mixes the members' faces under the posterior of the current context. The
population's core law is untouched. The computational object is the helical pair interaction: at
each context the members (navigator families) meet the receiving face. The owner touches **faces
and placement** (the mixed face, placed by its context), the **tube** (each context's posterior
moves only at its own ticks) and the **tower thread** (a `d = 2` context restricts to its `d = 1`
suffix and to the one context at `d = 0`). The helix, the pair's slip and the cell holonomy stay
attached through the members.

```sh
cargo run --release -p holonics --example hnn_population -- f0-local-probe .local/cuts/curated-f4-passage-cut.bin .local/cuts/curated-f4-passage-flat-cut.bin
cargo run --release -p holonics --example hnn_population -- f0-local .local/cuts/curated-f4-passage-cut.bin .local/cuts/curated-f4-passage-flat-cut.bin
cargo test -p holonics --lib local_tests
```

[proved-derived; formal-checked] **The law** (Lean `Compression/Landmark/Context/Population`):
- the faces telescope context by context to the contexts' totals (`local_telescope`);
- for every choice of one family per context, the code is at most
  `Σ_(c met) (min_f code_f(c) + log₂ M)` under the uniform prior (`local_mixture_code`);
- one context is the static mixture, whole-passage Bayes (`local_of_constant`).

[definition; established-bounded] **The executed chart.** Each weight is the dormancy module's
64-bit `Weight`, multiplied by the member's exact face and rounded down. A member more than `K = 64`
octaves below its context's leader is held at that floor, so the aligned carriers fit two machine
words. The executed face is exact and normalized, and the code lies within the bound plus a
certified drift `3·r·2^(−62) + M·φ·2^(1−K)` bits. `K` was declared as the chart's width before any
passage was read. The floor is also a switching law: a member that fell far behind returns at a price
of at most `K + log₂ M` bits a return (the owner's header; its Lean telescope is owed, #62).

Tests (exact, on fixtures): every rung's face sums to one; the opening rung equals the population's
whole-passage Bayes face by face and in its telescope; `d = 1` and `d = 2` equal node-local Bayes
stepped in ℚ, and `∏ q ≥ ∏_c max_f π_f L_f(c)` holds exactly; a rung chosen later reads as if it had
made every face; a non-dyadic face rounds within the drift; a member returns from the floor within
the switching path's code; death at zero likelihood; the refusals; and the standing's stream.

[definition; agent-inferred] **The measurement.** The eight families of `Members::Declared`, each
named by 3 bits (`π_f = 1/8` at every context), wrapped in one `LocalMixture` over the ladder
`d ∈ {0, 1, 2}`. Every rung reads every cell as a comparison. `d = 0` makes the face on the choosing
cells, and the choosing role's charged code picks the rung for validation (`⌈log₂ 3⌉ = 2` bits; ties
to the shallower). The admitted egg's own faces on the same cells are the egg alone.

**Projection.** The bounded probe read the first `2^16` choosing cells: the members alone took
8,690 ms, the mixture over them 11,519 ms. The full passage projected at 354,286 ms (the recorded
eight-family passage plus the mixture's 2,829 ms scaled, plus the flat tree and the standing stream),
within ten minutes. Memory was projected from the recorded 10,843,217,920-byte peak. The run passed
both.

**Choosing** (524,091 cells, 124,063 ms). The choosing stream, bytes and letters, at `L_R = 16`:

| Rung | Contexts met (whole passage) | Choosing stream | `d = 0` minus this rung |
|---|---|---|---|
| `d = 0` (chosen) | 1 | `1094761 + 12/16 + ε` | |
| `d = 1` | 177 | `1095008 + 11/16 + ε` | `−247 + 0/16 + ε` |
| `d = 2` | 5,286 | `1095020 + 12/16 + ε` | `−259 + 0/16 + ε` |
| the egg alone | | `1094756 + 12/16 + ε` | |

- `d = 0` is decided below both deeper rungs, so the gating ladder in space is not chosen.
- On the choosing bytes, the egg alone reads `−4593 + 5/16 + ε` against flat, as recorded, and
  `d = 0` reads `−4597 + 2/16 + ε`. That is `−5 + 12/16 + ε` against the egg alone, and
  `−3 + 12/16 + ε` with the 2 rung bits charged.
- On the choosing letters `d = 0` costs more: `2442 + 10/16 + ε` against the egg's
  `2435 + 6/16 + ε`.

**Validation** (523,236 bytes and 916 letters, read once; 139,620 ms):

| Validation bytes, the difference | Against flat | Against the egg alone |
|---|---|---|
| the egg alone | `−2430 + 8/16 + ε` (as recorded) | |
| **`d = 0`, chosen** | `−2727 + 1/16 + ε` | `−298 + 8/16 + ε` |
| `d = 0`, charged 2 bits (flat charged its 3) | `−2728 + 1/16 + ε` | **`−296 + 8/16 + ε`** |
| `d = 1`, disclosed | `−2512 + 7/16 + ε` | `−83 + 14/16 + ε` |
| `d = 2`, disclosed | `−2818 + 8/16 + ε` | `−389 + 15/16 + ε` |

- The unchosen rungs' readings are disclosed and choose nothing.
- The validation letters under `d = 0` read `3373 + 4/16 + ε`, against the egg's `3333 + 10/16 + ε`.

**The bound over every cell** (code ≤ `Σ_c min_f (code_f(c) + 3)` + drift; each drift below
`2^(−40)` bits):

| Rung | Code | Bound | Bound + drift − code | Floors bound at |
|---|---|---|---|---|
| `d = 0` | `2049206 + 0/16 + ε` | `2049463 + 15/16 + ε` | `257 + 14/16 + ε` | 270,223 cells |
| `d = 1` | `2049556 + 9/16 + ε` | `2049713 + 3/16 + ε` | `156 + 10/16 + ε` | 138,487 |
| `d = 2` | `2049328 + 5/16 + ε` | `2062784 + 8/16 + ε` | `13456 + 2/16 + ε` | 59,132 |

**Standing and work.** The standing is 11,513,530,846 bytes after 1,048,243 cells, 10,983 bytes a
cell. Of it, 11,513,530,398 bytes are the members' own checkpoints, and the chosen rung's table and
frame are 448 bytes. That is the eight-family standing again, against 2,653 bytes a cell for the egg
alone. The passage took 263,687 ms at an 8,407,535,616-byte peak resident set. Streaming the
standing took 30,973 ms and raised the peak to 14,226,153,472 bytes. The whole run took 320,571 ms.
The egg alone took 166,113 ms at 3,400,306,688 bytes, and the eight-family population 272,849 ms at
10,843,217,920.

[interpretation] **What carries the gain: dormancy in time, not in space.**
- At `d = 0` the bound's `min_f code_f` is the egg's own code, so over the whole passage the mixture
  codes `254 + 14/16 + ε` bits (less its drift) **below its best single member**. No static mixture
  can do that, since `Σ_f π_f L_f ≤ max_f L_f`. The eight families under exact whole-passage Bayes
  read the same as the egg alone. The gain is therefore the floor's: a tree that fell thousands of
  bits behind the egg returns after about `K + log₂ M = 67` bits of evidence wherever it codes
  closer for a while.
- The gating ladder does not pay on the choosing cells. Each context's posterior relearns the
  families' ranking from its prior, and the members are similar context models.

**Worker's verdict: adopted on the code criterion, as dormancy in time at `d = 0`.** The mixture's
validation bytes, with the 2 rung bits charged, lie strictly below the egg alone's: the difference
reads `−296 + 8/16 + ε`. The choosing bytes agree, charged, at `−3 + 12/16 + ε`. The gating ladder
(`d ≥ 1`) is not adopted. The adoption would restore the eight families' standing (10,983 bytes a
cell, from 2,653) and their passage time, for a difference of `−298 + 8/16 + ε` bits over 523,236
validation bytes. The section letters cost more under the mixture: `3373 + 4/16 + ε` on validation
against the egg's `3333 + 10/16 + ε`.

**Primary's verdict (September 28): measured, not adopted; the egg alone stays F0's byte
predictor.**
- **The rule.** THE_REBUILD adopts an F0 candidate by the choosing families alone. The brief put
  adoption on validation bytes, which contradicted that rule. On the choosing families the charged
  bytes read `−3 + 12/16 + ε` against the egg alone, and the whole choosing stream, letters
  included, about 7 bits above it.
- **The law.** The whole gain is carried by the floor, a switching law entered as the chart's width:
  `K = 64` sets the price of a return at `K + log₂ M` bits. Switching in time already has a declared
  law with a proved bound, the fixed share on the hazard ladder (`dormancy`,
  `switching.hazard-ladder-bound`). A number width that carries the measured effect is a literal
  inside a law, and the floor was never compared with the declared switching law.
- **The cost.** Four times the standing (10,983 bytes a cell against 2,653) and a 14,226,153,472-byte
  peak while streaming it, for `298 + 8/16` validation bits over 523,236 bytes: under one bit in
  1,700 bytes, against a rate of about `1 + 12/16` bits a byte.
- **What it shows.** Switching in time between similar context models pays on unseen families
  (`−298 + 8/16 + ε`) and hardly at all on seen ones (`−3 + 12/16 + ε`), and the gating ladder in
  space at `d = 1, 2` loses (`247` and `259` bits on the choosing stream). Mixing these families is
  not the lever on F0's rate.

### F6 chase terrain: the action phase (September 28)

Record: no dedicated record; the law is in [the learner must move](../../records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md) and the motion's first consumer in [the motion record](../../records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md) (§7).

```sh
cargo run --release -p holonics --example hnn_chase -- choose                         # stage 1
cargo run --release -p holonics --example hnn_chase -- choose 2 12 0,1,4,16,64,256    # stage 2
cargo run --release -p holonics --example hnn_chase -- action                         # acceptance
cargo test -p holonics --lib holarchy::terrain::chase_tests
```

In this phase the machine chases (THE_REBUILD F6; campaign 4, #27, #148).
`holarchy::terrain::pursuit` holds the terrain's laws for this phase: the chaser's capture reach,
the runner's viable tube, the capture basin over a fibre of candidate runners, the `Chaser` port,
the two controls and the passage. `receiver::population::chaser::MachineChaser` is the machine. It
reads the runner through the reception's population (`ChaseFamily`, escape `2^(−12)`), which reads
the chaser's live motion port (`ChaserPort`) as the chaser writes it. Every chaser has speed `3/2`
and traction `2`. It can always stop (`⌊v_C²⌋ = 2` is at most every class cap: 4, 16 and 36), and
`act` refuses any motion outside its traction-admitted set. The computational object is the helical
pair interaction: the runner and the chaser form a pair whose contact quadrance the chaser closes,
each meeting the friction field at its ground contact. The owners touch the pair, faces and
placement, the tube and the tower thread; the helix and the cell holonomy stay attached.

[definition; agent-inferred] **The laws** (the owners' headers state them in full).
- **The viable tube**, the cornering reading. The chaser's capture reach `D_k` is every position
  some chaser word of `k` ticks captures. The runner's forward viable reach is
  `F_(k+1) = Post(F_k) ∖ D_(k+1)`, and its kernel is the Pre recursion backward,
  `K_n = F_n, K_k = F_k ∩ Pre(K_(k+1))`. The reading is `|K₁| + … + |K_n|`, counted in runner motions
  `(x, v)`.
- **The capture basin over a fibre.** The fibre splits by each member's cell into observation classes.
  A class's value is `0` at capture, and otherwise `1 + min_u max_(class′)` of the value one tick
  deeper, up to the horizon `m`. A memo of belief nodes keeps it cheap: on the truth alone, depth 11
  took 10,552 nodes and 9 ms.
- **The machine.** Its fibre is the population's selected fibre.
  - It commits to a capture the basin certifies in the fewest ticks. Otherwise it commits to the
    move whose fibre-summed viable tube at `n` is least, breaking ties by nearness.
  - It probes only while the fibre is plural, where a move carries strictly more
    `I(Θ; Y_t, Y_(t+1) | do(u))` than the commit (compared exactly as `∏|c|^|c|`) and concedes at
    most `d` tube states a member.
  - Each tick records the release, the fibre's size, the certified bound and whether the leading
    class's predicted cell unfolded.
- **The controls.** Pure pursuit takes the admitted motion nearest the runner's present position.
  Constant bearing holds a collision course: approaching motions first (`⟨r, ṙ⟩ < 0`), then the least
  `|det(r, ṙ)|`, then the most closing, reading the runner as keeping its velocity.

**Choosing** (the choosing seeds `20261001 + s`, `s < 16`). The rule is the least sum of capture
ticks (an uncaptured passage counts its cap of 512), then the most seeds won against both controls,
then the least work. On these seeds pure pursuit sums 4,668 and constant bearing 240.

| Stage 1: the machine's sum (work) | `m = 4` | `m = 8` | `m = 12` | `m = 16` |
|---|---|---|---|---|
| `n = 2` | 1,157 (2,673 ms) | 159 (1,794 ms) | **150 (14,015 ms)** | 150 (55,211 ms) |
| `n = 3` | 1,157 (2,940 ms) | 154 (1,816 ms) | 150 (13,779 ms) | 150 (54,492 ms) |
| `n = 4` | 158 (969 ms) | 153 (2,123 ms) | 150 (14,053 ms) | 150 (56,726 ms) |

- The rungs at `m ≥ 12` tie at 150 with the same passages, so least work chooses `n = 2, m = 12`. A
  basin of 4 ticks certifies too late: the machine then follows pure pursuit's path and ties it.
- Stage 2, `d ∈ {0, 1, 4, 16, 64, 256}` at `n = 2, m = 12`: every rung is the same 150, and no probe
  fires. At every plural tick either every admitted move carries the same one-tick information or
  the commit is already among the most informative. So `d = 0`.
- On the choosing seeds the machine wins 9 against pure pursuit and 7 against constant bearing. The
  choice used the machine's own sum, which the controls do not enter.

**Acceptance** (seeds `20260927 + s`, `s < 16`, the reception's draw). Capture ticks are listed for
the machine, pure pursuit and constant bearing, then the truth-only basin's least capture from the
opening. That least is the least any chaser can reach knowing the runner's law, read to the machine's
own capture. The next column is the viable tube at horizon 4 under the truth, summed over the ticks
before the seed's first capture. The last column is the runner's slips, as onsets/slipping ticks.

| Seed | Truth | Machine | Pursuit | Bearing | Least | Tube before first capture | Slips |
|---|---|---|---|---|---|---|---|
| 20260927 | `[14]` v 2, γ 3/2, hold 2, circle ccw | 5 | 5 | 5 | 5 | 2291 / 2291 / 2538 | 0/0, 0/0, 0/0 |
| 20260928 | `[19]` v 3, γ 3/2, hold 1, circle cw | 16 | none | 35 | 14 | 9176 / 13138 / 11001 | 0/0, 40/40, 2/2 |
| 20260929 | `[23]` v 3, γ 3/2, hold 2, circle cw | 11 | none | 11 | 10 | 8599 / 10694 / 9324 | 0/0, 0/0, 0/0 |
| 20260930 | `[10]` v 2, γ 3/2, hold 1, circle ccw | 12 | none | 11 | 11 | 5455 / 5551 / 5564 | 0/0, 0/0, 0/0 |
| 20260931 | `[36]` v 2, γ 1, hold 2, zig-zag 3 | 14 | none | 13 | 13 | 3827 / 4163 / 4258 | 1/2, 24/37, 1/2 |
| 20260932 | `[26]` v 2, γ 3/2, hold 1, zig-zag 2 | 4 | 17 | 42 | 4 | 13 / 167 / 151 | 0/0, 0/0, 0/0 |
| 20260933 | `[14]` v 2, γ 3/2, hold 2, circle ccw | 10 | none | 11 | 4 | 1011 / 2716 / 2211 | 0/0, 0/0, 0/0 |
| 20260934 | `[39]` v 3, γ 3/2, hold 2, zig-zag 3 | 9 | none | 88 | 9 | 9707 / 15043 / 15731 | 0/0, 15/29, 5/7 |
| 20260935 | `[37]` v 3, γ 1, hold 2, zig-zag 3 | 9 | 9 | 15 | 9 | 3530 / 3884 / 7270 | 0/0, 0/0, 0/0 |
| 20260936 | `[29]` v 3, γ 1, hold 2, zig-zag 2 | 10 | 10 | 33 | 10 | 3299 / 3961 / 4206 | 2/3, 2/3, 3/5 |
| 20260937 | `[7]` v 3, γ 3/2, hold 2, flee | 10 | none | 26 | 10 | 7873 / 11046 / 14248 | 0/0, 0/0, 0/0 |
| 20260938 | `[1]` v 3, γ 1, hold 1, flee | 11 | 11 | 14 | 11 | 2390 / 2390 / 4212 | 0/0, 0/0, 0/0 |
| 20260939 | `[35]` v 3, γ 3/2, hold 1, zig-zag 3 | 12 | 12 | 13 | 12 | 13837 / 13850 / 14456 | 0/0, 0/0, 1/1 |
| 20260940 | `[39]` v 3, γ 3/2, hold 2, zig-zag 3 | 13 | 30 | 17 | 13 | 7380 / 7724 / 11472 | 0/0, 1/1, 0/0 |
| 20260941 | `[15]` v 3, γ 3/2, hold 2, circle ccw | 5 | 5 | 5 | 5 | 9548 / 9548 / 9697 | 0/0, 0/0, 0/0 |
| 20260942 | `[37]` v 3, γ 1, hold 2, zig-zag 3 | 13 | 21 | 27 | 13 | 13118 / 14702 / 17105 | 1/2, 1/2, 2/4 |

- **Sums.** Capture ticks: the machine 164, pure pursuit 3,704, constant bearing 366 ("none" counts
  512). The tube before each first capture sums to 101,054, 120,868 and 133,444. Over whole
  passages it sums to 101,054, 2,750,616 and 227,295. The runner's slips are (4, 7), (83, 112) and
  (14, 21), with 9, 151 and 19 wall meetings.
- **Seeds won.** The machine is strictly faster on 10 seeds against pure pursuit, on 11 against
  constant bearing and on 7 against both at once. It reaches the truth-only least on 11.
- **The machine's releases.** 152 certified, 11 commits and 1 probe (on seed 20260942). The leading
  class's predicted cell missed on 21 of its 164 ticks.
- **Verdict: not passed** under the at-once reading (7 of 16). It passes in sum and against each
  control separately (10 and 11 of 16).
- [measured] **No chaser can pass the at-once reading on these seeds.** On 8 seeds (20260927,
  20260930, 20260931, 20260935, 20260936, 20260938, 20260939 and 20260941) a control already
  captures at the truth-only least, so no chaser beats both there. That leaves 8 seeds, which is not
  more than half, and the machine takes 7 of them. It misses 20260929, at 11 ticks against the least
  of 10 and bearing's 11.
- **Where the machine misses the least** (5 seeds: 20260928, 20260929, 20260930, 20260931 and
  20260933), it plans robustly over the opening's wide fibre. On 20260933 it certified capture within
  10 ticks over all 40 candidates at tick 0, while the truth alone is caught in 4.
- **The cornering receipt, tick by tick**, on 20260937 (the flee runner):

  | Chaser | The tube at horizon 4, ticks 0 to 11 | Capture |
  |---|---|---|
  | The machine | 3203 1589 590 1067 727 423 168 106 0 0 | tick 10 |
  | Pure pursuit | 3203 1589 590 1067 727 423 168 239 1199 1841 1990 80 … | none by 512 |
  | Constant bearing | 3203 1667 725 1891 1708 1528 1307 1056 740 423 168 106 … | tick 26 |

  Pure pursuit shares the machine's first seven ticks. It then lets the runner out while the machine
  closes the tube to zero, cornering it two ticks before capture. `action trace` prints every
  passage this way.
- **The control was corrected before this verdict.** The first acceptance run's constant bearing
  ordered `|det(r, ṙ)|` before approach. Against a runner at rest, resting nulls the rotation, so it
  stood still: its tube held at 1985 for hundreds of ticks on 20260937, and it summed 4,934 capture
  ticks. Against that control the machine won 12 of 16 and 6 at once, with the same verdict. The
  correction follows §14.4 ("approach also needs `⟨r, ṙ⟩ < 0`") and strengthens the control.
- **Resources.** The acceptance run took 18,055 ms at a 249,788 kB peak resident set. Each seed's
  machine passage took 108 to 2,875 ms. Stage 1 took 220,727 ms at a
  510,580 kB peak, and stage 2 took 83,171 ms at 256,012 kB.
- **Tests** (`chase_tests.rs`, under a second together):
  - the tube's `F_k` and `K_k` equal a brute-force enumeration of runner and chaser words on a
    `6 × 6` arena at `n = 3`, over four cases: two constitutions, a held slip, and one cornered
    runner;
  - every motion the machine and both controls release satisfies the traction bound in ℚ on the cell
    it left, within the speed bound and inside the arena;
  - the machine's certified captures are kept;
  - a chaser outside its bound is refused;
  - the controls' laws.
- **Not built.** The switches: the lag channel, and three observation channels with loop-closure
  attribution. The construction record's F6 action-phase receipt and #62 ("The chase consumer") record the owed Lean.

### F6: the chase reads the move pair, and the move reading (U4's rebase, September 28)

Record: the motion's first consumer, [the motion record §7](../../records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md#7-the-first-consumer-the-chase); THE_REBUILD U4.

```sh
cargo run --release -p holonics --example hnn_chase                    # the reception phase
cargo run --release -p holonics --example hnn_chase -- action trace    # the action phase, with the move reading
cargo test -p holonics --lib geometry::motion holarchy::terrain
```

[definition; agent-inferred] **The rebase.** `holonics::geometry::motion` owns the move pair
`(v, v′)` over the Gaussian integers `ℤ[i]`, carried undivided (`Move`), with its change, its kind
(`MoveKind`: rest, start, stop, free fall, turn, boost, turn and boost, decided on the integers
without division where a velocity vanishes), its traction disk (`within_cap` on the lattice at
`⌊r²⌋`, `within_bound` in ℚ), its power `Re(v̄·Δv)` and its signed turn `Im(v̄·Δv)`, each cited to
Lean `Geometry/Motion`. The chase's traction law (`RunnerLaw::admits`), its demand and slip test
(`Runner::demand`, `Runner::cell`), its letters (`Arena::observe`: a move letter realizes
`(v, v + Δv)`, a slip the held move `(v, v)`), the chaser's admitted motions (`Pursuer::motions`) and
the viable tube's successors (`pursuit`'s `post`) read their moves through it. The lattice
arithmetic (`Point`, `add`, `sub`, `scale`, `quadrance`, `quarter_turn`, `dot`, `det`) moved into the
owner, each checked equal to `ratio::GaussianRat`'s on `ℤ[i]`; it stays in machine words because the
tube and the basin read it for every runner motion of every decision. `floor_cap` stays in the chase:
it reads the chase's declared rational bounds (speed, capture) as well as the traction disk.

**Parity: every chase receipt is unchanged.** The 11 chase and pursuit tests pass with their file
untouched. Built before and after the rebase, the harness's output agrees line for line with only
the wall times masked: the reception phase's 414 lines (the 16 arenas' codes, fibres and future
classes), `action trace`'s 185 lines (capture ticks 164 / 3,704 / 366, the cornering sums
101,054 / 120,868 / 133,444 and 101,054 / 2,750,616 / 227,295, every tube tick by tick, the slips
(4, 7) / (83, 112) / (14, 21), the walls 9 / 151 / 19, the releases 152 / 11 / 1 and the 21 misses)
and the choosing rung `choose 2 12 0` (150 / 4,668 / 240). The action run took 16,020 ms at a
249,420 kB peak resident set (16,620 ms at 249,156 kB before).

**The move reading** (a reading of the receipt, not a change of law): each tick's move of the
runner and of the chaser by kind, over the 16 acceptance seeds.

| Against | Mover | Rest | Start | Stop | Free fall | Turn | Boost | Turn and boost |
|---|---|---|---|---|---|---|---|---|
| the machine | runner | 22 | 33 | 24 | 38 | 3 | 22 | 22 |
| | chaser | 0 | 16 | 1 | 104 | 16 | 0 | 27 |
| pure pursuit | runner | 133 | 339 | 332 | 1,969 | 91 | 370 | 470 |
| | chaser | 0 | 16 | 0 | 2,796 | 367 | 0 | 525 |
| constant bearing | runner | 46 | 63 | 52 | 82 | 8 | 61 | 54 |
| | chaser | 0 | 17 | 1 | 149 | 102 | 0 | 97 |

- **Every slip reads as the demanded move outside the traction disk while the realized move is the
  held one.** Every onset's demanded move (the runner's law re-read at the tick) lies outside the
  disk of the cell it stands on: 4 of 4, 83 of 83 and 14 of 14. Every slipping tick realizes
  `(v, v)`: 7 of 7, 112 of 112 and 21 of 21. The demanded moves are turns and boosts (4; 69; 6),
  pure turns (0; 13; 1) and stops (0; 1; 7): a stop demanded as on the firmer ground behind slips
  where the speed passes the disk of the ground underfoot.
- **The chaser never boosts purely.** Its speed cap `⌊v_C²⌋ = 2` admits only the nonzero lattice
  velocities of quadrance `1` (the axes) and `2` (the diagonals), one to each ray, so each of its
  speed changes turns as well. Its starts are its openings, one a seed, and constant bearing's one restart after
  its one stop; the machine's one stop is its last move before capture.

### F6: the chaser releases through the one law (U3's second loop, September 28)

Record: no dedicated record; the law is in `receiver::release` and `receiver::population::chaser`
(their headers), and F6's amended action law in [THE_REBUILD](../../../docs/plans/THE_REBUILD.md#f6-motion-the-chase-terrain-then-the-motor-chart-campaign-4-27-148); U3, #73, #27.

```sh
cargo run --release -p holonics --example hnn_chase                    # the reception phase
cargo run --release -p holonics --example hnn_chase -- action trace    # the action phase, each uncertified release read through the law
cargo run --release -p holonics --example hnn_chase -- choose 2 12 0   # the chosen rung
cargo test -p holonics --lib receiver::release receiver::population::chaser holarchy::terrain::chase_tests
```

[definition; agent-inferred] **The chaser's arms.** Each tick the machine reads the
capture-within-`m` reading over the population's selected fibre and decides it by the one law
(`DecisionRule(Release, Ask)` at tolerance zero). The basin's certificate over every member is
width zero, and the law returns `Released`: the certified capture. Beyond it the law asks the
offered probe (`Ask`, carrying its `ProbePartition`: its class sizes against the commit's, compared
as `∏|c|^|c|`) and holds where no admitted motion separates the fibre more than the commit. The
cornering commit is the declared separate arm. It takes the law's `Hold`, or an `Ask` whose
concession `K(u_p) − K(u*)` exceeds the price `d·|Θ|`: the price is its separating term.

**Parity: every chase receipt reproduces exactly.** The harness was built at `c10acca9` and after the
change, and each run was compared with only the wall times masked.
- The reception phase: 414 lines, identical.
- `action trace`: 342 lines, identical, with 12 new lines, one for each uncertified release. They
  carry the capture ticks 164 / 3,704 / 366 and each seed's; the cornering sums 101,054 / 120,868 /
  133,444 and 101,054 / 2,750,616 / 227,295 with every tube tick by tick; the slips (4, 7) / (83, 112)
  / (14, 21); the walls 9 / 151 / 19; the releases 152 / 11 / 1; and the 21 misses.
- `choose 2 12 0`: 150 / 4,668 / 240, identical.
- A scratch printer read every machine receipt tick by tick (release, fibre, certified bound,
  misses) on 64 passages: the acceptance seeds at `d = 0, 1, 256` and the choosing seeds at
  `d = 0`. It agreed on every tick. At `d = 256` the acceptance seeds release 4 probes: three on
  20260932, at fibres 40, 24 and 16, and one on 20260942.
- The pre-U3 selector runs beside the law in `chaser_tests.rs` and agrees on 8,320 fixtures.
- The action run took 16,310 ms at a 249,280 kB peak resident set (16,695 ms at 249,484 kB before).

**The uncertified releases on the acceptance seeds at `d = 0`.**

| Seed, tick | Fibre | The law | The arm |
|---|---|---|---|
| 20260942, 0 | 40 | `Ask`: classes `{12, 4, 2, 4, 2, 4, 2, 6, 2, 2}`, `∏ = 2^64·3^18`, against the commit's `{12, 6, 4, 2, 4, 2, 6, 2, 2}`, `2^60·3^24` | the probe, emitted (concession 0) |
| 20260932, 0 | 40 | `Ask`: `{16, 6, 2, 4, 4, 4, 4}`, `2^104·3^6`, against `{24, 4, 4, 4, 4}`, `2^104·3^24` | cornering: concession 242 above the price 0 |
| 10 ticks on 6 seeds (20260928 ticks 0–3; 20260930, 20260934, 20260940, 20260941 tick 0; 20260931 ticks 0–1) | 40, 28, 2, 2; 40; 40, 12 | `Hold` | cornering: no probe offered |

[measured] **What the sequential test would read.** Of the 152 certified releases on the acceptance
seeds, 143 came over a plural fibre (138 of 144 on the choosing seeds). There every member's
likelihood is `(1 − η)^n` (Lean `Population.survivors_share_one_likelihood`), and the accumulated
log-odds between members are zero. A test on them commits only on the 9 ticks (6 on the choosing
seeds) whose fibre is one member, and the capture reading had already certified every one. No
cornering commit came over a single member. So F6's action law is amended to the built rule
(THE_REBUILD F6, with the superseded text quoted).

### F6: the measured failure located, a candidate plan, and a fresh population (U4's next loop, September 28)

Record: no dedicated record; THE_REBUILD U4 ("The measured next failure first"; "F6's action
acceptance stays as written"). Campaign 4, #27, #148.

```sh
cargo run --release -p holonics --example hnn_chase -- diagnose 20260928 20260929 20260930 20260931 20260933
cargo run --release -p holonics --example hnn_chase -- choose 2 12 0 robust,certified-expected,expected
cargo run --release -p holonics --example hnn_chase -- fresh    # at commit 7f2c5d4f; `fresh` now reads the pledge loop's population
cargo test -p holonics --lib holarchy::terrain::chase_tests
```

The computational object is the helical pair interaction: the runner and the chaser as a pair whose
contact quadrance the chaser closes. This loop touches the **pair** (the capture basin and the
expected capture read the contact) and **faces and placement** (each candidate's cell face, the
fibre's observation classes and their posterior weights); the helix, the cell holonomy, the tube and
the tower thread stay attached through the terrain's laws.

**The failure, read from the traces** (`diagnose`: the machine itself decides; beside it each tick
reads every admitted move's certificate `b(u)` over the fibre at `m = 12`, its cornering `K(u)`, its
nearness `N(u)`, its information product, and the truth's own least capture through the move, the
truth-only basin from the joint state after it; the diagnosis checks that the commit order on its
readings returns the machine's release at every certified and committed tick). On each of the 5
seeds the regret enters at exactly one tick, and every other tick keeps the truth's least:

| Seed | Regret tick | Fibre (classes) | Release | The separator |
|---|---|---|---|---|
| 20260928 | tick 1: 15 against the truth's 13 (+2) | 28 (2) | commit | **the horizon**: no move is certified within `m = 12` (the truth alone needs 13 from here), the tube at `n = 2` is flat across the 9 moves (`K = 1416` each), and the fibre-summed nearness (1010 against 1114) releases a move the truth pays 2 ticks for |
| 20260929 | tick 0: 11 against 10 (+1) | 40 (8) | certified | **a tie of certificates**: four moves certify `b = 11`; the fibre-summed tube takes `K = 5088` over the truth's moves at 5198 and 5348 |
| 20260930 | tick 5: 7 against 6 (+1) | 4 (1) | certified | **a tie of certificates** with a flat tube: six moves at `b = 7`, `K = 50` each; the nearness takes 196 over the truth's 200 |
| 20260931 | tick 6: 8 against 7 (+1) | 4 (2 + 2) | certified | **the truth's class**: the two classes need different moves and every move leaves one of them at 8; the classes part on the runner's cell of that tick, read only after the move, and the truth stands in the one the tie order does not favour |
| 20260933 | tick 0: 10 against 4 (+6) | 40 (6) | certified | **a tie of certificates**: six moves certify `b = 10`; the tube takes `K = 2526` over the truth's move at 2848, which alone captures it in 4 |

[measured] No regret tick is a probe's (no probe fired) and none a basin horizon too short to
certify a move the truth needed, except 20260928's. On four seeds the robust certificate ties
across the moves, and its worst case over the fibre does not read the members it does not bind;
the tie then goes to the fibre-summed tube or, where the tube is flat, to the nearness.

**The candidate** ([definition; agent-inferred]; `receiver::population::chaser::Plan`,
`holarchy::terrain::pursuit::{ExpectedCapture, expected_ticks}`): read every member at its
posterior weight. The **expected capture** `E(u)` is the Bellman value at a unit price a tick over
the fibre's classes: the members an adaptive strategy leaves uncaptured within `m`, then the sum of
the others' capture ticks, least lexicographically; the fibre's posterior is uniform, so the sum
orders the expectations exactly. On the diagnosis's regret ticks `E` picks a move the truth needs
on 20260929 (`E = (0, 337)`), 20260930 (`(0, 26)`) and 20260933 (`(0, 242)`); on 20260928 it ties
(`(14, 140)` on three moves, the nearness again) and on 20260931 it weighs the other class
(`(0, 29)` against `(0, 30)`). Two plans place it: after the certificate (`certified-expected`) or
before it (`expected`). **Chosen on the choosing seeds only** (`choose 2 12 0 …`, the pinned rule:
the least sum of capture ticks, then the most seeds won against both, then the least work): the
robust plan sums 150 (3 won against both), the certified-then-expected plan 148 (4) and the expected
plan 147 (4), so the candidate is **the expected plan** at the pinned `n = 2, m = 12, d = 0`. The
sweep took 94,791 ms at a 617,548 kB peak. The robust plan's receipts are unchanged: `action trace`
agrees line for line with the rebase's (342 lines, wall times masked).

**Pinned before the run** (this commit; `hnn_chase.rs`'s `FRESH_SEED`, `FRESH_SEEDS`,
`CANDIDATE_PLAN` and `fresh`):
- **The fresh population**: seeds `20261101 + s`, `s < 64`, a declared contiguous range disjoint
  from the acceptance and choosing seeds, none read before this pin and none selected by any
  property. Projected from the choosing sweep at about four minutes and under 1 GB, against ten
  minutes and 20 GB.
- **The chasers**, each from the reception's draw under the same traction bound: the machine under
  its robust plan (the current rule), the candidate, pure pursuit and constant bearing; an
  uncaptured passage counts its cap `2^9`. The truth-only least `L` is read to the least of the four
  captures, which bounds it.
- **The criteria**: aggregate capture ticks `Σ T` for each chaser; the sum of regrets
  `Σ (T − L)`; win/tie/loss (strictly fewer ticks, equal, more) of each machine against pure
  pursuit, against constant bearing and against both at once (the lesser of the two on the seed),
  and of the candidate against the robust machine; F6's action acceptance as written for each
  machine (strictly fewer ticks than both controls in sum and strictly fewer than both on more than
  half of the seeds); the candidate improves on the current machine exactly when its aggregate
  capture ticks are strictly fewer and it wins more seeds against it than it loses.
- **Reported separately, as a conditional reading, never as the acceptance**: the seeds whose
  truth-only least lies strictly below both controls, with each machine's win/tie/loss against both
  at once and its regret sum there.
- **Amended before the rerun** (the next commit). The first run stopped at seed `20261135`, the
  35th, after 34 seeds (118,694 ms, 635,312 kB peak): its draw opens the runner and the chaser
  within capture, which the terrain refuses (`Chase::draw`, `pursuit::act`), and the pin had not
  declared the case. A refused draw is a seed with no chase: it is printed, read by no chaser and
  enters no sum, and "more than half of the seeds" counts the chased seeds. The refusal reads the
  openings alone, the same for every chaser, so it selects by no chaser's outcome. Nothing else
  changed; the rerun must reproduce the first run's 34 seed lines exactly.

**The run** (once, on the amended pin: `fresh`, 226,712 ms at a 643,932 kB peak; its first 34 seed
lines equal the stopped run's). The terrain refuses 2 of the 64 draws (20261135 and 20261149 open
within capture), so 62 seeds are chased.

| Over the 62 chased seeds | The machine (robust) | The candidate (expected) | Pure pursuit | Constant bearing |
|---|---|---|---|---|
| Capture ticks in sum | 594 | **574** | 15,348 | 1,559 |
| The sum of regrets to the truth-only least (`Σ L = 565`) | 29 | **9** | 14,783 | 994 |
| Win/tie/loss against pure pursuit | 41/21/0 | 42/20/0 | | |
| Win/tie/loss against constant bearing | 49/9/4 | 50/12/0 | | |
| Win/tie/loss against both at once | 35/23/4 | 37/25/0 | | |
| Releases: certified, commit, probe | 549, 44, 1 | 530, 40, 4 | | |

- **The candidate against the robust machine**: 12 won, 49 tied, 1 lost (20261126, 10 against
  8). The candidate's regret falls on 6 seeds (20261101 +2, 20261109 +1, 20261126 +2, 20261129 +1,
  20261137 +2, 20261157 +1); the robust machine's on 15. **Verdict: the candidate improves on the
  current machine** (fewer ticks in sum, more seeds won than lost against it).
- **F6's action acceptance as written**, its capture bullet (strictly fewer ticks than both
  controls in sum and strictly fewer than both on more than half of the seeds): on the fresh
  population it passes for the robust machine (35 of 62) and for the candidate (37 of 62). On the
  pinned acceptance seeds it failed (7 of 16), and that failure stands as written. The acceptance's
  other bullets are not read here: the switches (lag and the faulty sensor) are not built, so F6's
  action acceptance as a whole is not passed.
- **The conditional reading** (not the acceptance): 39 of the 62 seeds admit a win beyond both
  controls (the truth-only least strictly below both); there the robust machine wins 35, ties 1 and
  loses 3 against both at once (regret 28), and the candidate wins 37, ties 2 and loses 0 (regret 9).
- **Work.** The candidate reads the expected capture for all 9 moves at every tick. Its
  certificate is kept as the release's reading but is no longer a promise: after a certified release
  the expected plan may leave the minimax strategy, so capture can come later than the certified
  bound (the test checks the plan's motions against the traction bound, not the certified bound).

### F6: the capture distances as a function of the admitted move set (U4's next loop, September 28)

```sh
cargo run --release -p holonics --example hnn_chase -- moves          # the acceptance seeds
cargo run --release -p holonics --example hnn_chase -- moves fresh    # the fresh population
```

[definition; agent-inferred] `pursuit::MoveSet` is a declared variant of the chaser's move set,
not a change of the terrain's law: the chaser moves on the lattice `(1/g)ℤ[i]` under the same speed
bound `3/2`, the same traction disk on the same friction field and the same capture `ρ² = 2`, each
bound read exactly in the grain's units, optionally without pure boosts or below a declared top
speed; the runner reads the chaser at any grain by the plane's law (`Runner::cell_at_grain`, every
score `g²` times the plane's). `pursuit::least_capture` reads the truth-only least breadth-first over
the joint states (the runner is one deterministic law); on the lattice it equals the capture basin's
truth-only reading on every seed read (checked at run time, and in the test). The four sets:
**L**, the chaser's lattice (no pure boost; axis speed 1, diagonal `√2`); **H≤√2**, the half
lattice held to the lattice's realized top speed `√2` (pure boosts `1/2 → 1` admitted); **H∖B**, the
half lattice without pure boosts (axis speed `3/2` reached by starts and turns); **H**, the half
lattice.

| Seed | L | H≤√2 | H∖B | H |
|---|---|---|---|---|
| 20260927 | 5 | 5 | 5 | 5 |
| 20260928 | 14 | 14 | 11 | 11 |
| 20260929 | 10 | 10 | 8 | 8 |
| 20260930 | 11 | 11 | 9 | 9 |
| 20260931 | 13 | 13 | 12 | 12 |
| 20260932 | 4 | 4 | 3 | 3 |
| 20260933 | 4 | 4 | 4 | 4 |
| 20260934 | 9 | 9 | 8 | 8 |
| 20260935 | 9 | 9 | 8 | 8 |
| 20260936 | 10 | 10 | 8 | 8 |
| 20260937 | 10 | 10 | 9 | 9 |
| 20260938 | 11 | 11 | 11 | 11 |
| 20260939 | 12 | 12 | 11 | 11 |
| 20260940 | 13 | 13 | 11 | 11 |
| 20260941 | 5 | 5 | 5 | 5 |
| 20260942 | 13 | 13 | 10 | 10 |
| **Sum (16)** | **153** | **153** | **133** | **133** |
| **Sum, the fresh population (62)** | **565** | **565** | **478** | **478** |

- [measured] **The pure boost is not what the lattice lacks.** Admitting pure boosts below the
  lattice's top speed changes no seed's least (L = H≤√2 on all 78), and removing them from the half
  lattice changes none either (H∖B = H on all 78).
- [measured] **The lattice under-realizes the chaser's declared speed.** At `v_C = 3/2` its nonzero
  velocities have quadrance `1` or `2`, so along an axis it moves at 1, not `3/2`. The half lattice
  realizes `3/2` on the axes, and that alone lowers the least on 12 of the 16 acceptance seeds (20
  ticks) and on 46 of the 62 fresh seeds (87 ticks). The capture distances are a function of the top
  speed the move set realizes on each ray, not of which kinds of move are elementary.
- Work: 11,547 ms at an 89,940 kB peak (16 seeds) and 79,979 ms at 88,872 kB (62 seeds).
- **Owed in Lean** (#62, "The chase consumer"): the expected capture's recursion is exact (the
  least of a sum of independent class strategies is the sum of their least, on lexicographic `ℤ²`),
  and the grain embedding `g ↦ kg` keeps every admitted motion and the runner's order, so a finer
  set's least capture is at most the coarser's. Both are checked here by tests, not proved.
- Gates: `cargo check --workspace --all-targets`; `cargo test -p holonics --lib`, 895 passed (the
  chase tests 13, two of them new: the expected capture and the move set).

### F6: the chaser's release is its own continuation, the pledge (U4's next loop, September 28)

Record: no dedicated record; THE_REBUILD U4 ("The pledge"). Campaign 4, #27, #148.

```sh
cargo run --release -p holonics --example hnn_chase -- choose 2 12 0 robust,certified-expected,expected
cargo run --release -p holonics --example hnn_chase -- fresh
cargo test -p holonics --lib holarchy::terrain::chase_tests
cargo test -p holonics --lib receiver::population::chaser
```

The computational object is the helical pair interaction: the runner and the chaser as a pair whose
contact quadrance the chaser closes. This loop touches the **pair** (the capture basin and the
expected capture read the contact, and the pledge bounds when it closes) and **faces and placement**
(the fibre's observation classes and their posterior weights); the helix, the cell holonomy, the
tube and the tower thread stay attached through the terrain's laws.

**The problem, at the consumer.** Every plan decides through `release_among`: the commit in the
plan's order, then `receiver::release::release` at tolerance zero on the capture reading over the
selected fibre, and width zero (the capture basin certifies the commit) returns `Released`. Under the
robust and certified-then-expected plans the least certificate comes first, so the next tick's least
is at most `b(u*) − 1` and the released bound is the machine's own. The expected plan ordered by
`E(u)` first and released the commit's certificate `b(u*)`; it may leave the minimax strategy after
the release, so that bound was the terrain's.

**The law** ([definition; proved-derived; agent-inferred]; `receiver::population::chaser`'s header
states the argument in full, `pursuit::ExpectedCapture` the recursion):
- `ExpectedCapture` gains a third coordinate, `W`, the least worst case among the strategies of the
  least sum: `(U, S, W) ⊕ (U′, S′, W′) = (U + U′, S + S′, max(W, W′))`, still exact (the first two
  coordinates are additive and `⊕` is monotone in the lexicographic order). `U = 0` exactly when the
  capture basin certifies the fibre, and then `b ≤ W ≤` the horizon.
- A `Released` tick carries its **bound** `B_t` (`MachineReceipt::certified`), and the machine keeps
  the **pledge** `T = min_t (t + B_t)`. Under the robust plans `B_t = b(u*)`. Under the **pledged
  expected plan** `B_t = W(u*)`, and once a pledge stands `E` is read at the depth `T − t − 1`: the
  horizon is frozen at the release.
- **It keeps its bound.** The child of `E(u*) = (0, S, W)` for the class the runner's cell names reads
  `U = 0` at depth `W − 1`, and that child is the least over the next tick's moves of `E` read to the
  pledge. So every later commit is certified with `W′ ≤ W − 1`, the deadline never moves later, and
  every member is captured by `T`. The frozen reading is the Bellman value of the least expected
  capture among the strategies that capture every member by `T`, which continues the value the plan
  chose by at the release.
- **The alternatives, decided from the mathematics.** The commit's certificate as the expected plan's
  bound fails: a sum falls by delaying the worst member (captures at `1` and `6` sum `7`, at `4` and
  `4` sum `8`). `W` read with a sliding horizon (`E` at `m` every tick) is time-inconsistent: a tick
  later the horizon is one tick further, and a lesser sum that captures a member there is taken. A
  pledge at `b(u*)` with `E` inside it is kept, but the release tick then chose by a value its pledge
  forbids. The certified-then-expected plan keeps its bound already; the choosing seeds decide
  between it and the pledged plan.
- **A broken pledge**: where no admitted move is certified within `T − t`, the runner has left every
  fibre member's law. The pledge is counted (`MachineReceipt::broken`), dropped, and the plan reads on
  at `m`. With the truth in the declared family it never breaks.

[measured] **The unpledged plan kept its bounds by the terrain.** Read on 94 seeds (the 16 choosing
seeds, the 16 acceptance seeds and the 62 chased seeds of the spent first fresh population), the
unpledged expected plan at commit `7f2c5d4f` released 814 bounds (141, 143 and 530) and capture came
within every one. It was never a promise the plan made, and the pledge makes it one.

**Chosen on the choosing seeds only** (`choose 2 12 0 robust,certified-expected,expected`, the pinned
rule: the least sum of capture ticks, then the most seeds won against both controls, then the least
work; the sweep now prints each rung's released bounds and whether its passages kept them):

| Plan (`n = 2, m = 12, d = 0`) | Capture ticks in sum | Won against both, of 16 | Released bounds kept | Pledges broken | Work |
|---|---|---|---|---|---|
| Robust | 150 | 3 | 144 of 144 | 0 | 13,206 ms |
| Certified, then expected | 148 | 4 | 142 of 142 | 0 | 39,624 ms |
| **Expected, pledged** | **147** | **4** | 141 of 141 | 0 | 29,982 ms |

The least sum chooses the **pledged expected plan**. Its capture ticks equal the unpledged plan's on
every choosing seed (147 in both), with less work, since `E` is read to the pledge rather than at `m`
after the first release. The sweep took 82,822 ms at a 653,468 kB peak. The robust plan's receipts
are unchanged: `action trace` agrees line for line with the previous commit's (354 lines, wall times
masked).

- Tests: `holarchy::terrain::chase_tests::every_released_bound_is_kept_by_the_plan_itself` (every
  plan, on the 16 choosing seeds and on 11 chased fixtures of an `8 × 8` arena of the same law at
  `m = 6`: capture within every released bound, deadlines never later, a release followed only by
  releases, no pledge broken); `receiver::population::chaser::tests::the_released_bound_is_the_plans_own`
  (the pledged plan releases its own strategy's worst case `6` where the certificate is `4`, and a
  disagreeing reading is refused); the expected-capture test reads `W` against the basin's
  certificate and the horizon.
- **Owed in Lean** (#62, "The chase consumer"): the three-coordinate recursion is exact, `U = 0`
  exactly when the basin certifies and then `b ≤ W ≤` the depth, and the pledged plan keeps its
  bound (the frozen-horizon reading of the class the cell names attains `U = 0` at `W − 2`, so each
  later `W′ ≤ W − 1`).

**Pinned before the run** (this commit; `hnn_chase.rs`'s `FRESH_SEED`, `FRESH_SEEDS`,
`CANDIDATE_PLAN` and `fresh`):
- **The fresh population**: seeds `20261201 + s`, `s < 64`, a declared contiguous range disjoint from
  every range read so far (the acceptance seeds `20260927 + s` and the choosing seeds
  `20261001 + s`, `s < 16`; the spent first fresh population `20261101 + s`, `s < 64`, which `moves
  fresh` still reads), none read before this pin and none selected by any property. Projected from
  the first fresh run (226,712 ms at 643,932 kB) and the pledged rung's lesser work at about four
  minutes and under 1 GB, against ten minutes and the host's memory.
- **The chasers**, each from the reception's draw under the same traction bound: the machine under
  its robust plan (the current `MachineChaser::new`), the candidate (the pledged expected plan at
  `n = 2, m = 12, d = 0`), pure pursuit and constant bearing; an uncaptured passage counts its cap
  `2^9`. The truth-only least `L` is read to the least of the four captures, which bounds it. A draw
  the terrain refuses (openings within capture) is printed, read by no chaser and enters no sum, and
  "more than half of the seeds" counts the chased seeds.
- **The criteria**, the first fresh run's: aggregate capture ticks `Σ T` for each chaser; the sum of
  regrets `Σ (T − L)`; win/tie/loss (strictly fewer ticks, equal, more) of each machine against pure
  pursuit, against constant bearing and against both at once (the lesser of the two on the seed),
  and of the candidate against the robust machine; F6's action acceptance as written for each
  machine.
- **The adoption rule**, fixed now: the candidate becomes `MachineChaser::new` exactly when its
  aggregate capture ticks are strictly fewer than the robust machine's and it wins more seeds against
  it than it loses.
- **Printed beside them, not criteria**: each machine's released bounds and those its passages kept,
  and the pledges broken. **Reported separately, as a conditional reading, never as the
  acceptance**: the seeds whose truth-only least lies strictly below both controls, with each
  machine's win/tie/loss against both at once and its regret sum there.

**The run** (once, on the pin: `fresh`, 179,384 ms at a 626,836 kB peak, within its projection).
The terrain refuses 1 of the 64 draws (20261239 opens within capture), so 63 seeds are chased.

| Over the 63 chased seeds | The machine (robust) | The candidate (pledged expected) | Pure pursuit | Constant bearing |
|---|---|---|---|---|
| Capture ticks in sum | **617** | 618 | 14,657 | 2,008 |
| The sum of regrets to the truth-only least (`Σ L = 592`) | **25** | 26 | 14,065 | 1,416 |
| Win/tie/loss against pure pursuit | 43/20/0 | 44/19/0 | | |
| Win/tie/loss against constant bearing | 41/18/4 | 45/16/2 | | |
| Win/tie/loss against both at once | 28/31/4 | 32/29/2 | | |
| Releases: certified, commit, probe | 581, 33, 3 | 582, 31, 5 | | |
| Released bounds kept, pledges broken | 581 of 581, 0 | 582 of 582, 0 | | |

- **The candidate against the robust machine**: 6 won, 54 tied, 3 lost. It gains 12 ticks on 6
  seeds (20261204 +1, 20261218 +2, 20261219 +2, 20261225 +3, 20261230 +2, 20261256 +2) and loses 13
  on 3 (20261203 +11, 20261212 +1, 20261252 +1). **The adoption rule is not passed**: its aggregate
  (618) is not strictly fewer than the robust machine's (617), though it wins more seeds against it
  than it loses. `MachineChaser::new` stays the robust plan, so `action trace` is unchanged: it
  agrees line for line with the previous commits' (354 lines, wall times masked), and the 16
  acceptance seeds' reading stands (164 capture ticks, 7 of 16 won against both controls at once).
- **The loss, read on the spent seeds after the run** (each machine's releases tick by tick). On
  20261203 neither machine certifies at tick 0 (a fibre of 40, no move certified within `m = 12`),
  and both commit uncertified. The robust plan's cornering takes `(6, 13)`, from which the fibre of 4
  at tick 1 is certified within 1 and captured at tick 2, the truth-only least. The expected order
  (fewest members uncaptured within `m`, then the tick sum) takes `(5, 13)`; at tick 1 it releases
  `W = 12` over a fibre of 4 and keeps it exactly, capturing at 13. On 20261212 and 20261252 both
  machines certify at tick 0 (bounds 12 and 12, then 10 and 11) and the expected order spends one
  tick more.
  **The failed gate, by its measurement**: at an uncertified tick the expected order loses 11 ticks
  on one seed of 63, more than its net gain on the others.
- **Every released bound kept**: 581 of 581 and 582 of 582, no pledge broken. The pledged plan's
  release is a promise it keeps by construction and kept on every tick here.
- **F6's action acceptance as written**, its capture bullet (strictly fewer ticks than both
  controls in sum and strictly fewer than both on more than half of the seeds): on this population
  it is not passed for the robust machine (28 of 63) and passed for the candidate (32 of 63). On the
  pinned acceptance seeds it failed (7 of 16), and that failure stands as written. The switches are
  not built, so F6's action acceptance as a whole is not passed.
- **The conditional reading** (not the acceptance): 33 of the 63 seeds admit a win beyond both
  controls; there the robust machine wins 28, ties 2 and loses 3 against both at once (regret 23),
  and the candidate wins 32, ties 1 and loses 0 (regret 14).
- Gates: `cargo check --workspace --all-targets`; `cargo test -p holonics --lib`, 876 passed.

### F6: the switches and their attribution (September 28)

Record: no dedicated record; THE_REBUILD F6 (the switches, the deposition law, the action
acceptance's third bullet) and the record of September 27, §9, §12 items 7 and 10, §13 and §14.5.
Campaign 4, #27, #63.

```sh
cargo run --release -p holonics --example hnn_chase -- switches probe 1 16   # the projection, choosing seeds
cargo run --release -p holonics --example hnn_chase -- switches              # the pinned run, once
cargo test -p holonics --lib holarchy::terrain::sensing_tests
```

The computational object is the helical pair interaction: the runner and the chaser as a pair, and
the three observation channels as pair contacts between the observed frame and the runner, whose
loop closure locates a defect. This loop touches the **pair** (each channel's contact and its slip,
a quarter-turn), the **cell holonomy** (the syndrome is each circuit's holonomy, expected to be the
identity) and **faces and placement** (the channels' readings of the runner's cell in their own
frames); the helix (the fault's switch clock), the tube (the lag's withheld span) and the tower
thread stay attached.

**The switches** ([definition; agent-inferred]; `holarchy::terrain::sensing`), declared families
whose truth the terrain returns (the `Switching` pattern):
- each of three time-aligned channels reads the runner's cell at tick `τ` as its kind (move, slip,
  wall), the line of sight `x_R(τ) − x_C(τ)` and the heading `v_R(τ + 1)`, in its own frame; a
  reading names its cell exactly (`Reading::cell`, refused unless the cell's own reading returns);
- **the lag** `d`: the readings of `τ` arrive once `τ + d` has moved, and the controls read the
  runner's motion at `t − d`, the motion the channels agree on (they need no attribution, so the
  faulty frame costs them nothing: the comparison is conservative against the machine);
- **the faulty sensor**: one channel (uniform on three) reports a rotated heading, its frame turned by
  `i^a` (`a` uniform on the three nonidentity quarter-turns, the unit group of `ℤ[i]`), on the odd
  aeons of a switch clock drawn from a declared `AeonFamily` (`SwitchTruth::drawn`, the aeons the
  epochs of the tick clock at the fault's section). Its draw continues the chase's own
  (`Chase::draw_key`), so a seed names the same runner, arena and openings with the switches off.
  [agent-inferred] The frame, not the velocity alone, is turned: a turn of a zero velocity is zero, a
  cornered runner stands for ticks at a time, and a fault that makes no error cannot be located; the
  line of sight is never zero before capture, so a turned frame errs at every active tick.

**The separation condition, checked on the circuit matrix** ([proved-derived]; `ChannelMenu`). With
`y_k = i^(e_k) x`, `e ∈ (ℤ/4)³`, the circuits `(0, 1)`, `(0, 2)`, `(1, 2)` give
`C = [[1, −1, 0], [1, 0, −1], [0, 1, −1]]` and `s = C e`. A defect on at most `k` channels is located
uniquely exactly when no nonzero `v` of support at most `2k` has `C v = 0`. `ker C = {(c, c, c)}` (the
common mode, `im d₀` of three parallel edges), of support `3`: at `k = 1` the 36 nonzero vectors of
support at most 2 all lie outside it, and each of the nine one-channel defects is located with its
turn. At `k = 2` `(1, 1, 1)` breaks it; two channels at `k = 1` are broken by `(1, 1)` (a fault
detected, located nowhere). The lag is `(d, d, d) ∈ ker C` in the time chart: no channel circuit sees
it.

**The attribution at its consumer** ([definition; proved-derived; agent-inferred];
`receiver::population::chaser`, "The attribution", and "The lag"). A reading of `τ` meets three loops:
- the **channel loop**: the menu's syndrome names the turned channel and its turn; **its locus is the
  channel** (`MachineReceipt::located`), and the constitution reads a cleared channel's reading;
- the **mover's loop**: the named cell against the contemporary fibre's own cells at `τ`, against the
  motor record at `τ`; **its locus is the runner's constitution**, the only deposit (`ChaseFamily`
  reads the port at its own tick);
- the **lag's loop**: the action-time prediction of `τ` (made `d` readings short) against the
  contemporary one; `q − p_act = (q − p_con) + (p_con − p_act)`, and deposition consumes `q − p_con`
  alone: **its locus is none** (`MachineReceipt::lag_misses` counts the misses the lag caused).
- Under the lag the machine reads the constitution's fibre projected through the withheld ticks
  against its own port, a member the chaser would have captured on the way dropped (the passage goes
  on), and the capture basin reads the lagged information structure (`pursuit::Pending`): the class it
  learns next is named by the cell of `t − d`, each member at its own motion. At `d = 0` it is the
  unlagged recursion value for value: `action trace` and the reception phase agree line for line with
  the previous commit's (354 and 414 lines, wall times masked).

**Pinned before the run** (this commit; `hnn_chase.rs`'s `SWITCH_SEED`, `SWITCH_SEEDS`,
`SWITCH_LAG`, `FAULT_AEONS` and `switches`):
- **the population**: seeds `20261301 + s`, `s < 64`, a declared contiguous range disjoint from every
  range read so far (acceptance `20260927 + s` and choosing `20261001 + s`, `s < 16`; the spent fresh
  populations `20261101 + s` and `20261201 + s`, `s < 64`), none read before this pin;
- **the switches**: the lag `d = 1`, the least lag that withholds a reading (fixed by that reason
  before any probe); the faulty sensor's aeons uniform on `1..=4` ticks (the machine captures within
  13 ticks on every choosing seed, so a passage sees its first active aeon within four ticks);
- **the chasers**: the machine under `MachineChaser::new`'s plan (robust, `n = 2, m = 12, d = 0`),
  pure pursuit and constant bearing, each with the switches off and on, from the reception's draw
  under the same traction bound; an uncaptured passage counts its cap `2^9`;
- **the criteria, the switch bullet as written**: with the switches on, (1) the machine's capture
  ticks strictly fewer than each control's in sum, and strictly fewer than both at once on more than
  half of the chased seeds; (2) the fault located on exactly the aeons it is active, over the
  readings received: every active aeon located, no inactive one, every location naming the truth's
  channel and turn; (3) lag-caused errors deposit nothing: the switched machine's constitution equals
  the prompt reception's on the true cells at every decision and exactly at the end, on every chased
  seed. A draw the terrain refuses is printed and enters no sum, and "more than half" counts the
  chased seeds;
- **printed beside them, not criteria**: the capture ticks with the switches off on the same seeds,
  the truth-only least, the per-tick location, the misses and those the lag caused, the deposits, and
  the released bounds kept.
- **The projection** (`switches probe 1 16`, the choosing seeds, a development reading): 45,374 ms at a
  292,932 kB peak for 16 seeds with both switch settings, so the run projects at about three minutes
  and under 1 GB, against ten minutes. The probe's own reading there, not a criterion: the machine 157
  capture ticks with the switches on (150 off), pure pursuit 4,734 (4,668), constant bearing 822
  (240); won against both at once on 9 of 16 (3 off); the fault located on 25 of 25 active aeons and
  60 of 60 active ticks, none else; the constitution equal to the prompt one on 16 of 16; 146 of 146
  released bounds kept.

**The run** (once, on the pin at commit `95a8864a`: `switches`, 162,402 ms at a 269,180 kB peak,
within its projection). The terrain refuses 1 of the 64 draws (20261325 opens within capture), so 63
seeds are chased.

| Over the 63 chased seeds | The machine | Pure pursuit | Constant bearing |
|---|---|---|---|
| Capture ticks in sum, **switches on** | **646** | 19,255 | 4,713 |
| Capture ticks in sum, switches off | 611 | 17,034 | 1,949 |
| The machine against both at once, win/tie/loss, switches on | 38/18/7 | | |
| The machine against both at once, win/tie/loss, switches off | 36/25/2 | | |

The truth-only least sums 587 (the machine's regret 59 with the switches on, 24 off). Pure pursuit
leaves 36 passages uncaptured by `2^9` with the switches on (32 off), each counting its cap.

- **Criterion 1, capture still beats both controls: passed.** 646 < 19,255 and 646 < 4,713, and the
  machine takes strictly fewer ticks than both at once on 38 of the 63 chased seeds (more than half
  is 32). It loses on 7: 20261314 (8 against pursuit's 6), 20261327 (14 against bearing's 13),
  20261330 (4 against 1 and 1; 3 with the switches off, the least 1), 20261333 (10 against bearing's
  7), 20261338 (11 against 10), 20261349 (7 against 6) and 20261361 (8 against pursuit's 6). The
  switches cost the machine 36 ticks over 22 seeds (at most 6, on 20261360) and save it 1 on
  20261344, 35 net; the cost is the lag's, since at lag zero the located fault leaves every passage
  unchanged (the probe at `d = 0` and `sensing_tests`). They cost constant bearing 2,764 and pure
  pursuit 2,221.
- **Criterion 2, the fault located on exactly its active aeons: passed.** Over the 583 readings
  received, 250 aeons are read, 111 of them active: all 111 are located, no inactive aeon is, and
  every location names the truth's channel and turn. Per tick: located exactly on 264 of the 264
  active ticks, none wrong, none unlocated, no false alarm.
- **Criterion 3, lag-caused errors deposit nothing: passed.** The switched machine's constitution
  equals the prompt reception's on the true cells at every decision and exactly at the end, on 63 of
  63 seeds. Of its 126 action-time misses, 48 are the lag's (the contemporary constitution predicted
  the reading); they reach no locus. 178 readings deposit in the runner's constitution (a member of
  the contemporary fibre emitted another cell).
- **The lagged basin keeps its certificates**: 589 of 589 released bounds kept under `d = 1`, no pledge
  broken.
- **F6's switch bullet, as written, passes on this population.** F6's action acceptance as a whole
  still reads its first bullet on the pinned acceptance seeds, where it fails (7 of 16 won against
  both controls at once, `action trace`, unchanged); that failure stands as written, so the action
  acceptance is not passed. With the switches off, this population reads the capture bullet as
  passing too (611 against 17,034 and 1,949; 36 of 63), beside the second fresh population's 28 of 63
  for the robust plan.
- Gates: `cargo check --workspace --all-targets`; `cargo test -p holonics --lib`, 886 passed.
- **Owed in Lean** (#62): the localization condition (a defect on at most `k` edges of a circuit menu
  is located uniquely iff `ker C` holds no nonzero vector of support at most `2k`) with the complete
  three-channel menu over `ℤ/4` as its instance; the lagged capture basin is the Pre recursion of the
  lagged information structure (and equals the unlagged one at `d = 0`); the attribution's split
  `q − p_act = (q − p_con) + (p_con − p_act)` with deposition consuming `q − p_con` alone.

### Residual-founded transport discovery on the moiré (September 28)

`hnn_population.rs`'s `birth`, `birth-probe` and `birth-dimensions` modes
(`hnn_population_birth.rs`, whose header states the pins) run
`holonics::receiver::population::birth` (Lean `Compression/Landmark/Context/Birth`); the pins and
the verdict are in [the record](../../records/2026-09-28_RESIDUAL_FOUNDED_TRANSPORT_DISCOVERY_PINNED_BEFORE_ITS_SEEDS_ARE_READ.md).

```sh
cargo run --release -p holonics --example hnn_population -- birth-probe
cargo run --release -p holonics --example hnn_population -- birth
cargo run --release -p holonics --example hnn_population -- birth-dimensions
```

- **The probe** (no pinned seed): the founding on rates `1/8, 1/7, 1/5` (`d = 280`) in 73 ms,
  dimension 141 after 139 strict steps; both populations over `2^12` cells in 122 and 451 ms; peak
  resident 42,900 KiB.
- **The pinned run** (commit `4a452884`; eight seeds, `2^14` cells each): 10,882 ms, peak resident
  53,744 KiB. The acceptance fails as pinned. Six seeds found nothing: on four the declared two-ring
  parity gratings survive (`13 + 10/16 + ε` bits the passage), on two the trees read periods 28 and
  7 inside the opening section. On 2026092883 and 2026092887 (one orbit each) the founding at cell
  512 closes to the Hankel rank exactly (106 and 141, in 104 and 139 strict steps), the newborn
  codes the rest at the truth exactly (`7 + 11/16 + ε` and `8 + 2/16 + ε`), and the population with
  the birth less the control reads `−465 + 4/16 + ε` and `−682 + 5/16 + ε`; the margin bound is
  attained within `3/2^97` bits, undecided.
- **The diagnostic** (after the run, never an acceptance): the founded dimension equals the Hankel
  rank on six seeds and exceeds it by one on 2026092881 and 2026092884, each the one founded form
  silent on the visited orbit, a conserved charge (`T*v = v`); the restriction to the visited orbit
  has the Hankel rank on all eight.
- Gates: `cargo check --workspace --all-targets`; `cargo test -p holonics --lib`; `bash
  tools/lean_check.sh Holonics HolonicsResearch`.

### The ring-search experiment (September 28)

Record: [the rings as a search for keys](../../records/2026-09-28_THE_RINGS_AS_A_SEARCH_FOR_KEYS_PINNED_BEFORE_THE_RUN.md)
(its pin, the run and what it located). #28, #73, #63.

```sh
cargo run --release -p holonics --example hnn_ring_search -- bank        # the declaration
cargo run --release -p holonics --example hnn_ring_search -- preflight   # development seeds only
cargo run --release -p holonics --example hnn_ring_search -- run         # the pinned run, once
```

The computational object is the helical pair interaction: the rings as complex parametrons whose
ports are joined by their contacts (neighbours and half-turn partners), carried by their rotors at
their rates, locking onto sheets past the pump's bifurcation. This loop touches the **helix** (each
ring's rotor winding with carry, the phase-carried moment), the **pair** (the contacts' coupling and,
on the crib, the Bombe's wires joined by the menu's stages) and the **cell holonomy** (the Bombe's
loop closure, and the crib's revisited joint state); faces and placement, the tube and the tower
thread stay attached.

Pinned at `c2f577f1`, run once (6,887 ms, peak resident 174,500 kB, 24 cores); every passage's
balance closed (672 moiré, 78 crib, 91 prior), and every certified key was future-equivalent to the
truth. The work to a certified key, summed over 8 fresh seeds a terrain (a moiré bank with its
declaration, 3,795,456):

| Terrain | Bank | Nonlocking control | Enumeration | Menu propagation |
|---|---|---|---|---|
| Blind moiré | 7 of 8 certified: none | 7 of 8: none | 25,566 | not declared |
| Parity moiré | 6 of 8: none | 7 of 8: none | 53,017,545 | not declared |
| Rotor crib | 1,512,813,925 | 1,512,813,925 | 460,880 | 268,218 |

(1) fails on all three terrains. (2) fails: the undriven bank lands on a plural lock in all but
`[596/2^24, 597/2^24)` of its `2^122` configurations, and its single-rate basins do not follow
`2^(−ℓ)` (114 ordering violations). The rings are recorded as not a search.
