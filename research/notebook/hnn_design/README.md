# HNN design measurements

[definition] The exterior harnesses behind the HNN's measured receipts: exact Python scripts and
cargo examples that run the crate's host reference and owners. This page is a route to what
remains. The [index](#index) names each kept harness, what it measures, its command and its record;
[the baseline replay](#the-baseline-replay) is the behavioural check every retirement batch reruns;
[the retired harnesses](#the-retired-harnesses) are named with the commit that holds each and the
section of this page, at that commit, that holds its receipts; the kept harnesses'
[receipts](#receipts) follow. A harness's declarations are in its own header (the Rust `//!` header
or the Python docstring). Commands run from the repository root.

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
kernel's status for the harnesses' memory receipts) and the exact presentation of readings. The
examples include it by `#[path]`.

## Index

Each kept harness with what it measures, its command and its record. A Rust harness is a cargo
example of `holonics` (`hnn_exposure` also of `holonics-cuda`); its header states its declarations
and every mode. A Python script needs only the standard library unless its docstring says otherwise.

| Harness | What it measures | Command | Record |
|---|---|---|---|
| `hnn_prediction.rs` (with `hnn_executed_loop.rs`) | **Step 1's harness** (THE_REBUILD U6): `hnn::executed` on the known-truth terrains (order-2, the alternation, the line) at `E` alone. `executed move`: one committed move of `E` on the release's own comparison, printed whole; `executed train`: an arm's certified training from the declared or founded opening, its `E` written; `executed evaluate`: every constitution's release from the open section, its counts and every section; `executed spread` and `executed slopes`: diagnostics at the open section. The modes before the executed comparison (`copy`, `moire`, `text`, `probe`, `develop`, `pumped below\|past`, native generation of September 29) remain until batch N2 strips them | `cargo run --release -p holonics --example hnn_prediction -- executed evaluate <terrain> <seed> <count> <out> <label[=E]>…` | [the baseline](../../records/2026-09-30_THE_BASELINE_BEFORE_THE_SEPTEMBER_30_RETIREMENTS.md), [the modulus founded off one](../../records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_MEASURED_THE_MODULUS_STAYS_BELOW_ONE_AND_ORDER_TWO_TRAINING_LEARNS_THE_LAG_ONE_COPY.md), [the station-framed placement](../../records/2026-09-30_THE_STATION_FRAMED_PLACEMENT_MEASURED_THE_REFIT_READS_BOTH_CHAINS_AND_THE_CERTIFIED_MOVE_KEEPS_THE_MODULUS_AT_ONE.md), [the executed comparison](../../records/2026-09-30_THE_EXECUTED_COMPARISON_JOINED_A_CERTIFIED_MOVE_DESCENDS_IT_AND_ORDER_TWO_LEARNS_ONLY_THE_TERMINATION.md), [native generation](../../records/2026-09-29_NATIVE_GENERATION_THE_MOIRE_CONTINUES_EXACTLY_THE_COPY_IS_NEAR_AND_TEXT_IS_ILLEGIBLE.md) |
| `replay_baseline.sh` | The minimal replay: `executed evaluate` on development seed 41, 8 requests, over the lossless and founded openings, the trained order-2 constitution and the station-framed refit, diffed byte for byte against the committed reference, the wall time and the resident set masked | `bash research/notebook/hnn_design/replay_baseline.sh` | [the baseline](../../records/2026-09-30_THE_BASELINE_BEFORE_THE_SEPTEMBER_30_RETIREMENTS.md) §5 |
| `bank_causes_probe/eF_confirmation_counts.py`, `bank_causes_probe/eM_section_shapes.py` | Exact counts of an `executed evaluate` listing, per constitution: released and held, whole sections, the first lock at station 0 or 1 and its stations; the released sections' shapes (the classes, adjacent stations equal, the terrain's rule among a section's own stations) | `python3 research/notebook/hnn_design/bank_causes_probe/eM_section_shapes.py <listing> <order2\|alternation\|line>` | [the station-framed placement](../../records/2026-09-30_THE_STATION_FRAMED_PLACEMENT_MEASURED_THE_REFIT_READS_BOTH_CHAINS_AND_THE_CERTIFIED_MOVE_KEEPS_THE_MODULUS_AT_ONE.md), [the modulus founded off one](../../records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_MEASURED_THE_MODULUS_STAYS_BELOW_ONE_AND_ORDER_TWO_TRAINING_LEARNS_THE_LAG_ONE_COPY.md) §3 |
| `hnn_exposure.rs` | Campaign 1's exposure on a cut: the model face (the receiver's population over the landmark tree and the combined face), the baselines, keys, aeons and the first law; on the host or the card (`realization card`); the loaded resonator (`resonator source`); F2's adoption gate (`gate f2`: the population with and without the field on the held-out cells, work, memory and budgets) | `cargo run --release -p holonics --example hnn_exposure -- cut-file .local/cuts/standing-real-cut-campaign-1.bin cells all` | [campaign 1 meets its criterion](../../records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md), [the resonator](../../records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md), [campaign 2](../../records/2026-09-26_CAMPAIGN_TWO_THE_RINGS_AND_CONTACTS_ARE_LAWFUL_AND_ADD_NO_BITS_ON_TEXT.md), [F2's adoption gate](../../../docs/plans/THE_REBUILD.md#f2-the-field-as-a-family-step-4-73) |
| `hnn_chase.rs` | F6's chase terrain: the reception phase, the action phase's choosing sweep (`choose`) and its acceptance (`action`, with U4's move reading and U3's release reading); U4's next loop: the failure's diagnosis (`diagnose`) and the fresh population (`fresh`); F6's switches and their attribution (`switches`) | `cargo run --release -p holonics --example hnn_chase` | [the learner must move](../../records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md) (no dedicated record; the receipts below) |
| `exterior.rs` | The shared exterior boundary the examples include | | |
| `standing_cut.py` | Pins the standing real cut (`6148`) and the wide cut (`wide 1048576`) | `python3 research/notebook/hnn_design/standing_cut.py 6148` | [campaign 1 meets its criterion](../../records/2026-09-26_CAMPAIGN_ONE_MEETS_ITS_CRITERION_THE_TREE_RECEIVES_AND_THE_WAVE_IS_WEIGHED.md), [at scale](../../records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) |
| `curated_source.py`, `curated_incidence.py` | The curated source, its pinned cut and flat twin; the admitted relations on the cut | `HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/curated_source.py 1048576` | [the receiving population](../../records/2026-09-27_THE_RECEIVING_POPULATION_WAS_BUILT_ON_TERRAIN_WITH_KNOWN_TRUTH_AND_THE_CURATED_SOURCE_NOW_CODES_BELOW_THE_FLAT_STREAM.md) |
| `development_families.py`, `family_passage.py` | The split by conversation with the development reserve (U6), the spent family splits (F-items, U2) behind `--read-reserve`, and their joined passages | `HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/development_families.py [U6]` | [F4](../../records/2026-09-27_F4_DEVELOPMENT_FAMILY_SPLIT_AND_RELEASE_GATE.md), [U2's acceptance run](../../records/2026-09-28_U2_F0S_MEMORY_ACCEPTANCE_RUN_PINNED_BEFORE_ITS_SPLIT_IS_READ.md) |
| `f5_context.py` (tests: `f5_context_tests.py`) | F5's request context from declared provider-parent incidence (an exterior source codec) | `python3 research/notebook/hnn_design/f5_context_tests.py` | [F5](../../records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md) |
| `athena_protocol.py`, `athena_file_protocol.py`, `athena_file_checkpoint.py`, `athena_blind.py` (tests: `athena_*_tests.py`) | Athena-0's exterior protocol, checkpoint transport and blind judging surface | `python3 research/notebook/hnn_design/athena_protocol_tests.py` | [F5](../../records/2026-09-27_F5_DEVELOPMENT_AND_BLIND_GATE.md), [the atomic standing audit](../../records/2026-09-27_F5_ATOMIC_STANDING_OWNER_AUDIT.md) |
| `field.py`, `power.py`, `swing_power.py`, `capacity.py` | The step 4 design review's kept scripts: the revised tick's exact reference, its power balance, one exponent per ring against one per contact, and the capacity `n*` by counting | `python3 research/notebook/hnn_design/power.py` | the step 4 design ("The step 4 design scripts" below) |

## The baseline replay

[measured] THE_REBUILD U6's order, item C.1, fixes the baseline before the September 30
retirements at commit `d4596102`
([record](../../records/2026-09-30_THE_BASELINE_BEFORE_THE_SEPTEMBER_30_RETIREMENTS.md)). Every
retirement batch runs, after its change:

```sh
bash research/notebook/hnn_design/replay_baseline.sh
```

It builds `hnn_prediction`, runs `executed evaluate order2 41 8` over the lossless opening, the
founded opening, the trained order-2 constitution
(`2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_receipts/E_trained_order2.txt`) and the station-framed
refit on the lattice (`…/refit_on_lattice.txt`), and diffs the listing (the harness's stdout, then its
section listing) against
[`replay_reference.txt`](../../records/2026-09-30_THE_BASELINE_receipts/replay_reference.txt). Only
the last line's wall milliseconds and resident-set bytes are masked. Exit 0 is a match, 1 a mismatch
(with the diff), 2 a read that reached its 600 s guard. At the baseline the read takes about
93,000 ms on 24 cores and reads 0, 0, 0 and 6 whole sections of 8.

## The retired harnesses

Each retired harness with the commit that holds its source and the sections of this page, at that
commit, that hold its receipts; its records hold the measurements. N1 is batch N1 of THE_REBUILD
U6's consolidation (September 30), which retired the harnesses step 1 does not run
([the baseline record](../../records/2026-09-30_THE_BASELINE_BEFORE_THE_SEPTEMBER_30_RETIREMENTS.md)
§6 lists every file with its permalink).

| Harness | What it measured | Retired | Source at | Receipts on this page at that commit |
|---|---|---|---|---|
| `bank_causes.rs` and `bank_causes_probe/` (all but the two listing counters) | The causes' analysis of the bank's learning path: dumps of the declared field's placement, exact bank readings and `E` after each certified deposit; `native-release` (Stage 0, the station-framed refit's native read), `reentry`; the float fits `eO_fit.py`, `eP_rho_path.py`, `eR_fit.py` and their export | N1 | [`d4596102`](https://github.com/brandonrdug/holonics/tree/d4596102/research/notebook/hnn_design) | none: the September 30 records and their receipts |
| `hnn_population.rs` with `hnn_population_{birth,census,curated,evolution,f0,u2,u6}.rs` | The egg population: terrain, evolution and species, the curated source with its merges and admitted receivers, F4, F5's native paths and checkpoints, F0's egg and acceptance run, U2's census and acceptance run, U6's symmetric comparison, residual-founded transport discovery | N1 | [`d4596102`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_population.rs) | [the egg population on terrain](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-egg-population-on-terrain-rebuild-step-4-item-4-september-27), [the evolved prior](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-evolved-prior-and-species-collapse-rebuild-step-4-item-7-september-27), [the curated source through the population](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-curated-source-through-the-population-campaign-5-september-27), [the admitted receivers](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-admitted-receivers-campaign-5-september-27), [merges](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#merges-learned-byte-classes-and-shared-counts-campaign-5-september-27), [with the learned classes](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-admitted-receivers-with-the-learned-classes-september-27), [F4](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#f4-release-and-the-disjoint-development-families-september-27), [F0's first diagnosis](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#f0-the-predictor-on-unseen-families-the-first-diagnosis-september-28), [U2's census](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#u2-the-standing-census-of-f0s-egg-september-28), [U2's acceptance run](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#u2-the-acceptance-run-of-f0s-memory-september-28), [F0's acceptance run](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#f0-the-acceptance-run-the-predictor-on-unseen-families-september-28), [U6 item 2](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#u6-item-2-the-symmetric-comparison-on-the-conversation-split-september-29), [residual-founded transport discovery](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#residual-founded-transport-discovery-on-the-moiré-september-28) |
| `hnn_landmark.rs` | The landmark tree, count-only: the depth sweep and the prequential passage; `letters`, `prior`, `wide`, `compact`, `capacity` | N1 | [`d4596102`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_landmark.rs) | [`hnn_landmark`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#hnn_landmark) |
| `hnn_parametron.rs` | The parametron re-derived: the Floquet certificate on pumped rings, and the receiving bank's reading of relative phase | N1 | [`d4596102`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_parametron.rs) | none: [its receipt](../../records/2026-09-29_THE_PARAMETRON_RE_DERIVED_THE_PUMP_READS_RELATIVE_PHASE_AND_THE_FLOQUET_CERTIFICATE_DECIDES_THE_LOCK.md) |
| `f1_dictionary.py`, `f1_validation_part.py`, `f2_capacity_probe.py`, `f4_retrospective.py`, `f5_retrospective.py`, `f5_dev_request.py`, `f5_request_bundle.py`, `f5_blind_input.py`, `athena_dev_gate.py`, `release_legibility.py` | The spent F1, F2, F4 and F5 splits' scripts (F2's probe cut also fed `hnn_exposure`'s `gate f2`), Athena-0's development gate, and the count-only readings of released text | N1 | [`d4596102`](https://github.com/brandonrdug/holonics/tree/d4596102/research/notebook/hnn_design) | [F1](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#f1-word-alphabet-pin-september-27), [F2's preflight](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#f2-field-family-preflight-september-27), [F4](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#f4-release-and-the-disjoint-development-families-september-27), [F5](#f5-development-only-release-and-product-protocol-september-27) (kept below) |
| `bits2.py`, `collapse_bezout.py`, `collapse_check.py`, `critical_cayley.py`, `deposit_bits.py`, `propagation.py`, `release.py`, `word_bits.py` | Step 4 design scripts; every number they reproduce is in the [construction record](../../records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md) | N1 | [`d4596102`](https://github.com/brandonrdug/holonics/tree/d4596102/research/notebook/hnn_design) | [the step 4 design scripts](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-step-4-design-scripts) |
| `hnn_lattice_growth.rs` | The deposited constitution's bits, the integral chart's equality, the path's openness | September 28 | [`2d34b819`](https://github.com/brandonrdug/holonics/blob/2d34b819/research/notebook/hnn_design/hnn_lattice_growth.rs) | [`hnn_lattice_growth`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#hnn_lattice_growth-retired-september-28-last-at-commit-2d34b819) |
| `hnn_diagnose.rs` | Campaign 1's located failure | September 28 | [`2d34b819`](https://github.com/brandonrdug/holonics/blob/2d34b819/research/notebook/hnn_design/hnn_diagnose.rs) | [`hnn_diagnose`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#hnn_diagnose-retired-september-28-last-at-commit-2d34b819) |
| `hnn_born.rs` | The Born receiver beside the tree | September 28 | [`2d34b819`](https://github.com/brandonrdug/holonics/blob/2d34b819/research/notebook/hnn_design/hnn_born.rs) | [`hnn_born`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#hnn_born-retired-september-28-last-at-commit-2d34b819) |
| `hnn_curated.rs` | The curated cut as typed letters against the flat tree | September 28 | [`2d34b819`](https://github.com/brandonrdug/holonics/blob/2d34b819/research/notebook/hnn_design/hnn_curated.rs) | [`hnn_curated`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#hnn_curated-retired-september-28-last-at-commit-2d34b819) |
| `hnn_terrain.rs` (with `hnn_terrain_arithmetic.rs`) | The landmark tree on terrain a declared Holarchy made; `arithmetic` | September 28 | [`2d34b819`](https://github.com/brandonrdug/holonics/blob/2d34b819/research/notebook/hnn_design/hnn_terrain.rs) | [terrain a declared Holarchy made](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#terrain-a-declared-holarchy-made-the-record-of-september-27-33-and-5), [the arithmetic terrain](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-arithmetic-terrain-the-record-of-september-27-on-the-faces-of-integers-7-and-9) |
| `hnn_release_terrain.rs` | The population's release checks on known-truth terrain | September 28 | [`2d34b819`](https://github.com/brandonrdug/holonics/blob/2d34b819/research/notebook/hnn_design/hnn_release_terrain.rs) | [the release checks](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#population-release-checks-on-known-truth-terrain-september-27-retired-september-28) |
| `hnn_word_probe.rs` | F1's exact byte-word work preflight | September 28 | [`2d34b819`](https://github.com/brandonrdug/holonics/blob/2d34b819/research/notebook/hnn_design/hnn_word_probe.rs) | [F1](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#f1-word-alphabet-pin-september-27) |
| `hnn_tokens.rs` | F0 candidate 3: learned tokens with the tree over them | September 28 | [`2d34b819`](https://github.com/brandonrdug/holonics/blob/2d34b819/research/notebook/hnn_design/hnn_tokens.rs) | [F0 candidate 3](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#f0-candidate-3-learned-tokens-with-the-receiving-tree-over-them-september-28) |
| `hnn_population_local.rs` (`hnn_population f0-local`) | F0 candidate 2: a family wins where it is closest | September 28 | [`2d34b819`](https://github.com/brandonrdug/holonics/blob/2d34b819/research/notebook/hnn_design/hnn_population_local.rs) | [F0 candidate 2](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#f0-candidate-2-a-family-wins-where-it-is-closest-september-28) |
| `hnn_ring_search.rs` | The rings as a search for keys | September 28 | [`10a837fd`](https://github.com/brandonrdug/holonics/blob/10a837fd/research/notebook/hnn_design/hnn_ring_search.rs) | [the ring-search experiment](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-ring-search-experiment-september-28) |
| `hnn_population`'s `composition` and `arithmetic` modes (`hnn_population_{composition,arithmetic}.rs`) | Eggs composed at ports: the arithmetic eggs (catered machinery) | September 29 | [`1b374d46`](https://github.com/brandonrdug/holonics/blob/1b374d46/research/notebook/hnn_design/hnn_population_arithmetic.rs) | [eggs composed at ports](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#eggs-composed-at-ports-the-arithmetic-eggs-rebuild-step-4-item-6-september-27) |
| the curated source's own navigators | Measured and retired | September 27 (commit `38b0b81c`, reverted) | [`38b0b81c`](https://github.com/brandonrdug/holonics/commit/38b0b81c) | [the curated source's own navigators](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-curated-sources-own-navigators-measured-and-retired-commit-38b0b81c-reverted) |

## Receipts

The kept harnesses' receipts, per harness and then by date, each pointing to its record.

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
`2^20` is the largest power of two within the memory cap (`hnn_landmark -- … wide`, stage 0;
`hnn_landmark` retired September 30, at `d4596102`).

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
  receivers", on this page at
  [`d4596102`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-admitted-receivers-campaign-5-september-27)).

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

**Through the population** (`hnn_population.rs curated`, retired September 30; the dated section "[The curated source through the population](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-curated-source-through-the-population-campaign-5-september-27)" of this page at `d4596102`): The curated cut through the egg population (campaign 5): the curated cell tree and the typed tree (the channel read once at the section) as families, and the boundary egg (the part clock ⊳ the typed tree and the letter tree through the hazard law on a partition learned by priced merges on the development cells, the declared partition and the refused stage read on the same cells), one passage over the whole cut against the flat tree at `D = 48`; `merges` runs the learning alone; development receipts, counts and bits only Receipts: The boundary egg selected (`−log₂ w = 0 + 0/16 + ε`); learned classes 167 values → 4 (declared 6), shares refused (`7/16` above); the whole curated stream charged against the flat stream: development `−1072 + 15/16 + ε` (declared `−950 + 9/16`), held out `−369 + 8/16 + ε` (declared `−415 + 3/16`)

### The step 4 design scripts

Record: the step 4 design (THE_REBUILD) and #62; no dedicated record.

[established-bounded; measured] The exact-arithmetic scripts behind measured numbers in the
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
exactly what the earlier scripts drew. `power.py` imports it, and `swing_power.py` and `capacity.py`
its exact printing. `swing_power.py` answered the second review (R2); `power.py`'s contrast-port cases
and the counting `capacity.py` answered the third (R3). `capacity.py` takes about 6 min (375,000 ms
in the last run); the other two take seconds.

These three stay because the construction record holds their readings only in part (the
[baseline record](../../records/2026-09-30_THE_BASELINE_BEFORE_THE_SEPTEMBER_30_RETIREMENTS.md) §6
says which). The other eight (`bits2.py`, `collapse_bezout.py`, `collapse_check.py`,
`critical_cayley.py`, `deposit_bits.py`, `propagation.py`, `release.py`, `word_bits.py`) were retired
on September 30 with every number they reproduce in the construction record; they and their rows
of this table are at [`d4596102`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md#the-step-4-design-scripts).

| Script | What it measures | The design's number it reproduces |
|---|---|---|
| `power.py` | The global power `P` over 8 ticks on six rings of widths 4, 2, 4, 6, 2, 4: the six-cycle plus a chord | Lossless: `P` is constant exactly. Dissipative: `P(t) − P(t+1)` equals the dissipation exactly at every tick. With the contrast port `W_c ≠ 0`: `P(t+1) − P(t) = Π_c` exactly; with dissipation, passive `W_s` and `W_c` together, `P(t+1) − P(t) = −dissipation + (W_s term ≤ 0) + Π_c` exactly at every tick, and `Π_c` takes both signs over 8 starting states. With `W_c` 8 times larger the balance stays exact and `P` grows in 8 ticks by `P(8)/P(0) = 244 + e`, `e in [2626/3871, 251/370]` (an exact ratio of 7,580 bits) |
| `swing_power.py` | Junction scattering's power with one exponent per ring against one per contact | Per ring (not conserved): `73199/1920` (38 rem 239 over 1920) at tick 0, `50 + e`, `e in [3683/3851, 285/298]` at tick 5, `43 + e`, `e in [1577/3270, 1074/2227]` at tick 6. Per contact: `648509/23040` (28 rem 3389 over 23040) at every tick |
| `capacity.py` | The capacity `n*` by counting: the least `n` with `N(n) < \|A\|^n`, certified by exact integers at `n* − 1` and `n*`; the moment's dense code as a reading | `n* = 137` on three rings of periods 3, 4, 5 over `\|A\| = 2`; 6,148 cells on campaign 1's declared field; 8,577 for one byte ring of period 7 with `Δ = {1}`; 3,641,698 for eight source rings of period 16 (8,421,376 slots). The dense code: 135 bits at `n = 128` and 138 at 144 on the control; about 117,000 cells for the period-7 ring; for the eight rings, with uniform counts, below the source for good from 4,243,457 cells (the dense code over the source bits `9472/9375` (1 rem 97 over 9375) at `n = 4,200,000`, `132608/134375` at `n = 4,300,000`) |

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

### F2 adoption gate on the receiving population (September 28)

Record: [THE_REBUILD F2](../../../docs/plans/THE_REBUILD.md#f2-the-field-as-a-family-step-4-73)
(the pins and the receipt).

```sh
cargo run --release -p holonics-cuda --example hnn_exposure -- cut-file .local/cuts/f2v2-gate-probe.bin cells all realization card gate f2
```

The run used a fresh split (`F2V2`, 18,068 choosing and 4,381 validation families) and the
6,148-cell probe at `n*` (written by `f2_capacity_probe.py F2V2`, retired September 30, at
`d4596102`) (4,096 choosing and 2,052 validation byte cells). It ran once on the
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

Retired September 30 (at `d4596102`): the native paths below (`hnn_population f5-native`,
`f5-family`, `f5-family-verify`, `f5-bundle`, `f5-checkpoint-census`, `f5-checkpoint-restore`) and
the split scripts (`f5_retrospective.py`, `f5_dev_request.py`, `f5_request_bundle.py`,
`f5_blind_input.py`, `athena_dev_gate.py`). The protocol fixtures, `f5_context.py` and
`athena_blind.py` remain.

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

### U6: the data protocol, by conversation, with a reserve nothing reads (September 29)

Record: [the text chart, audited](../../records/2026-09-29_THE_TEXT_CHART_AUDITED_ONE_PREDICTOR_SEEN_CONVERSATIONS_AND_NO_ARITHMETIC.md),
§4 item 1; plan: THE_REBUILD U6. Refs #73 #148 #63.

The split's unit is the conversation (the aeon), and the reserve is named before any role is read.
Count-only, on the development partition's metadata (keys, sessions, ports and links; no text):

```sh
HOLONICS_ROOT=$PWD python3 research/notebook/hnn_design/development_families.py U6
```

- **The roles** (86 units: 87 conversations, one relation joining two): choosing 61 conversations
  (60 units) and 16,314 messages; validation 11 conversations and 682 messages; the reserve 15
  conversations and 5,453 messages. The validation role drew 11 of 71 units at one in five, and
  small ones.
- **The checks**: conversations with messages in two roles 0; `comparison-request` 16,698 within a
  role, 0 across, 3,555 outside the partition; `later-human-after-agent` 1,374, 0, 757;
  `provider-parent` 3, 0, 6,782.
- **The reserve**: `RESERVE_SIZE = 15` (the least `k` whose mean over `k` of 87 conversations reads
  no less sharply than validation's at one in five of the rest, `72·71 = 5112 ≤ 4·1290 = 5160`),
  named `09d7ae5b86d1b34cd1f57a100fb0ec412f59902f6ec3b90924a7c80b136f8a24`, committed in
  `development_families.py` and `exterior.rs`. The membership is
  `19f8b42d46e1ea96dbcaa2f8e83029ab9c9b92a5dd7cee9b138244d8207a6e75`. The reserve's conversations
  were read by every earlier split (F0's choosing role held all 87): it is unread from its naming
  on.
- **The present retention law on the incidence** (by message; choosing and validation only): of the
  choosing role's requests, 12,254 are held at rank class 0 (their run's latest message), 7 released
  and 2,207 reach no earlier development part with cells; of its human returns 1,105 are held at rank
  class 0 and 1 reaches another conversation (the joined pair); in validation every request and
  return that reaches an earlier part with cells, 462 and 53, is held at rank class 0. The reserve's
  messages are not read, not even for their ports.
- **The guard**: every script that reads the source, a cut or a receipt refuses the reserve's
  material unless `--read-reserve` is passed, logged to `.local/cuts/reserve-reads.log`; no run
  passed it. Every artifact written before the reserve was named is refused (the spent F4, F1, F2,
  F2V2, F5, U2 and F0 splits are reshuffles of read material).
- **Checked on a synthetic source** (24 made-up conversations, no private data): the scripts emit the
  roles, their incidence, the joined passage and its aeons end to end, and `hnn_population f0-acceptance` (retired September 30, at `d4596102`) read it
  with 126 conversation changes entered; without `--read-reserve` the harness refuses the synthetic
  cut, which does not name the committed reserve.

The roles' streams (`curated_source.py 524288 <role>`, `curated_incidence.py <role>`,
`family_passage.py`) are generated by the loop that measures them, after its pins.

### U6: native generation, a section refined and released whole (September 29)

Records: [the pins](../../records/2026-09-29_NATIVE_GENERATION_PINNED_BEFORE_ITS_RUNS.md) (committed
at `70a572e7` before any run) and [the receipt](../../records/2026-09-29_NATIVE_GENERATION_THE_MOIRE_CONTINUES_EXACTLY_THE_COPY_IS_NEAR_AND_TEXT_IS_ILLEGIBLE.md);
plan: THE_REBUILD U6. Refs #73 #148 #63.

```sh
cargo run --release -p holonics --example hnn_prediction -- copy
cargo run --release -p holonics --example hnn_prediction -- moire
cargo run --release -p holonics --example hnn_prediction -- text .local/cuts/curated-u6-passage-cut.bin .local/cuts/u6-native-sections.txt
```

`hnn_prediction.rs` declares three rings of 32 in a chain with no pair offset, campaign 1's
constitution and steps, `K = 2` continuing words of one tick, and a batch of 16 refinements a
deposit. The computational object is the helical pair interaction: the section is a span of the
receiving ring's helix (**the helix**), the refinement is **the tube**, the joint readout is **faces
and placement**, and the contacts' transit carries **the pair**; the cell holonomy and the tower
thread stay attached through the field's complex and carry chain.

- **The checks** hold on all 2,818 refinements: every balance, every exact pairing on the executed
  charts, every commit's deposition work, and every locus outside a refinement's diamond unchanged.
- **Known truth.** The moiré (two gratings, least period 6): all 6 windows continue exactly after 512
  windows. The copy (8 of 4 symbols): 234 of 256 fresh requests echoed exactly, 2,026 of 2,048
  stations, after 1,536 requests; the pin asked for 256.
- **Text.** Two passes over the passage's 385 choosing pairs; the 8 validation requests (F0's rule)
  gave 7 sections of 32 bytes and one typed refusal, strings of `e`, `o`, `r` and spaces: illegible.
  The text is owner-only.
- **Cost.** 447,718, 142,464 and 389,739 ms; peak resident sets 401,580,032, 381,526,016 and
  819,576,832 bytes.

### U6: the passage's own transports, the founded port chart (September 29)

Records: [the pin](../../records/2026-09-29_THE_PASSAGES_OWN_TRANSPORTS_PINNED_BEFORE_ITS_RUNS.md)
(`962d038e`) and [the receipt](../../records/2026-09-29_THE_PASSAGES_OWN_TRANSPORTS_THE_MOIRE_FOUNDS_ITS_RANKS_WITH_NO_TRANSPORT_DECLARED_AND_TEXT_CODES_BELOW_THE_CELL_CHART.md);
plan: THE_REBUILD U6. Refs #73 #148 #63.

```sh
cargo run --release -p holonics --example hnn_exposure -- cut-file .local/cuts/u6-encoding-probe.bin cells all ports passage expansions <owner-only file>
cargo run --release -p holonics --example hnn_exposure -- found-only yes            # the founding alone, on the public control
cargo run --release -p holonics --example hnn_prediction -- text .local/cuts/curated-u6-passage-cut.bin <owner-only file> founding .local/cuts/u6-encoding-probe.bin [train <pairs>] [passes <n>]
cargo run --release -p holonics --example hnn_prediction -- develop text .local/cuts/curated-u6-passage-cut.bin 385 1 .local/cuts/u6-encoding-probe.bin
```

[historical] These commands ran at `96d8940b`. The founding and its modes (`ports passage`,
`expansions`, `found-only`, `founding <cut>`) and the keyed latent were retired on September 29
([lessons](../../records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)
§4); every field now reads the declared residue chart.

- **The founding** (development cells only): the public control's 4,958 cells found 41 classes from
  101 reached cells in 29,254 ms; the probe's 4,096 found 36 from 65 in 9,647 ms.
- **The exposure**: the held-out field face `5461 + 10/16 + ε` against the 65-cell chart's
  `5463 + 9/16 + ε`; 437,281 ms, peak 381,263,872 bytes. On the public control (a development
  reading) ring 0's lock admitted 2,128 of 4,958 development cells and the joint clock closed 37
  aeons (484,315 ms of exposure).
- **The prediction**: the pinned text run passed its bound (660 s, then 900 s) with no section; the
  founded `E_0` grows a batch's stage to 55,433 ms from the ninth deposit, against at most 6,047 on
  the residue chart (`develop text`, one pass). A bounded reading (`train 128 passes 1`) released 8
  illegible sections, six empty. The text is owner-only.

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
