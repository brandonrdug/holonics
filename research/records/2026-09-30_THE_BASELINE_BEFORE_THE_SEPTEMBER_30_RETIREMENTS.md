# The baseline before the September 30 retirements

**Date.** September 30. **Issues.** #63, #73. **Grade.** [source-inspected] for the harness, its
configuration, the controls' artifacts and the consumer checks; [measured] for the replay's runs.

**Occasion.** THE_REBUILD U6's order, item C.1: before any retirement batch (N1, N2, P, H) and
before step 1a edits the harness, a record fixes the baseline commit, step 1's harness, its seeds and
configurations, the exact source and output artifacts of the current controls, and a minimal replay
whose listing every later batch must reproduce byte for byte. Evidence stays in history; this
record says where each piece is.

## 0. The recorded failures this work could repeat, and how each is held

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **7, a local pass read as progress.** `cargo check` and the library tests show that the code
  builds and the laws' tests hold, not that the harness still releases what it released. The replay
  (§5) is the behavioural check: the same read, the same listing, byte for byte.
- **A retirement that leaves a live consumer broken.** Every file N1 deletes (§6) was checked for a
  consumer across every configured target and every active worktree before it was deleted, and the
  replay runs after the batch.
- **Deleting evidence instead of keeping it in history.** Each deleted file is named with its
  permalink at the baseline commit; the receipts the notebook README carried stay in the README at
  that commit; every record keeps its receipts.
- **9, a refusal answered with a larger limit.** The replay's time was projected before its first
  run and it carries a guard (§5); a read that reaches the guard is reported incomplete.

## 1. The baseline commit

`d4596102d686c4879105d4a65ad03d19ea314c17` (main, "THE_REBUILD U6: the order revised under
Astra's review"). Its tree is at <https://github.com/brandonrdug/holonics/tree/d4596102>.

The gates at the baseline, run in this record's worktree:
- `cargo check --workspace --all-targets`: clean, no warning;
- `cargo test -p holonics --lib`: 975 passed, 0 failed, 0 ignored.

## 2. Step 1's harness

Step 1 runs `hnn::executed` through one cargo example of the `holonics` crate:

```sh
cargo build --release -p holonics --example hnn_prediction
cargo run --release -p holonics --example hnn_prediction -- executed move <seed> <requests>
cargo run --release -p holonics --example hnn_prediction -- executed train <arm> <terrain> <seed> <batch> <moves> <deadline ms> <out>
cargo run --release -p holonics --example hnn_prediction -- executed evaluate <terrain> <seed> <count> <out> <label[=E]>…
cargo run --release -p holonics --example hnn_prediction -- executed spread <terrain> <seed> <count> <label[=E]>…
cargo run --release -p holonics --example hnn_prediction -- executed slopes <terrain> <seed> <count> <label[=E]>…
```

- **Sources.** [`hnn_prediction.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_prediction.rs)
  (`main`'s `executed` arm dispatches), [`hnn_executed_loop.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_executed_loop.rs)
  (the modes: `stage_one`, `train`, `evaluate`, `spread`, `slopes`), and
  [`exterior.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/exterior.rs)
  (the resident set). The library owners it runs: `hnn::executed`, the bank's release
  (`hnn::prediction::{bank_release, BankPlacement, generate_by_bank, Refinement}`),
  `hnn::ring::ReceivingBank` and `Constitution::{initial, founding_transport, founded_transport}`.
- **The arms of `evaluate`, `spread` and `slopes`.** `lossless` alone is the declared opening
  `Constitution::initial(field, CAMPAIGN_ONE_BUDGET)` (`E₀`, transport modulus 1); any other label
  without a file is the founded opening (`E₀` at the founding modulus `ρ₀ = 102837/131072`,
  `Constitution::founded_transport`); `label=<file>` reads a written source port (`E 120 5`, 120
  realified rows of 5 rationals) and its `rho` line, if any, onto the opening.
- **The declaration** (`order_declared(false)`): the joint residue ring of period `60 = 2²·3·5`;
  alphabet `5` (four symbols and the termination); `K = 2` continuing words of span `w = 1`; `m = 8`
  stations; batch 16; request `n = 40` cells; no pump; three rings of period 60 in a chain (ring 0
  the source and locked on every phase), admittance 2 and exponent 0 on every contact; the
  constitution's budget `CAMPAIGN_ONE_BUDGET = 2³³`; the bank at strength `5/8`, read at the grain
  `2^(−16)` (`BANK_GRAIN = 16`).
- **The terrains** (`terrain_pairs`; only the terrain computes truth): `order2`,
  `x_t = x_(t−2) + 1 (mod 4)` after 40 drawn cells; `alternation`, two drawn classes alternating;
  `line`, a drawn start and step, `x_t = x_0 + s t (mod 4)`. Requests are drawn by the harness's
  `Draw` at the seed given.

## 3. The seeds and configurations in use

| Seed | Role | Where |
|---|---|---|
| 21, 22 | `develop order2` training and evaluation draws | `hnn_prediction.rs` |
| 41 | development batch of the modulus pin's reads (§1b–§1e, §5 there); **this record's replay** | the [modulus pin](2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_PINNED_BEFORE_ITS_RUNS.md) |
| `2_026_092_901` / `902` / `903` / `904` / `905` / `906`; `20_260_929` | the September 29 training, evaluation, moiré, mask, probe and probe-mask seeds; the release seed | `hnn_prediction.rs` |
| `2_026_093_001` / `002`; `004`; `005`–`008` | Stage 2: order-2 training / confirmation; the partition arms' mask; the alternation and the line | the [bounded test's pin](2026-09-30_THE_EXECUTED_COMPARISONS_BOUNDED_TEST_PINNED_BEFORE_ITS_RUNS.md) |
| `2_026_093_011`–`016` | the station-framed placement's training and confirmation (order-2, alternation, line) | the [station-framed pin](2026-09-30_THE_STATION_FRAMED_PLACEMENT_PINNED_BEFORE_ITS_RUNS.md) |
| `2_026_093_021`–`026` | the modulus founded off one: training and confirmation (order-2, alternation, line) | the [modulus pin](2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_PINNED_BEFORE_ITS_RUNS.md) |
| 101 (the float fit's own draws) | the station-framed refit: `eO_fit.py order2 400 256 101 0.03 0.05 1 16` | the [station-framed receipt](2026-09-30_THE_STATION_FRAMED_PLACEMENT_MEASURED_THE_REFIT_READS_BOTH_CHAINS_AND_THE_CERTIFIED_MOVE_KEEPS_THE_MODULUS_AT_ONE.md) §2a |

The final confirmation set of loop 1a is unread; it is not among these seeds.

## 4. The controls: their source and output artifacts

SHA-256 of each file at the baseline commit. Receipts directories:
[modulus](2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_receipts/) (`M/`),
[station-framed](2026-09-30_THE_STATION_FRAMED_PLACEMENT_receipts/) (`S/`).

- **The lossless opening** (`E₀`, `ρ = 1`) and **the founded opening** (`E₀`, `ρ₀ =
  102837/131072`): no file; the code at the baseline commit makes them. On order-2 confirmation
  (`executed evaluate order2 2026093022 128 <out> lossless opening executed-open=<E>`): lossless 0
  released, 128 held, 0 whole; founded 121 released, 7 held, 0 whole (`M/confirm_order2_log.txt`,
  `M/confirm_order2_sections.txt`, SHA-256 `5a71cdc99f97c93948c078267ca37a324922989da9afe349f308edc489ee037b`).
- **The native trained constitutions** (the certified move from the founded opening; the modulus
  record §2):

  | File | Training | `ρ` | Confirmation, whole of 128 | SHA-256 |
  |---|---|---|---|---|
  | `M/E_trained_order2.txt` | `executed train executed-open order2 2026093021 8 16 6000000` (`M/train_order2_log.txt`) | `1750365/2097152` | 0 (seed `…022`) | `756dbe7568adb72d29ec41fade8b41f7edfc256ed4b5a8c7c05a225bfc1283e0` |
  | `M/E_trained_alternation.txt` | 8 moves of 8 at `…023` (`M/train_alternation_log.txt`) | `1670477/2097152` | 22 (seed `…024`; `M/confirm_alternation_sections.txt`, `68ecc4ae6801eb4f0e936ab18ac32f84c23a3175cc0b3cf4e1aed1810cf8c6f8`) | `8dab4f53adaed74a3614e35c9d71f03acdc01caeef1c0d58f177cfefa18abde3` |
  | `M/E_trained_line.txt` | 8 moves of 8 at `…025` (`M/train_line_log.txt`) | `840009/1048576` | not read (stopped by the orchestrator) | `0365ceeb99d58bd863a72885377a7ee3dbf59ac50d6b2ba5a4b1c4a04671b3a3` |

  The earlier trained ports (Stage 2's `E_*.txt` in the executed comparison's receipts, the
  station-framed `S/E_executed_open_*.txt` at `ρ = 1`) are superseded evidence, kept in their
  receipts.
- **The station-framed refit, the representation control** (96 whole sections of 128; the
  station-framed receipt §2a). Its chain of artifacts:
  1. the float fit `eO_fit.py order2 400 256 101 0.03 0.05 1 16` on the release's own trajectory,
     its log `S/seed_fit.txt`;
  2. its last `E` and `ρ` exported as exact rationals of the floats, `S/seed_export.txt`
     (SHA-256 `57091b22022a3d33cca4968491c70e786388e06b36250b9d448741bae7fe1683`);
  3. the native read on Stage 0's 128 held-out requests, `bank_causes -- native-release`, rounding
     `E` to the source port's lattice `2^(−21)` and `ρ` to `137573/262144`: `S/seed_native_log.txt`,
     `S/seed_native_release.txt` (SHA-256 `7196dc916d003c439c87dfa96540777f89b9642528a38a3b772f4549142dd725`),
     counted in `S/seed_counts.txt` (released 128, whole 96, stations right 917 of 1,024, first lock
     right 128);
  4. the same `E` and `ρ` on the lattice as a port the executed harness reads,
     `M/refit_on_lattice.txt` (`ρ = 137573/262144`; SHA-256
     `5d8c4a2c7369ef23cbfbe7bdf80ea3dbe398b97e191f5fafcba39fa2d97f7fa5`).

  Steps 1 to 3 ran through files N1 deletes (`eO_fit.py`, `export.py` and `bank_causes.rs`); they
  are reproduced at the baseline commit. Step 4 is read by the kept harness, and the replay reads it.

## 5. The minimal replay

[`replay_baseline.sh`](../notebook/hnn_design/replay_baseline.sh) builds the harness and runs one
development read:

```sh
cargo run --release -q -p holonics --example hnn_prediction -- executed evaluate order2 41 8 <out> \
  lossless opening \
  executed-open=research/records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_receipts/E_trained_order2.txt \
  refit=research/records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_receipts/refit_on_lattice.txt
```

It writes the listing (the harness's stdout, then the section listing written to `<out>`) and diffs
it against the reference [`replay_reference.txt`](2026-09-30_THE_BASELINE_receipts/replay_reference.txt)
(41 lines, 6,616 bytes, SHA-256 `9e10a890dcf935fd7ef158d9cc6681658578ec401ddd45618c80dc7e4b1cb050`,
regenerated at step 1a's join `7ca300bb` once its diff was confirmed to be only 1a's constant and
nonconstant strata and a per-constitution time; the baseline's first reference was 6,160 bytes,
SHA-256 `e2c0ca40035532ce8a39c8844f9d02d29f270dfe3914fa590585281a3497f2cd`).

- **What is masked, exactly.** The harness's last line,
  `executed evaluate: <ms> ms; resident <now> now, <peak> peak` (or `resident unread`), whose three
  integers (wall milliseconds, the resident set now and at its peak, in bytes) are replaced by
  `<ms>`, `<now>` and `<peak>`; and, since step 1a, the wall milliseconds ending each
  constitution's summary line (`first lock right <n>; <ms> ms`). Every other byte is compared, the
  transport moduli, counts, requests, targets, released classes and lock orders included.
- **What it reads.** Development seed 41 is the modulus pin's development batch (read there at 8
  requests too); no pinned training, confirmation or final-confirmation seed is read. The four
  constitutions are the controls of §4: lossless, founded, the trained order-2 port and the refit.
- **Its projection, before the first run.** The modulus record's order-2 confirmation read 3 × 128
  requests in 749,108 ms on the host's 24 cores; 8 requests fit one parallel pass, so an arm costs
  about one request's serial time. Projected 180,000–360,000 ms for the four arms, with a guard of
  600 s on the read (the script's `timeout 600`). Build: 46 s from a clean target.
- **The baseline listing** (the reference's counts, 8 requests each):

  | Constitution | Transport modulus | Released / held | Whole | Stations right (of 64) | First lock at station 0 or 1 | First lock right |
  |---|---|---|---|---|---|---|
  | lossless | 1 | 0 / 8 | 0 | 14 | 0 | 0 |
  | founded opening | `102837/131072` | 8 / 0 | 0 | 15 | 0 | 3 |
  | trained order-2 | `1750365/2097152` | 8 / 0 | 0 | 13 | 4 | 1 |
  | the refit | `137573/262144` | 8 / 0 | **6** | 57 | 0 | 8 |

- **The runs at the baseline** (host, 24 cores, one at a time):

  | Run | Harness wall | Peak resident bytes | Listing |
  |---|---|---|---|
  | the first read (its listing became the reference) | 93,933 ms | 85,925,888 | the reference |
  | replay 1, the committed script | 92,544 ms | 85,590,016 | matches, byte for byte |
  | replay 2, the committed script | 93,925 ms | 84,918,272 | matches, byte for byte |

  Two earlier replays, before the script carried its guard and exit codes (the read and the diff
  unchanged), matched too (93,391 and 93,597 ms). Below the projection; the read is deterministic at
  the baseline (exact arithmetic, the requests collected in index order).

Every retirement batch runs `bash research/notebook/hnn_design/replay_baseline.sh` after its change
and records the result; exit 0 is a match, 1 a mismatch (with the diff), 2 a read that reached its
guard (incomplete).

## 6. The files N1 deletes

Batch N1 (THE_REBUILD U6, the order's C.2) deletes 52 files of the notebook, 18,132 lines, each
checked for a consumer first (the `[[example]]` entries, `#[path]` includes, Python imports, script
calls and tests, across `crates/holonics` and `crates/holonics-cuda`'s targets, the main checkout,
the step-1a worktree and the protein worktree's working tree, read only). Each is recovered at its
permalink.

| File (under `research/notebook/hnn_design/`) | Lines | What it was |
|---|---|---|
| [`bank_causes.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes.rs) | 3,230 | the causes' probe harness (a stale copy of `hnn_prediction.rs` with dump modes, `native-release`, `reentry`) |
| [`bank_causes_probe/bankprobe.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/bankprobe.py) | 121 | the probe's float bank |
| [`bank_causes_probe/certify.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/certify.py) | 123 | the probe's certification check |
| [`bank_causes_probe/check_grad.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/check_grad.py) | 37 | a gradient check |
| [`bank_causes_probe/common.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/common.py) | 94 | the probe's shared imports |
| [`bank_causes_probe/dumpio.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/dumpio.py) | 83 | the dump parser |
| [`bank_causes_probe/e3_decompose.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/e3_decompose.py) | 83 | experiment E3 |
| [`bank_causes_probe/eA1_alignment.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eA1_alignment.py) | 63 | experiment A1 |
| [`bank_causes_probe/eC_chains.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eC_chains.py) | 26 | experiment C, the chains |
| [`bank_causes_probe/eD_reentry.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eD_reentry.py) | 107 | the re-entry's float prototype |
| [`bank_causes_probe/eF_reentry_distances.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eF_reentry_distances.py) | 64 | counts of a `reentry` trace |
| [`bank_causes_probe/eF_release_counts.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eF_release_counts.py) | 95 | counts of a `native-release` trace |
| [`bank_causes_probe/eG_generation.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eG_generation.py) | 57 | experiment G |
| [`bank_causes_probe/eM_movement.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eM_movement.py) | 48 | experiment M, the movement |
| [`bank_causes_probe/eO_fit.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eO_fit.py) | 117 | the refit's float fit (§4) |
| [`bank_causes_probe/eP_rho_path.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eP_rho_path.py) | 85 | the float fit's modulus path |
| [`bank_causes_probe/eR_fit.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eR_fit.py) | 72 | the passage law's fit |
| [`bank_causes_probe/eS_stations.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/eS_stations.py) | 20 | experiment S |
| [`bank_causes_probe/export.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/export.py) | 36 | the fit's export for the native read |
| [`bank_causes_probe/fit.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/fit.py) | 114 | the probe's float fit |
| [`bank_causes_probe/measure.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/measure.py) | 13 | a time and memory wrapper |
| [`bank_causes_probe/model.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/model.py) | 267 | the probe's float model |
| [`bank_causes_probe/s1_margin.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/s1_margin.py) | 67 | Stage 1's margins |
| [`bank_causes_probe/s1_steps.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bank_causes_probe/s1_steps.py) | 20 | Stage 1's steps |
| [`hnn_population.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_population.rs) | 1,389 | the egg population on terrain (the `hnn_population` example) |
| [`hnn_population_birth.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_population_birth.rs) | 537 | residual-founded transport discovery |
| [`hnn_population_census.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_population_census.rs) | 433 | U2's standing census |
| [`hnn_population_curated.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_population_curated.rs) | 2,489 | the curated source, F4, F5 |
| [`hnn_population_evolution.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_population_evolution.rs) | 483 | the evolved prior and species |
| [`hnn_population_f0.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_population_f0.rs) | 992 | F0's egg and acceptance run |
| [`hnn_population_u2.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_population_u2.rs) | 640 | U2's acceptance run |
| [`hnn_population_u6.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_population_u6.rs) | 849 | U6's symmetric comparison |
| [`hnn_landmark.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_landmark.rs) | 2,864 | the landmark tree, count-only |
| [`hnn_parametron.rs`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_parametron.rs) | 860 | the parametron re-derived |
| [`f1_dictionary.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/f1_dictionary.py) | 100 | F1's dictionary |
| [`f1_validation_part.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/f1_validation_part.py) | 74 | F1's held-out part |
| [`f2_capacity_probe.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/f2_capacity_probe.py) | 116 | F2's probe cut (and `F2V2`'s, which `hnn_exposure`'s spent `gate f2` read) |
| [`f4_retrospective.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/f4_retrospective.py) | 182 | F4's requests and retrieval control |
| [`f5_retrospective.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/f5_retrospective.py) | 19 | F5's requests |
| [`f5_dev_request.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/f5_dev_request.py) | 55 | F5's development request |
| [`f5_request_bundle.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/f5_request_bundle.py) | 52 | F5's request bundle |
| [`f5_blind_input.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/f5_blind_input.py) | 80 | F5's blind cases |
| [`athena_dev_gate.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/athena_dev_gate.py) | 82 | Athena-0's development gate |
| [`release_legibility.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/release_legibility.py) | 162 | count-only readings of released text |
| [`bits2.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/bits2.py) | 110 | step 4 design: bits, the cone, the moment |
| [`collapse_bezout.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/collapse_bezout.py) | 73 | step 4 design: case (5) by Bezout |
| [`collapse_check.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/collapse_check.py) | 67 | step 4 design: case (5) by Sylvester |
| [`critical_cayley.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/critical_cayley.py) | 29 | step 4 design: the lossless storage wave |
| [`deposit_bits.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/deposit_bits.py) | 68 | step 4 design: a deposited map's bits |
| [`propagation.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/propagation.py) | 112 | step 4 design: key location by propagation |
| [`release.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/release.py) | 127 | step 4 design: the causal diamond |
| [`word_bits.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/word_bits.py) | 46 | step 4 design: a word's bits |

Every step 4 design number these eight reproduce is in the
[construction record](2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md)
(its step 4 design and "Bits: what is bounded, and what is not"), and `release.py`'s six-ring path is
also held by the crate's tests (`hnn/tests/{learning, retention}.rs`).

**Kept against the audit** (it named twelve step 4 design scripts): `power.py`, `swing_power.py`
and `capacity.py`, whose numbers are only partly recorded, and `field.py`, which the three import.
- `power.py`: the construction record states the balance's cases and "grows 245-fold in 8 ticks";
  the exact reading, `P(8)/P(0) = 244 + e`, `e ∈ [2626/3871, 251/370]` (an exact ratio of 7,580
  bits), is only in the notebook README.
- `swing_power.py`: the record states that the per-ring power rose, then fell, and that the
  per-contact power is exactly the same at every tick; the values (`73199/1920` at tick 0,
  `50 + e`, `e ∈ [3683/3851, 285/298]` at tick 5, `43 + e`, `e ∈ [1577/3270, 1074/2227]` at tick 6;
  `648509/23040` per contact at every tick) are only in the README.
- `capacity.py`: every `n*` is recorded; the dense code's readings `135` bits at `n = 128`, about
  117,000 cells for the period-7 ring, and `9472/9375` at `n = 4,200,000` and `132608/134375` at
  `n = 4,300,000` are only in the README.

**Kept in `bank_causes_probe/`**: `eF_confirmation_counts.py` and `eM_section_shapes.py`, which
count `executed evaluate` listings (the modulus record §3 reads them).

## 7. N1's receipt

[measured; source-inspected] N1 deleted the 52 files of §6 (18,132 lines), removed the
`[[example]]` entries of `hnn_landmark`, `hnn_population`, `hnn_parametron` and `bank_causes` from
`crates/holonics/Cargo.toml`, rewrote the notebook README as a route to what remains (the kept
harnesses' index and receipts, the replay, and the retired harnesses with the commit holding each and
the README sections, at that commit, holding their receipts; 2,855 lines to 1,359), and repinned
every markdown link to a deleted file or to a removed README section onto its permalink at
`d4596102`: 18 links in `docs/HNN_FORMULA.md` and five records (F1, F4, F5, the construction record,
U2's pin). THE_REBUILD's link to the README's "F0 candidate 2" section resolves to a heading the
README keeps for it.

- **The consumer checks** (before the deletions): the only code consumers were the four
  `[[example]]` entries; no `#[path]` include, Python import, script call or test outside the deleted
  set names a deleted file. The step-1a worktree changes only `hnn_prediction.rs` and
  `hnn_executed_loop.rs`, and neither names a deleted file. The protein worktree's working tree
  differs from its head `03ecec71` only in its workspace manifest and its new crates, none of which
  names a deleted file.
- **The gates after N1**: `cargo check --workspace --all-targets` clean, no warning (the remaining
  examples re-checked); `cargo test -p holonics --lib` 975 passed, as at the baseline; the kept
  Python tests pass (`athena_blind_tests.py` 5, `athena_file_checkpoint_tests.py` 11,
  `athena_file_protocol_tests.py` 8, `athena_protocol_tests.py` 14, `f5_context_tests.py` 5); the
  two listing counters read the replay's listing; `power.py` and `swing_power.py` print the readings
  §6 names.
- **The replay after N1**: the listing matches the reference byte for byte (164,855 ms, peak
  resident 89,366,528 bytes; the host was shared with another worker's runs).

## 8. N2's receipt

[measured; source-inspected] Batch N2 (THE_REBUILD U6, the order's C.4), on step 1a's tip
`7ca300bb`, in two commits.

- **The step 4 scripts.** `power.py`, `swing_power.py` and `capacity.py` were re-run (`capacity.py`
  in 370 s) and printed the readings §6 names. Every reading they print that the
  [construction record](2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md)
  did not hold is now written there exactly: the power balance's `P` and `Π_c` at every tick with
  their bit sizes and `P(8)/P(0) = 244 + e`, `e ∈ [2626/3871, 251/370]` (replacing "245-fold"); the
  per-ring power at every tick (replacing "rose, then fell": it falls at the first tick, rises
  through the fifth and falls at the sixth) and the per-contact `648509/23040`; the control's
  `log₂N(n)` bounds and dense code at every `n` read (135 bits at `n = 128`, 138 at 144), the
  period-7 ring below the source at 117,000 and at no multiple of 1,000 before it, the eight rings'
  stretches (from 3,190,785, not below again at 3,670,785, below from 4,243,457) and the ratios
  `9472/9375` and `132608/134375`. Then `field.py`, `power.py`, `swing_power.py` and
  `capacity.py` were deleted (232, 64, 39 and 126 lines: 461), with the record's three links
  repinned to `d4596102`.
- **The harness strip.** `hnn_prediction.rs` keeps only the declaration the executed loop reads
  (`Declared`, `declare`, `ingest`, `Engine` with `new` and its field, refinement and opening,
  `bank_of`, `bank_strength`, `order_declared`, `order_pairs`, `resident`) and the dispatch of
  `executed move | train | evaluate | spread | slopes | counts`; 2,344 lines to 317. Retired: the
  modes `copy`, `moire`, `divergence`, `order2 [pinned|bank|learn]`, `pumped below|past`, `text`,
  `probe` and `develop …`, the `Engine`'s methods `learn`, `generate`, `generate_banks`, `report`,
  `report_bank` and `report_learning`, their tallies (`Tally`, `LearningTally`, `BankTally`) and
  their terrains, pins and guards. `hnn_executed_loop.rs` loses `executed train`'s `face` arm (the
  arm name keeps its form, `executed-open` or `executed-partition`). The source of all of it is at
  `7ca300bb`.
- **The per-constitution clock.** `executed evaluate`'s clock for each constitution started after
  its parallel generation, so every summary line printed `0 ms`; it now starts before the
  generation. The replay masks that field.
- **The exterior relations.** `Relation` and `RelationKind` are defined in `exterior.rs`, and
  `read_incidence` returns them; the crate's `receiver::population::admitted` keeps its own
  definitions until batch P retires it. `HUMAN` and `AGENT` were not moved: after the strip no
  notebook file reads them.
- **The chase's tree control.** `hnn_chase.rs`'s reception phase no longer reads the landmark tree
  at depths 1, 2, 4, 8. Its output at `7ca300bb` and after the change, run once each: 414 and 334
  lines, identical outside the 64 per-depth code lines, the 16 ordering lines, the summary's tail
  (the old run: strictly below the tree's least on 16 of 16) and the wall times.
- **The consumer checks** (before the deletions): no file in this worktree, the main checkout's
  working tree (its three untracked `tools/agent_mailbox*` files included) or the protein
  worktree's working tree (names and imports only; its new crates `holonics-figures` and
  `holonics-protein`) imports `field.py` or the three scripts, includes `hnn_prediction.rs` or
  `hnn_executed_loop.rs`, or names a removed harness function. The crate's own mentions (prose in
  `hnn/tests/propagation.rs`, `hnn/constitution.rs` and `hnn/prediction.rs`) are batch H's.
- **The gates after N2**: `cargo check --workspace --all-targets` clean, no warning;
  `cargo test -p holonics --lib` 976 passed, as before the batch; the kept Python tests pass
  (`athena_blind_tests.py` 5, `athena_file_checkpoint_tests.py` 11,
  `athena_file_protocol_tests.py` 8, `athena_protocol_tests.py` 14, `f5_context_tests.py` 5).
- **The replay after N2**: the listing matches the reference byte for byte (the harness 91,160 ms,
  peak resident 84,869,120 bytes). The four constitutions' own times, now read: lossless 768 ms,
  the founded opening 18,107, the trained order-2 port 36,162 and the refit 36,071.
