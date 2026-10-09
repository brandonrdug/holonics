# Publication note

This directory publishes the compact receipts of C1b-1, the World's learned model (the
[receiving-phase record](../../2026-10-08_THE_RECEIVING_PHASE_COMPARISON_RETAINS_AN_EXACT_FAMILY_AND_ITS_PROBE_IS_A_DECLARED_LEVERAGE.md)
§7; Refs #73).
- Source `0a7fa87a4` (`0a7fa87a44823`, full `0a7fa87a448232a273e7f9375d85f1dd90df649c`, tree
  `aaea23f1e3e4f198f19323cdce3ed6994bb3a17a`), a header-only successor of the reviewed `fce952952`: its one
  changed path is `crates/holonics/src/hnn/physical/action/model.rs`, and the operational Rust body is
  byte-identical once the module header lines are removed.
- The C1b-1 source against `5864e4f58`: the new owner `hnn::physical::action::model`, its ingestion in
  `physical/action.rs`, the Resident's retention, binding and bit charge in `hnn/reference.rs` and
  `hnn/reference/interaction.rs`, the owner's test `crates/holonics/tests/world_model.rs`, and §7 of the record.
- The published source is byte-identical to `0a7fa87a4`. Its `model.rs` module header still reads
  "[source under review, not yet compiled or run]", written before this acceptance; the current grading
  is this note and the record's §7.

- **Native acceptance at `0a7fa87a4`** ([handoff](native-v1/HANDOFF.md),
  [validation](native-v1/VALIDATION.json)).
  - The workspace all-targets check passed. Four test executables were freshly compiled.
  - 22 unique fixtures passed, each once and none failed:
    - the owner's seven: the World's own key reproduces every actual step and its fibre is the batch
      preimage; a disconnected key is eliminated only by its exact annihilator; a non-passive key is held at
      its certified cut while the tick advances; an interrupted encounter is absorbed through its executed
      steps without rollback; binding is refused without a World, off its tick or off the source frame; the
      Resident charges the model's current bits at every encounter; the return image separates the free and
      forced responses and holds the actual returns;
    - the affected `native_action_return` four and `physical_action` four, and seven guards (`guards`:
      eleven, fifteen twice, five, four, nine and one).
  - The compiler's only warnings are three `dead_code` methods outside this change
    (`Word::anchor_differential_joined` in `hnn/port.rs`, `SourceObserverView::seeds` in `hnn/receiving.rs`,
    `HeldContactVariation::advanced` in `hnn/word/variation.rs`).
- **Stages** ([validation](native-v1/VALIDATION.json)). Each stage was accepted, quiescent and released, and
  finished within its fixed projection; no limit was raised after launch.

  | Stage | Threads | Wall ns | Projection ns | CPU ns | Group peak B | Group cap B | Child RSS KiB |
  |---|---:|---:|---:|---:|---:|---:|---:|
  | `actual-c1b-prep8-20261009-v206` | 1 | 9,169,318,185 | 17,000,000,000 | 6,467,318,000 | 8,448,020,480 | 8,589,934,592 | 39,784 |
  | `actual-c1b-check4-20261009-v207` | 4 | 26,968,060,377 | 65,000,000,000 | 27,170,679,000 | 1,823,686,656 | 4,294,967,296 | 1,513,152 |
  | `actual-c1b-build4-20261009-v207` | 4 | 56,520,477,615 | 65,000,000,000 | 57,800,242,000 | 2,434,633,728 | 4,294,967,296 | 2,157,392 |
  | `c1b-first-20261009-v208` | 1 | 1,204,673,928 | 16,387,764,493 | 1,149,701,000 | 26,533,888 | 4,294,967,296 | 23,916 |
  | `c1b-remaining-20261009-v208` | 1 | 1,902,093,772 | 31,775,528,986 | 1,833,964,000 | 27,262,976 | 4,294,967,296 | 24,940 |
  | `c1b-native-action-return-20261009-v209` | 1 | 799,260,279 | 21,517,019,324 | 738,294,000 | 27,295,744 | 4,294,967,296 | 24,924 |
  | `c1b-physical-action-20261009-v209` | 1 | 391,080,692 | 21,517,019,324 | 339,503,000 | 25,980,928 | 4,294,967,296 | 24,928 |
  | `c1b-guards-20261009-v209` | 1 | 540,818,170 | 36,904,783,817 | 488,337,000 | 27,287,552 | 4,294,967,296 | 30,664 |

  The ratio of measured to projected wall time is each row's wall over its projection. An earlier 8 GiB
  reservation was refused before any compiler launched; its evidence is kept hash-only. The compilation ran
  under the supported 4 GiB reservation with one Cargo job and four codegen CPUs.
- **Committed:** the handoff, the validation, every stage's stdout and stderr (the largest is 41,914 bytes
  projected; whole, except the host paths projected below) and `native-v1/FILE_HASHES.json`.
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). Four committed files carry absolute host
  paths in their original bytes: the check and build stages' stdout and stderr.
  - They are published with the queue admissions directory replaced by `<queue-admission>/` (1, 86, 2 and
    132 times) and the crates.io registry sources by `<cargo-registry>/` (50 times in each stdout). No other
    byte changes.
  - Each original's sha256 and size stand beside its projected pins, and in the unchanged
    `native-v1/FILE_HASHES.json`. The placeholders do not occur in the originals, so substituting the
    prefixes back restores the pinned bytes (checked for all four before commit).
- **Hashed only:** [native-v1/OMITTED.md](native-v1/OMITTED.md): the packet's other files, among them the
  352 frozen source inputs, the four executables, the stage configurations and seals, the preserved 8 GiB
  refusal and the withheld source-review clearance. The manifest lists 531 files (186,879,899 bytes).
- **Scope.**
  - Claimed: on declared native-kind keys, the exact fixed-key filter over actual executed World steps (the
    complete `(a, b)` preimage restriction and advance, elimination only by an exact annihilator, a held key
    keeping its certified cut), ingestion of completed and interrupted encounters without rollback, binding on
    the source's frame, the return image over a declared future word, and the mutable model state charged in
    the Resident's state bits.
  - Not claimed: a coupled source/World future certificate (C2's finite forward cover), the face chart, the
    Ask over keys, learning through the model, the World/Robin and all-material variation, CUDA parity, and
    any process or device capacity. The bits do not measure the immutable key laws, solve workspace or
    process memory.

## The joined-source compilation at `0c9cd6714`

The C1b-1 acceptance is pinned to `0a7fa87a4`, on `5864e4f58`. Its join onto published main `887ad60df`
places the C1b code beside the published diagnostic unit test, so the join was compiled before publication.
- Source `0c9cd6714` (full `0c9cd67146088ce944353a954ae9e044191810fa`, tree
  `1c7acd8979c3cfcdffc44049cb08993733975de6`), the merge of the source-unchanged packet `4540649207` onto
  `887ad60df`. All five C1b source files equal the accepted `0a7fa87a4`; against it the 352 native inputs
  differ in exactly the diagnostic unit test (`hnn/tests/physical_communication.rs`) and the `paired.rs`
  header.
- **Compilation** ([handoff](integration-compile-v1/HANDOFF.md),
  [validation](integration-compile-v1/VALIDATION.json)). `cargo test -p holonics --lib --no-run`, one Cargo job
  and four codegen CPUs under the 4 GiB reservation: compiler exit 0, no error, one fresh library-test
  executable. Its only warning is the pre-existing `dead_code` method `HeldContactVariation::advanced`
  (`hnn/word/variation.rs`). Compiler wall 34,157,392,129 ns; guarded wall 35,012,583,451 ns against the
  fixed 65,000,000,000 ns; aggregate CPU 35,832,805,000 ns; peak child resident set 2,146,132 KiB; group peak
  2,429,689,856 B.
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). The compilation built in the integration
  candidate's own worktree with a private run directory, so its stdout and stderr name two host directories
  beyond the earlier three. Two placeholders are declared for them in the header, `<candidate-worktree>/` and
  `<native-run>/`; the stdout replaces `<cargo-registry>/` 50 times, `<candidate-worktree>/` 6 times and
  `<native-run>/` 51 times, the stderr `<candidate-worktree>/` once. No other byte changes; the placeholders do
  not occur in the originals, and substituting every prefix back restores each pinned original (checked for
  all six entries before commit; the four earlier entries are unchanged).
- **Hashed only:** [integration-compile-v1/OMITTED.md](integration-compile-v1/OMITTED.md); the manifest lists
  32 files (3,908,248 bytes), among them the executable record, the input and output seals and the stage
  configuration.
- **Scope.** Compilation of the joined library tests only: no fixture ran, the native acceptance stays at
  `0a7fa87a4`, and nothing here extends it to a coupled World future, learning through the model or the
  World's observed face.
