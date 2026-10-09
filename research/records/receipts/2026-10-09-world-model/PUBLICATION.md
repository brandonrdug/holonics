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
- The C1b-1 source was published byte-identical to `0a7fa87a4`, whose `model.rs` header read "[source
  under review, not yet compiled or run]" from before that acceptance. Since C1b-2a (`a739963f6`, below) the
  header points to the record's §7, which carries the current grading.

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

## C1b-2a: the coupled prospect at `a739963f6`

The World model's coupled prospect, read before an encounter, runs the prepared action's own controlled
opening with each emitted wave answered by a live key's charts: one `k` for the whole passage
(`Word::prospective_coupled_passage`, `ProspectiveControl::controlled_word`, `WorldModel::coupled_prospect`,
`PreparedPhysicalAction::world_prospect`; the record's §7).
- Source `a739963f6` (full `a739963f68d6085eb41f5ae6a77f306151489e6d`, tree
  `c05b77cc19289652ea14b903b7efcad74728f78d`), on the C1b-1 receipts successor `3cfb2b71a`. It joins this
  main byte-identical in all six C1b source files.
- **Scoped native acceptance** ([handoff](coupled-native-v1/HANDOFF.md),
  [validation](coupled-native-v1/VALIDATION.json)). With 352 frozen native inputs, every scoped stage passed:
  - the workspace all-targets check;
  - four freshly built test executables;
  - 24 unique fixtures, each executed once: the nine of `world_model` (the two new coupled fixtures among
    them), `native_action_return` four, `physical_action` four and seven retention guards;
  - the guard lints of the affected library and tests;
  - all 57 guard doctests.

  In the passed coupled fixture, the encounter's actual incident and reflected waves and its own blind read
  of the compared station (the native receiving logits `R x`, in the producing frame) are carried by one `k`
  of the World key's prospect, read before the encounter, and match it exactly at a point fibre.
- **The whole gate failed, and that failure stays bound to `a739963f6`.** The all-targets guard clippy exited
  101 on one error: `std::process::exit` at `crates/holonics/examples/helical_duplex.rs:189`, denied by guard 7
  ([provenance](coupled-native-v1/LINT_FAILURE_PROVENANCE.json)). That file is byte-identical at
  `a739963f6`, `0a7fa87a4` and `3cfb2b71a`, so the failure is not a C1b change. The repair in this candidate
  makes the example's `main` return a `std::process::ExitCode`: the same message, then `FAILURE`, else
  `SUCCESS`. An ordinary exterior status return preserves the boundary receipt and lets owned resources end
  normally. The two clippy stderr files (all targets 315,264 bytes, affected 316,786 bytes) exceed the
  compact limit and are hash-only.
- **Stages**, each within its fixed projection and released, the 4 GiB reservation enforced, and no limit
  raised after launch:

  | Stage | Exit | Wall ns | Projection ns | CPU ns | Child RSS KiB |
  |---|---:|---:|---:|---:|---:|
  | check | 0 | 27,401,353,431 | 65,000,000,000 | 29,047,080,000 | 1,528,624 |
  | build | 0 | 53,195,231,405 | 65,000,000,000 | 56,027,692,000 | 2,111,620 |
  | coupled development v2 | 0 | 2,219,163,368 | 135,718,806,008 | 3,453,759,000 | 28,708 |
  | nondestructive development | 0 | 3,001,755,880 | 183,971,396,176 | 4,122,371,000 | 28,912 |
  | world existing | 0 | 2,612,187,044 | 17,534,143,576 | 3,676,631,000 | 28,652 |
  | native action | 0 | 575,311,025 | 10,876,653,472 | 1,653,169,000 | 18,368 |
  | physical action | 0 | 183,929,055 | 10,876,653,472 | 1,277,125,000 | 18,360 |
  | retention guards | 0 | 283,926,508 | 17,534,143,576 | 1,387,497,000 | 30,568 |
  | clippy, all targets | 101 | 10,312,081,621 | 65,000,000,000 | 11,773,525,000 | 981,860 |
  | clippy, affected | 0 | 6,966,837,336 | 65,000,000,000 | 8,314,040,000 | 709,184 |
  | doctests | 0 | 24,370,429,705 | 65,000,000,000 | 26,265,342,000 | 1,413,436 |

  The first launch of the coupled development fixture (v1) exited 125 before Cargo ran: its timeout carried
  the unsupported `us` suffix. It ran no fixture and is preserved; v2 corrected only the syntax, with the
  same deadline and caps.
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). Eight stage outputs name the validation's
  private run directory. One more placeholder is declared, `<coupled-run>/`, beside the earlier five. They
  replace it, and `<cargo-registry>/` in the check and build stdout, with no other byte change. All fourteen
  entries invert to their pinned originals, and no host path remains.
- **Hashed only:** [coupled-native-v1/OMITTED.md](coupled-native-v1/OMITTED.md); the manifest lists 262 files
  (21,121,913 bytes).
- **Scope.** Not claimed: the World's target face, raw `x` where `R` has a kernel, C2's two-encounter
  acceptance, the Ask, learning through the model, or the whole gate at `a739963f6`. The repaired example is
  compiled only by this candidate's own validation.

## C1b-2b: the key's face at `1ad7f4988`

A key may declare the World face it hypothesizes. The coupled prospect then predicts that raw face at every
compared epoch under the same `k` as the waves and the native readout (`ModelKey::with_face`, `KeyFace`,
`WorldModel::coupled_prospect`, `PreparedPhysicalAction::world_prospect`; the record's §7).
- Source `1ad7f4988` (full `1ad7f498825dcffbbcf4e4509519fea366cceb5b`, tree
  `a6619d3c6fd00482a40c049a8096cd48ccb2e0d6`), a descendant of C1b-2a's `a739963f6`. Its merge `7119527f4`
  joins this candidate byte-identical in the four 2b source files: `physical/action.rs`,
  `physical/action/model.rs`, `word/action.rs` and `tests/world_model.rs`.
- **Scoped native acceptance** ([handoff](face-native-v1/HANDOFF.md),
  [validation](face-native-v1/VALIDATION.json)). With 352 frozen native inputs, every scoped stage passed:
  - the workspace all-targets check;
  - four freshly built test executables;
  - 25 unique fixtures, each executed once: the ten of `world_model` (the new face fixture among them),
    `native_action_return` four, `physical_action` four and seven retention guards;
  - the guard lints of the affected library and tests;
  - all 57 guard doctests.

  The passed face fixture reads the World's actual raw face at a compared epoch (`C_S ξ_S⁺ + C_R ξ_R⁺ + o` on
  the step's after-state), the encounter's own blind native read (`R x`, required to occur) and its actual
  waves. One `k` of the faced key's prospect, read before the encounter, carries all three. Where the wave
  columns alone fix `k` (full column rank), a key with the true law and a wrong face offset is incompatible
  with the actual face. A key without a face adds no face rows and leaves the wave and native passage
  unchanged.
- **The whole gate was not rerun at `1ad7f4988`.** Its all-targets guard clippy failure stays bound to
  `a739963f6` (above). `helical_duplex.rs` is byte-identical at `1ad7f4988` and `a739963f6`, so the producer
  reused that failure's evidence and did not rerun it. The reused copies in `face-native-v1/inherited-gate/`
  are hash-only here: they are byte-identical to the committed `coupled-native-v1` `VALIDATION.json`,
  `LINT_FAILURE_PROVENANCE.json` and `FILE_HASHES.json`, and to that packet's all-targets clippy stderr. The
  affected guard lints passed, and they do not clear the whole gate. This candidate's final joined gate,
  with the `ExitCode` repair, is owed and has no result here.
- **Stages**, each within its fixed projection and released, the 4 GiB reservation enforced, and no limit
  raised after launch:

  | Stage | Exit | Wall ns | Projection ns | CPU ns | Child RSS KiB |
  |---|---:|---:|---:|---:|---:|
  | check | 0 | 27,899,159,150 | 65,000,000,000 | 29,903,743,000 | 1,520,780 |
  | build | 0 | 56,528,434,979 | 65,000,000,000 | 60,218,461,000 | 2,140,464 |
  | face development | 0 | 3,984,305,544 | 244,139,459,528 | 5,249,899,000 | 29,124 |
  | world existing | 0 | 7,928,651,752 | 37,858,749,896 | 9,373,843,000 | 28,552 |
  | native action | 0 | 602,373,817 | 17,937,222,176 | 1,904,934,000 | 18,312 |
  | physical action | 0 | 185,652,504 | 17,937,222,176 | 1,378,060,000 | 18,356 |
  | retention guards | 0 | 286,412,854 | 29,890,138,808 | 1,518,685,000 | 30,324 |
  | clippy, affected | 0 | 11,271,833,405 | 65,000,000,000 | 12,821,565,000 | 979,704 |
  | doctests | 0 | 26,999,751,617 | 65,000,000,000 | 29,356,512,000 | 1,410,144 |

  The face development deadline is a counted-work allocation. The later runtime deadlines use the larger of
  that measured fixture and the prior scoped runtime, all fixed before launch. The affected clippy stderr
  (315,700 bytes) exceeds the compact limit and is hash-only.
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). Seven stage outputs name the validation's
  private run directory. One more placeholder is declared, `<face-run>/`, beside the earlier six. The seven
  outputs replace it (1, 86, 2, 132, 26, 1 and 1 times), and the check and build stdout also replace
  `<cargo-registry>/` 50 times each, with no other byte change. All 21 entries invert to their pinned
  originals, and no host path remains.
- **Hashed only:** [face-native-v1/OMITTED.md](face-native-v1/OMITTED.md); the manifest lists 214 files
  (19,101,834 bytes).
- **Scope.** Claimed: on a declared raw face, prospective compatibility of the World's actual face, the native
  read and the waves under one `k`. Not claimed: the grain-level reading of a declared face (`Face::of_read`),
  conditioning retained fibres on actual face observations, deployed elimination of wrong-face alternatives,
  C2, the Ask, learning through the model, CUDA, the World/Robin and all-material variation, or the whole gate
  at `1ad7f4988`.

## The final joined gate at `d96cdbd86`

The combined candidate joins C1b-2a and C1b-2b onto published main `97c00ce9f`, with the repaired example,
and the whole gate ran on it once.
- Source `d96cdbd86` (full `d96cdbd86bc3ced02049682b1acbdd8512797d95`, tree
  `0ad64ee86f09c336939982aabb308adf90d95940`). On `97c00ce9f` it carries the merge `9bd63beca` of `a739963f6`,
  the example repair `bf425a34e`, the merge `7119527f4` of `1ad7f4988`, and the record, atlas and receipt
  commits above. All six C1b owner and test paths equal the tested `1ad7f4988`. Against it, the 352 native
  inputs differ in exactly three paths: the example's exterior status return, a documentation comment in
  `hnn/paired.rs`, and main's added diagnostic test in `hnn/tests/physical_communication.rs`.
- **The whole gate passed at `d96cdbd86`** ([handoff](joined-gate-v1/HANDOFF.md),
  [validation](joined-gate-v1/VALIDATION.json), [join scope](joined-gate-v1/JOIN_SCOPE_PROOF.json)).
  - `bash tools/gate.sh` exited 0. It ran the workspace all-targets check, the full all-targets guard lints
    (with the repaired `helical_duplex` example) and all 57 guard doctests. The script's own component times
    were 29,256 ms, 29,488 ms and 36,307 ms.
  - A fresh `cargo test -p holonics --lib --no-run` then passed and built one library-test executable. The
    added diagnostic test was compiled, not run.
  - This pass is bound to `d96cdbd86` alone. The failure at `a739963f6` and its inheritance, not rerun, at
    `1ad7f4988` stand as recorded above.
- **Stages**, within their fixed projections, released, the 4 GiB reservation enforced, and no limit raised
  after launch:

  | Stage | Exit | Wall ns | Projection ns | CPU ns | Child RSS KiB |
  |---|---:|---:|---:|---:|---:|
  | gate | 0 | 95,060,959,909 | 196,670,000,000 | 99,768,498,000 | 1,696,416 |
  | joined library tests, compile only | 0 | 34,970,983,050 | 65,000,000,000 | 37,263,247,000 | 2,149,012 |

  The gate's projection is three sequential compile units, each at the largest measured 64,890,000,000 ns,
  plus a 2,000,000,000 ns lifecycle allowance. To admit that grouped projection, the queue's resource guard
  copies changed only their sealed native-build wall and CPU ceilings. Monitoring, sealing, accounting, stop,
  cleanup and the lease are unchanged (`RESOURCE_POLICY_JOIN.json`, hash-only).
- **No runtime fixture was repeated.** The C1b-2a and C1b-2b acceptances stand at their producer pins, and
  the joined packet's `producer/` copies are byte-identical to the committed `face-native-v1` `HANDOFF.md`,
  `VALIDATION.json` and `FILE_HASHES.json` ([reuse](joined-gate-v1/PRODUCER_REUSE.json)).
- **Projected host paths** ([PROJECTION.json](PROJECTION.json)). One more placeholder is declared,
  `<gate-run>/`, for the gate's private run directory, beside the earlier seven.
  - `PRODUCER_REUSE.json` replaces `<repository>/research/records/receipts/` once.
  - The library compile's stdout replaces `<cargo-registry>/` 50 times and `<gate-run>/` 57 times, and its
    stderr replaces `<gate-run>/` once.

  There is no other byte change. All 24 entries invert to their pinned originals, and no host path remains.
- **Hashed only:** [joined-gate-v1/OMITTED.md](joined-gate-v1/OMITTED.md). The manifest lists 62 files
  (12,978,731 bytes), and 55 of them (12,937,056 bytes) are hash-only, among them the gate's stderr (365,761
  bytes, over the compact limit) and the `producer/` copies.
- **Scope.** Claimed: the repository's whole gate and the joined library-test compilation at this tree. Not
  claimed: any runtime fixture at this tree, or anything beyond the C1b-2a and C1b-2b scopes above.
