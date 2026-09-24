# Phase 12b coupled continuation return

The source cut on `codex/consolidation-phase-12b` transplants the paused WIP `eda4ed3b` onto
Phase 12a and preserves the original WIP branch. It retires the coupled continuation's retained
operation programme: a published return carries the contemporary coupled wave, consumed root
address and material/source counts. A pending prediction retains its source family, member and
chart; a comparison reads its produced family at the contemporary constitution.

## Phase 11 and 12a joins

The WIP overlapped Phase 11 in `wave/coupled.rs` and
`wave/coupled/comparison/constitutive.rs`. The join keeps Phase 11's
`read_source_passage` result: a source map is retained, while its prediction is a returned
passage reading. It uses the one `prepare_consequence`/`can_commit_consequence`/
`publish_consequence` law and `read_wave_relation_in_chart`. The WIP's old
`ConditionContactReading`, `read_consequence_wave_relation`, `prepare_advance` and
`retained_prediction` paths do not return. Phase 12a has no same-path source overlap.

## Current rest formats

| Rest | Current writer and reader | Retired reader |
|---|---|---|
| Coupled outer `NormalWaveRest` | v7 without pending or historical current; v12 with pending source operands or historical current. The v12 reader checks the chart and source-family origin. | v8–v10 produced-family and relation-word frames. |
| Published `CoupledConstitutiveRest` | v7 header plus contemporary coupled wave. Its consumed root and counts are validated at read and remount. | v1–v6 frozen pre-return base and replay programme. |
| Plain normal bank | Existing writer-selected v1–v4, v6 Applied, v11 pending source joint. | v5 `LegacyCut` was already retired by R4 #103 and remains refused. |
| Nested wave relation | Phase 11's writer-selected v2/v4/v5. | v1/v3 remain refused. |

The previous positive tests of legacy replay/programme frames were retired with their
unconsumed implementation. Current tests cover v7/v12 rest, pending-source origin refusal,
the published continuation's process-exit rest and contemporary source return. A comparison
read at an earlier constitution is refused; the continuation tests re-read the pending
comparison at the current cut before returning it.

## Verification and remaining scope

`cargo check -p holonic-engine --lib` passed after the WIP transplant. The changed engine test
target compiled; six focused tests passed: current v7/v12 roundtrip and old-tag refusal,
pending-source origin refusal, dependent v1–v6 refusal, published continuation process-exit
return, its unit-sum receiver, and the atomic coupled source return. HNA all-targets compiled
against the cut. See `docs/VERIFICATION_RECEIPTS.tsv` for exact commands and logs. The original
70-minute synthetic HNA deposition probe was not run.

The handoff's second Phase 12b packet (junction/material-transport archive,
`current_history_source`, contextual lift and associated rest) and Phase 14 remain open. This
source cut does not claim their acceptance or the final M1/M2 library layout.
