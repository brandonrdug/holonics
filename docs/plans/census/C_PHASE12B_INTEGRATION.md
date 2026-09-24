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

## Second packet: exterior occurrence placement

The `FieldArchive`/`ArchivedField` exterior placement ladder is retired. A repository-wide Rust
source search found its APIs only in engine tests; no non-test caller depended on it. This removes
`field/archive.rs`, the placement report/API, `enable_history_archive`, `archive_history_before`,
and `remount_with_history_archive`. `HeldField` now owns a resident history carrier directly;
there is no optional resident/archived split or on-demand archive remount. Legacy constituted-field
occurrence clocks remain because the engine drivers and source/material readers consume them.
Source-only fields still refuse legacy advancement and validate empty history.

The ordinary `NativeFieldRest` writer and reader retain all six current formats:
`HNA-NATIVE-FIELD-REST\x01` and `\x02` base/packed, `\x03` and `\x04` current-report
base/packed, and `\x05` and `\x06` joint-current base/packed. The joint formats retain their
current-report presence byte. Current source, complete/contextual/moment material transport,
operative history, and contextual-lift operators remain in place. Existing archive-driven tests
were retargeted to resident history plus ordinary write/read/remount, preserving their source,
material and continuation assertions; file-placement fault/checksum tests are retired with the
file-placement mechanism.

**Archive packet verification, September 24.** `cargo check -p holonic-engine --lib` and
`cargo check --locked -p holonic-engine --all-targets` pass on the final source after the
remount-test mutable binding correction (`0c851a35`). Under `.local/gpu.lock`, the seven field rest
tests pass, including source-only refusal and the 12-occurrence ordinary rest/remount test. The
dedicated writer test passes for all six current tags (`\x01`–`\x06`). Focused current-history,
contextual-lift, complete/contextual/moment material, packed-v2 report support, operative source
and current, internal-current, and historical-source ordinary-remount tests pass. Exact commands
and outcomes are pinned in `docs/VERIFICATION_RECEIPTS.tsv` against this packet commit.

HNA all-targets and Phase14 integration remain separate gates.

## Third packet: coupled-wave session envelope

The production writer in `NativeCoupledWaveSession::checkpoint_stream` emits only
`HNA-COUPLED-WAVE-SESSION\x03`. The outer reader previously accepted `\x01` and `\x02` as well,
constructing an affine-only session from an older `NormalWaveRest`. A whole-repository Rust source
search found no production writer for those envelope tags; the only in-repo positive fixture was
the ignored `coupled_session_reads_legacy_affine_frames` test. The cut removes those two readers and
the affine fallback from `NativeCoupledWaveSavedSession::read`, keeps the affine import in
`from_model_directory` (a distinct current model-directory input), and replaces the positive old
wire fixture with explicit v1/v2 refusal. A current v3 checkpoint still crosses the public stream
resume path and retains its pending emission.

Nested writer formats remain as recorded above: coupled `NormalWaveRest` v7/v12 and dependent
`CoupledConstitutiveRest` v7; plain normal v1–v4, v6 Applied, v11 pending; nested relation v2/v4/v5.
The separate outer `HNA-FIELD-SESSION` keeps its writer-selected v3/v4/v5. This packet does not
retire or reinterpret any of those nested charts.

**Verification, September 24.** The host v1/v2 refusal test passed; five GPU-locked v3 session
tests passed for pending-emission process resume, base-prediction return, observed-next reception,
source-pair generation/reentry, and incorporation. `cargo check -p holonics-hna --all-targets -j2`
passed with existing warnings only. Exact commands and results are pinned in
`docs/VERIFICATION_RECEIPTS.tsv` against this session packet commit. No broad HNA or Phase14 suite
was run.

The current-history source, contextual lift/material transport, HNA session contract, behavior
measurement and `NormalWaveHolon` reception/actuation chart remain open; Phase 14 also remains open.
This source cut does not claim their acceptance or the final M1/M2 library layout.

## Fourth packet: organizational standing archive refusal

`OrganizationalGrammarStanding` writes the quotient fields under the existing
`OrganizationalGrammarStanding` serde name. Its writer has never emitted the retired `history`
field, but its derived read record previously inherited Serde's default behavior of silently
ignoring unknown fields. Consequently an old observation archive was accepted and discarded even
though no current writer could produce it. The reader now denies unknown fields, so a rest carrying
that retired archive is refused. This strictness is local to the organizational standing DTO; it
does not alter the writer name, schema, field set or field values. Future additions must be explicit
versioned/rest laws rather than silently discarded fields.

The former positive legacy-history fixture is replaced by a current writer roundtrip that checks
the exact serialized field set and schema, rejects the retired `history` field, and compares the
continued radiation and certificate after remount. Actual nested consumers remain
`CausalStateGrammarQuotient.state_organizations` and `OrganizationalGrammarLaw`; neither changes.
Run the focused test
`cargo test --locked -p holonic-engine --lib organizational_grammar::tests::current_standing_rest_roundtrips_and_retired_history_is_refused`.
This source/doc packet has not run Cargo yet; the focused gate is intentionally deferred while the
receiver-release gate uses the shared build resources.
