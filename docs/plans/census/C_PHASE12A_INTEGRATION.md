# Phase 12a integration map

Source-linked integration and verification map for the HNN field/session packet. Phase 11 is
present on draft PR #108; it is not merged. The Phase 12a source cut is on
`codex/c-phase12a-current-cut`, stacked on #108. This note records its source and wire boundaries
and the measured gates below; further C-phase work remains.

## Branches and overlaps

| Work | Current source state |
|---|---|
| Phase 11 | Draft PR #108, branch tip `3587c382` on facade `3b2acef7`; not merged. Source commits `a6c0c95d`/`53e085eb` retired relation-rest v3/v1. Tests at `a6c0c95d`: engine normal 172/172, resident relation 2/2, contact 10/10; wave rest 6/6. The full HNA lib run at `a6c0c95d` was interrupted at `deposition_split_synthetic_long_control` (115 passed before interruption, 1 active, 100 not reached; no suite result). The later `53e085eb` host wave-rest gate passed 4 with two CUDA tests ignored. Exact command receipts are in `.local/p11-continuation/docs/VERIFICATION_RECEIPTS.tsv`. |
| Phase 12a | Original WIP `0ee4ea6d` remains untouched at `.local/p12a-wt`; the source transplant and current-format cut are on `codex/c-phase12a-current-cut`, based on #108. |
| M1 facade base | `codex/restructure-m1-facade`, current tip `3b2acef7`. The facade cut does not touch phase-12a source paths. |

The path intersection from the shared `5b7c89ab` base between phase 11 and phase 12a is exactly:

| Shared path | Phase 11 change | Phase 12a change | Join to preserve |
|---|---|---|---|
| [`field_session.rs`](../../../crates/holonics-hna/src/native/field_session.rs) | Adapt `attach_normal_prediction` refusal mapping to `NormalRefusal` (`map_err(|r| r.reason)`). | Release incident comparisons through `presentation.retained_shared`; pass retained shared operands into incident remount. | Keep both changes. They occupy separate hunks and serve independent owners. |
| [`native_source.rs`](../../../crates/holonics-hna/src/native/field_session/native_source.rs) | Adapt the same refusal mapping at source attach. | State that observed output is returned through contemporary field `D` and reaction material `M`; retain only the new comparison operands. | Keep the phase-11 caller fix and phase-12a return/rest contract. |

Phase 12a and the M1 facade have **zero changed-path overlap** from their shared `5b7c89ab`
base. Phase 11 draft #108 is already a descendant of facade tip `3b2acef7`; its earlier plan-file
overlap was integrated in that rebase. The Phase 12a transplant is now based on tip `3587c382`;
the two HNA files retain both disjoint sets of changes. The original WIP branch stays intact.

## Keep the phase-11 law distinct

Phase 11 owns the normal constitutive law `W H = B` in
[`constitution.rs`](../../../crates/holonic-engine/src/native_ecology/constitutive_fibre/field/material_transport/normal/constitution.rs)
and the scoped normal-wave `HolonLaw` in
[`wave/holon.rs`](../../../crates/holonic-engine/src/native_ecology/constitutive_fibre/field/material_transport/normal/direct/wave/holon.rs).
`NormalConstitution` carries storage and deposition readings; `NormalWaveHolon` supplies the exact
normal-wave step and balance. Phase 12a consumes those owners where the field reaction meets them;
it should not rebuild the normal law or restore duplicate constitutive views.

Phase 12a's [`ResidentHolonChart`](../../../crates/holonics-hna/src/native/coupled_wave/body/field/incident/holon_chart.rs)
charts a different object: the fixed generator machine, its ring Holons, helical pair-contact
junctions, and phase reception. It is used by incident `energy.rs` and `machine_receiving.rs`.
Keep that machine chart alongside phase 11's normal-wave specialization.

The chart already has host equality checks:
`the_machine_holon_is_the_interconnection_of_its_rings_and_contacts` compares the composed Holon
with a hand-assembled one, and `the_step_balance_is_the_ring_holons_advance_balance` checks the
ring step balance. Its device chart-square and full word-adjoint checks
(`the_reference_reaction_advance_lies_in_the_device_ball` and
`the_cayley_word_adjoint_pairs_with_its_central_difference`) remain ignored CUDA tests; do not
describe the full resident chart equality as gated until those run.

## One contemporary-read packet

Treat the 20-file WIP as one behavior packet because the retained operands and their readers cross
the field body, incident word, session release/remount and rest codecs.

- `FieldModel.pending` becomes `(input, condition, held, epoch)` in
  [`body/field.rs`](../../../crates/holonics-hna/src/native/coupled_wave/body/field.rs). At
  `observe`, rebuild through the current field source and reaction material, compare the target at
  that section, and return the covector through the same operands. A refusal restores the pending
  comparison. No producing `D`, reaction output or frozen receiver is retained.
- An incident comparison retains a prepared boundary or passage moments/condition and its
  declaration. `contemporary_incident_comparison_at` rebuilds the word through the current encoder,
  field and material; `incident_application` reads the returned faces through the current receiver.
  `retained_shared` is the source/session operand used when remounting the incident presentation.
- The returned law is tested by delayed-versus-immediate comparisons at the same contemporary
  constitution. Keep the state and evidence equality in
  `delayed_field_return_equals_an_immediate_return_at_the_same_constitution` and
  `public_incident_session_reads_a_delayed_comparison_at_the_contemporary_constitution`.

## Writer/reader matrix under restructure §0.2

Use the actual writer selections, not numeric order, to decide which parsers are current. The
restructure [retirement rule](../THE_REPOSITORY_RESTRUCTURE.md) says no old save-format readers or
legacy decoders.

| Payload | Writer emits now | Read disposition for the integrated packet |
|---|---|---|
| Outer `HNA-FIELD-SESSION` | `NativeFieldSavedSession::write` selects `\x03` source, `\x04` incident, or `\x05` generator (`field_session.rs`, `write`). A source scan found no other writer of `\x01`/`\x02`; those tags are read-only in `read`. | Preserve active `\x03`/`\x04`/`\x05`. Remove `\x01`/`\x02` reader branches under §0.2. Keep public field-session schema/API identifiers unchanged. |
| `NativeFieldModelRest` extension | No extension or `\x01` for the current no-pending forms; `\x04` for pending operand rest (`body/field.rs::write`). | Keep no-extension/`\x01`/`\x04`. Remove the `\x02`/`\x03` `Frozen` decode/remount branches and replace `delivered_frozen_field_comparisons_decode_to_operands_and_continue` with current-writer roundtrip/observation coverage. |
| `HNA-INCIDENT-FIELD` | The pre-12a writer emits `\x01` for no pending and `\x04` for pending moments; phase 12a's writer emits `\x01` for no pending and `\x05` for every pending operand form (`incident/rest.rs::write`). | Preserve `\x01` only for its active empty-pending form and `\x05` for pending operands. Remove `\x02` source-tape and old pending `\x04` decoders; remove the special `\x03` old-format handler (it already refuses). The base reader already refused `\x02`, so do not reintroduce that decoder. |
| Incident presentation rest | Phase 12a writes no frozen pending presentation cuts; shared source/request data is in the current session operands. | Remove `IncidentPendingRest`'s `frozen_text`, `frozen_support`, cohort and encoded-row reader. Do not retain the `a_pre_12a_incident_session_wire_decodes_and_continues` old-layout test. |
| Outer normal-wave rest (adjacent R4 gate) | Current facade tip writes normal v1/v2/v3/v4 by seed/epoch, v6 for applied transport, v11 for one-cut pending; coupled v7/v9/v10. | Preserve these writer-emitted forms, including v6 Applied. The current reader's coupled v8 branch has no writer in this source cut; audit its historical producer/consumer before phase 12b decides it. Do not remove versions just because their number is lower. |
| Phase-11 normal-wave relation rest | Current phase-11 branch keeps the current v2/v4/v5 relation-rest forms; the v1 and v3 reader paths are being retired in commits `a6c0c95d` and `53e085eb`. | Preserve current writer forms and the stable HNA wire name; do not reintroduce v1/v3 readers when rebasing phase 11. |

The exact set of current outer field-session writer constants is limited to the three selected by
`NativeFieldSavedSession::write`; `MAGIC` (`\x01`) and `REGIONS_MAGIC` (`\x02`) occur only in the
reader. This source inspection confirms no other current Rust writer emits the outer v1/v2 tags.
Do not change application-level `hna` identifiers or current schema names while retiring these
read-only branches.

## Tests to keep or replace

- Keep the current-writer delayed/immediate tests and the `ResidentHolonChart` host equalities.
- Replace `delivered_frozen_field_comparisons_decode_to_operands_and_continue`,
  `a_pre_12a_incident_session_wire_decodes_and_continues`, the frozen-wire subcase of
  `delayed_boundary_comparison_equals_an_immediate_one_and_the_frozen_wire_decodes`, and
  `a_retired_source_tape_decodes_to_the_moment_of_its_rows` with tests of current `\x04` field
  operand rest / `\x05` incident operand rest across process-exit remount, plus refusal of old
  frozen/tape tags. Retain a no-pending `\x01` incident roundtrip because the current writer still
  emits it.
- `original_one_pass_field_model_remains_readable` must be tied to a current-writer-produced
  no-pending rest; a checked-in old fixture alone is not evidence that §0.2 permits its decoder.
- The phase-11 HNA lib run at source/test commit `a6c0c95d` was interrupted during the 70-minute
  `deposition_split_synthetic_long_control` probe. Do not rerun that probe automatically. After
  phase-12a source integration, run the focused body/incident/field-session tests for contemporary
  reads, current-format rest and chart equality. Broader HNA, workbench/all-target and remaining
  GPU acceptance gates are still owed; schedule them separately when resource-appropriate rather
  than treating this map as an automatic full-suite run.

## Implemented source cut and measured gates

The current cut retains field comparison operands and reconstructs each comparison through the
contemporary field source and reaction material. Field rest writes no pending extension or the
current `1`/`4` forms; readers for frozen extensions `2`/`3` and their migration test are gone.
Incident rest writes `\x01` only with no pending comparison and `\x05` for pending boundary or
moment operands. The read-only frozen word, source tape, old moment and accumulated-anchor tags,
their test fixture writers and the tape-conversion helper are removed. The presentation no longer
reads frozen per-comparison encoder/receiver cuts; the retained shared request remains in the
session. The outer session reader accepts its writer-selected `\x03`/`\x04`/`\x05` forms and
refuses read-only `\x01`/`\x02` forms. No public HNA identifier or current schema name changed.

The focused HNA test binary compiled and thirteen selected tests passed: two host old-tag
refusals; three current field/passage/session rest roundtrips; four delayed or solver-return
checks; two host Holon interconnection/balance equalities; and the device reaction-ball and
word-adjoint checks. `cargo check -p holonics-hna --all-targets` passed, covering examples and
test callers of the removed helpers. Exact commands and logs are in the verification TSV. This
is a focused source-cut return; the Phase 12a handoff's remaining ladder/disposition/exposure
work and later C/M1/M2 acceptance stay open.
