# Publication note

This directory publishes the compact receipts of the scoped native validation of the retained-release
candidate (the [online-learning record](../../../2026-10-10_ONLINE_LEARNING_OF_A_RINGS_SECTION_WORD_ON_ITS_LOCATED_FIELD.md)
§15; Refs #73 #386 #148).
- Tested source `e0d0c499e41ebdbbe9b62ae9d0904c4e1daefe8f`, tree `be83839ba96f4b9f47f3cd29b43aa8beb83d73c9`,
  from a whole-tree immutable archive, unchanged before and after.
- Published with the record-only correction `099b1d2212280907477824693fd35e6054dbc427`, tree
  `6e38c26b722724e67774a2892f459e5b71328981`. It changes one record, §13's stage ranges, and no source, so it is
  not the tested tree ([RECORD_ONLY_SUCCESSOR.json](RECORD_ONLY_SUCCESSOR.json)).
- **Passed** ([handoff](HANDOFF.md), [validation](VALIDATION.json)): gate (63 guard doctests, the workspace check,
  the declared law lints), `acoustic_encoding` 11, receiving 38, source entrance 5, and one exterior Contact
  declaration fixture.
  - The Contact fixture distinguishes six unreduced bound declarations, including `(1, 2)` and `(2, 4)`.
  - It corrects an overly broad inference in the preserved core receiving readout
    ([CONTACT_SCOPE_CORRECTION.json](CONTACT_SCOPE_CORRECTION.json)).
- **Stages.** Each stage passed, was quiescent and was released within its fixed projection. No limit was raised.

| Stage | Command wall ns | Projection ns | Group CPU ns | Child RSS KiB | Charged group peak B | Exit |
|---|---:|---:|---:|---:|---:|---:|
| `gate` | 101684960304 | 152151901055 | 197163635000 | 1713604 | 2147536896 | 0 |
| `acoustic` | 106089978867 | 194961654253 | 244904004000 | 1801256 | 2016620544 | 0 |
| `receiving` | 69290079072 | 140266475475 | 142236762000 | 2716920 | 2965262336 | 0 |
| `source` | 2670718052 | 209192238203 | 6360568000 | 734496 | 923729920 | 0 |
| `contact` | 1087055881 | 116022238203 | 2755489000 | 713644 | 434614272 | 0 |

- **Failed attempts, preserved** (none replaced):
  - the first export put helper files in the source directory, and the strict membership preflight refused it
    before any native start ([PRIOR_ATTEMPT.json](PRIOR_ATTEMPT.json));
  - the second, partial export omitted the notebook example and include paths
    (`research/notebook/hnn_design/`), so its gate failed and the affected checks were skipped
    ([FAILED_GATE_ATTEMPT.json](FAILED_GATE_ATTEMPT.json); the repair, [MATERIALIZATION_REPAIR.json](MATERIALIZATION_REPAIR.json));
  - the supplemental Contact output path collided with a preserved core log, and exclusive open refused it before
    any lease or native start ([CONTACT_LAUNCH_FAILURE.json](CONTACT_LAUNCH_FAILURE.json)).
- **Scope** ([consumer scope](CONSUMER_SCOPE.json), [definitions](CONSUMER_DEFINITION_BINDINGS.json)):
  - conditional exact reconstruction of the 120-sample tone window from a supplied, uncharged, prefix-only
    `ToneContext` and the delimited stream (703 bits = 9 framing + 25 class code + 669 sample-index fibre);
  - O3 on the frozen-prefix period-7 family, with the four declaration-inclusive charged C3 comparisons;
  - the retained advance law and its pre-mutation refusals;
  - M2 as stage accounting only.
- **Not claimed:** complete-cost compression, unrestricted production, a receiving-comparison certificate, or
  unseen-family discovery. Strict all-target Clippy remains unresolved: the gate checks only its declared lints,
  and no all-quality-checks claim is made.
- **Projection.** Every JSON here except the verbatim files is an allowlisted projection
  ([ORIGINALS.json](ORIGINALS.json) binds each original by size and SHA-256). Each dropped or reduced key is listed
  in [PROJECTION_EXCEPTIONS.json](PROJECTION_EXCEPTIONS.json), as is each packet file name whose cargo
  metadata-hash suffix is written as `<cargo-hash>`. The other 247 files of the packet are listed in
  [OMITTED.md](OMITTED.md).
