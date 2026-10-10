# Publication note

This directory publishes the receipts of the acoustic second rung:
- [the matched wave and the dynamic section](../../2026-10-09_A_MATCHED_WAVE_ENTERS_A_LOADED_RING_AND_ITS_STATE_CROSSES_ITS_OWN_SECTION.md);
- [the located period](../../2026-10-09_A_TONES_PERIOD_IS_LOCATED_NOT_DECLARED.md).

Refs #148 #73. The validated source is exactly `87082a1e` (tree `8c514590`).

The published history replays its eight commits with one change: the host path in the second line of
`native_runs.txt`, which now reads `<repository>`. The replayed tree differs from `8c514590` only
there. `native_runs.txt` and the `replica*`, `lock_predictions*` and `symbol_word_prediction*` files
are developer reads, not claim-bearing.

| Packet | Pin | Result and scope |
|---|---|---|
| [acoustic-8708](acoustic-8708-native-v1/HANDOFF.md) | `87082a1e` | Four scoped commands PASS. The gate covered the check, three guard lints and 63 doctests. The test suites passed `acoustic_wave_port` 15, `dynamic_section` 6 and `section_lock` 10 ([summary](acoustic-8708-native-v1/VALIDATION_SUMMARY.json)). |
| [aeeb hold](acoustic-8708-native-v1/AEEB_HOLD.json) | `aeeb0ee8` | The independent review's hold. Both WavePort repairs had source GO, but the public section word admitted a forged crossing. No compiler ran on this pin. |

**Failures kept with this work:**
- The polarity reading's first failure is in record §4.5.
- The signed stiffness and the scalar reflected value are in §13.
- The forged public word, and the original joint-test fixture that was itself a forged word, are in §14.
- The strict all-target clippy run (`-D warnings`, a developer run stricter than the gate's guard lints) FAILED with exit 101. Its primary diagnostic locations lie in 91 files the repair did not touch. That is not a waiver, and an identical failure set on the parent is not proved. Its log and receipt are bound by hash in [`ORIGINALS.json`](acoustic-8708-native-v1/ORIGINALS.json).

**Limits that stay in force:**
- A lock is a repetition inside a declared finite window of a declared bank. It is not a proof that the steady state is periodic beyond the window, and not a located cause.
- The quarter-turn grain does not resolve phase inside a quadrant.
- A section symbol carries no receiver, clock or subtick placement.
- A ring's own symbol word is not a located route on its helix, so no strand is located.
- Transcript association is not established.

**Projection.** `HANDOFF.md`, `ACOUSTIC_READOUT.json` and `WAVE_GUARD_COVERAGE.json` are the queue's
own files, byte for byte. `VALIDATION_SUMMARY.json` and `AEEB_HOLD.json` are compact summaries
written from the queue's private originals, copying their values and omitting host paths, argv,
environment, mailbox and harness identifiers. `ORIGINALS.json` pins every private original by size
and SHA-256. The originals stay in local custody.
