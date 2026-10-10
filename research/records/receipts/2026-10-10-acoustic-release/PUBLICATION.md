# The acoustic first rung's publication (October 10)

**Accepted pin.** `aaf174102341214d5cdb1cdee5ea84a862cac870`, tree
`dd644a63c29f124705e8f2d29520516ea547ebe4`, with its documentation-only correction
`04ac5e43c68b9ef6a842d7695dbc251f999209d3`, tree `b2817e695d7eff127192722cbd382608cef9bb4e`. The
correction makes A2's gain maximal under the declared headroom ceiling and states the rung's proved
scope; all code is identical. Queue receipt `VALIDATION.json`, SHA-256 `d3d2962516d0df398be88e137270d6355d8f063b8a21915dea1e9d39b18c3388`
([projection](bank-aaf-native-v1/)).

**Public replay.** The published history carries the replay of these two commits, identical except
one receipt line that named the private input's path ([replay map](REPLAY.md)).

**Passed at the queue.** Gate 1 with 63 doctests, the 17 wave-port tests, a fresh build of the
example, and the complete 24-ring render of the private recording. Every tick and every whole-stream
balance closed.

**Failures kept as they happened.**
- The developer gate first FAILED on guard 7: the example's file reads lacked the exterior
  boundary's allowance. Its raw log is retained locally, and the rerun passed
  ([receipt](TESTS_AND_GATE_FAILED.v1.json)).
- The developer render ran on a binary built before the two allow attributes. The queue's fresh
  build closes that difference.
- Strict all-target clippy remains FAILED (exit 101), without a waiver. No equivalent failure set on
  the parent has been proved, and none is claimed.
- Developer reads stay developer reads.

**Scope.**
- The bank and the PCM grain are fixed.
- The chunk equivalence holds with a shared gain and continued state.
- The whole window's PCM remainder is the summed quantization error.
- The render is the declared bank's emission. It is not a learned generation, not a decoder of
  located keys, and not a reconstruction of the source.
- The recording and the render stay private and local. No audio is published.

**Projection.** `HANDOFF.md`, `EXACT_READINGS.json` and `RENDER_DERIVED_ACCEPTANCE.json` are
verbatim. `VALIDATION_SUMMARY.json` and `ACOUSTIC_READOUT.json` drop argv, environment, paths (every private
`.local` path, including the recording's) and identifiers. The originals are pinned in [`ORIGINALS.json`](bank-aaf-native-v1/ORIGINALS.json),
including the private render's hash.
