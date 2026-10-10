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

## The cell codec, the inverse tick and the octant grain (October 10, second packet)

**Accepted sources** (queue receipts below):
- `ec1b950ad056082a252e750d01775a6b81cb81c7`: the emitted cell codec and its independent decoder,
  with its receipt-only successor `291845a0`;
- `4776faecb2d667dee4c645d8a5628ad3b5a499ba`: the ring's inverse tick, with its admission repairs
  (a charted solve refused; the canonical carry `[−δ/2, δ/2)`; the recovered rate on the lattice);
- `39304646ee8b3e6f4aa7f7c57f22b322afaf6acc`: the octant grain.

The published history carries their public replay ([replay map](REPLAY_CODEC.md)). Each replayed
commit equals its original except the one receipt line naming the private input. The octant's
wording correction is applied on top.

**Scope.**
- Encoder-produced bytes only: `codec_decode(codec_encode(x)) = x` with the sample and the rate
  equal. Malformed, truncated, reserved, out-of-range-index and trailing-data inputs are not
  validated.
- The ring, the law, the rest state and the grains are declared, shared context.
- The margins against `16 · N` (quarter turn: 1481048 bits; octant: 1364296 bits; both against
  1498880) are the section grain's narrowing against the uniform samples' slack, not learned content.
- No `Encoding` or repair join, adaptive learning or joint credit is claimed.
- The earlier arithmetic-cost failures stand: the declared bank's emission keys cost 3872041 bits, and
  after the clock repair 2455192 bits, 2343116 without the quadrature's zeros, all above 1498880.
- §16's interval pass is containment only, with estimated lengths.

**Failures and custody limits, kept as they happened.**
- The first inverse (`11142433`) admitted a charted solve and did not check the carry contract. Its
  tests passed without exercising either. Both were repaired (`4439785b`), and the half-open carry
  and the lattice rate were repaired after them (`4776faec`).
- §16 first claimed a lossless decode that was not built. It was corrected (§18) before the codec
  existed.
- A developer gate overlapped an edit to the example; it is not cited.
- The developer binary that ran the codec was overwritten in the shared target, so only its source
  and build log bind it.
- The developer octant run exceeded no deadline. The interval run exceeded its projection's upper
  end (228710618817 ns against 190 s, within its 300 s deadline), which is reported as the
  projection's error.
- Strict all-target clippy remains FAILED (exit 101), without a waiver. No equivalent failure set on
  the parent has been proved, and none is claimed.

**The queue's receipts.**
- **`ec1b950a`.** Gate (63 doctests), 24 wave-port tests, a fresh exact-source build, and one full
  codec consumer: every sample and the rate equal after the independent decode of the actual byte
  vector from rest. 185131 bytes, 1481048 charged bits, with the 69-bit header and the padding
  included. `VALIDATION.json` SHA-256 `232b054889df4b78ba81e76abc97e2ebe6d03a6f6a61a94387db5787ca214fba` ([projection](codec-ec1-native-v1/)). The codec's wall
  time, 899375716205 ns, exceeded its 441987128832 ns projection, with no limit raised. The cause
  was the queue's own guard sharing the pinned core.
- **`4776faec`, with the octant `39304646` byte-identical.** Gate (63), the three affected inverse
  fixtures (edges, refusals, round trip), a fresh build, and one full octant consumer: every sample
  and the rate equal. 1364296 charged bits, with the 70-bit header (the octant flag included) and the
  padding. `VALIDATION.json` SHA-256 `45af774ba651ed2ddf3ebf9b25c1574bd87d817ac9179c05cd20617dad20a511` ([projection](inverse-octant-4776-native-v1/)). The
  general inverse API beyond its fixtures is not accepted.

**Projection of the queue's receipts (allowlisted).** Each projection keeps only declared evidence,
reading and custody fields. Nested values survive only as booleans, integers, exact rationals,
commit and tree identifiers, or SHA-256 bindings. Keys naming argv, environment, paths, mail,
threads, messages, reviewers or process identifiers are dropped, and any other hex identifier is
refused. `HANDOFF.md` is verbatim. `ORIGINALS.json` binds every private original by size and SHA-256.
This replaces a first projection, never published, which copied arbitrary metadata and filtered it
afterwards, and so carried one private mailbox identifier. The developer binary that ran the codec is
not retained (it was overwritten in the shared build target). It is bound by its source,
`ec1b950ad056082a252e750d01775a6b81cb81c7`, and by its build log, SHA-256
`34534b7cb9b7816b0e997c49e6c13c637c30a95293794179b405a67a0ac361b6`.
