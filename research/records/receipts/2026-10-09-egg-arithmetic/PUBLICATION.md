# Publication note

This directory publishes the compact receipt of the kernel check of
`lean/HolonicsResearch/Geometry/EggModular.lean` (source SHA-256 `d17596df`, 14,166 bytes), which
adds `egg_to_fullTwoTorsion` and its concrete consumer `egg_321_fullTwoTorsion`. Queue label:
`egg-two-torsion-20261009-v136-compile`.

- **Committed:**
  - the queue's [HANDOFF.md](native-v1/HANDOFF.md) and [VALIDATION.json](native-v1/VALIDATION.json);
  - `native-v1/admission/KERNEL_VALIDATION.json`;
  - the compiler's whole stdout, with all eleven `#print axioms` results, each only `propext`,
    `Classical.choice` and `Quot.sound`, and its empty stderr;
  - `native-v1/FILE_HASHES.json`, which manifests every file of the complete packet.
- **Hashed only, not committed:** the files listed in [OMITTED.md](OMITTED.md).
- **Scope:** the module alone was checked, not the full research root. The accepted claim is the
  affine equation transport (`b ≠ 0`) and the `a=3, b=2, w=1` equation. It makes no claim to the
  projective or group map to `GeneralFace.E`, the prime-11 counts, BSD, or a mass gap.
- **The complete local packet** stays untracked under the main checkout's
  `research/records/receipts/2026-10-09-egg-arithmetic/`.

## The point and descent consumer

`lean/HolonicsResearch/EllipticCurve/EggSource.lean` constructs the actual egg point in the existing
`GeneralFace.E (-(a-w)^2) (-(a+w)^2)` point group and consumes the existing doubling/descent theorem.
The sole queue checked two pins of it.

- **Rejected, [point-descent-native-v1](point-descent-native-v1/HANDOFF.md).** Pin `f78070c8a`,
  source SHA-256 `07d84474`, 8,142 bytes, queue label `egg-point-descent-20261009-v138`. Compiler
  exit `1` after `5,517,855,699 ns`; complete compile stage `7,558,736,932 ns` under the
  `21,132,554,884 ns` projection. All six queries were reached and two depended on `sorryAx`. The
  whole stdout names the diagnostics: a missing separator at line 121, an unfolded constructor at
  line 159, and the unqualified `RankIsOn` at lines 165 and 170.
- **Accepted, [point-descent-native-v2](point-descent-native-v2/HANDOFF.md).** Repair pin
  `896a325f0`, source SHA-256 `b3c37f28`, 8,133 bytes, queue label
  `egg-point-descent-repair-20261009-v145`, written October 9 at 04:54 UTC. Compiler exit `0`,
  compiler wall `10,073,507,353 ns`; complete compile stage `12,236,369,152 ns` under the unchanged
  `21,132,554,884 ns` projection; aggregate CPU `6,987,427,000 ns`; group peak
  `5,120,466,944 bytes`; child peak RSS `4,015,440 KiB`. All six `#print axioms` results are only
  `propext`, `Classical.choice` and `Quot.sound`. The one remaining linter note
  (`unnecessarySeqFocus`, line 171) is not a diagnostic of a claim. The admitted
  `EggModular.lean` is the published one, SHA-256 `d17596df`.
- **Committed for each pin:** HANDOFF.md, VALIDATION.json, `admission/KERNEL_VALIDATION.json`, the
  compiler's whole stdout and its empty stderr, and FILE_HASHES.json, which manifests the complete
  packet. The other 203 files of each packet are hashed in that pin's `OMITTED.md`
  ([v1](point-descent-native-v1/OMITTED.md), [v2](point-descent-native-v2/OMITTED.md)).
- **Not committed:** the queue's failure-owner ledger
  `2026-10-09-native-queue-batch/admission-v1/FAILURE_OWNER_LEDGER.v2.json` (SHA-256
  `881bb7a8822576694537a107f12431880f7c55bd9667b2174a45d7e4badfcafd`), which also carries other
  lanes' rows. Its egg row names notification `b46566a79091467d8fd4d28e094d559a` and the same
  diagnostics as the v1 stdout above.
- **Scope:** the module alone was checked, not the full research root. The accepted claim is the
  affine point and its doubling-to-descent join, the nonzero-`X` inverse chart, the classification
  of the source's infinity points, the explicit `(0,0)` assignment to the second one and its
  two-torsion, and the rank bound on the receiving model `E(-4,-16)`. It makes no claim to a
  projective or group equivalence with the original source, to a regular extension at the
  exceptional points, or to a rank of the original source group (#62). The receiving-model bound
  assumes no BSD conjecture; the prime-11 counts stay a displayed table, not a formal claim.
