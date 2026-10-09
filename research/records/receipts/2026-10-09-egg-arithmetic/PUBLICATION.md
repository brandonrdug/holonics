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
