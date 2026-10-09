# Publication note

This directory publishes the compact receipt of the kernel check of
`lean/Holonics/Transport/DeletionReceiver.lean` (source `d5f7c140b`, SHA-256 `e391c76f`, 925 lines) and of its import into
`lean/HolonicsResearch.lean`.

- **Committed:** the queue's [HANDOFF.md](native-v1/HANDOFF.md) and [VALIDATION.json](native-v1/VALIDATION.json),
  `native-v1/FILE_HASHES.json`, and for both the owner compile and the import compile the whole compiler stdout and
  stderr and `KERNEL_VALIDATION.json`. The ten queried laws report only standard axioms; the 90 warnings are unused
  fallback tactics.
- **Hashed only, not committed:** the files listed in [OMITTED.md](OMITTED.md).
- **Scope:** the deletion receiver's exact finite laws (the clock, moment, transport, channel composition, likelihood and
  covector identities). The full `HolonicsResearch` library was not built. No native receiver or learned reconstruction
  is claimed.
