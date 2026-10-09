# Publication note

This directory publishes the compact receipt of the native validation of the helical code's step 2,
the paired carrier (`crates/holonics/src/hnn/paired.rs`, source `083640894`, tree `5a8edd2c`).

- **Committed:** the queue's [HANDOFF.md](h-native-v1/HANDOFF.md) and
  [VALIDATION.json](h-native-v1/VALIDATION.json), the targeted test run's whole stdout (16 passed)
  and stderr (its exact readings), and `h-native-v1/FILE_HASHES.json`, which manifests every file of
  the complete packet.
- **Passed:** the all-targets check, the guard clippy, all 57 guard doctests and the 16 `hnn::paired`
  tests. Each stage has its wall time, projection, CPU and peak memory in the handoff.
- **Hashed only, not committed:** the files listed in [OMITTED.md](OMITTED.md).
- **Scope:** the structural laws of the paired carrier, the dyad moment and the current-port
  re-certification only. There is no learned-code, deposition-equivariance or damage-channel claim.
