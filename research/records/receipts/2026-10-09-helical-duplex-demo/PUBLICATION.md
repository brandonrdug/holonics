# Publication note

This directory publishes the compact receipt of the native helical duplex example,
`crates/holonics/examples/helical_duplex.rs` (source `9e8041d0a`, tree `c09bbaa2`). It is a
fixed-key, known-truth calibration of the accepted `compression::keys::duplex` owner, and makes no
learned-repair claim.

- **Committed:** the queue's reviewed [HANDOFF.md](native-v1/HANDOFF.md) and
  [VALIDATION.json](native-v1/VALIDATION.json), the whole smoke stdout and stderr (the stderr keeps
  the library's three existing dead-code warnings), and `native-v1/FILE_HASHES.json`, which
  manifests every file of the complete packet.
- **Hashed only, not committed:** the files listed in [OMITTED.md](OMITTED.md), which were not
  reviewed for publication.
- **The complete local packet** remains untracked under the main checkout's
  `research/records/receipts/2026-10-09-helical-duplex-demo/`.

The command is `cargo run -p holonics --example helical_duplex`. The handoff gives its measured
resources, and the queue's text describes the complete local packet as "preserved here".
