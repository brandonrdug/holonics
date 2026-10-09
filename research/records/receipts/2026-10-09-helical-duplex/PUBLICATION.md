# Publication note

This directory publishes a part of the sole validation queue's receipt for the native duplex consumer, accepted at `02658c6c2` (native-v2); the first seal `c6fcc82a1` was never executed.

- **Committed here:** the queue's small structured receipts and logs. These include the complete
  raw compiler or runtime stdout and stderr, the selectors and requests, the time, memory, cleanup
  and release records, and each packet's `FILE_HASHES.json`, which manifests every file of the
  complete packet by SHA-256. Small consuming query sources are committed with them, such as an
  import-smoke consumer.
- **Hashed only, not committed:** the files listed in [OMITTED.md](OMITTED.md). These are compiled
  objects, import seals, large or binary files and copies of git-tracked source. Their bytes are
  not supplied here; only their hashes are, in `FILE_HASHES.json`.
- **The complete local packet** stays where the queue wrote it, untracked, under the main
  checkout's `research/records/receipts/2026-10-09-helical-duplex/`.

The queue's own texts ([native-v2/HANDOFF.md](native-v2/HANDOFF.md) and `VALIDATION.json`) are historical receipts written before
publication. Where they say the files are "preserved here" or "local and uncommitted", they
describe that complete local packet.
