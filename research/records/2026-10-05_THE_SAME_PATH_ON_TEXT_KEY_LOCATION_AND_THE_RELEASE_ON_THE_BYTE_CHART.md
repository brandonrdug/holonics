# The same path on text: key location and the release on the byte chart

**Date.** October 5. **Issues.** #73, #148, #63. **Lanes.** B and C of U6 (THE_REBUILD, "U6's order
from October 5"), on text. **Grade.** [measured] for every count below (the runs of
`2026-10-05_THE_SAME_PATH_ON_TEXT_receipts/runs.sh`, at this record's commit); [agent-inferred] for the
pins.

**Occasion.** Lanes B and C passed U6 step 1 on order-2: the turn menu located the key from 16
observations, the certified step deposited it, and the release read it on equal material, 128 of 128
sections whole on the final confirmation
([B](2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md),
[C](2026-10-05_THE_RELEASE_READS_THE_LOCATED_PAIR_ON_EQUAL_MATERIAL.md)). The plan requires every loop
to show Brandon a text release, and none has been shown since September 29. This loop runs that same
path, with no new machinery, on a passage of real text, and shows what it releases.

The computational object is the helical pair interaction. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this loop reads **the helix**
(a distance is a residue of the source ring's clock), **the pair** (two crossings `δ` ticks apart, the
menu's edge) and **faces and placement** (the ring's ports, the residue chart `code mod 60`, and the
bank's reading of each candidate's placement); the cell holonomy (the menu's loop law), the tube and
the tower thread stay attached and unchanged.

## 0. The claim and the pins, fixed before any run

**The claim.** The deliverable is the measurement and the output, not a pass: the turn menu's
survivors by distance on a text passage, and one release per request, shown whole with its copy
length (guard 19). No acceptance is claimed.

**The data** [agent-inferred]. The U6 conversation split's choosing role, its flat cut
(`.local/cuts/curated-u6-choosing-flat-cut.bin`, sha256 `eab73259…5dd2`, 523,215 bytes; development
partition, the reserve excluded by its manifest, the evaluation partition outside the stream). The
validation role and every spent split's validation role are not read.
- **The training passage**: the cut's bytes `[0, 6144)`, read as 128 consecutive windows of
  `n + m = 48` bytes, each a request of 40 cells and its section of 8 stations: the order-2 terrain's
  training shape, `1,024 = 2¹⁰` observations.
- **The requests**: 16 windows of 48 bytes in the cut's held-out range `[457751, 523215)`, the `i`-th
  at `457751 + 4091·i` (`4091 = ⌊65464/16⌋`), each a request of the last 40 bytes and its truth, the
  next 8. They are disjoint from each other and from the training passage; no run of this loop
  reads them before the pinned run. (The September 29 text runs read this cut, with other machines;
  nothing of them enters this one: every state here is the declared opening or its deposit.)
- **The development window** (timing only): the bytes `[6144, 6192)`, the window after the training
  passage.

**The field** [agent-inferred]. The order-2 declaration unchanged (`hnn_prediction.rs`,
`order_declared`: three rings of period `60 = 2²·3·5` in a chain, ring 0 the source and receiving
ring, `K = 2`, `w = 1`, `m = 8`, `n = 40`, the bank at `p = 5/8` read at `2^(−16)`), with the exterior
chart the byte chart: `|A| = 257`, the bytes `0 … 255` and the termination `256`. The ring's ports are
its residue chart, `port(x) = x mod 60` (guard 9), so each port holds four or five bytes. `Field::declare`
fixes the rings without the alphabet, so the field is the one step 1 read.

**The path.** `executed text <cut> <out> run` (`hnn_keys_loop.rs`): lane B's location
(`hnn::keys::{station_pairs, PairLocation}`, every distance `δ ∈ [1, 59]` its span reaches), each
distance's menu followed to the observation at which it fails; at a first lock, `pair_deposit` on both
openings and the release on the deposits; with no lock, the release on the lossless and the founded
openings (`generate_by_bank`, lane C's owner, unchanged). Beside it, a terrain-side reading only: the
same edges on the bytes themselves (a turn menu a distance on 256 ports), separating the residue
chart's fold from the passage's own relation. The released stations are decoded to bytes through the
byte chart; each release's copy length (`tools/copy_length.py`) is read against the training passage
and against its own request. Every byte is written only to the worktree's `.local/text_loop/`.

**Thread budget** 12 (`RAYON_NUM_THREADS=12`).
