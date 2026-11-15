# Receipts: the own states' lap (G199), November 15

Device: the RTX 4080 SUPER under `.local/gpu.lock`; the host's part is the trainer's cut and deposit (one process).

- `lines.txt`: the run's own lines. These are the `own-states` tool's verdict, gate 3 with the word absent on lap 17
  (parity on 3 sections, 24 reproduced, the read byte for byte: `GATE_ENGINE EQUAL`), the own lap's and lap 17's `STORE_PASS` and
  `MEASURE` lines (the same 27,978,549 stretches read by both), and the reads' and writes' closing lines. No line carries text of
  the private store.
- The own lap: projection 2,010 s, deadline 2,400 s, wall 1,999.5 s (ratio 0.99), peak resident 350,540 KiB.
- The reads: `read-cavity` 278 s and `read-loudness` 213 s on the lap's `MEAN.3000`; each write about 50 s at run 256 and 157 s
  at run 512.
- The tables of the record (§2) were computed from `cavity.tsv` (the `P` and `W` rows' `cK`, nats = `cK / 2^20 · ln 2`), from
  `tools/loudness_table.py` on both laps' loudness reads, and from the writes' bytes by the ruler of §2. The writes and the
  loudness tables' piece lines derive from private documents and stay under `.local/`.
