# The runs behind the record

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs` at `8147a5dd7`, built on
Brandon's PC (7900X) in its own worktree in 1 min 59 s, `complete-language` its first argument, host
backend. Binary SHA-256 `1e286994a15b5a4151642791cbb9d33bbea27a7c4280fb067e84e8962bf0e3a9`. Each run
ran alone on the host (about 95% idle before each) under `timeout` at its deadline,
`RAYON_NUM_THREADS=8` (the samples one thread each), a memory ceiling of 8 GiB, inside a `wait4`
wrapper that prints `RUN_RECEIPT`. The passes also ran under the observer that stops a run when its
mean time a section passes its bound. Paths are relative to the run directory, which is not in the
repository.

```text
B found-tower-clock role_clock/copyD8/STATE SHA train_all.txt SHA UNITS SHA 8 128 role_clock/lapD.state
B read-tower-held-cells STATE SHA dev.txt SHA 8 OUT UNITS SHA
B train-unit-tower UNITS SHA train_all.txt SHA dev.txt SHA dev.roles SHA keys SHA 64 64 256 2 8 128 1 7 OUT FROM SHA
python3 -I tools/listener/bank_trace.py role train_all.txt dev.txt twin8.cells copyD8.cells lapT8.cells lapD8.cells
python3 -I tools/listener/bank_trace.py held dev.txt lapT8.cells lapD8.cells '"\n\n"'
B sample-unit-tower UNITS SHA lapD8/STATE SHA prompt_framed.txt SHA keys_sN SHA 400 OUT [2]
```

Every input matched its SHA-256: the inputs of the
[copy founding's receipts](../2026-10-26_THE_POOL_FOUNDS_THE_CLOCK_AFTER_ANY_AND_ITS_COPY_PAYS_THE_CERTIFICATE_WHILE_THE_ROLE_STAYS_UNREAD_receipts/RUN.md),
the founded pass's state `copyD8/STATE` `3551b608…b8f3`, its held-out cells `copyD8.cells`
`5e51e0a3…46fd` and the first twin's cells `twin8.cells` `d538b2c9…e8b9`.

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| 1. the founding on the founded pass's state | 47.4 s + 7.3 s + 1,311 × 149.3 ms + 10 s = 260.4 s | 261 s | 155.2 s | 0.60 | 508,640 KiB |
| 2. the opening, held-out cells from the refounded state | 10 s | 10 s | 4.4 s | 0.44 | 36,468 KiB |
| 3. the lap's twin | 1,311 × 154.0 ms + 5 s = 206.9 s | 207 s | 159.0 s | 0.77 | 384,104 KiB |
| 4. the founded lap | 1,311 × 154.0 ms + 5 s = 206.9 s | 207 s | 159.2 s | 0.77 | 382,464 KiB |
| 5. held-out cells, twin then founded | 10 s each | 10 s | 4.4 s each | 0.44 | 37,704 and 36,404 KiB |
| 5. the role and held observers | 10 s each | 10 s | 0.3 and 0.2 s | — | 47,292 and 68,268 KiB |
| 6. 16 samples, 8 at a time | 10 s each | 10 s each | 2.0 s at most, 3.4 s in all | 0.20 | 37,772 KiB at most |

- Run 1's eight streams all reported by 47.2 s against the early-stop bound of 57.4 s. Its pool read
  took 47,239 ms, its drops 7,262 ms and its moments read 1,311 sections in 100,597 ms (76.7 ms a
  section).
- Run 3's mean section was 117.6 ms and its largest window 119.1 ms (section 352); run 4's 117.8 ms
  and 118.7 ms (section 480). Neither took a halving.
- States: `lapD.state` `2f78e490365faea8524b239f6d14c73a5cd5b3db4b6d78cde9e5bed2568b919c`; the twin
  `lapT8/STATE` `c45119509c55a7a7545d4d646b93152ce12ecbcf5c0af3cf1a75d483b77735b7`; the founded lap
  `lapD8/STATE` `70c765788f02b857ed6f8b3bb7204394f4890ae241a696bed1bc12ec2b2851c0`.
- Every run exited 0. The worktree's only untracked path was its `target/`, retired by name before the
  worktree was removed.

The pool's lines are whole in [`POOL.txt`](POOL.txt), the passes' in [`PASSES.txt`](PASSES.txt),
the held-out reads in [`HELD.txt`](HELD.txt) and every sample in [`SAMPLES.md`](SAMPLES.md).
