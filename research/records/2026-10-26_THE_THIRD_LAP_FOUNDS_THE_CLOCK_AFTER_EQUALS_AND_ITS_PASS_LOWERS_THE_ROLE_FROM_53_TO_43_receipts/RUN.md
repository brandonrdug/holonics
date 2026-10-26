# The runs behind the record

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs` at `9b915dbe1` (the code
of `8147a5dd7`; only records differ), built on Brandon's PC (7900X) in its own worktree in 1 min
58 s, `complete-language` its first argument, host backend. Binary SHA-256
`8d9ac1839ce414c84c07f3b0ea745d891703b6616c7990c58fef75de19db7b51` (the second lap's build from
another worktree path read `1e286994…e3a9`). Each run ran alone on an idle host under `timeout` at its
deadline, `RAYON_NUM_THREADS=8` (the samples one thread each), a memory ceiling of 8 GiB, inside a
`wait4` wrapper that prints `RUN_RECEIPT`. The passes also ran under the observer that stops a run
when its mean time a section passes its bound. Paths are relative to the run directory, which is not
in the repository.

```text
B found-tower-clock role_clock/lapD8/STATE SHA train_all.txt SHA UNITS SHA 8 128 role_clock/lap3D.state
B read-tower-held-cells STATE SHA dev.txt SHA 8 OUT UNITS SHA
B train-unit-tower UNITS SHA train_all.txt SHA dev.txt SHA dev.roles SHA keys SHA 64 64 256 2 8 128 1 7 OUT FROM SHA
python3 -I tools/listener/bank_trace.py role train_all.txt dev.txt twin8.cells copyD8.cells lapD8.cells lap3T8.cells lap3D8.cells
python3 -I tools/listener/bank_trace.py held dev.txt lap3T8.cells lap3D8.cells '"="'
B sample-unit-tower UNITS SHA lap3D8/STATE SHA prompt_framed.txt SHA keys_sN SHA 400 OUT [2]
```

Every input matched its SHA-256: the inputs of the
[second lap's receipts](../2026-10-26_THE_SECOND_LAP_FOUNDS_THE_BLANK_LINES_CLOCK_AND_THE_ROLE_IS_READ_IN_53_OF_97_WHILE_JOHN_STAYS_UNANSWERED_receipts/RUN.md),
its founded state `lapD8/STATE` `70c76578…51c0` and the cells `lapD8.cells` `44539a70…d16b`,
`lapT8.cells` `fef905ad…3b95`, `copyD8.cells` `5e51e0a3…46fd` and `twin8.cells` `d538b2c9…e8b9`.

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| 1. the founding on the second lap's state | 47.4 s + 7.3 s + 1,311 × 149.3 ms + 10 s = 260.4 s | 261 s | 155.4 s | 0.60 | 508,048 KiB |
| 2. the opening, held-out cells from the refounded state | 10 s | 10 s | 4.4 s | 0.44 | 37,032 KiB |
| 3. the lap's twin | 1,311 × 154.0 ms + 5 s = 206.9 s | 207 s | 159.0 s | 0.77 | 383,000 KiB |
| 4. the founded lap | 1,311 × 154.0 ms + 5 s = 206.9 s | 207 s | 159.3 s | 0.77 | 382,720 KiB |
| 5. held-out cells, twin then founded | 10 s each | 10 s | 4.4 s each | 0.44 | 36,064 and 36,792 KiB |
| 5. the role and held observers | 10 s each | 10 s | 0.3 and 0.2 s | — | 47,072 and 68,364 KiB |
| 6. 16 samples, 8 at a time | 10 s each | 10 s each | 0.4 to 1.9 s | 0.19 at most | 37,744 KiB at most |

- Run 1's eight streams all reported by 47.2 s against the early-stop bound of 57.4 s. Its pool read
  took 47,259 ms, its drops 7,255 ms and its moments read 1,311 sections in 100,789 ms.
- Run 3's mean section was 117.6 ms and its largest window 118.6 ms; run 4's 117.9 ms and 119.7 ms.
  Neither took a halving.
- States: `lap3D.state` `ee050e22df3d984eb25ca38656e8c867055e2d4789590e6f45438899260016f2`; the twin
  `lap3T8/STATE` `3331784425b940522736c535c8035d6b6fc23d531fb122d19c46d5cffc0ef6be`; the founded lap
  `lap3D8/STATE` `5118c9d525f7121c9085e0458e045f05b3eaea037a2e7ccd9ed6ac0fc0b52599`.
- Every run exited 0. The worktree's only untracked path was its `target/`, retired by name before the
  worktree was removed.

The pool's lines are whole in [`POOL.txt`](POOL.txt), the passes' in [`PASSES.txt`](PASSES.txt),
the held-out reads in [`HELD.txt`](HELD.txt) and every sample in [`SAMPLES.md`](SAMPLES.md).
