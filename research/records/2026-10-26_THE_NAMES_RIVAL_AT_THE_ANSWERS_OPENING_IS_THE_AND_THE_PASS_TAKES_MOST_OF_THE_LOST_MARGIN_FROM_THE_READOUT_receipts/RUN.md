# The runs behind the record

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs` at `dff592a16`, built on
Brandon's PC (7900X) in its own worktree in 1 min 59 s, `complete-language` its first argument, host
backend. Binary SHA-256 `d063352416288d5992b7e2649f6b0cb2460980f86344b8fbf3ead18cca2d9e6c`. Each run
ran alone on an idle host under `timeout` at its deadline, `RAYON_NUM_THREADS=8`, a memory ceiling of
8 GiB, inside a `wait4` wrapper that prints `RUN_RECEIPT`. Paths are relative to the run directory,
which is not in the repository.

```text
python3 -I tools/listener/bank_trace.py requests train_all.txt TEXT role_clock/copies/{train,dev}.requests
B read-tower-clock-cells role_clock/S/STATE SHA TEXT SHA UNITS SHA 8 REQUESTS SHA role_clock/copies/S.{train,dev}.copies
python3 -I tools/listener/bank_trace.py copies train_all.txt TEXT UNITS role_clock/copies/{lapD8,lap3T8,lap3D8}.{train,dev}.copies
```

Every input matched its SHA-256: `train_all.txt` `050b94f3…3b95`, `dev.txt` `e5bffe0e…3153`, the units
`d0973c39…782a` and the states `lapD8` `70c76578…51c0`, `lap3T8` `33317844…f6be` and `lap3D8`
`5118c9d5…2599`.

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| 1. the requests, training text and held out | unmeasured, planned at 10 s | 10 s each | well inside, not timed apart | — | — |
| 2. the copies on the training text, three states in turn | 38.3 s (the largest held-cells read of the same partition) | 42 s | 37.6, 37.6, 37.7 s | 0.98 | 107,344 to 107,732 KiB |
| 3. the copies held out, three states in turn | 4.4 s | 10 s | 4.3, 4.3, 4.4 s | 0.98 to 1.00 | 34,016 to 34,096 KiB |
| 4. the observer, training text then held out | unmeasured, planned at 60 s and 10 s | 60 s, 10 s | 0.18 s, 0.11 s | — | — |

- The requests: `train.requests` `78528683…9d56` (4,524 named problems), `dev.requests` `86600c2c…5236`
  (421).
- The copies files: `lapD8.train.copies` `c5c77835…3479`, `lap3T8.train.copies` `d7cf4a80…3460`,
  `lap3D8.train.copies` `a25007cd…7d92`, `lapD8.dev.copies` `a36800ea…21d0`, `lap3T8.dev.copies`
  `ecdf9822…db73`, `lap3D8.dev.copies` `f6cce4de…02a4`, held with the training text's places off the
  repository.
- The check held: each copies file gives the first unit the largest mass in as many answers as the
  role read from the same state (695, 561, 599 on the training text; 53, 37, 43 held out).
- The first build attempt exited 127 before compiling, the host having no `/usr/bin/time`, and was
  rebuilt without it. The observer's first attempt ran under zsh, which did not split its arguments,
  and was refused by `timeout` before Python started; its rerun under Bash is the one reported.
- Every reported run exited 0. The worktree's only untracked path was its `target/`, retired by name
  before the worktree was removed.

The lines are whole in [`COPIES.txt`](COPIES.txt).
