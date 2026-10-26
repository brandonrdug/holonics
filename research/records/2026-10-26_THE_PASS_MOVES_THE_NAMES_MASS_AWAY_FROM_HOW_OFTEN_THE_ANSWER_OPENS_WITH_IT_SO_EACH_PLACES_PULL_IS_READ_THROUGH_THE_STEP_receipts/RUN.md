# The runs behind the record

## The calibration read (§1–2)

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs` at `f21cf37a2`, built on
Brandon's PC (7900X) in its own worktree, `complete-language` its first argument, host backend.
Binary SHA-256 `21aa0daa93a1baa4d415067850e33d1ba969c348129a61f26a5a10afaf07e2ef`. Each run ran alone
on an idle host under `timeout` at its deadline, `RAYON_NUM_THREADS=8`, a memory ceiling of 8 GiB
with no swap, inside a `wait4` wrapper that prints `RUN_RECEIPT`. Paths are relative to the run
directory, which is not in the repository.

```text
B read-tower-clock-cells role_clock/S/STATE SHA TEXT SHA UNITS SHA 8 REQUESTS SHA role_clock/calib/S.{train,dev}.copies
python3 -I tools/listener/bank_trace.py copies train_all.txt TEXT UNITS role_clock/calib/{lapD8,lap3T8,lap3D8}.{train,dev}.copies
```

Every input matched its SHA-256: `train_all.txt` `050b94f3…3b95`, `dev.txt` `e5bffe0e…3153`, the units
`d0973c39…782a`, the requests `train.requests` `78528683…9d56` and `dev.requests` `86600c2c…5236`,
and the states `lapD8` `70c76578…51c0`, `lap3T8` `33317844…f6be` and `lap3D8` `5118c9d5…2599`.

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| the build | 119 s | 180 s | 118.8 s | 0.998 | 3,279,548 KiB |
| the copies on the training text, three states in turn | 37.7 s | 41 s | 37.6, 37.5, 37.6 s | 0.995 to 0.997 | 106,516 to 108,172 KiB |
| the copies held out, three states in turn | 4.4 s | 10 s | 4.3 s each | 0.977 | 34,120 to 35,108 KiB |
| the observer, training text then held out | 0.18 s, 0.11 s | 60 s, 10 s | 0.3 s, 0.2 s | 1.67, 1.82 | 50,316 and 46,904 KiB |

- The observer's walls include the receipt wrapper and Python's start-up; its projection was the
  previous read's bare time.
- The copies files: `lapD8.train.copies` `8fb14dd2…4477`, `lap3T8.train.copies` `fbb187af…9131`,
  `lap3D8.train.copies` `436ddf52…f77f`, `lapD8.dev.copies` `4c18405b…34e9`, `lap3T8.dev.copies`
  `9ca16768…0fe8`, `lap3D8.dev.copies` `cde88204…b1f8`, held with the training text's places off the
  repository. The observer's output: `observer.train.raw` `0e6e9d49…1d2c`, `observer.dev.raw`
  `74c22cc6…0940`.
- Both checks held: with the new block and the receipt line removed, each observer output equals the
  previous read's byte for byte, and the largest-mass counts equal the role read's (695, 561, 599;
  53, 37, 43).
- Every run exited 0. The worktree's untracked paths (its build log and `target/`) were retired by
  name before the worktree was removed.

The lines are whole in [`CALIB.txt`](CALIB.txt).

## The covectors' read (§3–4)

Fixed before it runs, at the commit that adds `read-tower-clock-covectors`:

```text
B read-tower-clock-covectors role_clock/S/STATE SHA train_all.txt SHA UNITS SHA 8 128 role_clock/copies/train.requests SHA
python3 -I tools/listener/bank_trace.py change train_all.txt train_all.txt UNITS role_clock/calib/lapD8.train.copies role_clock/calib/S.train.copies
```

`S` is `lapD8` then `lap3T8` for the reader, and `lap3T8` then `lap3D8` for `change`.

| run | projection | deadline | memory |
|---|---|---|---|
| the reader, each state | 54.5 s (37.6 s × the measured 1.45) | 60 s | about 210 MB, ceiling 8 GiB |
| `change`, each pair | unmeasured, planned at 10 s | 10 s | — |
