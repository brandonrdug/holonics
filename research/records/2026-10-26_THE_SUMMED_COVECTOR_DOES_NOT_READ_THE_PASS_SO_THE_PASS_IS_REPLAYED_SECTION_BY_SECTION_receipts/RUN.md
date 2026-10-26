# The runs behind the record

## The covectors' read (§1–2)

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs` at `58d3a05db`, built on
Brandon's PC (7900X) in its own worktree with no shared target directory, `complete-language` its
first argument, host backend. Binary SHA-256
`b71355c6110b735fb1a2ce25ace46a3eeeaa346b124b294796777afce13ebe1a`. Each run ran alone on an idle
host under `timeout` at its deadline, `RAYON_NUM_THREADS=8`, an 8 GiB memory scope with no swap,
inside a `wait4` wrapper that prints `RUN_RECEIPT`. Paths are relative to the run directory, which is
not in the repository.

```text
B read-tower-clock-covectors role_clock/S/STATE SHA train_all.txt SHA UNITS SHA 8 128 role_clock/copies/train.requests SHA
python3 -I tools/listener/bank_trace.py change train_all.txt train_all.txt UNITS role_clock/calib/lapD8.train.copies role_clock/calib/T.train.copies
```

`S` is `lapD8` then `lap3T8`; `T` is `lap3T8` then `lap3D8`. Every input matched its SHA-256:
`train_all.txt` `050b94f3…3b95`, the units `d0973c39…782a`, the requests `78528683…9d56`, the states
`lapD8` `70c76578…51c0` and `lap3T8` `33317844…f6be`, and the copies files `lapD8.train.copies`
`8fb14dd2…4477`, `lap3T8.train.copies` `fbb187af…9131` and `lap3D8.train.copies` `436ddf52…f77f`.

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| the build | 119 s | 180 s | 118.9 s | 1.00 | 3,449,764 KiB |
| the reader at `lapD8` | 54.5 s | 60 s | 43.5 s | 0.80 | 204,564 KiB |
| the reader at `lap3T8` | 54.5 s | 60 s | 43.7 s | 0.80 | 206,096 KiB |
| `change`, each pair | unmeasured, planned at 10 s | 10 s | 0.2 s each | 0.02 | 50,140 and 50,900 KiB |

- The reader's output files: `lapD8.train.covectors` `58813f71…59f5`, `lap3T8.train.covectors`
  `20cf3d69…0ebc`; `change`'s: `change.lapD8.lap3T8.out` `1de85247…c4c1`, `change.lapD8.lap3D8.out`
  `76628db2…e8eb`. They are held off the repository with the run directory.
- The first build launch did not start (the host has no `/usr/bin/time`, exit 127, nothing
  compiled); it was relaunched once under the `wait4` wrapper with the same deadline.
- Every run exited 0. The worktree's untracked paths (its build log and `target/`) were retired by
  name before the worktree was removed.

The lines are whole in [`COVECTORS.txt`](COVECTORS.txt).

## The smoke (§3)

In this container (4 threads), the release build of the commit that adds the replay, on a slice of
the training text (`text`, 162,937 bytes, the first 300 problems), the units `d0973c39…782a`, a
two-clock state founded on the slice (`two.state` `1419ad40…97bf`, its copies at zero) and its 204
requests.

```text
B train-unit-tower UNITS SHA text SHA dev40.txt SHA dev40.roles SHA keys SHA 64 64 256 2 4 128 1 7 pass1 two.state SHA
B replay-tower-clock-pass two.state SHA text SHA UNITS SHA 4 128 req SHA d2aeb9930e4ac7d4a06e3b05bbc56c2ca37b077fec9c2d9658ab0bc0b0b7c34f
```

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| the pass | 42 s | 90 s | 35.2 s | 0.84 | 219,320 KiB |
| the replay | 73 s | 150 s | 65.2 s | 0.89 | 309,692 KiB |

The pass reached `d2aeb9930e4ac7d4a06e3b05bbc56c2ca37b077fec9c2d9658ab0bc0b0b7c34f` (121 deposits, no
halving); the replay printed `expected=match`. Its sections took 46.7 s (386 ms each, against the
pass's 291), of which 11.8 s read the sections by place; its two whole reads took about 9 s each.

## The replay (§4)

Fixed before it runs, at the commit that adds `replay-tower-clock-pass`:

```text
B replay-tower-clock-pass role_clock/lapD8/STATE SHA train_all.txt SHA UNITS SHA 8 128 role_clock/copies/train.requests SHA 3331784425b940522736c535c8035d6b6fc23d531fb122d19c46d5cffc0ef6be
```

| run | projection | deadline | memory |
|---|---|---|---|
| the replay | 1,311 sections × 159.2 ms (the pass's largest window on the PC, 119.7 ms, × the smoke's 386/291) = 208.7 s, two whole reads × 43.7 s (the reader on the PC) = 87.4 s, the state's load and hash 10 s: 306.1 s | 310 s | about 600 MB (the pass's 383 MB, the sections' sums by place 88 MB, a whole read's 110 MB), ceiling 8 GiB |

The replay prints its elapsed time every 32 sections; a window of 32 sections past 5.1 s
(32 × 159.2 ms) stops the run as incomplete.
