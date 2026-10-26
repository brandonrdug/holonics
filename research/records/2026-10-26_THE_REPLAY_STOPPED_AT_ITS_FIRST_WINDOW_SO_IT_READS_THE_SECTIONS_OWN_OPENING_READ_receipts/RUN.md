# The runs behind the record

## The stopped run (§1–2)

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs` at `d366e6201`, built on
Brandon's PC (7900X) in its own worktree with no shared target directory, `complete-language` its
first argument, host backend. Binary SHA-256
`2ab54355782f26dbe735547becdbb4d07f4464c3e0c3005c58f88a83e4f2a85d`. Each run ran under `timeout` at
its deadline, `RAYON_NUM_THREADS=8`, an 8 GiB memory scope with no swap, inside a `wait4` wrapper
that prints `RUN_RECEIPT`. Paths are relative to the run directory, which is not in the repository.

```text
B replay-tower-clock-pass role_clock/lapD8/STATE SHA train_all.txt SHA UNITS SHA 8 128 role_clock/copies/train.requests SHA 3331784425b940522736c535c8035d6b6fc23d531fb122d19c46d5cffc0ef6be
```

Every input matched its SHA-256: `train_all.txt` `050b94f3…3b95`, the units `d0973c39…782a`, the
requests `78528683…9d56`, the states `lapD8` `70c76578…51c0` and `lap3T8` `33317844…f6be`.

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| the build | 119 s | 180 s | 118.7 s | 1.00 | 3,488,176 KiB |
| the replay | 306.1 s; a 32-section window 5,100 ms | 310 s | stopped at 49.0 s; the first window 5,270 ms | 1.03 a window | 499,176 KiB |

The replay's log (`lapD8.replay.log`, SHA-256
`9e007a1add11c63cd8ad4847e63e14b150c64af5fb136f7284f58fa4e58f21d5`) holds exactly:

```text
TOWER_REPLAY_OPEN requests=4524 placed=4524 openings=4519 unheld=4 name_mass=+906.5 F=-12641.553 elapsed_ms=43644
TOWER_REPLAY_SECTION section=32 deposits=32 halvings=0 read_ms=1284 elapsed_ms=48914
```

and the wrapper printed `RUN_RECEIPT exit=-15 wall_s=49.0 peak_rss_kib=499176 user_s=379.3`. The
load, hash and first whole read took 43.6 s against 53.7 s projected (0.81); the first window took
164.7 ms a section against 159.2 ms projected (1.035), 40.1 ms of it in the place read and 124.6 ms
in the rest. The host carried desktop applications (load average 2.49 at launch, just after the
build). The first build launch did not start (the host has no `/usr/bin/time`, exit 127); it was
relaunched once under the `wait4` wrapper with the same deadline. The worktree's untracked paths
(its build log, kept with the run directory, and `target/`) were retired by name before the
worktree was removed.

## The smoke of the changed read (§3)

In this container (4 threads), the release build of the commit that adds this record, on the slice
of the first smoke (`text`, 162,937 bytes, the first 300 problems), the units `d0973c39…782a`, the
two-clock state `two.state` `1419ad40…97bf` and its 204 requests, expecting the state its pass
reached.

```text
B replay-tower-clock-pass two.state SHA text SHA UNITS SHA 4 128 req SHA d2aeb9930e4ac7d4a06e3b05bbc56c2ca37b077fec9c2d9658ab0bc0b0b7c34f
```

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| the changed replay | under the first replay's 65.2 s | 70 s | 56.8 s | 0.87 | 333,676 KiB |

It printed `expected=match`, and every `TOWER_REPLAY` line equals the first replay's once the
`read_ms` and `elapsed_ms` fields are removed (the two logs' SHA-256 `2165edd3…70b3` and
`d9fb686f…f9c1` differ only there). Its sections took 37,080 ms against the first replay's 46,651 ms
(0.795), the place read 2,350 ms against 11,775 ms; its end (state text and hash, whole read, lines)
took 9.76 s against the start's 9.90 s.

## The replay (§4)

Fixed before it runs, at the commit that adds this record:

```text
B replay-tower-clock-pass role_clock/lapD8/STATE SHA train_all.txt SHA UNITS SHA 8 128 role_clock/copies/train.requests SHA 3331784425b940522736c535c8035d6b6fc23d531fb122d19c46d5cffc0ef6be
```

| run | projection | deadline | memory |
|---|---|---|---|
| the replay | upper end 1,311 sections × 164.7 ms (the stopped read, one forward more a section) = 215.9 s, the start 43.6 s and the end at most 43.6 s as measured: 303.2 s; expected 1,311 × 130.9 ms + 87.2 s ≈ 259 s | 304 s | 487 MiB measured, ceiling 8 GiB |

A 32-section window past 5,270 ms stops the run as incomplete.
