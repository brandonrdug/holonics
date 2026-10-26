# The replay of the third lap's pass, run to its end

On Brandon's PC (Ryzen 9 7900X, RTX 4080 SUPER unused), at `cea8c660c5b8140cc27154e34600847f99863ac6`, in a fresh
worktree whose own target directory built the example (`Compiling holonics` from the worktree, with
no shared `CARGO_TARGET_DIR`). Every run under a `wait4` wrapper that prints `RUN_RECEIPT`, with
`RAYON_NUM_THREADS=8` and an 8 GiB memory scope (`MemoryMax=8G`, `MemorySwapMax=0`), alone on an
idle host (load about 1 to 3, desktop applications only).

- Binary `examples/solenoidal_alpha`, SHA-256 `0fcdfb3521e5898e5950b5a506ada40592efcbd00ccf709b71ba5eeef85b98af`.
- Inputs, each checked by SHA-256 before the run: the training text `050b94f3…3b95`, the units
  `d0973c39…782a`, the copies' requests `78528683…9d56`, `lapD8/STATE` `70c76578…51c0` and
  `lap3T8/STATE` `33317844…f6be`.

```text
B replay-tower-clock-pass role_clock/lapD8/STATE SHA train_all.txt SHA UNITS SHA 8 128 role_clock/copies/train.requests SHA 3331784425b940522736c535c8035d6b6fc23d531fb122d19c46d5cffc0ef6be
```

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| build | 119 s | 180 s | 126.3 s | 1.06 | 3,357,520 KiB |
| replay | 303.2 s upper end, 259 s expected | 304 s | 276.3 s | 0.911 of the upper end, 1.067 of the expected | 598,440 KiB |

Build receipt: `RUN_RECEIPT exit=0 wall_s=126.3 peak_rss_kib=3357520 user_s=200.6`. The replay's
start (load, hash and whole read) took 44,838 ms against 43.6 s; its 1,311 sections 185,932 ms,
141.8 ms a section against 130.9 ms expected and the 164.7 ms bound; every whole 32-section window
4,485 to 4,679 ms against the stop line of 5,270 ms; its end 45,449 ms against 43.6 s.

[`REPLAY.log`](REPLAY.log) is the run's log, all 60 lines, as the PC wrote it (its SHA-256 below is
the PC file's). The worktree's two ignored items (the build log, copied out first, and `target/`)
were retired by name, and the worktree removed and pruned.
