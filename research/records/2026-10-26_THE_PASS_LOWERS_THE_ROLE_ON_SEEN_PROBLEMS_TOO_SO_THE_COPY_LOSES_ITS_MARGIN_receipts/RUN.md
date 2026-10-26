# The runs behind the record

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs` at `7f0921b4b`, built on
Brandon's PC (7900X) in its own worktree in 1 min 58 s, `complete-language` its first argument, host
backend. Binary SHA-256 `18e05215c0e49998fd1e59f1c84761ea0c6a22e80f0f0b9cbd4cb25808139042`. Each run
ran alone on a host idle but for desktop applications, under `timeout` at its deadline,
`RAYON_NUM_THREADS=8`, a memory ceiling of 8 GiB, inside a `wait4` wrapper that prints
`RUN_RECEIPT`. Paths are relative to the run directory, which is not in the repository.

```text
B read-tower-held-cells role_clock/S/STATE SHA train_all.txt SHA 8 role_clock/seen/S.train.cells UNITS SHA
python3 -I tools/listener/bank_trace.py role train_all.txt train_all.txt role_clock/seen/{copyD8,lapT8,lapD8,lap3T8,lap3D8}.train.cells
python3 -I tools/listener/bank_trace.py role train_all.txt dev.txt role_clock/{twin8,copyD8,lapT8,lapD8,lap3T8,lap3D8}.cells
```

Every input matched its SHA-256: `train_all.txt` `050b94f3…3b95`, `dev.txt` `e5bffe0e…3153`, the units
`d0973c39…782a`, the five states (`copyD8` `3551b608…b8f3`, `lapT8` `c4511950…35b7`, `lapD8`
`70c76578…51c0`, `lap3T8` `33317844…f6be`, `lap3D8` `5118c9d5…2599`) and the six held-out cells files
of the [third lap's receipts](../2026-10-26_THE_THIRD_LAP_FOUNDS_THE_CLOCK_AFTER_EQUALS_AND_ITS_PASS_LOWERS_THE_ROLE_FROM_53_TO_43_receipts/RUN.md).

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| 1. the training text's cells, five states in turn | 4.4 s × 3,528,168 / 397,669 bytes = 39.0 s | 40 s | 38.1, 38.2, 38.2, 38.3, 38.3 s | 0.977 to 0.982 | 153,908 to 156,912 KiB |
| 2. the role on the seen problems | unmeasured, planned at 60 s | 60 s | 2.0 s | 0.033 | 271,708 KiB |
| 3. the role held out | 10 s | 10 s | 0.4 s | 0.04 | 46,860 KiB |

- Run 1 read 1,342,752 cells a state. Its margin was thin (at most 1.7 s); the next read of this size
  projects from its largest measured wall, 38.3 s.
- The cells files' SHA-256:
  - `copyD8.train.cells` `0a554b46e4b240370aae3d8ec3032c01350d6f0d4a7a541773d6df5775e7f4ca`
  - `lapT8.train.cells` `10533dac4900d777a75a69ccbd78d7bce0321ece0946776663e747f4c75a3b77`
  - `lapD8.train.cells` `b98d572993eeb3001373ef9a09a9b9e4e32cf5f0c29f0e85def59ab3621e8e28`
  - `lap3T8.train.cells` `c644bcad300a48422348ced130cab9b2b5f4794c7b648f0ed7bd2db3668d7f54`
  - `lap3D8.train.cells` `7fd7626d7b6afebabead60b0fb7ac56e89867769a8d732b2078c8bbe5c35d514`

  They hold the training text's cell places and stay off the repository with the text.
- Every run exited 0. The worktree's only untracked path was its `target/`, retired by name before the
  worktree was removed.

The observers' lines are whole in [`ROLE.txt`](ROLE.txt).
