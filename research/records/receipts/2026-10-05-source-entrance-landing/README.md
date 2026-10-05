# Receipt: the source entrance's landing gates (#377)

- **Source:** Codex's `codex/hnn-physical-source-join` at `1141cc85`, rebased by the coordinator onto
  `c1def677` as `74b0e561` + `c368e93d` (the only conflict a records README route, both kept). The
  seven owner files are byte-equal to `1141cc85`. Merged as `7ab0fdfb`.
- **Build:** the coordinator's worktree target (dev profile for check/tests; `PATH=/opt/cuda/bin`),
  isolated from every other worktree.
- **Commands, in order:** `bash tools/gate.sh`; `cargo test -p holonics --test source_entrance --
  --test-threads=1`; `cargo test -p holonics --lib`; `flock .local/gpu.lock cargo test -p
  holonics-cuda -- --include-ignored --test-threads=1`. Exit 0.
- **Output:** `gates.txt` (the script's filtered output with each step's wall milliseconds):
  check 11,279 ms, guard lints 13,456 ms, guard doctests 17,097 ms; source_entrance 4 of 4
  (18,634 ms); lib 1,003 (182,954 ms); GPU 41 (225,646 ms). Projections were not pinned for this
  landing (guard 22's pins began with #372 for the notebook harness); peak memory was not read.
