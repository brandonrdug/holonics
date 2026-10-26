# The runs behind the record

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs` at `76568dd0a`, built on
Brandon's PC (7900X) in its own worktree in 1 min 57 s (the previous build took 1 min 59 s),
`complete-language` its first argument, host backend. Binary SHA-256
`765d57cc303767019672a593b0d887d4eb302dad989149c822d54d552ff3534c`. Each run ran alone on the host
under `timeout` at its deadline, `RAYON_NUM_THREADS=8` (the samples one thread each), a memory
ceiling of 8 GiB with no swap, inside a `wait4` wrapper that prints `RUN_RECEIPT`. The founded pass
also ran under the observer that stops a run when its mean time a section passes its bound. Paths are
relative to the run directory, which is not in the repository.

```text
B found-tower-clock bankA7/STATE SHA TEXT SHA UNITS SHA 8 128 OUT
B read-tower-held-cells STATE SHA dev.txt SHA 8 OUT UNITS SHA
B train-unit-tower UNITS SHA TEXT SHA dev.txt SHA dev.roles SHA keys SHA 64 64 256 2 8 128 1 7 OUT FROM SHA
python3 -I tools/listener/bank_trace.py role train_all.txt dev.txt twin8.cells copyD8.cells
python3 -I tools/listener/bank_trace.py held dev.txt twin8.cells copyD8.cells '"any "'
B sample-unit-tower UNITS SHA STATE SHA prompt_framed.txt SHA keys_sN SHA 400 OUT [2]
```

Every input matched its SHA-256: the GSM8K units `d0973c39…782a`, the training text `050b94f3…3b95`,
its first eighth `717deec4…8a4d`, its first 300 problems `15b1aac8…0803`, the held-out text
`e5bffe0e…3153`, the held-out roles `c978b971…1b78`, the founding keys `bd71c574…a958`, the four-pass
bank state `1dee7db0…6ea4`, the framed prompt `e697eca0…9652`, the eight sample key streams, and the
twin's held-out cells `d538b2c9…e8b9`. Their full SHA-256s are in the
[four-pass record's receipts](../2026-10-26_THE_BANK_COMPLETES_A_WORD_THE_QUESTION_HOLDS_AND_DOES_NOT_CHOOSE_IT_AND_PROSE_ALONE_STALLS_ABOVE_BZ2_receipts/RUN.md)
and the [pool record's](../2026-10-26_THE_POOL_CHOOSES_THE_BLANK_LINES_CLOCK_AND_ITS_PASS_CODES_ABOVE_ITS_TWIN_SO_NOTHING_IS_FOUNDED_receipts/RUN.md).

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| 1. the pool on the first eighth | unmeasured, planned at up to 3 min | 180 s | 24.9 s | — | 427,496 KiB |
| 2. the founding on the whole text | 8 × 5,766 + 8 × 6,512 ms + 1,311 × 149.3 ms + 10 s = 304.0 s | 304 s | 154.9 s | 0.51 | 506,560 KiB |
| 3. the opening, held-out cells from the founded state | 10 s | 10 s | 4.4 s | 0.44 | 36,532 KiB |
| 4. timing, 300 problems | `timeout 120` | 120 s | 11.6 s | — | 349,756 KiB |
| 5. the founded pass | 1,311 × 154.0 ms + 5 s = 206.9 s | 207 s | 158.5 s | 0.77 | 383,880 KiB |
| 6. held-out cells from the founded pass | 10 s | 10 s | 4.4 s | 0.44 | 37,196 KiB |
| 6. the role and held observers | 10 s each | 10 s | 0.2 s each | — | 47,068 and 68,140 KiB |
| 7. 16 samples, 8 at a time | 2.2 s each | 10 s each | 1.9 s at most, 2.4 s in all | 0.19 | 37,552 KiB at most |

- Run 2's eight streams all reported by 47.3 s against the early-stop bound of 56.1 s (8 × run 1's
  read plus 10 s). Its pool read took 8.2 times run 1's, its drops 1.1 times, and its moments read
  1,311 sections in 100,156 ms (76.4 ms a section).
- Run 4's largest window was 118.3 ms with no halving, so run 5 kept the 154.0 ms bound. Run 5 took
  no halving in any of its 1,311 sections, and its mean section was 117.2 ms.
- States: `copyE.state` (the eighth's founding, read only for the projection)
  `5fe8cb85ccd01635b836285d78915f3c4c625784dde28f1f8fd7cd2be6d6831a`; `copyD.state`
  `6417eb3dd37ea302d838c1dc6a95b2efa6a8df04b539c6c2d6a9c66b0539a9d9`; the train300 pass
  `bb7a83dfc71c3b23fbf9c8c950bf3359ec8af26db3deb7341a0f2b31e3a39191`; the founded pass
  `copyD8/STATE` `3551b608e1f9444f27e76a2f04ebbd718d2afcd2f6f85bbc89719db11edab8f3`.
- Every run exited 0. The worktree's untracked paths were its `target/` and its `.local/` build log;
  the log was copied into the run directory and both were retired by name before the worktree was
  removed.

The pool's lines are whole in [`POOL.txt`](POOL.txt), the passes' in [`PASSES.txt`](PASSES.txt),
the held-out reads in [`HELD.txt`](HELD.txt) and every sample in [`SAMPLES.md`](SAMPLES.md).
