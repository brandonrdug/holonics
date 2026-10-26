# The runs behind the record

`B` is the release build of `crates/holonics/examples/solenoidal_alpha.rs`, built on Brandon's PC
(7900X) in its own worktree, `complete-language` its first argument, host backend. Each run ran under
`timeout` at its deadline inside a `wait4` wrapper that prints `RUN_RECEIPT` (exit, wall, peak
resident set, user time); the passes also ran under an observer that stops a run when its mean time
a section passes its bound. `RAYON_NUM_THREADS=8` a run. Paths are relative to the run directory,
which is not in the repository. The pool's lines are whole in [`POOL.txt`](POOL.txt), the passes'
in [`PASSES.txt`](PASSES.txt), and every sample in [`SAMPLES.md`](SAMPLES.md).

```text
B found-tower-clock bankA7/STATE SHA train_all.txt SHA UNITS SHA 8 128 0 OUT
B train-unit-tower UNITS SHA train_all.txt SHA dev.txt SHA dev.roles SHA keys SHA 64 64 256 2 8 128 1 7 OUT FROM SHA
B read-tower-held-cells STATE SHA dev.txt SHA 8 OUT UNITS SHA
python3 -I tools/listener/bank_trace.py role train_all.txt dev.txt twin8.cells clockB8.cells
B sample-unit-tower UNITS SHA STATE SHA prompt|prompt_framed SHA keys_sN SHA 400 OUT [2]
```

## The first founding, whose join's moments opened at zero (`44fc07f96`)

`solenoidal_alpha` at `44fc07f96`, binary SHA-256
`78a0124305b99e5cba0acbb56ce71913806c947f8926671edcbf00a52a53d474`, release build 1 min 59 s in
its own worktree. Brandon's PC (7900X), `RAYON_NUM_THREADS=8` a run, the two certification passes
together.

| input | SHA-256 |
|---|---|
| GSM8K units (`UNITS`) | `d0973c39ebf391bf1115322a2df8c42157036e96c3eca79c37c869d557a2782a` |
| training text (`train_all.txt`) | `050b94f367625ad2c533bb3af53c730ea6d12e140a080a6a3def9ffdc0de3b95` |
| held-out text (`dev.txt`) | `e5bffe0ea3949a2e8efec1c43120918891867c342a9e9ffd288cc798a8363153` |
| the four-pass bank state (`bankA7/STATE`) | `1dee7db05633e773c7b9e4e0eda6db1ab54bce979a4014e0a696f35adeb56ea4` |
| the training text's first eighth (`train8.txt`, 441,319 bytes) | `717deec4065bbf1e14ab96a758ce8e8b40ee3bce79cf0debe645036a6e008a4d` |

The held-out roles, founding keys, prompts and sample keys are the four-pass record's, checked by
SHA-256 ([its receipts](../2026-10-26_THE_BANK_COMPLETES_A_WORD_THE_QUESTION_HOLDS_AND_DOES_NOT_CHOOSE_IT_AND_PROSE_ALONE_STALLS_ABOVE_BZ2_receipts/RUN.md)).

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| 1. the pool on the first eighth | unmeasured, planned at up to 3 min | 180 s | 21.1 s | — | 340,556 KiB |
| 2. the pool on the whole text | 8 × 11,796 + 8 × 9,258 ms + 10 s = 178.4 s | 179 s | 113.9 s | 0.64 | 605,528 KiB |
| 3. timing, 300 problems, two passes together | `timeout 120` | 120 s | 15.0 and 14.9 s | — | 435,452 and 348,180 KiB |
| 4. twin pass | 1,311 × 153.4 ms + 5 s = 206.1 s | 207 s | 161.1 s | 0.78 | 382,536 KiB |
| 4. founded pass | 1,311 × 154.0 ms + 5 s = 206.9 s | 207 s | **stopped early at 9.2 s** | — | 454,984 KiB |
| the opening, held-out cells from both states | 10 s each | 10 s | 5.7 and 5.6 s | — | 37,400 and 37,804 KiB |

Run 2's streams all reported by 94.2 s against the early-stop bound of 104.4 s (the eighth's read
times eight, plus 10 s).

The pool's lines are whole in [`POOL.txt`](POOL.txt). Both pools founded class 313, the blank line,
and wrote the same state: `d85c23ba60e28933de4ac5d093bf6f627668e037b0976d660821f2ffb9388876`,
294,700 material entries (the join opens at zero, so the state depends only on the class).

Run 3, 300 training problems (`15b1aac8f8376361…`, 162,937 bytes):

```text
founded: TOWER_PASS pass=0 train_bits_a_byte=1.727 dev_bits_a_byte=1.719 dev_regions Q=1.960 P=1.438 N=2.361 M=1.263 deposits=60/60 pass_ms=14824 elapsed_ms=14859 train_code=292360822414 dev_code=716729590510 grain_bits=20
twin:    TOWER_PASS pass=0 train_bits_a_byte=1.524 dev_bits_a_byte=1.577 dev_regions Q=1.797 P=1.314 N=2.254 M=1.124 deposits=60/60 pass_ms=14759 elapsed_ms=14795 train_code=257938428470 dev_code=657467918477 grain_bits=20
```

Largest windows 154.0 ms (founded, one halving) and 153.4 ms (twin, none).

Run 4, the whole training text:

```text
twin:    TOWER_PASS pass=0 train_bits_a_byte=1.524 dev_bits_a_byte=1.596 dev_regions Q=1.797 P=1.358 N=2.241 M=1.147 deposits=1311/1311 pass_ms=160544 elapsed_ms=160574 train_code=5636231354399 dev_code=665305828192 grain_bits=20
founded: TOWER_SECTION pass=0 section=32 bits_a_byte=2.304 deposits=31 halvings=90 elapsed_ms=8762
         TOWER_SWELL pass=0 section=32 L0 x=327986 h=3756406 r=14607280 a=1048910 push=55499327 read=58871137 contact=47574777 return=28959403 lambda=1060540964 L1 x=1250192 h=60564356 r=169936009 a=550911 push=55021085 read=109714494 contact=20644094 return=14995090 lambda=1072420288 readout=49446927
         RUN_RECEIPT exit=-15 wall_s=9.2 peak_rss_kib=454984 user_s=55.2 stopped=early stop: the mean 273.8 ms a section past the 154.0 bound at pass 0 section 32
```

The twin's state: `d422a52396bc198fd27921acd3ac424ac1379f6fce0e55ee8b96aaa911bb0fcf`, largest
window 149.3 ms. At the same section the twin read `bits_a_byte=1.526 deposits=32 halvings=0`,
`L1 h=8174281 r=25223976`. The founded pass was not relaunched.

The opening: the held-out cells read from `bankA7/STATE` and from the founded state are
byte-identical (`8163fb5d11ed12e9b7a0756c0607c1763b6b605606b54534032017625baab954`), so the
founded state's damage was done by its deposits, not by its join.

## The second founding, whose join's moments open on its passage (`b6345c706`)

`solenoidal_alpha` at `b6345c706`, binary SHA-256
`c1d9fdd9d0c6d2c8d79f188fd05c54054e4a9f49b2c7b6cc779835f91e78a13e`, release build 2 min 00 s.
Every input matched its SHA-256. The twin pass stands as measured above and was not rerun.

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| 1. the founding with its moments | 94.3 + 19.5 s (the pool) + 1,311 × 149.3 ms (the moments) + 10 s = 319.5 s | 320 s | 216.6 s | 0.68 | 626,416 KiB |
| 2. timing, 300 problems | `timeout 120` | 120 s | 11.6 s | — | 350,008 KiB |
| 3. the founded pass | 1,311 × 154.0 ms + 5 s = 206.9 s | 207 s | 160.0 s | 0.77 | 384,948 KiB |
| 4. held-out cells, twin and founded | 10 s each | 10 s | 6.0 and 4.3 s | — | 36,724 and 36,740 KiB |
| 4. the role observer | 10 s | 10 s | 0.2 s | — | 47,128 KiB |
| 5. 48 samples, 8 at a time | 2.6 s each | 10 s each | 2.2 s at most, 7.1 s in all | 0.85 | 38,428 KiB at most |

Run 1's eight streams all reported by 94.9 s against the early-stop bound of 104.4 s. The moments
read 1,311 sections in 102,869 ms (78.5 ms a section: a forward and reverse without the reread). The
founded state: `fdd0d38d3452032a8e9d6c90c41c2d52d4cf3ea3ebca79d38e929704ae4cc9cb`. Run 2's largest
window was 118.7 ms with no halvings (the first founding's was 154.0 ms with one); its state
`9e3c47cecc66caaf5605c199b662ec32f6158d1f3eb8cfc6e42d20f84ed46f75`. Run 3 took no halving in any
of its 1,311 sections, read 117.6 to 120.0 ms a section, and wrote
`b413e9663aadb22d23349cdeef8edf12cbb492a4f40e41d1b33a7e41a3b5fac8`.

Run 4:

```text
TOWER_HELD_CELLS unjoined=false units=1318 streams=8 cells=151676 grain_bits=20 out=role_clock/twin8.cells
TOWER_HELD_CELLS unjoined=false units=1318 streams=8 cells=151676 grain_bits=20 out=role_clock/clockB8.cells
role_clock/twin8.cells: 97 named answers opening with the name, 97 read, 0 skipped; the first unit has the largest mass in 1; its mean code 6.582 bits
role_clock/clockB8.cells: 97 named answers opening with the name, 97 read, 0 skipped; the first unit has the largest mass in 1; its mean code 6.121 bits
```

Run 5's prompt bits a byte: 1.969 for the founded state on the framed prompt, 2.080 for the twin on
the framed prompt, 2.689 for the founded state on the prompt as written. Every run exited 0. The
worktree's only untracked path was its `target/`, retired by name before the worktree was removed.
