# The live set, by coverage (C1 of #603)

The plan's step: [THE_CONSOLIDATION](../../../../docs/plans/THE_CONSOLIDATION.md) §9, C1. This is a reading of the live line on the PC,
with no change to the machine.

- **Tree.** `main` at `07eb714c7` (PR #812 merged). The binary is `field_pass`, built in its own target directory with
  `RUSTFLAGS="-C instrument-coverage"` in the release profile.
  - `llvm-profdata` and `llvm-cov` come from the stable toolchain's `llvm-tools` component (LLVM 21.1.3).
  - The system's LLVM 23 refuses the toolchain's profiles: they use raw profile format 10, and it expects 11.
- **States.** These are copies of the four-lane line's lap-6 opening (`lap5_STATE.3000.four`, `f930262f…`), its mean
  (`lap5_MEAN.3000.four`, `163607db…`) and lap 5's three-lane end (`lap5/STATE.3000`, `8be62890…`, for `found-lane`).
  - The declaration it ran: `hnn-field-v14m 244 128 4 8 2 128 4 4 3771 4 0 32 0 1 0 1`.
  - The learner's line: `hnn-field-learner-v3 12 593408 81 -`.
- **The run.** Every command of `commands.txt` was run once, in one hold of the card lock (18:36:47 to 18:43:01 UTC, November 14),
  writing only to scratch:
  - `train-store`: 24 sections, saves every 12;
  - `read-cavity`: 1,000 places;
  - `write-store`: 1 document, 64 places of prompt, 64 written, 2 refine passes;
  - `found-lane` and `next-pass`.

  Then `train-store`, `read-cavity` and `write-store` ran again with `FIELD_PROFILE` for the kernels. Their coverage profiles were kept
  apart, because the line never sets `FIELD_PROFILE`. Every command exited 0.
- **Time.** The projection was about 5 minutes for both rounds. The hold measured 374 s, 1.25 times the projection.

  | Command | Wall time | Projection | Peak resident set |
  |---|---|---|---|
  | `train-store` | 26.1 s and 28.9 s | 40 s | 354 MB |
  | `read-cavity` | 153.2 s and 156.9 s | 30 s (a miss of 5.1 times) | 425 MB |
  | `write-store` | 2.9 s and 4.5 s | 30 s | 254 MB |
  | `found-lane` | 0.5 s | 10 s | |
  | `next-pass` | 0.4 s | 10 s | |

  The read's cost is not proportional to its places. The line's uninstrumented read of 20,000 places takes 305 s.
- **Profiles.** `llvm-profdata` warned that 7 functions have mismatched data across the five profiles.

## Files (`rust_files.tsv`)

The binary carries coverage maps for 335 files of the tree and 152 outside it (the standard library and the registry, 40 of which
executed).

**16 of the tree's files executed**, and the prediction holds all 16 (`score.txt`):

| File | Executed lines |
|---|---|
| `crates/holonics-cuda/examples/field_pass.rs` | 43 of 190 |
| `crates/holonics-cuda/src/cuda.rs` | 241 of 1,320 |
| `crates/holonics-cuda/src/hnn/card.rs` | 158 of 624 |
| `crates/holonics-cuda/src/hnn/field.rs` | 2,215 of 2,967 |
| `crates/holonics/examples/solenoidal_alpha.rs` | 30 of 1,629 |
| `solenoidal_alpha/complete_language.rs` | 50 of 964 |
| `complete_language/field_train.rs` | 99 of 3,750 |
| `complete_language/store_train.rs` | 733 of 3,075 |
| `complete_language/tower_train.rs` | 7 of 3,987 |
| `hnn/tower/field.rs` | 1,400 of 5,796 |
| `hnn/tower/field/moment.rs` | 192 of 485 |
| `hnn/tower/field/scale.rs` | 126 of 310 |
| `hnn/tower.rs` | 110 of 4,846 |
| `hnn/keyed_modes.rs` | 52 of 560 |
| `hnn/units.rs` | 58 of 283 |
| `number/census.rs` | 11 of 64 |

**The score: no miss, and six predicted entries ran no line.** No executed file stands outside the prediction, so the plan missed
no dependency of the run. Six entries of the prediction executed nothing:

- `receiver/coupling.rs` and `compression/landmark/context` (both `context.rs` and the `context/` directory). The engine reaches them
  only through its host reference: `coupling_code` from `port_reading` (`field.rs:1128`) and `wide_mul` from `one_end_length`
  (`field.rs:9048`). The card realization stands in for both on the line. They remain dependencies of the engine's law, and C3 still
  carries them: the host reference is the law the card is checked against, and it moves whole.
- `holonics-cuda/src/ffi.rs`: 9 lines and one function, never called.
- The crates' `lib.rs` and `mod.rs` files: no executed region. They hold declarations.

**319 of the 335 files ran no line.**

| Part | Files | Lines |
|---|---|---|
| `crates/holonics/src/hnn` | 124 | 77,439 |
| `holonics-cuda/src/hnn` | 17 | 12,547 |
| `compression` | 17 | 9,906 |
| `receiver` | 17 | 7,453 |
| `examples/solenoidal_alpha` | 11 | 7,200 |
| `holon` | 19 | 6,442 |
| `ratio` | 20 | 6,234 |
| `holarchy` | 12 | 4,212 |
| `physics` | 23 | 3,169 |
| `geometry` | 13 | 2,282 |
| `aeon` | 9 | 1,557 |
| `number` | 9 | 876 |
| `navigator` | 3 | 597 |
| `vendor/num-bigint` | 23 | 4,329 |

Files with no function in the binary (types, constants, generics never instantiated) are not listed at all. The executed files
themselves are mostly idle by line: 5,525 of the 30,850 lines these 16 files carry ran.

## Kernels (`kernels.tsv`, `kernels_declared.tsv`)

The three commands launched **86 of the 163 kernels** the CUDA sources declare. They made 175,046 launches. A kernel named in a
macro, such as `field_contact_l##LL`, is counted as one family, and every launched kernel has a declaration.

| Source | Declared | Launched |
|---|---|---|
| `field.cu` | 103 | 80 |
| `field_cavity.cuh` | 6 | 6 |
| `field_moment.cuh` | 6 | 0 |
| `tower.cu` | 23 | 0 |
| `hnn.cu` | 7 | 0 |
| `tree.cu` | 6 | 0 |
| `hnn_word.cuh` | 5 | 0 |
| `number.cu` | 3 | 0 |
| `hnn_word_exact.cuh` | 2 | 0 |
| `hnn_inverse_exact.cuh` | 1 | 0 |
| `epoch_flow.cuh` | 1 | 0 |

`field.cu`'s 23 unlaunched kernels are listed in `kernels_declared.tsv` with 0 launches. Among them are the `field_yard_*` family,
`field_triad` and its adjoint, the unpaced `field_moment_*_all`, `field_echo_apply` and `field_series_check`.

## What the reading decides (C1's scope)

- **Outside the engine:**
  - the 48 kernels of the eight sources other than the three field sources, none launched by the line;
  - the files that ran no line, apart from the engine's;
  - 199 of the dispatch's 204 commands, since the line calls five (`commands.txt`).

  These are the candidates to retire. Each one retires by its own step's test (D6), never by this table alone.
- **Inside the engine:** nothing. A branch the present declaration does not take is still the law of a state founded another way,
  and the campaign moves the engine whole. This covers `field.cu`'s 23 unlaunched kernels, `field_moment.cuh`, and the unexecuted
  lines of the engine's files.
- **A tool the line calls stands outside the tree.** Every run and read script calls `measure.py`, a 6-line tool for wall time and
  peak resident set. It is untracked, in another worktree's `.local/`. The plan's C2 now brings it into `tools/`.
