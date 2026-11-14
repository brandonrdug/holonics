# The engine's gates (C2 of #603)

The plan's step is [THE_CONSOLIDATION](../../../../docs/plans/THE_CONSOLIDATION.md) §9, C2. This receipt holds the gates that hold
the live line, and the check that a deliberate alteration of the engine fails them.

## Gate 1

- `tools/gate.sh` now runs the engine's host tests: `cargo test -p holonics --lib hnn::tower::field`, covering 122 tests (with
  `moment.rs` and `scale.rs`, 42 s in debug).
  - One test, `the_covector_matches_the_code_across_the_far_support`, takes about 150 s in debug against 49 s for the other 122
    together. It runs in gate 2, with the tests of a step that changes the engine.
- `tools/measure.py` comes into the tree, and its controls (`tools/test_measure.py`) run in gate 1. Every run and read script of the
  line calls it, from another worktree's untracked `.local/` until now (C1's finding).
- `tools/reproduction.py` takes `--no-save` for a run shorter than the line's first save, and its controls cover the flag.
- The whole gate passed in this tree (exit 0).

## Gate 3: `tools/gate_engine.sh LINE BIN OUT`

These three runs take one hold of the card, against the line that trains:

1. **`parity-store`**, on 3 of the line's sections from the state its lap trained from. The command is `train-store` itself, run
   through a realization that asks both the card and the host (`HostField`) for every read and compares the results whole.
   - The learner is given the card's result, so the run's `STORE_SECTION` lines are also a reproduction of those sections.
   - Every method the card overrides is forwarded to its override. The store line's training calls one of them,
     `read_and_return_opening`, once a section.
   - The parity of November 2 (`parity-field`) recorded only the face and covector reads. On this line it would have let the
     opening's path fall to the trait's default, leaving the card's own path unchecked.
2. **The reproduction** of 24 sections from the same state, the card alone, read against the lap's own lines by
   `tools/reproduction.py`.
3. **The lap's read**: `read-cavity` on the lap's mean, its `cavity.tsv` compared byte for byte with the lap's own.

## The runs (November 14, the four-lane line's lap 6)

| Build | Parity (3 sections) | Reproduction (3 / 24 sections) | Read | Gate |
|---|---|---|---|---|
| Unaltered | EQUAL | 3 of 3 / 24 of 24 | EQUAL | **EQUAL** |
| A: the deposit's divisor `⌊√v⌋ + 2` for `+ 1` (host only) | EQUAL | 3 of 3 / 10 of 24 (first difference at section 10: `before`, `transfer`, `external`) | EQUAL | **DIFFERS** |
| B: `LN2_FACE_BITS` 29 for 30 in `field.cu` (card only) | DIFFERS: 0 unequal sites, 1,001,297 unequal covector entries over 3 calls | 0 of 3 / 0 of 24 (`external` from section 0) | EQUAL | **DIFFERS** |

Both alterations were built from this tree, copied out and reverted. Every arm caught something the others did not:

- **The parity** cannot see a change of law made where both realizations read the same learner, such as A's deposit.
- **The first 3 reproduced sections** do not see A at all. It first shows in the printed fields at section 10.
- **The read** holds neither alteration, because it reads faces and B changes only the return.

So the 24 reproduced sections are what hold a change to the deposit, and the parity is what holds the card's covector. Both alterations
fail gate 3, which is C2's done condition. Gate 1 was not run on them.

- **Time.** The unaltered gate held the card from 19:23:05 to 19:31:23 UTC (498 s, against a projection of about 9 minutes).

  | Run | Wall time | Peak resident set |
  |---|---|---|
  | Parity | 200.4 s | 6.4 GB |
  | Reproduction | 17.7 s | 0.35 GB |
  | Read | 279.0 s | 0.56 GB |

  The host's side of the parity took 194.6 s against the card's 2.2 s for the same three reads, 90 times.
- **A finding for the line.** Lap 7 stopped at 2,899 of its 3,000 sections at its projection (2,100.7 s). It ran beside this step's
  release builds and gate 1. Since #812 the deposit's per-entry loops run across all of the host's cores, so host work beside the line
  now slows its laps. The lap's read was taken at `MEAN.2000`.

The files `gate3_unaltered.txt`, `gate3_altA.txt` and `gate3_altB.txt` hold each run's lines.
