# Receipts: the blank's outer sums walk the live sites; the ten unlaunched moment entries retire (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 56 (08:25 to 08:42 UTC). Control: #888 (`athena_rel5`), the
line's binary from lap 56. Sections: lap 56's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3. The build
carries both changes, and its one gate 3 covers both.

- **The reading that chose it** (`FIELD_BLANK_LIVE` with the profile, #888, on 4 of lap 54's sections, in the gap after lap 55). Over 48 blank
  returns the kernels walked 964,866 sites. Of these, 135,014 carried a nonzero face covector `δz` in some class: 0.140. The entries (sites ×
  244 classes) were 235,427,304, and 14,086,934 of them nonzero: 0.060 of all, 0.427 within a live site. So the walk's 86% of dead sites set
  the cost: `field_blank_bias_enc` and `field_blank_lift_read` loaded `δz` or `δy` at every walked site to find it zero, and `field_blank_dy`
  walked 244 classes at every cell of a dead site.
- **The change** (`crates/engine-cuda/kernels/field.cu`, `crates/engine-cuda/src/hnn/{clock,resident}.rs`). No bit moves.
  - `field_blank_dz` marks each site whose `δz` is nonzero in some class (`live_at`, by `__syncthreads_or` over the site's classes).
  - `field_blank_live_scan` lists those sites in ascending order: one block of 1,024 threads, each thread a contiguous run of the batch's
    sites, the counts scanned across the block. The list is the same on every schedule (the theory thread's note of 08:01 UTC).
  - `field_blank_bias_enc` and `field_blank_lift_read` walk tiles of the list. A tile is the fewest live sites that let the entry's threads
    cover the list in about the threads the card holds of that entry at once: the multiprocessors times the blocks of the entry each holds,
    as the driver reads its occupancy (`cuOccupancyMaxActiveBlocksPerMultiprocessor`, 5 blocks of 256 at 48 registers: 102,400 threads).
    Each thread reads four sites' operands before it forms their four terms, with no test of each: a zero term adds zero.
  - `field_blank_dy` writes zero at a dead site with no walk of its classes.
  - Every term is released before it enters its sum and the partials meet in integer adds, so neither the list's order nor the tile
    changes a bit.
  - A bound of six blocks a multiprocessor on the two walks was compiled and left out: it held them at 40 registers with 72 and 92 octets of
    spill stores.
- **The retirement** (`crates/engine-cuda/kernels/{field.cu,field_moment.cuh}`, #891). Removed: the ten moment entries no host code names
  (`field_moment`, `field_moment_admit`, `field_moment_return_admit`, `field_moment_prefix`, `field_moment_return_prefix`,
  `field_moment_return`, and the unpaced `field_moment_admit_all`, `field_moment_prefix_all`, `field_moment_all`, `field_moment_return_all`),
  and four helpers only they called. ptxas read the other 127 entries' registers unchanged.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`): parity on 3 calls, 3 and 24 sections reproduced, the cavity read equal.
- **Counters** (`ncu_blank.txt`, the first three launches of each entry on 2 sections). A launch against the control:

  | entry | control µs | this build µs | ratio | issue | warps active | long scoreboard an issued instruction |
  |---|---|---|---|---|---|---|
  | `field_blank_bias_enc` | 1,938–1,989 | 754–755 | 0.38–0.39 | 24–27% → 53.5% | 97% → 60% | 37–42 → 5.1 |
  | `field_blank_lift_read` | 1,098–1,117 | 406–407 | 0.37 | 30% → 46.5% | 97% → 58% | 31 → 5.3–6.6 |
  | `field_blank_dy` | 1,246–1,340 | 395–559 | 0.32–0.42 | 39–43% → 62% | 96% → 85% | 19–22 → 4.8–6.9 |
  | `field_blank_dz` | 190–214 | 200–204 | 1.0–1.06 | 58% | 77% | 3.9 |
  | `field_blank_live_scan` | none | 8.0 | | 30% | 65% | 7.4 |

  The two walks launch 400 blocks of 256, 102,400 threads, against the 122,880 the card would hold of a lighter entry. Their warps active,
  57–60% against the 83% that 40 warps of 48 allow, is a tail: the threads of a wave do not finish together.
- **Profiles** (`PROFILE_PAIR`, ms a section over 24 sections):
  - `field_blank_bias_enc` 15.29 → 5.38 (0.352), its mean grid 1,264,384 → 102,400 threads;
  - `field_blank_dy` 11.12 → 3.79 (0.341);
  - `field_blank_lift_read` 8.83 → 3.25 (0.368), its grid 663,285 → 102,400 threads;
  - the three together 35.24 → 12.42, and the kernel total 523.1 → 500.7.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal):
  - control 536.1, 536.4, 535.8, 536.3, 535.0 (spread 1.4);
  - this build 512.0, 511.4, 511.0, 511.1.

  The means are 535.9 and 511.4: 0.954, 24.5 ms a section. Paired run by run with the control beside each, the differences are 24.4, 24.4,
  25.3 and 23.9 ms.
- **Guesses**, fixed at 08:09 UTC:
  - gate 3 equal: held;
  - `field_blank_bias_enc` 0.10–0.30 a launch: 0.35 to 0.39, a miss on the side of less;
  - `field_blank_lift_read` 0.15–0.35: 0.37, a miss on the side of less;
  - `field_blank_dy` 0.15–0.35: 0.34 by the profile, held, with its launches at 0.32 to 0.42;
  - the scan under 15 µs a launch: 8.0, held;
  - the section 0.945–0.965: 0.954, held.

  The walks' misses sit in their tail: a wave of 102,400 threads that stands at 58–60% of warps active.
- **Into the line.** The hold wrote this build as the chain's next on the equal gate. Chain 17 had already read lap 57's binary (#888), so this
  build trains from lap 58.
