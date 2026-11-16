# Receipts: the columns gather a chunk of receivers and their column entries at once (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 65 (14:22 to 14:38 UTC). Control: #911 (`athena_crowdsums`),
the line's binary from lap 66. Sections: lap 65's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3.
The columns' source counters read in the gap after lap 64 (`../2026-11-16_crowdsums/source_lines_columns_909.txt`) chose it: the line
that adds `δs_ij` times the bracket held 0.233 of `field_contact_columns`' stall samples and `receiver_at` 0.142, because each pass of the
receiver loop waited on a chain, the receiver's located index and then its column entries.

- **The change** (`crates/engine-cuda/kernels/field.cu`, `field_contact_columns`). For each chunk of 32 receivers a lane locates one
  receiver and reads its two column entries, `δs_ij` and `p_ij` (the region block read down a column, `i · sites + j`), into the warp's
  shared rows (a receiver's index, or the mark `UINT32_MAX` where it has none or is skipped; 2,560 octets a block). After a warp
  barrier the lanes over the span's entries and parts read them, each part its own receivers in their order, and a second barrier stands
  before the next chunk overwrites the rows. The sums are the same integers released once after the loop, so no bit moves.
- **Compiled** (ptxas at `sm_89`): 72 registers, no spill, 2,560 octets of shared memory; seven blocks a multiprocessor as before.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Source counters** (`source_lines_911.txt`, `source_lines_colgather.txt`, by `../2026-11-16_rowsacc/rows_lines.py`, two launches each):
  the kernel's stall samples 123,708 → 98,479 (0.796) and its warp instructions 551.1 → 472.3 million (0.857). The line that adds
  `δs_ij` times the bracket 0.228 → 0.008 of the samples; `receiver_at` 0.142 → 0.024. The bracket's line now holds 0.255, on the
  receiver's probe (`pq`, read across the span for each receiver).
- **Counters** (`hold.txt`, `NCU_ROWS`, eight launches of each build): 0.812, 0.858, 0.931, 0.928, 0.795, 0.792, 0.910 and 0.904 of the
  control's; instructions 13–18% fewer.
- **Profiles**: `field_contact_columns` 47.79 → 41.75 ms a section (0.874); the kernel total 478.8 → 473.4.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 494.2, 493.9, 494.2, 494.3, 494.2
  (spread 0.4); this build 487.1, 487.5, 487.4, 486.5. The means are 494.2 and 487.1: 0.986, 7.0 ms a section. Paired run by run the
  differences are −6.8, −6.7, −6.9 and −7.7 ms: resolved.
- **Guesses** (fixed before the read):
  - this thread's (14:03 UTC): gate 3 equal, held; that line under 0.08, held (0.008); the columns 0.85–0.95 a launch, held by profile
    (0.874) and missed on the side of less on four launches (0.79–0.86); the section 0.985–0.996, held at its edge (0.986);
  - the theory thread's (14:03 UTC): that line 0.05–0.10, missed on the side of less; `receiver_at` under 0.06, held; the columns
    0.91–0.96, missed on the side of less; the section 0.991–0.996, missed on the side of less. Its premise, a conversion of about 0.3 of
    a removed share into time at 28 warps a multiprocessor, read low: 0.20 of the samples removed took 0.13 of the columns' time, about
    0.6 here, because the removed loads were also instructions (the column addresses and the index chain) and not only waits.
- **What follows.** The columns' next wait stands on the receiver's probe in the bracket's line. Its loads no longer wait on a located
  index, so they can stand in flight for several receivers at once.
- **Into the line.** The hold wrote this build as the chain's next on the equal gate at 14:36 UTC; lap 66 had read #911 before, so it
  trains from lap 67.
