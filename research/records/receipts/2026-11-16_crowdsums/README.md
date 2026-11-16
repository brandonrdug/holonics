# Receipts: the crowds' sums read their rows whole, and the columns' source counters place their waits (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 64 (13:42 to 13:57 UTC). Lap 64 closed the pass at 632
sections, so the counters, profiles and timing hold read lap 63's `STATE.3000`; gate 3 reads lap 17's. Control: #909
(`athena_rowsatomics`), the line's binary from lap 65. The rows' source counters of the gap after lap 62 chose it (the crowds' sums 0.050
of the rows' stall samples, 45% of their L2 sectors in excess), and the theory thread read the same layout at 13:37 UTC.

- **The change** (`crates/engine-cuda/kernels/field.cu`). In `field_contact_rows`' pass A a crowd's sum `Σ_x δỹ_i[x] · D(Δv)[x]` is
  formed by a part's lanes over the span's entries, one crowd at a time, as the crowds' returns already read them: each lane holds its one
  `δỹ_i` entry, reads its entry of the crowd's two summed rows (a row whole across the part, 16 octets a lane), and the part's lanes add
  their terms by a tree (`entries_sum`: exclusive-or offsets 1 to S/2 where the span divides the warp, else the warp's sum). The sum is
  staged in `dpcs` and divided by its crowd's lane as before. A lane's term is formed only under `active && jj < nslots` and a nonzero
  count, else it is 0: where the span does not divide the warp, the lanes past it wrap to entries already held, and the guard keeps them
  out of the warp's sum (the theory thread's check of 13:43 UTC). A ring sum in any bracketing, so no bit moves.
- **Compiled** (ptxas at `sm_89`): 128 registers, spill 28 → 36 octets of stores and 52 → 60 of loads.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Source counters** (`source_lines_909.txt`, `source_lines_crowdsums.txt`, by `../2026-11-16_rowsacc/rows_lines.py`, two launches each):
  the crowds' sums' line 0.050 → 0.023 of the rows' stall samples, with the tree 0.013 and the guards about 0.011 beside it. The block's
  L2 sectors 13.8 million, 45% of them in excess of the ideal, → 6.9 million with under 0.3% in excess. The kernel's stall samples
  216,754 → 218,161 and its instructions 2.2% more on these two launches.
- **Counters** (`NCU_ROWS`, eight launches of each build): 1.004, 1.028, 0.951, 0.961, 0.997, 0.995, 0.968 and 0.975 of the control's: the
  two smaller shapes 1.00–1.03, the two larger 0.95–0.975, where the instructions fell 2.7%.
- **Profiles**: `field_contact_rows` 58.58 → 57.54 ms a section (0.982); the kernel total 477.2 → 476.4.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 491.5, 490.1, 491.6, 491.8 and
  535.6; this build 489.6, 490.5, 490.1, 491.1. The last control ran 13,161 ms against 12,070–12,122 for every other run, a disturbance of
  the card at the hold's end, and is set aside. The means are 491.3 and 490.3: 0.998, 0.9 ms a section. The three pairs with an undisturbed
  control beside them differ by −0.5, −1.1 and −1.7 ms, inside the controls' spread of 1.7: unresolved.
- **Guesses** (fixed before the read):
  - this thread's (13:45 UTC): gate 3 equal, held; the share 0.015–0.030, held by the line (0.023) and missed with its tree (0.036); the
    lines' excess under 15%, held; the rows 0.985–0.997, missed on both sides by launch (0.951–1.028) and on the side of less by profile
    (0.982); the section 0.998–1.001 unresolved, held;
  - the theory thread's (13:37 UTC): the share 0.015–0.030, as above; the excess under 10%, held; the rows 0.985–0.995, missed as above;
    the section 0.998–1.000, held.
- **The columns' waits** (`source_lines_columns_909.txt`, the same ruler on #909's `field_contact_columns`, two launches: 524.8 million
  warp instructions, 117,482 stall samples). The line that adds `δs_ij` times the bracket holds 0.233 of the samples, two thirds of them
  long scoreboard on `δs_ij` (`ds` read down a column of the region's block, `i · sites + j`); the bracket's line 0.134 (half long
  scoreboard on the receiver's probe); the share's line 0.082; `receiver_at`, which locates receiver `i` before any of these loads can
  issue, 0.142. Each pass of the loop waits on a chain: the receiver's index, then its column entries. So the columns' next form gathers a
  chunk of 32 receivers at once, a lane a receiver with its `δs_ij` and `p_ij`, before the lanes over the span read them.
- **Into the line.** The hold wrote this build as the chain's next on the equal gate at 13:54 UTC; lap 65 had read #909 before, so it
  trains from lap 66.
