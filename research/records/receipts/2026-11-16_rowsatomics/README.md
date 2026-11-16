# Receipts: the crowds' returns put their four low words in flight together (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 63 (13:18 to 13:35 UTC). Control: #903 (`athena_rows`), the
line's binary. Sections: lap 63's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3. The source counters
of the gap after lap 62 (`../2026-11-16_rowsacc/`) chose it: the atomic add of a crowd's low word, whose returned word the high word's
carry waits for, held 0.077 of the rows' stall samples on 0.011 of their instructions.

- **The change** (`crates/engine-cuda/kernels/field.cu`). `add_wide`'s step on `Z/2^128` is also written as its two halves:
  `add_wide_low` adds the low word and returns the word it found, `add_wide_high` adds the high word with the carry read from that word.
  In `field_contact_rows` the crowds' returns, the four ring sums into the difference arrays `cw` and `cv` at a crowd's two ends, issue
  their four low words before any high word. In #903's machine code they ran as low, high, low, high, two round trips one after the other;
  here the four `ATOMG.E.ADD.64` stand back to back and the four `RED.E.ADD.64` follow. Each term's carry is read from its own low word's
  add, so any order and any interleaving leave the same 128 bits.
- **Compiled** (ptxas at `sm_89`): 128 registers, spill unchanged (28 octets of stores, 52 of loads).
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Source counters** (`source_lines_903.txt`, `source_lines_atomics.txt`, by `../2026-11-16_rowsacc/rows_lines.py`, a ruler, on
  `-lineinfo` copies of both builds, two launches each on lap 63's sections). The low word's wait fell from 0.089 of the rows' stall
  samples (on these sections) to 0.034: `add_wide_high` 0.031, the rest 0.003. The first high word of a crowd holds 0.020 of it, the later
  three 0.008 together, so a crowd waits one round trip. The kernel's stall samples fell from 222,453 to 215,494 (0.969), on 0.5% more
  instructions.
- **Counters** (`NCU_ROWS`, eight launches of each build): a launch at 0.977, 0.978, 0.979, 0.981, 0.976, 0.971, 0.982 and 0.984 of the
  control's.
- **Profiles**: `field_contact_rows` 59.46 → 58.33 ms a section (0.981); the kernel total 470.0 → 469.4.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 480.2, 480.3, 480.1, 480.1, 480.6
  (spread 0.5); this build 479.5, 478.6, 479.5, 479.4. The means are 480.3 and 479.3: 0.998, 1.0 ms a section. Paired run by run the
  differences are −0.8, −1.5, −0.6 and −1.2 ms, each past the control's spread: resolved.
- **Guesses** (both fixed before the read):
  - this thread's (13:00 UTC): gate 3 equal, held; the low word's share 0.077 → 0.02–0.04, read 0.089 → 0.034 on these sections, held;
    the rows 0.95–0.985 a launch, held (0.971–0.984); the section 0.993–0.998, held at its edge (0.998);
  - the theory thread's (13:02 UTC): the share 0.030–0.045, held; the rows 0.965–0.985, held; the section 0.995–0.999, held.

  The share fell by 0.055 of the samples and the rows' time by about 2%: each sample of a wait converts to about 0.35 of its share in
  time here, because the other warps' work fills part of it.
- **What follows.** A carry-save form with no returned word (the theory thread's lead of 13:02 UTC: three 64-bit words a difference entry,
  each a reduction) would remove the remaining 0.031. At this conversion that is about 1% of the rows, near 0.6 ms a section, against the
  spread's reads of `cw` and `cv` at 1.5 times their octets; it is not built until the spread's load share is read.
- **Into the line.** The hold wrote this build as the chain's next on the equal gate at 13:32 UTC. Chain 18 had read lap 64's binary
  (#903) before, so it trains from lap 65.
