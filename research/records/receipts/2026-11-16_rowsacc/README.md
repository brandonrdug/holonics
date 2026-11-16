# Receipts: the pair covector on two partials changes nothing, and the rows' source counters place their waits (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 62 (12:37 to 12:53 UTC). Control: #903 (`athena_rows`), the
line's binary. Sections: lap 62's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3. The attempt is
the theory thread's lead of 10:52 UTC; its code is not merged.

- **The attempt** (`crates/engine-cuda/kernels/field.cu`, `pair_dp8` in `field_contact_rows`). The pair covector's sixteen 128-bit adds
  went into two partials, the even entries' and the odd entries', added once at the end: two chains of eight in place of one of sixteen.
  The terms meet at one grain and are added once, so no bit moves. ptxas at `sm_89`: 128 registers, spill 28 → 16 octets of stores and
  52 → 28 of loads.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Counters** (`hold.txt`, `NCU_ROWS`, eight launches of each build on 2 of lap 62's sections): a launch at 0.994, 0.999, 1.003, 1.005,
  0.994, 0.996, 1.003 and 1.000 of the control's, with 0.3% more instructions. Long scoreboard and wait stand where they stood.
- **Profiles**: `field_contact_rows` 59.29 → 59.46 ms a section; the kernel total 477.9 on both.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 492.0, 492.3, 492.0, 492.0, 493.2
  (spread 1.2); this build 491.3, 492.4, 491.9, 491.0. The means are 492.3 and 491.7, 0.9987. Paired run by run the differences are −1.0,
  +0.4, −0.1 and −2.2 ms, inside the control's spread: unresolved.
- **Guesses**: gate 3 equal (both threads), held. This thread's (12:24 UTC) rows 0.985–1.000 a launch missed at the edge on four launches
  (1.003–1.005); its section 0.998–1.001 held. The theory thread's (12:17 UTC) rows 0.96–0.995 missed on six of eight; its section
  0.996–1.000 held.
- **Where the rows' work and waits stand** (`source_lines.txt`, by `rows_lines.py`, a ruler, on a `-lineinfo` copy of #903's code, two
  launches: 599.1 million warp instructions, 182,503 stall samples; each line of the kernel's body by itself, every other line under the
  function that opens above it):
  - the pair covector's first product line holds 0.100 of the samples on 0.050 of the instructions, three quarters of them long
    scoreboard: the wait on the source's value row arriving, not on the chain of adds (its wait is 0.06 of the line's samples). The
    second line holds 0.026. So the attempt's premise did not stand where the attempt reached;
  - `add_wide`'s atomic add of the low word, whose returned word the high word's carry waits for, holds 0.077 of the samples on 0.011
    of the instructions, 0.92 of them long scoreboard. Most of the rows' calls are the crowds' returns, four a crowd a lane (the
    difference arrays `cw` and `cv` at a crowd's two ends), each waiting out its own round trip before the next is issued;
  - pass B's staged products hold 0.114 of the instructions and 0.068 of the samples (wait 0.35, short scoreboard 0.13);
  - `crowd_base_narrow` 0.057 and 0.056; the crowds' sums 0.043 and 0.044, with 45% of that line's L2 sectors in excess of the ideal;
  - the divisions (`divide_word`, `divisor_of`, `div_nearest_by`, `div_nearest`, `divide_by`) 0.151 of the instructions and 0.068 of the
    samples;
  - `support_at` 0.017 and 0.045; the comparison's gather 0.021 of the samples, 32% of its sectors in excess.
- **The rows' memory** (`NCU_ROWS`; the theory thread's premise of 12:18 UTC). The one launch: 4.9–7.1 sectors a request on global
  loads; L1 at 23.7–30.5% of its peak, L2 at 31.9–43.3%, DRAM at 21.9–28.3%; shared memory at 12.9–14.7 million wavefronts a launch,
  with bank conflicts about 8% of them. The split's pass A alone (`athena_rowsfission`, four launches): 6.4–7.0 sectors a request; L1 at
  41.4–57.2%, L2 at 40.0–53.1%, DRAM at 31.9–45.8%; long scoreboard 5.2–7.5. No unit stands near its peak, so the lead of four lanes a
  support, which waited on L1 near its peak, is not built.
- **What follows.** The crowds' returns issue each crowd's four low-word atomics before any high word, so their four round trips stand
  together. Integer sums on `Z/2^128` in any order, so no bit moves.
