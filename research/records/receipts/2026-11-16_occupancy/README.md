# Receipts: the outer sum takes its rows' bias in the same launch; the spread at two blocks a multiprocessor (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 58 (09:50 to 10:07 UTC). Control: #896 (`athena_regionscan`),
the line's binary from lap 59. Sections: lap 58's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3.

- **The changes** (`crates/engine-cuda/kernels/field.cu`, `crates/engine-cuda/src/hnn/{contact,adjoint,level,moment,resident}.rs`).
  Integer sums, so no bit moves.
  - With a bias address given, the outer tiles of the first column block sum the rows' bias `Σ_t y_t` from the words they stage, or over
    the walk on 128 bits in the wide form, into `g[bias + o]`. One thread for each four rows does it, and the narrow partial goes in only
    where the walk ends narrow. Before, the bias had a launch of its own over the same `y` and sites.
  - The thirteen call pairs (a weight and its bias over one `y`) are one `outer_biased` call each. The two bias-only calls with no partner
    launch alone as before.
  - `field_spread` runs 640 threads, 20 warps, so that two blocks stand on a multiprocessor at its 48 registers. The register file's four
    quarters hold 10 warps of 1,536 registers each.
- **Compiled** (ptxas at `sm_89`): `field_outer_x32` 126 → 128 registers with 12 octets of spill stores, `field_outer_x64` 126 → 128 with
  none, `field_spread` 48.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Counters** (`ncu.txt`).
  - The outer sums with a weight, matched by grid: 405 blocks 76.3 → 77.9 µs (1.02), 204 blocks 164.3–166.1 → 175.2–178.3 (1.07),
    148 blocks 81.7–88.1 → 86.7–93.9 (1.06).
  - `field_spread` 43.1–43.8 → 45.1–45.3 µs (1.04). It now stands two blocks a multiprocessor in one wave (0.77 waves, warps active 44% →
    58%). The busiest multiprocessor's cycles hold at about 101,000 where the least busy's fell to 25,000, so a multiprocessor's two blocks
    take about as long as the one-block build's two waves.
  - The blank walks, unchanged in source, read their spread over the card: `field_blank_bias_enc`'s multiprocessors are active 887,832 to
    1,237,185 cycles (mean 0.88 of the most) and its schedulers 688,737 to 1,241,215 (0.77). So equal tiles finish unevenly across the card
    and within a multiprocessor, which is where their warps active stands at 56%.
- **Profiles** (`PROFILE_PAIR`, ms a section over 24 sections):
  - `field_outer_x32` 20.12 → 13.83, its launches 8,544 → 3,648 (204 fewer a section);
  - `field_outer_x64` 5.12 → 5.54;
  - the kernel total 486.8 → 481.6.

  The profile synchronizes around every launch, about 30 µs each, so its fall is mostly the launches removed. Under the theory thread's
  note of 09:28 UTC, the section is scored on the hold.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal):
  - control 496.5, 495.7, 496.3, 494.5, 495.3 (spread 2.0);
  - this build 494.4, 494.3, 494.7, 494.5.

  The means are 495.7 and 494.5: 0.998, 1.2 ms a section. Paired run by run with the control beside each, the differences are 1.3, 2.0,
  −0.2 and 0.8 ms. The difference lies inside the control's own spread, so the hold does not resolve it.
- **Guesses**:
  - gate 3 equal (both threads): held;
  - the theory thread's (09:32 UTC), the section 0.995–0.999: 0.998, held. Its `field_outer_x32` 1.00–1.04 and `field_outer_x64` 1.00–1.03:
    1.02 to 1.07, a miss at the larger grids;
  - this thread's (09:35 UTC), the outer launches 1.00–1.05: a miss at the 204-block shapes (1.07). Its section 0.990–0.997: a miss on the
    side of less;
  - the theory thread's (09:29 UTC), the spread 0.60–0.85 of #896's time a launch: 1.04, a miss. The two blocks on a multiprocessor share
    its issue, so a wave of two blocks costs what two waves of one did.
- **What follows.** The bias as a column of ones staged beside `x` (the theory thread's lead of 09:33 UTC) would carry the same sum with no
  registers of its own and no spill. The spread's walk is set by the busiest multiprocessor's two regions, so its next form divides a
  region's walk between blocks.
- **Into the line.** The hold wrote this build as the chain's next on the equal gate. Chain 17 had read lap 59's binary (#896) before, so it
  trains from lap 60.
