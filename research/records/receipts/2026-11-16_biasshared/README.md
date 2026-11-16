# Receipts: the outer sums' bias partial in shared memory, spread over every warp; the spread back at 672 (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 59 (10:32 to 10:49 UTC). Control: #899 (`athena_occupancy`),
the line's binary from lap 60. Sections: lap 59's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3.

- **The changes** (`crates/engine-cuda/kernels/field.cu`, `crates/engine-cuda/src/hnn/resident.rs`). Integer sums, so no bit moves.
  - The bias partial of #899 stood in four registers a thread on one thread in sixteen. Now it stands in shared memory, a word a row and
    quarter. After each chunk's products, thread `j` adds row `j mod 64`'s staged words at the chunk's places `kc ≡ ⌊j/64⌋ (mod 4)`, so
    every warp carries eight adds a chunk and none stands behind the barrier for them (the theory thread's lead of 10:13 UTC). The four
    quarters meet at the walk's end, behind the chunk loop's last barrier. The walk's closing barrier stands before the next walk zeroes
    them.
  - `field_spread` returns to 672 threads.
- **Compiled** (ptxas at `sm_89`): `field_outer_x32` at 128 registers with no spill (12 octets in #899), `field_outer_x64` at 128 with 8
  octets of spill stores, `field_spread` at 48.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Counters** (Nsight Compute, 2 of lap 59's sections, a launch matched by grid against the control):
  - `field_outer_x32`: 156 blocks 0.946, 158 blocks 0.936, 216 blocks 0.938, 431 blocks 0.989;
  - `field_outer_x64`: 158 blocks 0.979, 216 blocks 0.939;
  - `field_spread` (128 blocks): 50.0 → 46.4 µs (0.928).
- **Profiles** (ms a section over 24 sections): `field_outer_x32` 14.29 → 13.71, `field_outer_x64` 5.83 → 5.46, `field_spread` 8.50 →
  7.25.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal):
  - control 495.4, 494.9, 495.7, 496.3, 495.1 (spread 1.4);
  - this build 494.4, 496.3, 496.0, 495.0.

  The means are 495.5 and 495.4: 1.000. The difference is inside the control's spread, so the hold reads none.
- **Guesses**:
  - gate 3 equal (both threads): held;
  - this thread's (10:15 UTC, fixed on the one-quarter form and scored on this build):
    - the outer sums 0.93–1.00 at the 204- and 148-block grids: held (0.936–0.979);
    - the spread 0.94–0.98: 0.928, a miss on the side of more;
    - the section 0.996–1.000: held at its edge;
  - the theory thread's second guess (10:14 UTC, for this four-quarter build):
    - the outer sums 0.94–0.97: held but at two grids (`x32` 158 blocks 0.936, `x64` 158 blocks 0.979);
    - the spread 0.95–0.97: a miss on the side of more;
    - the section 0.997–1.000: held.
- **Into the line.** The hold wrote this build as the chain's next on the equal gate; it trains from lap 61.
