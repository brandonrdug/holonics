# Receipts: the regions' prefix walks chunked across a block; the blank walks' tile is one a thread (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 57 (09:09 to 09:25 UTC). Control: #892 (`athena_blankload`),
the line's binary from lap 58. Sections: lap 57's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3.

- **The changes** (`crates/engine-cuda/kernels/field.cu`, `crates/engine-cuda/src/hnn/{contact,adjoint,resident}.rs`). Integer sums
  throughout, so no bit moves.
  - `field_spread` runs 672 threads a region (21 chunks of the span of 32), where 256 gave 8. Its chunk scan takes any count.
  - `field_sums` is a block of 1,024 a head and a region. Its `2S + 1` entries' chunks are summed, scanned across the block and walked again
    to the outputs. Before, one thread an entry walked a region's sites in order, 12,480 to 13,061 threads a launch.
  - The blank live walks' tiles are `⌊want / entries⌋`, each `⌈n / tiles⌉` sites long, so no cell passes `want` and no thread walks a second
    tile.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Counters** (`ncu.txt`; the first launches on 2 sections). A launch against the control:
  - `field_spread` 68.0–68.6 → 43.4–44.1 µs (0.64), issue 8.6% → 14.5%, warps active 23% → 44%. Its registers allow one block of 672 a
    multiprocessor, not two. The register file is split across the four schedulers, 16,384 registers each, so 42 warps of 1,536 registers
    need 11 a scheduler where 10 fit. Two blocks need at most 20 warps a block (640 threads).
  - `field_sums` 259–260 → 81–82 µs on the larger launches (0.32) and 34.6–34.8 → 26.2–26.5 on the smaller. Issue 5.5% → 29%, warps active
    8.5% → 66.5%.
  - `field_blank_bias_enc` 828 → 780 µs (0.94) and `field_blank_lift_read` 447 → 444 (0.99), one launch each. Warps active stood at 57–60%
    in both builds.
- **Profiles** (`PROFILE_PAIR`, ms a section over 24 sections):
  - `field_spread` 8.46 → 7.17 (0.85), at 96 launches a section, about 75 µs each with the profile's synchronization;
  - `field_sums` 5.00 → 2.17 (0.43);
  - `field_blank_bias_enc` 5.50 → 5.46 and `field_blank_lift_read` 3.38 → 3.33;
  - the kernel total 491.8 → 489.5.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal):
  - control 500.4, 500.0, 499.8, 500.0, 500.3 (spread 0.6);
  - this build 495.4, 496.2, 495.7, 496.8.

  The means are 500.1 and 496.0: 0.992, 4.1 ms a section. Paired run by run with the control beside each, the differences are 4.6, 3.6,
  4.3 and 3.5 ms.
- **Guesses**, fixed at 08:52 UTC:
  - gate 3 equal: held;
  - `field_spread` 0.30–0.55 of its time a section: 0.85 by the profile and 0.64 a launch by the counters, a miss on the side of less. The
    block stands one a multiprocessor, and the profile's 96 launches a section carry their synchronization;
  - `field_sums` 0.25–0.50: 0.43, held;
  - the blank walks 0.60–0.75 a launch, with warps active 72–83% (the theory thread's guess, 08:46 UTC): 0.94 and 0.99, with warps active
    at 56–57%, a miss. That guess's own test reads it: the tail is not the tiles' ceiling;
  - the section 0.973–0.983: 0.992, a miss on the side of less.
- **Into the line.** The hold wrote this build as the chain's next on the equal gate. Chain 17 had already read lap 58's binary (#892), so
  this build trains from lap 59.
