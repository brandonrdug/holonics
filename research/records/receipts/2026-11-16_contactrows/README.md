# Receipts: the contact rows' pass B stages its words by asynchronous copies (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 60 (11:14 to 11:30 UTC). Control: #901 (`athena_biasshared`),
the line's binary from lap 61. Sections: lap 60's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3. The
theory thread's pick of 10:52 UTC chose it. Its premise was that pass B's inner loop waited on one `words[jx · S + entry]` load a pair.

- **The change** (`crates/engine-cuda/kernels/field.cu`, `crates/engine-cuda/src/hnn/adjoint.rs`). The rows take a dynamic shared array of
  `REV_ROWS · 16 · S` words of 32 bits, 4 KB a block at the line's span of 16, beside their 20,128 octets of static shared memory. For each
  half of a chunk's 32 staged pairs, each lane copies the words it then reads with `__pipeline_memcpy_async` (4 octets each), commits, waits
  once and forms its products from shared memory. `mul32` reads the word on 32 bits, so the products are the same. A full chunk of 64-bit
  words (8 KB a warp) would have cut the rows below four blocks a multiprocessor.
- **Compiled** (ptxas at `sm_89`): 128 registers, spill 20 → 28 octets of stores and 28 → 52 of loads.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Counters** (Nsight Compute, the first eight launches on 2 of lap 60's sections): a launch at 0.976, 0.981, 0.995 and 0.982 of the
  control's (1,113.6–1,702.9 µs → 1,092.6–1,663.5). Long scoreboard fell from 3.78–4.18 to 3.02–3.58 an issued instruction, issue rose from
  35.6–37.9% to 37.6–40.7%, and the blocks a multiprocessor held at 4 by registers and by shared memory.
- **Profiles**: `field_contact_rows` 60.54 → 59.50 ms a section (0.983); the kernel total 475.0 → 475.1.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal):
  - control 489.8, 490.0, 489.4, 489.2, 489.4 (spread 0.8);
  - this build 489.2, 488.2, 488.4, 489.6.

  The means are 489.6 and 488.9: 0.999, 0.7 ms a section. Paired run by run with the control beside each, the differences are 0.8, 1.2, 0.8
  and −0.2 ms. That is at the control's own spread, so it is not resolved.
- **Guesses**:
  - gate 3 equal (both threads): held;
  - the theory thread's (10:52 UTC) rows 0.86–0.94 a launch, the section 0.986–0.994: 0.98 and 0.999, both missed on the side of less;
  - this thread's (11:05 UTC) rows at 4 blocks still: held. Its 0.88–0.96 a launch and the section 0.988–0.996 missed on the side of less.

  The words' loads held about a fifth of pass B's long-scoreboard waits, not most of them.
- **Into the line.** The hold wrote this build as the chain's next on the equal gate. It trains from lap 62.
