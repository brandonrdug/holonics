# Receipts: the columns ask for a receiver's probe as soon as the receiver is known (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 66 (15:03 to 15:19 UTC). Control: #913 (`athena_colgather`),
the line's binary from lap 67. Sections: lap 66's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3.
The source counters after the gather (`../2026-11-16_colgather/source_lines_colgather.txt`) chose it: the bracket's line, which waits on
the receiver's probe, held 0.255 of `field_contact_columns`' stall samples. In #913's machine code the probe's load stood after the whole
of the skin's branchy path (`paced_hs`, `support_entry`'s search, `decay_hs`, `pair_skin_word`), so it waited behind the skin's own loads.

- **The change** (`crates/engine-cuda/kernels/field.cu`, `field_contact_columns`). The receiver's probe `pq[(first + i) · S + entry]` and
  its covector entry `dyr[i · S + entry]` are loaded as soon as `i` is read from the warp's shared rows, before the skin is formed, and
  the source's own word `words[j · S + entry]` is read once before the receiver loop. In the machine code the probe's `LDG.E.64` and the
  covector's load now stand two instructions after the `LDS` of `i`. The same integers in the same order, so no bit moves.
- **Compiled** (ptxas at `sm_89`): 72 registers, no spill, seven blocks a multiprocessor as before.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Source counters** (`source_lines_913.txt`, `source_lines_colprobe.txt`, two launches each): stall samples 104,095 → 95,525 (0.918),
  warp instructions 497.0 → 479.2 million (0.964); the bracket's line 0.257 → 0.177 of the samples.
- **Counters** (`NCU_ROWS`, eight launches): 0.976, 0.938, 0.918, 0.925, 0.934, 0.950, 0.934 and 0.941 of the control's.
- **Profiles**: `field_contact_columns` 41.83 → 40.00 ms a section (0.956); the kernel total 472.6 → 472.0.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 486.8, 485.3, 487.9, 486.9, 486.7
  (spread 2.6); this build 484.6, 485.7, 483.9, 484.0. The means are 486.7 and 484.6: 0.9955, 2.2 ms a section. Paired run by run the
  differences are −0.7, −2.2, −3.0 and −2.7 ms, every one on the side of less, two of them past the control's spread and the mean inside
  it: not resolved by the hold's own rule, though the profile and every launch read the same direction.
- **Guesses** (fixed before the read):
  - this thread's (14:44 UTC): gate 3 equal, held; the bracket's line 0.12–0.20, held (0.177); the columns 0.955–0.985, held by profile
    (0.956) and missed on the side of less on seven launches (0.918–0.950); the section 0.996–0.999, missed on the side of less (0.9955);
  - the theory thread's (14:45 UTC): the line 0.10–0.18, held; the columns 0.95–0.98, held by profile and missed on the side of less on six
    launches; the section 0.995–0.999, held. Its premise of two conversions (the hoisted word's load and instructions at about 0.6, the
    early probe at about 0.35) read: 0.082 of the samples and 3.6% of the instructions removed took 4.4% of the columns' time.
- **Into the line.** The hold wrote this build as the chain's next on the equal gate at 15:17 UTC; lap 67 had read #913 before, so it
  trains from lap 68.
