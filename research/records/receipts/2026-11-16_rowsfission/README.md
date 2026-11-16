# Receipts: the contact rows split into two launches, an attempt measured slower and kept out of the line (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 61 (11:55 to 12:11 UTC). Control: #903 (`athena_rows`),
the line's binary from lap 62. Sections: lap 61's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3. The
attempt is commit `46a760526`, reverted on its branch so that `main` carries it in its history beside this receipt.

- **The attempt** (`crates/engine-cuda/kernels/field.cu`, `crates/engine-cuda/src/hnn/adjoint.rs`). `field_contact_rows` became one
  template over its two passes with two entries. Pass A (`field_contact_rows_a`) forms the pairs' covectors, the crowds' covectors and the
  row's mean, and writes the mean (a site's 128 bits) and the crowds' covectors (a site's slots) to memory. Pass B (`field_contact_rows_b`)
  reads them back and forms the comparison's covector, the probe role and the crowds' returns. Integers written once and read once, so no
  bit moves. Its premise: the one launch holds both passes to pass B's 128 registers and four blocks a multiprocessor, with pass B's spill,
  and pass A alone would stand at six blocks and hide its loads.
- **Compiled** (ptxas at `sm_89`): pass A 80 registers, 10,912 octets of shared memory, no spill; pass B 128 registers, 20,128 octets, no
  spill (the one launch: 128, with 28 octets of spill stores and 52 of loads).
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Counters** (`ncu.txt`, the launches in order, the control's first six matched to this build's six pairs):
  - a pair A + B against the one launch: 1,163.4 / 1,139.0 (1.02), 1,045.7 / 1,035.3 (1.01), 1,541.3 / 1,419.2 (1.09), 1,671.5 / 1,531.6
    (1.09), 1,188.0 / 1,161.4 (1.02), 1,067.1 / 1,060.5 (1.01) µs;
  - pass A alone took 0.27 to 0.29 of the one launch, at six blocks a multiprocessor and 43% warps active against the one launch's 27 to
    29%, while its long-scoreboard waits rose to 5.5–8.4 an issued instruction (the one launch's 2.9–3.6);
  - pass B took 0.73 to 0.82 of the one launch at the same 128 registers and four blocks. Its waits on the two larger shapes, 4.35 and 4.46
    against 3.51 and 3.55, are the mean and the crowds' covectors read back;
  - the pair issued 3 to 4% more instructions than the one launch (`hold.txt`, `NCU_BLANK` lines).
- **Profiles** (`PROFILE_PAIR`, ms a section over 24 sections): `field_contact_rows` 59.96 → `_a` 19.88 + `_b` 49.08 = 68.96 (1.15), with
  96 more launches a section; the kernel total 476.9 → 485.2. The profile synchronizes around every launch, so it overstates the split's
  cost by about 3 ms a section, and the section is scored on the hold.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal):
  - control 491.7, 492.7, 493.2, 493.1, 492.9 (spread 1.5);
  - this build 498.7, 499.0, 498.3, 498.6.

  The means are 492.7 and 498.7: 1.012, 5.9 ms a section more. Paired run by run with the control beside each, the differences are 6.0,
  5.8, 5.2 and 5.7 ms, each past the control's own spread, so the hold resolves it: the split is slower.
- **Guesses**:
  - gate 3 equal (both threads): held;
  - this thread's (11:42 UTC), the rows A + B 0.88–0.98 of the one launch and the section 0.990–1.000: 1.01–1.09 by the counters and 1.012,
    both missed on the side of more;
  - the theory thread's (11:39 UTC), 0.87–0.97 and 0.985–0.996: both missed the same way.

  The premise failed at pass A. Half again as many warps bought it no time: its waits grew with its warps, so its loads' latency is not
  hidden by occupancy at this shape, and pass B, freed of its spill at the same four blocks, ran no faster for it. The rows' time is set by
  their loads and the chains that depend on them, not by the register file.
- **What follows.** The rows stay one launch (#903). The lever left in them is the dependence inside a pair's products, which a next build
  reads on the one launch.
- **Kept out of the line.** The hold wrote this build as the chain's next on the equal gate at 12:09 UTC; the chain's next was set back to
  #903 before lap 63 read it, and lap 62 had read #903 at lap 61's end. No lap trained on this build.
