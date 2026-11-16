# Receipts: the outer products' tile fetches its walk's next chunk behind its products; the blank covector's checked products (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 52 (06:01 to 06:17 UTC). Control: #877, the line's binary
from lap 52. Sections: lap 52's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3. The issue activity
that chose these two (`../2026-11-16_issue/issue_by_kernel.txt`): `field_outer_x32` issued at 18.9% of peak with 25% of its warps
active, `field_outer_x64` at 22.4%, and in `field_blank_dy` `wide_bits` and `mul_fits` held 0.20 of the instructions.

- **The changes** (`crates/engine-cuda/kernels/field.cu`). The words and the integers are the same in each.
  - `outer_tile` gets `map_tile`'s fetch: the walk's next chunk is read into registers once the current chunk is staged and proved
    narrow, and staged after the current chunk's products are summed. ptxas at `sm_89`: 126 registers in both entries, no spills,
    shared memory unchanged.
  - `field_blank_dy` checks its product of the wide covector by a 32-bit weight with `mul_fits_w64`, with no bit count.
- **Gate 1 passed; gate 3 equal** (`hold.txt`).
- **Counters** (`ncu_counters.txt`; the first twelve launches of the two outer entries). The outer-tile launches fell from 220.3,
  228.4, 213.9 and 214.1 µs to 168.7, 166.7, 164.4 and 164.2 (0.74 to 0.77). Their long scoreboard fell from 5.3–5.9 to 1.8–2.0 an
  issued instruction. The bias launches did not move. Blocks a multiprocessor stood at 2 in both builds (the registers' limit; shared
  memory allows 3), and warps active held at 28%.
- **Profiles** (`PROFILE_PAIR`, ms a section over 24 sections): `field_outer_x32` 22.4 → 21.0 over all its launches, its many short
  bias launches unchanged; `field_outer_x64` 6.1 → 5.2; `field_blank_dy` 12.0 → 10.9. In all, about 3.4 ms a section less.
- **Timing, one balanced hold** (`RATE_TIMING`): control 550.7, 550.3, 558.1, 535.5, 531.5 (spread 26.6 ms); this build 547.7, 547.5,
  518.3, 547.2. The control's spread is eight times the profile's difference, so the hold does not resolve the section, and the
  profile's entries are the reading.
- **The theory thread's guesses** (fixed 05:00 and 05:37 UTC): gate 3 equal (held); the outer tiles at under half of peak issue
  0.76–0.88 a launch (0.74–0.77, at the guess's edge on the side of more), with the blocks a multiprocessor kept (held at 2); `field_blank_dy`
  0.88–0.98 a launch over all its launches (0.91 by the profile, held); the section unresolved.
- **Into the line.** The hold wrote this binary as the chain's next on the equal gate; chain 16 had read lap 53's (#877) before, so it
  trains from lap 54.
