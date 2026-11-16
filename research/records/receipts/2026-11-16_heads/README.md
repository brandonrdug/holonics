# Receipts: the return reads its head's ring set once, and the columns' products stand on the words P54 bounds (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 47 (02:29 to 02:47 UTC). Control: the reuse build (#867),
the line's binary from lap 47. Sections: lap 47's `STATE.3000` (the first lap of the prefix's third pass) for the counters, the profiles
and the timing hold, lap 17's for gate 3.

- **What the source counters showed** (the reading of the gap after lap 46, on a `-lineinfo` copy of the reuse build). In
  `field_contact_columns` one line held 0.547 of the stall samples and 0.396 of the instructions: the key's bracket formed three 128 by
  128 products, and the covector's product a fourth, where P54's table bounds them (the skin `D ≤ 2^30`, the probe and the word 32 bits
  each). In `field_contact_rows`, `h mod frames < still` (`still_head`, under `skinless`) held 0.059 of the samples and 0.068 of the
  instructions: the head is the launch's argument, but every term's skin, carried value, decay and pace test divided by the frames again.
- **The change** (`crates/engine-cuda/kernels/field.cu`). `HeadSkin` holds a head's skinlessness, pace index and decay slot, formed once a
  launch, and the `_hs` helpers read it in the rows' and columns' loops. The columns' bracket is `mul32(D, probe)` shifted, less
  `mul32(D, D)` times the word as one 64 by 64; it lies under `2^92` and is released to under `2^63`. The covector times it is one 64 by 64,
  and the share times the carried value (under `2^63`) is its magnitude's product. Each is the same integer as the product it replaces.
- **Compiled** (ptxas at `sm_89`): the columns 72 registers and no spills, as before; the rows 128 registers with 20/44 octets of spills
  (8/8 before), from the head's words held live.
- **Gate 1 passed; gate 3 equal** (`hold.txt`).
- **Counters** (`ncu_counters.txt`; the first four launches matching either kernel, which are one head's rows and columns on two ticks).
  The rows 1.304 → 1.225 and 1.153 → 1.078 ms a launch (0.94), their instructions 0.91–0.92. The columns 0.867 → 0.804 and 0.727 → 0.671
  ms (0.92–0.93), their instructions 0.98: these launches are of a head whose bracket's products the change shortens least, so the
  profile over all launches is the columns' reading.
- **Profiles** (`PROFILE_PAIR`, ms a section over 24 sections): the columns 56.6 → 47.8 (0.845), the rows 64.5 → 60.5 (0.938); the forward
  contact 38.8 and 38.1, the exposure 17.5 and 17.6; no other entry moved by more than 1.2 ms.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 584.3, 584.6, 584.7, 583.3, 584.5
  (spread 1.4); the return build 572.8, 570.4, 570.6, 570.1. Means 584.3 and 571.0: 0.977, 13.3 ms a section, the rows' and columns' 12.8.
- **The theory thread's guess** (fixed 02:02 UTC): gate 3 equal (held); the columns 0.85–0.95 a launch (0.92–0.93 on the launches ncu read,
  0.845 over all launches by the profile); the rows 0.90–0.96 (0.94; 0.938 by the profile); a section 0.975–0.992 (0.977).
- **Into the line.** The hold wrote this binary as the chain's next on the equal gate; the chain had read lap 48's (reuse) before, so it
  trains from lap 49.
