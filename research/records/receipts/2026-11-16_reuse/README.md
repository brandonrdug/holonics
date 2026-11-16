# Receipts: the forward contact's crowds staged once for their shares, and the row's pace index read once (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 45 (01:26 to 01:45 UTC). Control: the carry-save build
(#866), the line's binary from lap 46. Sections: lap 45's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for
gate 3.

- **The change** (`crates/engine-cuda/kernels/field.cu`, `contact_body`). Pass three formed each crowd's share by computing its score
  again (`crowd_score`, then `term_of`'s face). The crowds' chunk already holds that term: its face in `st0` and, now, its bits above the
  row's least in `stk`, which a crowd's numerators never read. Pass three reads them from the warp's slot (the same lane holds the same
  slot in both passes) with the same expression for the share. The pace index, a property of the row's head, is read once a row rather
  than in every term's product. Every bit is kept: the inputs, the lane and the expression are the same.
- **Compiled** (ptxas at `sm_89`, the four-limb entry): 80 registers in both; spills 430/888 octets (stores/loads) in the carry-save
  build, 310/624 here.
- **Gate 1 passed; gate 3 equal** (`hold.txt`): parity on 3 sections, 3 and 24 sections reproduced, the cavity table byte for byte.
- **Counters** (`ncu_counters.txt`; three four-limb launches of `field_contact_l4`, each build). A launch fell from 4.30–4.33 to
  3.37–3.42 ms (0.784), its executed warp instructions from 1.570–1.585e9 to 1.243–1.258e9 (0.793). The no-instruction stall (the warps
  waiting on the instruction fetch) halved, 0.92–0.97 to 0.42–0.43 an issued instruction, with the kernel's code smaller; long-scoreboard
  stalls rose from 3.42–3.50 to 3.68–3.71, the loads now the larger share of what is left.
- **Profiles** (`PROFILE_PAIR`, ms a section over 24 sections): `field_contact_l4` 48.9 → 39.0; the rows 65.7 and 66.0, the columns 57.3
  and 58.2, the exposure 17.9 and 18.0.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 595.4, 595.3, 604.7, 607.2,
  607.7; reuse 584.2, 587.2, 568.5, 567.2. The card changed state between the hold's two halves (the control read 595 in the first and
  605 to 608 in the second), so the builds are compared state by state: 0.984 in the first half and 0.935 in the second, 0.958 over the
  hold. The profile's 9.9 ms a section in the forward contact, about 0.984 of a section, is the reading that holds in both states.
- **The theory thread's guess** (fixed 00:55 UTC): gate 3 equal (held); l4 0.88–0.94 of carry-save a launch (read 0.784, a miss on the
  side of more); the exposure within 3% (held, 1.006); a section 0.990–0.996 (read 0.984 in the steadier half, a miss on the same side).
  The guess counted the crowd score's own instructions and not the code it took from the instruction cache (`agent-inferred`).
- **Into the line.** The hold wrote this binary as the chain's next on the equal gate; the chain had already read lap 46's (carry-save),
  so this build trains from lap 47.
