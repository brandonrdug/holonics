# Receipts: the release is one add and one shift; the skin return keeps its five blocks (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 54 (07:29 to 07:47 UTC). Control: #885 (`athena_scansplit`), the
line's binary from lap 55. Sections: lap 54's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3. The issue
table (`../2026-11-16_issue/issue_by_kernel.txt`) and its source counters chose the target: `rel` held 0.33 to 0.36 of the instructions of
`field_tied_back_e` and `field_pair_scan_back` and 0.18 of `field_pace_skin_back`'s.

- **The change** (`crates/engine-cuda/kernels/field.cu`). `rel(x, b)` for `b > 0` is `(x + h − [x < 0]) >> b` with `h = 2^(b−1)`: for `x < 0`,
  `−⌊(−x + h)/2^b⌋ = ⌊(x + h − 1)/2^b⌋`, and `>>` on a signed word is the floor. The two-branch form negated twice and selected. The quotient
  is the same wherever that form did not overflow, and `rel(x, 0) = x` keeps its guard. The 64-bit series product's inline release is
  written the same way. The theory thread's ruler read the identity equal on 52,699 reads for every `b` from 1 to 127.
- **Compiled** (ptxas at `sm_89`, no spills but the one below). Twelve entries' registers moved:
  - `field_pace_skin_back` 96 → 104. At 128 threads that is 13,312 registers a block, four blocks a multiprocessor where 96 held five (the
    theory thread's reading, 07:11 UTC). So a second realization bounds it, `__launch_bounds__(128, 5)`: 96 registers, 32 octets of spill
    stores and 44 of loads.
  - `field_pair_scan_back` 78 → 72, `field_pair_scan` 62 → 64, `field_pair_back` 48 → 40.
  - `field_moment_return_prefix` 56 → 64. No host code launches it.
- **Gate 1 passed. Gate 3 equal on the bounded realization** (`hold.txt`): parity on 3 calls, 3 and 24 sections reproduced, the cavity read
  equal. The hold profiled both realizations first and gated the one whose `field_pace_skin_back` profiled lower (744 ms over 24 sections
  against 798). The two differ in that entry alone.
- **Refused beside the lap.** The first hold ran gate 3 for both beside lap 54 with no lock, as the card-lock rule allows. All three runs were
  refused at 07:15 UTC: the lap's pool held 10.7 GB of the 16 (its budget 10.8 GB from 15.8 GB free at its open), and with 4.6 GB left
  "the exponential's resident face passes the card's batch budget". The guide now says so beside the rule.
- **Counters** (`ncu_inst.txt`; every launch of one section, each launch serialized). Per launch against the control:

  | kernel | instructions | time | registers, blocks a multiprocessor |
  |---|---|---|---|
  | `field_tied_back_e` | 0.786 | 0.823 | 34, 6 |
  | `field_pair_scan_back` | 0.862 | 1.001 | 78 → 72, 3 |
  | `field_pace_skin_back`, unbounded | 0.873 | 1.000 | 104, 5 → 4 |
  | `field_pace_skin_back`, bounded | 0.868 | 0.921 | 96, 5 |

  The other kernels read: `field_clock_fill` 0.963, `field_contact_columns` 0.974 (with instructions 1.032), `field_exposure` 0.982 and
  `field_contact_rows` 0.994. `field_chart`, `field_skin_fill` and `field_contact_l4` read within 0.006 of 1.

  The reverse scan's chain latency binds it, so its fewer instructions bought no time.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal):
  - control 534.2, 534.9, 532.7, 534.6, 532.5 (spread 2.4);
  - this build 522.7, 523.5, 523.6, 522.8.

  The means are 533.8 and 523.2: 0.980, 10.6 ms a section. Paired run by run with the control beside each (534.9 with 522.7, 532.7 with
  523.5, 534.6 with 523.6, 532.5 with 522.8), the differences are 12.2, 9.2, 11.0 and 9.7 ms.
- **Profiles** (`hold.txt`, `PROFILE_PAIR`, one run of each build). The per-entry changes match the counters: `field_pace_skin_back` 32.4 →
  31.0, `field_tied_back_e` 9.0 → 7.5, `field_clock_fill` 20.6 → 20.1. The totals read 521.2 for the control and 522.3 for this build, but
  each is one run with its entries scattered about ±0.9 ms (`field_spread` +0.9, `field_contact_l4` +0.6). The control's profile ran
  7 minutes after the others, behind the gate and the counters. Under the timing standard, the section is read on the hold.
- **Guesses**, fixed at dispatch (07:09 UTC):
  - gate 3 equal: held;
  - instructions 0.82–0.92 in `field_tied_back_e`: 0.786, a miss on the side of more;
  - instructions 0.85–0.95 in `field_pair_scan_back`: 0.862, held;
  - instructions 0.92–0.98 in `field_pace_skin_back`: 0.873, a miss on the side of more;
  - the section 0.985–0.997 (3 to 8 ms): 0.980 (10.6 ms), a miss on the side of more.

  The guesses fixed at 07:12–07:14 UTC were for `field_pace_skin_back`'s time:
  - the theory thread's, 0.97–1.06 a launch at four blocks: 1.000, held;
  - this thread's, 0.90–0.97 at five: 0.921, held.
- **The blanks' stall split** (`blank_stalls.txt`, the theory thread's ask (a) of 07:04 UTC, on the control):

  | entry | ms a launch | issue active | warps active | stalls an issued instruction | of them long scoreboard |
  |---|---|---|---|---|---|
  | `field_blank_bias_enc` | 2.18–2.26 | 28–33% | 97% | 36–42 | 29–35 |
  | `field_blank_dy` | 1.40–1.55 | 42–47% | 96% | 25–28 | 16–20 |
  | `field_blank_lift_read` | 1.30–1.31 | 36% | 95% | 32 | 24.5 |

  L1 hit 74–83%. With DRAM at 4–13% of peak (`../2026-11-16_scansplit/blanks_dram.txt`), each thread waits on its own chain of loads over
  its 512 sites at full occupancy.

  The blank covector's nonzero share (ask (b)) has its reading in this change (`FIELD_BLANK_LIVE` with the profile, admitted among the
  store command's readings). Its first run was refused by the command's guard on unlisted variables, and it is read in the next gap.
- **Into the line.** The hold wrote the bounded realization (`athena_rel5`) as the chain's next on the equal gate. Chain 16 had already read
  lap 55's binary (#885), so this build trains from lap 56.
