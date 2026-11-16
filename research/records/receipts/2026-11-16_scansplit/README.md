# Receipts: the carry circles' scans carry one store a step, their other terms off the chain (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 53 (06:44 to 07:01 UTC). Control: #883, the line's binary
from lap 54. Sections: lap 53's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3. The theory thread's
reading of the two chains (its 05:40 UTC note, recorded in #881) chose the split; the scans ran at about 7% of warps active, one thread a
(region, circle), in the order the law declares, a section at every step.

- **The change** (`crates/engine-cuda/kernels/field.cu`, `crates/engine-cuda/src/hnn/{contact,adjoint}.rs`). The same terms on the same
  operands, and the refusals are an OR.
  - Forward. `field_pair_scan` carries `Q` alone (`pqm` written, then `Q = fit64(κb + rel(γQ, 30))`). The face `p = a·Q(t∓1)`, which the
    chain never reads back, is formed after it by `field_pair_scan_face` on the pair's grid from the operand the scan kept (`pqm`, a
    fitted word, so the same `Q`).
  - Reverse. `field_pair_scan_pre` forms, before the chain, the terms that read no `u`: `δa = conj(Qm)·δp` and the pair part
    `h = conj(a)·δp`, which it keeps on 128 bits in `dh` until it meets the chain's sum before that sum's one fit. `field_pair_scan_back`
    carries `u` alone (`db = u`, `u ← fit64(h + rel(conj(γ)u, 30))`). `field_pair_gate_back` forms `δγ = conj(Qm)·u` from `db` and `pqm`
    and writes it before anything in it can refuse, so a refused cell keeps `δγ` as before.
  - Each chain reads its step's operands a step ahead.
- **Compiled** (ptxas at `sm_89`): `field_pair_scan` 62 registers (56 before), `field_pair_scan_back` 78 (78), `field_pair_scan_pre` 40,
  `field_pair_scan_face` 38, `field_pair_gate_back` 66; no spills.
- **Gate 1 passed; gate 3 equal** (`hold.txt`).
- **Counters** (`ncu_counters.txt`). The forward scan fell from 727–744 µs a launch to 259–263 µs (0.35), and its face kernel takes 42.5 µs.
  The reverse scan fell from 836–838 µs to 277 µs (0.33), and its pre-kernel takes 75 µs. The forward scan's issue rose from 25.8% to
  43.4% of peak with long scoreboard from 2.3–3.0 to 0.5–0.6 an issued instruction. The grid kernels wait on their loads (long scoreboard
  35 to 36) at full width, which is what they are for.
- **Profiles** (ms a section over 24 sections, `hold.txt`): the carry circles' kernels together 22.7 → 12.4 (`field_pair_scan` 9.17 → 3.38,
  `field_pair_scan_back` 11.29 → 4.21, `field_pair_gate_back` 2.25 → 2.08, the new `field_pair_scan_face` 0.88 and `field_pair_scan_pre`
  1.83; `field_pair_gamma` 1.54 in both).
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 545.8, 547.7, 546.2, 545.9,
  548.1 (spread 2.3); this build 535.4, 536.4, 535.9, 535.0. Means 546.7 and 535.7: 0.980, 11.0 ms a section. Paired run by run with the
  control beside each (547.7 with 535.4, 546.2 with 536.4, 545.9 with 535.9, 548.1 with 535.0), the differences are 12.3, 9.8, 10.0 and 13.1 ms.
- **The theory thread's guesses** (fixed 05:47 UTC, #882): gate 3 equal (held); the forward scan 0.50–0.75 a launch (0.35, a miss on the
  side of more); the reverse 0.30–0.55 (0.33, held); the grid kernels 0.03–0.10 of the old scans' time (0.13, 2.71 of 20.46 ms, a miss on the
  side of less, while the gate's reverse, which now forms `δγ`, fell by 0.17 ms); 7 to 13.5 ms a section (11.0, held); the section 0.975–0.987 (0.980, held).
- **The blanks' DRAM throughput** (`blanks_dram.txt`, on #883, two launches each). `field_blank_bias_enc` ran at 8.2% of peak with
  69% of its L2 sectors hit, `field_blank_dy` at 12.6–13.3% (40–48% hit) and `field_blank_lift_read` at 3.6–3.9% (80–82% hit). The
  bytes do not bind them.
- **Into the line.** The hold wrote this binary as the chain's next on the equal gate. Chain 16 had already read lap 54's binary (#883),
  so this build trains from lap 55.
