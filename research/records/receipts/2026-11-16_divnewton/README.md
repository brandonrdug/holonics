# Receipts: the crowds' divisors' reciprocal by Newton steps, the same integers and no measured time (November 16)

Device: the RTX 4080 SUPER, under the card's lock in the gap after lap 67 (15:44 to 16:01 UTC). Control: #915 (`athena_colprobe`), the
line's binary from lap 68. Sections: lap 67's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3. The
theory thread's lead of 15:22 UTC chose it.

- **The change** (`crates/engine-cuda/kernels/field.cu`). `divisor_of`'s reciprocal `v = ⌊(2^128 − 1)/d⌋ − 2^64` of a normalized `d` is
  formed by Möller and Granlund's Algorithm 2 (`reciprocal_word`: a first approximation from `d`'s top nine bits by one 32-bit division,
  two Newton steps and a third in 64-bit products, one adjustment) in place of a 128 by 128 division in software. It reaches the contact
  rows' crowds (two divisors a crowd lane), the pace skin's return's crowds (two a crowd) and the forward contact's top-limb divisor.
- **The host ruler** (`reciprocal_ruler.c`, C with a 128-bit reference): 433,554,434 values, every `k` and `k²` normalized for `k < 2^24`,
  the four edges `2^63`, `2^63 + 1`, `2^64 − 2`, `2^64 − 1` and 400 million random normalized words, none unequal; a planted one-bit error was
  caught 12,256 times in 83 million. The theory thread checked the adjustment against the paper's step 10.
- **Gate 1 passed. Gate 3 equal** (`hold.txt`).
- **Source counters** (`source_lines-*.txt`, two launches each). The reciprocal held less than the lead's premise: `divisor_of` was 0.020 of
  the rows' instructions and 0.024 of the pace return's, the division inlined there. It is now 0.010 and 0.014 (`reciprocal_word` with
  `divisor_of`). The kernels' instructions 709.5 → 701.7 million (rows) and 1,099.9 → 1,088.2 million (pace return), each 1.1% fewer;
  their stall samples 223,089 → 223,414 and 294,740 → 293,256.
- **Counters** (`NCU_ROWS`, the rows, eight launches): 1.008, 1.009, 0.975, 1.006, 1.032, 1.005, 0.988 and 1.027 of the control's.
- **Profiles** (ms a section): `field_contact_rows` 57.08 → 57.58, `field_contact_l4` 38.92 → 38.42, `field_pace_skin_back` 30.42 → 30.42;
  the kernel total 471.1 → 470.9.
- **Timing, one balanced hold, disturbed** (`RATE_TIMING`): control 475.9, 478.3, 530.0, 483.4, 474.9; this build 479.8, 486.8, 489.9,
  479.6. The hold was not alone: from 15:56 to 16:06 UTC this thread built and ran a host reading (the cold-restart receipt, whose command
  opens the card) and gate 1 on the host, against the rule that every other build on the host is paused during a hold. The third control ran
  13,043 ms against 11,700–12,070 for the others, and the controls' spread without it is 8.5 ms. The timing reads nothing; the counters
  and the profile, which do not depend on the host's load, read no change.
- **Guesses**: gate 3 equal (both threads), held. The reciprocal's own instructions under a fifth (both threads): missed, about half,
  since its premise (the routine about 0.09 of the rows' instructions) read 0.020. This thread's rows 0.975–0.995 and the theory thread's
  0.96–0.985: missed, about 1.00. The pace return 0.97–0.995 (this thread) and 0.96–0.99 (theory): missed, 1.000 by profile. The sections'
  guesses are not scored, the hold being disturbed.
- **Into the line.** The change keeps every bit and removes a software division's loop; it enters on its gate as a realization with no
  measured gain. The hold wrote it as the chain's next at 15:57 UTC; lap 68 had read #915, so it trains from lap 69.
