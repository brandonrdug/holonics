# Receipts: the forward contact's numerators as a carry-save sum (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 44 of the line (00:38 to 00:56 UTC). Control: the line's
binary, the limbs build (#852). Sections: lap 44's `STATE.3000` for the profiles and the timing hold, lap 17's for gate 3.

- **The change** (`crates/engine-cuda/kernels/field.cu`, the term loop of `contact_body`). The limbs build added each signed term
  `x = value × source` to a 256-bit group sum with a carry detected and propagated at every term (two 128-bit adds, two compares,
  a select). The carry-save build splits each term's product into six 32-bit chunks, adds them into six lane-private 64-bit sums
  with the term's sign word, and propagates the carries once, when the group's limb changes or the row ends. Every chunk sum is a
  sum of co-present terms at one grain, released once, so the bits are the limbs build's (gate 3 below).
- **Gate 3 equal** (`hold.txt`): parity on 3 sections, 3 and 24 sections reproduced, the read's cavity table byte for byte.
- **Counters** (`ncu_counters.txt`; Nsight Compute on three four-limb launches of `field_contact_l4`, each build, 2 of lap 44's
  sections). A launch fell from 4.83–4.88 to 4.65–4.67 ms (0.957) and its executed warp instructions from 1.704–1.723e9 to
  1.641–1.659e9 (0.963). Both builds hold 80 registers and six resident blocks. Issue stays at about 50% of peak; long-scoreboard
  stalls rose from 3.18 to 3.42 an issued instruction and math-pipe throttle fell from 0.75 to 0.68: with the carries' chain gone, the
  warps wait on their loads.
- **Where the kernel's work and waits stand** (`source_shares_limbs.txt`, by `source_shares.py`, a ruler, on a `-lineinfo` copy of
  the limbs build: two launches, each line of `field.cu` at 2866ae635 assigned to the function that opens above it). The term
  loop's own lines in `contact_body` hold 0.327 of the executed instructions and 0.271 of the stall samples. The crowds' scores
  (`crowd_base`, `lock_of`, `mul_fits`, `add_fits`, `wide_bits`, `div_nearest` and the crowd skin) hold about 0.26 of the
  instructions, and the shares pass computes each crowd's score a second time. `paced_index` is 0.036 of the instructions, called
  per term on the row's own head. The skin's loads stand far above their instructions: `skin_word` 0.074 of the samples on 0.004
  of the instructions, `pair_skin_word` 0.071 on 0.017, `support_at` 0.031 on 0.011, `crowd_skin_word` 0.025 on 0.009.
- **Profiles** (`hold.txt`, `PROFILE_PAIR`, ms a section over 24 sections): `field_contact_l4` 49.2 → 47.1; every other entry within
  0.2 ms (the rows 66.2 and 66.3, the columns 57.7 and 57.5, the exposure 18.1 and 18.0).
- **Timing, one balanced hold** (`hold.txt`, `RATE_TIMING`, ms a section, every run's 24 section lines equal): control 605.8, 605.4,
  604.0, 603.3, 603.8; carry-save 601.3, 601.6, 603.1, 602.9. Means 604.5 and 602.2, 0.996. Each pair of carry-save runs stands
  under the controls on both sides of it (by 2.4 to 4.5 ms in the first block, 0.2 to 0.9 in the second), while the controls'
  own spread is 2.5 ms, so the section's gain stands at the hold's resolution; the profile's 2.1 ms a section in the forward
  contact alone, with nothing else moving, is the reading that decides it. The theory thread's guess (l4 0.86–0.94, a section
  0.985–0.995) missed on the contact and stood at its edge on the section; it scores the miss in its record.
- **Into the line.** The hold wrote the carry-save binary as the chain's next binary on the equal gate; the chain reads it before
  lap 46 (lap 45 had opened at 00:56:31 on the limbs build).
