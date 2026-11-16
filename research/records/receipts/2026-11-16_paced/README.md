# Receipts: the pace skin's return, the outer products' bias and the maps' tile staging (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 49 (03:53 to 04:11 UTC). Control: the return build (#870),
the line's binary from lap 49. Sections: lap 49's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3.
The changes come from the source counters read in the gaps after laps 46 and 48 (ncu on a `-lineinfo` copy, the ruler
`research/records/receipts/2026-11-16_carrysave/source_shares.py`).

- **The changes** (`crates/engine-cuda/kernels/field.cu`). The integers are the same in each.
  - (lift) `field_pace_skin_back` reads its pace test once a row. A paced head's skins read its clock over the receiver's region, a property
    of the row's receiver, and the kernel asked it at every pair's every mode: `paced_index` and `paced_at` held 0.115 of its samples.
  - (c) The same kernel's checked products of a 64-bit word by a wide one (`e·inner`, `ds·bracket`, the crowds' four) are formed 64 by 128
    by `mul_fits_w64`, from the wide word's halves, with the overflow read from the words above. `mul_fits` counted both operands' bits
    first (`wide_bits` 0.122 of samples, `mul_fits` 0.077). Both give the product where it fits and refuse where it does not.
  - (fold) `outer_bias_tile` sums its walk on 128 bits in one pass. Before, it read the walk once for its largest magnitude and again for
    the sum, and the first read held 0.496 of `field_outer_x32`'s samples.
  - (stage) `map_tile` stages each warp's chunk as eight terms of four rows (`map_stage`), with each staged row padded by four words, so a
    warp's 32 shared stores fall on 32 banks. Before, all 32 fell on one bank, and the store held 0.225 of `field_transposed`'s samples
    on 0.039 of its instructions.
- **Gate 1 passed; gate 3 equal** (`hold.txt`).
- **Counters** (`ncu_counters.txt`; the first eight launches of the four kernels, which happened not to include the pace skin's return).
  The bias launches of `field_outer_x32` fell from 105.4, 73.0 and 74.9 µs to 80.3, 45.6 and 47.3 (0.62 to 0.76), its instructions to
  a third. Its outer-tile launch did not move (220.0 and 220.6). `field_transposed` read 216.1 → 217.6 and 126.1 → 130.0 µs: its MIO throttle and
  short-scoreboard stalls fell (0.22 → 0.14, 0.55 → 0.39 an issued instruction) while long scoreboard stood at 5.5 to 7.0, so the stalls at
  the store were the loaded word's wait. `field_affine_tiled_x32` read 0.97 and 1.007.
- **Profiles** (`PROFILE_PAIR`, ms a section over 24 sections): `field_pace_skin_back` 35.2 → 30.9 (0.878), `field_outer_x32` 22.0 →
  20.4, `field_affine_tiled_x32` 19.1 → 18.3, `field_transposed` 26.5 → 26.3, `field_affine_tiled_x64` 7.6 → 7.3. The entries that moved
  sum to 7.2 ms a section less, about 0.987 of a section.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 565.3, 566.1, 580.9, 566.0,
  586.7; the paced build 574.1, 568.3, 572.3, 560.2. The control's own spread is 21.4 ms, three times the profile's difference, so the
  hold does not resolve the section. Its means (573.0 and 568.7) read 0.992. The profile's per-kernel entries are the reading here.
- **The theory thread's guesses** (fixed 02:49, 03:29 and 03:33 UTC). Gate 3 equal held. (lift) and (c) together: `field_pace_skin_back`
  0.69–0.85 a launch, read 0.878 by the profile, a miss on the side of less. (fold): `field_outer_x32` 0.50–0.75, its bias launches read
  0.62–0.76 and the kernel over all launches 0.927 (its outer tiles unchanged). (stage): `field_transposed` 0.80–0.92, read 0.99, a miss. The
  decider the thread named held: the store's samples were the load's wait, so the next tile's load belongs behind the current MAC. The
  tiled affine maps 0.85–0.96 or within 3%: read 0.958 and 0.96. Section 0.945–0.978: unresolved by the hold (0.992 at its means, 0.987 by
  the profile).
- **Into the line.** The hold wrote this binary as the chain's next on the equal gate; chain 16 had read lap 50's (#870) before, so it
  trains from lap 51.
