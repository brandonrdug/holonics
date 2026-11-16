# Receipts: the forward contact at four resident blocks (November 15, set aside)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 42 (23:16 to 23:32 UTC). Control: the line's limbs build
(#852). The build (`claude/contact-blocks` at 295d6ab90) set `CONTACT_MIN_BLOCKS` to four, so the forward contact and the
exposure compile at 128 registers with no spills in their walk, where at six blocks they hold 80 and spill (the record of the evening,
§9).

- **Gate 3 equal** (`hold.txt`): 3 and 24 sections reproduced, the cavity table byte for byte.
- **Counters** (`ncu_stalls.txt`, `ncu_six_blocks_details.csv`, `ncu_four_blocks_details.csv`; three four-limb launches of
  `field_contact_l4`, each build). At four blocks a launch took 5.00–5.09 ms against 4.70–4.76 ms at six. The spills' local loads went:
  the LSU pipe's share fell from 21.4% to 12.6% of peak and long-scoreboard stalls from 3.16 to 1.59 an issued instruction. A third of
  the resident warps went with them, and the warps left could not hide the remaining latency (`agent-inferred`).
- **Timing, one balanced hold** (`hold.txt`, ms a section, every run's 24 section lines equal): control 568.6, 574.4, 575.6, 574.6, 578.3
  (mean 574.3); four blocks 595.5, 587.5, 578.8, 579.0 (mean 585.2), 1.019. Set aside: the kernel is latency-bound and occupancy is what
  hides it, so registers bought by fewer warps cost more than the spills they remove.
