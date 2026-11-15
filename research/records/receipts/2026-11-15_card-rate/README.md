# Receipts: a section's realization, first loop (Brandon, November 15 15:19: "40 minutes a lap is a lot")

Device: the RTX 4080 SUPER, the line's sections from lap 31's `STATE.3000` (24 of them), the line's binary as control.

- The profile (`FIELD_PROFILE`, every launch timed alone) puts about 662 ms a section in the card's kernels: the contact family (rows, the
  fifth lane's contact, columns, exposure) about 200 ms, the clocks and skins (the paced skins' return, the clock and skin fills, the paces,
  the moments under them) about 110 ms, the maps (outer sums, transposes, affine tiles) about 120 ms. An unprofiled section reads 695 ms, so
  the card is busy about 95% of it: the time is the kernels' own work.
- Five realization changes, each keeping every bit: the stage's lists built region by region across the host's cores and joined in order;
  each kernel's handle looked up once; `field_paces`, `field_pace_kappa_back` and `field_moment_skinned_all` as block scans (their terms are
  each released before they enter a sum, so the sums are order-free); `field_blank_dz` forming the blank clock's mean once a site and head.
- Gate 3 on lap 17 is equal for the first four and for all five (`lines.txt`). The five's comparisons were run by hand on its finished
  runs, because `tools/gate_engine.sh` was edited while it ran.
- Timing, the first four, one balanced hold: the control 717 to 724 ms a section, the build 704 to 708 (`RATE_TIMING`), about 2%. The
  stage's lists did not move (their phase is the card's wait at a batch's drop, not host work); the scans give the rest.
- The line runs on the five's build from lap 34 (chain 12), its reads beside its next lap.
