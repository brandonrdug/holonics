# Receipts: the open places' face in the maps' tile form, and two readings of the contact (November 15)

Device: the RTX 4080 SUPER, the line's sections (24 from lap 36's `STATE.3000`), the line's binary (`athena_maps`, #839) as control.

- **The face through the encoding and the lift's covector in the tile form.** `field_tied_face` and `field_tied_back_y` ran one thread a cell
  over every term on 128 bits; both are maps (the encoding's rows `A × D` over the lift, and their transpose over the face's covector) and
  now run in `map_tile`, which takes the release's bits, a bias added after the release and zeros at the skipped sites as template
  parameters. Profiled entry by entry in one hold (`lines.txt`, `PROFILE_PAIR`): the face 17.2 ms a section to 4.9, its return 4.5 to 2.0.
- **The open places' per-entry sums walk 512 sites a thread** (`BLANK_TILE`, from 64): fewer atomic adds, the same bits, and no measured
  change (15.7, 9.2 and 9.5 ms before and after): their atomics were not what bound them.
- **The moments' clock covector sums a receiver's own skin terms once a site**: one atomic step a term where it took two; 8.1 ms to 7.9.
- Gate 3 on lap 17 equal: parity on 3 sections, 24 sections reproduced, the read's cavity table byte for byte.
- Timing, one balanced hold: the control 637.5 to 664.6 ms a section, the build 629.0 to 649.4, every run's 24 section lines equal; pair by
  pair the build reads 0.984 and 0.981 of the control. The face's entry changed by a multiple and stands on the profile; the whole
  section's gain, about 1.6%, sits inside the control's spread of 4%.
- **The rows' pair covector on 64 bits, set aside.** `field_contact_rows` formed `⟨δỹ_i, D ṽ_j⟩` as a 64-bit sum where every value stood
  under `2^31` and the row's covector's l1 times the pair's largest value under `2^63`, the same integer; gate 3 equal, and in one balanced
  hold on lap 35's sections it read 656 to 665 ms a section against a control of 629 to 667: no difference. The arithmetic of pass A is not
  what binds the rows (the November 12 ablation read their memory walk alone at about half their time).
- **The return's covector read by the bits ruler** (`dyh`, which no ruler had read; the engine record §9): 31 bits at the largest, 25 to 27
  at the 0.999 quantile, the values at 23 (`lines.txt`, `FIELD_BITS`).
