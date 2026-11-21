# The widths read on the line: half the face grain's steps are silent, nine places under the point carry what the mean reads, and the kernel's widths are the host's

November 21, the lead, 20:10 to 21:00 UTC. Refs #1088. This is E1 to E3 of [the precision record](2026-11-21_A_WIDTH_IS_A_TOLERANCE_A_WORDS_TOP_GROWS_BY_ITS_CARRY_ITS_BOTTOM_STANDS_WHERE_THE_UNREAD_TAIL_NO_LONGER_MOVES_ITS_RECEIVERS_CODE_AND_THE_LATTICE_RULE_THAT_DERIVED_THE_ENGINES_WIDTHS_WAS_BUILT_IN_OCTOBER_AND_NEVER_TAKEN.md)'s
§9. Its guesses were fixed by the formal thread at 19:23Z and are scored beside them
([`receipts/2026-11-21_widths/GUESS.txt`](receipts/2026-11-21_widths/GUESS.txt)). The state read is W80t, the line at W79t's end plus 3,000
sections with no change (its STATE.3000 and MEAN.3000). The held read is the 800 frontier rows of held text read by two streams (139,998
places, `read-reach` on the host).

## 1. The reads

| read | what came out | guess |
|---|---|---|
| G-W0, the top: `\|θ\|` by block | the largest is 19.8, and the 99.9th hundredth is under 4 in 60 of 65 blocks; over 4 in `read_bias` (18.9), `pace` (19.7), `before` (5.1), `after` (4.6), `v` (4.2) | held on the largest, missed on the hundredth |
| G-W1, the material's bottom for the mean: every entry rounded to `2^(−g)` | the held code rises 0.00019, 0.00037, 0.00069, 0.0025 and 0.030 nats a place at `g` = 12, 10, 9, 8, 6 | held: the coarsest `g` under 0.001 is 9 |
| G-W2, the standing spread: the rms of the lap's end less its mean | from `2^(−10.2)` to `2^(−6.7)` by block; nine blocks above `2^(−7.8)`, the face-grain encodings among them | missed at the top |
| G-W2b, a place under the spread priced as the walk | the end stands 0.0405 nats a place over the mean; the quotient is 19.2, 2.36, 1.10, 0.99 and 0.76 at `g` = 12, 10, 9, 8, 6 | held from 9 to 12, at its edge at 8 |
| G-W3, the states' bottom: every state rounded to `2^(−g)` after each tick | under 0.0001 for every `g` down to 5; +0.0012 at `g` = 1 at the lap's end | missed: the state's bottom stands about 15 places above its grain |
| G-W4, the deposit's silent steps | of the moving entries, 4.9%, 10.6% and 27.2% release to zero at rates 12, 16 and 20. On the material's grain: 0.08%, 1.2% and 19.5%. On the face's grain (174,865 entries: the encodings `E`, `E₋`, `E₊`, the moments' encodings, every bias): **50.4%**, 99.6% and 100% | missed at 12 and 16 by the face grain |
| G-W5, a covector's coherence: the cosine between successive sections at one state | 0.65 to 0.83 over the whole material, and by family from 0.30 to 0.90 | missed: it was guessed near zero |

## 2. What they say

- **The deposit drops half of the symbol rows' steps.** An entry's step is `((m ≪ grain) ≫ rate)/root`. On the face's grain `2^(−16)`
  at rate `2^(−12)` that is `16 m/root`, which releases to zero wherever `|m/root|` is under a sixteenth. Half of the encodings'
  moving entries stand there in a section, and with no remainder carried (W80t's state has no `remainder` line) those steps are lost,
  not delayed. On the material's grain the same step loses a thousandth. The grain picked for the face's families decides which slow
  fluxes exist in the symbols' rows. E4's carried remainder makes it a delay.
- **Nine places under the point carry what the mean reads.** Rounding every entry to `2^(−9)` costs the held code 0.0007 nats a place,
  and to `2^(−8)` 0.0025. Where the rounding's variance passes the walk's own spread (`g` = 8 and coarser), it is priced as the walk is
  (quotient 1). Finer, a place costs more than its variance share (2.4 at `g` = 10, 19 at 12), because the deposit's steps are even over
  the entries while the code's curvature is not. For the mean's receiver the material's read part is about 9 to 10 places. The October
  lattice rule asks 18 places at `2^(−10)` nats for every symbol of every place, so E5 reads its blocks against both receivers.
- **The states carry nothing below about `2^(−1)`.** Each lane is read through its own power, and a state's scale stands far above its
  grain, so its sixteen places under the point read nothing the code reads. A state's bottom is relative to its lane's power. That is
  where E5 and E9 place a state's width.
- **A covector's news is coherent across sections.** At one state, successive sections' covectors stand at a cosine of 0.65 to 0.83.
  The first moment's eight sections then average one direction, not eight draws. Together with the walk's thousand-section cosines
  near −0.2 (THE_ENGINE §11), this says the line's deposit moves along a coherent covector at a fixed step and overshoots. That is the
  cooling law's subject, and here it is read.

## 3. E2 and E3, as built

- **E2, one owner for widths** (a realization). The number owner of the October library (`crates/holonics/src/number` at `d5ed4adc1`,
  laws N1 to N8, its guards' doctests) stands in `crates/engine/src/number`, with its tests and its `compile_fail` guards passing. The
  eight literal widths are written as their derivations: `REMAINDER_BITS = STEP_BITS − FACE_BITS`, `CONTACT_BITS = COVECTOR_BITS + FACE_BITS`,
  `WEIGHED_DIGITS = UNIT_BITS − 2`, `PACED_L1 = 2^(MOVE_BITS + 1)`, `LN2_BITS = MOVE_BITS`, and `units.rs`'s and `coupling.rs`'s private
  copies named from `width.rs`. The width census reads literal 8 → 0 and picked 15 → 13. Every value is the same number, so every bit is
  kept.
- **E3, one declaration for host and kernel** (a realization). The card crate's build script writes the kernels' widths
  (`widths.cuh`) from `holonics_engine::width::kernel_widths`, the host's own declarations. The kernels no longer declare `FACE_BITS`,
  `MATERIAL_BITS`, `MOVE_BITS`, `COVECTOR_BITS`, `UNIT_BITS`, `CONTACT_BITS`, `SHARE_BITS`, `TEMPER_TOP`, `LN2_FACE_BITS` or `PACE_BITS`.
  The dead `CARRIED_BITS` and `HOLD_BITS` are gone, and `CONTACT_BACK` is the host's `CONTACT_BITS + FACE_BITS − COVECTOR_BITS`, which
  `adjoint.rs` now reads by name. The census reads dead 2 → 0. The kernels' PTX is byte for byte the image the tree compiled before.

## 4. E4, built, and its arm

Every release of the deposit returns its remainder. The step's remainder already had its law, the learner's `remainder` line of
November 18, and the line ran without it. The moments' forced grain becomes a carried remainder (`toward_carried`,
`Learner::carried`, two trailing lines of the state). A moment moves as `t = (g − m) + r`, `m ← m + release(t, rate)`, and `r` keeps the
rest inside half of its rate's grain, so `m + r 2^(−rate)` tracks the moment's true mean within a grain (Lean
`Foundation/CarriedRelease`, `release_tracks`; atlas `deposition.moment-remainder-carried`). A test reaches a constant input and tracks
a quarter-grain input within two fine grains over 20,000 sections. `set-rate RATE OUT remainder moments` founds both at zero. A state
without the lines reads, writes and trains as before, and the build reproduced W80g's lap with them off (gate 3).

The arm W81e (W80g's end with both carried) runs beside W81t (W80g's end, no change), its guess G-E4 fixed first
([`GUESS_E4.txt`](receipts/2026-11-21_widths/GUESS_E4.txt)). Its premise is §2's first point. Its reading is added here when it lands.
