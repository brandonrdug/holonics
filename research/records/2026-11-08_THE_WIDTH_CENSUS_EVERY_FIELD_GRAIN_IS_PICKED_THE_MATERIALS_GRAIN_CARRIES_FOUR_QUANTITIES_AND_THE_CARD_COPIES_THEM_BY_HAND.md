# The width census: every grain the field reads is picked, the material's grain carries four quantities, and the card copies the widths by hand

> **Note of November 11.** The census was read at a tip that held the energy field. Its rows for the energy field's host owner, card owner and kernel header name code that left the tree on November 11 and is at [`b6ff1f795`](https://github.com/brandonrdug/holonics/tree/b6ff1f795); the rows for the face field, the material's grain and the number owner stand ([the port's record](2026-11-11_THE_TRAINING_LINE_BECOMES_THE_TRUNKS_FIELD_THE_ENERGY_ATTEMPT_LEAVES_THE_TREE_AND_A_READING_A_LINE_IS_SCORED_BY_IS_CONSUMED_CODE.md)).

Status (2026-11-08): step 0's static half of the number owner's build order
([the number-graph record](2026-11-08_A_NUMBER_IS_A_CLASS_ON_A_GRAPH_OF_PLACES_AND_EVERY_METHOD_IS_A_BRACKETING_A_CHART_OR_AN_END.md),
§10): every declared width at the design branch's tip `bbe6d6a0` (`claude/project-thread-nclk1x`), with its
consumer and whether it is derived or picked. Read only: no code changed, no machine run. The card read that gives
each width's measured need is §5, owed by the design thread. Refs #76, #73, #410.

Receipts: [`census.py`](2026-11-08_THE_WIDTH_CENSUS_receipts/census.py) reads the tree at a git ref and lists
every integer constant of the Rust crates and every `#define` of the CUDA kernels, with its value (simple
expressions evaluated, Rust's `use super::*` resolved to the parent module), its doc tag and its uses by word match
outside comments; it joins the hand classification in
[`classes.tsv`](2026-11-08_THE_WIDTH_CENSUS_receipts/classes.tsv). Outputs:
[`census.tsv`](2026-11-08_THE_WIDTH_CENSUS_receipts/census.tsv) (721 rows),
[`summary.txt`](2026-11-08_THE_WIDTH_CENSUS_receipts/summary.txt) (unused declarations, one name with several
values, one value declared more than once, tags) and [`twins.txt`](2026-11-08_THE_WIDTH_CENSUS_receipts/twins.txt)
(each card define beside its host twin, from [`twins.py`](2026-11-08_THE_WIDTH_CENSUS_receipts/twins.py)). The
table of §3 is [`table.py`](2026-11-08_THE_WIDTH_CENSUS_receipts/table.py)'s output.
[`literals.py`](2026-11-08_THE_WIDTH_CENSUS_receipts/literals.py) lists the literal widths of finding 3
([`literals.tsv`](2026-11-08_THE_WIDTH_CENSUS_receipts/literals.tsv)) and
[`counts.py`](2026-11-08_THE_WIDTH_CENSUS_receipts/counts.py) counts the refusal and release sites of findings 9 and 10
([`counts.tsv`](2026-11-08_THE_WIDTH_CENSUS_receipts/counts.tsv)), both on code lines with test-only items set apart. Grades: [census] read from
source at `bbe6d6a0`, [derived] derived here, [design] a choice for the code.

**Lessons this census could repeat** ([the lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)):
- a declared constant standing in for a derivation, which the
  [October 2 census](2026-10-02_THE_CONSTANTS_NOTHING_DERIVES_THE_GRAIN_IS_THE_ROOT_AND_ITS_READING_COUNT_IS_THE_ADMITTED_FUTURE.md)
  found on the previous machine: this census names each one and derives none by fiat;
- a refusal answered with a larger limit (lesson 9): no carrier is widened here, and a width step stays a law change
  judged by a paired read (N3, N5);
- bits read as progress: the census changes no reading; its use is the owner's steps 1, 2, 3, 5 and 7.

## 1. What a declared width is here

A value carries its places `[lo, lo + w)` (N1). A declaration sets one end:
- the **grain**, `lo`, where a release rounds;
- the **carrier**, `lo + w`, the preset register the value is realized in (`i32`, `i64`, `u64`, `i128`, the card's
  `__int128`).

Each declaration is one of these classes:
- **derived**: from the operands' widths by N3 (a sum one more place, `n` terms `⌈log₂ n⌉` more, a product
  `w_a + w_b`), or from the theory's structure;
- **grain, criterion stated**: a receiver's tolerance whose reason states the criterion it meets but not the number
  (the October 2 census derived one such grain from its two-part code, `2L² ≥ N ln 2`);
- **grain, picked**: chosen, with `agent-inferred` or no reason;
- **carrier, preset**: fitted to a native register;
- **identity**: set equal to another width with no derivation of the equality;
- **schedule**: a rate or halving count of a step;
- **realization**: launch geometry, a memory partition or a shared-memory bound, which never changes bits;
- **exterior**, **read** or **dead** (declared, unused).

## 2. The count

[census] Under `crates/` at `bbe6d6a0`:
- 474 source files hold 721 integer constants and card defines;
- 691 of them lie outside tests: 395 in Rust and 296 card defines;
- 146 of those are width-named (`*_BITS`, `*GRAIN*`, `*_SHIFT`, `*WIDTH`, `*CARRIER*`, `*DIGITS`, `*_EXP`, `*TOP`,
  `*MARGIN`, `*LIMBS`), 87 of them in Rust;
- 62 are limits (`CEILING`, `BUDGET`, `LIMIT`, `MAX_`);
- doc tags: 633 untagged, 40 `agent-inferred`, 17 `definition`, 1 `measurement`.

**The field path** [design; agent-inferred]: what lap 14 executes, plus the tower grains it imports, the keyed
modes' release and exponential it calls, and the card twins of each. Lap 14 runs law (D), the deposit against each
place's whole conditional, through `FieldLearner::section_conditional_weighed`
(`section_conditional`, `_coin`, `_beat`), the energy reads (`read_energies`, `read_energy_material`,
`read_energy_faces`) and the deposit's moments. It holds 57 declarations, classified in §3.

## 3. The field path's widths

[census] Rows from [`classes.tsv`](2026-11-08_THE_WIDTH_CENSUS_receipts/classes.tsv) joined with the values the
census read. "Need" names what the card read of §5 prints for the width, or the static derivation.

| Width | Value | Owner | Class | Quantity | Need |
|---|---|---|---|---|---|
| `LN2_BITS` | 30 | keyed_modes.rs:148 | grain, picked | ln 2's face 2^-30, the one ln2_face() releases to | twin of field's LN2_FACE_BITS |
| `FACE_BITS` | 16 | tower.rs:242 | grain, picked | a face: encodings E(a), letter faces z(a), class biases, ring faces | top place of \|E\|,\|z\| a section; bottom place moved of the face families |
| `MATERIAL_BITS` | 24 | tower.rs:244 | grain, picked (one grain, four quantities) | the material theta (i32), and by identification the clocks (PACE_BITS), law (D)'s conditional p(v) and its weights, the coin's tau | top place of \|theta\| by family (i32 leaves 7 whole bits); bottom place moved of each family's step; least nonzero p(v) and the weight released below 2^-23 |
| `MOVE_BITS` | 30 | tower.rs:246 | grain, picked | decays D, rates b, phasors zeta, exp_series faces | bottom place of the released products; \|zeta\| stays <= 1 |
| `STATE_BITS` | 24 | tower.rs:248 | grain, picked | the tower's mode state (2^-24); not the field's STATE_BITS (16) | tower only |
| `COVECTOR_BITS` | 24 | tower.rs:250 | grain, picked | the face families' covector | bottom place of the face families' covector |
| `STEP_BITS` | 32 | tower.rs:252 | grain, picked | the tower deposit's covector grain and its epsilon | tower only |
| `READ_BITS` | 20 | tower.rs:257 | grain, picked | a code reading in bits, 2^-20 | written as 20 at 10 lines of the field and the energy (literals.tsv) |
| `CONTACT_BITS` | 40 | field.rs:181 | grain, picked | the contact covector dz, ds on 2^-40 | card writes the derived 32 as the literal CONTACT_BACK |
| `LN2_FACE_BITS` | 30 | field.rs:642 | grain, picked, declared twice | ln 2's face 2^-30; keyed_modes holds the same as LN2_BITS, untied | one declaration owed |
| `LN2_FACE_BITS` | 30 | field.cu:68 | grain, picked | 30 | parity by hand |
| `ENERGY_BITS` | 32 | energy.rs:46 | grain, criterion stated | Phi, G, log2 p on 2^-32; a fall is certified past slack = logs + logs' + 2 units | smallest certified fall about 2R 2^-32 bits for R logarithms read: count of ticks resting with the fall inside the slack, beside R |
| `ENERGY_BITS` | 32 | field_energy.cuh:19 | grain, criterion stated | card twin | parity by hand |
| `LOCK_BACK_BITS` | 33 (`2 * FACE_BITS + 1`) | field.rs:692 | grain, derived | 2*16+1, the lock's covector read back | derived |
| `COEFFICIENT_BITS` | 90 (`3 * MOVE_BITS`) | moment.rs:131 | grain, derived | three faces on 2^-30: W on 2^-90 | derived |
| `RETURN_BITS` | 84 (`2 * MOVE_BITS + COVECTOR_BITS`) | moment.rs:136 | grain, derived | conj(zeta) D times a covector, 2^-84 | derived |
| `RETURN_RELEASE_BITS` | 60 (`RETURN_BITS - COVECTOR_BITS`) | moment.rs:138 | grain, derived | 84 - 24 = 60 released | derived |
| `MARGIN` | 12 | tower.rs:255 | derived from a horizon, reason stale | moves' margin \|lambda\| <= 1-2^-12 (memory about 4,096 classes) | reason cites GSM8K's 520-byte problems; ceil(log2 3,771) = 12 restates it from today's longest region |
| `CONTACT_BACK` | 32 | field.cu:43 | derived, written literal | 32 = CONTACT_BITS + FACE_BITS - COVECTOR_BITS (the host computes it) | parity by hand |
| `NEAR_SLOTS` | 10 (`(2 * (NEAR - 1))`) | field.cu:56 | derived | 2(NEAR-1) = 10 | derived |
| `TERM_EXPONENT` | 123 | field_energy.cuh:22 | derived, written literal | 123 = 2*62 - 1: face and multiplier on 2^-62, the face's fraction 2^(f-1); the host's log_row writes 123 too | parity by hand |
| `PUSH_BITS` | 2 | keyed_modes.rs:143 | carrier, derived bound | pushes \|beta\| <= 2^2, the carrier's headroom | keyed modes only |
| `SQUARE_BITS` | 8 | keyed_modes.rs:146 | carrier, derived bound | square law \|h\| <= 2^8, the carrier's headroom | keyed modes only |
| `TEMPER_TOP` | 7 | field.rs:650 | carrier, inherited, written literal | ceil(log2 T) <= 7 and T >= 2^-23: 31 - 24, the additive chart's 32-bit temperature its comment names; host and card now read T in 128 bits | the headroom it now stands for: top place of a covector times 1/T |
| `TEMPER_TOP` | 7 | field.cu:67 | carrier, inherited, written literal | 7 | parity by hand |
| `UNIT_BITS` | 62 | keyed_modes.rs:141 | carrier, preset | the exponential navigator's unit (second declaration) | declared five times |
| `UNIT_BITS` | 62 | tower.rs:263 | carrier, preset | the exponential navigator's unit 1 on 2^-62 (i64 less sign and one doubling) | declared five times |
| `SHARE_BITS` | 63 | field.rs:177 | carrier, preset | a term's share of its row's mass, 1 on 2^-63 (u64 holding [0,1]) | none: the share is <= 1 by construction |
| `WEIGHT_BITS` | 62 | field.rs:1473 | carrier, preset | a source's and crowd's value multiplier 1 on 2^-62 | none |
| `STATE_BITS` | 16 | field.rs:184 | identity (= FACE_BITS by value, declared apart) | a site's carried face shares on 2^-16 | name collides with the tower's STATE_BITS 24 |
| `BLANK_HELD` | 16 (`STATE_BITS`) | field.rs:646 | identity | = STATE_BITS | derived by name |
| `PACE_BITS` | 24 (`MATERIAL_BITS`) | field.rs:711 | identity | = MATERIAL_BITS: rate, clock and variation on 2^-24 | card twin is a literal |
| `PACE_BITS` | 24 | field.cu:532 | identity, written literal | 24 (host = MATERIAL_BITS) | parity by hand |
| `NEAR` | 6 | field.rs:190 | structural | the near field, lcm(2,3) = 6, the solenoid's two finest rings | derived |
| `FIRST_RATE` | 3 | tower.rs:261 | schedule, imported | first moment rate 2^-3 | the classical 0.9 read dyadic |
| `SECOND_RATE` | 8 | tower.rs:262 | schedule, imported | second moment rate 2^-8 | the classical 0.999 read dyadic |
| `AVERAGE_RATE` | 8 | field.rs:6152 | schedule | averaged constitution's rate 2^-8 a section (= SECOND_RATE by value) | picked equal |
| `FIRST_HALVINGS` | 2 | energy.rs:49 | schedule, picked | eta = 2^-2 at the first tick | picked |
| `MOST_HALVINGS` | 24 (`STATE_BITS + 8`) | energy.rs:51 | schedule, derived with a picked 8 | STATE_BITS + 8 = 24 halvings (the field's STATE_BITS, 16) | the 8 assumes \|force\| times scale below 2^8: print the top place of that product |
| `ENERGY_EPS_SHIFT` | 4 | field_train.rs:4129 | read | the attribution read's step 2^-4 of a letter's uniform weight | a read's probe step |
| `MAX_CLASS_TRITS` | 7 | field.rs:193 | realization | 3^7 = 2,187 classes within the card's 2^12 buckets a head and region | the bucket count is the card's |
| `CHUNK` | 16 | field.rs:6360 | realization | 16 places a read (16*alphabet configurations, about 0.8 GB) | memory partition |
| `MAX_CROWD_SLOTS` | 32 | field.cu:51 | realization, derived bound | one warp; 2(ceil(log2 reach)-1) <= 32 iff reach <= 2^17 | 22 slots at reach 3,771 |
| `WINDOW_LIMBS` | 8 | field.cu:1310 | realization | contact carriers to 8 limbs (512 bits) add in place | realization |
| `CONTACT_MIN_BLOCKS` | 8 | field.cu:1312 | realization | 8 resident blocks a multiprocessor | launch geometry |
| `SPREAD_THREADS` | 256 | field.cu:1314 | realization | 256 a block of field_spread | launch geometry |
| `MAX_PROBES` | 127 | field.cu:1323 | realization, measured | 127 probes keep the contact and reverse kernels' blocks an SM (ptxas -v, theory 00:25) | measured |
| `CONTACT_ROWS` | 4 | field.cu:1331 | realization | 4 warps a contact block | launch geometry |
| `REV_ROWS` | 4 | field.cu:2913 | realization | 4 warps a reverse block | launch geometry |
| `ROW_CURRENT_SPAN` | 32 | field.cu:3357 | realization | 32 | launch geometry |
| `OUTER_TILE` | 64 | field.cu:3439 | realization | 64 | launch geometry |
| `ENERGY_SUMS` | 8 | field_energy.cuh:26 | realization | 8 sums of 128 bits a region (pair on 2^-40, the rest on 2^-32) | realization |
| `RECORD` | 30 (`0x1E`) | field_train.rs:121 | exterior | ASCII RS, the record separator | exterior |
| `UNIT` | 31 (`0x1F`) | field_train.rs:122 | exterior | ASCII US, the codec's unit separator | exterior |
| `MOMENT_BITS` | 106 (`COEFFICIENT_BITS + FACE_BITS`) | moment.rs:133 | dead | W times an encoding, 2^-106 | declared, unused |
| `CARRIED_BITS` | 70 | field.cu:42 | dead | 70, no use | declared, unused |
| `HOLD_BITS` | 40 | field.cu:48 | dead | a hold's face on 2^-40; its named host twin is gone | declared, unused |

## 4. Findings

[census unless marked]

1. **Every grain the field reads is picked.** `FACE_BITS` 16, `MATERIAL_BITS` 24, `MOVE_BITS` 30,
   `COVECTOR_BITS` 24, `CONTACT_BITS` 40, `READ_BITS` 20 and ln 2's 30 carry no derivation. `ENERGY_BITS` 32 states
   its criterion, a certified fall read past the two reads' summed slack, `logs + logs′ + 2` units of `2^(−32)`, but
   not its number.
   - [derived] The criterion gives the number. A fall `δΦ` bits is certified only when `δΦ · 2^32 > 2R + 2` for `R`
     logarithms a read, so the grain binds where the relaxation rests with its fall inside the slack. For `H`
     heads over a region of 3,771 receivers, `R ≤ 3,771·H`, and falls below about `H · 2^(−19)` bits rest uncertified.
     Whether that binds is §5's read (c).
   - The derived widths are the products of these grains (`LOCK_BACK_BITS` 33, `COEFFICIENT_BITS` 90, `RETURN_BITS`
     84, `RETURN_RELEASE_BITS` 60) and the near field `NEAR = lcm(2, 3)`.
   - Two carriers are already derived by N3 in the code: `Field::contact_return_bits`,
     `126 − 2·MOVE_BITS − 2 − ⌈log₂ reach⌉`, and `Field::row_bits`, "read from the declaration's own bounds, never
     chosen". The owner generalizes them.
2. **One grain carries four quantities.** `MATERIAL_BITS` (24) is the material θ's grain and, by identification:
   - the clocks' (`PACE_BITS = MATERIAL_BITS`);
   - law (D)'s conditional `p(v)` and its weights, released to zero below `2^(−23)`;
   - the coin's `τ = 2^(24 − tau_bits)` on `2^(−24)`.

   `TEMPER_TOP = 7` is `31 − 24` written as a literal: the range of the additive chart's 32-bit temperature, which
   its comment names. Host and card now read `T` in 128 bits, so the bound stands for the products' headroom with no
   derivation of it. Its floor `1 − MATERIAL_BITS` is tied to the grain by name; its top is not. A width step on 24
   would move four quantities at once and leave the top at 7. Under N1 each quantity owns its places; splitting them
   at today's value is a realization step that keeps bits.
3. **Literals stand for widths in the live law.** [`literals.tsv`](2026-11-08_THE_WIDTH_CENSUS_receipts/literals.tsv)
   lists each code line of the field path, host and card, where 40, 20, 62, 16 or 8 stands as a shift, a release's
   grain or an offset of a named width.
   - `40`, 9 host lines: the material families' covector grain `2^(−40)`, released to `40 − COVECTOR_BITS` in four
     section laws (`section_contrast`, `section_contrast_scaled`, `section_kernel_grouped`,
     `section_conditional_weighed`), the temperature's covector `nats << (40 − ENERGY_BITS)` in three, and
     `predicted_change` in two. It equals `CONTACT_BITS` by value but is another quantity.
   - `20`, 12 host lines: `READ_BITS`, a code reading on `2^(−20)`, at 10 (`pull_reading`, `predicted_change`,
     `newton_terms`' α, the scaled contrast's η, the grouped kernel's log ratio, the conditional's KL, the energy's
     floor code and its `λ`); and a redrawn face's squared shares on `2^(−20)` at 2, another quantity at the same
     number.
   - `62`, `UNIT_BITS`, 5 host lines (`skin_of`, `temperature_of`, the two row-width bounds `62 + WEIGHT_BITS + …`,
     the energy's floor code `62 << 20`) and 3 on the card.
   - `16`, 11 host lines and 5 on the card: a release by 16 places in `skin_back` and `turn_phasor` (host and card),
     two of the energy's reads and the card's letter faces, and `with_theta`'s half turn on
     `2^(−(MOVE_BITS + 16))`; the lanes' host share on `2^(−16)` at 4 (a realization); and the coin measure's squares
     at 2. Which width each release by 16
     stands for (`FACE_BITS`, the field's `STATE_BITS`, or `40 − MATERIAL_BITS`) is not written.
   - `8`, 15 host lines and 9 on the card: the extra places a tangent is held at (7 host, 6 card, the card's as
     `CONTACT_BACK + 8 + g0`), the encodings' covector (3 host), the radial correction's `2·FACE_BITS + 8` (3 host,
     2 card), the far collision's `SHARE_BITS − 8` (1 each) and `MOST_HALVINGS = STATE_BITS + 8`. No reason is stated
     for it.
4. **One name, several values.**
   - `STATE_BITS`: 24 in the tower and its card, 16 in the field. `MOST_HALVINGS = STATE_BITS + 8` reads the field's,
     so it is 24.
   - `TURN_BITS`: 16 in the tower, 40 in the split.
   - `COVECTOR_BITS`: 24 in the tower and both kernels, 192 in `ring.rs`.
   - `MARGIN`: 12 in the tower and its card, `2^30` bytes in the CUDA host's memory budget.
   - `CODE_BITS`: 32 in `units.rs`, 20 in `receiver/coupling.rs`.
   - `CHUNK`: 16, 4,096 and 8,000 in three owners.
5. **One value, many declarations, and the card's twins by hand.**
   - `UNIT_BITS` is declared five times: tower, keyed modes, units and both kernels.
   - ln 2's grain is declared twice and the two are not tied: `LN2_BITS` in the keyed modes is the one `ln2_face()`
     releases to; `LN2_FACE_BITS` in the field is a separate 30.
   - `receiver/coupling.rs` copies `COVECTOR_BITS` and `READ_BITS` as the literals 24 and 20, naming their source in
     a comment.
   - 33 card defines repeat a host constant by name, 23 of them widths. Each equals its host value at this tip
     ([`twins.txt`](2026-11-08_THE_WIDTH_CENSUS_receipts/twins.txt)).
   - Derived widths are written as literals: `CONTACT_BACK` 32 on the card (the host computes `CONTACT_BITS +
     FACE_BITS + g − COVECTOR_BITS`, which is `32 + g`), `PACE_BITS` 24 on the card (the host's `= MATERIAL_BITS`), and
     `TERM_EXPONENT` 123 on both sides (`2·62 − 1`: face and multiplier on `2^(−62)`, the face's fraction `2^(f−1)`;
     the host's `log_row` writes 123). Parity holds by hand.
6. **Dead.** `CARRIED_BITS` 70 and `HOLD_BITS` 40 on the card (`HOLD_BITS`'s comment names a host twin that no longer
   exists), and `MOMENT_BITS` 106 on the host. `summary.txt` also lists `REFUSED_SHIFT`, six unused layout
   defines and the tower classes example's `MOVE_OCTAVE`.
7. **Imported rates.** `FIRST_RATE` 3 and `SECOND_RATE` 8 are "the classical 0.9 and 0.999 read as dyadic rates",
   the moments' rates, and `AVERAGE_RATE` equals `SECOND_RATE` by value. They are a convention brought in, not read
   from the field's own clocks.
8. **A stale reason.** `MARGIN` 12 says a mode's memory reaches "past a GSM8K problem of some 520 bytes". The corpus
   has been python-codes-25k since November 5.
   - [derived] `⌈log₂ 3,771⌉ = 12` at today's longest region, so the value stands with its reason restated.
   - The field does not read `MARGIN`; the tower does.
9. **Every carrier refuses, and the read side clips.** No field value widens (N2's ray); past its preset a value is
   refused.
   - θ is `i32` on `2^(−24)`, seven whole bits.
   - Faces, states and covectors are `i64` through `fit64`, which refuses past it: 93 calls in the host's field,
     energy and moment laws (50, 41 and 2) and 90 in their card kernels (55, 33 and 2), the card's with status bits.
   - Products are `i128` with checked operations; 25 code lines name a refusal past the 128-bit carrier (14 in the
     field, 8 in the energy, 3 in the moments), several of them a message reused at many sites.
   - The averaged field narrows with an unchecked `as i32`, safe because an average of `i32` entries stays in
     range.
   - The coin measure's `metric` saturates (`unwrap_or(u128::MAX)`, `saturating_add`), as do `v_coin` and
     `v_deposit`, and its mean truncates (`sum / n`); `energy_sweep_at`'s reading per answer saturates at
     `i128::MAX` before its release. These are reads, not the law, but a clipped read reports silently. (Two
     share conversions also carry `unwrap_or(u64::MAX)`, unreachable since a share is at most 1 on `2^(−63)`.)
10. **Releases drop their remainders.** `keyed_modes::release` (to the nearest, half away from zero) and
    `div_nearest` return no remainder. The field path's code holds 194 host release calls and 42 `div_nearest`
    (the field 108 and 23, the energy 74 and 19, the moments 12), and on the card 169 `rel` and 28 `div_nearest`
    (`field.cu` 103 and 17, `field_energy.cuh` 58 and 11, `field_moment.cuh` 8). That is step 3's subject, N5.

**Outside the field path** (step 6 reaches these; `census.tsv` lists every one):
- `ring.rs`: `COVECTOR_BITS` 192, `ATTAINMENT_BITS` 128, `ROOT_ATTAINMENT_BITS` 96, `SEPARATION_BITS` 48.
- `prediction.rs` `DERIVATIVE_BITS` 192, `overture.rs` `REMAINDER_BITS` 128 and `REFERENCE_BITS` 40, `surprisal.rs`
  `LOG_SERIES_BITS` 192, `ratio/exponentiated/carried.rs` `READING_BITS` 64, `chart.rs` `CARRIER` `2^127`.
- `units.rs` `CODE_BITS` 32 and `UNIT_BITS` 62, `section_lock.rs` `ADVANCE_BITS` 3.
- The tower's `participation.rs` `ENTROPY_BITS` 20 and `split.rs` `TURN_BITS` 40, `PRICE_BITS = READ_BITS`,
  `SCORE_BITS` 48.
- `holarchy/terrain/pursuit.rs` `GRAIN_LIMIT` 16; the CUDA host's `tree.rs` `MAX_DIGITS` 32 and `SPLIT_BITS` 512;
  the tower training example's `SEARCH_DIAGONAL_BITS` 50, `SEARCH_KEPT_BITS` 30, `BLOCK_GRAIN` 5, `MUTUAL_SHIFT` 2.
- The keyed modes' `Grains::DECLARED` (`moves` 30, `face` 32, `covector` 30, `exponent` 24, `margin` 8, `square`
  16), agent-inferred; the field calls only the keyed modes' release, `ln2_face` and `Exponential`.
- `receiver/coupling.rs` carries a mass as `m · 2^e` with `m` in `[2^62, 2^63)`. That is the float chart of the
  number-graph record's §2.4 built from integers, with a picked mantissa width, inside a law.

## 5. The measured need: what the card read prints

[design] Reads only, on a saved state at a boundary, so lap 14 is untouched (steps 0 and 1 touch nothing in lap
14). Each prints the width it measures beside the declared one.

- (a) **The material**, for each family: the top place of `|θ|` (the largest bit length, against `i32`'s 31); the
  bottom place moved (a histogram of the lowest set bit of each nonzero step); and the count of steps released to
  zero.
- (b) **Law (D)'s conditional**, at each place: the least nonzero `p(v)`; the count of letters whose weight released
  to zero below `2^(−23)`; and their summed weight before release on `2^(−32)`, the mass the grain drops.
- (c) **The energy's grain**, per region: the logarithms read `R` beside the reason the relaxation rested, either a
  fall inside the slack `2R + 2` or `MOST_HALVINGS` reached.
- (d) **Each `i128` refusal site**: the largest bit length reached, so its headroom is `127` less it.
- (e) **Faces, states and covectors** through `fit64`: the largest bit length reached, against 63.
- (f) **The coin measure**: a count of saturations.
- (g) **`MOST_HALVINGS`' 8**: the top place of `|force| × scale`, which the 8 assumes below `2^8`.

A width whose top place reached stays far below its carrier, or whose bottom places never move, is over-declared. A
width whose steps release to zero, whose conditional drops mass, or whose falls rest inside the slack, binds. The
first width step of step 5 is the one whose measured need stands farthest from its declaration.

## 6. What it sets in the build order

[design]
- **Step 1, the host owner `holonics::number`.**
  - Its presets are the census's carriers: `i32` at `2^(−24)`, `i64` at `2^(−16)`, `2^(−24)`, `2^(−30)`, `2^(−40)`
    and `2^(−62)`, `u64` at `2^(−63)`, checked `i128` products, and the card's `__int128`.
  - Each width is declared once. The derived ones are expressions: `TEMPER_TOP`, `CONTACT_BACK`, `TERM_EXPONENT`,
    `LOCK_BACK_BITS`, `NEAR_SLOTS` and the moment widths; the live law's literal 40 and 20 get names.
  - The four quantities on `2^(−24)` get their own declarations at today's value, bits unchanged.
- **Step 2, `number.cuh`**, generates the card's 33 repeated defines from the one declaration.
- **Step 3** returns the remainders at the field path's release sites, 194 on the host and 169 on the card, and at
  their 42 and 28 `div_nearest`.
- **Step 5** takes the picked grains one at a time, each judged by a paired read, starting where §5 shows the
  largest gap.
- **Step 7, the lint**, refuses:
  - a width declared twice;
  - a literal grain inside a law;
  - a card twin written by hand;
  - a dead width;
  - a name carrying two values.
