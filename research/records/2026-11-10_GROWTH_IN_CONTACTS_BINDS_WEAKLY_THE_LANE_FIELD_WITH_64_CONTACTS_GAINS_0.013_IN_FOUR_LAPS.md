# Growth in contacts binds weakly: the lane field with 64 contacts gains 0.013 in four laps

Status (2026-11-10): measurement. This record covers theory's order of November 10 09:55: grow the merge's pair contacts on the
latest lane state, and run four laps against the lane-only chain from the same state. It also records the order's second item,
the locked-visit instrument, which is now built and run. The code is on the line: 24b686bd9, 8a0d34672, 9d097c134 and ab82a0cb0.
Refs #73, #406.

## 1. The lever and its test

[definition; theory, November 10 09:55] Count tables read on TRAIN put the locked field's code beside a joint table of the
letters around each place:

| Reader | Code, held 0–31 locked (nats a place) |
| --- | --- |
| the field at lap 26 | 0.565 |
| a joint table of one letter each side | 1.564 |
| a joint table of two letters each side | 0.569 |
| a joint table of three letters each side | 0.419 |

So the field holds the joint law of two letters each side and nothing joint beyond it. Two facts about the merge go with this:
- The strand contact joins sites two apart in the first tick.
- Later hops reuse the same 8 complex contacts a side and add none.

The lever named is the contact count.

[definition; 24b686bd9, `Field::contacted`] Growth in contacts adds a fresh set the size of the founding set: `f` goes from 32 to
64, and the width, heads, modes, lanes and reach are kept.
- **The new pair drives.** The new `a` and `b` rows are drawn as a founding draws them, at `√(3/D)` of the current width, from
  the key stream past every draw already read (`contact_draws` = 2 · added · width).
- **The new zeros.** `W`'s new columns, the pair drives' biases and, in an energy field, `pair_c` start at zero, so every sum
  the forward forms is the old sum.
- **What is kept.** The field keeps its declared clocks (`Field::clocked_as`). Old contacts keep their complex pair and strand
  side, and the new ones follow them in each half.
- **The learner.** It opens the new entries' moments on their family's mean second moment, as the lane growth does.
- **The refusal.** `grow-contacts-field` reads the held joint before and after on the card, compares every face of the held
  joint states, and refuses to write the state if one moved.

[measurement] Verification:
- Host tests: `a_growth_in_contacts_keeps_every_face` (still 0 to 2, two lanes, an energy field, two successive growths) and
  `a_deposit_after_a_growth_in_contacts_reaches_the_new_contacts`. All 132 field tests pass.
- Card parity on a grown field (D 64 in two lanes, f 64, three sections and a withheld read): faces, covectors, the learner's
  text, rows, shares and currents equal.
- No kernel changed: `field_pair`, `field_pair_back` and the affines take `f` at run time.
- On lane lap 37's state, all 174,266 faces of the 1,020 held joint states are identical after the growth. The held joint
  reads 1.828577 before and after.

[decision; agent-inferred] The lane chain trains with binaries built from the 01bd3b362 tree (the v14 line, `FIELD_CLOCK_BARE`,
no carried remainders), not the line's current law. Today's binary differs from lap 34's log from section 0, so training the grown
arm with it would add a second difference.
- The growth was therefore ported onto 01bd3b362 (`contacts-on-01bd3b362.patch` in the receipts) and built as `field_pass.v14`.
  On lap 33's state that build reproduces lap 34's first 227 section lines bit for bit.
- Both arms train with the control's own `field_pass` and read with its `field_pass.reads`. Both arms are read on the
  references with the line's `charge-field` (references alone, 790bad001).

## 2. Four laps against the lane-only control

[measurement; RTX 4080 SUPER, the two arms' stages interleaved under `.local/gpu.lock`] Both arms start from lane lap 37's state
and train under `lane2.sh`'s law (no bare clock), with reads on the bare clock.
- The plain held joint (`FIELD_JOINT_NATS` own, 43,470 places) is read after each lap.
- The references' locked code and summed entropy are read on all of HELD128 (43,342 places).

| Lap | Held joint, 64 contacts | Held joint, 32 contacts (lane laps 38–41) | References' code, 64 | References' code, 32 |
| --- | --- | --- | --- | --- |
| start | 1.828577 | 1.828577 | 0.590100 | 0.590100 |
| 1 | 1.823373 | 1.826142 | 0.585064 | 0.587544 |
| 2 | 1.816549 | 1.822659 | 0.582074 | 0.586968 |
| 3 | 1.811575 | 1.822278 | 0.574039 | 0.583070 |
| 4 | 1.804295 | 1.817565 | 0.569367 | 0.581301 |

- After four laps, the grown arm's held joint is 0.0133 under the control's, and its references' locked code is 0.0119 under
  the control's (0.0207 under its start).
- Theory's guesses were at least 0.03 on each. Its rule was to withdraw contact count as a lever below 0.01 and turn next to the
  ticks' return. **The gain lies between the two: contact count binds, weakly.**
- The references' summed entropy alternates from lap to lap in both arms (control 0.571, 0.552, 0.567, 0.548; grown 0.569,
  0.546, 0.559, 0.536). So does the point re-draws' rest on held 0–31 (grown 0.847, 0.714, 0.811, 0.767; control 0.813, 0.734,
  0.828, 0.744). The re-draws therefore do not separate the arms at four laps.

## 3. The locked-visit instrument

[definition; 9d097c134, ab82a0cb0, `locked-visit-field`] The command takes the reach census's locked visit: each reference cut
to its room, every answer place read once with the rest locked, and the stop place where the room holds it. For every place it
writes one packed little-endian record:
- the problem (u32) and the place (u32);
- a stop flag (u8) and the letter (u16, the codec's class, the void at a stop);
- the face's shares (alphabet × u16 at 2^-16, released by partition with the remainder dropped; a face with all its mass on one
  class holds 65535);
- the readout chart (width × i32 on 2^-16).

Each set has a header with the layout, the counts, the state's sha and the grains. The files hold numbers only and stay under
`.local/`. Its host test checks each file against `locked_faces` and the host chart read.

[measurement] Lap 26's state was visited on held and on TRAIN's every-6 samples. That is 1,391,521 records of 339 bytes, 472 MB
in all. Read back on the host, the held file's faces code held 0–31 at 0.5643 nats a place, against the field's 0.565, and all
of held at 0.647.

## Receipts

Device: RTX 4080 SUPER under `.local/gpu.lock`, the stages of the two arms and the visit interleaved. Host threads: as the scripts
declare (8 for the card reads).

| Run | Projection | Deadline | Wall | Measured / projected | Peak RSS |
| --- | --- | --- | --- | --- | --- |
| growth (`grow.sh`) | 20 s | 25 s | 9.3 s | 0.47 | 0.33 GB |
| grown laps ct1–ct4 | 1,155 s | 1,520 s (outer) | 1,120, 1,121, 1,131 and 1,120 s | 0.97–0.98 | 0.79–0.88 GB |
| control laps 38–41 | 1,700 s (bound) | 2,060 s | 1,103, 1,100, 1,078 and 1,067 s | 0.63–0.65 | 0.82–0.87 GB |
| references' reads (10) | 120 s | 150 s | 111.8–119.4 s | 0.93–1.00 | 2.28–2.38 GB |
| visit, held | 140 s | 175 s | 119.5 s | 0.85 | 1.02 GB |
| visit, TRAIN even | 2,052 s | 2,565 s | 1,891 s | 0.92 | 1.16 GB |
| visit, TRAIN odd | 2,052 s | 2,565 s | 1,850 s | 0.90 | 1.11 GB |

Gate 3 on the line's code (crates as at ab82a0cb0): the card suite `cargo test -p holonics-cuda -- --include-ignored
--test-threads=1`, alone on the idle card under the lock, passes 149 of 149 in 781 s (its first read at this size; outer guard
3,600 s).

Scripts in `*_receipts/`, with the machine root replaced by `${HOLONICS_ROOT}`:
- the run scripts: `grow.sh`, `contacts_lap.sh`, `chain4.sh`, `refread.sh` and `visit.sh`;
- the projection's measured reads (`PROJECTION.txt`);
- the growth's port onto the v14 tree (`contacts-on-01bd3b362.patch`).
