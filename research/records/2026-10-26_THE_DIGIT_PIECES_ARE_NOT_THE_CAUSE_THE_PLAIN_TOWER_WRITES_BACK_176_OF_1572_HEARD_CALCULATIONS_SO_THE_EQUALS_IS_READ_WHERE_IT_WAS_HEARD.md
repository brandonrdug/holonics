# The digit pieces are not the cause: the plain tower writes back 176 of 1,572 heard calculations, so the equals is read where it was heard

October 26. Refs #404, #406, #405. The cause test fixed in
[the second lap's record](2026-10-26_THE_SECOND_LAP_WRITES_BACK_225_OF_1572_HEARD_CALCULATIONS_SO_THE_DIGIT_UNITS_ARE_TESTED_AS_THE_CAUSE.md)
§5 and §6 ran on Brandon's PC as fixed. This record gives the read, the decision it fixed, and the
next loop's read with its decision and run, fixed before that read. Grades: [measured] for the
reads, [definition] for the slice and the rules, [agent-inferred] for each choice and reading.
Receipts:
[`…_receipts/`](2026-10-26_THE_DIGIT_PIECES_ARE_NOT_THE_CAUSE_THE_PLAIN_TOWER_WRITES_BACK_176_OF_1572_HEARD_CALCULATIONS_SO_THE_EQUALS_IS_READ_WHERE_IT_WAS_HEARD_receipts/RUN.md).

Computational object: the helical pair interaction, here the tower's pair contact between its
carried face and the unit it writes after a calculation's `=`. The read touches faces and
placement; the helix, the level's pair contacts, cell holonomy, tube and tower thread stay as the
plain tower has them. Nothing is founded or deposited by a read.

## 1. The read

[measured] Both plain towers trained their three passes inside their deadlines (285.5 s of 360 s
and 307.7 s of 350 s, no 32-section window over its bound), and both reads ran to their end
(12.9 s and 13.6 s of 30 s). `C` is the tower on the committed units, `F` the tower on the foil's.
Beside the earlier rows:

| | (a) | (b) free | (c) | (b) at the equals | met | never met |
|---|---|---|---|---|---|---|
| references | 743 | 2,448 / 2,448 | 566 / 740 | — | — | — |
| 6-gram | 64 | 570 / 986 | 20 / 533 | 1,348 / 2,448 | 1,318 / 1,572 | 30 / 876 |
| 8-gram | 77 | 981 / 1,155 | 20 / 585 | 1,559 / 2,448 | 1,525 / 1,572 | 34 / 876 |
| `lapD8`, one draw (clock copy) | 167 | 108 / 2,475 | 31 / 725 | 242 / 2,448 | 225 / 1,572 | 17 / 876 |
| `C`, committed units | 47 | 53 / 1,219 | 25 / 637 | 190 / 2,448 | 176 / 1,572 | 14 / 876 |
| `F`, digit foil | 38 | 61 / 1,227 | 49 / 618 | 156 / 2,448 | 131 / 1,572 | 25 / 876 |

By operation at the equals, `C` writes 14 of 470 sums, 21 of 388 differences, 114 of 897 products
and 29 of 343 quotients right; `F` writes 14, 14, 91 and 20. Paired, calculation by calculation:
on met calculations only `C` is right at 158, only `F` at 113 and both at 18; on never-met ones
only `C` at 14, only `F` at 25 and both at none. At John's two calculations `C` writes `24>>`,
right, and `23>>`, wrong; `F` writes `24>>` and `24>>`, right and wrong.

The towers' held-out codes after three passes were 1.869 (`C`) and 1.837 (`F`) bits a byte, a
reading beside the rules and never a measure of progress.

[measured] The rules stopped once on `F`'s read: a free release wrote `<<8(2/3)=15>>`, whose
juxtaposed numeral and parenthesis passes the rules' character filter and reads as a call. The
rules' docstring reads any expression outside numerals, `.`, the four operations and parentheses
as no value, so `value` now returns none for it as well (`TypeError`, one line, with a test). It
was the only such calculation in either read, and the copy with that line read `C` byte-identically.

## 2. The decision applied

`F_met` = 131 is below `G` = 1,318, so decision 1 does not hold. With `b` = 113 and `c` = 158,
`b − c` = −45 is not above `1.96·√271` = 32.3, so decision 2 does not hold either. Decision 3
holds: the digit pieces are not the cause, and the next loop reads the plain tower's equals on the
training problems.

[agent-inferred] Three further readings, none of which changes the decision:
- The foil writes back fewer heard calculations than the committed units (`c − b` = 45 is past
  the same line). It does take more operands from the question at (c) (49 against 25), and its 25
  never-met calculations against 14 are within the line (`11 < 1.96·√39` = 12.2).
- The clean plain tower stays on the problem far less than `lapD8` did: 47 against 167 at (a),
  under both n-grams. `lapD8` was trained longer and carried the clock's copy of the question's
  first unit; the clean reading is `C`'s.
- Both towers write few calculations of any kind right, heard or not. That is the reading the
  next loop separates.

## 3. The next read, fixed before it runs

[definition] **The slice.** Training problems 0, 9, 18, … of the training text (`050b94f3…3b95`),
split as the reader and the rules split it (6,730 problems at a blank line), joined by blank lines
and ended by one, as the held-out text is. That gives 748 problems, 392,606 bytes and 2,344
calculations, SHA-256 `b9a22366…04b2`. Every ninth problem spreads the slice over the whole
passage the streams read, so it is neither the first part every pass opened on nor the last part
every pass closed on.

[definition] **The read.** `read-unit-tower-written` from `C`'s `STATE` (`84e2bacf…78b4`) with
the committed units, the key file of the `lapD8` read, one draw, 400 free bytes, the equals at 64
and a cap of 8 units, over the slice. The rules then read it as `written_rules.py train9.txt
train_all.txt C_train`. Every calculation of the slice is met by construction, so the reading is
`R_train`, right of 2,344.

**The decision**, with `R_held` = 176 / 1,572, `C`'s held-out met reading, and `z` the pooled
two-proportion statistic of `R_train` against `R_held` (an exterior reading):
1. **`z ≤ 1.96`.** The tower does not write back a calculation even in the problem it heard it in.
   The failure is holding: what three passes keep of a heard result. The next loop's subject is
   what a pass deposits where a result arrives, read on the tower's own modes.
2. **`z > 1.96`.** The tower holds a calculation where it heard it and does not reach it from a new
   question. The failure is addressing. The next loop derives the address from the tower's own
   geometry, the phase and winding a question leaves on its rings, and never from a store
   ([the audit's direction](2026-10-26_THE_SECOND_LAP_WRITES_BACK_225_OF_1572_HEARD_CALCULATIONS_SO_THE_DIGIT_UNITS_ARE_TESTED_AS_THE_CAUSE.md#3-what-the-audit-changes)).

Beside the decision, read and reported: by operation, and (a), (b) free and (c) on the slice.

[definition] **The run.** On the PC with the binary of the cause test (`04232e3d…70b5`), under the
`wait4` wrapper, `RAYON_NUM_THREADS=8`, an 8 GiB memory scope, alone on the host.
- The units the read can move are at most its prompt bytes (1,190,596: each problem's framed
  question and each calculation's question and answer through its `=`), plus 400 a problem and 8 a
  calculation: 1,508,548. A unit is at least a byte.
- The largest measured rate on these states is `read_C`'s, 12.9 s × 8 / (468,588 + 116,253) =
  0.1765 ms a unit a thread.
- The projection is 1,508,548 × 0.1765 / 8 = 33.3 s. The deadline is 40 s, held by `timeout`, and
  a read whose first 64 problems pass 4.4 s (11%) is stopped and reported incomplete.

## 4. The recorded failures this loop could repeat

- **Seen material graded as unseen.** The slice is training material and is read as such: it
  separates holding from reaching and is never set beside held-out readings as a generalization.
- **An authored routine standing in for learning.** The slice and the rules are exterior; nothing
  enters the machine.
- **Store or copy machinery standing in for learning.** Whichever decision holds, the next mechanism
  takes nothing from a store, a slot table or an index of contexts; the retirement of the bank, the
  reset clock, the passage tree and the letters copy is in progress in the same lane.
- **A refusal answered with a larger limit.** The deadline is fixed above.
