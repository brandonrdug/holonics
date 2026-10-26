# The second lap writes back 225 of 1,572 heard calculations, so the digit units are tested as the cause

October 26. Refs #404, #406, #405. The written-rule read fixed in
[the rules record](2026-10-26_THE_HELD_OUT_PROBLEMS_ARE_READ_BY_WRITTEN_RULES_AND_THE_MARKUP_IS_WRITTEN_AT_ITS_EQUALS.md)
ran on Brandon's PC from `lapD8/STATE`, and its fixed decision chose the units cause test. This
record gives the read, the decision, what an outside audit changes in it, and the cause test with
its own decision and run, fixed before it runs. Grades: [measured] for the reads, [definition] for
the foil and the rules, [agent-inferred] for each choice and reading. Receipts:
[`…_receipts/`](2026-10-26_THE_SECOND_LAP_WRITES_BACK_225_OF_1572_HEARD_CALCULATIONS_SO_THE_DIGIT_UNITS_ARE_TESTED_AS_THE_CAUSE_receipts/RUN.md).

Computational object: the helical pair interaction, here the pair contacts between adjacent units
that the founding prices, and the tower's pair contact between its carried face and the next unit at
the equals. The test touches the **pair** (which adjacent pairs found a unit) and **faces and
placement** (where a digit sits in the units the tower reads); the helix, cell holonomy, tube and
tower thread stay as the plain tower has them.

## 1. The read

[measured] Both reads ran to their end inside their 30 s deadline (20.3 s and 20.9 s; peak 41 MiB),
and their `MARKS.tsv` are the same bytes, as the shared keys require. Beside the baselines of the rules
record:

| | (a) | (b) free | (c) | (b) at the equals | met | never met |
|---|---|---|---|---|---|---|
| references | 743 | 2,448 / 2,448 | 566 / 740 | — | — | — |
| 6-gram | 64 | 570 / 986 | 20 / 533 | 1,348 / 2,448 | 1,318 / 1,572 | 30 / 876 |
| 8-gram | 77 | 981 / 1,155 | 20 / 585 | 1,559 / 2,448 | 1,525 / 1,572 | 34 / 876 |
| `lapD8`, one draw | 167 | 108 / 2,475 | 31 / 725 | 242 / 2,448 | 225 / 1,572 | 17 / 876 |
| `lapD8`, two agreeing | 260 | 186 / 2,402 | 38 / 698 | (the same) | (the same) | (the same) |
| development state | 50 | 80 / 1,401 | 42 / 668 | 218 / 2,448 | 205 / 1,572 | 13 / 876 |

By operation at the equals, `lapD8` writes 13 of 470 sums, 19 of 388 differences, 151 of 897
products and 45 of 343 quotients right. At John's two calculations it writes `2*12=24>>`, right, and
`24*3=216>>2`, wrong.

[agent-inferred] Two readings follow.
- The tower writes back few of the calculations it heard. A two-clock smoke state trained on 4.6%
  of the training text already writes 205 of the 1,572; `lapD8`, trained on all of it over two
  laps, writes 225.
- Its free releases write many calculations, 2,475 at one draw against the 6-gram's 986, and get
  few of them right. They are mostly invented expressions with wrong values.

## 2. The decision applied

The rules record's §4 fixed it before the read: `T` met = 225 is below the 6-gram's 1,318, so
decision 1 holds. The tower does not write back what it heard, and the next loop tests the founded
units as the cause.

## 3. What the audit changes

An outside audit of the machinery for store and copy machinery (another thread, October 26, at
Brandon's request) found that the reset clock is a copy pointer. It holds a unit after its arrival
and raises that unit's mass at the output. The audit names three more owners as stores or copiers:
the binding bank, the passage tree's lock, and the unit copy. The design thread retires all four in
its next change.

[agent-inferred] Two consequences for this loop:
- `lapD8` carries the clock's copy of the question's first unit, which is why John's releases open
  with "John". Its (a) reading of 167 and 260 is not a clean reading of the tower. The plain towers
  below carry no clock, bank or lock, so their (a) reading is the clean one beside the n-grams.
- The audit lists the plain tower as clean and grades the founded units borderline (a pre-pass
  founding its units by code length). The cause test reads the units' effect on the plain tower and
  adds nothing to either.

## 4. The foil

[definition] `tools/gsm8k/digit_units.py` removes every founded unit whose bytes hold a decimal
digit from the committed units (`d0973c39…782a`), keeping the rest in founding order. It removes 113
of the 1,062 merges, leaving 1,205 units (`186b82ed…d0b4`), so each digit is read as its own byte unit.
John's answer line, read in the committed units and then in the foil's:

```text
'He ' | 'v' | 'ol' | 'un' | 't' | 'e' | 'ers ' | '2*' | '12' | '=' | '<<' | '2*' | '12' | '=' | '24>>' | '24' | ' times ' | 'a ' | 'year'
'He ' | 'v' | 'ol' | 'un' | 't' | 'e' | 'ers ' | '2' | '*' | '1' | '2' | '=' | '<<' | '2' | '*' | '1' | '2' | '=' | '2' | '4' | '>>' | '2' | '4' | ' times ' | 'a ' | 'year'
```

[measured] The training text reads as 1,535,797 units instead of 1,342,760, and the held-out text
as 173,650 instead of 151,684. A pass of the recipe below has 1,499 sections instead of 1,311.

[agent-inferred] The foil is a cause test and never the product. A founding rule that names digits
is text-specific, and the founding reads any passage of byte classes. If the cause holds, the next
loop derives where a digit sits from the machine's own geometry: the digits' ring of ten that the
tension locates
([record](2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md)),
on the base's tower of the digit-word law. Removing merges from the committed list, rather than
founding again with digit pairs refused, keeps every other unit the same, so the two towers differ
only where digits are.

## 5. The comparison and its decision, fixed before the run

Two plain towers are trained from scratch with the recipe of the bank record's `towerA` (width 64,
64 modes, 256 contacts, two levels, eight streams, sections of 128, three passes, rate `2^(−7)`),
with the same founding key stream: `C` on the committed units and `F` on the foil's. Each is read at
pass 3 by `read-unit-tower-written` with the key file of the `lapD8` read, at one draw, 400 free
bytes, the equals at 64 and a cap of 8 units. The rules read both, with `pair`.

With `G` the 6-gram's 1,318 met calculations, `F_met` and `C_met` the towers' met counts at the
equals, `b` the met calculations only `F` writes right and `c` those only `C` writes right:

1. **`F_met ≥ G`.** The digit welding is the cause. The next loop derives the founding from the
   machine's own located ring of ten, as above.
2. **Otherwise, `b − c > 1.96·√(b + c)`** (the paired count's two-sided 5% line, an exterior reading).
   The welding is a located cause but not the whole failure. The next loop is the same derivation,
   and the remaining gap to `G` is the loop after it.
3. **Otherwise** the units are not the cause. The next loop reads the plain tower's equals on the
   training problems themselves, where every calculation was heard in place. That separates a tower
   that never holds a heard calculation from one that holds it and does not reach it from a new
   question. Any mechanism that follows takes its addressing from the tower's own geometry, never
   from a store (§3).

Beside the decision, read and reported: (a), (b) free and (c) for both towers against the
n-grams; never-met and each operation at the equals; and John's two releases, whole, shown to
Brandon.

## 6. The run, fixed before it runs

On the PC, at the commit that adds this record, under the `wait4` receipt wrapper, each run with
`RAYON_NUM_THREADS=8` and an 8 GiB memory scope, the two trainings side by side on 16 of the 24
cores and nothing else on the host:

1. **Development read.** Both recipes for one pass over the first 800 training problems
   (`173c9ac3…f0d0`, 418,797 bytes; 155 and 178 sections), side by side. The rate at this commit is
   not yet measured, so the read is planned at three minutes and stopped at 180 s. From each:
   - `w`, its largest 32-section window over 32, in ms a section;
   - `h`, its `TOWER_PASS` elapsed less its last `TOWER_SECTION` elapsed: the held-out read and the
     pass's end.
2. **The two trainings**, side by side, from scratch over the training text (`050b94f3…3b95`).
   - Per-section bound `1.12·w`. The margin is the largest measured excursion of a window over its
     development read's rate (70.4 against 63.3 ms in the bank record's first launch).
   - Projection, upper end: `3·(S·1.12·w + h) + 1 s` for the start (the whole text reads into units
     in 0.6 s here), with `S` = 1,311 and 1,499. The deadline is that, rounded up to the next 10 s,
     held by an outer `timeout`.
   - A training any of whose 32-section windows passes `32·1.12·w` ms is stopped and reported
     incomplete with its rate.
   - Memory: the bank record's three bankless passes peaked at 216 MB. The ceiling is 8 GiB.
3. **The two reads**, one after the other, each held by `timeout 30`.
   - The units each can move: its prompts (468,588 committed; 518,610 for the foil, counted here
     from the same text) plus 400 a problem and 8 a calculation. That is 786,972 and 836,994.
   - Each unit costs at most `lapD8`'s measured 0.28125 ms a thread, since the plain tower does a
     part of `lapD8`'s work a unit (`lapD8` adds the clock, the copy and the bank).
   - Over 8 threads that projects 27.7 s and 29.5 s with the load.
   - A read whose first 64 problems pass 3,300 ms is stopped and reported incomplete.
4. The rules: `written_rules.py dev.txt train_all.txt pair C F`.

## 7. The recorded failures this loop could repeat

- **Text run on its codec's grain as the exception.** The foil names digits and is used only as a
  cause test. The product's founding, if the cause holds, comes from the machine's own located ring.
- **An authored routine standing in for learning.** Nothing in the foil computes a value. The tower
  learns the same text in other units.
- **Seen material graded as unseen.** Met and never-met calculations are read apart, and so are the
  paired counts.
- **A refusal answered with a larger limit.** Every deadline above is fixed before launch. A run past
  its deadline is reported incomplete and not relaunched with a larger one.
- **Store or copy machinery standing in for learning** (§3). The towers compared have none.
