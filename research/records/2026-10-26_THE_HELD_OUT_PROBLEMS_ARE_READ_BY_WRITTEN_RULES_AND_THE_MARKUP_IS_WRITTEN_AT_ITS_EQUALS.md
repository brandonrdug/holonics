# The held-out problems are read by written rules, and the markup is written at its equals

October 26. Refs #404, #406, #405. The role line closed at the second lap
([record](2026-10-26_THE_REPLAY_IS_THE_PASS_AND_ITS_TOP_STEP_CARRIES_A_THIRD_OF_THE_NAMES_LOSS_SO_THE_ROLE_LINE_CLOSES_AT_THE_SECOND_LAP.md)
§3): John's answer opens with "He", and what it asks is the question's content carried into the
answer and two products written right. This record fixes, before the tower's state is read, the
rules a loop is read by on all 747 held-out problems, the reader that writes what they read, the
exterior baselines beside it, the decision the reading feeds, and the run. Grades: [definition] for
the rules and the reader, [measured] for what the references, the baselines and the development read
gave, [agent-inferred] for each choice and reading. Receipts:
[`…_receipts/`](2026-10-26_THE_HELD_OUT_PROBLEMS_ARE_READ_BY_WRITTEN_RULES_AND_THE_MARKUP_IS_WRITTEN_AT_ITS_EQUALS_receipts/RUN.md).

Computational object: the helical pair interaction, here the pair contact between the tower's
carried face and the next unit it releases, read at the output face where the tower writes a
calculation's value after its `=`. The read touches faces and placement; the helix, the level's
pair contacts, cell holonomy, tube and tower thread stay as the tower has them. Nothing is founded
or deposited: the tower is read at rest.

## 1. The rules

[definition] `tools/gsm8k/written_rules.py` states them in its docstring; in short:

- **(a) on the problem.** A free release's answer (its bytes up to its first blank line) holds at
  least one of the question's content words: its words of at least four letters outside the
  training text's 100 most frequent such words. For John: `john`, `volunteer`, `volunteers`,
  `shelter`.
- **(b) markup.** Each `<<expression=c>>` the answer writes is right when `c` is the expression's
  exact value, in rationals.
- **(c) operands from the question.** The answer's first calculation takes every operand from the
  numerals the question writes or the values of a fixed list of number words (`twice` is 2,
  `dozen` 12, …).
- **(b) at the equals.** At each of the 2,448 calculations the held-out answers write, the
  tower receives the framed question and the answer through the calculation's `=` and writes on;
  the bytes before its first `>>` are right when they are the expression's exact value. A
  calculation is **met** when the training text holds the held-out `<<expression=c>>` whole: 1,572
  are met and 876 never met.

None reads the answer key: (b) reads each calculation's own expression, (a) and (c) read the
question. The final answer after `####` is not read (`tools/gsm8k/README.md`).

[measured] **The rules on the references** (the held-out answers themselves): (a) 743 of 747,
(b) 2,448 right of 2,448, (c) 566 of the 740 answers that calculate. [agent-inferred] (c) is a
strict rule: a quarter of the references take an operand the question never writes, John's among
them (`2*12`, the months of a year), so the references' 566 is its ceiling, not 740.

## 2. The reader

[definition] `read-unit-tower-written` (`tower_train.rs`, beside `sample-unit-tower`): every
problem and every calculation is read by a fork that opens at rest, as the John prompt is, so
each is read alone. The free release is 400 bytes from the framed question (a blank line, the
question, its line end) at one draw, the face as it is, or at two agreeing draws; at each
calculation's `=` the fork writes units at 64 agreeing draws (the arithmetic line's
`read-lines-stream` wrote its sums at 64) until its bytes hold `>>` or a line end, or 8 units are
written. Problem `i` draws from its own window of the key file, so the reading is the same on any
number of threads. Its files are `FREE.tsv` and `MARKS.tsv`; it grades nothing.

[measured] Checked on a development state (`covsmoke/two.state`, the two-clock smoke state, trained
on a 162,937-byte slice, not a state any reading is about): the reader's files hold the 747
problems and the 2,448 calculations in the rules' order, and the rules read them (at the equals
218 of 2,448). Over all 747 problems on 4 threads it moved 582,085 units in 73.3 s, 0.504 ms a unit
a thread; the 16-problem slice took 0.581 ms. Repeated with the units counted, it wrote the same
two files in 75.4 s: 468,588 units were prompts (each problem's framed question and each
calculation's prompt, parsed from rest) and 113,497 released, and the heaviest problem moved 4,720.
The 16-problem slice peaked at 29.8 MiB resident on the 9.6 MB development state.

## 3. The baselines

[measured] `tools/gsm8k/ngram_release.py` writes an interpolated Witten–Bell character n-gram's
releases into the same files, read by the same rules, trained on the same training text (exterior;
its floats are its own; the free release at one draw, each calculation at 64 agreeing draws and at
most 24 bytes):

| | (a) | (b) free | (c) | (b) at the equals | met | never met |
|---|---|---|---|---|---|---|
| references | 743 | 2,448 / 2,448 | 566 / 740 | — | — | — |
| 6-gram | 64 | 570 / 986 | 20 / 533 | 1,348 / 2,448 | 1,318 / 1,572 | 30 / 876 |
| 8-gram | 77 | 981 / 1,155 | 20 / 585 | 1,559 / 2,448 | 1,525 / 1,572 | 34 / 876 |

[agent-inferred] The n-grams write back a calculation they heard and almost never one they did not:
that is recall, the bar a learner that keeps what it heard must reach at the equals. Neither stays on
the problem (a).

## 4. The decision, fixed before the read

The tower's state is `lapD8/STATE`. With `T` its reading at the equals and `G` the 6-gram's:

1. **`T` on met calculations is below `G`'s (1,318 of 1,572).** The tower does not write back what
   it heard. The next loop tests the founded units as the cause: a foil founded on the same text
   whose merges keep each digit its own unit, its tower trained by the same recipe to the stage
   compared, read by these rules beside the committed units' tower at that stage. The foil is a
   cause test and never the product: a founding rule that names digits is text-specific (the
   founding reads any passage of byte classes, `hnn::units`). If the foil reaches `G` on met
   calculations, the next loop derives the founding from the machine's own located ring (the
   tension locates the digits' ring of ten,
   [record](2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md)).
2. **Otherwise, `T` on never-met calculations is under half its rate on met ones.** The tower
   recalls and does not compute; the next loop joins the arithmetic line's founded ring (445 of 495
   held-out sums written on the arithmetic terrain) at the markup's equals.
3. **Otherwise** markup arithmetic is not the failure that binds, and the next loop carries the
   question's content, read by (a) and (c).

Beside the decision, read and reported: (a), (b) free and (c) at one draw and at two agreeing
draws, against the references and the n-grams, and John's two releases, whole, shown to Brandon.

## 5. The run, fixed before it runs

On the PC, at the commit that adds this record, with `RAYON_NUM_THREADS=8`, an 8 GiB memory scope,
alone on the host, `read-unit-tower-written` from `lapD8/STATE` (`70c76578…51c0`) with the committed
units (`d0973c39…782a`) and a fresh key file pinned by its SHA-256:

1. **The development read.** The container's rate belongs to another state, so the rate on
   `lapD8/STATE` is measured first: the 128 held-out problems 100 to 227 (`0be718d4…5c39`, the
   slice the container read) at one draw, unmeasured and so planned at three minutes and stopped
   at 180 s. Its rate `r` is its elapsed time times 8 over the units it moved (prompts plus
   releases), per unit per thread. Its files are not read.
2. **The two reads**, over all 747 held-out problems (`e5bffe0e…3153`), at one draw and then at two
   agreeing draws, each with 400 free bytes, the equals at 64 and a cap of 8 units, one after the
   other because `r` was measured on a lone read. They share their keys and the equals' law, so
   their `MARKS.tsv` must be the same bytes.
   - Projection, upper end, each: the units a read can move are its prompts, 468,588 (fixed by the
     text and the units, whatever the state), plus at most 400 for each free release and 8 for each
     calculation (each unit is at least a byte): 786,972. Times `r` over 8 threads, plus the
     development read's opening time, rounded up to the next 10 s, is the deadline, held by an
     outer `timeout`.
   - The first 64 problems took 10.4% of the container read's time (7,658 of 73,349 ms; 9.9% in its
     repeat). A read whose first `TOWER_WRITTEN_PROGRESS` comes after 11% of its deadline is
     stopped and reported incomplete with its rate.
   - Memory: the reader holds the state and one fork a thread. The ceiling stays 8 GiB and each
     read's peak is reported.
3. `written_rules.py` reads both directories against the held-out text and the training text
   (`050b94f3…3b95`, the text `lapD8` trained on and the n-grams were trained on).

## 6. The units

An outside audit of the John line (another thread, October 26) proposed reading the founded units
as a cause, and quoted the n-gram baselines on the John prompt. [measured, checked here] The
committed units parse John's answer as

```text
'He ' | 'v' | 'ol' | 'un' | 't' | 'e' | 'ers ' | '2*' | '12' | '=' | '<<' | '2*' | '12' | '=' | '24>>' | '24' | ' times ' | 'a ' | 'year'
'So ' | 'he ' | 'v' | 'ol' | 'un' | 't' | 'e' | 'ers ' | 'for ' | '24' | '*' | '3=' | '<<' | '24' | '*' | '3=' | '7' | '2' | '>>' | '7' | '2' | ' hour' | 's'
```

The digits are welded to the operators and the markup differently from one calculation to the
next (`2*` `12` `=` against `24` `*` `3=`; the value `24>>` inside the markup and `24` after it),
against the digit-word law (a number is a digit word at a level of the base's tower). Whether this
is why the tower writes `2*2=8` is what decision 1 tests, if the reading reaches it.

## 7. The recorded failures this loop could repeat

- **An authored routine standing in for learning.** The rules and the n-grams are exterior reads;
  nothing enters the machine, and no release is selected by them.
- **Seen material graded as unseen.** The problems are held out, but a met calculation is a fact
  the training text holds whole: met and never met are read apart, never summed into one rate that
  would pass recall off as computation.
- **Bits read as progress** and **a single scalar of progress.** No bits are read; the reads are
  reported side by side and never combined.
- **Text run on its codec's grain as the exception.** The rules read GSM8K's markup and words, and
  they stay outside the machine. The units foil, if it runs, is a cause test, and the product's
  founding would come from the machine's own located ring.
- **A refusal answered with a larger limit.** The run's deadline is fixed above, and a run past it
  is reported incomplete, never relaunched with a larger one.
