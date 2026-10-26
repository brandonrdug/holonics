# The replay is the pass, and its top step carries a third of the name's loss, so the role line closes at the second lap

**Withdrawn, October 26.** The reset clock this record builds or measures is a copy pointer: it
holds the unit that arrived after a chosen class and raises that unit's logit at the output. An
audit made at Brandon's request found it, and commit `0934a25ff` retired it ([the
retirement](2026-10-26_THE_STORES_AND_COPIERS_ARE_RETIRED_AND_THE_PLAIN_TOWER_CODES_THE_SAME_BITS_WITHOUT_THEM.md)).
The measurements below stand only as measurements of that machinery, never as progress of the
learner, and nothing here is a design to resume.

October 26. Refs #404, #405, #386. The section-by-section replay of the third lap's pass, fixed in
the [stopped run's record](2026-10-26_THE_REPLAY_STOPPED_AT_ITS_FIRST_WINDOW_SO_IT_READS_THE_SECTIONS_OWN_OPENING_READ.md)
§4, ran to its end on Brandon's PC. This record gives what it read, the decision its fixed rule
gives
([record](2026-10-26_THE_SUMMED_COVECTOR_DOES_NOT_READ_THE_PASS_SO_THE_PASS_IS_REPLAYED_SECTION_BY_SECTION.md)
§4), and why the loop that rule names is not taken. Grades: [measured] for what the run printed,
[agent-inferred] for each reading of it. Receipts:
[`…_receipts/`](2026-10-26_THE_REPLAY_IS_THE_PASS_AND_ITS_TOP_STEP_CARRIES_A_THIRD_OF_THE_NAMES_LOSS_SO_THE_ROLE_LINE_CLOSES_AT_THE_SECOND_LAP_receipts/RUN.md).

Computational object: the helical pair interaction, here the pair contact between the next arrival
and the arrival a reset clock holds, read at the output face beside the readout's own face, and the
deposition's step that moves both. The read touches faces and placement and the deposition; the
helix, the level's pair contacts, cell holonomy, tube and tower thread stay as the tower has them.

## 1. The run

[measured] At `cea8c660c`, from `lapD8/STATE` over the training text, 8 streams, sections of 128
units, `RAYON_NUM_THREADS=8`, an 8 GiB memory scope, alone on an idle host. Exit 0 in 276.3 s
against the projection's upper end of 303.2 s (0.911) and its expected 259 s (1.067), deadline 304 s,
peak resident set 598,440 KiB. A section took 141.8 ms against the expected 130.9 ms and the bound
164.7 ms; every whole 32-section window lay between 4,485 and 4,679 ms, under the stop line of
5,270 ms. The log ([`REPLAY.log`](2026-10-26_THE_REPLAY_IS_THE_PASS_AND_ITS_TOP_STEP_CARRIES_A_THIRD_OF_THE_NAMES_LOSS_SO_THE_ROLE_LINE_CLOSES_AT_THE_SECOND_LAP_receipts/REPLAY.log))
is every line it printed, whole.

## 2. What it read

**Step 0 holds: the replay is the pass.** [measured] All 1,311 sections passed their moment check
(the run refuses at the first that fails), and the state reached is
`3331784425b9…f6be`, the third lap's (`TOWER_REPLAY_STATE … expected=match`).

**Case A: the lower levels carry the change.** [measured] Over the 4,519 openings the start holds,
the name's log-mass falls by `ΔF = −1,415.823` bits (`name_mass` 906.5 to 750.3). The whole step's
first-order change on the copies and the readout, read as the trapezoid of its start and end
(`TOWER_REPLAY_TOP`), is `−445.259`: the same sign and 0.314 of `ΔF`, under half. By the fixed rule
the change of the top face carries the pass's effect on the name: about two thirds of the name's
loss comes from the lower levels moving the top face `x`, not from the step on the copies and the
readout. [agent-inferred] The remainder also holds the step's second-order part, which the
trapezoid of a first-order reading does not separate from the lower levels' part.

[measured] Within the top step, by family (trapezoid of start and end): the readout `+42.47`, the
first clock's copy `−0.14`, the blank line's clock's copy `−487.59`. The step that lowers the name
is the blank line's copy; the readout's own step raises it a little.

**The place parts cancel.** [measured] Every place part is two to three orders larger than the sum
it makes. For the blank line's copy at the start: where the name arrives (`arrives=1`) each place
raises the name (question `+182,910`, opening `+308,628`, answer `+298,079`, elsewhere `+222,090`),
where it does not (`arrives=0`) each lowers it (`−144,999`, `−177,650`, `−201,114`, `−488,715`), and
the eight sum to `−771.8`; the opening moment adds `+193.6` and the remainder `−1.8`, `−580.1` in
all. Summed over arrival, the question, the opening and the answer raise the name (`+37,911`,
`+130,978`, `+96,964`) and the cells elsewhere lower it (`−266,625`). [agent-inferred] A first-order
reading that is the small residue of opposed pulls up to 630 times its size is not a reading of one
place's cause; under Case A the split is not read further.

**The summed reading failed by its path.** [measured] For the blank line's clock the realized bias
change is `+15,001`; the covector summed along the pass predicts `+14,379` (0.959), and the
covector at the start predicts `−318,538`. For the first clock: `+8,025`, `+8,059` along the pass,
`+392,159` at the start. By the rule fixed beside the decision, the summed reading failed because
the covector along the pass is not the start's, not because of the second moments or the opening
moment.

## 3. The decision: the role line closes at the second lap

The fixed rule names Case A's next loop: read the lower levels' covector by place, through the
change of `x`, by `section_compared`'s law, about eight masked reverses a section. It is not taken.

[agent-inferred, from the key's own acceptance] The role key's acceptance has two halves. The
held-out role half (the answer's opening unit most massive on at least 49 of the 97 held-out answers
that open with the name) is met by the second lap's state, `lapD8`: 53 of 97. The John half reads
one held-out problem, and its reference answer, whole, is

```text
He volunteers 2*12=<<2*12=24>>24 times a year
So he volunteers for 24*3=<<24*3=72>>72 hours
#### 72
```

It opens with "He" and never names John (checked against GSM8K's training row 207, which the
partition holds out). A role key that read every named opening perfectly would put no right word
into this answer; what it asks is the question's content carried into the answer and two products
written right. The third lap's loss of the role (53 to 43) explains a teacher-forced margin that
`lapD8` already holds, and no further reading of it can move the John half. So:

- `lapD8/STATE` is the state kept. The third lap is not taken further and no lap of this kind
  follows.
- The lower levels' by-place read is parked here, with its law and its cost above, for the day a
  loop needs a pass's effect on one face located below the top.
- The John prompt stays the sample shown to Brandon at the end of a loop, and stops being a loop's
  gate: the same 0 of 16 is scored by a 6-gram, an 8-gram, retrieval and a standard tiny model of
  the tower's size, so it cannot tell two designs apart. The next loop's gate is read on all 747
  held-out problems by written rules (the
  [next record](2026-10-26_THE_HELD_OUT_PROBLEMS_ARE_READ_BY_WRITTEN_RULES_AND_THE_MARKUP_IS_WRITTEN_AT_ITS_EQUALS.md)).

An outside audit of the John line (another thread, October 26) reached the same reading of the
reference answer and of the role margin; its baselines and its parse of the founded units are
quoted in the next record, with what was checked here.

## 4. The recorded failures this loop could repeat

- **Bits read as progress** and **a single scalar of progress.** The role's 53 of 97 is a
  teacher-forced margin; it is reported as the key's half met, never as movement toward John.
- **A located cause carried unrepaired into a new consumer.** The replay located where the name's
  loss lies (the lower levels' change of the top face); it is recorded and parked, not carried into
  a further lap.
- **A failed gate is the next loop's subject.** The failed half is John's, so the next loop reads
  what John's answer needs (the question's content and the markup's arithmetic) on all 747 held-out
  problems, named by its measurement.
- **Seen material graded as unseen.** The replay is on the training text; nothing here counts
  toward a held-out acceptance.
