# The name's rival at the answer's opening is "The ", and the pass takes most of the lost margin from the readout

**Withdrawn, October 26.** The reset clock this record builds or measures is a copy pointer: it
holds the unit that arrived after a chosen class and raises that unit's logit at the output. An
audit made at Brandon's request found it, and commit `0934a25ff` retired it ([the
retirement](2026-10-26_THE_STORES_AND_COPIERS_ARE_RETIRED_AND_THE_PLAIN_TOWER_CODES_THE_SAME_BITS_WITHOUT_THEM.md)).
The measurements below stand only as measurements of that machinery, never as progress of the
learner, and nothing here is a design to resume.

October 26. Refs #404, #405, #386. The read the previous record fixed
([record](2026-10-26_THE_PASS_LOWERS_THE_ROLE_ON_SEEN_PROBLEMS_TOO_SO_THE_COPY_LOSES_ITS_MARGIN.md) §3),
on Brandon's PC at `dff592a16`. Grades: [measured] for what the runs printed, [agent-inferred] for each
reading of them. Receipts:
[`…_receipts/`](2026-10-26_THE_NAMES_RIVAL_AT_THE_ANSWERS_OPENING_IS_THE_AND_THE_PASS_TAKES_MOST_OF_THE_LOST_MARGIN_FROM_THE_READOUT_receipts/RUN.md).

Computational object: the helical pair interaction, here the pair contact between the answer's first
arrival and the arrival the blank line's clock holds, read at the output face beside the readout's
own face. The read touches faces and placement only; the helix, the level's pair contacts, cell
holonomy, tube and tower thread stay as the tower has them.

## 1. The margin taken apart

[measured] At each named answer that opens with the name, the margin of the answer's first unit over
its strongest rival, in bits, as the readout's own part plus the copies' raise on the first unit less
their raise on the rival (means):

| state | seen: first | seen margin | readout | raise on the name | held out: first | held-out margin | readout | raise on the name |
|---|---|---|---|---|---|---|---|---|
| `lapD8` | 695 of 1,074 | +0.417 | −3.865 | +4.289 | 53 of 97 | −0.010 | −4.269 | +4.260 |
| `lap3T8` (one more pass) | 561 | −0.063 | −4.066 | +4.009 | 37 | −0.573 | −4.542 | +3.969 |
| `lap3D8` (one more pass, `"="` founded) | 599 | −0.047 | −4.039 | +3.999 | 43 | −0.337 | −4.315 | +3.978 |

- The blank line's clock holds the answer's first unit in 1,072 of the 1,074 seen answers and all 97
  held out. The raise on the rival averages at most 0.008 bits: no clock holds the rival in 1,071 seen and
  all 97 held out.
- Where the rival carries more than the name it is `"The "` in 369 of 379 seen answers at `lapD8`
  (then `"#### "` 6, `"If "` 3) and in all 44 held out; at `lap3T8` in 477 of 513 seen (`"If "` 26) and
  60 of 60 held out.
- So the readout alone prefers `"The "` to the name by about 4 bits at the opening, and the copy's
  raise of about 4 bits sets the name level with it. The role read counts which side of that level
  each answer falls on.

## 2. The copies' own weights

[measured] Each clock's bias `b_A` in bits and its row's length `‖r_A‖` (on the top face's unit):

| clock | `lapD8` | `lap3T8` | `lap3D8` |
|---|---|---|---|
| after the blank line | 0.571, 1.870 | 0.800, 1.944 | 0.791, 2.013 |
| after `"any "` | 0.326, 1.767 | 0.448, 1.832 | 0.449, 1.812 |
| after `"="` | — | — | 0.036, 1.067 |

[agent-inferred] Over the pass the blank line's copy grows in bias and in length while its raise at
the answers' openings falls by 0.280 bits seen and 0.291 held out. The copy is not shrinking: its row
turns away from the face the readout reads at an answer's opening, while it gains where the held name
recurs elsewhere.

## 3. The decision

[measured; by the rule fixed in the previous record's §3] Over the 165 seen answers `lapD8` gave the
largest mass and `lap3T8` lost, the margin fell 1.163 bits: the readout's part −0.796, the raise on
the name −0.348, the raise on the rival +0.019. The readout's part falls most, and held out the same
(17 lost: −0.855 of −1.098). By the rule this is case 2: the pass raises another class at the opening
through the readout, and the next loop reads which classes the rivals are and what the readout's
covector does there. The rival is read (§1): `"The "`.

Beside it [measured]: over the 530 seen answers kept, the margin fell 0.424 with the raise taking
−0.321 of it. Both parts fall over the pass, and the answers that cross the level are the ones where
the readout fell most.

## 4. What the covector does at the opening

[agent-inferred] Of the 4,524 named problems of the training text, 1,074 answers open with the name
(23.7%); of the 421 held out, 97 (23.0%). The rest open with `"The "` and other words. At every
named answer's opening the comparison `p̂ − q` asks the face for the frequency the answer opens with
the question's first unit, about a quarter, and the copy's raise there is read on all 4,524 openings,
not only on the 1,074. A face that gives the name a mass near a quarter puts it level with `"The "`
on a large share of the answers that do open with it, so the role read counts a margin near zero.
Whether that is what happened is measured by the face's mass on the name at every named opening
beside how often the answer opens with it.

## 5. The next read: the face at every named opening, its decision fixed now

[definition] `read-tower-clock-cells` now writes each held class's code beside its raise, and the
observer's `copies` mode reads every named answer's opening, whatever it opens with. The clock holding
the question's first unit is the one whose held class's piece the problem opens with (the longest such
piece). It prints the face's summed mass on that unit, the face's own deviation of the count
`√Σ p(1 − p)`, and how many answers open with it, in all and by bands of the mass. Beside these it
prints how often the unit carries the largest mass where the answer opens otherwise, the mean code of
every answer's actual first unit, and what the answers open with otherwise. The read runs on `lapD8`,
`lap3T8` and `lap3D8`, over the training text and held out.

The decision, fixed before the read, on the training text, where the pass's covector is summed:
1. **The pass calibrates the name.** At `lap3T8` the count of answers opening with the question's first
   unit lies within two of the face's own deviations of its summed mass, or the pass moved the summed
   mass toward the count. Then the pass does what its comparison asks at the openings, and the role
   read's largest mass reads where a calibrated mass near a quarter crosses `"The "`. The next loop
   re-derives the role item on what the key determines, with the mass bands showing how far the face
   tells the answers that open with the name from the rest, and fixes it before any lap. The bar of
   49 of 97 is not lowered on the same read.
2. **The pass moves the name away from its frequency.** At `lap3T8` the summed mass lies more than two
   deviations below the count and further from it than at `lapD8`. Then the openings' own covector is
   outweighed by the copy's and the readout's covectors elsewhere. The next loop reads those
   covectors by place: the openings beside the cells where the held name recurs.

`lapD8/STATE` stays the state the role and John are read from, and no lap is taken until the read
decides.

## 6. The recorded failures this loop could repeat

- **An authored routine standing in for learning.** Nothing names `"The "` or a name to the machine:
  the rival and the held unit are read off the face and the clocks, and the observer's held unit is
  whichever held piece the problem opens with.
- **A refusal answered with a larger limit.** No further lap is taken. If the role item is re-derived,
  its replacement is fixed before any run and the old bar is not lowered on the old read.
- **Seen material graded as unseen.** The decision is read on the training text, where the pass's
  covector is summed; held out is read beside, and neither is counted toward a lap's acceptance.
