# The pass moves the name's mass away from how often the answer opens with it, so each place's pull is read through the step

October 26. Refs #404, #405, #386. The read the previous record fixed
([record](2026-10-26_THE_NAMES_RIVAL_AT_THE_ANSWERS_OPENING_IS_THE_AND_THE_PASS_TAKES_MOST_OF_THE_LOST_MARGIN_FROM_THE_READOUT.md)
§5), on Brandon's PC at `f21cf37a2`, and the read it decides, built here with its decision fixed
before it runs. Grades: [measured] for what the runs and tests printed, [agent-inferred] for each
reading of them, [definition] for what the new reader computes. Receipts:
[`…_receipts/`](2026-10-26_THE_PASS_MOVES_THE_NAMES_MASS_AWAY_FROM_HOW_OFTEN_THE_ANSWER_OPENS_WITH_IT_SO_EACH_PLACES_PULL_IS_READ_THROUGH_THE_STEP_receipts/RUN.md).

Computational object: the helical pair interaction, here the pair contact between the next arrival
and the arrival a reset clock holds, read at the output face beside the readout's own face, and the
deposition step that moves both. The read touches faces and placement and the deposition's step;
the helix, the level's pair contacts, cell holonomy, tube and tower thread stay as the tower has
them.

## 1. The face's mass on the name at every named opening

[measured] At every named answer's opening (4,520 of the training text's 4,524 read, 419 of the 421
held out; at the other 6 no clock holds the question's first unit), the face's summed mass on the
question's first unit, its own deviation of the count `√Σ p(1 − p)`, and how far the count of answers
opening with that unit lies below it:

| state | training: mass | deviation | count 1,118 lies above by | held out: mass | deviation | count 102 lies above by |
|---|---|---|---|---|---|---|
| `lapD8` | 906.6 | 25.3 | 8.4 deviations | 79.7 | 7.6 | 2.9 |
| `lap3T8` (one more pass) | 750.4 | 23.6 | 15.6 | 62.7 | 6.9 | 5.7 |
| `lap3D8` (one more pass, `"="` founded) | 754.5 | 23.7 | 15.3 | 64.8 | 7.0 | 5.3 |

- By the face's mass at `lapD8` on the training text, how often the answer opens with the name:
  mass 0.051 opens 0.185; 0.149, 0.241; 0.247, 0.301; 0.345, 0.297; 0.444, 0.268; 0.560, 0.250
  (172 openings); 0.722, 0 of 5. At `lap3T8` the bands are near the same, and fewer openings stand in
  the upper ones (431 above 0.4 at `lapD8`, 225 at `lap3T8`).
- The name carries the largest mass at 1,859 openings where the answer opens otherwise (`lap3T8`
  1,437, `lap3D8` 1,539). Those answers open with `"The "` 584, `"First "` 383, `"He "` 375,
  `"If "` 189, and others.
- The answers' actual first unit codes 4.553 bits on the mean at `lapD8`; the pass adds 0.045
  (`lap3T8`) and 0.017 (`lap3D8`).
- The earlier lines are unchanged byte for byte, and the largest-mass counts equal the role read's
  (695, 561, 599 seen; 53, 37, 43 held out).

[agent-inferred] The face's mass on the name tells the answers that open with it from the rest
little: from a mass of 0.05 to 0.25 the frequency rises from 0.19 to 0.30, and above 0.3 it falls
again, below the mass. So the mass's order is not a reading of what decides the opening.

## 2. The decision: case 2

[measured; by the rule fixed in the previous record's §5] At `lap3T8` the summed mass lies 15.6
deviations below the count, further than at `lapD8` (8.4). Held out the same (2.9 to 5.7). This is
case 2: the pass moves the name's mass away from how often the answer opens with it.

[agent-inferred] Read at the openings alone, the comparison `p̂ − q` asks the summed mass up toward
the count, since the mass lies below the count in every band under 0.3. The pass moves it down, so
the covectors the pass sums elsewhere outweigh it there. By the rule, the next loop reads those
covectors by place.

## 3. The next read: each place's pull on the name, read through the step

[definition] `read-tower-clock-covectors` reads one state over the training pass's own partition
(`STREAMS` streams of `chunk = len/streams` classes, `(chunk − 1)/section` sections each). A problem
runs from its first byte `f` to the byte after the blank line following its answer's opening `p`;
its name `n` is the class at `f`. Each cell falls in one of eight groups: place {question, opening,
answer, elsewhere} by whether the class that arrives next is the name (elsewhere, a class some clock
holds). Over each group it sums the covector the pass sums:

- on each clock's copy, `G_(r_A) = Σ δz[held] x` and `G_(b_A) = Σ δz[held]`;
- on the readout, `G_U = Σ δz ⊗ x` and `G_c = Σ δz`;

with `δz = p̂ − [· = next]` on `2^(−24)` and `x` the top face on `2^(−16)`. At every opening where a
clock holds the name it sums the covector toward the name, `Y = Σ_o δz_o^(n) ⊗ (x_o, 1)` with
`δz^(n) = p̂ − [· = n]`, on the same families.

With `F = Σ_o log₂ p̂_o(n)`, `∂F/∂z = −δz^(n)` (the logits are in bits), and the learner moves
`θ → θ − step(G)`. So to first order the pass changes `F` by

```text
ΔF = ⟨Y, step(G)⟩      on 2^(−64) bits: a row's step on 2^(−24) against Y on 2^(−40);
                       a bias's step on 2^(−16) against Σ δz on 2^(−24), raised by 24.
```

`step` is the learner's own deposit at its present second moments:
`TowerLearner::step_for(start, g)` puts `g` on the step grain and returns
`((g << grain) >> rate) / (⌊√v⌋ + 1)` entry by entry, `v` the learner's second moment, and refuses a
move-chart family. The section's deposit and this reading now share the two functions
(`on_step_grain`, `deposit_step`), so the reading cannot drift from the deposit.

Each group's line prints its share of `ΔF` on the readout (the rows of classes that name a problem
and the rest) and on each clock's copy, in bits. Beside it, the plain share `⟨Y, G⟩` in the
parameters' own units (a row's on `2^(−80)`, a bias's raised from `2^(−48)`) in parts a thousand of
the total's size, and the change of each clock's raise, `−⟨X, step(G)⟩` over `X = Σ_o (x_o, 1)`, a
mean per opening. The whole line adds each clock's bias and its predicted change `−step(G_(b_A))`,
and the sign of the plain total. The lower levels are not read: a change of the top face `x` lies
outside this reading.

`tools/listener/bank_trace.py change` reads the measured counterpart from two copies files: over
every named opening where a clock holds the question's first unit in both, the summed change of its
log-mass `Σ Δ log₂ p̂`, and each clock's mean change of raise.

[measured] Checks:
- `the_step_read_for_a_sections_covector_is_the_step_it_deposits`: a fresh learner's first section
  moves the copies and the readout by exactly `step_for` of the section's covector, released by the
  halvings its certificate took.
- `the_step_moves_a_names_log_mass_as_its_first_order_reading_says`: moving the readout and the
  copies by `2^(−3)` of the step changed `F` by −53,530 against the reading's −53,351 (on `2^(−20)`
  bits), and by `2^(−5)` of it −13,178 against −13,338.
- On a 300-problem slice of the training text in this container (4 threads), the reader read 61,952
  cells in 10.4 s, against 7.2 s for `read-tower-clock-cells` on the same input (ratio 1.45). Its
  summed mass on the name was 2.5 over 202 openings, beside the observer's 2.6 over 203 in the
  held-cells partition.
- `change` on a constructed pair of files shifted by one bit gave +203.000 bits over 203 openings and
  +1.000 raise.

Projection on the PC: the largest training read of the same partition took 37.6 s; times 1.45 is
54.5 s, so the deadline is 60 s. Memory: 9 sums of the readout's `1,318 × 65` entries on 16 bytes in
each of 8 streams is about 99 MB beside the read's 108 MB, so about 210 MB under the 8 GiB ceiling.

## 4. The decision, fixed before the read

The reader runs on `lapD8` (decisive: the state the pass started from) and on `lap3T8` (beside),
training text, 8 streams, sections of 128 units. `change` runs on the calibration's copies files,
`lapD8` then `lap3T8` (giving `ΔF_meas`) and `lapD8` then `lap3D8` (beside). `ΔF_top` is the whole
line's readout share plus every clock's share at `lapD8`.

1. **The gate: is the summed reading a reading of this pass?** The measured bias changes over the
   pass are +8,025 grains on `"any "`'s copy and +15,001 on the blank line's. Both predicted changes
   must carry the measured sign, and the predicted ratio of the blank line's to `"any "`'s must lie
   within a factor of two of the measured 1.87. [agent-inferred] The gate reads a ratio, not a size,
   because the pass's per-section halvings and its moving first moment scale the whole step, which
   moves no place's share against another's. Then `ρ` = measured over predicted change on the blank
   line's bias scales the reading. If the gate fails, the summed reading is not a reading of this
   pass, and the next loop reads the pass section by section.
2. **Case 3: the lower levels turn the pass.** `ρ·ΔF_top` does not carry `ΔF_meas`'s sign, or is
   under half its size. Then the change of the top face carries the pass's effect on the name. The
   next loop reads the whole tower's covector by place, by `section_compared`'s law.
3. **Case 1: the deposit's normalization turns the pass.** Otherwise, the plain total `⟨Y, G⟩` is
   positive (the plain gradient would raise `F`) while the step lowers it. Then the per-entry second
   moments turn the pass. The next loop derives the step law at these families.
4. **Case 2: a place outweighs the openings.** Otherwise, the group with the most negative share
   (readout and copies together) names the place, and the family carrying most of that share names
   the face. The next loop derives the key that separates that place from the openings where the
   name arrives. It never weights the openings' comparison, which would be an authored routine. Its
   acceptance is fixed before any build.

`lapD8/STATE` stays the state the role and John are read from, and no lap is taken until the read
decides.

## 5. The recorded failures this loop could repeat

- **An authored routine standing in for learning.** Nothing enters the machine: the reader and the
  observer are exterior. The places are the problem's own question, opening and answer, located by
  where the name was read, and no word is named to the machine. Case 2's next loop derives a key; it
  never reweights the comparison at the openings.
- **Bits read as progress.** `ΔF` reads where the name's mass goes over the pass; no share is
  counted as a gain toward the acceptance.
- **A located cause carried unrepaired into a new consumer.** The step reading shares the deposit's
  own functions, and the first-order reading was checked against an actual step before it runs on
  the PC.
- **A refusal answered with a larger limit.** No lap is taken. The read's deadline is fixed from its
  projection; a stop at it is reported incomplete and not relaunched with a larger one.
- **Seen material graded as unseen.** The decision is read on the training text, where the pass's
  covector is summed; held out is read beside and counts toward no acceptance.
