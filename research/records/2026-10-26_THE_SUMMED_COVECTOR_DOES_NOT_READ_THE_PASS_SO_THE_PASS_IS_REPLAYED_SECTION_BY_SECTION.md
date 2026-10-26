# The summed covector does not read the pass, so the pass is replayed section by section

October 26. Refs #404, #405, #386. The read the previous record fixed
([record](2026-10-26_THE_PASS_MOVES_THE_NAMES_MASS_AWAY_FROM_HOW_OFTEN_THE_ANSWER_OPENS_WITH_IT_SO_EACH_PLACES_PULL_IS_READ_THROUGH_THE_STEP.md)
§4), on Brandon's PC at `58d3a05db`, and the read its failed gate calls for, built here with its
decision fixed before it runs. Grades: [measured] for what the runs and tests printed,
[agent-inferred] for each reading of them, [definition] for what the new reader computes. Receipts:
[`…_receipts/`](2026-10-26_THE_SUMMED_COVECTOR_DOES_NOT_READ_THE_PASS_SO_THE_PASS_IS_REPLAYED_SECTION_BY_SECTION_receipts/RUN.md).

Computational object: the helical pair interaction, here the pair contact between the next arrival
and the arrival a reset clock holds, read at the output face beside the readout's own face, and the
deposition's step that moves both, now section by section with its moments. The read touches faces
and placement and the deposition; the helix, the level's pair contacts, cell holonomy, tube and
tower thread stay as the tower has them.

## 1. The summed reading at the state the pass starts from

[measured] `read-tower-clock-covectors` on the training text, 8 streams, sections of 128 units, at
`lapD8` and at `lap3T8` (one pass later); `change` on the calibration's copies files.

- Openings: of 4,524 requests all are placed; a clock holds the name at 4,519 and none at 4, and one
  opening lies in the tail of a stream's share past its last whole section, which the training
  pass's partition does not read. The summed mass on the name is 906.5 at `lapD8` and 750.3 at
  `lap3T8`, the calibration's 906.6 and 750.4 less that opening.
- The pass's measured change over every named opening where a clock holds the name in both states:
  `ΔF_meas = −1,415.655` bits (−0.313 an opening); the raise changes by −0.025 bits an opening on
  `"any "`'s clock and by −0.261 on the blank line's. Beside it, to `lap3D8`: −1,400.863 bits,
  −0.082 and −0.280.
- The gate, each clock's bias change over the pass:

| clock | bias at `lapD8` | measured change | predicted from `lapD8`'s summed covector | predicted from `lap3T8`'s |
|---|---|---|---|---|
| 0, after `"any "` | 21,337 | +8,025 | +392,159 | +365,900 |
| 1, the blank line | 37,441 | +15,001 | −318,538 | −120,902 |

- Summed at `lapD8`, the reading puts the name's predicted change on the blank line's copy
  (−281,124.5 bits, against the readout's −10,755.1), its largest pulls from cells elsewhere where no
  held class arrives (−560,897.0) and from the answers' cells where the name does not arrive
  (−340,937.3), against the openings where it arrives (+305,776.4). The plain total `⟨Y, G⟩` is
  negative at both states.

## 2. The gate fails

[measured; by the rule fixed in the previous record's §4] The blank line's predicted change has the
wrong sign, and the predicted ratio of the blank line's change to `"any "`'s is −0.81 against the
measured 1.87. The summed reading is not a reading of this pass, so its shares decide nothing.

[measured] The reader's covector is the learner's own:
`the_copies_reading_sums_the_reverses_covector_on_the_copies_and_the_readout` sums `Σ δz[held] (x, 1)`
and `Σ δz ⊗ (x, 1)` from the copies' reading and finds them equal, entry for entry, to the reverse's
covector on the clocks' copies and the readout. The failure is the pass's, not the instrument's.

[agent-inferred] The predicted changes are 20 to 50 times the measured ones, and the third lap's
receipts record no halving in the pass, so the certificate does not shrink the pass's steps. The
summed reading reads every section's covector at the start's material and second moments and leaves
out the moment the pass opened with. Three readings fit: the covector along the pass is not the
start's (each section moves the material, and the bias then sits where the sections' covectors
balance), the second moments change over the pass, or the moment the pass opened with carries the
change. The replay separates them.

## 3. The replay

[definition] `replay-tower-clock-pass` takes the pass itself. The learner of `STATE` takes one pass
over the training text in its own partition, `TowerLearner::section_realized` on the host section
by section, as `train-unit-tower` takes it, and the end state's SHA-256 is compared with the pass's
(`lap3T8/STATE`, `33317844…f6be`). Before each section the streams' carried states read the section
at the present material, and every cell's covector on the clocks' copies and the readout is summed
by its group (the eight groups of the previous record's §3).

- The groups' sum must be the section's own covector. `TowerLearner::first_after` moves the first
  moment toward that sum as the section moves it, and the result is checked, entry for entry,
  against the moment the section leaves; a difference refuses the run.
- The first moment is linear in the sections' covectors, so it splits into parts carried `2^(−16)`
  finer: each group's part moves toward the group's covector at the first moment's rate `2^(−3)`, and
  the moment the pass opened with decays at that rate.
- Each part's share of a section's step is the deposit's step of its moment at the section's second
  moments (`TowerLearner::step_of_moments`, the deposit's own `deposit_root` and `deposit_over`),
  released by the certificate's halvings. What the moments' and the deposit's rounding leave is the
  remainder, so the parts sum to the step taken exactly.
- Over the pass each part's summed step is read through the covector toward the name at the openings
  (`Y`, as the summed reading reads it) at the start state and at the end state. Each part's line
  gives its first-order change of `F = Σ_o log₂ p̂_o(n)` on the readout and on each clock's copy, at
  the start's `Y` and the end's, and its change of each clock's bias. The trapezoid of the two is
  the part's share. Beside them, `F` read at both states and its change `ΔF`, and each clock's
  realized bias change against the summed reading's prediction from the start's covector and from
  the covector summed along the pass, both at the start's second moments.

The library readings the replay uses are the deposit's own: `Tower::step_grain_at` puts a declared
covector on the deposit's grain by `on_step_grain`; `TowerLearner::step_for` is now
`step_of_moments` of that, and its doc says the hold is not read.

[measured] Checks:
- `a_sections_moment_and_deposit_are_read_from_its_covector`: on an opened learner, a second
  section's covector read by the reverse gives, through `first_after`, the first moment the section
  leaves, and `step_of_moments` of that moment, released by the section's halvings, is its deposit
  on the copies and the readout; a moment split in two parts carried 16 bits finer steps as the
  parts' steps sum, within two grains of the finer carrier.
- The smoke, in this container on a 300-problem slice of the training text (61,952 cells, 4 streams,
  121 sections) from a two-clock state whose copies open at zero: one `train-unit-tower` pass took
  35.2 s and reached `d2aeb993…c34f`; the replay of that pass took 65.2 s, passed every section's
  moment check and reached the same state. The remainder moved the blank line's bias by −14.8 grains
  of the realized +18,308; the whole step's trapezoid read +703.1 bits against the measured
  `ΔF = +771.1`; and the blank line's realized +18,308 grains stood against +217,595 predicted from
  the start's covector and +24,602 from the covector summed along the pass. [agent-inferred] On the
  slice the first-order reading holds along the pass, and the summed reading at the start fails by
  its path; the slice decides nothing about the pass on the PC.

## 4. The decision, fixed before the read

The replay runs from `lapD8/STATE` over the training text, 8 streams, sections of 128 units,
expecting `lap3T8/STATE`.

0. **The replay is the pass.** Every section's groups reproduce the section's first moment (else
   the run refuses), and the end state's SHA-256 equals `lap3T8`'s. If either fails, the replay is
   not the pass, and the next loop repairs the reader before any reading.
1. **Case A: the lower levels carry the change.** The trapezoid of the whole step's first-order
   change on the copies and the readout (`TOWER_REPLAY_TOP`) does not carry the sign of the replay's
   measured `ΔF`, or is under half its size. Then the change of the top face carries the pass's
   effect on the name, and the next loop reads the lower levels' covector by place, through the
   change of `x`, by `section_compared`'s law.
2. **Otherwise the most negative part names the cause.** Among the eight groups, the opening moment
   and the remainder, the part whose trapezoid share (readout and copies together) is most negative:
   - **a group** names the place; the family that carries most of that part's share (the readout, or
     a clock's copy) names the face. The next loop derives the key that separates that place from
     the openings where the name arrives. It never weights the openings' comparison, which would be
     an authored routine, and its acceptance is fixed before any build.
   - **the opening moment** carries it: the next loop replays the pass before (the second lap's, from
     its founding) the same way.
   - **the remainder** carries it: the next loop derives the moments' and the deposit's rounding at
     these families.

Beside the decision, fixed too: for the blank line's clock, if the prediction from the covector
summed along the pass carries the realized change's sign and lies within a factor of two of it,
the summed reading failed by its path (the covector along the pass is not the start's); otherwise by
the second moments or the opening moment, whose shares the part lines give.

`lapD8/STATE` stays the state the role and John are read from, and no lap is taken until the read
decides.

## 5. The recorded failures this loop could repeat

- **A located cause carried unrepaired into a new consumer.** The summed reading failed its gate, so
  none of its shares enters a decision; the replay checks its own covector against the learner's
  moment at every section and its end state against the pass's before it reads anything.
- **An authored routine standing in for learning.** Nothing enters the machine: the replay takes
  the pass the training command takes and reads beside it. The places are the problem's own
  question, opening and answer, and no word is named to the machine.
- **Bits read as progress.** `ΔF` and the shares read where the name's mass goes over the pass; none
  is counted as a gain toward the acceptance.
- **A refusal answered with a larger limit.** The run's deadline is fixed from its projection; a stop
  at it is reported incomplete and not relaunched with a larger one.
- **Seen material graded as unseen.** The read is on the training text, where the pass's covector is
  summed; nothing here counts toward the held-out acceptance.
