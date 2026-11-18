# Cooling was measured on November 4 and retired, the line's level is traded by its mix, an open place is never a source, and a change to a line runs beside a control

November 18, 03:20 UTC. A second audit of the store line, made the same hour as
[the audit of November 18](2026-11-18_THE_LINE_FLAILS_BECAUSE_A_FIXED_RATE_DEPOSIT_TRACKS_AN_UNSHUFFLED_MOVING_TERRAIN_PARTS_ARE_ADDED_AND_NEVER_REMOVED_AND_PAST_CONFIGURATIONS_WERE_BARRED_BY_NAME.md)
by another thread on the same request of Brandon's (02:38Z), neither reading the other. This record keeps what the second adds and the
one place where it corrects the first. Read only: no card, no state changed, no run touched. Its rulers and tables are in
[the receipts](receipts/2026-11-18_audit-levels/README.md). Held codes are nats a place at the saved means, over the five text slices'
100,508 one-place rows and 3,717 whole-mask rows unless a region is named.

## 1. Where two independent reads agree

| reading | the first audit | this one |
|---|---|---|
| the step: Adam at `2^(−12)` on every lap, nothing lowers it, `RateParts::updated` uncalled and floored at the base | §1.1 | the same lines of `deposit.rs` and every state's first line, `parts` line and absent `rates` line |
| mean of the first moment over the root of the second, lap 94's end state | 0.193 over 388,671 entries | 0.186 field, 0.168 level, 0.197 glue |
| successive moves point against each other | −0.13 to −0.53 over thirds of lap 94 | −0.14 to −0.30 over thirds of laps 69 and 93; −0.07 to −0.22 lap to lap from lap 40 |
| the level and its glue | 149,776 entries, 37%, at the noise floor | the same count; the glue moves 7 to 11% of its own rms a lap, the most of any block |
| text at the store switch | code 0.4901 to 0.5449, never recovered | five slices 0.7734 to 0.8249, 0.8256 at lap 94 |

[measurement] Two rulers written apart give one picture: the state of the line is a walk at the floor of its own step.

## 2. The whole trajectory, and what a lap can be read to

[measurement] `levels.tsv` holds every lap from 1 to 95. The one-place code fell from 0.9671 to 0.7734 over laps 1 to 70 with a gain
a lap of 9.7, 4.2, 2.0, 1.4, 0.9, 0.55 and 0.47 thousandths of a nat by decade of laps, and the scatter between laps about that trend
stood at 1.2 to 1.4 thousandths from lap 30 on. From about lap 45 a lap's own gain is under the scatter between laps, so no single lap
can be read, and every change entered from lap 71 was judged on one or two.

[measurement] The whole-mask code, the read whose states are nearest a write's, fell from 2.340 to 2.235 by lap 30, to 2.213 by lap
70, and reads 2.250 at lap 94. Every lap report led with the one-place code.

## 3. The level is traded by the mix

[measurement] The line holds what its present diet holds, and gives it back within a lap when the diet changes.

| change | what rose | what fell | source |
|---|---|---|---|
| lap 71: arithmetic and word problems join, text halved | text +0.0515 in one lap, about 45 laps of its earlier gain | | `levels.tsv` |
| laps 71 to 94: 24 laps on the mixed store | text 0.8249 to 0.8256 | word problems 0.8106 to 0.7652 (0.045 of it by lap 74) | `levels.tsv` |
| lap 95: arithmetic out, 6,000 sections | held arithmetic 1.5737 to 1.7571 | text 0.8256 to 0.8157, word problems 0.7652 to 0.7385 | `levels.tsv` |
| November 15, the own-states lap | held one-place +0.2523 in one lap | | the own-states record §2 |
| November 17, fifteen passes compared at the boundary alone | a place among known neighbours 0.920 to 2.921 | the share of written words in the lexicon 38% to 76% | the level's design record §13 |

[agent-inferred] These are one behaviour: every entry is stepped at the one rate, so every entry relaxes on one clock of about a third
of a lap (§1's cosines), and the state is the standing spread of its current mixture. Nothing in the engine is slower than that clock,
so nothing accumulates across a change of diet. It is the first audit's §1.1 and §1.3 read as a statement about memory.

## 4. Cooling was measured, and the line search is not its instrument

[measurement] The running record of November 1 holds the reading (its §16.41 and §16.42, November 4, on the field of that week):
- "a constant step leaves the code above its least by about what its own noise costs"; doubling the step from `2^(−11)` to `2^(−10)`
  raised the joint code 0.053 nats a place at once;
- under the law that moved the rate to the octave nearest the transfer's joint least, the line fell from 1.054 to 1.011 and stood; the
  halved arm fell 0.016 in its first lap; the floor at `2^(−11)` read 0.032 to 0.053 nats a place;
- the transfer itself read empty: "A step helps the section after it by nothing measurable at first order", the joint least "is not a
  price of the step", and "The law's direction (cool) is right and its price is empty";
- its close: "The step is retired as the next law's subject."

No line has cooled since. The store line ran at `2^(−12)` for 94 laps, and `store.rs` still computes that transfer every section,
"printed and never acted on" (its lines 5 and 332).

[agent-inferred] **A correction to the first audit's §3 item 1.** It proposes to "act on the line search the trainer already computes".
That line search is the November 4 law: its joint least reads a ratio of curvatures and no price, and on the store line it prints
`octave=1`, the step doubled, at every save. Acting on it heats the line. What November 4 measured is that cooling pays when it is
read directly, so the first reading is direct: three arms from one state at rates 12, 14 and 16 (the receipts hold the guesses, fixed
before any such run). The other instruments the first audit names stand: each block's `|m|/√v` against 0.206 as the deposit's own
measure of signal, and the octave law with a floor under the base.

[measurement] The saved `MEAN.k` is the mean of the states since the save before it, 1,000 sections on the line, not of the lap
(`store.rs:486` opens a new sum after every save). A level "at the lap's mean" has been the last third's.

## 5. An open place is never a source

[measurement] `support` (`crates/engine/src/contact.rs:199-212`) gives a receiver its near field's keyed sites and, past it, "only
definite sources". A site that is unresolved and carries no face is neither (`field.rs:104-108`). So open places meet each other only
along the strand, through the pair contact and the carry scan, and through the second read's mark, which is three entries
(`declaration.rs:685`). The release draws each place from its own face, one place a read, in an order by octave of distance and then
by key, so a place is often drawn before the place to its left is known.

[agent-inferred] This is the mechanism under the first audit's §1.4 and under the whole-mask code's stand in §2: where most places are
open, the contact has almost nothing to gather, and no count of laps of the one-place regime changes that. The night run of November 17
is the control that shows it: compared on everything to its left and written left to right, the share of written words in the lexicon
doubled in fifteen passes.

## 6. The loop that steered the line, in counts

[measurement] From the PRs' diffs and the guess files (the first audit's §1.10 counts the PRs by kind):
- Laps 71 to 78 took five changes (the store, the world's acts, ten crossing triads, the refined act, the redrawn slice), built and
  merged inside six and a half hours on November 16. Each one's guess on what it would buy missed or was never opened, none had a
  control from the same state, and all five were still in the state at lap 94.
- The control that would have isolated the acts (G-B2) was "not run: it costs a lap". The one controlled comparison in 24 laps was the
  side lap of November 17.
- PRs #938 to #972: 105 guesses, 34 held, 44 missed, 19 mixed. Of about 25 guesses that a new part or lever would buy a gain, none
  held. Fifteen statements were made and withdrawn, at a median of about 50 minutes.

## 7. Set aside, beside the first audit's §2

- **Cooling by the step's own reading** (§4): measured at 0.043 nats a place, retired the same day on the emptiness of its price.
- **The fifth lane** (S2, November 16): the third lane had bought 0.013 to 0.027; the fifth was displaced by the store switch and never
  trained, and its guessed price was later quoted as a measurement.
- **A memory line of November 3**, "Ruled out as levers (toy): ticks, modes, still heads, section size, step rate, momentum, drawn
  founding of returns, width by copies": two toy terrains at three seconds a lap, no reason and no scope. It is reworded in project
  memory as the dated reading it was.

## 8. What changed in the guides with this record

- CLAUDE.md, Method, "Theory picks, and a run tests a stated prediction": a change to a running line is such a comparison. It runs
  beside a control from the same saved state and leaves the line when its guess misses (§2 and §6 are the reason).
- CLAUDE.md, Method, "A temperature is a store's state, never a reading's dial": a deposit's rate is such a store, and a law that
  lowers it from the store's own travel or price is owed. The rule bars a dial passed to a reading or a release and never a cooling
  law (§4 is the reason).
- THE_ENGINE §4 and §11: the line's declaration at lap 94, and the temperature row with the reading of November 4.

## Receipts

`receipts/2026-11-18_audit-levels/`: `held_levels.py` and its `levels.tsv` (every lap's held code from the line's read files), the
fits, the states' travel by block, and the cooling read's guesses with its projection. Seven Sonnet readers read the host law, the
card's kernels, PRs #890 to #972, the records' readings and the set-aside pieces; the lines this record cites were read again in
source.
