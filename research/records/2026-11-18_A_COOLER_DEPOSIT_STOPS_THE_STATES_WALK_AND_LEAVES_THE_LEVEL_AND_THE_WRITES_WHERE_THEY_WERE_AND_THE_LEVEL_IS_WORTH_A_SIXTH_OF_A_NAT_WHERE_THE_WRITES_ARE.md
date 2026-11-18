# A cooler deposit stops the state's walk and leaves the level and the writes where they were, and the level is worth a sixth of a nat where the writes are

November 18, 2026, 03:13 to 05:45 UTC. Refs #404 #73. The lead's first acts on
[the audit of November 18](2026-11-18_THE_LINE_FLAILS_BECAUSE_A_FIXED_RATE_DEPOSIT_TRACKS_AN_UNSHUFFLED_MOVING_TERRAIN_PARTS_ARE_ADDED_AND_NEVER_REMOVED_AND_PAST_CONFIGURATIONS_WERE_BARRED_BY_NAME.md)
and [its companion](2026-11-18_COOLING_WAS_MEASURED_ON_NOVEMBER_4_AND_RETIRED_THE_LINES_LEVEL_IS_TRADED_BY_ITS_MIX_AN_OPEN_PLACE_IS_NEVER_A_SOURCE_AND_A_CHANGE_TO_A_LINE_RUNS_BESIDE_A_CONTROL.md),
at Brandon's word of 03:13Z that the audit be acted on. `measurement` for every figure
([`arms.txt`](receipts/2026-11-18_cooling/arms.txt)), `agent-inferred` for the readings. The guess G-1118-1 was fixed and pushed before
any lap ([the guess file](receipts/2026-11-18_cooling/guesses.txt)), and the audit thread's own guesses G-A1 to G-A4 are scored beside it.

## 1. What was checked before acting

The audits rank first that the deposit runs at one rate, `2^(−12)` on every entry from lap 1 to lap 94, and that the state is a walk at
its own noise floor. Read again on the line's saved states before anything ran: at lap 70 the mean of `|m| / √v` over the entries is
0.22 where a covector with no consistent sign gives 0.20; the field's material moves 1.8% of its own size a lap, and successive laps'
moves have cosines −0.158 and −0.149 (laps 67 to 70).

## 2. What had to be built to read it

At a cool rate the truncated step is zero on a face-grain entry: its size in grains is the ratio `m / (⌊√v⌋ + 1)` times
`2^(16 − rate)`, and at rate 16 that is under one on every such entry. A cool lap would have frozen the encodings, and the read would
have confounded cooling with freezing.

- **The step's carried remainder** (`Learner::remainder`, `REMAINDER_BITS = 16`): a step is formed 16 bits under its entry's grain,
  its whole part released and the rest carried to the next section. It is the precision law's own clause (a term is released by
  partition, its remainder accounted). It is carried in the learner's text and only where present, so a state without the line trains
  as before: the build reproduces lap 70's first 24 sections from lap 69's state line for line. Its test holds the released steps and
  the remainder left to the finer steps' sum.
- **State tools**: `set-rate` (the deposit's rate, with the remainder on request) and `zero-level-return` (a ruler's state with the
  level's prolongation at zero).

## 3. The laps

From lap 70's end state on the store of November 12 (text only, the last state before the terrain changed), one lap of 3,000 sections
each on the card, the same sections for every arm. A is the line's law at rate 12. B is rate 12 with the remainder carried. C is rate
14 with it. D is rate 16 with it. Nats a place on the held passage; a lap's mean is the mean of the states of its last 1,000
sections.

| arm | one place open, at its mean | at its end | whole masks, at its mean | at its end | cosines of its successive 1,000-section moves | a 1,000-section move over the state's size |
|---|---|---|---|---|---|---|
| A, rate 12 | 0.7727 | 0.7901 | 2.2089 | 2.2239 | −0.195, −0.171 | 0.020 |
| B, rate 12, remainder | 0.7727 | 0.7898 | 2.2089 | 2.2243 | −0.194, −0.171 | 0.020 |
| C, rate 14, remainder | 0.7696 | 0.7729 | 2.2085 | 2.2125 | +0.006, −0.052 | 0.007 |
| D, rate 16, remainder | 0.7714 | 0.7714 | 2.2146 | 2.2146 | +0.227, +0.130 | 0.002 to 0.003 |

Paired place by place with A's mean, one place open: C −0.0031 (±0.0004), D −0.0013 (±0.0005), B +0.0000 (±0.0001). At whole masks:
C −0.0004 (±0.0018), D +0.0057 (±0.0024). The sections' own training code, paired section by section with A over the lap's last
third: C −0.0105, D −0.0111, B +0.0000 nats a compared place (corrected at 05:58 UTC: a section's line prints millionths of a bit, and the ruler had read it on 2^-20 bits, 4.6% low; no reading changes).

The panel (the fifty books' sixteen held prompts, 64 places each, by the law's writer): 48% of its words in the lexicon from A's end
state, 46% from A's mean, 47% from D's end.

## 4. What it says

- **The fixed rate is why the state walks.** At rate 12 each thousand sections' move points against the last, and the state the line
  trains from and writes from stands 0.017 nats a place above the mean of its own last thousand states. At rate 16 the moves align,
  the state travels a seventh as far, and its end reads as its mean does. At rate 14 the cosines stand at zero, which is where a law
  that cools a store whose moves fight and holds one whose moves do not would rest.
- **It is not why the level stands.** Read at the mean, as the line has been read since November 11, the coolest arm buys 0.0013 and
  the best arm 0.0031 with one place open, about six laps of the line's own slope, and nothing at whole masks. A mean of states had
  already shed the spread; cooling moves the state onto it and adds almost nothing under it.
- **The writes do not change.**
- **The truncated step is no cause.** At rate 12 the remainder changes no figure in the fourth digit.
- **Both guesses of a level gain missed.** The audit thread's guesses for rates 14 and 16 (0.006 to 0.020 under the control) read
  0.0031 and 0.0013, and its own rule for that outcome is that the standing spread is not what holds the level. My guess that a mean
  already sheds the spread held, and my size for the spread at the end (0.004 to 0.012) missed low.
- **What one lap cannot say** is whether a state that has stopped walking compounds over laps. It is not read here.

## 5. The level's worth

The audit asked that the level be decided by reading a lap's mean with the level's prolongation zeroed: if the code does not move, the
level is out. It moves.

| state | one place open, with the level | without | whole masks, with | without |
|---|---|---|---|---|
| lap 70's mean | 0.7734 | 0.9264 | 2.2127 | 2.4384 |
| lap 94's mean | 0.8811 | 1.0933 | 2.2672 | 2.5557 |

The field as trained leans on the level's return for 0.15 to 0.21 nats a place with one place open and 0.23 to 0.29 at whole masks,
on every slice (arithmetic most, 0.46 and 0.58). A part taken out of a field that grew around it reads worse than a field grown
without it would, so these are what the trained field leans on and no bound on what a level is worth to a fresh one. They settle the
audit's item: the level stays. They also stand against two statements of the night before: that the level "holds almost nothing"
(withdrawn then), and that it is not what her writes wait on. It is leaned on most at whole masks, the regime a write is made in,
and it does that with a restriction that keeps what a drawn projection keeps (the level's design record, §9 and §13).

## 6. What follows, and what runs

- The deposit's rate becomes a state with a law once a second reading says what it should rest on: the travel's cosine puts it at
  14 here. It is a small gain and a calmer state; it is adopted as upkeep, never as the lever.
- The audit's other causes are read one at a time beside a control from lap 70. The first is on the card as this is written
  (G-1118-2): boundary rows and half-open rows in one diet, to read whether her two readings both hold when both are kept up, after the
  night of November 17 found that the boundary alone bought the writes (38% to 76% of words) and cost the two-sided reading.
- Not taken up from the audit, with the reason: acting on the trainer's own line search (its companion record withdrew it: that
  search prints a doubled step at every save); removing the level (§5). Taken and still owed: the stream's order, the comparison's
  weights by declaration, the residue in the tree, and the guides brought to the line as trained.
