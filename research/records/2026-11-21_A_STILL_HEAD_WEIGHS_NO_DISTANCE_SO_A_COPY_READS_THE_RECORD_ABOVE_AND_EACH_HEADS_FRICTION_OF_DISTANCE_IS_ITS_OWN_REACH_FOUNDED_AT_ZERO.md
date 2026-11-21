# A still head weighs no distance, so a copy reads the record above; each head's friction of distance is its own reach, founded at zero

November 21, the lead, 16:10 to 20:10 UTC. Refs #404, #405. It follows
[the day's record of the terrain read by two streams](2026-11-21_A_LAW_FOUNDED_IN_A_REGIME_THE_WRITER_NEVER_READS_NEVER_REACHES_HER_WRITES_READ_BY_TWO_STREAMS_THE_TERRAIN_TAKES_BRACKETS_AND_SUMS_INSIDE_THE_LINE_AND_A_RELEASE_HALTS_WHERE_ITS_GAIN_DIES.md),
whose §7 item 2 named this loop's subject: sums with three-digit operands and carries, and copies beyond two digits, where the
terrain's third lap stood still (W79t: 27 of 96 held records whole, sums 4 and copies 3 of 16), because the binding reached a place or
two and not a line. Receipts: [`receipts/2026-11-21_reach/`](receipts/2026-11-21_reach/) (`guesses.txt` with every guess's stamp and
score, the rulers, their reads).

## 1. What she wrote

W79t's mean on the terrain's held panel, the copies, as they came out (prompt's last record, then her write):

```
copy 1 5 2 0 4 7 7 =   1 5 2 0 3 7 7
copy 4 7 8 =           8 7 8
copy 4 7 1 8 4 7 9 =   0 8 0 7 5 3 9
copy 0 1 7 6 =         7 1 7 6
copy 8 7 9 1 9 5 7 =   8 3 9 1 9 5 7
```

The third is the record above it in the prompt (`copy 0 8 0 7 5 3 = 0 8 0 7 5 3`), copied digit for digit until its sixth digit ran
out, and then this record's seventh. The slips are single digits taken from the same place of another record.

## 2. What the tree held

Searched before the reading (the atlas for reach, falloff, friction, octave, distance, copy, induction; the records they name):

- **The contact's prior.** A source `d` places away scores `⌊log₂ d⌋` lower at a turned head, equal mass an octave, which is the exponent
  `r = 1` at which a passage with one sharp tie an octave is a navigable small world (`contact.octave-falloff-navigable`, Kleinberg's
  theorem on the objects; at `r = 0` a ring of 16,384 places takes 115 relays where `r = 1` takes 47).
- **The reach is a friction matched to the distance** (`wave.matched-friction-reach`): a mode carries a push `L` ticks best at
  `ρ² = L/(L + 1)`, and a bank of octave frictions carries every distance with harmonic falloff.
- **The reach on the clock** (`tower.field-reach-on-clock`, November 13, designed and unbuilt): two terms a turned head, founded at zero,
  that put its falloff on the clock its skins run on.
- **The conservation of faces** (November 3, `agent-inferred`, `contact.rs`): "a still head reads content at any distance", so a still
  head's source is lowered by the octave of its class's count and never by its distance. A still head is the case `r = 0`.
- **The lock records of November 16**: head 0 is the head that addresses an operand digit, and two thirds of its row went to sources that
  serve its other work; the lock is short in its keys and not in its gain.
- **The wheel of November 17** (designed, unbuilt): a clock with a hand and a collapse, so a phase counted since a separator can address
  the `k`-th place of a record.

## 3. The reading: where the far operand's weight goes

`read-strand-states … past rows` (new, a ruler: each open place's row at every tick and head, by source) on W79t's mean, 1,800 passages
of three records of one kind as the terrain writes them (copies and reversals of 2 to 7 digits, sums of 1- to 3-digit operands), every
place read by two streams with the pass's `past`. At each answer digit of the third record, the row's share on the source its value is
fixed by (a copy's and a reversal's one operand digit, a sum's two aligned digits), on the near field, on the same digit's counterparts
in the two earlier records, and on the rest (`reach_ruler.py`, `rows_W79t.txt`):

| head 0's row | tick 0 | tick 1 | tick 2 | tick 3 |
|---|---|---|---|---|
| copy (2,655 digits): the operand digit | 0.032 | 0.500 | 0.651 | 0.586 |
| copy: the same digit in the earlier records | 0.064 | 0.230 | 0.278 | 0.237 |
| reversal (2,667): the operand digit | 0.018 | 0.025 | 0.316 | 0.759 |
| reversal: its counterparts | 0.034 | 0.046 | 0.126 | 0.055 |
| sum (1,579): the aligned pair | 0.262 | 0.351 | 0.326 | 0.352 |
| sum: its counterparts | 0.140 | 0.062 | 0.091 | 0.159 |

The turned heads (2 and 3) hold 0.006 to 0.033 on the needed source at the last tick, and 0.27 to 0.69 on the near field. The read after
the last tick holds the copy's operand digit at 0.69 of its indicator's variance, the reversal's at 0.73 (least squares, fitted on the
even passages, read on the odd).

So at a copy head 0 finds "digit `k` of a record" (0.93 of its row at tick 2) and does not tell which record: a still head weighs a
source by its class alone, and the nearest instance and every earlier one stand alike. That is the write of §1.

**The rows reweighed at their present keys** (`reweigh.py`, `reweigh_W79t.txt`: each source's share times `2^(−ψ⌊log₂ d⌋)`, renormalized;
first order, nothing downstream moved): at `ψ` of one bit an octave the copy's operand digit takes 0.804 of head 0's row at tick 2
(counterparts 0.135), the reversal's 0.877 at tick 3, the sum's pair 0.446.

**The code under a ruler's friction** (`read-reach`, new; `Constitution::ruler_friction`, the friction in the forward alone). G-R1 was
fixed at 16:25:13Z before the read was looked at, and held on every clause:

| head 0's listeners | copy digit | reversal digit | sum digit (hundreds) | held text, 800 frontier rows, nats a place |
|---|---|---|---|---|
| the law | 0.541 | 0.445 | 1.024 (2.465) | 1.3087 |
| half a bit an octave | 0.160 | 0.145 | 0.783 (1.791) | +0.0029 |
| one bit | 0.059 | 0.048 | 0.648 (1.409) | +0.0148 (code +0.013, wikidata +0.023) |
| two bits | 0.025 | 0.049 | 0.525 (1.023) | +0.0751 |
| heads 0 and 1, one bit each | 0.056 | 0.052 | 0.643 | +0.0190 |
| the turned heads one bit more | 1.044 | 0.778 | 1.000 | +0.0272 |

In nats a digit, by two streams. Over every place of the terrain's passages the code is 0.578 nats a place at the law and 0.553 at one bit.

## 4. On the objects

- A pair contact addresses by its lock, and its prior over distance is part of the contact's material: the friction a source's
  arrival pays for the places it crossed. The built field fixed that prior at one bit an octave for a turned head and at none for a
  still one. A contact with no friction over distance is a store at rest along the passage, which no store is (the stores law): it
  keeps every earlier instance of a content at full weight and never forgets one.
- The exponent belongs to the head, and the head's own covector says where it stands: a head whose useful source is nearer than its
  rivals is pushed toward more friction, a head whose useful sources are far is pushed toward less. At founding the push is the row's
  covariance between a source's use and its octave, `δψ = −Σ δz_ij ⌊log₂ d_ij⌋`, which a symmetric row does not cancel (the temperature's
  covector did cancel, the record of November 16 §3.1; this one has the reading of §3 behind it).
- Why not the wheel first. The wheel puts a record's own count on a clock so a probe can address the `k`-th place since a separator.
  Head 0 already addresses the `k`-th place (0.93 of its row at a copy), from what the turned heads gathered in the tick before. What it
  lacks is which record, and of the records that hold a `k`-th digit the one wanted is the nearest. That is a prior over distance, and
  the prior's place in the law is the falloff.
- One law for every stream: the friction is a contact's, for text, image, acoustic and motor input alike, read on held text beside the
  terrain (§3's last column).

## 5. The law, as built

`Declaration::friction` (head line `hnn-field-v14r`): each head's friction of distance, `ψ_(h,k)` on `2^(−16)` bits an octave for head `h`
and receiver kind `k`, eight entries on the line (`Loci::friction`, the last family; part 28, `friction`). A source `d` places from its
receiver scores `ψ_(h,k) ⌊log₂ d⌋` lower on top of the falloff that stands, and an octave's crowd `ψ` times its level lower. Founded at
zero (`Constitution::with_friction`, `Learner::with_friction`, the command `found-friction`), so the founded field reads every face of its
source bit for bit. The covector is the forward's own, `−Σ δz_ij ⌊log₂ d_ij⌋` over a head's rows of that kind, released once a row to the
face family's grain, and the deposit moves it as any entry (at most about `2^(−12)` bits an octave a section).

Receipts of the build:
- host: founded at zero every face and every standing covector is the source's, in regions and in passages read by two streams
  (`the_friction_founded_at_zero_keeps_every_face_and_every_standing_covector`); off zero the return matches the code's central
  difference on 306 probes, 24 at the frictions, none on a seam (`the_frictions_return_matches_its_codes_difference`);
- card: the score's friction (`friction_of`, `scored`, `crowd_score`) and its covector in `field_contact_rows`; the host's bits on the
  first run on regions of the law of 2 to 257 sites, passages read by two streams of 2 to 300 places and a section of both, the frictions
  taking a covector at both kinds (`the_friction_of_distance_on_the_card_reads_the_hosts_bits`);
- gate 3 against W79t's lap with the law off (`reach/gate3`): parity 3 of 3 sections equal, 24 of 24 sections reproduced, the lap's
  read byte for byte;
- `found-friction` on W79t's end: 12 lines judged, the declaration's head word, the fine material and both moments with eight new
  words at zero, the parts line with the friction's octave appended at zero, seven lines equal.

**The gate** (`Declaration::friction_gate`, the `v14r` line's friction word `2`; written after W80r's first lap showed one number a head
and kind standing still, §6). Head `h`'s friction at receiver `i` is `ψ_(h,k) + release(⟨a_h, r̂_i⟩, 24)`, with `r̂_i` the receiver's chart at
the tick (the read its key, probe and value are charted from) and `a_h` a row of `D` a head on `2^(−24)` (`Loci::friction_gate`, the friction's
part), founded at zero. Its covector is the row's `δψ_i` against the read, `δa_h = Σ_i δψ_i r̂_i`, and the read takes `a_h δψ_i` back, so the
friction is a gate of the site's state as the carry circle's leak is. Its premise read: a linear read of the receiver's last-tick state,
fitted on half the passages, told where a friction of one bit pays, and a friction set only there kept every copy and reversal digit's gain
(0.53 to 0.07 nats a copy digit) at +0.005 nats a text place where the friction everywhere cost +0.016 (`site_friction.py`). Receipts:
founded at zero every face and standing covector kept; off zero its return matches the code's difference on 325 probes, 36 at the gate;
the card the host's bits on the first run (`the_friction_read_from_the_receivers_state_on_the_card_reads_the_hosts_bits`); gate 3 equal
on its build; `found-friction … gate` founds both on a state (904 entries, every other line judged).

The friction's Lean statement (the score linear in `ψ` and in `a_h`, its covector `−Σ δz ⌊log₂ d⌋` and the gate's `Σ δψ r̂`) is owed in #410.

## 6. The arms

Three laps of 3,000 sections from W79t's end on the card, each read at its MEAN.3000 (the mean of its last 1,000 sections). W80t is the
control (no change). W80r carries the friction founded at zero, W80g the friction and its gate. Each arm differs from W80t by one change.
Each build reproduced W79t's lap with its new law off before it trained (gate 3: parity 3 of 3, 24 of 24 sections, the lap's read byte for
byte), and each founded state's first sections read the control's bits.

**What they wrote.** The terrain's held panel, the copies (the panel's last prompt, then the write):

```
                              W80t (control)         W80g (the gate)
copy 0 6 9 =                  6 0 8                  0 6 9
copy 4 8 5 =                  4 7 3                  4 8 5
copy 0 1 7 6 =                8 8 8 4                0 1 7 6
copy 1 3 4 0 0 =              9 3 4 0 0              1 3 4 0 0
copy 2 7 2 7 4 0 =            2 9 1 1 3 6            2 8 2 7 4 2
copy 4 7 1 8 4 7 9 =          0 8 0 7 5 3 9          0 8 0 7 5 3 9
730 + 929 =                   1359                   1579
```

| at the lap's mean | W80t | W80r | W80g |
|---|---|---|---|
| held records whole, of 96 | 37 | 30 | **41** |
| copies / reversals / sums / differences / products / brackets, of 16 | 3 / 5 / 7 / 7 / 4 / 11 | 3 / 3 / 4 / 7 / 5 / 8 | **7** / 5 / 6 / 9 / 3 / 11 |
| first symbol, of 96 | 63 | 63 | 70 |
| answer digits by two streams, nats a digit: copy / reversal / sum | 0.549 / 0.442 / 1.139 | 0.537 / 0.496 / 1.051 | **0.269 / 0.138 / 0.983** |
| held text, one place open, against W80t (nats a place) | | +0.0001 (±0.0002) | −0.0001 (±0.0002) |
| the frontier read against W80t | | +0.0001 (±0.0002) | +0.0000 (±0.0003) |
| wide panel, words in the lexicon | | 71% | 73% |

- **W80r: one friction a head and kind does not move.** Over the lap head 0's class receivers took 0.077 bits an octave and its listeners,
  the open places the writer reads, went to −0.042: less friction, where the copies needed more. The heads' frictions stood within a
  tenth of a bit. The passage's mix decides one number for every place, and text outweighs the terrain's answer digits, as one
  temperature for the whole passage did on November 16 (§4.3 of that record). The copies stay at 3 of 16, and the whole records fall
  from 37 to 30.
- **W80g: the friction read from the receiver's own state carries the operand.** The gate's rows moved fast (head 0's row reached a
  norm of 0.15 on `2^(−24)` by section 1,000) while the head's own friction stayed near zero, so each place takes the friction its own
  state asks for. Copy digits fell from 0.549 to 0.269 nats and reversals from 0.442 to 0.138. Copies written whole went from 3 to 7 of
  16, whole records from 37 to 41 of 96, and first symbols from 63 to 70. The held text did not move (−0.0001 ± 0.0002 nats a place at
  one place open, every region within 0.002). The ruler's static gate had kept the terrain's gain at a third of the text's price.
  Trained from zero, the gate takes half of that gain and pays none of the price.
- **What it does not yet carry.** `copy 4 7 1 8 4 7 9` still writes the record above it whole, and the sums gained a little in code and
  nothing in whole writes (7 of 16 at the control, 6 at the gate). A sum's answer digit needs two operands and their carry, and the
  friction brings the near one of the two (§3: head 0's pair took 0.35 of its row before and 0.45 under the ruler's friction).
- The loudness of every region at W80g's mean is in `loudness_W80g.txt` (all regions 21.80 octaves, temperature −0.023 a nat).

**The guesses.** G-F1 (16:57:07Z) missed on its writes, its codes and its friction (30 of 96, 3 copies; copy digits 0.537; head 0's
listeners at −0.042), and held its text clause. G-G1 (18:44:13Z) held on every clause: 0.269 against 0.35 a copy digit, 0.983 against
1.00 a sum digit, 41 of 96 whole against 34, 7 copies against 6, and text −0.0001 against 0.02. By each guess's own rule the line takes
the gate (W80g's end is the line's state from here), and the friction without its gate leaves it.

## 7. Recorded failures this could repeat

- A part founded at zero and waited for (November 13 to 16). What differs: its slope at the founding was read first, as a finite
  difference of the code (§3), and is large on the terrain and small on text. The first form still waited (W80r), because one number
  for every place is pulled by the whole passage; the gate gives each place its own.
- A width or a reach set by hand. The ruler's settings were readings; the law's `ψ` is located by its covector, and the arm reads where it
  goes.
- A routine standing in for learning. No copy, no counter of records: a contact's prior over distance, the same for every stream.
- The terrain's price on text. Read beside it (§3), and the arm's guess holds the text within 0.02 nats a place of its control.

## 8. Receipts

`receipts/2026-11-21_reach/`: `guesses.txt`; `make_rows.py` (the rows, seed 1121, 600 a kind); `reach_ruler.py`, `rows_W79t.txt`;
`reweigh.py`, `reweigh_W79t.txt`; `reach_read.sh`, `answer_codes.py`, `answer_codes_W79t.txt`, `text_codes_W79t.txt`; `site_friction.py`,
`site_friction_W79t.txt`; the arms' scripts `w80.sh`, `w80g.sh`; `terrain_scores_W80.txt`, `reach_W80.txt` (the answer digits' codes and
the frictions at each save), `text_W80.txt`, `panels_W80.txt`, `loudness_W80g.txt` (its regions' lines; the pieces stay under `.local/`). The passages' text
and the states stay under `.local/`.
